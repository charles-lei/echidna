{-# LANGUAGE BangPatterns, DeriveGeneric, FlexibleContexts, KindSignatures, LambdaCase, StrictData  #-}

module Echidna.Coverage (
    ContractCov(..)
  , CoverageInfo
  , CoverageRef
  , CoverageReport(..)
  , eCommandCoverage
  , ePropertySeqCoverage
  , execCallCoverage
  , getCover
  , mergeCoverage
  , printResults
  , ppHashes
  , reduceCoverage
  , module Echidna.Internal.Runner
  , module Echidna.Internal.JsonRunner
  ) where

import Control.DeepSeq            (force)
import Control.Concurrent.MVar    (MVar, modifyMVar_)
import Control.Lens               ((&), use, view)
import Control.Monad.IO.Class     (MonadIO, liftIO)
import Control.Monad.State.Strict (MonadState, StateT, evalStateT, get, runState)
import Control.Monad.Reader       (MonadReader, ReaderT, runReaderT, ask)
import Data.Aeson                 (ToJSON(..), encode)
import Data.ByteString.Lazy.Char8 (unpack)
import Data.Foldable              (Foldable(..), foldl')
import Data.IORef                 (IORef, modifyIORef', newIORef, readIORef)
import Data.Map.Strict            (Map, insertWith, toAscList, unionWith)
import Data.Maybe                 (fromMaybe)
import Data.Ord                   (comparing)
import Data.Set                   (Set, singleton, union)
import Data.Vector                (Vector, fromList)
import Data.Vector.Generic        (maximumBy)
import GHC.Generics

import qualified Control.Monad.State.Strict as S

import Hedgehog
import Hedgehog.Gen               (choice)

import EVM
import EVM.Types    (W256)

import Echidna.ABI (SolCall, SolSignature, genInteractions, mutateCall)
import Echidna.Config (Config(..), printCoverage)
import Echidna.Internal.Runner
import Echidna.Internal.JsonRunner
import Echidna.Exec

-----------------------------------------
-- Coverage data types and printing

type Coverage = Map W256 (Set Int)

mergeCoverage :: Coverage -> Coverage -> Coverage
mergeCoverage a b = unionWith union a b

reduceCoverage :: [Coverage] -> Coverage
reduceCoverage = foldl' mergeCoverage mempty

coverageSize :: Coverage -> Int
coverageSize = foldl' (\acc s -> acc + (length s)) 0

type CoverageInfo = (SolCall,Coverage)
type CoverageRef  = IORef CoverageInfo

printResults :: (MonadIO m, MonadReader Config m) => Coverage -> m ()
printResults ci = do liftIO (putStrLn $ "Coverage: " ++ show (coverageSize ci) ++ " unique arcs")
                     view printCoverage >>= \case True  -> liftIO . print . ppHashes $ ci
                                                  False -> pure ()

data ContractCov = ContractCov { hash :: String, arcs :: ![Int] } deriving (Show, Generic)
data CoverageReport = CoverageReport { coverage :: ![ContractCov] } deriving (Show, Generic)

instance ToJSON ContractCov
instance ToJSON CoverageReport

ppHashes :: Coverage -> String
ppHashes = unpack . encode . toJSON . CoverageReport
  . map (\(h, is) -> ContractCov (show h) (toList is)) . toAscList

-----------------------------------------
-- Set cover algo

getCover :: [(a, Coverage)] -> [a]
getCover [] = []
getCover xs = setCover (fromList xs) mempty totalCoverage []
  where totalCoverage = coverageSize . mconcat $ map snd xs

setCover :: Vector (a, Coverage) -> Coverage -> Int -> [a] -> [a]
setCover vs cov tot calls = best : calls & if coverageSize new == tot then id
                                                                else setCover vs new tot where
  (best, new) = mappend cov <$> maximumBy (comparing $ length . mappend cov . snd) vs

-----------------------------------------
-- Echidna exec with coverage
  
execCallCoverage :: (MonadState VM m, MonadReader CoverageRef m, MonadIO m) => SolCall -> m VMResult
execCallCoverage sol = execCallUsing (go mempty) sol where
  go !c = use result >>= \case
    Just x -> do ref <- ask
                 liftIO $ modifyIORef' ref (const (sol, c))
                 return x
    _      -> do current <- use $ state . pc
                 ch <- view codehash . fromMaybe (error "no current contract??") . currentContract <$> get
                 S.state (runState exec1)
                 go . force $ insertWith union ch (singleton current) c

eCommandCoverage :: (MonadGen n, MonadTest m, MonadState VM m, MonadReader CoverageRef m, MonadIO m)
                 => [SolCall] -> (VM -> Bool) -> [SolSignature] -> Config -> [Command n m VMState]
eCommandCoverage cov p ts conf = let useConf = flip runReaderT conf in case cov of
  [] -> [eCommandUsing (useConf $ genInteractions ts) (\(Call c) -> execCallCoverage c) p]
  xs -> map (\x -> eCommandUsing (choice $ useConf <$> [mutateCall x, genInteractions ts])
              (\(Call c) -> execCallCoverage c) p) xs

ePropertySeqCoverage :: (MonadReader Config m)
                     => [SolCall]
                     -> MVar [CoverageInfo]
                     -> (VM -> Bool)
                     -> [SolSignature]
                     -> VM
                     -> m Property
ePropertySeqCoverage calls cov p ts v = ask >>= \c -> ePropertyUsing (eCommandCoverage calls p ts c) writeCoverage v 
  where writeCoverage :: MonadIO m => ReaderT CoverageRef (StateT VM m) a -> m a
        writeCoverage m = do
          threadCovRef <- liftIO $ newIORef mempty
          let s = runReaderT m threadCovRef
          a         <- evalStateT s v
          threadCov <- liftIO $ readIORef threadCovRef
          liftIO $ modifyMVar_ cov (\xs -> pure $ threadCov:xs)
          return a
