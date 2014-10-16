{-
Copyright 2010-2012 Cognimeta Inc.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in
compliance with the License. You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under the License.
-}

{-# LANGUAGE TemplateHaskell, TypeFamilies, Rank2Types, GADTs, TupleSections, DeriveDataTypeable, GeneralizedNewtypeDeriving, ScopedTypeVariables, FlexibleContexts #-}

module Database.Perdure.LocalStoreFile (
    RawStoreFile(..),
    storeFileWriteWords,
    storeFileReadWords,
    LocalStoreFile,
    withFileStoreFile,
    withRawDeviceStoreFile,
    withRawDeviceStoreFiles,
    module Database.Perdure.StoreFile,
    narrowBufsLen,
    storeFileWrite1,
    storeFileRead1
) where


import Prelude ()
import Cgm.Prelude
import Data.Typeable
import qualified Data.ByteString as B
import Control.Concurrent
import Data.Word
import qualified Data.Map as Map
import Cgm.Data.Super
import Cgm.Data.Len
import Cgm.Data.Monoid
import Cgm.Data.NEList
import Cgm.Data.Either
import Cgm.System.Endian
import Cgm.Control.Concurrent.TThread
import Cgm.Control.Concurrent.Await
import Cgm.System.Mem.Alloc
import Database.Perdure.Validator
import System.IO
--import System.Posix.Files
--import System.Posix.IO
import System.Posix.Types
import Data.Bits
import Control.Monad.Error hiding (sequence_)
import Database.Perdure.StoreFile(SyncableStoreFile(..))
--import System.Posix.Fsync -- not needed with raw devices


-- | Opens the specified raw device as a LocalStoreFile, runs the provided function and closes the device.
-- Do not make concurrent calls on the same device, place concurrency in the passed function.
withRawDeviceStoreFile :: FilePath -> (LocalStoreFile -> IO a) -> ErrorT String IO a
withRawDeviceStoreFile path user =
  ErrorT $ bracket (openFd path ReadWrite Nothing $ defaultFileFlags {exclusive = True, append = True}) closeFd $ 
  \fd -> runErrorT $
         do fs <- lift $ getFdStatus fd
            bool (throwError "Not a raw device") (lift $ withRawFile (RawDevice fd fs 9) user) $ isCharacterDevice fs

-- | Like nesting multiple calls to 'withRawDeviceStoreFile'.
withRawDeviceStoreFiles :: [FilePath] -> ([LocalStoreFile] -> IO a) -> ErrorT String IO a
withRawDeviceStoreFiles ps user = foldr (\p u fs ->  (>>= ErrorT . pure) $ withRawDeviceStoreFile p $ \f -> runErrorT $ u $ fs `mappend` [f]) (lift . user) ps []

toFileOffset :: Integral n => Len Word8 n -> FileOffset
toFileOffset = fromIntegral . getLen

toByteCount :: Integral n => Len Word8 n -> ByteCount
toByteCount = fromIntegral . getLen

fdSeekLen :: Fd -> ByteAddr -> IO ()
fdSeekLen fd seek = () <$ fdSeek fd AbsoluteSeek (toFileOffset seek)

-- TODO: consider adding support for a 'STPrimArray RealWorld Pinned Block', and a matching address type, that would enfoce the above requirements
-- However we would have to cast/view it as an array of Word8 later on.
-- | Array's size and start must be aligned on the block size, and the ByteAddr too.
fdReadArray :: Fd -> ByteAddr -> ArrayRange (STPrimArray RealWorld Pinned Word8) -> ErrorT String IO ()
fdReadArray fd start a = ErrorT $ fmap (boolEither "" () . (==) (toByteCount $ arrayLen a)) $ 
                         fdSeekLen fd start >> withArrayPtr (\ptr len -> fdReadBuf fd ptr $ toByteCount len) a

fdWriteArray :: Fd -> ByteAddr -> ArrayRange (STPrimArray RealWorld Pinned Word8) -> ErrorT String IO ()
fdWriteArray fd start a = ErrorT $ fmap (boolEither "" () . (==) (toByteCount $ arrayLen a)) $ 
                          fdSeekLen fd start >> withArrayPtr (\ptr len -> fdWriteBuf fd ptr $ toByteCount len) a

-- A bit of info on raw devices that i did not find easily elsewhere: http://www.win.tue.nl/~aeb/linux/lk/lk-11.html#ss11.4

data RawDevice = RawDevice Fd FileStatus Int
rawDeviceBlockBytes :: RawDevice -> Len Word8 Word
rawDeviceBlockBytes (RawDevice _ _ lg) = unsafeLen $ 1 `shiftL` lg
instance Show RawDevice where show (RawDevice _ fs _) = show $ specialDeviceID fs
-- TODO merge consecutive writes to improve performance (avoids many needless reads to preserve data that will be overwritten)
instance RawFile RawDevice where                              
  fileWriteRaw r@(RawDevice fd _ _) start bufs =
    let len = up $ sum $ arrayLen <$> bufs in
    withBlockArray r start len $ ((. fullArrayRange) .) $ \tStart t -> 
    do
      let bb = rawDeviceBlockBytes r
      let tLen = arrayLen t
      let tEnd = tStart + up tLen
      when (tStart < start) $ fdReadArray fd tStart $ headArrayRange bb t
      when (start + len < tEnd) $ fdReadArray fd (tEnd - up bb) $ skipArrayRange (tLen - bb)  t
      let dest = skipArrayRange (fromJust $ unapply super $ start - tStart) t
      _ <- lift $ stToIO $ foldlM (\d b -> skipArrayRange (arrayLen b) d <$ mapMArrayCopyImm return b d) dest bufs
      fdWriteArray fd tStart t
  fileReadRaw r@(RawDevice fd _ _) start buf =
    withBlockArray r start (up $ arrayLen buf) $ ((. fullArrayRange) .) $ \tStart t -> 
     do 
       -- liftIO $ putStrLn $ "Before fdReadArray " ++ show start
       fdReadArray fd tStart t
       let rangeToCopy = skipArrayRange (fromJust $ unapply super $ start - tStart) t
       lift $ stToIO (mapMArrayCopy return rangeToCopy buf)
  fileFlush _ = return ()
  
-- Takes start and length, and passes rounded start and an aligned buffer
withBlockArray :: MonadIO m => RawDevice -> ByteAddr -> ByteAddr -> (ByteAddr -> STPrimArray RealWorld Pinned Word8 -> m a) -> m a
withBlockArray r@(RawDevice _ _ lgBlockBytes) seek len f = 
  let blockBytes = rawDeviceBlockBytes r
      seek' = getLen seek
      len' = getLen len
      start = (seek' `shiftR` lgBlockBytes) `shiftL` lgBlockBytes
      end = ((seek' + len' + up (getLen blockBytes) - 1) `shiftR` lgBlockBytes) `shiftL` lgBlockBytes
  in liftIO (stToIO $ newAlignedPinnedWord8Array blockBytes $ unsafeLen $ fromJust $ unapply super $ end - start) >>= 
     f (unsafeLen start)
           -- . trace ("withBlockArray blockBytes=" ++ show blockBytes ++ " start=" ++ show (unsafeLen start) ++ " size=" ++ (show $ arrayLen r))
