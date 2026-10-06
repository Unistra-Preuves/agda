{-# LANGUAGE CPP #-}

module Agda.Canonical.FFI (runCanonical) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Control.Exception (SomeException, bracket, displayException, try)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BS (unsafeUseAsCStringLen)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Word (Word8, Word64)
import Foreign.C.Types (CSize (..))
import Foreign.Marshal.Pool (Pool, pooledMallocBytes, withPool)
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr (FunPtr, Ptr, castPtr, nullPtr, plusPtr)
import Foreign.Storable (peekByteOff, pokeByteOff, sizeOf)
import System.Environment (lookupEnv)
import System.IO.Unsafe (unsafePerformIO)

#if defined(mingw32_HOST_OS)
import Foreign.Ptr (castPtrToFunPtr)
import System.Win32.DLL (getProcAddress, loadLibrary)
#elif !defined(wasm32_HOST_ARCH)
import System.Posix.DynamicLinker (RTLDFlags (..), dlopen, dlsym)
#endif

import Agda.Canonical.Types

{-
  Interface with the canonical-agda crate (crates/canonical-agda/src/lib.rs
  in the Canonical repository).

  Terms are exchanged as trees of C structs, without serialisation.
  Arrays are (pointer, length) pairs, strings are UTF-8 bytes without terminator.
  With w the size of a pointer (the Rust side checks this layout at compile time):

    FfiStr      = { ptr, len }                           -- 2w
    FfiSpine    = { head : FfiStr, args, nargs }         -- 4w
    FfiEquation = { lhs : FfiSpine, rhs : FfiSpine,
                    is_redex : u8 }                      -- 9w
    FfiDecl     = { name : FfiStr, typ (nullable),
                    equations, nequations }              -- 5w
    FfiExpr     = { params, nparams, lets, nlets,
                    spine : FfiSpine }                   -- 8w
    FfiResult   = { exprs, nexprs }                      -- 2w

  The goal lives in a Haskell pool, freed once Canonical returns;
  the result is allocated by Rust and released with canonical_free.

  The library is not linked with Agda: it is loaded at the first call, from the
  path in AGDA_CANONICAL_LIB, or else by name through the system search path
  (LD_LIBRARY_PATH, DYLD_LIBRARY_PATH, PATH).
-}

data FfiDecl
data FfiResult

type Solve = Ptr FfiDecl -> Word64 -> CSize -> IO (Ptr FfiResult)
type Free  = Ptr FfiResult -> IO ()

foreign import ccall safe "dynamic"
  mkSolve :: FunPtr Solve -> Solve

foreign import ccall unsafe "dynamic"
  mkFree :: FunPtr Free -> Free

data Canonical = Canonical
  { c_canonical_solve :: Solve
  , c_canonical_free  :: Free
  }

-- | Name of the library for the system search path.
libraryName :: FilePath
#if defined(mingw32_HOST_OS)
libraryName = "canonical_agda.dll"
#elif defined(darwin_HOST_OS)
libraryName = "libcanonical_agda.dylib"
#else
libraryName = "libcanonical_agda.so"
#endif

-- | Loads the library and finds its two functions.
loadCanonical :: FilePath -> IO Canonical
#if defined(mingw32_HOST_OS)
loadCanonical path = do
  dl <- loadLibrary path
  let sym s = castPtrToFunPtr <$> getProcAddress dl s
  Canonical <$> (mkSolve <$> sym "canonical_solve") <*> (mkFree <$> sym "canonical_free")
#elif !defined(wasm32_HOST_ARCH)
loadCanonical path = do
  dl <- dlopen path [RTLD_NOW, RTLD_LOCAL]
  Canonical <$> (mkSolve <$> dlsym dl "canonical_solve") <*> (mkFree <$> dlsym dl "canonical_free")
#else
loadCanonical _ = ioError (userError "dynamic loading is not supported on this platform")
#endif

-- | The library, once loaded. A failed load is retried at the next call.
loaded :: MVar (Maybe Canonical)
loaded = unsafePerformIO (newMVar Nothing)
{-# NOINLINE loaded #-}

getCanonical :: IO (Either String Canonical)
getCanonical = modifyMVar loaded $ \case
  Just c  -> return (Just c, Right c)
  Nothing -> do
    path <- maybe libraryName id <$> lookupEnv "AGDA_CANONICAL_LIB"
    r <- try (loadCanonical path)
    return $ case r of
      Right c -> (Just c, Right c)
      Left e  -> (Nothing, Left $ unlines
        [ "Canonical: cannot load " ++ path ++ "."
        , displayException (e :: SomeException)
        , "Build it with build_agda.py in the Canonical repository, then set"
        , "AGDA_CANONICAL_LIB to its path, or add its directory to the library search path."
        ])

w, sizeSpine, sizeEquation, sizeDecl, sizeExpr :: Int
w            = sizeOf (nullPtr :: Ptr ())
sizeSpine    = 4 * w
sizeEquation = 9 * w
sizeDecl     = 5 * w
sizeExpr     = 8 * w

{-
  Calls Canonical on the goal, with a timeout in seconds and the number of solutions.
  Returns [] if the search panicked, and an error if the library cannot be loaded.
-}
runCanonical :: CDecl -> Int -> Int -> IO (Either String [CExpr])
runCanonical goal timeout count = getCanonical >>= traverse \c -> withPool $ \pool -> do
  g <- pooledMallocBytes pool sizeDecl
  pokeDecl pool g goal
  bracket (c_canonical_solve c g (fromIntegral timeout) (fromIntegral count))
          (c_canonical_free c) $ \r ->
    if r == nullPtr then return [] else peekArray sizeExpr peekExpr r 0

---- Haskell -> Rust ----

-- | Writes the list as an array of elements of the given size, and its (pointer, length) at dst + off.
pokeArray :: Pool -> Int -> (Ptr () -> a -> IO ()) -> Ptr b -> Int -> [a] -> IO ()
pokeArray pool sz f dst off xs = do
  p <- if null xs then return nullPtr else pooledMallocBytes pool (sz * length xs) :: IO (Ptr ())
  sequence_ [ f (p `plusPtr` (i * sz)) x | (i, x) <- zip [0 ..] xs ]
  pokeByteOff dst off p
  pokeByteOff dst (off + w) (fromIntegral (length xs) :: CSize)

pokeStr :: Pool -> Ptr a -> String -> IO ()
pokeStr pool dst s = do
  let bs = T.encodeUtf8 (T.pack s)
      n  = BS.length bs
  p <- if n == 0 then return nullPtr else do
    p <- pooledMallocBytes pool n
    BS.unsafeUseAsCStringLen bs $ \(src, _) -> copyBytes p (castPtr src :: Ptr Word8) n
    return p
  pokeByteOff dst 0 p
  pokeByteOff dst w (fromIntegral n :: CSize)

pokeSpine :: Pool -> Ptr a -> CSpine -> IO ()
pokeSpine pool dst (CSpine h as) = do
  pokeStr pool dst h
  pokeArray pool sizeExpr (pokeExpr pool) dst (2 * w) as

pokeEquation :: Pool -> Ptr a -> CEquation -> IO ()
pokeEquation pool dst (CEquation l r redex) = do
  pokeSpine pool dst l
  pokeSpine pool (dst `plusPtr` (4 * w)) r
  pokeByteOff dst (8 * w) (if redex then 1 else 0 :: Word8)

pokeDecl :: Pool -> Ptr a -> CDecl -> IO ()
pokeDecl pool dst (CDecl n t eqs) = do
  pokeStr pool dst n
  pt <- case t of
    Nothing -> return nullPtr
    Just e  -> do
      p <- pooledMallocBytes pool sizeExpr :: IO (Ptr ())
      pokeExpr pool p e
      return p
  pokeByteOff dst (2 * w) pt
  pokeArray pool sizeEquation (pokeEquation pool) dst (3 * w) eqs

pokeExpr :: Pool -> Ptr a -> CExpr -> IO ()
pokeExpr pool dst (CExpr ps ls sp) = do
  pokeArray pool sizeDecl (pokeDecl pool) dst 0 ps
  pokeArray pool sizeDecl (pokeDecl pool) dst (2 * w) ls
  pokeSpine pool (dst `plusPtr` (4 * w)) sp

---- Rust -> Haskell ----

-- | Reads the array whose (pointer, length) is at src + off.
peekArray :: Int -> (Ptr () -> IO a) -> Ptr b -> Int -> IO [a]
peekArray sz f src off = do
  p <- peekByteOff src off :: IO (Ptr ())
  n <- peekByteOff src (off + w) :: IO CSize
  mapM (\i -> f (p `plusPtr` (i * sz))) [0 .. fromIntegral n - 1]

peekStr :: Ptr a -> IO String
peekStr src = do
  p <- peekByteOff src 0 :: IO (Ptr Word8)
  n <- peekByteOff src w :: IO CSize
  if n == 0 then return "" else
    T.unpack . T.decodeUtf8 <$> BS.packCStringLen (castPtr p, fromIntegral n)

peekSpine :: Ptr a -> IO CSpine
peekSpine src = CSpine <$> peekStr src <*> peekArray sizeExpr peekExpr src (2 * w)

peekEquation :: Ptr a -> IO CEquation
peekEquation src =
  CEquation <$> peekSpine src
            <*> peekSpine (src `plusPtr` (4 * w))
            <*> ((/= (0 :: Word8)) <$> peekByteOff src (8 * w))

peekDecl :: Ptr a -> IO CDecl
peekDecl src = do
  n  <- peekStr src
  pt <- peekByteOff src (2 * w) :: IO (Ptr ())
  t  <- if pt == nullPtr then return Nothing else Just <$> peekExpr pt
  CDecl n t <$> peekArray sizeEquation peekEquation src (3 * w)

peekExpr :: Ptr a -> IO CExpr
peekExpr src =
  CExpr <$> peekArray sizeDecl peekDecl src 0
        <*> peekArray sizeDecl peekDecl src (2 * w)
        <*> peekSpine (src `plusPtr` (4 * w))
