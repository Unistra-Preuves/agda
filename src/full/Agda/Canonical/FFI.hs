module Agda.Canonical.FFI (runCanonical) where

import Control.Exception (bracket)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe qualified as BS (unsafeUseAsCStringLen)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Word (Word8, Word64)
import Foreign.C.Types (CSize (..))
import Foreign.Marshal.Pool (Pool, pooledMallocBytes, withPool)
import Foreign.Marshal.Utils (copyBytes)
import Foreign.Ptr (Ptr, castPtr, nullPtr, plusPtr)
import Foreign.Storable (peekByteOff, pokeByteOff, sizeOf)

import Agda.Canonical.Types

{-
  Interface with the canonical-agda crate (Canonical/crates/canonical-agda/src/lib.rs).

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
-}

data FfiDecl
data FfiResult

foreign import ccall safe "canonical_solve"
  c_canonical_solve :: Ptr FfiDecl -> Word64 -> CSize -> IO (Ptr FfiResult)

foreign import ccall unsafe "canonical_free"
  c_canonical_free :: Ptr FfiResult -> IO ()

w, sizeSpine, sizeEquation, sizeDecl, sizeExpr :: Int
w            = sizeOf (nullPtr :: Ptr ())
sizeSpine    = 4 * w
sizeEquation = 9 * w
sizeDecl     = 5 * w
sizeExpr     = 8 * w

{-
  Calls Canonical on the goal, with a timeout in seconds and the number of solutions.
  Returns [] if the search panicked.
-}
runCanonical :: CDecl -> Int -> Int -> IO [CExpr]
runCanonical goal timeout count = withPool $ \pool -> do
  g <- pooledMallocBytes pool sizeDecl
  pokeDecl pool g goal
  bracket (c_canonical_solve g (fromIntegral timeout) (fromIntegral count))
          c_canonical_free $ \r ->
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
