{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Agda.Canonical.Canonical where

import Data.Aeson
import Data.Maybe
import Data.String (IsString (fromString))
import Data.Word
import Foreign.C (CString, newCString, peekCString)
import GHC.Generics (Generic, C1)
import qualified Agda.Compiler.Backend as Agda.Canonical
import Agda.Canonical.Types
import Agda.Interaction.Base (Rewrite)
import Agda.TypeChecking.Pretty
import Agda.Syntax.Common (InteractionId)

import Agda.Syntax.Common.Pretty qualified as P
import Agda.TypeChecking.Monad.Base (MonadTCM, TCM, liftTCM)
import Agda.Syntax.Position (Range)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Agda.TypeChecking.Monad.MetaVars

import Agda.TypeChecking.Monad.MetaVars (lookupInteractionId, lookupLocalMeta )

foreign import ccall "canonical" canonical :: CString -> CString -> Word64 -> Word64 -> IO CString

ty :: Type
ty =
  Type
    { bindings =
        [ ( "Sort",
            Type
              { bindings = [],
                codom =
                  Spine
                    { shead = "Sort",
                      sargs = []
                    }
              }
          ),
          ( "A",
            Type
              { bindings = [],
                codom =
                  Spine
                    { shead = "Sort",
                      sargs = []
                    }
              }
          ),
          ( "a",
            Type
              { bindings = [],
                codom =
                  Spine
                    { shead = "A",
                      sargs = []
                    }
              }
          )
        ],
      codom =
        Spine
          { shead = "A",
            sargs = []
          }
    }

call_canonical :: MonadTCM tcm => Rewrite -> InteractionId -> Range -> String -> tcm CanonicalResult
call_canonical norm ii rng args = do
  target <- liftTCM $ do
    metaId <- lookupInteractionId ii
    getMetaType metaId
  liftIO $ do
    ety <- newCString  (P.prettyShow target)
    name <- newCString "proof"
    res <- canonical ety name 1000 1
    fstr <- peekCString res
    return (CanonicalExpr fstr)



-- main :: IO ()
-- main = do
--   cstr <- newCString (show $ encode ty)
--   name <- newCString "proof"
--   res <- canonical cstr name 1000 1
--   fstr <- peekCString res
--   print (fromMaybe (Term {thead = [], targs = Spine {shead = "Error", sargs = []}}) (decode (fromString fstr)))
