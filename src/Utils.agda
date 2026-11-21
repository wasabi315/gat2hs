open import Agda.Primitive
open import Agda.Builtin.Equality
import Agda.Builtin.Equality.Rewrite

module Utils where

-- 'Resurrect' can be thought of a definitional version of the following record:
--
-- > record Resurrect (@0 A : Set) where
-- >   field
-- >     unwrap : A
--
-- 'Resurrect' is obviously unsafe in generated Haskell code, but we explicitly
-- don't write a COMPILE pragma, so we get an error if we try to include it in
-- the compiled code anyway!
{-# POLARITY Resurrect ++ #-}
postulate
  Resurrect : @0 Set → Set
  Resurrect≡ : (A : Set) → Resurrect A ≡ A
  {-# REWRITE Resurrect≡ #-}
