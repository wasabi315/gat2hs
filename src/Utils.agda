open import Agda.Primitive
open import Agda.Builtin.Equality
import Agda.Builtin.Equality.Rewrite

module Utils where

-- This is obviously unsafe in generated Haskell code, but we explicitly don't
-- write a COMPILE pragma, so we get an error if we try to include this in
-- compiled code anyway!

{-# POLARITY unsafe-resurrect ++ ++ ++ #-}
postulate
  unsafe-resurrect : ∀ {ℓ} {A : Set ℓ} → @0 A → A
  unsafe-resurrect≡ : ∀ {ℓ} {A : Set ℓ} (x : A) → unsafe-resurrect x ≡ x
  {-# REWRITE unsafe-resurrect≡ #-}
