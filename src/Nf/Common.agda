module Nf.Common where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Agda.Builtin.Nat
import Syntax as I
open I.Vars

variable
  @0 i : Nat

data Var : (@0 Γ : I.Ctx) (@0 A : I.Ty Γ i) (@0 tᴵ : I.Tm Γ A) → Set where
  Vz : Var (Γ I.▷ A) (A I.[ I.wk ]T) I.vz
  Vs : Var Γ B t → Var (Γ I.▷ A) (B I.[ I.wk ]T) (t I.[ I.wk ])
{-# COMPILE AGDA2HS Var #-}

pattern vz = Vz
pattern vs = Vs

