-- Traditional normal forms, mutually defined with neutrals
module Nf.Traditional where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Agda.Builtin.Nat
import Syntax as I
open I.Vars

open import Nf.Common

data Ne   : (@0 Γ : I.Ctx) (@0 A : I.Ty Γ i) (@0 t : I.Tm Γ A) → Set
data Nf   : (@0 Γ : I.Ctx) (@0 A : I.Ty Γ i) (@0 t : I.Tm Γ A) → Set
data TyNf : (@0 Γ : I.Ctx) (@0 i : Nat) (@0 A : I.Ty Γ i) → Set

data Ne where
  VarNe : Var Γ A t → Ne Γ A t
  App   : Ne Γ (I.Π A B) t → Nf Γ A u → Ne Γ (B I.[ I.id I., u ]T) (I.app t u)
  Fst   : Ne Γ (I.Σ A B) t → Ne Γ A (I.fst t)
  Snd   : Ne Γ (I.Σ A B) t → Ne Γ (B I.[ I.id I., I.fst t ]T) (I.snd t)
  Lower : Ne Γ (I.Lift A) t → Ne Γ A (I.lower t)

pattern var x   = VarNe x
pattern app t u = App t u
pattern fst t   = Fst t
pattern snd t   = Snd t
pattern lower t = Lower t

data Nf where
  Lam   : Nf (Γ I.▷ A) B t → Nf Γ (I.Π A B) (I.lam t)
  Pair  : TyNf (Γ I.▷ A) i B → Nf Γ A t → Nf Γ (B I.[ I.id I., t ]T) u
        → Nf Γ (I.Σ A B) (I.pair B t u)
  Code  : TyNf Γ i A → Nf Γ (I.U i) (I.Code A)
  Raise : Nf Γ A t → Nf Γ (I.Lift A) (I.raise t)

pattern lam t      = Lam t
pattern pair B t u = Pair B t u
pattern raise t    = Raise t

data TyNf where
  Π    : TyNf Γ i A → TyNf (Γ I.▷ A) i B → TyNf Γ i (I.Π A B)
  Σ    : TyNf Γ i A → TyNf (Γ I.▷ A) i B → TyNf Γ i (I.Σ A B)
  U    : (i : Nat) → TyNf Γ (suc i) (I.U i)
  El   : Ne Γ (I.U i) t → TyNf Γ i (I.El t)
  Lift : TyNf Γ i A → TyNf Γ (suc i) (I.Lift A)

{-# COMPILE AGDA2HS Ne   #-}
{-# COMPILE AGDA2HS Nf   #-}
{-# COMPILE AGDA2HS TyNf #-}
