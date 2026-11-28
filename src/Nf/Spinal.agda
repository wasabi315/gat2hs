-- "Spinal" normal forms. Might be more convenient?
module Nf.Spinal where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Agda.Builtin.Nat
import Syntax as I
open I.Vars

open import Nf.Common

data Sp   : (@0 Γ : I.Ctx) (@0 A : I.Ty Γ i) (@0 B : I.Ty Γ j)
            (@0 t : I.Tm Γ A) (@0 u : I.Tm Γ B) → Set
data Elim : (@0 Γ : I.Ctx) (@0 A : I.Ty Γ i) (@0 B : I.Ty Γ j)
            (@0 t : I.Tm Γ A) (@0 u : I.Tm Γ B) → Set
data Nf   : (@0 Γ : I.Ctx) (@0 A : I.Ty Γ i) (@0 t : I.Tm Γ A) → Set
data TyNf : (@0 Γ : I.Ctx) (@0 i : Nat) (@0 A : I.Ty Γ i) → Set

-- Spine entry
data Elim where
  App   : Nf Γ A u → Elim Γ (I.Π A B) (B I.[ I.id I., u ]T) t (I.app t u)
  Fst   : Elim Γ (I.Σ A B) A t (I.fst t)
  Snd   : Elim Γ (I.Σ A B) (B I.[ I.id I., I.fst t ]T) t (I.snd t)
  Lower : Elim Γ (I.Lift A) A t (I.lower t)

data Sp where
  SNil  : Sp Γ A A t t
  SCons : Elim Γ A B t u → Sp Γ B C u v → Sp Γ A C t v
pattern []       = SNil
pattern _,-_ δ t = SCons δ t

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
  U    : (@0 i : Nat) → TyNf Γ (suc i) (I.U i)
  El   : Var Γ A t → Sp Γ A (I.U i) t u → TyNf Γ i (I.El u)
  Lift : TyNf Γ i A → TyNf Γ (suc i) (I.Lift A)

{-# COMPILE AGDA2HS Sp   #-}
{-# COMPILE AGDA2HS Elim #-}
{-# COMPILE AGDA2HS Nf   #-}
{-# COMPILE AGDA2HS TyNf #-}
