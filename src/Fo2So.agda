module Fo2So where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; pi )
import Syntax as FO
import SOSyntax as SO

{-# FOREIGN AGDA2HS

import Prelude hiding ( pi )
import Syntax qualified as FO

#-}

--------------------------------------------------------------------------------

record Σ (A : Type) (B : A → Type) : Type where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B fst

open Σ

Ctx : Type
Ctx = SO.Tel
{-# COMPILE AGDA2HS Ctx #-}

Ty : @0 Ctx → Type
Ty Γ = SO.Env Γ → SO.Ty
{-# COMPILE AGDA2HS Ty #-}

Tm : (@0 Γ : Ctx) → @0 Ty Γ → Type
Tm Γ A = (ρ : SO.Env Γ) → SO.Tm (A ρ)
{-# COMPILE AGDA2HS Tm #-}

Sub : @0 Ctx → @0 Ctx → Type
Sub Δ Γ = SO.Env Δ → SO.Env Γ
{-# COMPILE AGDA2HS Sub #-}

postulate
  fo2soCtx : FO.Ctx → Ctx
  fo2soTy  : FO.Ty FO.Γ → Ty (fo2soCtx FO.Γ)
  fo2soTm  : FO.Tm FO.Γ FO.A → Tm (fo2soCtx FO.Γ) (fo2soTy FO.A)
  fo2soSub : FO.Sub FO.Δ FO.Γ → Sub (fo2soCtx FO.Δ) (fo2soCtx FO.Γ)

{-# COMPILE AGDA2HS fo2soCtx existing #-}
{-# COMPILE AGDA2HS fo2soTy existing #-}
{-# COMPILE AGDA2HS fo2soTm existing #-}
{-# COMPILE AGDA2HS fo2soSub existing #-}

{-# FOREIGN AGDA2HS

fo2soCtx :: FO.Ctx -> Ctx
fo2soCtx = \case
  FO.CNil -> cnil
  FO.CSnoc g a -> csnoc (fo2soCtx g) (fo2soTy a)

fo2soTy :: FO.Ty -> Ty
fo2soTy = \case
  FO.TySub a sub -> tysub (fo2soTy a) (fo2soSub sub)
  FO.Pi a b -> pi (fo2soTy a) (fo2soTy b)

fo2soSub :: FO.Sub -> Sub
fo2soSub = \case
  FO.SNil -> snil
  FO.SId -> sid
  FO.SComp sub1 sub2 -> scomp (fo2soSub sub1) (fo2soSub sub2)
  FO.SSnoc sub t -> ssnoc (fo2soSub sub) (fo2soTm t)
  FO.SFst sub -> sfst (fo2soSub sub)

fo2soTm :: FO.Tm -> Tm
fo2soTm = \case
  FO.TmSub t sub -> tmsub (fo2soTm t) (fo2soSub sub)
  FO.SSnd sub -> ssnd (fo2soSub sub)
  FO.Lam t -> lam (fo2soTm t)
  FO.App t u -> app (fo2soTm t) (fo2soTm u)

#-}

variable
  @0 Γ Δ Θ : Ctx
  @0 A B C : Ty _
  @0 t u v : Tm _ _
  @0 δ σ γ : Sub _ _

cnil : Ctx
cnil = SO.tnil
{-# COMPILE AGDA2HS cnil #-}
syntax cnil = •

csnoc : (Γ : Ctx) → Ty Γ → Ctx
csnoc = SO.tsnoc
{-# COMPILE AGDA2HS csnoc #-}
syntax csnoc Γ A = Γ ▷ A

sid : Sub Γ Γ
sid = λ ρ → ρ
{-# COMPILE AGDA2HS sid #-}
syntax sid = id

snil : Sub Γ •
snil = λ _ → SO.enil
{-# COMPILE AGDA2HS snil #-}
syntax snil = ε

scomp : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
scomp δ σ = λ ρ → δ (σ ρ)
{-# COMPILE AGDA2HS scomp #-}
syntax scomp δ σ = δ ⨾ σ

tysub : Ty Γ → Sub Δ Γ → Ty Δ
tysub a sub = λ env → a (sub env)
{-# COMPILE AGDA2HS tysub #-}
syntax tysub a sub = a [ sub ]T

tmsub : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]T)
tmsub t sub = λ env → t (sub env)
{-# COMPILE AGDA2HS tmsub #-}
syntax tmsub t sub = t [ sub ]

_^_ : ∀ δ A → Sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
δ ^ _ = λ ρ → δ (SO.π₁ ρ) SO., SO.π₂ ρ

ssnoc : (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T) → Sub Δ (Γ ▷ A)
ssnoc δ t = λ ρ → δ ρ SO., t ρ
{-# COMPILE AGDA2HS ssnoc #-}
syntax ssnoc δ t = δ , t

sfst : Sub Δ (Γ ▷ A) → Sub Δ Γ
sfst δ = λ ρ → SO.efst (δ ρ)
{-# COMPILE AGDA2HS sfst #-}
syntax sfst = π₁

ssnd  : (δ : Sub Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
ssnd δ = λ ρ → SO.esnd (δ ρ)
{-# COMPILE AGDA2HS ssnd #-}
syntax ssnd = π₂

pi : ∀ A → Ty (Γ ▷ A) → Ty Γ
pi a b = λ ρ → SO.Π (a ρ) λ τ → b (SO.esnoc ρ τ)
{-# COMPILE AGDA2HS pi #-}
syntax pi = Π

lam : Tm (Γ ▷ A) B → Tm Γ (Π A B)
lam t = λ ρ → SO.lam λ τ → t (SO.esnoc ρ τ)
{-# COMPILE AGDA2HS lam #-}

app : Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ id , u ]T)
app t u = λ ρ → SO.app (t ρ) (u ρ)
{-# COMPILE AGDA2HS app #-}

-- -- postulate
-- --   fo2so• : fo2soCtx FO.• ≡ •
-- --   {-# REWRITE fo2so• #-}
-- --   fo2so▷ : fo2soCtx (FO.Γ FO.▷ FO.A) ≡ fo2soCtx FO.Γ ▷ fo2soTy FO.A
-- --   {-# REWRITE fo2so▷ #-}
