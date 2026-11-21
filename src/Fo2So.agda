{-# OPTIONS --local-rewriting #-}

module Fo2So where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; pi )
import Syntax as FO
import Syntax.StrictElim as FO
import SOSyntax as SO
import SOSyntax.Tel as SO

{-# FOREIGN AGDA2HS

import Prelude hiding ( pi, id, (^) )
import Syntax qualified as FO

#-}

--------------------------------------------------------------------------------

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

variable
  @0 Γ Δ Θ : Ctx
  @0 A B C : Ty _
  @0 t u v : Tm _ _
  @0 δ σ γ : Sub _ _

cnil : Ctx
cnil = SO.•
{-# COMPILE AGDA2HS cnil #-}
• = cnil
{-# COMPILE AGDA2HS • inline #-}

_▷_ : (Γ : Ctx) → Ty Γ → Ctx
_▷_ = SO._▷_
{-# COMPILE AGDA2HS _▷_ #-}

id : Sub Γ Γ
id = λ ρ → ρ
{-# COMPILE AGDA2HS id #-}

ε : Sub Γ •
ε = λ _ → SO.ε
{-# COMPILE AGDA2HS ε #-}

_⨾_ : Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
_⨾_ δ σ = λ ρ → δ (σ ρ)
{-# COMPILE AGDA2HS _⨾_ #-}

tysub : Ty Γ → Sub Δ Γ → Ty Δ
tysub a sub = λ env → a (sub env)
{-# COMPILE AGDA2HS tysub #-}
_[_]T = tysub
{-# COMPILE AGDA2HS _[_]T inline #-}

tmsub : Tm Γ A → ∀ δ → Tm Δ (A [ δ ]T)
tmsub t sub = λ env → t (sub env)
{-# COMPILE AGDA2HS tmsub #-}
_[_] = tmsub
{-# COMPILE AGDA2HS _[_] inline #-}

_^_ : ∀ δ A → Sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
δ ^ _ = λ ρ → δ (SO.π₁ ρ) SO., SO.π₂ ρ
{-# COMPILE AGDA2HS _^_ #-}

ssnoc : (δ : Sub Δ Γ) → Tm Δ (A [ δ ]T) → Sub Δ (Γ ▷ A)
ssnoc δ t = λ ρ → δ ρ SO., t ρ
{-# COMPILE AGDA2HS ssnoc #-}
_,_ = ssnoc
{-# COMPILE AGDA2HS _,_ inline #-}

π₁ : Sub Δ (Γ ▷ A) → Sub Δ Γ
π₁ δ = λ ρ → SO.π₁ (δ ρ)
{-# COMPILE AGDA2HS π₁ #-}

_ : {δ : Sub Δ Γ} {t : Tm Δ (A [ δ ]T)} → π₁ {A = A} (δ , t) ≡ δ
_ = refl

π₂ : (δ : Sub Δ (Γ ▷ A)) → Tm Δ (A [ π₁ δ ]T)
π₂ δ = λ ρ → SO.π₂ (δ ρ)
{-# COMPILE AGDA2HS π₂ #-}

_ : {δ : Sub Δ Γ} {t : Tm Δ (A [ δ ]T)} → π₂ {A = A} (δ , t) ≡ t
_ = refl

pi : ∀ A → Ty (Γ ▷ A) → Ty Γ
pi a b = λ ρ → SO.Π (a ρ) λ τ → b (ρ SO., τ)
{-# COMPILE AGDA2HS pi #-}
Π = pi
{-# COMPILE AGDA2HS Π inline #-}

lam : Tm (Γ ▷ A) B → Tm Γ (Π A B)
lam t = λ ρ → SO.lam λ τ → t (ρ SO., τ)
{-# COMPILE AGDA2HS lam #-}

app : Tm Γ (Π A B) → (u : Tm Γ A) → Tm Γ (B [ id , u ]T)
app t u = λ ρ → SO.app (t ρ) (u ρ)
{-# COMPILE AGDA2HS app #-}

postulate
  •η : {δ : Sub Γ •} → δ ≡ ε
  Πη : {t : Tm Γ (Π A B)} → _≡_ {A = Tm Γ (Π A B)} t (λ ρ → SO.lam (SO.app (t ρ)))

_ : {t : Tm (Γ ▷ A) B} {u : Tm Γ A}
  → app {B = B} (lam t) u ≡ λ ρ → SO.app (SO.lam (λ τ → t (ρ SO., τ))) (u ρ)
_ = refl

-- fo2soCtx : FO.Ctx → Ctx
-- fo2soCtx =
--   FO.elimCtx
--     Ctx Sub Ty Tm
--     id _⨾_ refl refl refl
--     tysub tmsub refl refl refl refl
--     • _▷_
--     ε _,_ π₁ π₂ •η refl refl refl refl refl refl
--     Π lam (λ {Γ} {A} {B} → app {Γ} {A} {B}) refl refl refl refl (λ {Γ} {A} {B} {t} → Πη {Γ} {A} {B} {t})
-- {-# COMPILE AGDA2HS fo2soCtx #-}

-- fo2soSub : FO.Sub FO.Δ FO.Γ → Sub (fo2soCtx FO.Δ) (fo2soCtx FO.Γ)
-- fo2soSub =
--   FO.elimSub
--     Ctx Sub Ty Tm
--     id _⨾_ refl refl refl
--     tysub tmsub refl refl refl refl
--     • _▷_
--     ε _,_ π₁ π₂ •η refl refl refl refl refl refl
--     Π lam (λ {Γ} {A} {B} → app {Γ} {A} {B}) refl refl refl refl (λ {Γ} {A} {B} {t} → Πη {Γ} {A} {B} {t})
-- {-# COMPILE AGDA2HS fo2soSub #-}

-- fo2soTy  : FO.Ty FO.Γ → Ty (fo2soCtx FO.Γ)
-- fo2soTy =
--   FO.elimTy
--     Ctx Sub Ty Tm
--     id _⨾_ refl refl refl
--     tysub tmsub refl refl refl refl
--     • _▷_
--     ε _,_ π₁ π₂ •η refl refl refl refl refl refl
--     Π lam (λ {Γ} {A} {B} → app {Γ} {A} {B}) refl refl refl refl (λ {Γ} {A} {B} {t} → Πη {Γ} {A} {B} {t})
-- {-# COMPILE AGDA2HS fo2soTy #-}

-- fo2soTm  : FO.Tm FO.Γ FO.A → Tm (fo2soCtx FO.Γ) (fo2soTy FO.A)
-- fo2soTm =
--   FO.elimTm
--     Ctx Sub Ty Tm
--     id _⨾_ refl refl refl
--     tysub tmsub refl refl refl refl
--     • _▷_
--     ε _,_ π₁ π₂ •η refl refl refl refl refl refl
--     Π lam (λ {Γ} {A} {B} → app {Γ} {A} {B}) refl refl refl refl (λ {Γ} {A} {B} {t} → Πη {Γ} {A} {B} {t})
-- {-# COMPILE AGDA2HS fo2soTm #-}
