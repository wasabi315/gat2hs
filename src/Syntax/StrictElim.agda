{-# OPTIONS --local-rewriting #-}

module Syntax.StrictElim where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Agda.Builtin.Equality.Rewrite renaming ( primRewriteNoMatch to ⟨_⟩ )
open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; pi )
import Syntax as FO

{-# FOREIGN AGDA2HS

import Syntax qualified as FO

#-}

--------------------------------------------------------------------------------

module _
  (ctx : Type) (sub : @0 ctx → @0 ctx → Type)
  (ty : @0 ctx → Type) (tm : (@0 Γ : ctx) → @0 ty Γ → Type)

  (id   : ∀ {@0 Γ} → sub Γ Γ)
  (comp : ∀ {@0 Δ Γ Θ} → sub Δ Γ → sub Θ Δ → sub Θ Γ)
  (let _⨾_ = comp)
  (@0 @rewrite id⨾ : ∀ {@0 Δ Γ} {@0 δ : sub Δ Γ} → id ⨾ δ ≡ δ)
  (@0 @rewrite ⨾id : ∀ {@0 Δ Γ} {@0 δ : sub Δ Γ} → δ ⨾ id ≡ δ)
  (@0 @rewrite ⨾⨾  : ∀ {@0 Δ Γ Θ Λ} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ} {@0 γ : sub Λ Θ}
    → (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ))

  (tysub : ∀ {@0 Γ Δ} → ty Γ → sub Δ Γ → ty Δ)
  (tmsub : ∀ {@0 Γ Δ A} → tm Γ A → ∀ δ → tm Δ (tysub A δ))
  (let _[_]T = tysub; _[_] = tmsub)
  (@0 @rewrite [id]T : ∀ {@0 Γ} {@0 A : ty Γ} → A [ id ]T ≡ A)
  (@0 @rewrite [id]  : ∀ {@0 Γ A} {@0 t : tm Γ A} → t [ id ] ≡ t)
  (@0 @rewrite [][]T : ∀ {@0 Δ Γ Θ A} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ}
    → A [ δ ]T [ σ ]T ≡ A [ δ ⨾ σ ]T)
  (@0 @rewrite [][]  : ∀ {@0 Δ Γ Θ A} {@0 t : tm Γ A} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ}
    → _[_] {A = ⟨ _ ⟩} (t [ δ ]) σ ≡ t [ δ ⨾ σ ])

  (cnil : ctx) (csnoc : (Γ : ctx) → ty Γ → ctx)
  (let • = cnil; _▷_ = csnoc)

  (snil  : ∀ {@0 Δ} → sub Δ •)
  (ssnoc : ∀ {@0 Δ Γ A} (δ : sub Δ Γ) → tm Δ (A [ δ ]T) → sub Δ (Γ ▷ A))
  (let ε = snil; _,_ = ssnoc)
  (sfst  : ∀ {@0 Δ Γ A} → sub Δ (Γ ▷ A) → sub Δ Γ)
  (let π₁ = sfst)
  (ssnd  : ∀ {@0 Δ Γ A} (δ : sub Δ (Γ ▷ A)) → tm Δ (A [ π₁ δ ]T))
  (let π₂ = ssnd)
  (@0 •η : ∀ {@0 Δ} {@0 δ : sub Δ cnil} → δ ≡ ε)
  (@0 @rewrite ,⨾ : ∀ {@0 Δ Γ Θ A} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ} {@0 t : tm Δ (A [ δ ]T)}
    → _≡_ {A = sub Θ (Γ ▷ A)} ((δ , t) ⨾ σ) ((δ ⨾ σ) , (t [ σ ])))
  (@0 @rewrite ▷β₁ : ∀ {@0 Δ Γ A} {@0 δ : sub Δ Γ} {@0 t : tm Δ (A [ δ ]T)}
    → π₁ {A = A} (δ , t) ≡ δ)
  (@0 @rewrite ▷β₂ : ∀ {@0 Δ Γ A} {@0 δ : sub Δ Γ} {@0 t : tm Δ (A [ δ ]T)}
    → π₂ {A = A} (δ , t) ≡ t)
  (@0 @rewrite π₁⨾ : ∀ {@0 Δ Γ Θ A} {@0 δ : sub Δ (Γ ▷ A)} {@0 σ : sub Θ Δ}
    → π₁ δ ⨾ σ ≡ π₁ (δ ⨾ σ))
  (@0 @rewrite π₂⨾ : ∀ {@0 Δ Γ Θ A} {@0 δ : sub Δ (Γ ▷ A)} {@0 σ : sub Θ Δ}
    → _[_] {A = ⟨ _ ⟩} (π₂ δ) σ ≡ π₂ (δ ⨾ σ))
  (@0 @rewrite ▷η : ∀ {@0 Δ Γ A} {@0 δ : sub Δ (Γ ▷ A)} → π₁ δ , π₂ δ ≡ δ)

  (pi : ∀ {@0 Γ} → ∀ A → ty (Γ ▷ A) → ty Γ)
  (let Π = pi)
  (lam : ∀ {@0 Γ A B} → tm (Γ ▷ A) B → tm Γ (Π A B))
  (app : ∀ {@0 Γ A B} → tm Γ (Π A B) → (u : tm Γ A) → tm Γ (B [ id , u ]T))

  (let wk : ∀ {@0 Γ A} → sub (Γ ▷ A) Γ
       wk = π₁ id
       vz : ∀ {@0 Γ A} → tm (Γ ▷ A) (A [ wk ]T)
       vz = π₂ id
       _^_ : ∀ {@0 Δ Γ} δ A → sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
       δ ^ _ = (δ ⨾ wk) , vz)

  (@0 @rewrite Π[] : ∀ {@0 Δ Γ A B} {@0 δ : sub Δ Γ}
    → Π A B [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ^ A ]T))
  (@0 @rewrite lam[] : ∀ {@0 Δ Γ A B} {@0 t : tm (Γ ▷ A) B} {@0 δ : sub Δ Γ}
    → lam t [ δ ] ≡ lam (t [ δ ^ A ]))
  (@0 @rewrite app[] : ∀ {@0 Δ Γ A B} {@0 t : tm Γ (Π A B)} {@0 u : tm Γ A} {@0 δ : sub Δ Γ}
    → _[_] {A = ⟨ _ ⟩} (app t u) δ ≡ app (t [ δ ]) (u [ δ ]))

  (@0 @rewrite Πβ : ∀ {@0 Γ A B} {@0 t : tm (Γ ▷ A) B} {@0 u : tm Γ A}
    → app (lam t) u ≡ t [ id , u ])
  (@0 Πη : ∀ {@0 Γ A B} {@0 t : tm Γ (Π A B)}
    → t ≡ lam (app (t [ wk ]) vz))
  where

  elimCtx : FO.Ctx → ctx

  postulate
    elimSub : ∀ {@0 Δ Γ} → FO.Sub Δ Γ → sub (elimCtx Δ) (elimCtx Γ)
    elimTy  : ∀ {@0 Γ} → FO.Ty Γ → ty (elimCtx Γ)
    elimTm  : ∀ {@0 Γ A} → FO.Tm Γ A → tm (elimCtx Γ) (elimTy A)

  elimCtx FO.CNil        = •
  elimCtx (FO.CSnoc g a) = elimCtx g ▷ elimTy a

  {-# COMPILE AGDA2HS elimCtx          #-}
  {-# COMPILE AGDA2HS elimSub existing #-}
  {-# COMPILE AGDA2HS elimTy  existing #-}
  {-# COMPILE AGDA2HS elimTm  existing #-}

{-# FOREIGN AGDA2HS

elimSub ::
  sub -> (sub -> sub -> sub) ->
  (ty -> sub -> ty) -> (tm -> sub -> tm) ->
  ctx -> (ctx -> ty -> ctx) ->
  sub -> (sub -> tm -> sub) ->
  (sub -> sub) -> (sub -> tm) ->
  (ty -> ty -> ty) -> (tm -> tm) -> (tm -> tm -> tm) ->
  FO.Sub ->
  sub
elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app = \case
  FO.SNil -> snil
  FO.SId -> id
  FO.SComp sub1 sub2 ->
    comp
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sub1)
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sub2)
  FO.SSnoc sub t ->
    ssnoc
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sub)
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app t)
  FO.SFst sub ->
    sfst
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sub)

elimTy ::
  sub -> (sub -> sub -> sub) ->
  (ty -> sub -> ty) -> (tm -> sub -> tm) ->
  ctx -> (ctx -> ty -> ctx) ->
  sub -> (sub -> tm -> sub) ->
  (sub -> sub) -> (sub -> tm) ->
  (ty -> ty -> ty) -> (tm -> tm) -> (tm -> tm -> tm) ->
  FO.Ty ->
  ty
elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app = \case
  FO.TySub a sub ->
    tysub
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app a)
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sub)
  FO.Pi a b ->
    pi
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app a)
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app b)

elimTm ::
  sub -> (sub -> sub -> sub) ->
  (ty -> sub -> ty) -> (tm -> sub -> tm) ->
  ctx -> (ctx -> ty -> ctx) ->
  sub -> (sub -> tm -> sub) ->
  (sub -> sub) -> (sub -> tm) ->
  (ty -> ty -> ty) -> (tm -> tm) -> (tm -> tm -> tm) ->
  FO.Tm ->
  tm
elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app = \case
  FO.TmSub t sub ->
    tmsub
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app t)
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sub)
  FO.SSnd sub ->
    ssnd
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sub)
  FO.Lam t ->
    lam
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app t)
  FO.App t u ->
    app
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app t)
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app u)

#-}
