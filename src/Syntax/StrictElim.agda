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

module Elim
  (ctx : Type) (sub : @0 ctx → @0 ctx → Type)
  (ty : @0 ctx → @0 Nat → Type) (tm : {@0 i : Nat} (@0 Γ : ctx) → @0 ty Γ i → Type)

  (id   : ∀ {@0 Γ} → sub Γ Γ)
  (comp : ∀ {@0 Δ Γ Θ} → sub Δ Γ → sub Θ Δ → sub Θ Γ)
  (let _⨾_ = comp)
  (@0 @rewrite id⨾ : ∀ {@0 Δ Γ} {@0 δ : sub Δ Γ} → id ⨾ δ ≡ δ)
  (@0 @rewrite ⨾id : ∀ {@0 Δ Γ} {@0 δ : sub Δ Γ} → δ ⨾ id ≡ δ)
  (@0 @rewrite ⨾⨾  : ∀ {@0 Δ Γ Θ Λ} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ} {@0 γ : sub Λ Θ}
    → (δ ⨾ σ) ⨾ γ ≡ δ ⨾ (σ ⨾ γ))

  (tysub : ∀ {@0 Γ Δ i} → ty Γ i → sub Δ Γ → ty Δ i)
  (tmsub : ∀ {@0 Γ Δ i A} → tm {i} Γ A → ∀ δ → tm Δ (tysub A δ))
  (let _[_]T = tysub; _[_] = tmsub)
  (@0 @rewrite [id]T : ∀ {@0 Γ i} {@0 A : ty Γ i} → A [ id ]T ≡ A)
  (@0 @rewrite [id]  : ∀ {@0 Γ i A} {@0 t : tm {i} Γ A} → t [ id ] ≡ t)
  (@0 @rewrite [][]T : ∀ {@0 Δ Γ Θ i} {@0 A : ty Γ i} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ}
    → A [ δ ]T [ σ ]T ≡ A [ δ ⨾ σ ]T)
  (@0 @rewrite [][]  : ∀ {@0 Δ Γ Θ i A} {@0 t : tm {i} Γ A} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ}
    → _[_] {A = ⟨ _ ⟩} (t [ δ ]) σ ≡ t [ δ ⨾ σ ])

  (cnil : ctx) (csnoc : ∀ {@0 i} (Γ : ctx) → ty Γ i → ctx)
  (let • = cnil; _▷_ = csnoc)

  (snil  : ∀ {@0 Δ} → sub Δ •)
  (ssnoc : ∀ {@0 Δ Γ i A} (δ : sub Δ Γ) → tm {i} Δ (A [ δ ]T) → sub Δ (Γ ▷ A))
  (let ε = snil; _,_ = ssnoc)
  (sfst  : ∀ {@0 Δ Γ i} {@0 A : ty Γ i} → sub Δ (Γ ▷ A) → sub Δ Γ)
  (let π₁ = sfst)
  (ssnd  : ∀ {@0 Δ Γ i A} (δ : sub Δ (Γ ▷ A)) → tm {i} Δ (A [ π₁ δ ]T))
  (let π₂ = ssnd)
  (@0 •η : ∀ {@0 Δ} {@0 δ : sub Δ cnil} → δ ≡ ε)
  (@0 @rewrite ,⨾ : ∀ {@0 Δ Γ Θ i A} {@0 δ : sub Δ Γ} {@0 σ : sub Θ Δ} {@0 t : tm {i} Δ (A [ δ ]T)}
    → _≡_ {A = sub Θ (Γ ▷ A)} ((δ , t) ⨾ σ) ((δ ⨾ σ) , (t [ σ ])))
  (@0 @rewrite ▷β₁ : ∀ {@0 Δ Γ i A} {@0 δ : sub Δ Γ} {@0 t : tm {i} Δ (A [ δ ]T)}
    → π₁ {A = A} (δ , t) ≡ δ)
  (@0 @rewrite ▷β₂ : ∀ {@0 Δ Γ i A} {@0 δ : sub Δ Γ} {@0 t : tm {i} Δ (A [ δ ]T)}
    → π₂ {A = A} (δ , t) ≡ t)
  (@0 @rewrite π₁⨾ : ∀ {@0 Δ Γ Θ i} {@0 A : ty Γ i} {@0 δ : sub Δ (Γ ▷ A)} {@0 σ : sub Θ Δ}
    → π₁ δ ⨾ σ ≡ π₁ (δ ⨾ σ))
  (@0 @rewrite π₂⨾ : ∀ {@0 Δ Γ Θ i} {@0 A : ty Γ i} {@0 δ : sub Δ (Γ ▷ A)} {@0 σ : sub Θ Δ}
    → _[_] {A = ⟨ _ ⟩} (π₂ δ) σ ≡ π₂ (δ ⨾ σ))
  (@0 @rewrite ▷η : ∀ {@0 Δ Γ i} {@0 A : ty Γ i} {@0 δ : sub Δ (Γ ▷ A)} → π₁ δ , π₂ δ ≡ δ)

  (pi : ∀ {@0 Γ i} → (A : ty Γ i) → ty (Γ ▷ A) i → ty Γ i)
  (let Π = pi)
  (lam : ∀ {@0 Γ i A B} → tm {i} (Γ ▷ A) B → tm Γ (Π A B))
  (app : ∀ {@0 Γ i A B} → tm {i} Γ (Π A B) → (u : tm Γ A) → tm Γ (B [ id , u ]T))

  (let wk : ∀ {@0 Γ i} {@0 A : ty Γ i} → sub (Γ ▷ A) Γ
       wk = π₁ id
       vz : ∀ {@0 Γ i A} → tm {i} (Γ ▷ A) (A [ wk ]T)
       vz = π₂ id
       _^_ : ∀ {@0 Δ Γ i} δ (A : ty Γ i) → sub (Δ ▷ (A [ δ ]T)) (Γ ▷ A)
       δ ^ _ = (δ ⨾ wk) , vz)

  (@0 @rewrite Π[] : ∀ {@0 Δ Γ i} {@0 A : ty Γ i} {@0 B} {@0 δ : sub Δ Γ}
    → Π A B [ δ ]T ≡ Π (A [ δ ]T) (B [ δ ^ A ]T))
  (@0 @rewrite lam[] : ∀ {@0 Δ Γ i A B} {@0 t : tm {i} (Γ ▷ A) B} {@0 δ : sub Δ Γ}
    → lam t [ δ ] ≡ lam (t [ δ ^ A ]))
  (@0 @rewrite app[] : ∀ {@0 Δ Γ i A B} {@0 t : tm {i} Γ (Π A B)} {@0 u : tm Γ A} {@0 δ : sub Δ Γ}
    → _[_] {A = ⟨ _ ⟩} (app t u) δ ≡ app (t [ δ ]) (u [ δ ]))

  (@0 @rewrite Πβ : ∀ {@0 Γ i A B} {@0 t : tm {i} (Γ ▷ A) B} {@0 u : tm Γ A}
    → app (lam t) u ≡ t [ id , u ])
  (@0 Πη : ∀ {@0 Γ i A B} {@0 t : tm {i} Γ (Π A B)}
    → t ≡ lam (app (t [ wk ]) vz))

  (sigma : ∀ {@0 Γ i} → (A : ty Γ i) → ty (Γ ▷ A) i → ty Γ i)
  (let Σ = sigma)
  (pair : ∀ {@0 Γ i A} (@0 B : ty (Γ ▷ A) i)
    → (t : tm Γ A) → tm Γ (B [ id , t ]T) → tm Γ (Σ A B))
  (fst : ∀ {@0 Γ i A B} → tm {i} Γ (Σ A B) → tm Γ A)
  (snd : ∀ {@0 Γ i A B} → (t : tm {i} Γ (Σ A B)) → tm Γ (B [ id , fst t ]T))

  (@0 @rewrite Σ[] : ∀ {@0 Δ Γ i} {@0 A : ty Γ i} {@0 B} {@0 δ : sub Δ Γ}
    → Σ A B [ δ ]T ≡ Σ (A [ δ ]T) (B [ δ ^ A ]T))
  (@0 @rewrite pair[] : ∀ {@0 Δ Γ i A B} {@0 t : tm {i} Γ A} {@0 u : tm Γ (B [ id , t ]T)} {@0 δ : sub Δ Γ}
    → pair B t u [ δ ] ≡ pair (B [ δ ^ A ]T) (t [ δ ]) (u [ δ ]))
  (@0 @rewrite fst[] : ∀ {@0 Δ Γ i A B} {@0 t : tm {i} Γ (Σ A B)} {@0 δ : sub Δ Γ}
    → fst {B = B} t [ δ ] ≡ fst (t [ δ ]))
  (@0 @rewrite snd[] : ∀ {@0 Δ Γ i A B} {@0 t : tm {i} Γ (Σ A B)} {@0 δ : sub Δ Γ}
    → _[_] {A = ⟨ _ ⟩} (snd {B = B} t) δ ≡ snd (t [ δ ]))

  (@0 @rewrite Σβ₁ : ∀ {@0 Γ i A B} {@0 t : tm {i} Γ A} {@0 u : tm Γ (B [ id , t ]T)}
    → fst (pair B t u) ≡ t)
  (@0 @rewrite Σβ₂ : ∀ {@0 Γ i A B} {@0 t : tm {i} Γ A} {@0 u : tm Γ (B [ id , t ]T)}
    → snd (pair B t u) ≡ u)
  (@0 @rewrite Ση : ∀ {@0 Γ i A B} {@0 t : tm {i} Γ (Σ A B)}
    → pair B (fst t) (snd t) ≡ t)

  (u : ∀ {@0 Γ} (@0 i) → ty Γ (suc i))
  (el : ∀ {@0 Γ i} → tm Γ (u i) → ty Γ i)
  (code : ∀ {@0 Γ i} → ty Γ i → tm Γ (u i))
  (let U = u; El = el; Code = code)

  (@0 @rewrite U[] : ∀ {@0 Δ Γ i} {@0 δ : sub Δ Γ}
    → U i [ δ ]T ≡ U i)
  (@0 @rewrite El[] : ∀ {@0 Δ Γ i} {@0 t : tm Γ (u i)} {@0 δ : sub Δ Γ}
    → El t [ δ ]T ≡ El (t [ δ ]))
  (@0 @rewrite Code[] : ∀ {@0 Δ Γ i} {@0 A : ty Γ i} {@0 δ : sub Δ Γ}
    → Code A [ δ ] ≡ Code (A [ δ ]T))

  (@0 @rewrite Uβ : ∀ {@0 Γ i} {@0 A : ty Γ i}
    → El (Code A) ≡ A)
  (@0 @rewrite Uη : ∀ {@0 Γ i} {@0 t : tm Γ (u i)}
    → Code (El t) ≡ t)

  (lift : ∀ {@0 Γ i} → ty Γ i → ty Γ (suc i))
  (let Lift = lift)
  (raise : ∀ {@0 Γ i A} → tm {i} Γ A → tm Γ (lift A))
  (lower : ∀ {@0 Γ i A} → tm {suc i} Γ (lift A) → tm Γ A)

  (@0 @rewrite Lift[] : ∀ {@0 Δ Γ i} {@0 A : ty Γ i} {@0 δ : sub Δ Γ}
    → Lift A [ δ ]T ≡ Lift (A [ δ ]T))
  (@0 @rewrite raise[] : ∀ {@0 Δ Γ i A} {@0 t : tm {i} Γ A} {@0 δ : sub Δ Γ}
    → raise t [ δ ] ≡ raise (t [ δ ]))
  (@0 @rewrite lower[] : ∀ {@0 Δ Γ i A} {@0 t : tm {suc i} Γ (Lift A)} {@0 δ : sub Δ Γ}
    → lower t [ δ ] ≡ lower (t [ δ ]))

  (@0 @rewrite Liftβ : ∀ {@0 Γ i A} {@0 t : tm {i} Γ A}
    → lower (raise t) ≡ t)
  (@0 @rewrite Liftη : ∀ {@0 Γ i A} {@0 t : tm Γ (Lift {i = i} A)}
    → raise (lower t) ≡ t)

  (@0 dummy : ⊤) -- to work around the Agda issue #8965
  where

  elimCtx : FO.Ctx → ctx

  postulate
    elimSub : FO.Sub FO.Δ FO.Γ → sub (elimCtx FO.Δ) (elimCtx FO.Γ)
    elimTy  : FO.Ty FO.Γ FO.i → ty (elimCtx FO.Γ) FO.i
    elimTm  : FO.Tm FO.Γ FO.A → tm (elimCtx FO.Γ) (elimTy FO.A)

  elimCtx FO.•       = •
  elimCtx (g FO.▷ a) = elimCtx g ▷ elimTy a

  {-# COMPILE AGDA2HS elimCtx          #-}
  {-# COMPILE AGDA2HS elimSub existing #-}
  {-# COMPILE AGDA2HS elimTy  existing #-}
  {-# COMPILE AGDA2HS elimTm  existing #-}

  postulate
    elimId : elimSub (FO.id {Γ = FO.Γ}) ≡ id
    {-# REWRITE elimId #-}
    elimComp : elimSub (FO.δ FO.⨾ FO.σ) ≡ elimSub FO.δ ⨾ elimSub FO.σ
    {-# REWRITE elimComp #-}
    elim[]T : elimTy (FO.A FO.[ FO.δ ]T) ≡ elimTy FO.A [ elimSub FO.δ ]T
    {-# REWRITE elim[]T #-}
    elim[] : elimTm (FO.t FO.[ FO.δ ]) ≡ elimTm FO.t [ elimSub FO.δ ]
    {-# REWRITE elim[] #-}
    elimε : elimSub (FO.ε {Δ = FO.Δ}) ≡ ε
    {-# REWRITE elimε #-}
    elim, : elimSub (FO.δ FO., FO.t) ≡ elimSub FO.δ , elimTm FO.t
    {-# REWRITE elim, #-}
    elimπ₁ : elimSub (FO.π₁ FO.δ) ≡ π₁ (elimSub FO.δ)
    {-# REWRITE elimπ₁ #-}
    elimπ₂ : elimTm (FO.π₂ FO.δ) ≡ π₂ (elimSub FO.δ)
    {-# REWRITE elimπ₂ #-}
    elimΠ : elimTy (FO.Π FO.A FO.B) ≡ Π (elimTy FO.A) (elimTy FO.B)
    {-# REWRITE elimΠ #-}
    elimLam : elimTm (FO.lam FO.t) ≡ lam (elimTm FO.t)
    {-# REWRITE elimLam #-}
    elimApp : elimTm (FO.app FO.t FO.u) ≡ app (elimTm FO.t) (elimTm FO.u)
    {-# REWRITE elimApp #-}
    elimΣ : elimTy (FO.Σ FO.A FO.B) ≡ Σ (elimTy FO.A) (elimTy FO.B)
    {-# REWRITE elimΣ #-}
    elimPair : elimTm (FO.pair FO.B FO.t FO.u) ≡ pair (elimTy FO.B) (elimTm FO.t) (elimTm FO.u)
    {-# REWRITE elimPair #-}
    elimFst : elimTm (FO.fst FO.t) ≡ fst (elimTm FO.t)
    {-# REWRITE elimFst #-}
    elimSnd : elimTm (FO.snd FO.t) ≡ snd (elimTm FO.t)
    {-# REWRITE elimSnd #-}
    elimU : elimTy (FO.U {FO.Γ} FO.i) ≡ u FO.i
    {-# REWRITE elimU #-}
    elimEl : elimTy (FO.El FO.t) ≡ el (elimTm FO.t)
    {-# REWRITE elimEl #-}
    elimCode : elimTm (FO.Code FO.A) ≡ code (elimTy FO.A)
    {-# REWRITE elimCode #-}
    elimLift : elimTy (FO.Lift FO.A) ≡ Lift (elimTy FO.A)
    {-# REWRITE elimLift #-}
    elimRaise : elimTm (FO.raise FO.t) ≡ raise (elimTm FO.t)
    {-# REWRITE elimRaise #-}
    elimLower : elimTm (FO.lower FO.t) ≡ lower (elimTm FO.t)
    {-# REWRITE elimLower #-}

{-# FOREIGN AGDA2HS

elimSub ::
  sub -> (sub -> sub -> sub) ->
  (ty -> sub -> ty) -> (tm -> sub -> tm) ->
  ctx -> (ctx -> ty -> ctx) ->
  sub -> (sub -> tm -> sub) ->
  (sub -> sub) -> (sub -> tm) ->
  (ty -> ty -> ty) -> (tm -> tm) -> (tm -> tm -> tm) ->
  (ty -> ty -> ty) -> (tm -> tm -> tm) -> (tm -> tm) -> (tm -> tm) ->
  ty -> (tm -> ty) -> (ty -> tm) ->
  (ty -> ty) -> (tm -> tm) -> (tm -> tm) ->
  FO.Sub -> sub
elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower = \case
  FO.SNil -> snil
  FO.SId -> id
  FO.SComp sub1 sub2 ->
    comp
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower sub1)
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower sub2)
  FO.SSnoc sub t ->
    ssnoc
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower sub)
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)
  FO.SFst sub ->
    sfst
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower sub)

elimTy ::
  sub -> (sub -> sub -> sub) ->
  (ty -> sub -> ty) -> (tm -> sub -> tm) ->
  ctx -> (ctx -> ty -> ctx) ->
  sub -> (sub -> tm -> sub) ->
  (sub -> sub) -> (sub -> tm) ->
  (ty -> ty -> ty) -> (tm -> tm) -> (tm -> tm -> tm) ->
  (ty -> ty -> ty) -> (tm -> tm -> tm) -> (tm -> tm) -> (tm -> tm) ->
  ty -> (tm -> ty) -> (ty -> tm) ->
  (ty -> ty) -> (tm -> tm) -> (tm -> tm) ->
  FO.Ty -> ty
elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower = \case
  FO.TySub a sub ->
    tysub
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower a)
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower sub)
  FO.Pi a b ->
    pi
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower a)
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower b)
  FO.Sigma a b ->
    sigma
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower a)
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower b)
  FO.U -> _U
  FO.El t ->
    el
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)
  FO.Lift a ->
    lift
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower a)

elimTm ::
  sub -> (sub -> sub -> sub) ->
  (ty -> sub -> ty) -> (tm -> sub -> tm) ->
  ctx -> (ctx -> ty -> ctx) ->
  sub -> (sub -> tm -> sub) ->
  (sub -> sub) -> (sub -> tm) ->
  (ty -> ty -> ty) -> (tm -> tm) -> (tm -> tm -> tm) ->
  (ty -> ty -> ty) -> (tm -> tm -> tm) -> (tm -> tm) -> (tm -> tm) ->
  ty -> (tm -> ty) -> (ty -> tm) ->
  (ty -> ty) -> (tm -> tm) -> (tm -> tm) ->
  FO.Tm -> tm
elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower = \case
  FO.TmSub t sub ->
    tmsub
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower sub)
  FO.SSnd sub ->
    ssnd
      (elimSub id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower sub)
  FO.Lam t ->
    lam
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)
  FO.App t u ->
    app
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower u)
  FO.Pair t u ->
    pair
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower u)
  FO.Fst t ->
    fst
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)
  FO.Snd t ->
    snd
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)
  FO.Code a ->
    code
      (elimTy id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower a)
  FO.Raise t ->
    raise
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)
  FO.Lower t ->
    lower
      (elimTm id comp tysub tmsub cnil csnoc snil ssnoc sfst ssnd pi lam app sigma pair fst snd _U el code lift raise lower t)

#-}
