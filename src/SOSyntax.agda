module SOSyntax where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

#-}

open import Agda.Builtin.Equality.Rewrite
open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_; pi )

{-# FOREIGN AGDA2HS
import Prelude hiding ( pi, (^) )
#-}

--------------------------------------------------------------------------------

postulate
  Ty : Type
  Tm : @0 Ty → Type

variable
  @0 A B C D A₁ A₂ A₃ B₁ B₂ B₃  : Ty
  @0 t u v t₁ t₂ t₃ u₁ u₂ u₃ : Tm _
  @0 A[_] B[_] : Tm _ → Ty
  @0 t[_] u[_] : Tm _ → Tm _

-- Dependent functions
-- We use binary application because it behaves better with rewriting
postulate
  pi    : (A : Ty) → (Tm A → Ty) → Ty
  lam   : ((t : Tm A) → Tm (B[ t ])) → Tm (Π A B[_])
  app   : Tm (Π A B[_]) → (u : Tm A) → Tm (B[ u ])

syntax pi = Π

postulate
  Πβ : app (lam t[_]) u ≡ t[ u ]
  {-# REWRITE Πβ #-}
  Πη : {t : Tm (Π A B[_])} → t ≡ lam λ u → app t u

postulate
  Tel : Type
  Env : @0 Tel → Type

  tnil : Tel
  tsnoc : (Γ : Tel) → (Env Γ → Ty) → Tel

  enil  : Env •
  esnoc : {@0 Γ : Tel} {@0 A : Env Γ → Ty} (ρ : Env Γ) → Tm (A ρ) → Env (Γ ▷ A)
  efst  : ∀ {@0 Γ A} → Env (Γ ▷ A) → Env Γ
  esnd  : ∀ {@0 Γ A} → (ρ : Env (Γ ▷ A)) → Tm (A (efst ρ))

syntax tnil = •
syntax tsnoc Γ A = Γ ▷ A
syntax enil = ε
syntax esnoc ρ t = ρ , t
syntax efst = π₁
syntax esnd = π₂

{-# FOREIGN AGDA2HS

data Ty
  = Pi Ty (Tm -> Ty)

data Tm
  = Lam (Tm -> Tm)
  | App Tm Tm

pi  = Pi
lam = Lam
app = App

data Tel
  = TNil
  | TSnoc Tel (Env -> Ty)

data Env
  = ENil
  | ESnoc Env Tm

tnil = TNil
tsnoc = TSnoc
enil = ENil
esnoc = ESnoc
efst = \case
  ENil -> undefined
  ESnoc env _ -> env
esnd = \case
  ENil -> undefined
  ESnoc _ t -> t

#-}

{-# COMPILE AGDA2HS Ty existing #-}
{-# COMPILE AGDA2HS Tm existing #-}
{-# COMPILE AGDA2HS pi existing #-}
{-# COMPILE AGDA2HS lam existing #-}
{-# COMPILE AGDA2HS app existing #-}
{-# COMPILE AGDA2HS Tel existing #-}
{-# COMPILE AGDA2HS Env existing #-}
{-# COMPILE AGDA2HS tnil existing #-}
{-# COMPILE AGDA2HS tsnoc existing #-}
{-# COMPILE AGDA2HS enil existing #-}
{-# COMPILE AGDA2HS esnoc existing #-}
{-# COMPILE AGDA2HS efst existing #-}
{-# COMPILE AGDA2HS esnd existing #-}
