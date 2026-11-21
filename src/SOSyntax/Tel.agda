module SOSyntax.Tel where

{-# FOREIGN AGDA2HS

{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

import SOSyntax

#-}

open import Utils
open import Agda.Builtin.Equality.Rewrite
open import Haskell.Prelude hiding ( id; a; b; c; d; e; f; m; s; t; _,_ )
open import SOSyntax

data Tel : Set

Env' : Tel → Type

data Tel where
  TNil  : Tel
  TSnoc : (Γ : Tel) → (Env' Γ → Ty) → Tel

pattern • = TNil
pattern _▷_ Γ A[_] = TSnoc Γ A[_]

data Env• : Set where
  ENil : Env•
pattern ε = ENil

data Env▷ (@0 A : Set) (@0 B : A → Set) : Set where
  ESnoc : (δ : A) → B δ → Env▷ A B
pattern _,_ δ t = ESnoc δ t

Env' TNil    = Env•
Env' (Γ ▷ A) = Env▷ (Env' Γ) (λ δ → Tm (A δ))

-- Hack to compile the Env' inductive family to a non-positive datatype
Env : @0 Tel → Type
Env Γ = Resurrect (Env' Γ)

variable
  @0 Γ Δ Θ : Tel
  @0 δ σ γ : Env _

efst : Env (Γ ▷ A[_]) → Env Γ
efst (ESnoc ρ t) = ρ
{-# COMPILE AGDA2HS efst #-}

π₁ = efst; {-# INLINE efst #-}

esnd : (ρ : Env (Γ ▷ A[_])) → Tm (A[ efst ρ ])
esnd (ESnoc ρ t) = t
{-# COMPILE AGDA2HS esnd #-}

π₂ = esnd; {-# INLINE esnd #-}

▷η : (ρ : Env (Γ ▷ A[_])) → π₁ ρ , π₂ ρ ≡ ρ
▷η (_ , _) = refl

{-# FOREIGN AGDA2HS

data Tel
  = TNil
  | TSnoc Tel (Env -> Ty)

data Env
  = ENil
  | ESnoc Env Tm

#-}

{-# COMPILE AGDA2HS Tel    existing #-}
{-# COMPILE AGDA2HS Env    existing #-}
{-# COMPILE AGDA2HS TNil   existing #-}
{-# COMPILE AGDA2HS TSnoc  existing #-}
{-# COMPILE AGDA2HS ENil   existing #-}
{-# COMPILE AGDA2HS ESnoc  existing #-}

{-# COMPILE AGDA2HS π₁ inline #-}
{-# COMPILE AGDA2HS π₂ inline #-}
