{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

module SOSyntax
  (Ty, Tm, pi, lam, app, Tel, Env, tnil, tsnoc, enil, esnoc, efst, esnd)
where

import Prelude hiding ( pi, (^) )

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

