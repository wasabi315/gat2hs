{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

module Fo2So (Ctx, Ty, Tm, Sub, fo2soCtx, fo2soTy, fo2soTm, fo2soSub, cnil, csnoc, sid, snil, scomp, tysub, tmsub, ssnoc, sfst, ssnd, pi, lam, app) where

import SOSyntax qualified as SO (Env, Tel, Tm, Ty, app, efst, enil, esnd, esnoc, lam, pi, tnil, tsnoc)
import Syntax qualified as FO
import Prelude hiding (pi)

type Ctx = SO.Tel

type Ty = SO.Env -> SO.Ty

type Tm = SO.Env -> SO.Tm

type Sub = SO.Env -> SO.Env

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

cnil :: Ctx
cnil = SO.tnil

csnoc :: Ctx -> Ty -> Ctx
csnoc = SO.tsnoc

sid :: Sub
sid = \ρ -> ρ

snil :: Sub
snil = \_ -> SO.enil

scomp :: Sub -> Sub -> Sub
scomp δ σ = \ρ -> δ (σ ρ)

tysub :: Ty -> Sub -> Ty
tysub a sub = \env -> a (sub env)

tmsub :: Tm -> (SO.Env -> SO.Env) -> Tm
tmsub t sub = \env -> t (sub env)

ssnoc :: Sub -> Tm -> Sub
ssnoc δ t = \ρ -> SO.esnoc (δ ρ) (t ρ)

sfst :: Sub -> Sub
sfst δ = \ρ -> SO.efst (δ ρ)

ssnd :: Sub -> Tm
ssnd δ = \ρ -> SO.esnd (δ ρ)

pi :: Ty -> Ty -> Ty
pi a b = \ρ -> SO.pi (a ρ) (\τ -> b (SO.esnoc ρ τ))

lam :: Tm -> Tm
lam t = \ρ -> SO.lam (\τ -> t (SO.esnoc ρ τ))

app :: Tm -> Tm -> Tm
app t u = \ρ -> SO.app (t ρ) (u ρ)
