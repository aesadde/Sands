{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE ScopedTypeVariables       #-}

--------------------------------------------------------------------------------
--  FROM LIQUIDHaskell
--  https://github.com/ucsd-progsys/liquidhaskell
--------------------------------------------------------------------------------


module Visitor (

  -- * visitors
  CBVisitable (..)

  ) where

import           CoreSyn
import           Data.Hashable
import           DataCon
import           Literal
import           Prelude                          hiding (error)

import           Var

import           Data.List                        (foldl', (\\), delete,sort, group)

import qualified Data.HashSet                     as S
import           Unique


------------------------------------------------------------------------------
-------------------------------- A CoreBind Visitor --------------------------
------------------------------------------------------------------------------
sortNub :: Ord a => [a] -> [a]
sortNub = map head . group . sort

class CBVisitable a where
  freeVars :: S.HashSet Var -> a -> [Var]
  readVars :: a -> [Var]
  letVars  :: a -> [Var]
  literals :: a -> [Literal]

instance CBVisitable [CoreBind] where
  freeVars env cbs = sortNub xs \\ ys
    where xs = concatMap (freeVars env) cbs
          ys = concatMap bindings cbs

  readVars = concatMap readVars
  letVars  = concatMap letVars
  literals = concatMap literals

instance CBVisitable CoreBind where
  freeVars env (NonRec x e) = freeVars (extendEnv env [x]) e
  freeVars env (Rec xes)    = concatMap (freeVars env') es
                              where (xs,es) = unzip xes
                                    env'    = extendEnv env xs

  readVars (NonRec _ e)     = readVars e
  readVars (Rec xes)        = concat [x `delete` nubReadVars e |(x, e) <- xes]
    where nubReadVars = sortNub . readVars

  letVars (NonRec x e)      = x : letVars e
  letVars (Rec xes)         = xs ++ concatMap letVars es
    where
      (xs, es)              = unzip xes

  literals (NonRec _ e)      = literals e
  literals (Rec xes)         = concatMap (literals. snd) xes

instance CBVisitable (Expr Var) where
  freeVars = exprFreeVars
  readVars = exprReadVars
  letVars  = exprLetVars
  literals = exprLiterals

exprFreeVars :: S.HashSet Id -> Expr Id -> [Id]
exprFreeVars = go
  where
    go env (Var x)         = if x `S.member` env then [] else [x]
    go env (App e a)       = (go env e) ++ (go env a)
    go env (Lam x e)       = go (extendEnv env [x]) e
    go env (Let b e)       = (freeVars env b) ++ (go (extendEnv env (bindings b)) e)
    go env (Case e x _ cs) = (go env e) ++ (concatMap (freeVars (extendEnv env [x])) cs)
    go _   _               = []

exprReadVars :: (CBVisitable (Alt t), CBVisitable (Bind t)) => Expr t -> [Id]
exprReadVars = go
  where
    go (Var x)             = [x]
    go (App e a)           = concatMap go [e, a]
    go (Lam _ e)           = go e
    go (Let b e)           = readVars b ++ go e
    go (Case e _ _ cs)     = (go e) ++ (concatMap readVars cs)
    go _                   = []

exprLetVars :: Expr Var -> [Var]
exprLetVars = go
  where
    go (Var _)             = []
    go (App e a)           = concatMap go [e, a]
    go (Lam x e)           = x : go e
    go (Let b e)           = letVars b ++ go e
    go (Case e x _ cs)     = x : go e ++ concatMap letVars cs
    go _                   = []

exprLiterals :: (CBVisitable (Alt t), CBVisitable (Bind t))
             => Expr t -> [Literal]
exprLiterals = go
  where
    go (Lit l)             = [l]
    go (App e a)           = concatMap go [e, a]
    go (Let b e)           = literals b ++ go e
    go (Lam _ e)           = go e
    go (Case e _ _ cs)     = (go e) ++ (concatMap literals cs)
    go _                   = []


instance CBVisitable (Alt Var) where
  freeVars env (a, xs, e) = freeVars env a ++ freeVars (extendEnv env xs) e
  readVars (_,_, e)       = readVars e
  letVars  (_,xs,e)       = xs ++ letVars e
  literals (c,_, e)       = literals c ++ literals e


instance CBVisitable AltCon where
  freeVars _ (DataAlt dc) = dataConImplicitIds dc
  freeVars _ _            = []
  readVars _              = []
  letVars  _              = []
  literals (LitAlt l)     = [l]
  literals _              = []



extendEnv :: (Eq a, Foldable t, Hashable a)
          => S.HashSet a -> t a -> S.HashSet a
extendEnv = foldl' (flip S.insert)

bindings :: Bind t -> [t]
bindings (NonRec x _)
  = [x]
bindings (Rec  xes  )
  = map fst xes

instance Hashable Var where
  hashWithSalt = uniqueHash


uniqueHash :: Uniquable a => Int -> a -> Int
uniqueHash i = hashWithSalt i . getKey . getUnique
