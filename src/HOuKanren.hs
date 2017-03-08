{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module HOuKanren where

-- A twist to MicroKanren implementation https://github.com/rntz/ukanren
-- to support Higher-Order Relational Programming
--   - unification over beta-eta normal form
--   - reduction is very pure and very inefficient
--     so not expected to be scalabe for large terms

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State.Strict
import           Data.Hashable
import qualified Data.HashMap.Strict              as Map
import           Data.Maybe
import           Unbound.LocallyNameless          hiding (empty, fresh, join)
import qualified Unbound.LocallyNameless          as LN

{-# ANN module "HLint: ignore Use fmap" #-}
{-# ANN module "HLint: ignore Use mappend" #-}

type NameTm = Name Tm

data Tm = Var NameTm | C String [Tm]
        | Lam (Bind NameTm Tm) | App Tm Tm
  deriving Show

instance Eq Tm where (==) = aeq

$(derive [''Tm])

instance Alpha Tm

instance Subst Tm Tm where
  isvar (Var v) = Just (SubstName v)
  isvar _       = Nothing

instance Hashable NameTm where
  hashWithSalt s n = hashWithSalt s (name2String n, name2Integer n)

lam x = Lam . bind x

-- beta, eta reduction step
step :: Tm -> MaybeT FreshM Tm
step (C s ts) = C s <$> stepList ts
step (Var _) = mzero
step (Lam b) = do
  (x,t) <- unbind b
  let fv_t :: [Name Tm] = fv t
  case t of  App t1 (Var y) | x == y && x `elem` fv_t -> pure t1 -- eta
             _              -> lam x <$> step t
step (App t1@(Lam b) t2) = do { (x,t) <- unbind b; return $ subst x t2 t }
step (App t1 t2) = App <$> step t1 <*> pure t2 <|> App <$> pure t1 <*> step t2

stepList []     = mzero
stepList (t:ts) = (:) <$> step t <*> pure ts  <|>  (t:) <$> stepList ts

-- red = step*
red t = (step t >>= red) <|> pure t

-- reduce to a normal form
reduce :: Tm -> FreshM Tm
reduce t = fromJust <$> runMaybeT (red t)

reduce' = runFreshM . reduce

newVar = LN.fresh (s2n "_")
assign v t = lift $ _assign v t
_assign v t = modify (Map.insert v t)
deref v = lift $ _deref v
_deref v = gets (Map.lookup v)

-- Fair interleaving of finitely many lists.
interleaves :: [[a]] -> [a]
interleaves [] = []
interleaves l  = [x | x:_ <- l] ++ interleaves [xs | _:xs <- l]

interleave :: [a] -> [a] -> [a]
interleave a b = interleaves [a,b]


-- Search trees, so we can define the search algorithm separately.
data Tree a = Empty | Single a | Node (Tree a) (Tree a) deriving Show

instance Functor Tree where fmap = liftM
instance Applicative Tree where pure = return; (<*>) = ap
instance Monad Tree where
    return = Single
    Empty >>= _ = Empty
    Single x >>= f = f x
    Node l r >>= f = Node (l >>= f) (r >>= f)

-- NB. not a law-abiding Alternative/MonadPlus instance: not associative.
instance MonadPlus Tree where mzero = empty; mplus = (<|>)
instance Alternative Tree where empty = Empty; (<|>) = Node


-- Search strategies over Trees.
tree2listBy :: ([a] -> [a] -> [a]) -> Tree a -> [a]
tree2listBy _ Empty      = []
tree2listBy _ (Single a) = [a]
tree2listBy f (Node l r) = f (tree2listBy f l) (tree2listBy f r)

dfs, ifs, bfs :: Tree a -> [a]

dfs = tree2listBy (++)

-- Not sure if there's a standard name for this search strategy.
ifs = tree2listBy interleave

-- Unfortunately we can't write iterated deepening as a function on Trees,
-- because of Haskell's memoizing call-by-need evaluation. So we'll just do a
-- plain old memory-hogging BFS.
bfs t = search [] [t]
    -- we use the usual trick of encoding a queue as two stacks.
    where search [] []            = []
          search a []             = search [] (reverse a)
          search a (Empty : b)    = search a b
          search a (Single x : b) = x : search a b
          search a (Node l r : b) = search (r:l:a) b


-- unification state is a mapping from name to terms (a big substitution)
type UState = Map.HashMap NameTm Tm
-- Implementation of the Kanren interface
type K = FreshMT (StateT UState Tree)
type Goal = K ()

start :: UState
start = Map.empty

-- runK :: K a -> UState -> [(a, UState)]
runK k st = bfs $ runStateT (runFreshMT k) st
-- NB. if we change bfs to ifs, then fivesR fails!
-- with dfs you get prolog-like behavior, and even more things fail.

-- evalK :: K a -> UState -> [a]
evalK k st = fmap fst (runK k st)

-- execK :: K a -> UState -> [UState]
execK k st = fmap snd (runK k st)

-- Basic operators.
ok :: Goal
ok = pure ()


-- implemetation of Prolog's (/==)
(/==) :: Tm -> Tm -> Goal
a /== b = guard =<< (/=) <$> expand a <*> expand b

-- implemetation of Prolog's (==)
(===) :: Tm -> Tm -> Goal
a === b = guard =<< (==) <$> expand a <*> expand b

-- disj, conj :: Goal -> Goal -> Goal
disj = (<|>)
conj = (>>)

-- equivalent of disj+, conj+
-- disjs, conjs :: [Goal] -> Goal
disjs = msum
conjs = sequence_


-- expands variables at the top level until no change
-- expand :: Tm -> K Tm
expand :: Tm -> K Tm
expand t@(Var v) = do t' <- fromMaybe t <$> deref v
                      if t' == t then return t else expand t'
expand t = return t

-- expands variables inside terms
expand' :: Tm -> K Tm
expand' t@(Var _) = do t' <- expand t
                       if t==t' then return t' else expand' t'
expand' (C s ts) = C s <$> mapM expand' ts
expand' (App t1 t2) = App <$> expand' t1 <*> expand' t2
expand' (Lam b) = do (x,t) <- unbind b
                     lam x <$> expand' t


-- unification
eq :: Tm -> Tm -> K ()
eq t1 t2 = join $ e <$> (reduce'<$>expand t1) <*> (reduce'<$>expand t2)
  where
    e (Var x) (Var y) | x == y  = ok
    e (Var x) t  = assign x (reduce' t)
    e t (Var x)  = assign x (reduce' t)
    e (C s1 ts1) (C s2 ts2) | s1 == s2 && length ts1 == length ts2
          = zipWithM_ eq (map reduce' ts1) (map reduce' ts2)
    e (App t11 t12) (App t21 t22) = do { eq t11 t21; eq t12 t22 }
    e (Lam b1) (Lam b2) = do (x1,t1') <- unbind b1
                             (x2,t2') <- unbind b2
                             eq t1' (subst x2 (Var x1) t2')
    e _ _ = mzero
