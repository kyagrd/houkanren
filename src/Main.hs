{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

-- A twist to MicroKanren implementation https://github.com/rntz/ukanren
-- to support Higher-Order Relational Programming
--   - unification over beta-eta normal form
--   - reduction is very pure and very inefficient
--     so not expected to be scalabe for large terms

import           HOuKanren
import           Unbound.LocallyNameless

[x,y,z] = fmap s2n ["x","y","z"]

tmId = lam x (Var x)

main :: IO ()
main = do
  print $ runK (eq (tmId `App` Var x) (tmId `App` Var y)) start
  print $ runK (eq (tmId `App` Var x) (tmId `App` Var x)) start

{-
$ stack exec houkanren --
[((),fromList [(x,Var y)])]
[((),fromList [])]
-}
