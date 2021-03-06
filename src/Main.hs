-- vim: sw=2: ts=2: expandtab: ai:
{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

import           Control.Applicative
import           HOuKanren
import           Unbound.LocallyNameless (fv, s2n)

{-# ANN module "HLint: ignore Use fmap" #-}
{-# ANN module "HLint: ignore Use mappend" #-}

[x,y,z] = fmap s2n ["x","y","z"]

tmId = lam x (Var x)

-- Test cases
five :: Goal
five = fresh $ \x -> eq x (C "5" [])

fives :: Goal
fives = fresh fives_
-- where
fives_ x = eq x (C "5" []) <|> fives_ x

fivesR :: Goal
fivesR = fresh fivesR_
-- where
fivesR_ x = fivesR_ x <|> eq x (C "5" [])

aAndB :: Goal
aAndB = do fresh $ \a -> eq a (C "7" [])
           fresh $ \b -> eq b (C "5" []) <|> eq b (C "6" [])



etaTest :: Goal
etaTest = eq (etaExpand $ C "a" []) (C "a" [])
  where etaExpand f = lam x (f `App` Var x)


test t = take 10 $ runK t start

tst t = mapM_ print $ test t


main :: IO ()
main = do
  -- very simple cases of terms involving reduction
  putStrLn $ "Free Variables of " ++ show tm_id_x ++ " : "
          ++ show (fv tm_id_x :: [NameTm])
  putStrLn $ "Free Variables of " ++ show tm_id_y ++ " : "
          ++ show (fv tm_id_y :: [NameTm])
  putStrLn $ "Unification : " ++ show tm_id_x ++ " =?= " ++ show tm_id_y
  print $ runK (eq tm_id_x tm_id_y) start
  -- print $ runK (eq tm_id_x tm_id_y >> expand' tm_id_y) start
  -- print $ runK (eq tm_id_x tm_id_y >> expand' tm_id_x) start
  putStrLn $ "Unification : " ++ show tm_id_x ++ " =?= " ++ show tm_id_x
  print $ runK (eq tm_id_x tm_id_x) start
  where
    tm_id_x = tmId `App` Var x
    tm_id_y = tmId `App` Var y
