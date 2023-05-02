{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- AST and Type Definitions

data TYPELANG = TNum
              | TBool
                deriving (Show,Eq)

data TERMLANG = Num  Int 
              | Plus TERMLANG TERMLANG 
              | Minus TERMLANG TERMLANG
              | Mult TERMLANG TERMLANG
              | Div TERMLANG TERMLANG
              | Boolean Bool
              | And TERMLANG TERMLANG
              | Or TERMLANG TERMLANG
              | Leq TERMLANG TERMLANG
              | IsZero TERMLANG 
              | If TERMLANG TERMLANG TERMLANG
              | Bind String TERMLANG TERMLANG
              | Id String 
                deriving (Show,Eq)
  

type Env = [(String,TERMLANG)]

type Cont = [(String,TYPELANG)]


-------------------------------
------ Project Exercises ------
-------------------------------
-- Part 1: Adding Booleans

subst :: String -> TERMLANG -> TERMLANG -> TERMLANG
subst i v (Num x) = (Num x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (Mult l r) = (Mult (subst i v l) (subst i v r))
subst i v (Div l r) = (Div (subst i v l) (subst i v r))
subst i v (Boolean x) = (Boolean x)
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Or l r) = (Or (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero x) = (IsZero x)
subst i v (If c t e) = (If (subst i v c) (subst i v t) (subst i v e))
subst i v (Bind i' v' b') = if i==i' then (Bind i' (subst i v v') b') else (Bind i' (subst i v v') (subst i v b'))
subst i v (Id i') = if i == i' then v else (Id i')

-- Exercise 1
evalS :: TERMLANG -> (Maybe TERMLANG)
evalS (Num x) = if x<0 then Nothing else return(Num x)
evalS (Plus l r) = do{(Num l') <- evalS l;
  (Num r') <- evalS r;
  return (Num(l' + r'))}
evalS (Minus l r) = do{(Num l') <- evalS l;
  (Num r') <- evalS r;
  if ((l' - r') < 0) then Nothing else return (Num (l' - r'))}
evalS (Mult l r) = do{(Num l') <- evalS l;
  (Num r') <- evalS r;
  return (Num (l' * r'))}
evalS (Div l r) = do{(Num l') <- evalS l;
  (Num r') <- evalS r;
  if (r' == 0) then Nothing else return (Num (l' `div` r'))}
evalS (Boolean x) = Just (Boolean x)
evalS (And l r) = do{ (Boolean l') <- evalS l;
  (Boolean r') <- evalS r;
  return (Boolean(l' && r'))}
evalS (Or l r) = do{(Boolean l') <- evalS l;
  (Boolean r') <- evalS r;
  return (Boolean(l' || r'))}
evalS (Leq l r) = do{(Num l') <- evalS l;
  (Num r') <- evalS r;
  return (Boolean(l' <= r'))}
evalS (IsZero x) = do{ (Num x') <- evalS x;
  if x' == 0 then return(Boolean True) else return(Boolean False)}
evalS (If c t e) = do{(Boolean c') <- evalS c;
if c' then evalS t else evalS e}
evalS (Bind i v b) = do{v' <- evalS v;
  (evalS (subst i v' b))}
evalS (Id i) = Nothing

-- Exercise 2
evalM :: Env -> TERMLANG -> (Maybe TERMLANG)
evalM env (Num x) = if x<0 then Nothing else return(Num x)
evalM env (Plus l r) = do{(Num l') <- evalM env l;
  (Num r') <- evalM env r;
  return (Num(l' + r'))}
evalM env (Minus l r) = do{(Num l') <- evalM env l;
  (Num r') <- evalM env r;
  if ((l' - r') < 0) then Nothing else return (Num (l' - r'))}
evalM env (Mult l r) = do{(Num l') <- evalM env l;
  (Num r') <- evalM env r;
  return (Num (l' * r'))}
evalM env (Div l r) = do{(Num l') <- evalM env l;
  (Num r') <- evalM env r;
  if (r' == 0) then Nothing else return (Num (l' `div` r'))}
evalM env (Boolean x) = Just (Boolean x)
evalM env (And l r) = do{ (Boolean l') <- evalM env l;
  (Boolean r') <- evalM env r;
  return (Boolean(l' && r'))}
evalM env (Or l r) = do{(Boolean l') <- evalM env l;
  (Boolean r') <- evalM env r;
  return (Boolean(l' || r'))}
evalM env (Leq l r) = do{(Num l') <- evalM env l;
  (Num r') <- evalM env r;
  return (Boolean(l' <= r'))}
evalM env (IsZero x) = do{ (Num x') <- evalM env x;
  if x' == 0 then return(Boolean True) else return(Boolean False)}
evalM env (If c t e) = do{(Boolean c') <- evalM env c;
if c' then evalM env t else evalM env e}
evalM env (Bind i v b) = do{v' <- evalM env v;
  (evalM env (subst i v' b))}
evalM env (Id i) = Nothing

-- Exercise 3
testEvals :: TERMLANG -> Bool
testEvals n = do{
  if ((evalS n) == (evalM [] n)) then True else False}


-- Part 2: Type Checking

--Exercise 1
typeofM :: Cont -> TERMLANG -> (Maybe TYPELANG)
typeofM cons (Num x) = if x<0 then Nothing else return TNum
typeofM cons (Plus l r) = do{TNum <- typeofM cons l;
  TNum <- typeofM cons r;
  return TNum}
typeofM cons (Minus l r) = do{TNum <- typeofM cons l;
  TNum <- typeofM cons r;
  return TNum}
typeofM cons (Mult l r) = do{TNum <- typeofM cons l;
  TNum <- typeofM cons r;
  return TNum}
typeofM cons (Div l r) = do{TNum <- typeofM cons l;
  TNum <- typeofM cons r;
  return TNum}
typeofM cons (Boolean x) = return TBool
typeofM cons (And l r) = do{ TBool <- typeofM cons l;
  TBool <- typeofM cons r;
  return TBool}
typeofM cons (Or l r) = do{TBool <- typeofM cons l;
  TBool <- typeofM cons r;
  return TBool}
typeofM cons (Leq l r) = do{TNum <- typeofM cons l;
  TNum <- typeofM cons r;
  return TBool}
typeofM cons (IsZero x) = do{ TNum <- typeofM cons x;
  return TBool
}
typeofM cons (If c t e) = do{TBool <- typeofM cons c;
t' <- typeofM cons t;
e' <- typeofM cons e;
if t' == e' then return t' else Nothing}
typeofM cons (Bind i v b) = do{tv <- typeofM cons v;
  typeofM((i,tv):cons) b}
typeofM cons (Id i) = (lookup i cons)

--Exercise 2
evalT :: TERMLANG -> (Maybe TERMLANG)
evalT (Num x) = do{x' <- typeofM [] (Num x);
  evalM [] (Num x)}
evalT (Plus l r) = do{x' <- typeofM [] (Plus l r);
  evalM [] (Plus l r)}
evalT (Minus l r) = do{x' <- typeofM [] (Minus l r);
  evalM [] (Minus l r)} 
evalT (Mult l r) = do{x' <- typeofM [] (Mult l r);
  evalM [] (Mult l r)}
evalT (Div l r) = do{x' <- typeofM [] (Div l r);
  evalM [] (Div l r)}
evalT (Boolean x) = do{x' <- typeofM [] (Boolean x);
  evalM [] (Boolean x)}
evalT (And l r) = do{x' <- typeofM [] (And l r);
  evalM [] (And l r)}
evalT (Or l r) = do{x' <- typeofM [] (Or l r);
  evalM [] (Or l r)}
evalT (Leq l r) = do{x' <- typeofM [] (Leq l r);
  evalM [] (Leq l r)}
evalT (IsZero x) = do{x' <- typeofM [] (IsZero x);
  evalM [] (IsZero x)}
evalT (If c t e) = do{x' <- typeofM [] (If c t e);
  evalM [] (If c t e)}
evalT (Bind i v b) = do{x' <- typeofM [] (Bind i v b);
  evalM [] (Bind i v b)}
evalT (Id i) = do{x' <- typeofM [] (Id i);
  evalM [] (Id i)}