{-# LANGUAGE GADTs, FlexibleContexts #-}

-- Imports for Monads
import Control.Monad

-- AST Definition

data TYPELANG = TNum
              | TBool
              deriving (Show,Eq)

data TERMLANG = Num Int
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
              deriving (Show,Eq)

-------------------------------
------ Project Exercises ------
-------------------------------
-- Part 1: Evaluation Functions

-- Exercise 1
evalM :: TERMLANG -> (Maybe TERMLANG)
evalM (Num x) = if x<0 then Nothing else return(Num x)
evalM (Plus l r) = do{(Num l') <- evalM l;
  (Num r') <- evalM r;
  return (Num(l' + r'))}
evalM (Minus l r) = do{(Num l') <- evalM l;
  (Num r') <- evalM r;
  if ((l' - r') < 0) then Nothing else return (Num (l' - r'))}
evalM (Mult l r) = do{(Num l') <- evalM l;
  (Num r') <- evalM r;
  return (Num (l' * r'))}
evalM (Div l r) = do{(Num l') <- evalM l;
  (Num r') <- evalM r;
  if (r' == 0) then Nothing else return (Num (l' `div` r'))}
evalM (Boolean x) = Just (Boolean x)
evalM (And l r) = do{ (Boolean l') <- evalM l;
  (Boolean r') <- evalM r;
  return (Boolean(l' && r'))}
evalM (Or l r) = do{(Boolean l') <- evalM l;
  (Boolean r') <- evalM r;
  return (Boolean(l' || r'))}
evalM (Leq l r) = do{(Num l') <- evalM l;
  (Num r') <- evalM r;
  return (Boolean(l' <= r'))}
evalM (IsZero x) = do{ (Num x') <- evalM x;
  if x' == 0 then return(Boolean True) else return(Boolean False)
}

evalM (If c t e) = do{(Boolean c') <- evalM c;
if c' then evalM t else evalM e}


-- Exercise 2
typeofM :: TERMLANG -> Maybe TYPELANG
typeofM (Num x) = if x<0 then Nothing else return TNum
typeofM (Plus l r) = do{TNum <- typeofM l;
  TNum <- typeofM r;
  return TNum}
typeofM (Minus l r) = do{TNum <- typeofM l;
  TNum <- typeofM r;
  return TNum}
typeofM (Mult l r) = do{TNum <- typeofM l;
  TNum <- typeofM r;
  return TNum}
typeofM (Div l r) = do{TNum <- typeofM l;
  TNum <- typeofM r;
  return TNum}
typeofM (Boolean x) = return TBool
typeofM (And l r) = do{ TBool <- typeofM l;
  TBool <- typeofM r;
  return TBool}
typeofM (Or l r) = do{TBool <- typeofM l;
  TBool <- typeofM r;
  return TBool}
typeofM (Leq l r) = do{TNum <- typeofM l;
  TNum <- typeofM r;
  return TBool}
typeofM (IsZero x) = do{ TNum <- typeofM x;
  return TBool
}

typeofM (If c t e) = do{TBool <- typeofM c;
t' <- typeofM t;
e' <- typeofM e;
if t' == e' then return t' else Nothing}

-- Exercise 3
interpTypeEval :: TERMLANG -> Maybe TERMLANG
interpTypeEval (Num x) = do{x' <- typeofM (Num x);
evalM (Num x)}
interpTypeEval (Plus l r) = do{x' <- typeofM (Plus l r);
evalM (Plus l r)}
interpTypeEval (Minus l r) = do{x' <- typeofM (Minus l r);
evalM (Minus l r)} 
interpTypeEval (Mult l r) = do{x' <- typeofM (Mult l r);
evalM (Mult l r)}
interpTypeEval (Div l r) = do{x' <- typeofM (Div l r);
evalM (Div l r)}
interpTypeEval (Boolean x) = do{x' <- typeofM (Boolean x);
evalM (Boolean x)}
interpTypeEval (And l r) = do{x' <- typeofM (And l r);
evalM (And l r)}
interpTypeEval (Or l r) = do{x' <- typeofM (Or l r);
evalM (Or l r)}
interpTypeEval (Leq l r) = do{x' <- typeofM (Leq l r);
evalM (Leq l r)}
interpTypeEval (IsZero x) = do{x' <- typeofM (IsZero x);
evalM (IsZero x)}
interpTypeEval (If c t e) = do{x' <- typeofM (If c t e);
evalM (If c t e)}


-- Part 2: Optimizer

-- Exercise 1
optimize :: TERMLANG -> TERMLANG
optimize (Num n) = (Num n)
optimize (Boolean n) = (Boolean n)
optimize (Plus l (Num 0)) = (optimize l)
optimize (Plus l r) = (Plus (optimize l) (optimize r))
optimize (Minus l (Num 0)) = (optimize l)
optimize (Minus l r) = (Minus (optimize l) (optimize r))
optimize (Mult l (Num 0)) = (optimize (Num 0))
optimize (Mult l r) = (Mult (optimize l) (optimize r))
optimize (Div l r) = (Div (optimize l) (optimize r))

optimize (And (Boolean False) r) = (Boolean False)
optimize (And l (Boolean False)) = (Boolean False)
optimize (And (Boolean True) (Boolean True)) = (Boolean True)
optimize (And l r) = (And (optimize l) (optimize r))

optimize (Or (Boolean False) (Boolean False)) = (Boolean False)
optimize (Or (Boolean True) (Boolean True)) = (Boolean True)
optimize (Or l (Boolean True)) = (Boolean True)
optimize (Or (Boolean True) r) = (Boolean True)
optimize (Or l r) = (Or (optimize l) (optimize r))

optimize (Leq l r) = (Leq (optimize l)  (optimize r))
optimize (IsZero (Num 0)) = (Boolean True)
optimize (IsZero (Num x)) = (Boolean False)
optimize (IsZero x) = (IsZero (optimize x))

optimize (If (Boolean True) t e) = (optimize t)
optimize (If (Boolean False) t e) = (optimize e)
optimize (If c t e) = (If (optimize c) (optimize t) (optimize e))


-- Exercise 2
interpOptEval :: TERMLANG -> Maybe TERMLANG
interpOptEval n = evalM(optimize n)

