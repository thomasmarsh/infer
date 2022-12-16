{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Monad (join, replicateM)

import Control.Monad.State
   ( State
   , evalState
   , get
   , modify
   , put)

import qualified Data.Map as M

import System.Console.Haskeline
   ( InputT
   , defaultSettings
   , getInputLine
   , outputStrLn
   , runInputT
   )

import Text.ParserCombinators.Parsec
   ( (<|>)
   , GenParser
   , ParseError
   , between
   , chainl1
   , char
   , letter
   , many
   , many1
   , optional
   , parse
   , space
   , string
   )


------------------------------------------------------------------------------
--
-- AST
--
------------------------------------------------------------------------------

type Id  = String

data Expr
   = Lam Id Expr
   | App Expr Expr
   | Var Id

data Ty
   = TVar Id
   | Arrow Ty Ty

data AExpr
   = ALam Id AExpr Ty
   | AApp AExpr AExpr Ty
   | AVar Id Ty


------------------------------------------------------------------------------
--
-- Printing
--
------------------------------------------------------------------------------

protect :: Expr -> String
protect (Var x) = x
protect e       = "(" ++ show e ++ ")"

instance Show Expr where
   show (Var x)               = x
   show (Lam x e)             = "\\" ++ x ++ " -> " ++ show e
   show (App e1@(Lam _ _) e2) = protect e1 ++ " " ++ protect e2
   show (App a b)             = show a ++ " " ++ protect b

instance Show Ty where
   show (TVar x)                = x
   show (Arrow s@(Arrow _ _) t) = "(" ++ show s ++ ") -> " ++ show t
   show (Arrow s t)             = show s ++ " -> " ++ show t

instance Show AExpr where
   show (AVar x a)     = "(" ++ x ++ ":" ++ show a ++ ")"
   show (AApp e1 e2 a) = "((" ++ show e1 ++ " " ++ show e2 ++ "):" ++ show a ++ ")"
   show (ALam x e a)   = "((\\" ++ x ++ " -> " ++ show e ++ "):" ++ show a ++ ")"

 
------------------------------------------------------------------------------
--
-- Parsing
--
------------------------------------------------------------------------------

type Parser a = GenParser Char () a

identP :: Parser Id
identP = many1 $ letter <|> char '\''

varP :: Parser Expr
varP = Var <$> identP

lambdaP :: Parser Expr -> Parser Expr
lambdaP expr = do
    name <- char '\\' *> many space *> identP
    Lam name <$> (many space *> string "->" *> many space *> expr)
    
parens :: Parser a -> Parser a
parens = between (char '(' *> many space) (many space *> char ')')

nonApp :: Parser Expr
nonApp = parens exprP <|> lambdaP exprP <|> varP
    
exprP :: Parser Expr
exprP = chainl1 nonApp $ optional space >> pure App
    
tryParse :: String -> Either ParseError Expr
tryParse = parse exprP ""


------------------------------------------------------------------------------
--
-- Unification
--
------------------------------------------------------------------------------

data UnifyError = Circularity

-- invariant for substitutions:
-- no id on a lhs occurs in any term earlier in the list
type Substitution = [(Id, Ty)]

-- check if a variable occurs in a term
occurs :: Id -> Ty -> Bool
occurs x (TVar y)    = x == y
occurs x (Arrow u v) = occurs x u || occurs x v

-- substitute term s for all occurrences of variable x in term t
subst :: (Id, Ty) -> Ty -> Ty
subst (x, s) t@(TVar y) = if x == y then s else t
subst p (Arrow u v)     = Arrow (subst p u) (subst p v)

-- apply a substitution right to left
apply :: Ty -> Substitution -> Ty
apply = foldr subst

-- unify one pair
unifyOne :: Ty -> Ty -> Either UnifyError Substitution
unifyOne s t =
   case (s, t) of
      (TVar x,        TVar y)        -> Right [(x, t) | x /= y]
      (Arrow x y,     Arrow u v)     -> unify [(x,u), (y,v)]
      (TVar x,        u@(Arrow _ _)) -> f x u
      (u@(Arrow _ _), TVar x)        -> f x u
   where f x u =
            if occurs x u
               then Left Circularity
               else Right [(x,u)]

-- unify a list of pairs
unify :: [(Ty, Ty)] -> Either UnifyError Substitution
unify []        = Right []
unify ((x,y):t) = do
   t1 <- unify t
   t0 <- unifyOne (apply x t1) (apply y t1)
   pure $ t0 ++ t1


------------------------------------------------------------------------------
--
-- Inference
--
------------------------------------------------------------------------------

data ACtx = ACtx [Id] (M.Map Id Ty)

type AState a = State ACtx a

idents :: [Id]
idents =  join [replicateM n ['a'..'z'] | n <- [1..]]

initACtx :: ACtx
initACtx = ACtx idents M.empty

nextTypeVar :: AState Ty
nextTypeVar = do
   ACtx xs m <- get
   put $ ACtx (tail xs) m
   pure $ TVar (head xs)

lookupTy :: Id -> AState (Maybe Ty)
lookupTy x = get >>= \(ACtx _ m) -> pure $ M.lookup x m

insertTy :: Id -> Ty -> AState ()
insertTy x a = modify (\(ACtx xs m) -> ACtx xs (M.insert x a m))
   
typeOf :: AExpr -> Ty
typeOf = \case
   AVar _ a -> a
   ALam _ _ a -> a
   AApp _ _ a -> a

-- annotate all subexpressions with types
-- bv = stack of bound variables for which current expression is in scope
-- fv = hashtable of known free variables
annotate :: Expr -> AExpr
annotate expr = evalState (go [] expr) initACtx
   where
      go :: [(Id, Ty)] -> Expr -> AState AExpr
      go bv = \case
         Var x -> 
            -- Lookup in the stack of bound variables
            case lookup x bv of
               Just a -> pure $ AVar x a
               Nothing -> do
                  -- Lookup in the free variables
                  lookupTy x >>= \case
                     Just a -> pure $ AVar x a
                     -- Otherwise, create a new variable
                     Nothing -> do
                        a <- nextTypeVar
                        insertTy x a
                        pure $ AVar x a
         Lam x e -> do
            a <- nextTypeVar
            ae <- go ((x, a):bv) e
            pure $ ALam x ae (Arrow a (typeOf ae))
         App e1 e2 -> do
            a1 <- go bv e1
            a2 <- go bv e2
            AApp a1 a2 <$> nextTypeVar

collect :: [AExpr] -> [(Ty,Ty)] -> [(Ty, Ty)]
collect aexprs u =
   case aexprs of
      [] -> u
      (AVar _ _:r)    -> collect r u
      (ALam _ ae _:r) -> collect (ae:r) u
      (AApp ae1 ae2 a:r) -> 
         let (f, b) = (typeOf ae1, typeOf ae2)
          in collect (ae1:ae2:r) ((f, Arrow b a):u)
      
infer :: Expr -> Either UnifyError Ty
infer e = apply (typeOf ae) <$> unify (collect [ae] [])
   where ae = annotate e


------------------------------------------------------------------------------
--
-- REPL
--
------------------------------------------------------------------------------

handleLine :: String -> InputT IO ()
handleLine line =
   case tryParse line of
      Left err -> outputStrLn ("ERROR:\n" ++ show err) >> repl
      Right x -> do
         case infer x of
            Left Circularity -> outputStrLn "ERROR: not unifiable due to circularity"
            Right y          -> outputStrLn (show y)
         repl

repl :: InputT IO ()
repl = getInputLine "? " >>= \case
          Nothing   -> pure ()
          Just line -> handleLine line

main :: IO ()
main = runInputT defaultSettings repl
