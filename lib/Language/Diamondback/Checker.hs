{-# LANGUAGE FlexibleContexts #-}

--------------------------------------------------------------------------------
-- | This module contains the code for converting an `Expr` to a "A-Normal" form.
--------------------------------------------------------------------------------
module Language.Diamondback.Checker
  ( -- * Top-level Static Checker
    check

    -- * Error Constructors
  , errUnboundVar
  , errUnboundFun
  ) where

import           Control.Exception
import           Data.Monoid
import qualified Data.List          as L
import           Text.Printf        (printf)
import           Language.Diamondback.Types
import           Language.Diamondback.Utils

--------------------------------------------------------------------------------
check :: BareProgram -> BareProgram
--------------------------------------------------------------------------------
check p = case wellFormed p of
            [] -> p
            es -> throw es

-- | Map from function name to arity
type FunEnv = Env

--------------------------------------------------------------------------------
-- | `wellFormed p` returns the list of errors for a program `p`
--------------------------------------------------------------------------------
wellFormed :: BareProgram -> [UserError]
--------------------------------------------------------------------------------
wellFormed (Prog ds e) = duplicateFunErrors ds
                      ++ concatMap (wellFormedD fEnv) ds
                      ++ wellFormedE fEnv emptyEnv e
  where
    fEnv               = fromListEnv [(bindId f, length xs) | Decl f xs _ _ <- ds]

--------------------------------------------------------------------------------
-- | `wellFormedD fEnv vEnv d` returns the list of errors for a func-decl `d`
--------------------------------------------------------------------------------
wellFormedD :: FunEnv -> BareDecl -> [UserError]
wellFormedD fEnv (Decl _ xs e _) = duplicateParamErrors xs 
                                   ++ wellFormedE fEnv vEnv e 
  where
    vEnv                         = foldl (flip addEnv) emptyEnv xs

--------------------------------------------------------------------------------
-- | `wellFormedE vEnv e` returns the list of errors for an expression `e`
--------------------------------------------------------------------------------
wellFormedE :: FunEnv -> Env -> Bare -> [UserError]
wellFormedE fEnv env e = visit env e
  where
    visit :: Env -> Bare -> [UserError]
    visit seen (Number n l)      | n > (maxInt -1 ) = [ errLargeNum l n ]
                                 | n < (-maxInt ) = [ errLargeNum l n ]
                                 | otherwise = [] -- check that number isn't too big or small
    visit seen (Boolean b l)     = []
    visit seen (Prim1 o e l)     = visit seen e
    visit seen (If e1 e2 e3 l)   = concatMap (visit seen) [e1, e2, e3]
    visit seen (Prim2 o e1 e2 l) = concatMap (visit seen) [e1, e2]
    visit seen (Let x e1 e2 l)   = (if (memberEnv (bindId x) seen) then [errDupBind x] else [])
                                   ++ visit seen e1 ++ visit (addEnv x seen) e2 
    visit seen (Id x l) 
      | memberEnv x seen          = []
      | otherwise                = [errUnboundVar l x]
    visit seen (App f es l)      = case lookupEnv f fEnv of 
                                      Nothing -> [errUnboundFun l f]
                                      Just n  -> (if length es == n then [] else [errCallArity l f])
                                        ++ concatMap (visit seen) es 
--tail call compile it, mov to where it has to be
--------------------------------------------------------------------------------
-- | Error Checkers: In each case, return an empty list if no errors.
--------------------------------------------------------------------------------
duplicateFunErrors :: [BareDecl] -> [UserError]
duplicateFunErrors
  = fmap errDupFun
  . concat
  . dupBy (bindId . fName)

duplicateParamErrors :: [BareBind] -> [UserError]
duplicateParamErrors i 
  = fmap (errDupParam . head)
  .dupBy bindId 
  $ i

-- | `maxInt` is the largest number you can represent with 31 bits (accounting for sign
--    and the tag bit.

maxInt :: Integer
maxInt = 1073741824

--------------------------------------------------------------------------------
-- | Error Constructors: Use these functions to construct `UserError` values
--   when the corresponding situation arises. e.g see how `errDupFun` is used.
--------------------------------------------------------------------------------

errDupFun :: (Located (Bind a)) => Decl a -> UserError
errDupFun d = mkError (printf "duplicate function '%s'" (pprint f))    (sourceSpan f) where f = fName d

errDupParam :: (Located (Bind a)) => Bind a -> UserError
errDupParam x = mkError (printf "duplicate parameter '%s'" (bindId x)) (sourceSpan x)

errDupBind :: (Located (Bind a)) => Bind a -> UserError
errDupBind x = mkError (printf "shadow binding '%s'" (bindId x))      (sourceSpan x)

errLargeNum :: SourceSpan -> Integer -> UserError
errLargeNum   l n = mkError (printf "number '%d' is too large" n) l

errUnboundVar :: SourceSpan -> Id -> UserError
errUnboundVar l x = mkError (printf "unbound variable '%s'" x) l

errUnboundFun :: SourceSpan -> Id -> UserError
errUnboundFun l f = mkError (printf "function '%s' is not defined" f) l

errCallArity :: SourceSpan -> Id -> UserError
errCallArity  l f = mkError (printf "wrong arity of arguments at call of %s" f) l
