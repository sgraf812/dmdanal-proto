module Exp where

import Control.Monad
import Data.Foldable
import Debug.Trace
import qualified Text.ParserCombinators.ReadPrec as Read
import qualified Text.ParserCombinators.ReadP as ReadP
import qualified Text.Read as Read
import qualified Data.Map as Map
import Data.Char
import GHC.Stack
import Data.Functor.Classes (Eq2 (liftEq2))

assert :: HasCallStack => Bool -> a -> a
assert True  x = x
assert False _ = error "assertion failure"

assertMsg :: HasCallStack => Bool -> String -> a -> a
assertMsg True  _   x = x
assertMsg False msg _ = error ("assertion failure: " ++ msg)

traceWith :: (t -> String) -> t -> t
traceWith f a = trace (f a) a

type Name = String -- [a-z][a-zA-Z0-9]+
data Tag
  = FF | TT | None | Some | Pair | S | Z
  deriving (Show, Read, Eq, Ord, Enum, Bounded)

conArity :: Tag -> Int
conArity Pair = 2
conArity Some = 1
conArity S = 1
conArity _ = 0

data Exp
  = Var Name
  | App Exp Name
  | Lam Name Exp
  | Let Name Exp Exp
  | ConApp Tag [Name]
  | Case Exp Alts
type Alts = Map.Map Tag ([Name],Exp)

instance Eq Exp where
  e1 == e2 = go Map.empty Map.empty e1 e2
    where
      bind x benv = Map.insert x (Map.size benv) benv
      occ benv x = maybe (Left x) Right (Map.lookup x benv)
      go benv1 benv2 e1 e2 = case (e1,e2) of
        (Var x, Var y)         -> occ benv1 x == occ benv2 y
        (App f x, App g y)     -> occ benv1 x == occ benv2 y && go benv1 benv2 f g
        (Let x e1 e2, Let y e3 e4) -> go benv1' benv2' e1 e3 && go benv1' benv2' e2 e4
          where
            benv1' = bind x benv1
            benv2' = bind y benv2
        (Lam x e1', Lam y e2') -> go (Map.insert x (Map.size benv1) benv1)
                                     (Map.insert y (Map.size benv2) benv2)
                                     e1' e2'
        (ConApp k1 xs, ConApp k2 ys) -> k1 == k2 && all (\(x,y) ->occ benv1 x == occ benv2 y) (zip xs ys)
        (Case e1 alts1, Case e2 alts2) -> go benv1 benv2 e1 e2
           && liftEq2 (==) alt alts1 alts2
           where
             alt (xs1,rhs1) (xs2,rhs2)
               | let benv1' = foldr bind benv1 xs1
               , let benv2' = foldr bind benv2 xs2
               = go benv1' benv2' rhs1 rhs2
        _                      -> False

type Label = String
label :: Exp -> Label
label e = case e of
  Lam x _     -> "\\lambda " ++ x ++ ".."
  ConApp k xs -> show k ++ "(" ++ showSep (showString ",") (map showString xs) [] ++ ")"
  _           -> undefined

isVal :: Exp -> Bool
isVal Lam{}    = True
isVal ConApp{} = True
isVal _        = False

appPrec, lamPrec :: Read.Prec
lamPrec = Read.minPrec
appPrec = lamPrec+1

-- | Example output: @F (λa. G) (H I) (λb. J b)@
instance Show Exp where
  showsPrec _ (Var v)      = showString v
  showsPrec p (App f arg)  = showParen (p > appPrec) $
    showsPrec appPrec f . showString " " . showString arg
  showsPrec p (Lam b body) = showParen (p > lamPrec) $
    showString "λ" . showString b . showString ". " . showsPrec lamPrec body
  showsPrec p (Let x e1 e2) = showParen (p > lamPrec) $
    showString "let " . showString x
    . showString " = " . showsPrec lamPrec e1
    . showString " in " . showsPrec lamPrec e2
  showsPrec _ (ConApp k xs) =
    shows k
    . showString "("
    . showSep (showString ",") (map showString xs)
    . showString ")"
  showsPrec p (Case e alts) = showParen (p > appPrec) $
    showString "case " . showsPrec lamPrec e
    . showString " of { "
    . showSep (showString ";") (map showAlt (Map.assocs alts))
    . showString " }"

showAlt :: (Tag,([Name],Exp)) -> ShowS
showAlt (k,(xs,rhs)) = shows (ConApp k xs) . showString " -> " . showsPrec lamPrec rhs

showSep :: ShowS -> [ShowS] -> ShowS
showSep _   [] = id
showSep _   [s] = s
showSep sep (s:ss) = s . sep . showString " " . showSep sep ss

-- | The default 'ReadP.many1' function leads to ambiguity. What a terrible API.
greedyMany, greedyMany1 :: ReadP.ReadP a -> ReadP.ReadP [a]
greedyMany p  = greedyMany1 p ReadP.<++ pure []
greedyMany1 p = (:) <$> p <*> greedyMany p

-- | This monster parses Exprs in the REPL etc. It parses names that start
-- with an upper-case letter as literals and lower-case names as variables.
--
-- Accepts syntax like
-- @let x = λa. g z in (λb. j b) x@
--
-- >>> read "g z" :: Exp
-- g z
--
-- >>> read "λx.x" :: Exp
-- λx. x
--
-- >>> read "let x = x in x" :: Exp
-- let x = x in x
--
-- >>> read "let x = λa. g z in (λb. j b) x" :: Exp
-- let x = λa. g z in (λb. j b) x
--
-- >>> read "let x = λa. let y = y in a in g z" :: Exp
-- let x = λa. let y = y in a in g z
--
-- >>> read "case λa.x of { Pair( x , y ) -> λa. let y = Pair(y,y) in g z }" :: Exp
-- case λa. x of { Pair(x, y) -> λa. let y = Pair(y, y) in g z }
--
-- >>> read "let x = T() in let o = Some(x) in case o of { None() -> F(); Some(y) -> y }" :: Exp
-- let x = T() in let o = Some(x) in case o of { None() -> F(); Some(y) -> y }
instance Read Exp where
  readPrec = Read.parens $ Read.choice
    [ Var <$> readName
    , Read.prec appPrec $ do
        -- Urgh. Just ignore the code here as long as it works
        let spaces1 = greedyMany1 (ReadP.satisfy isSpace)
        (f:args) <- Read.readP_to_Prec $ \prec ->
          ReadP.sepBy1 (Read.readPrec_to_P Read.readPrec (prec+1)) spaces1
        guard $ not $ null args
        let to_var e = case e of Var n -> Just n; _ -> Nothing
        Just xs <- pure $ traverse to_var args
        pure (foldl' App f xs)
    , Read.prec lamPrec $ do
        c <- Read.get
        guard (c `elem` "λΛ@#%\\") -- multiple short-hands for Lam
        Var v <- Read.readPrec
        '.' <- Read.get
        Lam v <$> Read.readPrec
    , Read.prec lamPrec $ do
        Read.Ident "let" <- Read.lexP
        x <- readName
        Read.Punc "=" <- Read.lexP
        e1 <- Read.readPrec
        Read.Ident "in" <- Read.lexP
        e2 <- Read.readPrec
        pure (Let x e1 e2)
    , do
        k <- Read.readPrec
        Read.Punc "(" <- Read.lexP
        let comma = ReadP.skipSpaces >> ReadP.char ',' >> ReadP.skipSpaces
        xs <- Read.readP_to_Prec $ \_ ->
          ReadP.sepBy (Read.readPrec_to_P readName lamPrec) comma
        Read.Punc ")" <- Read.lexP
        pure (ConApp k xs)
    , Read.prec lamPrec $ do
        Read.Ident "case" <- Read.lexP
        e <- Read.readPrec
        Read.Ident "of" <- Read.lexP
        Read.Punc "{" <- Read.lexP
        let semi = ReadP.skipSpaces >> ReadP.char ';' >> ReadP.skipSpaces
        alts <- (Map.fromList . map (\(k,xs,e) -> (k, (xs,e)))) <$>
          Read.readP_to_Prec (\_ -> ReadP.sepBy (Read.readPrec_to_P readAlt lamPrec) semi)
        Read.Punc "}" <- Read.lexP
        pure (Case e alts)
    ]
    where
      readName = do
        Read.Ident v <- Read.lexP
        guard (not $ v `elem` ["let","in","case","of"])
        guard (not $ head v `elem` "λΛ@#5\\")
        guard (isLower $ head v) -- Ensures that there is no clash with Tag
        guard (all (\c -> isAlphaNum c || c == '_') v)
        pure v
      readAlt = do
        ConApp k xs <- Read.readPrec
        Read.Punc p <- Read.lexP
        guard (p `elem` ["->","→"])
        e <- Read.readPrec
        pure (k,xs,e)

