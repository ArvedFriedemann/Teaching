{-# LANGUAGE DeriveGeneric #-}
module PredLanguage where
import Text.Parsec (
  Parsec,
  (<|>),
  try,
  many,
  many1,
  spaces,
  string,
  noneOf,
  oneOf,
  parse,
  getInput,
  tokenPrim,
  incSourceColumn,
  lookAhead,
  between,
  choice)
import Debug.Trace
import Control.Applicative hiding (many, (<|>))
import Data.List
import Data.Tuple.Update
import Data.Maybe
import Data.Map (Map, insert, member, singleton, lookup, fromList)
import Data.Either
import Text.Parsec.Error
import Test.QuickCheck.Text
import GHC.Generics

import Spacer
import ColorCodes

data Pred a = PredTree (Pred a) (Pred a) | Terminal a | Empty deriving (Show, Eq, Ord, Generic)

data PredGraph = PredNode Integer [PredGraph] deriving (Show, Eq, Ord)

instance Functor Pred where
  fmap f = foldPred
    (\a b  -> PredTree (fmap f a) (fmap f b))
    (\a    -> Terminal $ f a)
    Empty

lToPred::[Pred a] -> Pred a
lToPred = normalize.lToPred'

lToPred'::[Pred a] -> Pred a
lToPred' = lToPredEnd' Empty

lToPredEnd'::Pred a -> [Pred a] -> Pred a
lToPredEnd' end l = foldl (\x y -> PredTree x y) end l

--should not be used...is just confusing.
--  lToPredEndList::[Pred a] -> [Pred a] -> Pred a
--  lToPredEndList x l = lToPred $ l++(reverse x) --should be unreversed and the other way aroung when using foldr above

tList::[a] -> Pred a
tList l = lToPred $ Terminal <$> l

delimleftAsscLst::(Eq a) => Pred a -> Pred a -> [Pred a]
delimleftAsscLst delim t@(PredTree (PredTree a delim') b)
  | delim == delim' = b:(delimleftAsscLst delim a)
  | otherwise = [t]
delimleftAsscLst delip p = [p]

normalize::Pred a -> Pred a
normalize (PredTree Empty Empty) = Empty
normalize (PredTree Empty p) = normalize p
normalize (PredTree p Empty) = normalize p
normalize (PredTree a b) = PredTree (normalize a) (normalize b)
normalize p = p

-- exchange a b p = exchanges a to b in p
exchange::(Eq a) => Pred a -> Pred a -> Pred a -> Pred a
exchange a b p = transPred (\p' -> if a==p' then b else p') p

transPred::(Eq a)=>(Pred a -> Pred a) -> Pred a -> Pred a
transPred fkt p@(PredTree a b)
  | p'==p = PredTree (transPred fkt a) (transPred fkt b)
  | otherwise = p'
  where p' = fkt p
transPred fkt p = fkt p

depthPred p = depthPred' p 0
depthPred'::Pred a -> Int -> Pred (a, Int)
depthPred' (PredTree l r) depth = PredTree (depthPred' l (depth + 1)) (depthPred' r (depth + 1))
depthPred' (Terminal a)   depth = Terminal (a, depth)
depthPred' (Empty)        depth = Empty

normalizeDepth p = normalizeDepth' p (minDepth p)
normalizeDepth'::Pred (a, Int) -> Int -> Pred (a, Int)
normalizeDepth' p norm = fmap (\a -> (fst a, (snd a) - norm)) p

minMaybe :: Ord a => Maybe a -> Maybe a -> Maybe a
minMaybe Nothing b = b
minMaybe a Nothing = a
minMaybe (Just a) (Just b) = Just $ min a b

minDepth::Pred (a, Int) -> Int
minDepth p = fromMaybe 0 (minDepthMaybe p)
minDepthMaybe::Pred (a, Int) -> Maybe Int
minDepthMaybe p = foldPred func (\a -> Just (snd a)) (Nothing) p
  where func = (\a b  -> (minMaybe (minDepthMaybe a) (minDepthMaybe b)))

predWithDepth::Integer -> Pred String -> Pred String
predWithDepth depth p@(PredTree l r) | depth == 0 = (PredTree (Terminal "[..]") (Terminal "[..]"))
                                     | otherwise  = (PredTree (predWithDepth (depth - 1) l) (predWithDepth (depth - 1) r))
predWithDepth depth p@(Terminal a)   = p
predWithDepth depth p@(Empty)        = p

--predToTreeString = predToTreeString' white (predR white) (predColor)
predToGreyTreeString = predToTreeString' white (greyToggleLst)
predToTreeString = predToTreeString' white (redThenGreenDecreaseLst)
predToTreeString'::Integer->[Integer] -> Pred String -> String
predToTreeString' reset clrs p = predToTreeStringWithDepth' reset clrs (normalizeDepth $ depthPred p)

predToTreeStringWithDepth = predToTreeStringWithDepth' white (redThenGreenDecreaseLst)
predToTreeStringWithDepth'::Integer->[Integer] -> Pred (String, Int) -> String
predToTreeStringWithDepth' reset clrs = (.) predToString $ fmap (\(cont, d) -> (color (clrs !! d))++cont++(color reset))

--test colors: putStrLn $ predToTreeString $ predFromString "a^a^a^a^a^a^a^a^a^a^a^a^a^a^a"

predToString:: Pred String -> String
predToString a = predToString' a--deleteSpaces (isAlphaNumPred) (predToString' (a))

predToString'::Pred String -> String
predToString' (PredTree a b@(Terminal t)) = (predToString' a)++" "++(predToString' b)
predToString' (PredTree a b) = (predToString' a)++" ("++(predToString' b)++")"
predToString' (Terminal a) = a
predToString' (Empty) = ""--"え"

smoothUnlines::[String]->String
smoothUnlines [] = ""
smoothUnlines [x] = x
smoothUnlines x = "\n "++ (unlines $ ("   "++) <$> x)

--Operations---------------------------------------
variablesP::(Eq a) => Pred a -> [a]
variablesP = foldPred (\a b -> nub $ (variablesP a)++(variablesP b)) return []

t::a -> Pred a
t a = Terminal a

--PredListFkt -> TerminalFkt -> EmptyElement -> b
foldPred::(Pred a -> Pred a -> b) -> (a -> b) -> b  -> Pred a -> b
foldPred predListFkt _ _  (PredTree a b) = predListFkt a b
foldPred _ terminalFkt _  (Terminal a)   = terminalFkt a
foldPred _ _ emptyElem    (Empty)        = emptyElem

--syntax specific functions---------------------------
isAlphaNumPred::String -> Bool
isAlphaNumPred "" = False
isAlphaNumPred s = (elem (head s) alphaNumVarSpecHead) && (and $ ((flip elem) alphaNumVarSpecTail) <$> s )

--easier parsing---------------------

predFromString::String -> Pred String
predFromString input = case parse predicate "" input of
                          Right res -> res
                          Left err -> error (show err)

predFromFile::String -> IO (Pred String)
predFromFile filename = predFromString <$> (readFile filename)

--Parsing------------------------------------------
predicate::Parsec String st (Pred String)
predicate = try preds

preds::Parsec String st (Pred String)
preds = (lToPred <$>) $ many1 $ choice $ try <$> [
                  between (inBlanks $ string "(") (inBlanks $ string ")") preds,
                  predSpecA, predSpecB]

--should not be needed anymore
swapRightToLeftAssociativity::Pred a -> Pred a
swapRightToLeftAssociativity (PredTree a@(Terminal t) Empty) = PredTree Empty a
swapRightToLeftAssociativity (PredTree a@(Terminal t) (PredTree b c)) = PredTree (swapRightToLeftAssociativity $ PredTree a b) (swapRightToLeftAssociativity c)
swapRightToLeftAssociativity p = p

alphaNumVarSpecHead = ['a'..'z']++['A'..'Z']++(concat $ show <$> [0..9])
alphaNumVarSpecTail = alphaNumVarSpecHead++"'"

predSpecA::Parsec String st (Pred String)
predSpecA = do {
  blanks;
  p <- oneOf alphaNumVarSpecHead;
  p' <- many $ oneOf alphaNumVarSpecTail;
  blanks;
  return (Terminal $ p:p')
}

predSpecB::Parsec String st (Pred String)
predSpecB = do {
  blanks;
  p <- many1 $ noneOf $ alphaNumVarSpecTail++"()' \n\t";
  blanks;
  return (Terminal p)
}

--IO----------------
parseFile::String -> IO String--IO (Either (Text.Parsec.Error.ParseError) (Pred String)) -> String
parseFile filename = do {
  c <- readFile filename;
  return (either parseErrorToString predToString (parse predicate filename c))
}
parseErrorToString::Text.Parsec.Error.ParseError -> String
parseErrorToString errorMsg = foldl (\x y -> x ++ messageString y) "" (errorMessages errorMsg)

--Parsec Util------------------------
asList::Parsec a st b -> Parsec a st [b]
asList p = do{x <- p; return [x]}

blanks::Parsec String st String
blanks = many (oneOf " \n\t")

inBlanks::Parsec String st a -> Parsec String st a
inBlanks = between blanks blanks

parsecTrace::String->Parsec String st ()
parsecTrace s = trace s $ return ()

parsecTraceInput::Parsec String st ()
parsecTraceInput = do {
  ipt <- getInput;
  parsecTrace ipt
}

--util-----------------------

(><)::(a->b)->(a,a)->(b,b)
(><) f (x,y) = (f x, f y)
