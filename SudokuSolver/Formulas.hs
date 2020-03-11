{-# LANGUAGE DeriveGeneric #-}
module Formulas where
import Control.Applicative
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import GHC.Generics

import SatSolver

import Control.Monad.State

--Major definitions-------------------------
-- | A literal carries some variable declaration that is either held positive or negative.
-- this way, formulas over Integers, String or other objects can be build.
data Lit a = Pos a | Neg a deriving(Show, Eq, Ord, Generic)
instance Functor Lit where
  fmap f (Pos a) = Pos (f a)
  fmap f (Neg a) = Neg (f a)

type Clause a = [Lit a]
type Formula a = [Clause a]
type BV = [Bool]

type VarState a = State [a]

getRes::[a] -> VarState a b -> b
getRes v m = evalState m v

getN::VarState a a
getN = do{
  l <- get;
  put $ tail l;
  return $ head l
}

getN'::(a-> b) -> VarState a b
getN' f = f <$> getN

takeN::Int -> VarState a [a]
takeN i = sequence $ replicate i getN

zipN::[b] -> VarState a [(b,a)]
zipN = zipN' id

zipN'::(a-> b) -> [c] -> VarState a [(c,b)]
zipN' f [] = return []
zipN' f (x:xs) = do{ n<-getN' f; rest <- zipN' f xs; return $ (x,n):rest }

unzipN::[b] -> VarState a ([b],[a])
unzipN l = unzip <$> (zipN l)

unzipN'::(a->b) -> [c] -> VarState a ([c],[b])
unzipN' f l = unzip <$> (zipN' f l)

zipWithN::(b->a->c) -> [b] -> VarState a [c]
zipWithN _ [] = return []
zipWithN f (x:xs) = do{ n<-getN; nx <- zipWithN f xs; return $(f x n):nx }

zipWithN'::(a->b) -> (c->b->d) -> [c] -> VarState a [d]
zipWithN' _ _ [] = return []
zipWithN' f0 f (x:xs) = do{ n<-getN' f0; nx <- zipWithN' f0 f xs; return $(f x n):nx }

unzipWithN::(b->a->(c,d)) -> [b] -> VarState a ([c],[d])
unzipWithN = unzipWithN' id

unzipWithN'::(a->b) -> (c->b->(d,e)) -> [c] -> VarState a ([d],[e])
unzipWithN' f0 f l = unzip <$> (zipWithN' f0 f l)

--baking------------

bakeMatrix::[[VarState a b]] -> VarState a [[b]]
bakeMatrix = sequence.(map sequence)

--Equations for Literals----------------------

-- | Retrieves a Literal from an integer i, where the polarity is stored in its sign
fromInt::Int -> Lit Int
fromInt i
  |i >= 0 = Pos i
  |otherwise = Neg (abs i)

-- | Inverse of fromInt
toInt::Lit Int -> Int
toInt (Pos i) = i
toInt (Neg i) = -i

-- | Retrieves the variable theliteral is referring to
var::Lit a -> a
var (Pos l) = l
var (Neg l) = l

(<~~>)::(Eq a) => Lit a -> Lit a -> Bool
(<~~>) a b = (var a)==(var b)

-- | Translates the stream of variablesF into a stream of corresponding positive literals
pLits::[a] -> [Lit a]
pLits = map Pos

toPLit::Lit a -> Lit a
toPLit l = Pos $ var l

toNLit::Lit a -> Lit a
toNLit l = Neg $ var l

-- | Translates the stream of variablesF into a stream of corresponding negative literals
nLits::[a] -> [Lit a]
nLits = map Neg

boolToLit::Bool -> a -> Lit a
boolToLit True a = Pos a
boolToLit False a = Neg a

litToBool::Lit a -> Bool
litToBool (Pos a) = True
litToBool (Neg a) = False

-- | Gives a stream of infinite variablesF starting from a
varStream::(Enum a) => a -> [a]
varStream = iterate succ

-- | Gives a stream of infinite numbered Sring variablesF starting with the given prefix
stringVarStream::String -> [String]
stringVarStream prefix = ((prefix++).show) <$> [1..]

-- | String variable stream starting with prefix "v"
stdStringVarStream::[String]
stdStringVarStream = stringVarStream "v"

-- | Gives a stream of infinite literals starting from a
lits::(Enum a) => a -> [Lit a]
lits a = map Pos (varStream a)

-- | negates a literal
negLit::Lit a -> Lit a
negLit (Pos l) = Neg l
negLit (Neg l) = Pos l

--Equations for Formulas-----------------------------

-- Useful constants-----------------------------------
emptyFormula = ([])
unsatFormula = ([[]])

-- | Formula only containing a clause with the given literal
olf::Lit a -> Formula a
olf l = [[l]]

-- | Formula only containing the given clause
ocf::Clause a -> Formula a
ocf c = [c]

toFacts::[Lit a] -> Formula a
toFacts = map return

toNegFacts::[Lit a] -> Formula a
toNegFacts = toFacts.(negLit<$>)

-- | Apply the given function to all variablesF in the Formula
mapVars::(a->b) -> Formula a -> Formula b
mapVars fkt f = mapLits (fkt <$>) f

-- | Apply the given function to all literals in the Formula
mapLits::(Lit a -> Lit b) -> Formula a -> Formula b
mapLits = (map.map)

-- | Apply the given function to all clauses in the Formula
mapClauses::(Clause a -> Clause b) -> Formula a -> Formula b
mapClauses = map

-- | Retrieve a well formatted formula from a list of integers, were the Polarity
-- of each literal is determined by the sign of the number
fromIntList::[[Int]]->Formula Int
fromIntList l = (map.map) fromInt l

-- | Conjunct two formulas regardless of context. Deprecated. Better use andf'
(°°)::Formula a -> Formula a -> Formula a
(c1) °° (c2) = (c1++c2)

-- | Exchange if a is equal to b return c. Otherwise keep a. This way for example all
-- literals with a specific variable can be removed while the others stay the same.
exchangeIfEqual::(Eq a) => a -> a -> a -> a
exchangeIfEqual out comp i
  | i == comp = out
  | otherwise = i

-- | Exchange all variablesF l with m
exchangeLit::(Eq a) => Formula a -> a -> a -> Formula a
exchangeLit f l m = mapVars (exchangeIfEqual l m) f

-- | Returns the set of variablesF in the formula
variablesF::(Eq a) => Formula a -> [a]
variablesF clauses = nub $ map var (concat clauses)

-- | Gives the highest variable in case the formula resonates over ordered variablesF
maxVar::(Ord a) => Formula a -> a
maxVar = maximum.variablesF

-- | Gives the next Var of a formula over ordered enumerable variablesF. Can be used
-- to construct a variable stream, but is not recommended.
nextVar::(Ord a, Enum a) => Formula a -> a
nextVar [] = toEnum 0
nextVar f = (succ.maximum.variablesF) f

--Boolean pointer operations------------------

-- | Adds a pointer variable to the formula such that all clauses are validated ("crossed out")
-- in case the literal evaluates to true. In case the literal validates to false
-- the formula remains untouched
addPointer::Lit a -> Formula a -> Formula a
addPointer l = mapClauses ([l]++)

-- | Mingles the given pointer into the formula, returning the pointer used and
-- the formula containing the pointer. Could be improved by not using the given pointer
-- but a pointer already contained in the formula, as is the case with one-literal formulas.
-- this special case is addressed in the _buildFormulaPointer function but should be handled
-- with caution as it has not been proven by the creator wether this optimization works when taking
-- context into consideration.
buildFormulaPointer::Formula a -> Lit a ->  (Lit a, Formula a)
buildFormulaPointer f l = (l, addPointer l f)

buildFormulaPointers::[Lit a] -> [Formula a] -> [(Lit a, Formula a)]
buildFormulaPointers = undefined

--getPointersN::[Formula a] -> [(Lit a, Formula a)]
--getPointersN fs = do{() <- zipN fs >>= unzip}

-- | Build an optimized pointer but use the existing pointer in case the formula is a one-literal-formula.
-- Warning: Correctness not proven!
_buildFormulaPointer::Formula a -> Lit a -> (Lit a, Formula a)
_buildFormulaPointer [[l]] _  = (negLit l, [])
_buildFormulaPointer f l = buildFormulaPointer f l

--Context preserving operations---------------

-- | Take one element from the source list every n elements
every::Int -> [a] -> [a]
every n = every' n 0
  where
    every' _ _ [] = []
    every' n 0 (x:xs) = x:(every' n (n-1) xs)
    every' n k (x:xs) = (every' n (k-1) xs)

-- | Splits the stream into two streams, distributing the elements evenly among the two streams
splitEveryOtherA::[a] -> ([a], [a])
splitEveryOtherA l = (\([x,y]) -> (x,y)) (splitInto 2 l)

-- | Split the stream into the given amount of disjunct substreams
splitInto::Int -> [a] ->[[a]]
splitInto n list = map (\i -> every n (drop i list)) [0..(n-1)]

-- |
streamBVMachine::[BV] -> [BV]
streamBVMachine = concatMap streamBVvars'

-- | Infinite List of bitvectors
streamBVvars::[BV]
streamBVvars = concat $ iterate streamBVMachine [[]]

streamBVvars'::BV -> [BV]
streamBVvars' n = [False:n, True:n]

-- | Works like splitEveryOther only for Bitvectors
splitEveryOther::[BV] -> ([BV], [BV])
splitEveryOther l = (map (False:) l, map (True:) l)

splitInfinite::[BV] -> [[BV]]
splitInfinite = (\(x,y) -> x:(splitInfinite y)).splitEveryOther

-- | Split into an infinite amount of streams. Warning: gets quite slow the more variablesF are used when discarding
-- subsequent streams.
splitInfiniteA::[a]->[[a]]
splitInfiniteA = (\(x,y) -> x:(splitInfiniteA y)).splitEveryOtherA
--axioms:
--forall a,b. (\l -> [k | k<-l, j<-(delete k l), k==j]) $ take a $ map (take b) $ splitInfinite [1..]   =   []

-- | Splits the stream into n-sized packages of finite streams
splitToSize::Int-> [a]-> [[a]]
splitToSize n l = (take n l):(splitToSize n (drop n l) )

splitMapF::[a] -> [([a]->b)] -> [b]
splitMapF ls fkts = map (\(a,b) -> a b) $ zip fkts (splitInto (length fkts) ls)

--debugging-----------------------------------
facts::Formula a -> [Lit a]
facts f = [head c | c <- f, (length c) == 1]

removeFacts::(Eq a) => Formula a -> Formula a
removeFacts form = [c \\ (negLit <$> fts) | c <- form, null $ intersect c fts]
  where fts = facts form

isTriviallyUNSAT::Formula a -> Bool
isTriviallyUNSAT = any null

unitPropagation::(Eq a) => Formula a -> [Lit a]
unitPropagation = concat.unitPropagation'

unitPropagation'::(Eq a) => Formula a -> [[Lit a]]
unitPropagation' = (facts <$>).unitPropagationParts

unitPropagationParts::(Eq a) => Formula a -> [Formula a]
unitPropagationParts = finIterate removeFacts

finIterate::(Eq a) => (a->a)->a->[a]
finIterate f a
  | (f a) == a = return a
  | otherwise = a:(finIterate f (f a))

--Boolean formula operations------------------

-- | "No Context Formula Operation" -> Operations transforming multiple formulas into one formula
type NCFOP a = ([Formula a]-> Formula a)
-- | "Multiple Formulas Operation" -> Operations transforming multiple formulas into one formula
-- propably using variablesF from the given variable stream.
type MFOP a  = ( [Formula a] -> VarState a (Formula a))
type MFOPN a  = ( [VarState a (Formula a)] -> VarState a (Formula a))
-- | "Formula Operation" -> Operation transforming a formula propably using additional variablesF from the given stream
type FOP a  = ( Formula a-> VarState a (Formula a))

(>>>)::(Monad m) => ([a] -> m b) -> [m a] -> m b
(>>>) f lst = sequence lst >>= f

-- | Conjuncting formulas
andf::MFOP a
andf fs = return $ andf' fs

-- | Conjuncting formulas without additional context stream. Works just as andf
andf'::NCFOP a
andf' fs = foldr (°°) emptyFormula fs

-- | Disjuncting formulas. Only optimized by basic Tseitin-like encoding.
orf::(Eq a) => MFOP a
orf fs = do{
  (ptrs, forms) <- unzipWithN' Pos buildFormulaPointer fs;
  negPtrs <- return $ map negLit ptrs;
  --WARNING! This is only for uniqueness of the solution! Will slow the solver down!
  -- oneOfK <- return $ [ [negLit a, negLit b] | a <- negPtrs, b <- negPtrs];
  -- ++[oneOfK]
  andf $ forms ++ [ocf negPtrs]
}

-- | Negating a clause to a formula in wich the clause is violated
negClause::Clause a -> Formula a
negClause = andf'.(olf <$>).(negLit <$>)

-- | Negate a FOrmula. Only optimized with the basic orf optimizations.
neg::(Eq a) => FOP a
neg f = orf $ negClause <$> f

--Flattening Formulas---------------------------------------------

flattenLit::(Eq a) => Lit (Formula a) -> VarState a (Formula a)
flattenLit (Pos f) = return f
flattenLit (Neg f) = neg f

flattenClause::(Eq a) => Clause (Formula a) -> VarState a (Formula a)
flattenClause clause = (sequence $ flattenLit <$> clause) >>= orf

flattenFormula::(Eq a) => Formula (Formula a) -> VarState a (Formula a)
flattenFormula f = (sequence $ flattenClause <$> f) >>= andf

--applications of flatten
implies::(Eq a) => Formula a -> Formula a ->  VarState a (Formula a)
implies f1 f2 = flattenFormula [[Neg f1, Pos f2]]

equivalence::(Eq a) => Formula a -> Formula a ->  VarState a (Formula a)
equivalence f1 f2 = sequence [implies f1 f2, implies f2 f1] >>= andf

--Conversions and interpretations---------------------------------

-- | interpret a Formula by the given interpretation function.
interpret::(a->b) -> Formula a -> Formula b
interpret = mapVars

-- | Build an integer interpretations numbering all variablesF in the formula
integerInterpretation::(Ord a) => Formula a -> (a -> Int)
integerInterpretation f = (Map.!) (Map.fromList (zip (variablesF f) [1..]))

-- | reverse interpretation for the integerInterpretation
reverseIntegerInterpretation::(Ord a) => Formula a -> (Int -> a)
reverseIntegerInterpretation f = (Map.!) (Map.fromList (zip [1..] (variablesF f)))

toIntList::Formula Int -> [[Int]]
toIntList = (map.map) toInt

--solving---------------------------------------------------------
--TODO: cleanup!
solveFormula::(Ord a) => Formula a -> Maybe [Lit a]
solveFormula f = do {
  s <- solveList $ toIntList $ (interpret (integerInterpretation f) f);
  return $ (reverseIntegerInterpretation f <$>) <$> (fromInt <$> s)
}

solveAllFormula::(Ord a) => Formula a ->  [[Lit a]]
solveAllFormula f = do {
  s <- solveListAll $ toIntList $ (interpret (integerInterpretation f) f);
  return $ (reverseIntegerInterpretation f<$>) <$> (fromInt <$> s)
}

safeSolveAllOf::(Ord a) => [Lit a] -> Formula a -> [[Lit a]]
safeSolveAllOf lts f = solveAllOf lts (f°°[[Neg l, Pos l]| l <- var<$>lts])

--only works if the given literals are contained in the formula
solveAllOf::(Ord a) => [Lit a] -> Formula a -> [[Lit a]]
solveAllOf [] form = maybeToList $ solveFormula form
solveAllOf lts form = case maybeToList $ solveFormula form of
                        [] -> []
                        [s] -> s:(solveAllOf lts $ form°°(toNegFacts $ onlyLits lts s))

diffSolution::(Eq a) => [Lit a] -> [Lit a] -> [Lit a]
diffSolution a b = filter (\x -> not $ elem x b) (intersectBy (\a b -> a <~~> b) a b)

--only take the literals from the second list whose names occur in the first list.
onlyLits::(Eq a) => [Lit a] -> [Lit a] -> [Lit a]
onlyLits  names = filter $ (flip elem (var <$> names)).var

--Visuals---------------------------------------------------------

-- | Showing a literal using a sign for polarity
cnfLit::(Show a) => Lit a -> String
cnfLit (Pos l) = show l
cnfLit (Neg l) = '-':(show l)

-- | Concatenating the string representation of all literals intercalated with a space
clauseToString:: (Show a) => Clause a-> String
clauseToString c = intercalate " " (map cnfLit c)

-- | Putting the given formula into the glorious dimacs format.
dimacs:: (Show a, Ord a) => Formula a-> String
dimacs f =
  "p cnf "++(show (length $ variablesF f))++" "++(show (length f)) ++
  (concatMap (++" 0") (map (("\n"++).clauseToString) f ) )


--Util--------------------------

-- | if ? then a else b
ite::Bool -> b -> b -> b
ite True t f = t
ite False t f = f

cmpLitCon::(Eq a)=>Lit a -> Lit a -> Bool
cmpLitCon a b = (var a) == (var b)

cmpLitPol::Lit a -> Lit a -> Bool
cmpLitPol (Pos _) (Pos _) = True
cmpLitPol (Neg _) (Neg _) = True
cmpLitPol _       _       = False
