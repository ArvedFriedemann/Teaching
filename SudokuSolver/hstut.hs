module Sudoku where

import Data.List
import Formulas hiding (neg)
import Data.Maybe

type FEntr = (Int,Int)
type EQConst a b = (a,b)

neg::Lit a -> Lit a
neg (Pos x) = Neg x
neg (Neg x) = Pos x

isPos::Lit a -> Bool
isPos (Pos _) = True
isPos _ = False

toPos::[a] -> [Lit a]
toPos lst = Pos <$> lst

onlyPos::[Lit a] -> [Lit a]
onlyPos lst = filter isPos lst

(==>)::Lit a -> Lit a -> Clause a
(==>) x y = [neg x, y]

headsTails::[[a]] -> ([a],[[a]])
headsTails lst = (head <$> lst, tail <$> lst)

exactlyOne::(Eq a) => [a] -> Formula a
exactlyOne = exactlyOne'.toPos

exactlyOne'::(Eq a) => [Lit a] -> Formula a
exactlyOne' lst = [x ==> neg y | x <- lst, y <- lst, x/=y] ++ [lst]

alldiffVec::(Eq a) => [[Lit a]] -> Formula a
alldiffVec lst = concatMap exactlyOne' (transpose lst)

sudokuConstr::Formula (EQConst FEntr Int)
sudokuConstr = concat $
  [exactlyOne' [Pos ((x,y), n) | n <- [1..9]]   | x <- [1..9], y <- [1..9]] ++
  [alldiffVec [[Pos ((x,y), n) | n <- [1..9]] | y <- [1..9]] | x <- [1..9]] ++
  [alldiffVec [[Pos ((x,y), n) | n <- [1..9]] | x <- [1..9]] | y <- [1..9]] ++
  [alldiffVec [[Pos ((x,y), n) | n <- [1..9]] | x <- [(1+dx)..(3+dx)], y <- [(1+dy)..(3+dy)] ] | dx<-(*3)<$>[0..2],dy<-(*3)<$>[0..2]]

sudoku1::Formula (EQConst FEntr Int)
sudoku1 = ((map.map) Pos
          [ [((1,1),3)],
            [((1,2),1)],
            [((1,7),4)],
            [((1,8),9)],
            [((1,9),6)],

            [((2,1),8)],
            [((2,4),5)],
            [((2,5),1)],
            [((2,6),4)],

            [((3,1),2)],
            [((3,2),4)],
            [((3,4),9)],
            [((3,7),5)],

            [((4,2),9)],
            [((4,5),8)],
            [((4,7),7)],
            [((4,8),5)],

            [((5,2),7)],
            [((5,3),6)],
            [((5,5),4)],
            [((5,7),2)],
            [((5,8),3)],

            [((6,2),2)],
            [((6,3),8)],
            [((6,5),3)],
            [((6,6),5)],
            [((6,7),6)],

            [((7,1),9)],
            [((7,3),1)],
            [((7,4),3)],
            [((7,6),6)],
            [((7,9),2)],

            [((8,4),4)],
            [((8,6),8)],
            [((8,8),6)],
            [((8,9),5)],

            [((9,1),6)],
            [((9,3),4)],
            [((9,8),7)],
            [((9,9),3)]
            ]) ++ sudokuConstr

solve :: String -> IO ()
solve fn = do {
  ins <- readFile fn;
  sud <- return $ makeSudoku (parseSudoku ins);
  case solveFormula sud of
    Just lits -> putStrLn $ unlines $ (map $ concat.(intersperse " ")) $
                  ((map.map) show) $
                  ((map.map) fromJust) $
                  fromCoords $ (var <$>) $ onlyPos lits
    Nothing -> putStrLn "no Solution!"
}

makeSudoku :: [EQConst FEntr Int] -> Formula (EQConst FEntr Int)
makeSudoku initials = (map (return.Pos) initials) ++ sudokuConstr

parseSudoku :: String -> [EQConst FEntr Int]
parseSudoku str = catMaybes $ map (\(c,i) -> (\i' -> (c,i')) <$> i) $ (toCoords $ parseSudoku' str)
parseSudoku' :: String -> [[Maybe Int]]
parseSudoku'  (x11:' ':x12:' ':x13:' ':x14:' ':x15:' ':x16:' ':x17:' ':x18:' ':x19:'\n':
               x21:' ':x22:' ':x23:' ':x24:' ':x25:' ':x26:' ':x27:' ':x28:' ':x29:'\n':
               x31:' ':x32:' ':x33:' ':x34:' ':x35:' ':x36:' ':x37:' ':x38:' ':x39:'\n':
               x41:' ':x42:' ':x43:' ':x44:' ':x45:' ':x46:' ':x47:' ':x48:' ':x49:'\n':
               x51:' ':x52:' ':x53:' ':x54:' ':x55:' ':x56:' ':x57:' ':x58:' ':x59:'\n':
               x61:' ':x62:' ':x63:' ':x64:' ':x65:' ':x66:' ':x67:' ':x68:' ':x69:'\n':
               x71:' ':x72:' ':x73:' ':x74:' ':x75:' ':x76:' ':x77:' ':x78:' ':x79:'\n':
               x81:' ':x82:' ':x83:' ':x84:' ':x85:' ':x86:' ':x87:' ':x88:' ':x89:'\n':
               x91:' ':x92:' ':x93:' ':x94:' ':x95:' ':x96:' ':x97:' ':x98:' ':x99:xs) =
                 (map.map) convert $
                 [[x11,x12,x13,x14,x15,x16,x17,x18,x19],
                  [x21,x22,x23,x24,x25,x26,x27,x28,x29],
                  [x31,x32,x33,x34,x35,x36,x37,x38,x39],
                  [x41,x42,x43,x44,x45,x46,x47,x48,x49],
                  [x51,x52,x53,x54,x55,x56,x57,x58,x59],
                  [x61,x62,x63,x64,x65,x66,x67,x68,x69],
                  [x71,x72,x73,x74,x75,x76,x77,x78,x79],
                  [x81,x82,x83,x84,x85,x86,x87,x88,x89],
                  [x91,x92,x93,x94,x95,x96,x97,x98,x99]]

convert :: Char -> Maybe Int
convert 'x' = Nothing
convert  x  = Just $ read [x]

toCoords::[[a]] -> [((Int,Int),a)]
toCoords lst = concat [ [((rid,cid), col) | (col, cid) <- zip row posNatp ] | (row, rid) <- zip lst posNatp]

posNatp :: [Int]
posNatp = fromIntegral <$> [1..]

posNatpU :: Int -> [Int]
posNatpU k = fromIntegral <$> [1..k]

fromCoords :: [((Int,Int),a)] -> [[Maybe a]]
fromCoords coords = [ [ lookup (x,y) coords | y <- posNatpU maxy] | x <- posNatpU maxx]
  where maxx = maximum $ map (\((x,_),_) -> x) coords
        maxy = maximum $ map (\((_,y),_) -> y) coords
