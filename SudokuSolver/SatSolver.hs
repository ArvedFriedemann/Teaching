module SatSolver where
import Picosat
import Data.List
--import PredLanguage
import Data.Maybe

type IntSolution = [Int]

extract :: Solution -> Maybe IntSolution
extract (Solution list) = Just list
extract Unsatisfiable   = Nothing
extract Unknown         = Nothing

solveList :: [[Int]] -> Maybe IntSolution
solveList to_solve = extract $ unsafeSolve to_solve

solveListAll::[[Int]] -> [IntSolution]
solveListAll to_solve = catMaybes $ extract <$> unsafeSolveAll to_solve

satisfiable :: Solution -> Bool
satisfiable (Solution list) = True
satisfiable Unsatisfiable   = False
satisfiable Unknown         = False

solveBool :: [[Int]] -> Bool
solveBool = isJust.solveList

--predToSat :: Pred a -> [[Int]]
--predToSat pred = []
