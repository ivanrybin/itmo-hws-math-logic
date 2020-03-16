{-

	Mathematical logic.	
  Truth table and disjunctive normal form builder.

	Ivan Rybin, 2020.
  
-}

import Data.Set as Set hiding (map)

data Expr = Var String 
            | Expr :* Expr 
            | Expr :+ Expr 
            | Expr :-> Expr 
            | Not Expr deriving (Eq, Show)

type TruthTable = [([Bool], Bool)]

propVars :: Expr -> Set String
propVars (Var v) = Set.singleton v
propVars (Not e) = propVars e
propVars (e1 :* e2) = propVars e1 `Set.union` propVars e2
propVars (e1 :+ e2) = propVars e1 `Set.union` propVars e2

makeDict :: [String] -> [(String, Int)]
makeDict xs = go xs 0 where go [] i = []
                            go (x:xs) i = (x, i) : go xs (i + 1)

genBools :: [a] -> [[Bool]]
genBools = sequence . map (\v -> [True, False])

truthTable :: Expr -> TruthTable
truthTable exp = let vars = makeDict $ toList $ propVars exp
                     bools = genBools vars
                  in go bools vars 
                        where go [] vars = [] 
                              go (r:rs) vars = (r, getExpRes exp r vars) : go rs vars
                                                            where getExpRes (Var x) r vs = let Just i = lookup x vs in r !! i
                                                                  getExpRes (Not e) r vs = not $ getExpRes e r vs
                                                                  getExpRes (e1 :* e2) r vs = (getExpRes e1 r vs) && (getExpRes e2 r vs)
                                                                  getExpRes (e1 :+ e2) r vs = (getExpRes e1 r vs) || (getExpRes e2 r vs)

fdnf :: TruthTable -> Expr
fdnf [] = Var "True"
fdnf (b:bs) = case b of
                  (vars, True) -> (go vars 0) :+ (fdnf bs) where go [] i = Var "True"
                                                                 go (True:xs) i = (Var ("x" ++ show i)) :* (go xs (i + 1))
                                                                 go (False:xs) i = (Not (Var ("x" ++ show i))) :* (go xs (i + 1))
                  (_, False) -> fdnf bs
