module Sequent where

import Data.Map.Strict as M
import Data.Set as S

{- Expression, sequent and logical rules types -}

data Expr = Var String 
            | Expr :* Expr 
            | Expr :+ Expr 
            | Expr :-> Expr 
            | Not Expr deriving (Eq, Show)

data Sequent = [Expr] :- [Expr] deriving Show

data Derivation =   AntConj Derivation Sequent
                  | AntDisj Derivation Derivation Sequent
                  | AntImpl Derivation Derivation Sequent 
                  | AntNot  Derivation Sequent
                  | DesConj Derivation Derivation Sequent 
                  | DesDisj Derivation Sequent
                  | DesImpl Derivation Sequen

infixr 3 :->
infixl 6 :+
infixl 7 :*
infix 8 :-

p = Var "p"
q = Var "q"
r = Var "r"
a = Var "a"
b = Var "b"
c = Var "c"

{- Sequents and reduction trees examples -}

-- |- p & q & r -> r
seq1 = [] :- [(p :* q :* r :-> r)]

-- |- (b -> c) -> (a -> b) -> a -> c          
seq2 = [] :- [((b :-> c) :-> (a :-> b) :-> a :-> c)]

-- iTree1 = buildTree seq1
iTree1 = DesImpl (AntConj 
        (Axiom ([Var "p" :* Var "q",Var "r"] :- [Var "r"])) 
          ([(Var "p" :* Var "q") :* Var "r"] :- [Var "r"])) 
          ([] :- [(Var "p" :* Var "q") :* Var "r" :-> Var "r"])

-- iTree2 = buildTree seq2
iTree2 = DesImpl (AntImpl (DesImpl (AntImpl (DesImpl 
        (Axiom ([Var "a"] :- [Var "c",Var "a",Var "b"])) 
          ([] :- [Var "a",Var "a" :-> Var "c",Var "b"])) 
        (Axiom ([Var "b"] :- [Var "a" :-> Var "c",Var "b"])) 
          ([Var "a" :-> Var "b"] :- [Var "a" :-> Var "c",Var "b"])) 
          ([] :- [Var "b",(Var "a" :-> Var "b") :-> (Var "a" :-> Var "c")])) 
        (DesImpl (AntImpl (DesImpl 
        (Axiom ([Var "a",Var "c"] :- [Var "c",Var "a"])) 
          ([Var "c"] :- [Var "a",Var "a" :-> Var "c"])) 
        (DesImpl 
        (Axiom ([Var "a", Var "b", Var "c"] :- [Var "c"])) 
          ([Var "b",Var "c"] :- [Var "a" :-> Var "c"])) 
          ([Var "a" :-> Var "b",Var "c"] :- [Var "a" :-> Var "c"])) 
          ([Var "c"] :- [(Var "a" :-> Var "b") :-> (Var "a" :-> Var "c")])) 
          ([Var "b" :-> Var "c"] :- [(Var "a" :-> Var "b") :-> (Var "a" :-> Var "c")])) 
          ([] :- [(Var "b" :-> Var "c") :-> ((Var "a" :-> Var "b") :-> (Var "a" :-> Var "c"))])


isAxiom l r = any (==True) $ Prelude.map (\y -> any (\x -> x == y) l) r

isOnlyVars [] = True 
isOnlyVars (x:xs) = case x of 
                        Var _ -> True && isOnlyVars xs 
                        _ -> False

fstNotVar acc [] = (Nothing, acc)
fstNotVar acc (x:xs) = case x of 
                           Var _ -> fstNotVar (x : acc) xs
                           _ -> (Just x, acc ++ xs)

varsSequent (l :- r) = S.toList $ S.fromList $ (Prelude.fmap go (l ++ r)) !! 0 where go (Var v) = [v]
                                                                                     go (e1 :-> e2) = (go e1) ++ (go e2) 
                                                                                     go (e1 :+ e2) = (go e1) ++ (go e2)
                                                                                     go (e1 :* e2) = (go e1) ++ (go e2)
                                                                                     go (Not e) = go e

{- Reduction tree builder -}

buildTree (l :- r) | isAxiom l r = Axiom (l :- r)
                   | isOnlyVars l && isOnlyVars r = Сounter (l :- r)
                   | not (isOnlyVars l) && isOnlyVars r = let (Just v, ant) = fstNotVar [] l in goAnt v ant
                   | isOnlyVars l && not (isOnlyVars r) = let (Just v, des) = fstNotVar [] r in goDes v des
                   | otherwise = let (Just v, ant) = fstNotVar [] l in goAnt v ant
                    where goAnt v ant = case v of
                                        e1 :-> e2 -> AntImpl (buildTree $ ant :- (e1 : r)) (buildTree $ (e2 : ant) :- r) (l :- r)
                                        e1 :+ e2   -> AntDisj (~buildTree $ (e1 : ant) :- r) (buildTree $ (e2 : ant) :- r) (l :- r)
                                        e1 :* e2  -> AntConj (buildTree $ (e1 : e2 : ant) :- r) (l :- r)
                                        Not e      -> AntNot  (buildTree $ ant :- (e : r)) (l :- r)
                          goDes v des = case v of
                                        e1 :-> e2 -> DesImpl (buildTree $ (e1 : l) :- (e2 : des)) (l :- r)
                                        e1 :+ e2   -> DesDisj (buildTree $ l :- (e1 : e2 : des)) (l :- r)
                                        e1 :* e2  -> DesConj (buildTree $ l :- (e1 : des)) (buildTree $ l :- (e2 : des)) (l :- r)
                                        Not e      -> DesNot (buildTree $ (e : l) :- des) (l :- r)

{- Derivation builder -}

deriveSequent :: Sequent -> Either (M.Map String Bool) Derivation
deriveSequent seq = let tree = buildTree seq 
                        getUnique b xs = fromSet (\x -> b) (S.fromList (Prelude.map (\(Var x) -> x) xs))
                     in case tree of
                        (Сounter (l :- r)) -> Left $ M.union (getUnique True l) (getUnique False r)
                        _ -> let m = go vars tree 
                                 vars = varsSequent seq 
                              in if M.null m 
                                 then Right tree 
                                 else Left m  
                                 where go v (Axiom _) = M.empty
                                       go v (Сounter (l :- r)) = let c = M.union (getUnique True l) (getUnique False r) 
                                                                 in if length c == length v
                                                                     then c
                                                                     else M.empty
                                       go v (AntConj d _) = go v d
                                       go v (AntDisj l r _) = getRightVars v (go v l) (go v r)
                                       go v (AntImpl l r _) = getRightVars v (go v l) (go v r)
                                       go v (AntNot d _) = go v d
                                       go v (DesConj l r _) = getRightVars v (go v l) (go v r)
                                       go v (DesDisj d _) = go v d
                                       go v (DesNot d _) = go v d
                                       go v (DesImpl d _) = go v d
                                       getUnique b xs = fromSet (\x -> b) (S.fromList (Prelude.map (\(Var x) -> x) xs))
                                       getRightVars v l r | length l == length v = l
                                                         | length r == length v = r
                                                         | otherwise = M.empty
 