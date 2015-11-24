{-# LANGUAGE FlexibleInstances, TypeFamilies #-}

import Prelude hiding (not)
import Control.Arrow
import Data.Monoid

class Booly b where
  (∨) :: b -> b -> b
  (∧) :: b -> b -> b
  not :: b -> b

class HasVariables b where
  type VarIndex b :: *
  lit :: VarIndex b -> b
  newVariables :: b -> [VarIndex b]

infixr 2 :∨, ∨
infixr 3 :∧, ∧
  

type Negation = Any

type CNFClause a = [(Negation, a)]

type CNF a = [CNFClause a]

instance Booly (CNF a) where
  -- conjunction is just concatenation of clause-lists:
  p₁ ∧ p₂ = p₁ ++ p₂
  
  -- use distributive law to implement disjunction:
  p₁ ∨ p₂ = [c₁ ++ c₂ | c₁<-p₁, c₂<-p₂]
  
  -- use De Morgan's law to implement negation of the conjunction of clauses
  -- as disjunction of the individual negations.
  not (p₁:ps) = [[first (Any False<>) x] | x <- p₁] ∨ not ps
  not [] = [[]]

instance (Enum a, Ord a) => HasVariables (CNF a) where
  type VarIndex (CNF a) = a
  lit x = [[(Any False, x)]]
  newVariables cnfs = tail [highest..]
   where highest = maximum $ map (maximum . map snd) cnfs


newtype CNF3Clause a = CNF3Clause {get3Clause :: CNFClause a} deriving (Show)

type CNF3 a = [CNF3Clause a]

getCNF3 :: CNF3 a -> CNF a
getCNF3 = map get3Clause

instance (Enum a, Ord a) => HasVariables (CNF3 a) where
  type VarIndex (CNF a) = a
  lit x = [CNF3Clause [(Any False, x)]]
  newVariables = newVariables . getCNF3

instance Booly (CNF3 a) where
  p₁ ∧ p₂ = p₁ ++ p₂
  
  -- short single-clause formulas can just be merged.
  [CNF3Clause [x]] ∨ p | all ((<3) . length . get3Clause) p
                       = map (\(CNF3Clause c) -> CNF3Clause (x:c))
  p ∨ [CNF3Clause [x]] | all ((<3) . length . get3Clause) p
                       = map (\(CNF3Clause c) -> CNF3Clause (x:c))
  -- For larger disjunctions, introduce new variables that represent
  -- satisfaction of either of the subequations.
  p₁ ∨ p₂ = (lit z₁∨lit z₂) ∧ (not(lit z₁)∨p₁) ∧ (not(lit z₂)∨p₂)
   where (z₁:z₂:_) = newVariables (p₁ ++ p₂)
  
  not (p₁:ps) = [[first (Any False<>) x] | x <- p₁] ∨ not ps
  not [] = [[]]
  

satTo3sat :: CNFClause Integer -> CNF3 Integer
satTo3sat p
  | l<=3       = [CNF3Clause p]
  | otherwise  = lit z ++ []
 where l = length p
       (pl,pr) = splitAt (l`div`2) p
       p'l = satTo3sat pl
       p'r = satTo3sat pr
       z = newVariable (p'l ++ p'r)



-- type NAE3CNF a = CNF3 a  -- interpreted differently: `:|` means
-- 
-- o3CNFToNAE3CNF :: CNF3Clause a -> CNF3 a
-- -- For a single disjunction, it's impossible
-- o3CNFToNAE3CNF (LitC n x) = [LitC n x :| LitC (not n) x]
-- o3CNFToNAE3CNF (LitC n x) = [LitC n x :| LitC (not n) x]

data SAT a = Lit a
           | Not (SAT a)
           | SAT a :∨ SAT a
           | SAT a :∧ SAT a
    deriving (Show)

instance Booly (SAT a) where
  (∨) = (:∨)
  (∧) = (:∧)
  not (Not a) = a
  not a = (Not a)

asSAT :: CNF a -> SAT a
asSAT = foldr1 (∧) . map (foldr1 (∨) . map mkLit)
 where mkLit (Any False, x) = Lit x
       mkLit (Any True, x) = Not (Lit x)


instance Booly Bool where
  (∨) = (||)
  (∧) = (&&)
  not False = True
  not True = False
