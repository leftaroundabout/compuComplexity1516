{-# LANGUAGE FlexibleInstances #-}

import Prelude hiding (not)
import Control.Arrow
import Data.Monoid

class Booly b where
  (∨) :: b -> b -> b
  (∧) :: b -> b -> b
  not :: b -> b

class HasVariables b where
  lit :: x -> b x
  newVariable :: (Enum x, Ord x) => b x -> x

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

instance HasVariables CNF where
  lit x = [[(Any False, x)]]
  newVariable cnfs = succ highest where highest = maximum $ map (maximum . snd) cnfs


newtype CNF3Clause a = CNF3Clause {get3Clause :: CNFClause a} deriving (Show)

type CNF3 a = [CNF3Clause a]

getCNF3 :: CNF3 a -> CNF a
getCNF3 = map get3Clause

instance Booly (CNF3 a) where
  -- conjunction is still just concatenation:
  p₁ ∧ p₂ = p₁ ++ p₂
  
  -- De Morgan's law works as before.
  not (CNF3Clause p₁:ps) = [CNF3Clause [first (Any False<>) x] | x <- p₁] ∨ not ps
  not [] = [CNF3Clause[]]
                
  -- defer to ordinary CNF to implement disjunction. 
  p₁ ∨ p₂ = cnfTo3CNF =<< getCNF3 p₁ ∨ getCNF3 p₂
  

satTo3sat :: CNFClause Integer -> CNF3 Integer
satTo3sat p
  | l<=3       = [CNF3Clause p]
     -- Eliminate clauses with more than three disjunctions by using De Morgan.
  | otherwise  = not $ (cnfTo3CNF =<< not [pl]) ∧ (cnfTo3CNF =<< not [pr])
 where l = length p
       (pl,pr) = splitAt (l`div`2) p



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
