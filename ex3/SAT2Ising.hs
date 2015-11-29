{-# LANGUAGE FlexibleInstances, TypeFamilies, ParallelListComp, TupleSections #-}

import Prelude hiding (not)
import Control.Arrow
import Control.Monad
import Data.Monoid

-- Example run:
-- @
-- GHCi> asSAT . getCNF3 $ satTo3sat =<< ((x₁ ∨ x₂ ∨ not x₃ ∨ x₅ ∨ x₇) ∧ (x₂ ∨ x₄ ∨ x₆ ∨ not x₇))
-- (Lit 1 :∨ (Lit 2 :∨ Lit 8)) :∧ ((Lit 9 :∨ (Lit 5 :∨ Lit 7)) :∧ ((Lit 2 :∨ (Lit 4 :∨ Lit 8)) :∧ (Lit 8 :∨ (Lit 6 :∨ Not (Lit 7)))))
-- @

satTo3sat :: (Enum a, Ord a) => CNFClause a -> CNF3 a
satTo3sat xs
  | n<=3       =  [CNF3Clause xs]
  
  | otherwise  =  [CNF3Clause [x₁, x₂, a₁]]
                 ∧ [CNF3Clause [not a, x, a']
                   | x <- xMid
                   | a <- newvarsMid
                   | a' <- tail newvarsMid ]
                 ∧ [CNF3Clause [newvars!!(n-4), xs!!(n-2), xs!!(n-1)]]
 where n = length xs
       (x₁:x₂:xMid) = take (n-2) xs
       newvars = (mempty,) <$> newVariables [xs]
       (a₁:newvarsMid) = take (n-3) newvars






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

instance Booly (Any, v) where
  (Any p₁,l₁) ∧ (Any p₂,_) = (Any $ p₁&&p₂, l₁)
  (Any p₁,l₁) ∨ (Any p₂,_) = (Any $ p₁||p₂, l₁)
  not (Any True, l) = (Any False, l)
  not (Any False, l) = (Any True, l)

instance Booly (CNF a) where
  -- conjunction is just concatenation of clause-lists:
  p₁ ∧ p₂ = p₁ ++ p₂
  
  -- use distributive law to implement disjunction:
  p₁ ∨ p₂ = [c₁ ++ c₂ | c₁<-p₁, c₂<-p₂]
  
  -- use De Morgan's law to implement negation of the conjunction of clauses
  -- as disjunction of the individual negations.
  not (p₁:ps) = [[first (Any True<>) x] | x <- p₁] ∨ not ps
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
  type VarIndex (CNF3 a) = a
  lit x = [CNF3Clause [(Any False, x)]]
  newVariables = newVariables . getCNF3

instance (Enum a, Ord a) => Booly (CNF3 a) where
  p₁ ∧ p₂ = p₁ ++ p₂
  
  p₁ ∨ p₂ = satTo3sat =<< getCNF3 p₁ ∨ getCNF3 p₂
  
  not = satTo3sat <=< not . getCNF3
  




type NAE3CNF a = CNF3 a  -- interpreted differently: `:|` means






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
