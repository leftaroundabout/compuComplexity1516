
infixr 2 :||, :|
infixr 3 :&&

data SAT a = Lit a
           | Not (SAT a)
           | SAT a :|| SAT a
           | SAT a :&& SAT a
    deriving (Show)

data CNFClause a = LitC Bool{-negated?-} a
                 | CNFClause a :| CNFClause a
    deriving (Show)

type CNF a = [CNFClause a]

asSAT :: CNF a -> SAT a
asSAT = foldr1 (:&&) . map asSAT'
 where asSAT' (LitC False a) = Lit a
       asSAT' (LitC True a) = Not (Lit a)
       asSAT' (a:|b) = asSAT' a :|| asSAT' b

-- Not-operator, avoiding double negation.
not' :: SAT a -> SAT a
not' (Not a) = a
not' a = (Not a)

cnfClauses :: SAT a -> CNF a
cnfClauses (Lit a) = [LitC False a]
-- Move all `Not` completely down the syntax tree.
cnfClauses (Not (Lit a)) = [LitC True a]
cnfClauses (Not (Not a)) = cnfClauses a
cnfClauses (Not (a :|| b)) = cnfClauses (not' a) ++ cnfClauses (not' b)
cnfClauses (Not (a :&& b)) = cnfClauses (not' a :|| not' b)
-- Move all `:&&` up the syntax tree.
cnfClauses (a :|| (b:&&c)) = cnfClauses (a:||b) ++ cnfClauses (a:||c)
cnfClauses ((a:&&b) :|| c) = cnfClauses (a:||c) ++ cnfClauses (b:||c)
cnfClauses (a:&&b) = cnfClauses a ++ cnfClauses b
cnfClauses (a:||b) = [a':|b' | a'<-cnfClauses a, b'<-cnfClauses b]
                     

assocR :: CNFClause a -> CNFClause a
-- Make the OR right-associative, so we can deconstruct it
-- left-to-right.
assocR ((a:|b):|c) = assocR a :| assocR b :| assocR c
assocR a = a

oCNFTo3CNF, oCNFTo3CNF' :: CNFClause a -> CNF a
oCNFTo3CNF = oCNFTo3CNF' . assocR
-- Eliminate clauses with more than three disjunctions.
oCNFTo3CNF' (LitC n x) = [LitC n x]
oCNFTo3CNF' (LitC n x :| LitC n' x') = [LitC n x :| LitC n' x']
oCNFTo3CNF' (LitC n x :| LitC n' x' :| LitC n'' x'')
         = [LitC n x :| LitC n' x' :| LitC n'' x'']
oCNFTo3CNF' (a:|b) = oCNFTo3CNF' . (a:|) =<< oCNFTo3CNF' b

