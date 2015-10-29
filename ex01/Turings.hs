data Q = FindStart | FindEnd | Carry | UnLead0 | Finish deriving (Eq)

data Σbin = BBlank | B0|B1                         deriving (Eq, Enum, Bounded, Show)
data Σdec = DBlank | D0|D1|D2|D3|D4|D5|D6|D7|D8|D9 deriving (Eq, Enum, Bounded, Show)

tPlus1 :: Turing Q Σbin
tPlus1 FindEnd BBlank =( BBlank, MvLeft,  Carry   )
tPlus1 FindEnd t      =( t,      MvRight, FindEnd )
tPlus1 Carry   B1     =( B0,     MvLeft,  Carry   )
tPlus1 Carry   _      =( B1,     Stay,    Finish  )
tPlus1 Finish  t      =( t,      Stay,    Finish  )

tMinus1 :: Turing Q Σdec
tMinus1 FindEnd   DBlank =( DBlank, MvLeft,  Carry     )
tMinus1 FindEnd   t      =( t,      MvRight, FindEnd   )
tMinus1 Carry     D0     =( D9,     MvLeft,  Carry     )
tMinus1 Carry     t      =( pred t, MvLeft,  FindStart )
tMinus1 FindStart DBlank =( DBlank, MvRight, UnLead0   )
tMinus1 FindStart t      =( t,      MvLeft,  FindStart )
tMinus1 UnLead0   D0     =( DBlank, MvRight, UnLead0   )
tMinus1 UnLead0   t      =( t,      Stay,    Finish    )
tMinus1 Finish    t      =( t,      Stay,    Finish    )

-- Conversion between baseis, using the increment/decrement machines.
-- This together is NOT a Turing machine, though it resembles a two-tape
-- TM. Also, the algorithm is of course extremely inefficient (O(eⁿ)).
baseConvert :: Tape Σdec -> Tape Σbin
baseConvert t
 | null . filter (/=D0) $ retrieveTapeWhile (/=DBlank) t -- zero
              = mkTape BBlank [B0]
 | otherwise  = execTuring (==Finish) tPlus1 FindEnd     -- increment binary
              . baseConvert
              $ execTuring (==Finish) tMinus1 FindEnd t  -- decrement decimal


-- AUXILIARY DEFINITIONS:
encode :: (Enum σ, Bounded σ) => Int -> Tape σ
encode = mkTape (toEnum 0) . reverse . enc
 where enc 0 = []
       enc n = let (n',b) = n`divMod`fromEnum σm
                   σm = maxBound
               in toEnum (b+1)`asTypeOf`σm : enc n'

type Turing s t = s -> t -> (t, TapeMvmt, s)

data TapeMvmt = MvLeft
              | Stay
              | MvRight

execTuring :: (s -> Bool) -> Turing s t -> s -> Tape t -> Tape t
execTuring termination machine = go
 where go s tp | termination s = tp
       go s (g:%l, h:%r) = case machine s h of
        (h', MvLeft,  s') -> go s' (l, g:%h':%r)
        (h', Stay,    s') -> go s' (l%:g, h':%r)
        (h', MvRight, s') -> go s' (l%:g%:h', r)

type Tape a = (InfiniteList a, InfiniteList a)
data InfiniteList a = a :% InfiniteList a
infixr 6 :%
infixl 6 %:
a%:b=b:%a

mkTape :: a -> [a] -> Tape a
mkTape defv l = (iRepeat defv, rend l)
 where rend [] = iRepeat defv
       rend (x:xs) = x:%rend xs

retrieveTapeWhile :: (a->Bool) -> Tape a -> [a]
retrieveTapeWhile pred (l,r) = reverse (go l) ++ go r
 where go (x:%xs) | pred x     = x : go xs
                  | otherwise  = []


iRepeat :: a -> InfiniteList a
iRepeat x = x :% iRepeat x
