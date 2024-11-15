{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

{- |
We solve the famous riddle from the Singapore math olympiad.
For the statement and standard solution of the puzzle, see:

- Hans van Ditmarsch, Michael Ian Hartley, Barteld Kooi, Jonathan Welton and Joseph B.W. Yeo (2017):
  /Cheryl's Birthday/
  <https://doi.org/10.4204/EPTCS.251.1>

For a solution of the puzzle using the explicit model checker DEMO-S5,
see also "SMCDEL.Examples.CherylDemo" and the discussion here:
<https://malv.in/posts/2015-04-20-finding-cheryls-birthday-with-DEMO.html>
-}

module SMCDEL.Examples.Cheryl where

import Data.HasCacBDD (Bdd,con,disSet)
import Data.List

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Internal.Help (powerset)
import SMCDEL.Internal.TexDisplay

-- * Initial Structure

-- | A possible solution to the puzzle.
type Possibility = (Int, String)

possibilities :: [Possibility]
possibilities =
  [ (15,"May"), (16,"May"), (19,"May")
  , (17,"June"), (18,"June")
  , (14,"July"), (16,"July")
  , (14,"August"), (15,"August"), (17,"August") ]

dayIs :: Int -> Prp
dayIs = P

-- | Propositions to encode which month it is.
--
-- >>> map monthIs ["May", "June", "July", "August"]
-- [P 5,P 6,P 7,P 8]
monthIs :: String -> Prp
monthIs "May"    = P 5
monthIs "June"   = P 6
monthIs "July"   = P 7
monthIs "August" = P 8
monthIs _        = undefined

thisPos :: Possibility -> Form
thisPos (d,m) = Conj $
  (PrpF (dayIs d) : [ Neg (PrpF $ dayIs d') | d' <- nub (map fst possibilities) \\ [d] ]) ++
  (PrpF (monthIs m) : [ Neg (PrpF $ monthIs m') | m' <- nub (map snd possibilities) \\ [m] ])

-- | Formula saying that \(i\) knows Cheryl's birthday, defined as the disjunction
-- over all statements of the form "Agent \(i\) knows that the birthday is \(s\)":
knWhich :: Agent -> Form
knWhich i = Disj [ K i (thisPos pos) | pos <- possibilities ]

-- | The initial structure for Cheryl's birthday puzzle.
start :: KnowStruct
start = KnS allprops statelaw obs where
  allprops = sort $ nub $ map (dayIs . fst) possibilities ++ map (monthIs . snd) possibilities
  statelaw = boolBddOf $ Conj
    [ Disj (map thisPos possibilities)
    , Conj [ Neg $ Conj [thisPos p1, thisPos p2] | p1 <- possibilities, p2 <- possibilities, p1 /= p2 ] ]
  obs = [ ("Albert" , nub $ map (monthIs . snd) possibilities)
        , ("Bernard", nub $ map (dayIs   . fst) possibilities) ]
$(addSvg 'start)

-- * Updates

{- $
We now make three updates, with formulas as public public announcements.
-}

round1,round2,round3 :: KnowStruct

-- | Albert: I don't know when Cheryl's birthday is and I know that Bernard does not know.
round1 = update start (Conj [Neg $ knWhich "Albert", K "Albert" $ Neg (knWhich "Bernard")])

-- | Bernard: ``Now I know when Cheryl's birthday is.''
round2 = update round1 (knWhich "Bernard")

-- | Albert says: ``Now I also know when Cheryl's birthday is.''
round3 = update round2 (knWhich "Albert")

-- * Solution

-- | Return the birthday remaining after all three announcements.
--
-- ==== __Spoiler Alert__
--
-- >>> cherylsBirthday
-- "July 16th"
--
cherylsBirthday :: String
cherylsBirthday = m ++ " " ++ show d ++ "th" where
  [(d,m)] = filter (\(d',m') -> [monthIs m', dayIs d'] `elem` statesOf round3) possibilities

-- * Cheryl's Age

{- $
We now formalize and implement the sequel of the Cheryl's Birthday puzzle.
This new puzzle concerns the age of Cheryl and two brothers.
To work with such numeric variable we first define some general functions.
For more information about this binary encoding, see Section 5.1 of [MG2018].
-}

newtype Variable = Var [Prp] deriving (Eq,Ord,Show)

bitsOf :: Int -> [Int]
bitsOf 0 = []
bitsOf n = k : bitsOf (n - 2^k) where
  k :: Int
  k = floor (logBase 2 (fromIntegral n) :: Double)

-- | Alternative to:  `booloutofForm (powerset props !! n) props`.
is :: Variable -> Int -> Form
is (Var props) n = Conj [ (if i `elem` bitsOf n then id else Neg) (PrpF k)
                        | (k,i) <- zip props [(0::Int)..] ]

-- | BDD of `is`.
isBdd :: Variable -> Int -> Bdd
isBdd v = boolBddOf . is v

-- | Inverse of `is`,
valueIn :: Variable -> State -> Int
valueIn (Var props) s = sum [ 2^i | (k,i) <- zip props [(0::Int)..], k `elem` s ]

explainState :: [Variable] -> State -> [Int]
explainState vs s = map (`valueIn` s) vs

-- | An agent knows the value iff they know-whether all bits.
kv :: Agent -> Variable -> Form
kv i (Var props) = Conj [ Kw i (PrpF k) | k <- props ]

-- TODO: generalize and split productIs into two functions??
-- newtype BddVariable = FVar [Bdd] deriving (Eq,Ord,Show)
-- newtype FormVariable = FVar [Form] deriving (Eq,Ord,Show)
-- product :: Variable -> Variable -> FormVariable --- ???


-- | We can now start our analysis of the puzzle by defining all possible triples.
-- Cheryl: I have two younger brothers. The product of all our ages is 144.
allStates :: [(Int,Int,Int)]
allStates = [ (c,b1,b2) | c  <- [1..144]
                        , b1 <- [1..(c-1)]
                        , b2 <- [1..(c-1)]
                        , c * b1 * b2 == 144 ]

-- | Two variables with eight bits each to encode the age of cheryl and one brother.
-- To use fewer variables we leave the age of the other brother implicit.
cheryl, broOne :: Variable
cheryl = Var [P (2*k   ) | k <- [0..7] ]
broOne = Var [P (2*k +1) | k <- [0..7] ]

-- | The initial structure for the age puzzle.
ageKnsStart :: KnowStruct
ageKnsStart = KnS allprops statelaw obs where
  allprops = let (Var cs, Var bs) = (cheryl, broOne) in sort $ cs ++ bs
  statelaw = disSet [ con (cheryl `isBdd` c) (broOne `isBdd` b) | (c,b,_) <- allStates ]
  obs = [("albernard",[])]
$(addSvg 'ageKnsStart)

{- $ We now update the structure in five steps, following the dialogue given in the puzzle. -}

step1,step2,step3,step4,step5 :: KnowStruct

-- | Albert: We still don't know your age. What other hints can you give us?
step1 = ageKnsStart `update` Neg (kv "albernard" cheryl)

-- | Cheryl: The sum of all our ages is the bus number of this bus that we are on.
step2 = step1 `update` revealTransformer

-- | For `step2` we need a way to reveal the sum, hence we use this knowledge transformer.
revealTransformer :: KnowTransformer
revealTransformer = noChange KnTrf addProps addLaw addObs where
  addProps = map P [1001..1008] -- 8 bits to label all sums
  addLaw = simplify $ Conj [ Disj [ label (c + b + a) | (c,b,a) <- allStates ]
                           , Conj [ sumIs s `Equi` label s | s <- [1..144] ] ] where
    label s = booloutofForm (powerset (map P [1001..1008]) !! s) (map P [1001..1008])
    sumIs n = Disj [ Conj [ cheryl `is` c, broOne `is` b ]
                   | (c,b,a) <- allStates, c + b + a == n ]
  addObs = [("albernard",addProps)]

-- | Bernard: Of course we know the bus number, but we still don't know your age.
step3 = step2 `update` Neg (kv "albernard" cheryl)

-- | Cheryl: Oh, I forgot to tell you that my brothers have the same age.
step4 = step3 `update` sameAge where
  sameAge = Disj [ Conj [cheryl `is` c, broOne `is` b ]
                 | (c,b,a) <- allStates
                 , b == a ]

-- | Albert and Bernard: Oh, now we know your age.
step5 = step4 `update` kv "albernard" cheryl

{- $
The solution can then be found by translating true propositions in the remaining state back to integers:

==== __Spoiler Alert__

>>> map (explainState [cheryl,broOne]) (statesOf step5)
[[9,4]]

-}
