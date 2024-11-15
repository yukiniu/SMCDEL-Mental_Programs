{- |

We model Example 6 from:

- [EBMN2017]
  Thorsten Engesser, Thomas Bolander, Robert Mattmüuller and Bernhard Nebel (2017):
  /Cooperative Epistemic Multi-Agent Planning for Implicit Coordination/.
  <https://doi.org/10.4204/EPTCS.243.6>

-}

module SMCDEL.Examples.LetterPassing where

import Data.List (sort)

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Translations.S5 (booloutof)
import SMCDEL.Other.Planning

-- * Formula helper functions

explain :: Prp -> String
explain (P k) | odd k     = "at " ++ show ((k + 1) `div` 2)
              | otherwise = "for " ++ show (k `div` 2)

atP, forP :: Int -> Prp
atP  k = P $ k*2 - 1
forP k = P $ k*2

at, for :: Int -> Form
at  = PrpF . atP
for = PrpF . forP

-- * Version for 3 agents

letterStart :: MultipointedKnowScene
letterStart = (KnS voc law obs, cur) where
  voc = sort $ map atP [1..3] ++ map forP [1..3]
  law = boolBddOf $ Conj $
    -- letter must be at someone, but not two:
       [ Disj (map at [1..3]) ]
    ++ [ Neg $ Conj [at i, at j] | i <- [1..3], j <- [1..3], i /= j ]
    -- letter must be for someone, but not two:
    ++ [ Disj (map for [1..3]) ]
    ++ [ Neg $ Conj [for i, for j] | i <- [1..3], j <- [1..3], i /= j ]
    -- make it common knowledge that the letter is at 1, but not adressed to 1:
    ++ [ at 1, Neg (for 1) ]
  obs = [ ("1",[atP 1, forP 1, forP 2, forP 3])
        , ("2",[atP 2])
        , ("3",[atP 3]) ]
  cur = booloutof [atP 1, forP 3] voc

letterPass :: Int -> Int -> Int -> Labelled MultipointedEvent
letterPass n i j = (label, (KnTrf addprops addlaw changeLaw addObs, boolBddOf Top)) where
  offset      = n*2 -- ensure addprops does not overlap with vocabOf (letterStartFor n)
  label       = show i ++ "->" ++ show j
  addprops    = map P [(offset + 1)..(offset + n)]
  addlaw      = Conj $ at i : [ PrpF (P (offset + k)) `Equi` for k | k <- [1..n] ]
  -- publicly pass the letter from i to j:
  changeLaw   = [ (atP i, boolBddOf Bot), (atP j, boolBddOf Top) ]
  -- privately tell j who the receiver is:
  addObs      = [ (show k, if k == j then addprops else []) | k <- [1..n] ]

-- | For all agents @i@, if @for i@ then @at i@.
letterGoal :: Form
letterGoal = Conj [ for i `Impl` at i | i <- [1,2,3] ]

letter :: CoopTask MultipointedKnowScene MultipointedEvent
letter = CoopTask letterStart actions letterGoal where
  actions = [ (show i, letterPass 3 i j) | (i,j) <- [(1,2),(2,1),(2,3),(3,2)] ]

{- $

With a search depth of 2 we find this plan:

>>> ppICPlan (head (findSequentialIcPlan 2 letter))
"1:1->2; 2:2->3."

Note that this is depth-first search which can lead to unnecessarily long plans:

>>> ppICPlan (head (findSequentialIcPlan 4 letter))
"1:1->2; 2:2->1; 1:1->2; 2:2->3."

We can also use breadth-first search:

>>> fmap ppICPlan (findSequentialIcPlanBFS 2 letter)
Just "1:1->2; 2:2->3."

-}

-- * General version for \(n\) agents

letterStartFor :: Int -> MultipointedKnowScene
letterStartFor n = (KnS voc law obs, cur) where
  voc = sort $ map atP [1..n] ++ map forP [1..n]
  law = boolBddOf $ Conj $
    -- letter must be at someone, but not two:
       [ Disj (map at [1..n]) ]
    ++ [ Neg $ Conj [at i, at j] | i <-[1..n], j <- [1..n], i /= j ]
    -- letter must be for someone, but not two:
    ++ [ Disj (map for [1..n]) ]
    ++ [ Neg $ Conj [for i, for j] | i <-[1..n], j <- [1..n], i /= j ]
    -- make it common knowledge that letter is at 1, but not adressed to 1:
    ++ [ at 1, Neg (for 1) ]
  obs = ("1", atP 1 : map forP [1..n]) : [ (show k, [atP k]) | k <- [2..n] ]
  cur = booloutof [atP 1, forP n] voc

letterLine :: Int -> CoopTask MultipointedKnowScene MultipointedEvent
letterLine n = CoopTask (letterStartFor n) actions goal where
  actions = [ (show i, letterPass n i j) | i <- [1..n], j <- [1..n], abs(i-j) == 1 ]
  goal = Conj [ for i `Impl` at i | i <- [1..n] ]
