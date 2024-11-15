{-# LANGUAGE TemplateHaskell #-}

{- |

Here we define knowledge structures for the Muddy Children, a story known in many versions.
These structures are also used for benchmarking.

References:

- J.E. Littlewood (1953):
  /A Mathematician's Miscellany/.
  <https://archive.org/details/mathematiciansmi033496mbp>

- Ronald Fagin, Joseph Y. Halpern, Yoram Moses and Moshe Y. Vardi (1995):
  /Reasoning about Knowledge/.
  <https://doi.org/10.7551/mitpress/5803.001.0001>
  (pages 24-30)

- Hans van Ditmarsch, Wiebe van der Hoek and Barteld Kooi (2007):
  /Dynamic epistemic logic/.
  <https://doi.org/10.1007/978-1-4020-5839-4>
  (pages 93-96)

-}

module SMCDEL.Examples.MuddyChildren where

import Data.List
import Data.Maybe (fromJust)
import Data.Map.Strict (fromList)

import SMCDEL.Internal.Help (seteq)
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.S5
import qualified SMCDEL.Symbolic.K
import qualified SMCDEL.Explicit.K

-- * The Story

-- | The initial knowledge structure, given the total number of children, and the number of muddy children.
mudScnInit :: Int -> Int -> KnowScene
mudScnInit n m = (KnS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = [ (show i, delete (P i) vocab) | i <- [1..n] ]
  actual = [P 1 .. P m]

-- | The initial structure for 3 muddy children.
-- The function `mudScnInit` is the general case for \(n\) children out of which \(m\) are muddy.
-- Here we focus on the case of three children who are all muddy.
-- As usual, all children can observe whether the others are muddy but do not see their own face.
-- This is represented by the observational variables:
-- Agent \(1\) observes \(p_2\) and \(p_3\), agent \(2\) observes \(p_1\) and \(p_3\) and agent \(3\) observes \(p_1\) and \(p_2\).
myMudScnInit :: KnowScene
myMudScnInit = mudScnInit 3 3
$(addSvg 'myMudScnInit)

-- | A formula to say that the given child knows whether it is muddy.
knows :: Int -> Form
knows i = Kw (show i) (PrpF $ P i)

-- | A formula to say that none out of \(n\) children knows its own state.
nobodyknows :: Int -> Form
nobodyknows n = Conj [ Neg $ knows i | i <- [1..n] ]

-- | Announcement of the father announce that someone is muddy.
father :: Int -> Form
father n = Disj (map PrpF [P 1 .. P n])

-- | Result after announcing `father 3` in `myMudScnInit`.
-- We can check that still nobody knows their own state of muddiness.
-- >>> evalViaBdd SMCDEL.Examples.MuddyChildren.mudScn0 (SMCDEL.Examples.MuddyChildren.nobodyknows 3)
-- True
mudScn0 :: KnowScene
mudScn0 = update myMudScnInit (father 3)
$(addSvg 'mudScn0)

-- | The result of updating `mudScn0` with `nobodyKnows 3`.
-- Here still nobody knows their own state.
--
-- >>> evalViaBdd SMCDEL.Examples.MuddyChildren.mudScn1 (SMCDEL.Examples.MuddyChildren.nobodyknows 3)
-- True
mudScn1 :: KnowScene
mudScn1 = update mudScn0 (nobodyknows 3)
$(addSvg 'mudScn1)

-- | Result after one more round announcing `nobodyknows 3`.
-- Now everyone knows that they are muddy.
-- We get a knowledge structure with only one state, marking the end of the story.
--
-- >>> evalViaBdd SMCDEL.Examples.MuddyChildren.mudScn2 (Conj [SMCDEL.Examples.MuddyChildren.knows i | i <- [1..3]])
-- True
-- >>> SMCDEL.Symbolic.S5.statesOf SMCDEL.Examples.MuddyChildren.mudKns2
-- [[P 1,P 2,P 3]]
--
-- We also make use of this example in the SMCDEL benchmarks.
mudScn2 :: KnowScene
mudKns2 :: KnowStruct
mudScn2@(mudKns2,_) = update mudScn1 (nobodyknows 3)
$(addSvg 'mudScn2)

-- * Building Muddy Children using Knowledge Transformers

{- $
We can also start modeling the muddy children story before they get muddy.
The following initial knowledge structure has no atomic propositions.
We then apply an `Event` in which each child can get muddy or not.
Interestingly, this way of modeling the story does not need factual change.
We do not change any facts, but rather introduce new ones.
-}

empty :: Int -> KnowScene
empty n = (KnS [] (boolBddOf Top) obs,[]) where
  obs    = [ (show i, []) | i <- [1..n] ]

buildMC :: Int -> Int -> Event
buildMC n m = (noChange KnTrf vocab Top obs, map P [1..m]) where
  obs = [ (show i, delete (P i) vocab) | i <- [1..n] ]
  vocab = map P [1..n]

-- | The result of ~empty 3 `update` buildMC 3 3~ which is exactly the same as `mudScnInit 3 3` defined above.
-- >>> buildResult == mudScnInit 3 3
-- True
buildResult :: KnowScene
buildResult = empty 3 `update` buildMC 3 3

-- * Muddy Children on general Kripke models

mudGenKrpInit :: Int -> Int -> SMCDEL.Explicit.K.PointedModel
mudGenKrpInit n m = (SMCDEL.Explicit.K.KrM $ fromList wlist, cur) where
  wlist = [ (w, (fromList (vals !! w), fromList $ relFor w)) | w <- ws ]
  ws    = [0..(2^n-1)]
  vals  = map sort (foldl buildTable [[]] [P k | k<- [1..n]])
  buildTable partrows p = [ (p,v):pr | v <-[True,False], pr <- partrows ]
  relFor w = [ (show i, seesFrom i w) | i <- [1..n] ]
  seesFrom i w = filter (\v -> samefor i (vals !! w) (vals !! v)) ws
  samefor i ps qs = seteq (delete (P i) (map fst $ filter snd ps)) (delete (P i) (map fst $ filter snd qs))
  cur = fromJust (elemIndex curVal vals)
  curVal = sort $ [(p,True) | p <- [P 1 .. P m]] ++ [(p,True) | p <- [P (m+1) .. P n]]

myMudGenKrpInit :: SMCDEL.Explicit.K.PointedModel
myMudGenKrpInit = mudGenKrpInit 3 3

-- * Muddy Children on Belief Structures

mudBelScnInit :: Int -> Int -> SMCDEL.Symbolic.K.BelScene
mudBelScnInit n m = (SMCDEL.Symbolic.K.BlS vocab law obs, actual) where
  vocab  = [P 1 .. P n]
  law    = boolBddOf Top
  obs    = fromList [(show i, SMCDEL.Symbolic.K.allsamebdd $ delete (P i) vocab) | i <- [1..n]]
  actual = [P 1 .. P m]

myMudBelScnInit :: SMCDEL.Symbolic.K.BelScene
myMudBelScnInit = mudBelScnInit 3 3
$(addSvg 'myMudBelScnInit)
