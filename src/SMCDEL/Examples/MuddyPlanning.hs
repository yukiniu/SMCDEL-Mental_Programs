{-|
We reframe "SMCDEL.Examples.MuddyChildren" as a planning problem.
This is a toy example to illustrate the functions in "SMCDEL.Other.Planning".
-}

module SMCDEL.Examples.MuddyPlanning where

import SMCDEL.Examples.MuddyChildren
import SMCDEL.Language
import SMCDEL.Other.Planning

{- $
Suppose we have three children, two of which are muddy.
The available actions are public announcements that at least one child
is muddy or that a specific child does not know their own state.
Finally, suppose our goal is that child 1 knows whether it is muddy,
  while child 2 should not learn whether it is muddy.
The following uses `offlineSearch` to find a solution.
-}

toyPlan :: [OfflinePlan]
toyPlan = offlineSearch maxSteps start acts cons goal where
  maxSteps = 5 -- 2 would be enough
  start = mudScnInit 3 2
  acts = Disj [PrpF (P k) | k <- [1,2,3]] : [Neg $ Kw (show k) $ PrpF (P k) | k <- [1,2,3]]
  cons = [ Neg $ Kw "2" (PrpF $ P 2) ]
  goal = Kw "1" (PrpF $ P 1)

{- $
We actually find two solutions, one with two and one with three announcements:

>>> map (map ppForm) toyPlan
[["(1 | 2 | 3)","~Kw 2 2"],["(1 | 2 | 3)","~Kw 3 3","~Kw 2 2"]]
-}
