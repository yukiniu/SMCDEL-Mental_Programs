{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

{- | What Sum

We quote the following "What Sum" puzzle from the following
article where it was implemented using `DEMO`:

- [vdR2007]
  Hans van Ditmarsch and Ji Ruan (2007):
  /Model Checking Logic Puzzles/.
  Annales du Lamsade, volume 8.
  <https://hal.archives-ouvertes.fr/hal-00188953>

> Each of agents Anne, Bill, and Cath has a positive integer on its forehead.
> They can only see the foreheads of others.
> One of the numbers is the sum of the other two.
> All the previous is common knowledge.
> The agents now successively make the truthful announcements:
>
> Anne: "I do not know my number."
> Bill: "I do not know my number.
> Cath: "I do not know my number.
> Anne: "I know my number. It is 50."
>
> What are the other numbers?

-}

module SMCDEL.Examples.WhatSum where

import SMCDEL.Examples.SumAndProduct (nmbr)
import SMCDEL.Language
import SMCDEL.Internal.Help
import SMCDEL.Symbolic.S5

-- | As we cannot make our model infinite, we use a fixed bound for all numbers.
-- Note that this gives extra knowledge to the agents and thereby limits the set of solutions.
wsBound :: Int
wsBound = 10

wsTriples :: [ (Int,Int,Int) ]
wsTriples = filter
  ( \(x,y,z) -> x+y==z || x+z==y || y+z==x )
  [ (x,y,z) | x <- [1..wsBound], y <- [1..wsBound], z <- [1..wsBound] ]

aProps,bProps,cProps :: [Prp]
(aProps,bProps,cProps) = ([(P 1)..(P k)],[(P $ k+1)..(P l)],[(P $ l+1)..(P m)]) where
  [k,l,m] = map (wsAmount*) [1,2,3]
  wsAmount = ceiling (logBase 2 (fromIntegral wsBound) :: Double)

aIs, bIs, cIs :: Int -> Form
aIs n = booloutofForm (powerset aProps !! n) aProps
bIs n = booloutofForm (powerset bProps !! n) bProps
cIs n = booloutofForm (powerset cProps !! n) cProps

wsKnStruct :: KnowStruct
wsKnStruct = KnS wsAllProps law obs where
  wsAllProps = aProps++bProps++cProps
  law = boolBddOf $ Disj [ Conj [ aIs x, bIs y, cIs z ] | (x,y,z) <- wsTriples ]
  obs = [ (alice, bProps++cProps), (bob, aProps++cProps), (carol, aProps++bProps) ]

wsKnowSelfA,wsKnowSelfB,wsKnowSelfC :: Form
wsKnowSelfA = Disj [ K alice $ aIs x | x <- [1..wsBound] ]
wsKnowSelfB = Disj [ K bob   $ bIs x | x <- [1..wsBound] ]
wsKnowSelfC = Disj [ K carol $ cIs x | x <- [1..wsBound] ]

-- | Result after the dialogue from the puzzle.
wsResult :: KnowStruct
wsResult = foldl update wsKnStruct [ Neg wsKnowSelfA, Neg wsKnowSelfB, Neg wsKnowSelfC ]

wsSolutions :: [State]
wsSolutions = statesOf wsResult

-- | A function to explain a state by computing the three numbers.
-- Uses the `nmbr` function from "SMCDEL.Examples.SumAndProduct".
wsExplainState :: [Prp] -> [(Char,Int)]
wsExplainState truths =
  [ ('a', explain aProps), ('b', explain bProps), ('c', explain cProps) ] where
    explain = nmbr truths

{- $

We can now use `fmap length (mapM (putStrLn.wsExplainState) wsSolutions)`
to list and count solutions:

>>> fmap length (mapM (print.wsExplainState) wsSolutions)
[('a',1),('b',3),('c',2)]
[('a',1),('b',3),('c',4)]
2

Comparer to the DEMO results from [vdR2007] we get the following
runtime results depending on different values of `wsBound`.

+-----------+--------------+----------------+-----------+
| `wsBound` | Runtime DEMO | Runtime SMCDEL | Solutions |
+===========+==============+================+===========+
| 10        | 1.59         | 0.22           | 2         |
| 20        | 30.31        | 0.27           | 36        |
| 30        | 193.20       | 0.23           | 100       |
| 40        | n/a          | 0.41           | 198       |
| 50        | n/a          | 0.83           | 330       |
+-----------+--------------+----------------+-----------+

-}

-- * Alternative version (not implemented (yet?))

{- $

The above was a simplification of the original puzzle.
The following version also suggested on page 144 of [vdR2007] does not
provide any bound, but does restrict to prime numbers.


> Each of agents Anne, Bill, and Cath has a positive integer on its forehead.
> They can only see the foreheads of others.
> One of the numbers is the sum of the other two.
> All the  previous  is common  knowledge.
> The agents now successively make the truthful announcements:
>
> Anne: "I do not know my number."
>
> Bill: "I do not know my number."
>
> Cath: "I do not know my number."
>
> What are the numbers, if Anne now knows her number and if all numbers are prime?

This seems hard to implement, because we would need to make the model infinite.
Even a high bound would still give extra knowledge to the agents.

-}

-- TODO implement advanced version of whatsum - needs infinite model?
