{-# LANGUAGE TemplateHaskell #-}

{- |
We model the "Drinking Logicians" example from <https://spikedmath.com/445.html>.

![comic 445 from spikedmath.com](docs/spikedmath-com-445-three-logicians-walk-into-a-bar.png)

> Three logicians - all very thirsty - walk into a bar and get asked
> "Does everyone want a beer?". The first two reply "I don't know".
> After this the third person says "Yes".

This story is /dual/ to the muddy children ("SMCDEL.Examples.MuddyChildren")
In the initial state here the agents only know their own piece of information and nothing about the others.
The reasoning here is that an announcement of ``I don't know whether everyone wants a beer.'' implies that the person making the announcement wants beer.
Because if not, then they would know that not everyone wants beer.
-}

module SMCDEL.Examples.DrinkLogic where

import SMCDEL.Language
import SMCDEL.Symbolic.S5
import SMCDEL.Internal.TexDisplay

-- | A knowledge structure to represent \(n\) logicians.
-- Let \(p_i\) represent that logician \(i\) wants a beer.
thirstyScene :: Int -> KnowScene
thirstyScene n = (KnS [P 1..P n] (boolBddOf Top) [ (show i,[P i]) | i <- [1..n] ], [P 1..P n])

thirstySceneThree :: KnowScene
thirstySceneThree = thirstyScene 3
$(addSvg 'thirstySceneThree)

{- |
A formula to say that nobody knows whether everyone wants beer, but after all but one agent have announced that they do not know, the agent \(n\) knows that everyone wants beer.

\(
  \bigwedge_i \lnot \left( K^?_i \bigwedge_k P_k \right)
  \ \ \land \ \
  [! \lnot K^?_1 \bigwedge_k P_k] \ldots [! \lnot K^?_{n-1} \bigwedge_k P_k]
    \left( K_n \bigwedge_k P_k \right)
\)
-}
thirstyF :: Int -> Form
thirstyF n = Conj [ Conj [ doesNotKnow k | k <- [1..n] ]
                  , pubAnnounceStack [ doesNotKnow i | i<-[1..(n-1)] ] $ K (show n) allWantBeer ]
  where
    allWantBeer   = Conj [ PrpF $ P k | k <- [1..n] ]
    doesNotKnow i = Neg $ Kw (show i) allWantBeer

-- | Check the above for a given number of agents.
thirstyCheck :: Int -> Bool
thirstyCheck n = evalViaBdd (thirstyScene n) (thirstyF n)

{-$

>>> thirstyCheck 3
True

>>> thirstyCheck 10
True

>>> thirstyCheck 100
True

>>> thirstyCheck 200
True

>>> thirstyCheck 400
True

-}
