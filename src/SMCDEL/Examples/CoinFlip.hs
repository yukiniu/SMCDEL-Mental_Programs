{-# LANGUAGE TemplateHaskell #-}

-- | Example: Coin Flip

module SMCDEL.Examples.CoinFlip where

import Data.Map.Strict (fromList)
import Data.List ((\\))

import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.S5 (boolBddOf)
import SMCDEL.Symbolic.K

-- | Consider a coin lying on a table with heads up: \(p\) is true and this is common knowledge.
coinStart :: BelScene
coinStart = (BlS [P 0] law obs, actual) where
  law    = boolBddOf (PrpF $ P 0)
  obs    = fromList [ ("a", allsamebdd [P 0]), ("b", allsamebdd [P 0]) ]
  actual = [P 0]
$(addSvg 'coinStart)

-- | Toss the coin randomly and only show the result to the given agent.
flipRandomAndShowTo :: [Agent] -> Prp -> Agent -> Event
flipRandomAndShowTo everyone p i = (Trf [q] eventlaw changelaw obs, [q]) where
  q = freshp [p]
  eventlaw = Top
  changelaw = fromList [ (p, boolBddOf $ PrpF q) ]
  obs = fromList $
    (i, allsamebdd  [q]) :
    [ (j,totalRelBdd) | j <- everyone \\ [i] ]
$(addSvg 'coinStart)

-- | Make a coin flip and show result only to agent @"b"@.
coinFlip :: Event
coinFlip = flipRandomAndShowTo ["a","b"] (P 0) "b"
$(addSvg 'coinFlip)

-- | Result of updating `coinStart` with `coinFlip`.
coinResult :: BelScene
coinResult = coinStart `update` coinFlip
$(addSvg 'coinResult)

{- $
The resulting structure has two states:

>>> statesOf (fst coinResult)
[[P 0,P 1,P 2],[P 2]]
-}
