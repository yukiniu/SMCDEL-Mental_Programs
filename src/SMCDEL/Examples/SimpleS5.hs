{-# LANGUAGE TemplateHaskell #-}

-- | Simple Actions in S5

module SMCDEL.Examples.SimpleS5 where

import Data.List ((\\))

import SMCDEL.Explicit.S5
import SMCDEL.Internal.TexDisplay
import SMCDEL.Translations.S5
import SMCDEL.Symbolic.S5
import SMCDEL.Language

-- * Publicly make p false

myStart :: KnowScene
myStart = (KnS [P 0] (boolBddOf Top) [("Alice",[]),("Bob",[P 0])],[P 0])
$(addSvg 'myStart)

publicMakeFalse :: [Agent] -> Prp -> Event
publicMakeFalse agents p = (KnTrf [] Top mychangelaw myobs, []) where
  mychangelaw = [ (p,boolBddOf Bot) ]
  myobs = [ (i,[]) | i <- agents ]

myEvent :: Event
myEvent = publicMakeFalse (agentsOf myStart) (P 0)
$(addSvg 'myEvent)

-- | Result of updating `myStart` by `myEvent`.
myResult :: KnowScene
myResult = myStart `update` myEvent
$(addSvg 'myResult)

-- * Make p false keeping it secret from Alice

exampleStart :: KnowScene
exampleStart = (KnS [P 0] (boolBddOf Top) [("Alice",[]),("Bob",[P 0])],[P 0])

makeFalseShowTo :: [Agent] -> Prp -> [Agent] -> Event
makeFalseShowTo agents p intheknow = (KnTrf [P 99] Top examplechangelaw exampleobs, []) where
  examplechangelaw = [ (p,boolBddOf $ PrpF (P 99)) ]
  exampleobs = [ (i,[P 99]) | i <- intheknow           ]
            ++ [ (i,[    ]) | i <- agents \\ intheknow ]

exampleEvent :: Event
exampleEvent = makeFalseShowTo (agentsOf exampleStart) (P 0) ["Bob"]
$(addSvg 'exampleEvent)

-- | Result of updating `exampleStart` with `exampleEvent`.
exampleResult :: KnowScene
exampleResult = exampleStart `update` exampleEvent
$(addSvg 'exampleResult)

-- * Showing the result only to Alice

thirdEvent :: Event
thirdEvent = makeFalseShowTo (agentsOf exampleStart) (P 0) ["Alice"]
$(addSvg 'thirdEvent)

-- | Result of updating `exampleStart` with `thirdEvent`.
thirdResult :: KnowScene
thirdResult = exampleStart `update` thirdEvent
$(addSvg 'thirdResult)

-- * The limits of observational variables

{- $
In "SMCDEL.Symbolic.S5" we encod Kripke frames using observational variables.
This restricts our framework to S5 relations.
In fact not even every S5 relation on distinctly valuated worlds can be modeled with observational variables as the following example shows.
Here the knowledge of Alice is given by an equivalence relation but it can not be described by saying which subset of the vocabulary \(V=\{p_1,p_2\}\) she observes.
We would want to say that she observes \(p \land q\) and our existing approach does this by adding an additional variable:
-}

problemPM :: PointedModelS5
problemPM = ( KrMS5 [0,1,2,3] [ (alice,[[0],[1,2,3]]), (bob,[[0,1,2],[3]]) ]
  [ (0,[(P 1,True ),(P 2,True )]), (1,[(P 1,True ),(P 2,False)])
  , (2,[(P 1,False),(P 2,True )]), (3,[(P 1,False),(P 2,False)]) ], 1::World )
$(addSvg 'problemPM)

problemKNS :: KnowScene
problemKNS = kripkeToKns problemPM
$(addSvg 'problemKNS)

{-
To overcome this limitation we need to switch from knowledge structures to
belief structures, where the observational variables are replaced with BDDs.
These BDDs describe relations between worlds as relations between sets of
true propositions.
-}
