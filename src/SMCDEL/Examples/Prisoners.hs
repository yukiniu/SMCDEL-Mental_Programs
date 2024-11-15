{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

{- |

We model the story of "Hundred Prisoners and a Lightbulb", from [DEW2010]:

"A group of 100 prisoners, all together in the prison dining area, are told
that they will be all put in isolation cells and then will be interrogated one
by one in a room containing a light with an on/off switch.  The prisoners may
communicate with one another by toggling the light-switch (and that is the only
way in which they can communicate). The light is initially switched off. There
is no fixed order of interrogation, or fixed interval between interrogations,
and the same prisoner may be interrogated again at any stage.  When
interrogated, a prisoner can either do nothing, or toggle the light-switch, or
announce that all prisoners have been interrogated. If that announcement is
true, the prisoners will (all) be set free, but if it is false, they will all be
executed. While still in the dining room, and before the prisoners go to their
isolation cells, can the prisoners agree on a protocol that will set them free
(assuming that at any stage every prisoner will be interrogated again
sometime)?"

The solution: Let one agent be a "counter". He turns off the light whenever
he enters the room and counts until this has happend 99 times. Then he knows
that everyone has been in the room, because: Everyone else turns on the light
the first time they find it turned off when they are brought into the room and
does not do anything else afterwards, no matter how often they are brought to
the room.

We first try to implement it with three agents and let the first one be the counter.

We use four propositions: \(p\) says that the light is on and \(p_1\) to \(p_3\) say
that the agents have been in the room, respectively.

The goal is \(\bigvee_{i} K_i (p_1 \land p_2 \land p_3)\).

Now, calling an agent \(i\) into the room is an event with multiple consequences:

- the agent learns P 0, i.e.~whether the light is on or off
- the agent can set the new value of P 0
- P i for that agent
- the other agents no longer know the value of P 0 and should consider
  it possible that anyone else has been in the room.

Reference:

- [DEW2010]
  Hans van Ditmarsch, Jan van Eijck and William Wu (2010):
  /One Hundred Prisoners and a Lightbulb --- Logic and Computation/.
  KR 2010, pages 90-100.
  <https://www.aaai.org/ocs/index.php/KR/KR2010/paper/view/1234>

-}

module SMCDEL.Examples.Prisoners where

import Data.HasCacBDD hiding (Top,Bot)

import SMCDEL.Explicit.S5
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.S5

-- * Explicit Version

{- $
We first give an explicit, Kripke model implementation, similar to the DEMO
version in~\cite{DitEijckWu2010:PrisonersLoCo}. In particular, we only model
the knowledge of the counter, ignoring what the other agents might know.
We also do not include a "nothing happens" event but instead model the
synchronous version only.

Both of these restrictions help to keep the Kripke model small.
-}

-- | 3
n :: Int
n = 3

-- | We use `P 0` for "The light is on".
light :: Form
light = PrpF (P 0)

-- | The initial structure.
-- Here `P i` means agent i has been in the room (and switched on the light).
-- Agent 1 is the counter, 2 and 3 are the others.
prisonExpStart :: KripkeModelS5
prisonExpStart =
  KrMS5
    [1]
    [ ("1",[[1]]) ]
    [ (1, [(P k,False) | k <- [0..n] ] ) ]

-- | Agent 1 knows that \(p_1\) to \(p_n\) are all true.
prisonGoal :: Form
prisonGoal = K "1" $ Conj [ PrpF $ P k | k <- [1..n] ]

-- | Action model for one round of interviewing.
prisonAction :: ActionModelS5
prisonAction = ActMS5 actions actRels where
  p = PrpF . P
  actions =
    [ (0, (p 0      , [(P 0, Bot), (P 1, Top)]) ) -- interview 1 with light on
    , (1, (Neg (p 0), [            (P 1, Top)]) ) -- interview 1 with light off
    ]
    ++
    [ (k, (Top, [(P 0, p k `Impl` p 0), (P k, p 0 `Impl` p k)]) ) | k <- [2..n] ] -- interview k
  actRels = [ ("1", [[0],[1],[2..n]]) ]

prisonInterview :: Int -> MultipointedActionModelS5
prisonInterview 1 = (prisonAction, [0,1])
prisonInterview k = (prisonAction, [k])

-- * Interlude: Story telling

{- $
We define a general function to execute a sequence of updates
on a given starting point and optimizing the intermediate steps.
We also define a function to \(\LaTeX\) a whole story.
-}

data Story a b = Story a [b]

endOf :: (Update a b, Optimizable a) => Story a b -> a
endOf (Story start actions) =
  foldl (\cur a -> optimize (vocabOf start) $ cur `update` a) start actions

instance (Update a b, Optimizable a, TexAble a, TexAble b) => TexAble (Story a b) where
  tex (Story start actions) = adjust (tex start) ++ loop start actions where
    adjust thing = " \\raisebox{-.5\\height}{ \\begin{adjustbox}{max height=4cm, max width=0.3\\linewidth} " ++ thing ++ " \\end{adjustbox} }\n"
    loop _       []     = ""
    loop current (a:as) =
      let
        new = optimize (vocabOf start) $ current `update` a
      in
        " \\ensuremath{ \\times } " ++ adjust (tex a) ++ " = " ++ adjust (tex new) ++ "\n" ++ loop new as

-- | The story of the prisoners, in which agents 2, 1, 3 and 1 are interviewed in this order.
-- We show only generated submodels here.
-- The full product models are actually much larger --- even more so, if we would also keep track of the knowledge of all other agents beside 1.
prisonExpStory :: Story PointedModelS5 MultipointedActionModelS5
prisonExpStory = Story (prisonExpStart,1) (map prisonInterview [2,1,3,1])
-- TODO: addSvg

{- $
And indeed we have:

>> endOf prisonExpStory |= prisonGoal
True
-}

-- * Symbolic Version

-- | In the initial structure the light is off and nobody has been interviewed.
-- This is the actual and the only state, thus common knowledge.
prisonSymStart :: MultipointedKnowScene
prisonSymStart = (KnS (map P [0..n]) law obs, actualStatesBdd) where
  law    = boolBddOf (Conj (Neg light : [ Neg $ wasInterviewed k | k <- [1..n] ]))
  obs    = [ ("1", []) ]
  actualStatesBdd = top

wasInterviewed, isNowInterviewed :: Int -> Form
wasInterviewed     = PrpF . P
isNowInterviewed k = PrpF (P (k + n))

lightSeenByOne :: Form
lightSeenByOne  = PrpF (P (1 + (2*n)))

prisonSymEvent :: KnowTransformer
prisonSymEvent = KnTrf -- agent 1 is interviewed
  (map P $ [ k+n | k <- [1..n] ] ++ [1+(2*n)] ) -- distinguish events
  (Conj [ isNowInterviewed 1 `Impl` (lightSeenByOne `Equi` light)
        , Disj [ Conj $ isNowInterviewed k : [Neg $ isNowInterviewed l | l <- [1..n], l /= k ] | k <- [1..n]]
        ] )
  -- light might be switched and visits of the agents might be recorded
  ( [ (P 0, boolBddOf $
          Conj $ isNowInterviewed 1 `Impl` Bot -- 1 turns off the light
               : concat [ [ Conj [Neg $ wasInterviewed k, isNowInterviewed k] `Impl` Top
                          , Conj [      wasInterviewed k, isNowInterviewed k] `Impl` light ]
                        | k <- [2..n] ])
  , (P 1, boolBddOf $ Disj [wasInterviewed 1, Conj [           isNowInterviewed 1]])
  ]
  ++
  [ (P k, boolBddOf $ Disj [wasInterviewed k, Conj [Neg light, isNowInterviewed k]])
  | k <- [2..n] ] )
  -- agent 1 observes whether they are interviewed, and if so, also observes the light
  [ ("1", let (PrpF px, PrpF py) = (isNowInterviewed 1, lightSeenByOne) in [px, py]) ]

prisonSymInterview :: Int -> MultipointedEvent
prisonSymInterview k = (prisonSymEvent, boolBddOf (isNowInterviewed k))

-- | The whole story, now symbolically.
-- Thanks to the optimization we can still draw all BDDs in the structures, but they are not very readable.
prisonSymStory :: Story MultipointedKnowScene MultipointedEvent
prisonSymStory = Story prisonSymStart (map prisonSymInterview [2,1,3,1])
-- TODO: addSvg

{- $
Finally, also in the symbolic version of the story we reach the goal:

>>> endOf prisonSymStory `isTrue` prisonGoal
True
-}
