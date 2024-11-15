{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

{- |

As another case study we analyze the Russian Cards problem. One of its
first (dynamic epistemic) logical treatments was [vD2003] and
the problem has since gained notable attention as an intuitive example
of information-theoretically (in contrast to computationally) secure
cryptography.

The basic version of the Russian Cards problem is this:

> Seven cards, enumerated from 0 to 6, are distributed between Alice, Bob and
> Carol such that Alice and Bob both receive three cards and Carol one card.
> It is common knowledge which cards exist and how many cards each agent has.
> Everyone knows their own but not the others' cards.
> The goal of Alice and Bob now is to learn each others cards without Carol
> learning their cards.
> They are only allowed to communicate via public announcements.

References:

- [vD2003]
  Hans van Ditmarsch (2003):
  /The Russian Cards problem/.
  Studia Logica, volume 75, number 1, pages 31-62.
  <https://doi.org/10.1023/A:1026168632319>

- [DS2011]
  Hans van Ditmarsch and Fernando Soler-Toscano (2011):
  /Three Steps/.
  {CLIMA 2011, pages 41-57.
  <https://doi.org/10.1007/978-3-642-22359-4_4>

- [DHMR2006]
  Hans van Ditmarsch, Wiebe van der Hoek, Ron van der Meyden and Ji Ruan (2006):
  /Model Checking Russian Cards/.
  Electronic Notes in Theoretical Computer Science, volume 149, number 2, pages 105-123.
  <https://doi.org/10.1016/j.entcs.2005.07.029>

- [EBMN2017]
  Thorsten Engesser, Thomas Bolander, Robert Mattmüller, and Bernhard Nebel (2017):
  /Cooperative Epistemic Multi-Agent Planning for Implicit Coordination/.
  Ninth Workshop on Methods for Modalities.
  <https://doi.org/10.4204/EPTCS.243.6>

See also:

- David Fernández-Duque and Goranko, Valentin (2014):
  /Secure aggregation of distributed information/.
  <https://arxiv.org/abs/1407.7582>

- Andrés Cordón-Franco, Hans van Ditmarsch, David Fernández-Duque, Fernando Soler-Toscano (2015):
  /A geometric protocol for cryptography with cards/.
  <https://doi.org/10.1007/s10623-013-9855-y>

-}

module SMCDEL.Examples.RussianCards where

import Control.Monad (replicateM)
import Data.HasCacBDD hiding (Top,Bot)
import Data.List ((\\),delete,intersect,nub,sort)
import Data.Map.Strict (fromList)

import SMCDEL.Internal.Help (powerset)
import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Other.Planning
import SMCDEL.Symbolic.S5
import qualified SMCDEL.Symbolic.K as K

-- * Formulas and Initial Structure

{- $
We begin implementing this situation by defining the set of players and the set
of cards. To describe a card deal with boolean variables, we let \(P_k\) encode
that agent \(k\ \mathsf{modulo}\ 3\) has card \(\mathsf{floor}(\frac{k}{3})\).
For example, \(P_{17}\) means that agent \(2\), namely Carol, has card \(5\)
because \(17=(3*5)+2\).
The function `hasCard` in infix notation allows us to write more natural statements.
We also use aliases `alice`, `bob` and `carol` for the agents 0, 1 and 2.

We could in principle use only two propositions per card instead of three and encode that Carol has a card by saying that the others don't have it.
Concretely, consider replacing @hasCard carol n@
with @Conj [ Neg (hasCard alice n), Neg (hasCard bob n) ]@.
But this would make it impossible to encode what Carol knows with observational variables.
The more general belief structures from "SMCDEL.Symbolic.K" provide a solution for this, see `rusBelScnfor` below.
-}

-- | The three players.
rcPlayers :: [Agent]
rcPlayers = [alice,bob,carol]

-- | Enumerating the agents: Alice is 0, Bob is 1, Carol is 2.
rcNumOf :: Agent -> Int
rcNumOf "Alice" = 0
rcNumOf "Bob"   = 1
rcNumOf "Carol" = 2
rcNumOf _ = error "Unknown Agent"

-- | The cards, enumerated from 0 to 7.
rcCards :: [Int]
rcCards   = [0..6]

-- | Entire vocabulary for the Russian Cards problem.
rcProps :: [Prp]
rcProps = [ P k | k <- [0..(length rcPlayers * length rcCards - 1)] ]

-- | Formula to say that the given agent has the given card/number.
--
-- >>> carol `hasCard` 5
-- PrpF (P 17)
--
hasCard :: Agent -> Int -> Form
hasCard i n = PrpF (P (3 * n + rcNumOf i))

-- | Formula to say that the given agent has this list of cards.
--
-- >>> ppForm $ bob `hasHand` [1,3,5]
-- "(4 & 10 & 16)"
--
hasHand :: Agent -> [Int] -> Form
hasHand i ns = Conj $ map (i `hasCard`) ns

-- | Helper function to translate propositions back to sentences.
--
-- >>> ppFormWith rcExplain (hasHand bob [1,3,5])
-- "(Bob has card 1 & Bob has card 3 & Bob has card 5)"
--
rcExplain :: Prp -> String
rcExplain (P k) = (rcPlayers !! i) ++ " has card " ++ show n where (n,i) = divMod k 3

{- $
We now describe which deals of cards are allowed.
For a start, all cards have to be given to at least one agent but no card can be given to two agents.
-}

allCardsGiven, allCardsUnique :: Form
allCardsGiven  = Conj [ Disj [ i `hasCard` n | i <- rcPlayers ] | n <- rcCards ]
allCardsUnique = Conj [ Neg $ isDouble n | n <- rcCards ] where
  isDouble n = Disj [ Conj [ x `hasCard` n, y `hasCard` n ] | x <- rcPlayers, y <- rcPlayers, x < y ]

{- $
Moreover, Alice, Bob and Carol should get at least three, three and one card, respectively.
As there are only seven cards in total this already implies that they can not have more.
-}

distribute331 :: Form
distribute331 = Conj [ aliceAtLeastThree, bobAtLeastThree, carolAtLeastOne ] where
  triples = [ [x, y, z] | x <- rcCards, y <- delete x rcCards, z <- rcCards \\ [x,y] ]
  aliceAtLeastThree = Disj [ Conj (map (alice `hasCard`) t) | t <- triples ]
  bobAtLeastThree   = Disj [ Conj (map (bob   `hasCard`) t) | t <- triples ]
  carolAtLeastOne   = Disj [ carol `hasCard` k | k<-[0..6] ]

{- $
We can now define the initial knowledge structure.
The state law describes all possible distributions using the three conditions we just defined.
As a default deal we give the cards \(\{0,1,2\}\) to Alice, \(\{3,4,5\}\) to Bob and \(\{6\}\) to Carol.
-}

-- | The initial knowledge structure for Russian Cards.
-- The BDD describing the state law is generated within less than a second but drawing it is more complicated and the result quite huge.
--
-- ==== __Show me__
--
rusSCN :: KnowScene
rusKNS :: KnowStruct
rusSCN@(rusKNS,_) = (KnS rcProps law [ (i, obs i) | i <- rcPlayers ], defaultDeal) where
  law = boolBddOf $ Conj [ allCardsGiven, allCardsUnique, distribute331 ]
  obs i = [ P (3 * k + rcNumOf i) | k<-[0..6] ]
  defaultDeal = [P 0,P 3,P 6,P 10,P 13,P 16,P 20]
$(addSvg 'rusSCN)

-- * Verifying a five-hand protocol

{- $
Many different solutions for Russian Cards exist. Here we will focus on the
following so-called five-hands protocols (and their extensions with six or
seven hands) which are also used in [DHMR2006].
First Alice makes an announcement of the form "My hand is one of these: ...".
If her hand is 012 she could for example take the set \(\{ 012,034,056,135,146,236 \}\).
It can be checked that this announcement does not tell Carol which cards Alice and Bob have,
independent of which card Carol has.
In contrast, Bob will be able to rule out all but one of the hands in the list because of his own hand.
Hence the second and last step of the protocol is that Bob says which card Carol has.
For example, if Bob's hand is 345 he would finish the protocol with "Carol has card 6".

To verify this protocol with our model checker we first define the two formulas for
  Alice saying "My hand is one of 012, 034, 056, 135 and 246." and
  Bob saying "Carol holds card 6".
Note that Alice and Bob make the announcements and thus the real announcement
is "Alice knows that one of her cards is 012, 034, 056, 135 and 246." and
"Bob knows that Carol holds card 6.", i.e. we prefix the statements with the
knowledge operators of the speaker.
-}

aAnnounce :: Form
aAnnounce = K alice $ Disj [ Conj (map (alice `hasCard`) hand)
                           | hand <- [ [0,1,2], [0,3,4], [0,5,6], [1,3,5], [2,4,6] ] ]

bAnnounce :: Form
bAnnounce = K bob (carol `hasCard` 6)

{- $

To describe the goals of the protocol we need formulas about the knowledge of the three agents:

- Alice should know Bob's cards,
- Bob should know Alice's cards, and
- Carol should be ignorant, i.e.\ not know for any card that Alice or Bob has it.

Note that Carol will still know for one card that neither Alice and Bob have them, namely his own.
This is why we use knowing-whether `Kw` for the first two but plain `K` for the last condition.

-}

aKnowsBs, bKnowsAs, cIgnorant :: Form
aKnowsBs = Conj [ alice `Kw` (bob   `hasCard` k) | k<-rcCards ]
bKnowsAs = Conj [ bob   `Kw` (alice `hasCard` k) | k<-rcCards ]
cIgnorant = Conj $ concat [ [ Neg $ K carol $ alice `hasCard` i
                            , Neg $ K carol $ bob   `hasCard` i ] | i<-rcCards ]

-- | Formulas that check how the knowledge of the agents changes during the communication,
-- i.e.~after the first and the second announcement.
--
-- 0: First we check that Alice says the truth,i .e. `aAnnounce`.
--
-- 1 and 2: After Alice announces five hands, Bob knows Alice's card and this is common knowledge among them.
--
-- 3: And Bob knows Carol's card. This is entailed by the fact that Bob knows Alice's cards.
--
-- 4: Carol remains ignorant of Alice's and Bob's cards, and this is common knowledge.
--
-- 5 and 6: After Bob announces Carol's card, it is common knowledge among Alice and Bob that they know each others cards.
--
-- 7: After both announcements Carol remains ignorant and this is common knowledge.
rcCheck :: Int -> Form
rcCheck 0 = aAnnounce
rcCheck 1 = PubAnnounce aAnnounce bKnowsAs
rcCheck 2 = PubAnnounce aAnnounce (Ck [alice,bob] bKnowsAs)
rcCheck 3 = PubAnnounce aAnnounce (K bob (PrpF (P 20)))
rcCheck 4 = PubAnnounce aAnnounce (Ck [alice,bob,carol] cIgnorant)
rcCheck 5 = PubAnnounce aAnnounce (PubAnnounce bAnnounce (Ck [alice,bob] aKnowsBs))
rcCheck 6 = PubAnnounce aAnnounce (PubAnnounce bAnnounce (Ck [alice,bob] bKnowsAs))
rcCheck _ = PubAnnounce aAnnounce (PubAnnounce bAnnounce (Ck rcPlayers cIgnorant))

-- | All `rcChecks` are true in `rusSCN`.
-- This verifies the protocol for the fixed deal \(012|345|6\):
-- We can also check multiple protocols in a row without taking much longer because the BDD package caches results.
-- Compared to that, the DEMO implementation from [DHMR2006] needs 4 seconds to check one protocol.
--
-- >>> rcAllChecks
-- True
rcAllChecks :: Bool
rcAllChecks = rusSCN |= Conj (map rcCheck [0..7])

-- * Finding all five/six/seven-hands solutions

{- $
We can not just verify but also /find/ all protocols based on a set of five, six or seven hands.
To make the problem feasible we use a combination of manual reasoning and brute-force.
-}

possibleHands :: [[Int]]
possibleHands = [ [x,y,z] | x <- rcCards, y <- filter (> x) rcCards, z <-filter (> y) rcCards ]

pickHandsNoCrossing :: [ [Int] ] -> Int -> [ [ [Int] ] ]
pickHandsNoCrossing _ 0 = [ [ [ ] ] ]
pickHandsNoCrossing unused 1 = [ [h] | h <- unused ]
pickHandsNoCrossing unused n = concat [ [ h:hs | hs <- pickHandsNoCrossing (myfilter h unused) (n-1) ]  | h <- unused ] where
  myfilter h = filter (\xs -> length (h `intersect` xs) < 2 && h < xs) -- do not allow intersection > 2

{- $
The last line in the implementation of `pickHandsNoCrossing` includes two important restrictions
to the set of possible lists of hands that we will consider.
  First, Proposition 32 in [vD2003] tells us that safe announcements
    from Alice never contain ``crossing'' hands, i.e.~two hands which have more
    than one card in common.
  Second, without loss of generality we can assume that the hands in her
    announcement are lexicographically ordered.
  This leaves us with 1290 possible lists of five, six or seven hands of three cards.
-}

-- | All possible hands.
--
-- >>> length allHandLists
-- 1290
--
allHandLists :: [ [ [Int] ] ]
allHandLists = concatMap (pickHandsNoCrossing possibleHands) [5,6,7]

{- $
Which of these are actually safe announcements that can be used by Alice?
We can find them with the following `checkSet` function.
-}

-- | Given a set of cards, return whether it can safely be used by Alice.
checkSet :: [[Int]] -> Bool
checkSet set = all (evalViaBdd rusSCN) fs where
  aliceSays = K alice (Disj [ Conj $ map (alice `hasCard`) h | h <- set ])
  bobSays = K bob (carol `hasCard` 6)
  fs = [ aliceSays
       , PubAnnounce aliceSays bKnowsAs
       , PubAnnounce aliceSays (Ck [alice,bob] bKnowsAs)
       , PubAnnounce aliceSays (Ck [alice,bob,carol] cIgnorant)
       , PubAnnounce aliceSays (PubAnnounce bobSays (Ck [alice,bob] $ Conj [aKnowsBs, bKnowsAs]))
       , PubAnnounce aliceSays (PubAnnounce bobSays (Ck rcPlayers cIgnorant)) ]

-- | Safe hands that pass the `checkSet` test.
--
-- >>> length safeHandLists
-- 102
--
safeHandLists :: [ [ [Int] ] ]
safeHandLists = sort (filter checkSet allHandLists)

{- $
We can thus filter out the 102 safe announcements within a few seconds,
generating and verifying the same list as in Figure 3 from [vD2003]
where it was manually generated.

>>> head safeHandLists
[[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6]]

>>> last safeHandLists
[[0,1,2],[0,5,6],[1,4,6],[2,3,6],[3,4,5]]
-}

-- * Protocol synthesis

{- $
We now adopt a more general perspective considered in [EBMN2017].
Taking the perspective of Alice, we want to \emph{find} a plan.
-}

-- | Fix that Alice has \(\{0,1,2\}\) and that she will announce five hands, including this one.
-- Hence she has to pick four other hands of three cards each, i.e. she has to choose among
-- \[ \binom{\binom{7}{3} - 1}{4} = \binom{34}{4} = 46376 \]
-- many possible actions.
--
-- >>> length alicesActions
-- 46376
alicesActions :: [Form]
alicesActions = [ Disj $ map (alice `hasHand`) ([0,1,2]:otherHands) | otherHands <- handLists ] where
  handLists :: [ [ [Int] ] ]
  handLists = pickHands (delete [0,1,2] possibleHands) 4
  pickHands :: [ [Int] ] -> Int -> [ [ [Int] ] ]
  pickHands _     0 = [ [ [ ] ] ]
  pickHands hands 1 = [ [ h   ] | h <- hands ]
  pickHands hands n = [ h:hs    | h <- hands, hs <- pickHands (filter (h <) hands) (n-1) ]

{- $
For example, the first action Alice will consider is this:

==== __Show me__

>>> ppFormWith rcExplain (head alicesActions)
"((Alice has card 0 & Alice has card 1 & Alice has card 2) | (Alice has card 0 & Alice has card 1 & Alice has card 3) | (Alice has card 0 & Alice has card 1 & Alice has card 4) | (Alice has card 0 & Alice has card 1 & Alice has card 5) | (Alice has card 0 & Alice has card 1 & Alice has card 6))"
-}

{- $
Alice does not know which card Bob has, but of course she knows that he cannot have one of her cards.
Hence Alice considers four possibilities for his action of saying which card Carol has.
-}

bobsActions :: [Form]
bobsActions = [ carol `hasCard` n | n <- reverse [4..6] ]

-- ** Manually

-- | Solutions to Russian Cards by considering all elements of
-- `alicesActions` and `bobsActions`.
rcSolutions :: [ [Form] ]
rcSolutions = [ [a, b] | a <- alicesActions, b <- bobsActions, testPlan a b ] where
  testPlan :: Form -> Form -> Bool
  testPlan aSays bSays = all (evalViaBdd rusSCN)
    -- NOTE: increasing checks are faster than one big conjunction!
    [ aSays
    , PubAnnounce aSays bKnowsAs
    , PubAnnounce aSays cIgnorant
    , PubAnnounce aSays bSays
    , PubAnnounce aSays (PubAnnounce bSays aKnowsBs)
    , PubAnnounce aSays (PubAnnounce bSays (Ck [alice,bob] $ Conj [cIgnorant,aKnowsBs,bKnowsAs])) ]

-- ** Using general planning functions

{- $
We can also model the problem using the general functions for planning from "SMCDEL.Other.Planning".
-}

rcGoal :: Form
rcGoal = Conj [ aKnowsBs
              , bKnowsAs
              , Ck [alice,bob] (Conj [aKnowsBs, bKnowsAs])
              , Ck [alice,bob,carol] cIgnorant ]

-- | The plan consisting of `aAnnounce` and `bAnnounce`.
--
-- >>> reachesOn rcPlan rcGoal rusSCN
-- True
rcPlan :: OfflinePlan
rcPlan = [ aAnnounce, bAnnounce ]

-- | Find solutions using using `offlineSearch` from "SMCDEL.Other.Planning".
rcSolutionsViaPlanning :: [OfflinePlan]
rcSolutionsViaPlanning = offlineSearch maxSteps start actions constraints goal where
  maxSteps    = 2 -- We need two steps!
  start       = rusSCNfor (3,3,1)
  actions     = alicesActions ++ bobsActions
  constraints = [cIgnorant,bKnowsAs]
  goal        = Conj [aKnowsBs, bKnowsAs]

-- TODO speed up rus cards via planning?
-- It now takes around 3 minutes to generate all the working plans when we fix bobsForms = hasCard carol 6
-- Given the definition above it takes around 20 minutes.
-- In both cases we find the same 60 solutions.

{- $
In fact, in both ways we find the same first solution:

>>> head rcSolutionsViaPlanning == head rcSolutions
True
>>> map (ppFormWith rcExplain) (head rcSolutions)
["((Alice has card 0 & Alice has card 1 & Alice has card 2) | (Alice has card 0 & Alice has card 1 & Alice has card 3) | (Alice has card 0 & Alice has card 1 & Alice has card 4) | (Alice has card 0 & Alice has card 1 & Alice has card 5) | (Alice has card 2 & Alice has card 3 & Alice has card 4))","Carol has card 6"]
-}

-- * Generalized Russian Cards

{- $
Fun fact: Even if we want to use more or less than 7 cards, we do not have to modify the function `hasCard`.
-}

-- | An instance of the problem given by the number of cards given to each of the three agents.
type RusCardProblem = (Int,Int,Int)

-- | Formula to say that the cards are distributed in the given way.
distribute :: RusCardProblem -> Form
distribute (na,nb,nc) = Conj [ alice `hasAtLeast` na
                             , bob   `hasAtLeast` nb
                             , carol `hasAtLeast` nc ] where
  n = na + nb + nc
  hasAtLeast :: Agent -> Int -> Form
  hasAtLeast _ 0 = Top
  hasAtLeast i 1 = Disj [ i `hasCard` k | k <- nCards n ]
  hasAtLeast i k = Disj [ Conj (map (i `hasCard`) (sort set))
                        | set <- powerset (nCards n), length set == k ]

nCards :: Int -> [Int]
nCards n = [0..(n-1)]

nCardsGiven, nCardsUnique :: Int -> Form
nCardsGiven  n = Conj [ Disj [ i `hasCard` k | i <- rcPlayers ] | k <- nCards n ]
nCardsUnique n = Conj [ Neg $ isDouble k | k <- nCards n ] where
  isDouble k = Disj [ Conj [ x `hasCard` k, y `hasCard` k ] | x <- rcPlayers, y <- rcPlayers, x/=y, x < y ]

-- | Initial structure for a given instance of the problem.
rusSCNfor :: RusCardProblem -> KnowScene
rusSCNfor (na,nb,nc) = (KnS props law [ (i, obs i) | i <- rcPlayers ], defaultDeal) where
  n = na + nb + nc
  props   = [ P k | k <-[0..((length rcPlayers * n)-1)] ]
  law = boolBddOf $ Conj [ nCardsGiven n, nCardsUnique n, distribute (na,nb,nc)  ]
  obs i = [ P (3 * k + rcNumOf i) | k<-[0..6] ]
  defaultDeal =  [ let (PrpF p) = i `hasCard` k in p | i <- rcPlayers, k <- cardsFor i ]
  cardsFor "Alice" = [0..(na-1)]
  cardsFor "Bob"   = [na..(na+nb-1)]
  cardsFor "Carol" = [(na+nb)..(na+nb+nc-1)]
  cardsFor _       = error "Who is that?"

{- $
For the following cases it is unknown whether a multi-announcement solution exists.
It /is/ known that no two-announcement solution exists.

- (2,2,1)
- (3,2,1)
- (3,3,2)

Note also: (4,4,2) is discussed in [DS2011].
-}

possibleHandsN :: Int -> Int -> [[Int]]
possibleHandsN n na = filter alldiff $ nub $ map sort $ replicateM na (nCards n) where
  alldiff [] = True
  alldiff (x:xs) = x `notElem` xs && alldiff xs

allHandListsN :: Int -> Int -> [ [ [Int] ] ]
allHandListsN n na = concatMap (pickHandsNoCrossing (possibleHandsN n na)) [5,6,7]

-- FIXME how to adapt the number of hands in `allHandListsN` for larger n?

{- $
Note that we still use the same `pickHandsNoDouble`.
This is a problem because of the intersection constraint!
They only should have striclty less than `na - nc` cards in common!
-}

-- TODO generalize pickHandsNoDouble

aKnowsBsN, bKnowsAsN, cIgnorantN :: Int -> Form
aKnowsBsN n = Conj [ alice `Kw` (bob `hasCard` k) | k <- nCards n ]
bKnowsAsN n = Conj [ bob `Kw` (alice `hasCard` k) | k <- nCards n ]
cIgnorantN n = Conj $ concat [ [ Neg $ K carol $ alice `hasCard` i
                            , Neg $ K carol $ bob   `hasCard` i ] | i <- nCards n ]

checkSetFor :: RusCardProblem -> [[Int]] -> Bool
checkSetFor (na,nb,nc) set = reachesOn plan rcGoal (rusSCNfor (na,nb,nc)) where
  n = na + nb + nc
  aliceSays = K alice (Disj [ Conj $ map (alice `hasCard`) h | h <- set ])
  bobSays = K bob (carol `hasCard` last (nCards n))
  plan = [ aliceSays, bobSays ]

checkHandsFor :: RusCardProblem -> [ ( [[Int]], Bool) ]
checkHandsFor (na,nb,nc) = map (\hs -> (hs, checkSetFor (na,nb,nc) hs)) (allHandListsN n na) where
  n = na + nb + nc

allCasesUpTo :: Int -> [RusCardProblem]
allCasesUpTo bound = [ (na,nb,nc) | na <- [1..bound]
                                  , nb <- [1..(bound-na)]
                                  , nc <- [1..(bound-(na+nb))]
                                  -- these restrictions are only proven
                                  -- for two announcement plans!
                                  , nc < (na - 1)
                                  , nc < nb ]

-- TODO: Think about russian card protocols with more than two steps

-- * Russian Cards on Belief Structures with fewer Atoms

dontChange :: [Form] -> K.RelBDD
dontChange fs = conSet <$> sequence [ equ <$> K.mvBdd b <*> K.cpBdd b | b <- map boolBddOf fs ]

noDoubles :: Int -> Form
noDoubles n = Neg $ Disj [ notDouble k | k <- nCards n ] where
  notDouble k = Conj [alice `hasCard` k, bob `hasCard` k]

rusBelScnfor :: RusCardProblem -> K.BelScene
rusBelScnfor (na,nb,nc) = (K.BlS props law (fromList [ (i, obsbdd i) | i <- rcPlayers ]), defaultDeal) where
  n = na + nb + nc
  props   = [ P k | k <-[0..((2 * n)-1)] ]
  law = boolBddOf $ Conj [ noDoubles n, distribute (na,nb,nc)  ]
  obsbdd "Alice" = dontChange [ PrpF (P $ 2*k) | k <- [0..(n-1)] ]
  obsbdd "Bob"   = dontChange [ PrpF (P $ (2*k) + 1) | k <- [0..(n-1)] ]
  obsbdd "Carol" = dontChange [ Disj [PrpF (P $ 2*k), PrpF (P $ (2*k) + 1)] | k <- [0..(n-1)] ]
  obsbdd _       = error "Unkown Agent"
  defaultDeal =  [ let (PrpF p) = i `hasCard` k in p | i <- [alice,bob], k <- cardsFor i ] where
    cardsFor "Alice" = [0..(na-1)]
    cardsFor "Bob"   = [na..(na+nb-1)]
    cardsFor "Carol" = [(na+nb)..(na+nb+nc-1)]
    cardsFor _       = error "Unkown Agent"
