{-# LANGUAGE TemplateHaskell #-}

{- |
We model the scenario described in the following reference.

- David Chaum (1988):
  /The dining cryptographers problem: Unconditional sender and recipient untraceability/.
  Journal of Cryptology, number 1, volume 1, pages 65-75.
  <https://doi.org/10.1007/BF00206326>

> Three cryptographers went out to have diner. After a lot of delicious and
> expensive food the waiter tells them that their bill has already been paid.
> The cryptographers are sure that either it was one of them or the NSA\@. They
> want to find what is the case but if one of them paid they do not want that
> person to be revealed.

To accomplish this, they can use the following protocol:

> For every pair of cryptographers a coin is flipped in such a way that only
> those two see the result. Then they announce whether the two coins they saw
> were different or the same. But, there is an exception: If one of them paid,
> then this person says the opposite. After these announcements are made, the
> cryptographers can infer that the NSA paid iff the number of people saying
> that they saw the same result on both coins is even.

This module works with the default choice of CacBDD and "SMCDEL.Symbolic.S5".
For an alternative version also compatible with the CUDD package and usable
for benchmarking, see "SMCDEL.Examples.DiningCrypto.General".

-}

module SMCDEL.Examples.DiningCrypto where

import Data.List (delete)
import Data.Maybe (fromJust)

import SMCDEL.Internal.TexDisplay
import SMCDEL.Language
import SMCDEL.Symbolic.S5

-- * Three Agents

-- ** Initial Structure

-- | A knowledge structure to model the story.
-- Given an index 0, 1, 2, or 3 for who paid and three boolean values for the random coins we get the corresponding scenario.
dcScnInit :: Int -> (Bool,Bool,Bool) -> KnowScene
dcScnInit payer (b1,b2,b3) = ( KnS props law obs , truths ) where
  props = [ P 0   -- The NSA paid
          , P 1   -- Alice paid
          , P 2   -- Bob paid
          , P 3   -- Charlie paid
          , P 4   -- shared bit of Alice and Bob
          , P 5   -- shared bit of Alice and Charlie
          , P 6 ] -- shared bit of Bob and Charlie
  law   = boolBddOf $ Conj [ someonepaid, notwopaid ]
  obs   = [ (show (1::Int),[P 1, P 4, P 5])
          , (show (2::Int),[P 2, P 4, P 6])
          , (show (3::Int),[P 3, P 5, P 6]) ]
  truths = [ P payer ] ++ [ P 4 | b1 ] ++ [ P 5 | b2 ] ++ [ P 6 | b3 ]

-- | The set of possibilities is limited by two conditions: Someone must have paid but no two people (including the NSA) have paid:
someonepaid, notwopaid :: Form
someonepaid = Disj (map (PrpF . P) [0..3])
notwopaid = Conj [ Neg $ Conj [ PrpF $ P x, PrpF $ P y ] | x<-[0..3], y<-[(x+1)..3] ]

-- | Example scenario where Alice paid and the random coins are 1, 1 and 0:
dcScn1 :: KnowScene
dcScn1 = dcScnInit 1 (True,True,False)
$(addSvg 'dcScn1)

-- ** Updates

-- | Helper function let each agent compute the `Xor` of all three variables they know.
--
-- >>> map (evalViaBdd dcScn1) [reveal 1, reveal 2, reveal 3]
-- [True,True,True]
--
reveal :: Int -> Form
reveal 1 = Xor (map PrpF [P 1, P 4, P 5])
reveal 2 = Xor (map PrpF [P 2, P 4, P 6])
reveal _ = Xor (map PrpF [P 3, P 5, P 6])

-- | Result after announcing these three facts.
dcScn2 :: KnowScene
dcScn2 = dcScn1 `updates` [reveal 1, reveal 2, reveal 3]
$(addSvg 'dcScn2)

-- | Formula to say that everyone knows whether the NSA paid for the dinner or not.
everyoneKnowsWhetherNSApaid :: Form
everyoneKnowsWhetherNSApaid = Conj [ Kw (show i) (PrpF $ P 0) | i <- [1..3]::[Int] ]

{- $
After the announcements everyone knows whether the NS paid:

>>> dcScn2 |= everyoneKnowsWhetherNSApaid
True

Further more, it is only known to Alice that she paid:

>>> dcScn2 |= K "1" (PrpF (P 1))
True

>>> dcScn2 |= K "2" (PrpF (P 1))
False

>>> dcScn2 |= K "3" (PrpF (P 1))
False
-}

-- | Check all of the above in one formula using ``announce whether'' operator.
-- Furthermore we parameterize the last check on who actually paid, i.e.\ if one of the three agents paid, then the other two do not know this.
nobodyknowsWhoPaid :: Form
nobodyknowsWhoPaid = Conj
  [ Impl (PrpF (P 1)) (Conj [Neg $ K "2" (PrpF $ P 1), Neg $ K "3" (PrpF $ P 1) ])
  , Impl (PrpF (P 2)) (Conj [Neg $ K "1" (PrpF $ P 2), Neg $ K "3" (PrpF $ P 2) ])
  , Impl (PrpF (P 3)) (Conj [Neg $ K "1" (PrpF $ P 3), Neg $ K "2" (PrpF $ P 3) ]) ]
$(addSvg 'nobodyknowsWhoPaid)

-- | Formula saying that after the three whether-announcements we have
-- both `everyoneKnowsWhetherNSApaid` and `nobodyknowsWhoPaid`.
dcCheckForm :: Form
dcCheckForm = pubAnnounceW (reveal 1) $ pubAnnounceW (reveal 2) $ pubAnnounceW (reveal 3) $
    Conj [ everyoneKnowsWhetherNSApaid, nobodyknowsWhoPaid ]

{- $
The formula holds in the Example scenario:

>>> dcScn1 |= dcCheckForm
True

We can also check that the formula is valid on the whole knowledge structure.
This means the protocol is secure not just for the particular instance where
Alice paid and the random bits (i.e.~flipped coins) are as stated above, but
for all possible combinations of payers and random bits or coin flips.
-}

-- | Check that `dcCheckForm` is valid on `dcScn1`.
-- Runs within a fraction of a second.
--
-- >>> dcValid
-- True
dcValid :: Bool
dcValid = validViaBdd dcStruct dcCheckForm where (dcStruct,_) = dcScn1

-- * General protocol for \(n\) agents

{- $
A generalized version of the protocol for more than \(3\) agents uses exclusive or instead of odd/even.
The following implements this general case for $n$ dining cryptographers.
We also use it for benchmarking.
Note that we need \( \sum_{i=1}^{n-1} i = \frac{n(n-1)}{2} \) many shared bits.
This distinguishes the Dining Cryptographers from
the Muddy Children ("SMCDEL.Examples.MuddyChildren") and
the Drinking Logicians example ("SMCDEL.Examples.DrinkLogic")
where the number of propositions needed to model the situation was just the number of agents.
-}

-- ** Initial Structure

genDcSomeonepaid :: Int -> Form
genDcSomeonepaid n = Disj (map (PrpF . P) [0..n])

genDcNotwopaid :: Int -> Form
genDcNotwopaid n = Conj [ Neg $ Conj [ PrpF $ P x, PrpF $ P y ] | x<-[0..n], y<-[(x+1)..n] ]

-- | Initial structure for Dining Cryptographers. Using a complete graph of shared bits.
genDcKnsInit :: Int -> KnowStruct
genDcKnsInit n = KnS props law obs where
  props = [ P 0 ] -- The NSA paid
    ++ [ (P 1) .. (P n) ] -- agent i paid
    ++ sharedbits
  law = boolBddOf $ Conj [genDcSomeonepaid n, genDcNotwopaid n]
  obs = [ (show i, obsfor i) | i<-[1..n] ]
  sharedbitLabels = [ [k,l] | k <- [1..n], l <- [1..n], k<l ] -- n(n-1)/2 shared bits
  sharedbitRel = zip sharedbitLabels [ (P $ n+1) .. ]
  sharedbits =  map snd sharedbitRel
  obsfor i =  P i : map snd (filter (\(label,_) -> i `elem` label) sharedbitRel)

genDcEveryoneKnowsWhetherNSApaid :: Int -> Form
genDcEveryoneKnowsWhetherNSApaid n = Conj [ Kw (show i) (PrpF $ P 0) | i <- [1..n] ]

-- ** Updates

genDcReveal :: Int -> Int -> Form
genDcReveal n i = Xor (map PrpF ps) where
  (KnS _ _ obs) = genDcKnsInit n
  ps            = fromJust $ lookup (show i) obs

genDcNobodyknowsWhoPaid :: Int -> Form
genDcNobodyknowsWhoPaid n =
  Conj [ Impl (PrpF (P i)) (Conj [Neg $ K (show k) (PrpF $ P i) | k <- delete i [1..n] ]) | i <- [1..n] ]

-- | Defined using `pubAnnounceWhetherStack`.
genDcCheckForm :: Int -> Form
genDcCheckForm n =
  pubAnnounceWhetherStack [ genDcReveal n i | i<-[1..n] ] $
    Conj [ genDcEveryoneKnowsWhetherNSApaid n, genDcNobodyknowsWhoPaid n ]

genDcValid :: Int -> Bool
genDcValid n = validViaBdd (genDcKnsInit n) (genDcCheckForm n)

{- $
We check the protocol for \(4\) dining cryptographers.

>>> genDcValid 4
True
-}
