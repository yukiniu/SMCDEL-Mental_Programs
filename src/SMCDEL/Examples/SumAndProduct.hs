{- |

We solve the famous Sum \& Product puzzle from:

- Hans Freudenthal (1969):
  /Formulering van het 'som-en-product'-probleem/.
  Nieuw Archief voor Wiskunde, volume 17, page 152.

Translated from Dutch the puzzle goes as follows:

> A says to S and P: "I chose two numbers x, y such that 1 < x < y
> and x + y <= 100. I will tell s = x+y to S alone, and p=xy
> to P alone.
> These messages will stay secret.
> But you should try to calculate the pair (x,y)."
>
> A does as announced. Now follows this conversation:
>
> P says: "I do not know it."
>
> S says: "I knew that."
>
> P says: "Now I know it."
>
> S says: "Now I also know it."
>
> Determine the pair (x,y).

Our implementation is faster than the one in the following work which also used BDDs:

- Xiangyu Luo, Kaile Su, Abdul Sattar and Yan Chen (2008):
  /Solving Sum and Product Riddle via BDD-Based Model Checking/.
  Proceedings of the 2008 IEEE/WIC/ACM International Conference on Web Intelligence and Intelligent Agent Technology, pages 630-633.
  <https://doi.org/10.1109/WIIAT.2008.277>

Overall it is known that BBDs encoding /products/ are relatively large and inefficient.
And indeed the explicit model checker DEMO-S5 still solves this puzzle a bit faster.
For a benchmark and further discussion see the file @bench/sumandproduct.hs@
and Section 4.6 of [MG2018].

-}

module SMCDEL.Examples.SumAndProduct where

import Data.List
import Data.Maybe

import SMCDEL.Language
import SMCDEL.Internal.Help
import SMCDEL.Symbolic.S5

-- * Encoding Numeric Variables

-- $ We first need to encode the value of numbers with boolean propositions.

-- | All possible pairs such that \( 1 < x < y \) and \( x + y \leq 100 \).
pairs :: [(Int, Int)]
pairs = [(x,y) | x<-[2..100], y<-[2..100], x<y, x+y<=100]

{- $
For each of the variables x y and s
we use 7 propositions to label [2..100], because \(2^6 = 64 < 100 < 128 = 2^7\)
-}

xProps, yProps, sProps :: [Prp]
xProps = [(P  1)..(P  7)]
yProps = [(P  8)..(P 14)]
sProps = [(P 15)..(P 21)]

-- | We need 12 propositions for the product, because 2^11 = 2048 < 2500 < 4096 = 2^12
pProps :: [Prp]
pProps = [(P 22)..(P 33)]

sapAllProps :: [Prp]
sapAllProps = sort $ xProps ++ yProps ++ sProps ++ pProps

{- $
The following four functions allow us to say that a variable has a given value.
For example:

>>> xIs 5
Conj [PrpF (P 1),PrpF (P 2),PrpF (P 3),PrpF (P 4),PrpF (P 6),Neg (PrpF (P 5)),Neg (PrpF (P 7))]
-}

xIs, yIs, sIs, pIs :: Int -> Form
xIs n = booloutofForm (powerset xProps !! n) xProps
yIs n = booloutofForm (powerset yProps !! n) yProps
sIs n = booloutofForm (powerset sProps !! n) sProps
pIs n = booloutofForm (powerset pProps !! n) pProps

xyAre :: (Int,Int) -> Form
xyAre (n,m) = Conj [ xIs n, yIs m ]

-- * Initial Structure

sapKnStruct :: KnowStruct
sapKnStruct = KnS sapAllProps law obs where
  law = boolBddOf $ Disj [ Conj [ xyAre (x,y), sIs (x+y), pIs (x*y) ] | (x,y) <- pairs ]
  obs = [ (alice, sProps), (bob, pProps) ]

sapKnows :: Agent -> Form
sapKnows i = Disj [ K i (xyAre p) | p <- pairs ]

-- * Updates and Solution

sapForm1, sapForm2, sapForm3 :: Form
sapForm1 = K alice $ Neg (sapKnows bob) -- Sum: I knew that you didn't know the numbers.
sapForm2 = sapKnows bob   -- Product: Now I know the two numbers
sapForm3 = sapKnows alice -- Sum: Now I know the two numbers too

sapProtocol :: Form
sapProtocol = Conj [ sapForm1
                   , PubAnnounce sapForm1 sapForm2
                   , PubAnnounce sapForm1 (PubAnnounce sapForm2 sapForm3) ]

-- | The solutions to the puzzle are those states where this conjunction holds.
--
-- __Spoiler Alert__
--
-- >>> sapSolutions
-- [[P 1,P 2,P 3,P 4,P 6,P 7,P 8,P 9,P 10,P 13,P 15,P 16,P 18,P 19,P 20,P 22,P 23,P 24,P 25,P 26,P 27,P 30,P 32,P 33]]
--
sapSolutions :: [[Prp]]
sapSolutions = whereViaBdd sapKnStruct sapProtocol

-- | A helper function to tell us what the value of `sapSolutions` means:
--
-- __Spoiler Alert__
--
-- >>> map sapExplainState sapSolutions
-- ["x = 4, y = 13, x+y = 17 and x*y = 52"]
--
sapExplainState :: [Prp] -> String
sapExplainState truths = concat
  [ "x = ", explain xProps
  , ", y = ", explain yProps
  , ", x+y = ", explain sProps
  , " and x*y = ", explain pProps ] where
  explain = show . nmbr truths

nmbr :: [Prp] -> [Prp] -> Int
nmbr truths varProps = fromMaybe (error "Value not found") $
  elemIndex (varProps `intersect` truths) (powerset varProps)

{- $
We can also verify that it is a solution, and that it is the unique solution.

If \(x = 4\) and \(y=13\), then the announcements are truthful:

>>> validViaBdd sapKnStruct (Impl (Conj [xIs 4, yIs 13]) sapProtocol)
True

And if the announcements are truthful, then x==4 and y==13.
>>> validViaBdd sapKnStruct (Impl sapProtocol (Conj [xIs 4, yIs 13]))
True
-}
