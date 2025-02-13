{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

{- |

This module implements so-called /Succinct Models/ where the relations of agents
are encoded using /Mental Programs/, a variant of /Propositional Dynamic Logic/.

References:

- [CS 2017]
  Tristan Charrier and François Schwarzentruber:
  /A Succinct Language for Dynamic Epistemic Logic/.
  In: AAMAS 2017.
  Paper: <http://www.aamas2017.org/proceedings/pdfs/p123.pdf>
  Long version: <https://hal.science/hal-01487001>

- [G 2020]
  Malvin Gattinger: /Towards Symbolic and Succinct Perspective Shifts/.
  In: EpiP at ICAPS 2020.
  Paper: <https://doi.org/10.5281/zenodo.4767546>
  Video: <https://www.youtube-nocookie.com/embed/h-LFXeqXKf4?rel=0>

The implementation here is based on:

- [H 2020]
  Maickel Hartlief: /Making Model Checking Scalable: Implementing Succinct Kripke Models for Public Announcement Logic/
  BSc thesis, University of Groningen, 2020.
  Thesis: <https://fse.studenttheses.ub.rug.nl/23607>
  Code: <https://github.com/maickelhartlief/SucExpModelCheckers>
-}

module SMCDEL.Succinct.K where

import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Test.QuickCheck

import SMCDEL.Language
import SMCDEL.Internal.Help (powerset)

import Data.HasCacBDD hiding (Top, Bot)
import SMCDEL.Symbolic.S5 (boolBddOf, boolEvalViaBdd)

import SMCDEL.Symbolic.K (mvP, cpP, mv, cp)
import Data.Maybe

-- | Syntax of mental programs.
-- π ::= p <- β | β? | π ; π | π ∪ π | π ∩ π) | π⁻
data MenProg = Ass Prp Form            -- ^ assign value of form to prop (can be restricted to Top/Bot)
             | Tst Form                -- ^ test form
             | Seq [MenProg]           -- ^ sequence
             | Cup [MenProg]           -- ^ union aka choice
             | Cap [MenProg]           -- ^ intersection
             | Inv MenProg             -- ^ inverse of program (can be eliminated)
             deriving (Show, Eq, Ord)

-- | Remove operators for inverse and general assignment.
-- The result is equivalent by Lemma 19 in [Gat 2020].
removeOps :: MenProg -> MenProg
removeOps mp@(Ass _ Top) = mp
removeOps mp@(Ass _ Bot) = mp
removeOps    (Ass prp f) = Cup [ Seq [Tst f, Ass prp Top]
                               , Seq [Tst (Neg f), Ass prp Bot] ]
removeOps (Tst tf      ) = Tst tf
removeOps (Seq mps     ) = Seq $ map removeOps mps
removeOps (Cup mps     ) = Cup $ map removeOps mps
removeOps (Cap mps     ) = Cap $ map removeOps mps
removeOps (Inv mp) = case removeOps mp of
  Ass p Top -> Seq [ Tst (PrpF p), Cup [Ass p Top, Ass p Bot] ]
  Ass p Bot -> Seq [ Tst (Neg $ PrpF p), Cup [Ass p Top, Ass p Bot] ]
  Ass _ _ -> error "impossible"
  Tst tf -> Tst tf
  Seq mps -> Seq (reverse $ map (removeOps . Inv) mps)
  Cup mps -> Cup (map (removeOps . Inv) mps)
  Cap mps -> Cap (map (removeOps . Inv) mps)
  Inv _ -> error "impossible"

-- | A state is the set of propositions that are true.
type State = IntSet

-- | A *succinct* model consists of a vocabulary, a state law,
-- a list of announced formulas (with the newest first)
-- and a mental program for each agent.
data SuccinctModel = SMo [Prp] Form [Form] (Map Agent MenProg) deriving (Eq,Ord,Show)

instance HasVocab SuccinctModel where
  vocabOf (SMo v _ _ _) = v

instance HasAgents SuccinctModel where
  agentsOf (SMo _ _ _ mp) = Map.keys mp

-- | States of a succinct model -- after restricting due to the announcements made.
statesOf :: SuccinctModel -> Set State
statesOf (SMo vocab betaM []     _) = Set.filter (`boolIsTrue` betaM) (allStatesFor vocab)
statesOf (SMo vocab betaM (f:fs) mp) = Set.filter (\s -> sucIsTrue (oldModel,s) f) (statesOf oldModel) where
  oldModel = SMo vocab betaM fs mp

-- | Given a state, evaluate a Boolean formula.
boolIsTrue :: State -> Form -> Bool
boolIsTrue a = boolEvalViaBdd (map P $ IntSet.toList a)

-- | The set of all states for a given vocabulary.
-- This can be exponential and should be avoided.
allStatesFor :: [Prp] -> Set State
allStatesFor = Set.map IntSet.fromList . Set.fromList . map (map (\(P i) -> i)) . powerset

-- | Check if the state is in a model, also after the already happened announcements!
isStateOf :: State -> SuccinctModel -> Bool
isStateOf s (SMo _     betaM []     _  ) = s `boolIsTrue` betaM
isStateOf s (SMo vocab betaM (f:fs) mp) =
   sucIsTrue (oldModel,s) f && (s `isStateOf` oldModel) where
     oldModel = SMo vocab betaM fs mp

-- | Are the two given states connected via this mental program?
areConnected :: [Prp] -> MenProg -> State -> State -> Bool
areConnected _ (Ass (P i) f) s1 s2       = if boolIsTrue s1 f
                                         then IntSet.insert i s1 == s2
                                         else IntSet.delete i s1 == s2
areConnected _ (Tst f) s1 s2         = s1 == s2 && boolIsTrue s1 f
areConnected _ (Seq []       ) s1 s2 = s1 == s2
areConnected voc (Seq (mp:rest)) s1 s2 = any (\ s3 -> areConnected voc (Seq rest) s3 s2) (reachableFromHere voc mp s1)
areConnected _ (Cup []       ) _ _   = False
areConnected voc (Cup (mp:rest)) s1 s2 = areConnected voc mp s1 s2 || areConnected voc (Cup rest) s1 s2
areConnected _ (Cap []       ) _ _   = True
areConnected voc (Cap (mp:rest)) s1 s2 = areConnected voc mp s1 s2 && areConnected voc (Cap rest) s1 s2
areConnected voc (Inv mp       ) s1 s2 = areConnected voc mp s2 s1

-- | Set of states that are reachable from a certain state via a mental program.
reachableFromHere :: [Prp] -> MenProg -> State -> Set State
reachableFromHere _ (Ass (P i) f) s = if boolIsTrue s f
                                     then Set.singleton $ IntSet.insert i s
                                     else Set.singleton $ IntSet.delete i s
reachableFromHere _ (Tst f) s         = if boolIsTrue s f then Set.singleton s else Set.empty
reachableFromHere _(Seq []) s        = Set.singleton s
reachableFromHere voc (Seq (mp:rest)) s = Set.unions $ Set.map (reachableFromHere voc (Seq rest)) (reachableFromHere voc mp s)
reachableFromHere _ (Cup []) _        = Set.empty
reachableFromHere voc (Cup (mp:rest)) s = reachableFromHere voc mp s `Set.union` reachableFromHere voc (Cup rest) s
reachableFromHere voc (Cap []) _        = allStatesFor voc -- I have changed `Set.empty` into this. This is where the problem comes from!
reachableFromHere voc (Cap (mp:rest)) s = reachableFromHere voc (Cap rest) s `Set.intersection` reachableFromHere voc mp s
reachableFromHere voc (Inv mp)        s = reachableFromHere voc (removeOps (Inv mp)) s

-- | Semantics on succinct models, computed explicitly.
sucIsTrue :: (SuccinctModel, State) -> Form -> Bool
sucIsTrue _  Top       = True
sucIsTrue _  Bot       = False
sucIsTrue (_ ,s) (PrpF (P i)) = i `IntSet.member` s
sucIsTrue a (Neg f)    = not $ sucIsTrue a f
sucIsTrue a (Conj fs)   = all (sucIsTrue a) fs
sucIsTrue a (Disj fs)   = any (sucIsTrue a) fs
sucIsTrue a (Xor fs)    = odd $ length (filter id $ map (sucIsTrue a) fs)
sucIsTrue a (Impl f g)  = not (sucIsTrue a f) || sucIsTrue a g
sucIsTrue a (Equi f g)  = sucIsTrue a f == sucIsTrue a g
sucIsTrue (m@(SMo voc _ _ mp), s) (K i f) =
   all
    (\s' -> sucIsTrue (m,s') f)
    (Set.filter (`isStateOf` m) $ reachableFromHere voc (mp ! i) s)
sucIsTrue a (Kw i f) = sucIsTrue a (Disj [ K i f, K i (Neg f) ])
sucIsTrue (m, s) (PubAnnounce f g)  = not (sucIsTrue (m, s) f) || sucIsTrue (m `update` f, s) g
sucIsTrue _ f = error $ "Operator not implemented: " ++ show f

-- | Push box of a mental program into a Boolean formula.
push :: MenProg -> Form -> Form
push (Ass (P i) af) (PrpF (P j)) = if i == j then af else PrpF (P j)
push (Ass (P _) _ ) Top = Top
push (Ass (P _) _ ) Bot = Bot
push (Ass (P i) af) (Neg f) = Neg $ push (Ass (P i) af) f
push (Ass (P i) af) (Conj fs) = Conj $ map (push (Ass (P i) af)) fs
push (Ass (P i) af) (Disj fs) = Disj $ map (push (Ass (P i) af)) fs
push (Ass (P i) af) (Xor fs) = Xor $ map (push (Ass (P i) af)) fs
push (Ass (P i) af) (Impl f g) = Impl (push (Ass (P i) af) f) (push (Ass (P i) af) g)
push (Ass (P i) af) (Equi f g) = Equi (push (Ass (P i) af) f) (push (Ass (P i) af) g)
push (Tst tf)        f = tf `Impl` f
push (Seq []       ) f = f
push (Seq (mp:rest)) f = push mp $ push (Seq rest) f
push (Cup mps      ) f = Conj [ push mp f | mp <- mps ]
push (Cap _        ) _ = error "Cannot push intersection into formula."
push (Inv mp       ) f = push (removeOps (Inv mp)) f
push _ f = error $ "not a Boolean formula: " ++ show f

-- | Reduction axioms for public announcements.
-- TODO: move to SMCDEL.Language
reduce :: Form -> Form -> Form
reduce _  Top = Top
reduce af Bot = Neg af
reduce af (PrpF (P i)) = af `Impl` PrpF (P i)
reduce af (Neg f) = af `Impl` Neg (reduce af f)
reduce af (Conj fs) = Conj (map (reduce af) fs)
reduce af (Disj fs) = Disj (map (reduce af) fs)
reduce af (Impl f g) = reduce af f `Impl` reduce af g
reduce af (Xor fs) = af `Impl` Xor (map (reduce af) fs)
reduce af (Equi f g) = af `Impl` Equi (reduce af f) (reduce af g)
reduce af (PubAnnounce f g) = reduce af (reduce f g)
reduce _  (Forall _ _) = error "cannot reduce through quantifier"
reduce _  (Exists _ _) = error "cannot reduce through quantifier"
reduce af (K i f) = af `Impl` K i (reduce af f)
reduce af (Kw i f) = af `Impl` Disj [ K i (reduce af f) , K i (Neg $ reduce af f) ]
reduce _  (Ck _ _) = error "cannot reduce through common knowledge"
reduce _  (Ckw _ _) = error "cannot reduce through common knowledge"
reduce _  (Dk _ _) = error "cannot reduce through common knowledge"
reduce _  (Dkw _ _) = error "cannot reduce through distributed knowledge"
reduce _  (G _) = error "cannot reduce through global modality"
reduce _  (Dia _ _) = error "cannot reduce through diamond"

-- | Rewrite a formula by eliminating K operators using `push`
-- and public announcements using reduction axioms.
-- PROBLEM: this ignores the announcements already done in the list in `m`.
rewrite :: SuccinctModel -> Form -> Form
rewrite _  Top       = Top
rewrite _  Bot       = Bot
rewrite _ (PrpF (P i)) = PrpF (P i)
rewrite m (Neg f)    = Neg $ rewrite m f
rewrite m (Conj fs)   = Conj $ map (rewrite m) fs
rewrite m (Disj fs)   = Disj $ map (rewrite m) fs
rewrite m (Impl f g)  = Impl (rewrite m f) (rewrite m g)
rewrite m (Equi f g)  = Equi (rewrite m f) (rewrite m g)
rewrite m@(SMo _ _ _ mp) (K i f) = push (mp ! i) (rewrite m f)
rewrite m (Kw i f)    = rewrite m (Disj [ K i (rewrite m f), K i (Neg (rewrite m f)) ])
rewrite m (PubAnnounce f g)  = rewrite m (reduce f g)
rewrite _ f = error $ "operator not implemented: " ++ show f

canRewrite :: Form -> Bool
canRewrite Top       = True
canRewrite Bot       = True
canRewrite (PrpF (P _)) = True
canRewrite (Neg f)    = canRewrite f
canRewrite (Conj fs)   = all canRewrite fs
canRewrite (Disj fs)   = all canRewrite fs
canRewrite (Impl f g)  = canRewrite f && canRewrite g
canRewrite (Equi f g)  = canRewrite f && canRewrite g
canRewrite (K _ f) = canRewrite f
canRewrite (PubAnnounce f g)  = canRewrite f && canRewrite g
canRewrite _ = False

-- | Semantics on succinct models, via rewriting and push - TODO: test this
evalViaRewrite :: PointedSuccinctModel -> Form -> Bool
evalViaRewrite (m, s) f = boolIsTrue s (rewrite m f)

-- * BDD VERSION

-- | Push box of a mental program into a BDD.
pushBdd :: MenProg -> Bdd -> Bdd
pushBdd (Ass (P i) af) b = Data.HasCacBDD.substit i (boolBddOf af) b
pushBdd (Tst tf)        b = boolBddOf tf `con` b
pushBdd (Seq []       ) b = b
pushBdd (Seq (mp:rest)) b = pushBdd mp $ pushBdd (Seq rest) b
pushBdd (Cup mps      ) f = conSet [ pushBdd mp f | mp <- mps ]
pushBdd (Cap _        ) _ = error "TODO" -- Conj [ pushBdd mp f | mp <- mps ] -- PROBLEM - how to do this?
pushBdd (Inv mp       ) f = pushBdd (removeOps (Inv mp)) f

-- | Rewrite a formula by eliminating K operators using `push`
-- and public announcements using reduction axioms.
-- PROBLEM: this ignores the announcements already done in the list in `m`.
rewriteBdd :: SuccinctModel -> Form -> Bdd
rewriteBdd _  Top       = top
rewriteBdd _  Bot       = bot
rewriteBdd _ (PrpF (P i)) = var i
rewriteBdd m (Neg f)    = neg $ rewriteBdd m f
rewriteBdd m (Conj fs)   = conSet $ map (rewriteBdd m) fs
rewriteBdd m (Disj fs)   = disSet $ map (rewriteBdd m) fs
rewriteBdd m (Impl f g)  = rewriteBdd m f `imp` rewriteBdd m g
rewriteBdd m (Equi f g)  = rewriteBdd m f `equ` rewriteBdd m g
rewriteBdd m@(SMo _ _ [] mp) (K i f) = pushBdd (mp ! i) (rewriteBdd m f) -- WRONG, not using announcements!

rewriteBdd m@(SMo _ _ anns mp) (K i f) = pushBdd (mp ! i) (rewriteBdd m f) -- WRONG, not using announcements!
-- IDEA: use pushBDD, but also demand that the announcements hold.
-- How/when should the announced *formulas* become Bdds?
-- - here/now: then we need to do it more often
-- - when being announced? ---> change SMo type to contain a BDD, compute boolean equiv when announcement is made.

rewriteBdd m (Kw i f)    = dis (rewriteBdd m $ K i f) (rewriteBdd m $ K i (Neg f))
rewriteBdd m (PubAnnounce f g)  = rewriteBdd (m `update` f) g
rewriteBdd _ f = error $ "operator not implemented: " ++ show f

-- | Semantics on succinct models, via rewriting and push - TODO: test this
evalViaRewriteBdd :: PointedSuccinctModel -> Form -> Bool
evalViaRewriteBdd (m, s) f = evaluateFun (rewriteBdd m f) (`elem` IntSet.toList s)

instance Pointed SuccinctModel State
type PointedSuccinctModel = (SuccinctModel, State)

instance Semantics PointedSuccinctModel where
  isTrue = sucIsTrue

instance Semantics SuccinctModel where
  isTrue m f = all (\s -> isTrue (m,s) f) (statesOf m)

-- | Update a succinct model with a public announcent.
sucPublicAnnounce :: SuccinctModel -> Form -> SuccinctModel
sucPublicAnnounce (SMo v fm fs rel) f = SMo v fm (f:fs) rel

instance Update PointedSuccinctModel Form where
   checks = []
   unsafeUpdate (m, s) f = (sucPublicAnnounce m f, s)

instance Update SuccinctModel Form where
   checks = []
   unsafeUpdate = sucPublicAnnounce

-- * Subformulas and Shrinking

-- | List of subprograms, including the given program itself.
-- Used by the `shrink` function for QuickCheck.
subprogs :: MenProg -> [MenProg]
subprogs (Ass p f)  = [Ass p f]
subprogs (Tst f)    = [Tst f' | f' <- shrinkform f]
subprogs (Seq mps)  = Seq mps : nub (concatMap subprogs mps)
subprogs (Cup mps)  = Cup mps : nub (concatMap subprogs mps)
subprogs (Cap mps)  = Cap mps : nub (concatMap subprogs mps)
subprogs (Inv mp)  =  mp : map Inv (subprogs mp)

shrinkprog :: MenProg -> [MenProg]
shrinkprog f = (subprogs f \\ [f]) ++ otherShrinks f
  where
    otherShrinks (Seq mps) = [Seq mps' | mps' <- powerset mps \\ [mps]]
    otherShrinks (Cup mps) = [Cup mps' | mps' <- powerset mps \\ [mps]]
    otherShrinks (Cap mps) = [Cap mps' | mps' <- powerset mps \\ [mps]]
    otherShrinks _ = []


-- * Random Generation

instance Arbitrary MenProg where
  arbitrary = sized $ randomMenProgWith defaultVocabulary
  shrink = shrinkprog

randomMenProgWith :: [Prp] -> Int -> Gen MenProg
randomMenProgWith voc 0 = oneof [ Ass <$> elements voc <*> elements [Top,Bot]
                                , pure $ Tst Top
                                , pure $ Tst Bot
                                ]
randomMenProgWith voc n = oneof [ Ass <$> elements voc <*> elements [Top,Bot]
                                -- , (\ p (BF f) -> Ass p f) <$> elements voc <*> randomboolformWith voc n
                                , pure $ Tst Top
                                , pure $ Tst Bot
                                , (\ (BF f) -> Tst f) <$> randomboolformWith voc n
                                , (\x y -> Seq [x,y]) <$> rmp <*> rmp
                                -- , (\x y z -> Seq [x,y,z]) <$> rmp <*> rmp <*> rmp
                                , (\x y -> Cup [x,y]) <$> rmp <*> rmp
                                -- , (\x y z -> Cup [x,y,z]) <$> rmp <*> rmp <*> rmp
                                , (\x y -> Cap [x,y]) <$> rmp <*> rmp
                                -- , (\x y z -> Cap [x,y,z]) <$> rmp <*> rmp <*> rmp
                                -- , Inv <$> rmp
                                ]
  where
    rmp = randomMenProgWith voc (n `div` 3)

{-
-- | Given an integer that indicates the number of primes needed, given the number of primes for a prticular proposition, 
-- output the corresponding number in the new vocabulary.
-- For example, assuming that there could be two primes in the new vocabulary, for P2', it's mapped to P 7 in the new vocabulary:
+-----------+-------------------+-------------------+
| Variable  | Single vocabulary | Triple vocabulary |
+==========-+===================+===================+
| \(p_0  \) | @P 0@             | @P 0@             |
+-----------+-------------------+-------------------+
| \(p_0' \) |                   | @P 1@             |
+-----------+-------------------+-------------------+
| \(p_0''\) |                   | @P 2@             |
+-----------+-------------------+-------------------+
| \(p_1  \) | @P 1@             | @P 3@             |
+-----------+-------------------+-------------------+
| \(p_1' \) |                   | @P 4@             |
+-----------+-------------------+-------------------+
| \(p_1''\) |                   | @P 5@             |
+-----------+-------------------+-------------------+
| \(p_2  \) | @P 2@             | @P 6@             |
+-----------+-------------------+-------------------+
| \(p_2' \) |                   | @P 7@             |
+-----------+-------------------+-------------------+
| \(p_2''\) |                   | @P 8@             |
+-----------+-------------------+-------------------+
...
-}

mvcpP :: Int -> Int -> Prp -> Prp
mvcpP n m (P k) = P (k * (n + 1) + m)

unmvcpP :: Int -> Int -> Prp -> Prp
unmvcpP n m (P x) = P ((x - m) `div` n)

positiveInt :: Gen (Int, Int, Int)
positiveInt = do
  Positive x <- arbitrary
  Positive y <- arbitrary
  Positive z <- arbitrary
  return (x, y, z)

mvinverse :: Property
mvinverse = forAll positiveInt $ \ (n, m, k) ->  P k == unmvcpP n m (mvcpP n m (P k))

-- | The list version of mvcp
mvcp :: Int -> Int -> [Prp] -> [Prp]
mvcp n m = map (mvcpP n m)

unmvcp :: Int -> Int -> [Prp] -> [Prp]
unmvcp n m = map (unmvcpP n m)

-- | Translations from Mental Programs to Bdds in section 5.
-- The inverse and general assignment operators are assumed to be removed from the mental programs inputs already.
translationMPToBdd :: [Prp] -> MenProg -> Form
translationMPToBdd v (Ass prp Top) = Conj [PrpF $ mvcpP 1 1 prp, Conj [ Equi (PrpF $ mvcpP 1 0 q) (PrpF $ mvcpP 1 1 q) | q <- v, prp /= q ]]
translationMPToBdd v (Ass prp Bot) = Conj [Neg $ PrpF $ mvcpP 1 1 prp, Conj [ Equi (PrpF $ mvcpP 1 0 q) (PrpF $ mvcpP 1 1 q) | q <- v, prp /= q ]]
translationMPToBdd v (Tst f) = Conj [replPsInF (v `zip` mvcp 1 0 v) f, Conj [ Equi (PrpF $ mvcpP 1 0 q) (PrpF $ mvcpP 1 1 q) | q <- v]]
translationMPToBdd v (Cup [mp1, mp2]) = Disj [translationMPToBdd v mp1 , translationMPToBdd v mp2]
translationMPToBdd v (Cap [mp1, mp2]) = Conj [translationMPToBdd v mp1 , translationMPToBdd v mp2]
translationMPToBdd v (Seq [mp1, mp2]) = replPsInF dictionary1 (exists vprime (Conj [replPsInF dictionary2 (translationMPToBdd v mp1), replPsInF dictionary5 $ replPsInF dictionary4 $ replPsInF dictionary3 (translationMPToBdd v mp2)]))
  where
    exists :: [Prp] -> Form -> Form
    exists [] f = f 
    exists (p : ps) f = exists ps $ eliminate p f
    vprime = mvcp 2 1 v
    dictionary1 = (mvcp 2 0 v `zip` mvcp 1 0 v) ++ (mvcp 2 1 v `zip` mvcp 1 1 v) ++ (mvcp 2 2 v `zip` mvcp 1 1 v)
    dictionary2 = (mvcp 1 0 v `zip` mvcp 2 0 v) ++ (mvcp 1 1 v `zip` mvcp 2 1 v)
    dictionary3 = (mvcp 1 0 v `zip` mvcp 2 0 v) ++ (mvcp 1 1 v `zip` mvcp 2 1 v)
    dictionary4 = mvcp 2 1 v `zip` mvcp 2 2 v
    dictionary5 = mvcp 2 0 v `zip` mvcp 2 1 v
translationMPToBdd _ _ = undefined

eliminate :: Prp -> Form -> Form 
eliminate p f = Disj [SMCDEL.Language.substit p Top f, SMCDEL.Language.substit p Bot f]

eliminatedFormExample1 :: Form 
eliminatedFormExample1 = SMCDEL.Language.substit (P 1) (Disj [Top, PrpF $ P 3]) (Conj [PrpF $ P 1, PrpF $ P 2])

-- | The substitution function which, given a formula, replaces all occurances of variables in v with v2.
-- replPsInF :: [(Prp,Prp)] -> Form -> Form
-- Already implemented from `src/SMCDEL/Language.hs`

-- QuickCheck examples:


listToState :: [Prp] -> State
listToState = IntSet.fromList . map (\(P x) -> x)

translationMPToBddcorrect :: Property
translationMPToBddcorrect = forAll (fmap (\ws -> P 0 : ws) (sublistOf (map P [1..7]))) $ \voc ->
                            forAll (randomMenProgWith voc 5) $ \mp ->
                            forAll (elements (powerset voc)) $ \s ->
                            forAll (elements (powerset voc)) $ \t ->
                            areConnected voc mp (listToState s) (listToState t) == boolIsTrue (listToState (mvcp 1 0 s) `IntSet.union` listToState (mvcp 1 1 t)) (translationMPToBdd voc (removeOps mp))

-- The debugging process (All couterexamples fixed already!): 
-- * This part helped me identify the errors in the definition of: reachableFromHere voc (Cap []) _ = Set.empty

-- -- *** Failed! Falsified (after 36 tests):  
-- -- [P 3,P 4]
-- -- Seq [Cap [Tst Top,Ass (P 3) Bot],Tst Top]
-- -- []
-- -- []

-- counterExample0 :: Bool 
-- counterExample0 = areConnected voc mp (listToState s) (listToState t) where 
--   voc = [P 3, P 4]
--   mp = Seq [Cap [Tst Top,Ass (P 3) Bot],Tst Top] -- False
--   -- mp = Cap [Tst Top,Ass (P 3) Bot] -- True
--   -- mp = Tst Top -- True
--   -- mp = Seq [Tst Top, Tst Top] -- True
--   s = []
--   t = []


-- counterExample0Reachable :: Set State
-- counterExample0Reachable = reachableFromHere voc mp s1 where 
--   voc = [P 3, P 4]
--   mp = Cap [Tst Top,Ass (P 3) Bot] -- fromList [], which is wrong
--   -- mp = Tst Top
--   s1 = listToState []

-- counterExample0Reachable' :: Set State
-- -- counterExample0Reachable = reachableFromHere (Ass (P 3) Bot) (listToState []) --fromList [fromList []]
-- counterExample0Reachable' = reachableFromHere voc (Tst Top) (listToState []) --fromList [fromList []]
--   where voc = [P 3, P 4]

-- counterExample0Reachable'' :: Set State
-- counterExample0Reachable'' = reachableFromHere voc (Cap (mp:rest)) s where 
--   voc = [P 3, P 4]
--   mp = Tst Top -- fromList [], which is wrong
--   rest = [Ass (P 3) Bot]
--   s = listToState []

-- counterExample0Reachable''' :: Set State
-- counterExample0Reachable''' = reachableFromHere voc (Cap rest) s `Set.intersection` reachableFromHere voc mp s where
--   voc = [P 3, P 4]
--   mp = Tst Top -- fromList [], which is wrong
--   rest = [Ass (P 3) Bot]
--   s = listToState []

-- counterExample0Reachable'''' :: Set State
-- counterExample0Reachable'''' = reachableFromHere voc (Cap rest) s where
--   voc = [P 3, P 4]
--   mp = Tst Top -- fromList [], which is wrong
--   rest = [Ass (P 3) Bot]
--   s = listToState []

-- counterExample0''' :: Bool
-- counterExample0''' = areConnected voc (Seq rest) s3 s2 where 
--   voc = [P 3, P 4]
--   rest = [Tst Top]
--   s3 = listToState [] 
--   s2 = listToState []

-- counterExample0'''' :: Bool
-- counterExample0'''' = any (\ s3 -> areConnected voc (Seq rest) s3 s2) (reachableFromHere voc mp s1) where 
--   voc = [P 3, P 4]
--   mp = Cap [Tst Top,Ass (P 3) Bot]
--   s1 = listToState []
--   rest = [Tst Top]
--   s2 = listToState []

-- counterExample0' :: Bool 
-- counterExample0' = boolIsTrue (listToState (mvcp 1 0 s) `IntSet.union` listToState (mvcp 1 1 t)) (translationMPToBdd voc (removeOps mp)) where 
--   voc = [P 3, P 4]
--   mp = Seq [Cap [Tst Top,Ass (P 3) Bot],Tst Top]
--   s = []
--   t = []

-- * This part helped me identify the problems with the definition `replPsInF repl (Exists ps f) = Exists (map (replPsInP repl) ps) (replPsInF repl f)`

-- voc1 :: [Prp]
-- voc1 = map P [0, 1, 2]

-- Counterexample:
--   *** Failed! Falsified (after 18 tests):  
-- Cup [Seq [Ass (P 2) Bot,Tst Top],Cup [Tst Top,Tst Bot]]
-- [P 1,P 2]
-- [P 0,P 1]

-- counterexample1 :: Bool
-- counterexample1 = areConnected mp (listToState s) (listToState t) where 
--   mp = Cup [Seq [Ass (P 2) Bot,Tst Top],Cup [Tst Top,Tst Bot]]
--   s = [P 1, P 2]
--   t = [P 0, P 1]

-- counterexample1' :: Bool
-- counterexample1' = boolIsTrue (listToState (mvcp 1 0 s) `IntSet.union` listToState (mvcp 1 1 t)) (translationMPToBdd voc1 (removeOps mp)) where 
--   mp = Cup [Seq [Ass (P 2) Bot,Tst Top],Cup [Tst Top,Tst Bot]]
--   s = [P 1, P 2]
--   t = [P 0, P 1]

-- counterexample1'' :: Form
-- counterexample1'' = translationMPToBdd voc1 (removeOps mp) where   
--   mp = Cup [Seq [Ass (P 2) Bot,Tst Top],Cup [Tst Top,Tst Bot]]

-- counterexample1''' :: Form
-- counterexample1''' = translationMPToBdd voc1 (removeOps mp) where   
--   mp = Seq [Ass (P 2) Bot,Tst Top]

-- counterexample1'''' :: Bool
-- counterexample1'''' = areConnected mp (listToState s) (listToState t) == boolIsTrue (listToState (mvcp 1 0 s) `IntSet.union` listToState (mvcp 1 1 t)) (translationMPToBdd voc1 (removeOps mp)) where 
--   -- mp = Seq [Ass (P 2) Bot,Tst Top] -- False
--   -- mp = Ass (P 2) Bot -- True
--   mp = Tst Top -- True
--   s = [P 1, P 2]
--   t = [P 0, P 1]

-- counterexample2 :: Bool
-- counterexample2 = areConnected mp (listToState s) (listToState t) == boolIsTrue (listToState (mvcp 1 0 s) `IntSet.union` listToState (mvcp 1 1 t)) (translationMPToBdd voc1 (removeOps mp)) where 
--   -- mp = Seq [Ass (P 1) Top, Ass (P 2) Bot] -- True
--   -- mp = Seq [Ass (P 2) Bot, Tst Top] -- False
--   -- mp = Seq [Tst Top, Tst Top] -- False 
--   -- mp = Seq [Tst Top, Tst Bot] -- True 
--   mp = Tst Top
--   s = [P 1, P 2]
--   t = [P 0, P 1]

-- counterexample2' :: Bool
-- counterexample2' = areConnected mp (listToState s) (listToState t) == boolIsTrue (listToState (mvcp 1 0 s) `IntSet.union` listToState (mvcp 1 1 t)) (translationMPToBdd voc1 (removeOps mp)) where 
--   -- mp = Seq [Ass (P 1) Top, Ass (P 2) Bot] -- True
--   -- mp = Seq [Ass (P 2) Bot, Tst Top] -- False
--   mp = Seq [Tst Top, Tst Top] -- False 
--   -- mp = Seq [Tst Top, Tst Bot] -- True 
--   s = [P 1, P 2]
--   t = [P 0, P 1]

-- counterexample2'' :: Bool
-- counterexample2'' = boolIsTrue (listToState (mvcp 1 0 s) `IntSet.union` listToState (mvcp 1 1 t)) (translationMPToBdd voc1 (removeOps mp)) where 
--   -- mp = Seq [Ass (P 1) Top, Ass (P 2) Bot] -- True
--   -- mp = Seq [Ass (P 2) Bot, Tst Top] -- False
--   mp = Seq [Tst Top, Tst Top] -- False 
--   -- mp = Seq [Tst Top, Tst Bot] -- True 
--   s = [P 1, P 2]
--   t = [P 0, P 1]



-- | Translations from Bdds to Mental Programs in section 5.
-- Is there any particular reason why we couldn't do pattern matching on Bdd? 
translationBddToMP :: [Prp] -> Bdd -> MenProg
translationBddToMP v b
    | b == bot = Tst Bot
    | b == top && null v = Tst Top
    | b == top = Seq [Cup [Ass (head v) Top, Ass (head v) Top], translationBddToMP (tail v) top]
    | null v = error (show b)
    | mvP (head v) == P (fromJust $ firstVarOf b) = Cup [Seq [Tst $ Neg $ PrpF (head v), translationBddToMP v (elseOf b)], Seq [Tst $ PrpF (head v), translationBddToMP v (thenOf b)]]
    | cpP (head v) == P (fromJust $ firstVarOf b) = Cup [Seq [Ass (head v) Bot, translationBddToMP (tail v) (elseOf b)], Seq [Ass (head v) Top, translationBddToMP (tail v) (thenOf b)]]
    | otherwise = Seq [Cup [Ass (head v) Bot, Ass (head v) Top], translationBddToMP (tail v) b]


