module SMCDEL.Mental_Programs.Syntax_Semantics where
import Data.List
import SMCDEL.Language
import Data.HasCacBDD hiding (Top,Bot) -- to get "Bdd" and "con" etc.
import qualified Data.HasCacBDD as B (BddTree(..)) -- to get "Top" and "Bot"
-- see https://hackage.haskell.org/package/HasCacBDD-0.2.0.0/docs/Data-HasCacBDD.html for help :-)

import SMCDEL.Symbolic.K
-- import SMCDEL.Symbolic.S5 (unsafeParseS)

import Test.QuickCheck

-- checks whether a formula is true given a list of true propositions
satisfies :: State -> Form -> Bool
satisfies _  Top       = True
satisfies _  Bot       = False
satisfies s (PrpF p)      = p `elem` s
satisfies a (Neg f)    = not $ satisfies a f
satisfies a (Conj fs)   = all (satisfies a) fs
satisfies a (Disj fs)   = any (satisfies a) fs
satisfies a (Impl f g)  = not (satisfies a f) || satisfies a g
satisfies a (Equi f g)  = satisfies a f == satisfies a g
satisfies _ (K _ _) = error "This is not a boolean formula"
satisfies _ (Kw _ _) = error "This is not a boolean formula"
satisfies _ (PubAnnounce _ _) = error "This is not a boolean formula"
satisfies _ (Xor _) = error "not implemented by this system"
satisfies _ (Forall _ _) = error "not implemented by this system"
satisfies _ (Exists _ _) = error "not implemented by this system"
satisfies _ (Ck _ _) = error "not implemented by this system"
satisfies _ (Ckw _ _) = error "not implemented by this system"
satisfies _ (PubAnnounceW _ _) = error "not implemented by this system"
satisfies _ (Announce _ _ _) = error "not implemented by this system"
satisfies _ (AnnounceW _ _ _) = error "not implemented by this system"
satisfies _ (Dia _ _) = error "not implemented by this system"

-- Syntax of Mental Programs (corresponds to section 1 of the latex file)
data MenProg = Settop Prp | Setbot Prp | Test Form | Cup MenProg MenProg | Cap MenProg MenProg | Seq MenProg MenProg
    deriving (Eq,Ord,Show)

type Vocab = [Prp]
type State = [Prp]
type Statelaw = Form
type LegitStates = [State]


allStates :: Vocab -> [State]
allStates [] = [[]]
allStates (p:ps) = sort (allStates ps ++ [p:ss | ss <- allStates ps])

legitStates :: Vocab -> [Statelaw] -> LegitStates
legitStates v ls = [s | s <- allStates v, all (\l -> s `satisfies` l) ls]

toSet :: Ord a => [a] -> [a]
toSet = nub . sort

-- Semantics of Mental Programs 
rel :: Vocab -> [Statelaw] -> MenProg -> State -> State -> Bool
rel _ _ (Settop p) s t = toSet t == toSet (s ++ [p])
rel _ _ (Setbot p) s t = toSet t == toSet s \\ [p]
rel _ _ (Test beta) s t = toSet s == toSet t && satisfies s beta
rel v ss (Cup p1 p2) s t = rel v ss p1 s t || rel v ss p2 s t
rel v ss (Seq p1 p2) s t = any (\u -> rel v ss p1 s u && rel v ss p2 u t) (legitStates v ss ::[State])
rel v ss (Cap p1 p2) s t = rel v ss p1 s t && rel v ss p2 s t


-- Some examples:

-- This should be all true
examples1 :: [Bool]
examples1 = [rel (map P [0,1]) [Top] (Settop (P 0)) [P 1] [P 0, P 1],
             rel (map P [0,1]) [Top] (Setbot (P 1)) [P 0, P 1] [P 0],
             rel (map P [0,1,2]) [Top] (Test (Conj [PrpF $ P 0, PrpF $ P 1])) [P 0, P 1] [P 0, P 1],
             rel (map P [0,1]) [Top] (Cup (Settop (P 0)) (Settop (P 1))) [P 0] [P 0, P 1],
             rel (map P [0,1,2]) [Disj [PrpF $ P 1, PrpF $ P 2]] (Seq (Settop (P 2)) (Setbot (P 1))) [P 1] [P 2],
             rel (map P [0,1,2,3]) [Neg $ PrpF $ P 0] (Cap (Seq (Settop (P 3)) (Setbot (P 2))) (Seq (Setbot (P 2)) (Settop (P 3)))) [P 1, P 2] [P 1, P 3]]

-- copy :: Prp -> Prp
-- copy prp = prp + 1000 -- to be replaced by cp etc. from SMCDEL.Symbolic.K

-- -- Translations from Mental Programs to Boolean Formulas in section 5
translate :: [Prp] -> MenProg -> Form
translate v (Settop prp) = Conj [PrpF prp, (Conj [ Equi (PrpF $ mvP q) (PrpF $ cpP q) | q <- v, prp /= q ])]
translate v (Setbot prp) = Conj [Neg $ PrpF prp, (Conj [ Equi (PrpF $ mvP q) (PrpF $ cpP q) | q <- v, prp /= q ])]
translate v (Test f) = Conj [f, (Conj [ Equi (PrpF $ mvP q) (PrpF $ cpP q) | q <- v])]
translate v (Cup b1 b2) = Disj [(translate v b1) , (translate v b2)]
translate v (Seq b1 b2) = undefined
translate v (Cap b1 b2) = Conj [(translate v b1) , (translate v b2)]


-- LATER: replace BoolForm with "Bdd" type :-)
-- then use "con" and "conSet"

bla :: BddTree
bla = B.Top

-- The translation from Bdds to Mental Programs
-- Question: How to use top from Bdd? (hiding)
translate' :: Vocab -> BddTree -> MenProg
translate' _ (B.Bot) = Test Bot
translate' [] (B.Top) = Test Top
translate' (p:ps) (B.Top) = Seq (Cup (Setbot p) (Settop p)) (translate' ps B.Top)
translate' (p:ps) (B.Var k l r) | mvP p == P k = Cup (Seq (Test $ Neg $ PrpF p) (translate' (p:ps) r)) (Seq (Test $ PrpF p) (translate' (p:ps) l))
translate' (p:ps) (B.Var k l r) | cpP p == P k = Cup (Seq (Setbot p) (translate' ps r)) (Seq (Settop p) (translate' ps l))
translate' (p:ps) b = Seq (Cup (Setbot p) (Settop p)) (translate' ps b)
translate' _ _ = error "Illegal inputs"


-- The translation from Bdds to Mental Programs
-- The variables in Bdd are primed already
translate'' :: Vocab -> Bdd -> MenProg
translate'' v b
  | b == bot = Test Bot
  | b == top && v == [] = Test Top
  | b == top = Seq (Cup (Setbot p) (Settop p)) (translate'' ps top)
  | mvP (head v) == P k = Cup (Seq (Test $ Neg $ PrpF p) (translate'' v r)) (Seq (Test $ PrpF p) (translate'' v l))
  | cpP (head v) == P k = Cup (Seq (Setbot p) (translate'' ps r)) (Seq (Settop p) (translate'' ps l))
  | otherwise = Seq (Cup (Setbot p) (Settop p)) (translate'' ps b)
  where
      p = head v
      ps = tail v
      (Just k) = firstVarOf b
      l = thenOf b
      r = elseOf b
-- translate'' _ bot = Test Bot
-- translate'' [] top = Test Top
-- translate'' (p:ps) top = Seq (Cup (Setbot p) (Settop p)) (translate'' ps top)

examples2 :: [Bool]
examples2 = [rel (map P [0,1]) [Top] (translate'' [P 0, P 1] top) [P 1] [P 0, P 1],
             rel (map P [0,1]) [Top] (Setbot (P 1)) [P 0, P 1] [P 0],
             rel (map P [0,1,2]) [Top] (Test (Conj [PrpF $ P 0, PrpF $ P 1])) [P 0, P 1] [P 0, P 1],
             rel (map P [0,1]) [Top] (Cup (Settop (P 0)) (Settop (P 1))) [P 0] [P 0, P 1],
             rel (map P [0,1,2]) [Disj [PrpF $ P 1, PrpF $ P 2]] (Seq (Settop (P 2)) (Setbot (P 1))) [P 1] [P 2],
             rel (map P [0,1,2,3]) [Neg $ PrpF $ P 0] (Cap (Seq (Settop (P 3)) (Setbot (P 2))) (Seq (Setbot (P 2)) (Settop (P 3)))) [P 1, P 2] [P 1, P 3]]

-- 1. Generate Random Boolean Formulas
-- 2. QuickCheck

test :: IO ()
test = quickCheck (forAll (randomboolformWith [P 1, P 2] 7) (\(BF f) -> f == f))