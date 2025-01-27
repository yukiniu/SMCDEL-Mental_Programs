module SMCDEL.Succinct.K_Old where

import Data.List
import Data.Maybe
import Data.HasCacBDD hiding (Top,Bot)
import qualified Data.HasCacBDD as B (BddTree(..))

import SMCDEL.Language
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.S5 (boolEvalViaBdd)

-- | Syntax of Mental Programs
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
legitStates v ls = [s | s <- allStates v, all (\l -> s `boolEvalViaBdd` l) ls]

toSet :: Ord a => [a] -> [a]
toSet = nub . sort

-- Semantics of Mental Programs
rel :: Vocab -> [Statelaw] -> MenProg -> State -> State -> Bool
rel _ _ (Settop p) s t = toSet t == toSet (s ++ [p])
rel _ _ (Setbot p) s t = toSet t == toSet s \\ [p]
rel _ _ (Test beta) s t = toSet s == toSet t && boolEvalViaBdd s beta
rel v ss (Cup p1 p2) s t = rel v ss p1 s t || rel v ss p2 s t
rel v ss (Seq p1 p2) s t = any (\u -> rel v ss p1 s u && rel v ss p2 u t) (legitStates v ss ::[State])
rel v ss (Cap p1 p2) s t = rel v ss p1 s t && rel v ss p2 s t



-- -- Translations from Mental Programs to Boolean Formulas in section 5
translate :: [Prp] -> MenProg -> Form
translate v (Settop prp) = Conj [PrpF prp, Conj [ Equi (PrpF $ mvP q) (PrpF $ cpP q) | q <- v, prp /= q ]]
translate v (Setbot prp) = Conj [Neg $ PrpF prp, Conj [ Equi (PrpF $ mvP q) (PrpF $ cpP q) | q <- v, prp /= q ]]
translate v (Test f) = Conj [f, Conj [ Equi (PrpF $ mvP q) (PrpF $ cpP q) | q <- v]]
translate v (Cup b1 b2) = Disj [translate v b1 , translate v b2]
translate v (Seq b1 b2) = undefined
translate v (Cap b1 b2) = Conj [translate v b1 , translate v b2]


-- The translation from Bdds to Mental Programs
translate' :: Vocab -> BddTree -> MenProg
translate' _      B.Bot = Test Bot
translate' []     B.Top = Test Top
translate' (p:ps) B.Top = Seq (Cup (Setbot p) (Settop p)) (translate' ps B.Top)
translate' (p:ps) (B.Var k l r) | mvP p == P k = Cup (Seq (Test $ Neg $ PrpF p) (translate' (p:ps) r)) (Seq (Test $ PrpF p) (translate' (p:ps) l))
translate' (p:ps) (B.Var k l r) | cpP p == P k = Cup (Seq (Setbot p) (translate' ps r)) (Seq (Settop p) (translate' ps l))
translate' (p:ps) b = Seq (Cup (Setbot p) (Settop p)) (translate' ps b)
translate' _ _ = error "Illegal inputs"


-- The translation from Bdds to Mental Programs
-- The variables in Bdd are primed already
translate'' :: Vocab -> Bdd -> MenProg
translate'' v b
    | b == bot = Test Bot
    | b == top && null v = Test Top
    | b == top = Seq (Cup (Setbot p) (Settop p)) (translate'' ps top)
    | null v = error (show b)
    | mvP (head v) == P k = Cup (Seq (Test $ Neg $ PrpF p) (translate'' v r)) (Seq (Test $ PrpF p) (translate'' v l))
    | cpP (head v) == P k = Cup (Seq (Setbot p) (translate'' ps r)) (Seq (Settop p) (translate'' ps l))
    | otherwise = Seq (Cup (Setbot p) (Settop p)) (translate'' ps b)
    where
      p = head v
      ps = tail v
      k = fromJust $ firstVarOf b
      l = thenOf b
      r = elseOf b
