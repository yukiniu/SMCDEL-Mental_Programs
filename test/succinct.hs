module Main where

import Control.Monad
import Test.QuickCheck
import Test.Hspec
import Data.HasCacBDD hiding (Top,Bot)
import qualified Data.HasCacBDD as B (BddTree(..))

import SMCDEL.Language
import SMCDEL.Succinct.K
import SMCDEL.Symbolic.K
import SMCDEL.Symbolic.S5 (boolBddOf, boolEvalViaBdd)

main :: IO ()
main = hspec $ do
  it "examples1" $
    and examples1

  it "examples2" $
    and examples1

  it "test1 translate''" $
    let voc = [P 0]
        voc' = [P 0, P 1]
        x = [] -- need to be subsets of voc
        y = [P 0]
    in (forAll (randomboolformWith voc' 7) (\(BF f) -> rel voc [] (translate'' voc (boolBddOf f)) x y == ((mv x ++ cp y) `boolEvalViaBdd` f)))

  it "test2 translate''" $
    let voc = map P [0..6]
        voc' = mv voc ++ cp voc
        x = [P 0, P 1] -- need to be subsets of voc
        y = [P 1, P 2]
    in quickCheck (forAll (randomboolformWith voc' 7) (\(BF f) -> rel voc [] (translate'' voc (boolBddOf f)) x y == ((mv x ++ cp y) `boolEvalViaBdd` f)))

  it "test3 translate''" $
    let voc = map P [0..3]
        voc' = mv voc ++ cp voc
        -- x = sublistOf voc -- need to be subsets of voc
        y = [P 1, P 2]
    in quickCheck (forAll (liftArbitrary2 (randomboolformWith voc' 7) (sublistOf voc))
        (\(BF f, x) -> rel voc [] (translate'' voc (boolBddOf f)) x y == ((mv x ++ cp y) `boolEvalViaBdd` f)))

  it "test4 translate''" $
    let voc = map P [0..3]
        voc' = mv voc ++ cp voc
        -- x = sublistOf voc -- need to be subsets of voc
        -- y = [P 1, P 2]
    in quickCheck
       (forAll (liftM3 (,,) (randomboolformWith voc' 7) (sublistOf voc) (sublistOf voc))
        (\(BF f, x, y) -> rel voc [] (translate'' voc (boolBddOf f)) x y == ((mv x ++ cp y) `boolEvalViaBdd` f)))

-- This should be all true
examples1 :: [Bool]
examples1 = [rel (map P [0,1]) [Top] (Settop (P 0)) [P 1] [P 0, P 1],
             rel (map P [0,1]) [Top] (Setbot (P 1)) [P 0, P 1] [P 0],
             rel (map P [0,1,2]) [Top] (Test (Conj [PrpF $ P 0, PrpF $ P 1])) [P 0, P 1] [P 0, P 1],
             rel (map P [0,1]) [Top] (Cup (Settop (P 0)) (Settop (P 1))) [P 0] [P 0, P 1],
             rel (map P [0,1,2]) [Disj [PrpF $ P 1, PrpF $ P 2]] (Seq (Settop (P 2)) (Setbot (P 1))) [P 1] [P 2],
             rel (map P [0,1,2,3]) [Neg $ PrpF $ P 0] (Cap (Seq (Settop (P 3)) (Setbot (P 2))) (Seq (Setbot (P 2)) (Settop (P 3)))) [P 1, P 2] [P 1, P 3]]



examples2 :: [Bool]
examples2 = [rel (map P [0,1]) [Top] (translate'' [P 0, P 1] top) [P 1] [P 0, P 1],
             rel (map P [0,1]) [Top] (Setbot (P 1)) [P 0, P 1] [P 0],
             rel (map P [0,1,2]) [Top] (Test (Conj [PrpF $ P 0, PrpF $ P 1])) [P 0, P 1] [P 0, P 1],
             rel (map P [0,1]) [Top] (Cup (Settop (P 0)) (Settop (P 1))) [P 0] [P 0, P 1],
             rel (map P [0,1,2]) [Disj [PrpF $ P 1, PrpF $ P 2]] (Seq (Settop (P 2)) (Setbot (P 1))) [P 1] [P 2],
             rel (map P [0,1,2,3]) [Neg $ PrpF $ P 0] (Cap (Seq (Settop (P 3)) (Setbot (P 2))) (Seq (Setbot (P 2)) (Settop (P 3)))) [P 1, P 2] [P 1, P 3]]
