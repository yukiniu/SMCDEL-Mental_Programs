{-# LANGUAGE FlexibleInstances, UndecidableInstances, MultiParamTypeClasses, AllowAmbiguousTypes, OverloadedStrings, BangPatterns #-}

module SMCDEL.Internal.TexDisplay where

import Control.Concurrent (threadDelay)
import Control.Monad
import Data.GraphViz
import Data.GraphViz.Types.Generalised
import Data.GraphViz.Types.Monadic
import Data.List
import qualified Data.Text.Lazy as T
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Language.Haskell.TH
import System.Directory (findExecutable, doesFileExist, getModificationTime)
import System.Exit
import System.IO (hGetContents)
import System.IO.Temp
import System.IO.Unsafe (unsafePerformIO)
import System.Process

begintab, endtab, newline :: String
begintab  = "\\\\begin{tabular}{c}"
endtab    = "\\\\end{tabular}"
newline   = " \\\\\\\\[0pt] "

removeDoubleSpaces :: String -> String
removeDoubleSpaces (' ':' ':rest) = removeDoubleSpaces (' ':rest)
removeDoubleSpaces (x  : xs     ) = x : removeDoubleSpaces xs
removeDoubleSpaces [            ] = [ ]

class TexAble a where
  tex :: a -> String
  texTo :: a -> String -> IO ()
  texTo !x filename = writeFile (filename++".tex") (tex x)
  texDocumentTo :: a -> String -> IO ()
  texDocumentTo !x filename =
    writeFile (filename++".tex") (pre ++ tex x ++ post) where
      pre = concat [ "\\documentclass{standalone}"
                   , "\\usepackage[utf8]{inputenc}"
                   , "\\usepackage{tikz,fontenc,graphicx}"
                   , "\\usepackage[pdftex]{hyperref}"
                   , "\\usepackage{amssymb,amsmath,adjustbox}"
                   , "\\hypersetup{pdfborder={0 0 0},breaklinks=true}"
                   , "\\begin{document}"
                   ]
      post= "\\end{document}"
  pdfTo :: a -> String -> IO ()
  pdfTo !x filename = do
    texDocumentTo x filename
    runAndWait $ "cd " ++ filename ++ "/../; /usr/bin/pdflatex -interaction=nonstopmode "++filename++".tex"
  disp :: a -> IO ()
  disp !x = withSystemTempDirectory "smcdel" $ \tmpdir -> do
    let filename = tmpdir ++ "/disp"
    pdfTo x filename
    runIgnoreAndWait $ "open " ++ filename ++ ".pdf"
    threadDelay 5000000 -- give viewer five seconds before deleting tmpdir
  svgViaTex :: a -> String
  svgViaTex !x = unsafePerformIO $ withSystemTempDirectory "smcdel" $ \tmpdir -> do
    let filename = tmpdir ++ "/svgViaTex"
    pdfTo x filename
    runAndWait $ "pdftocairo -nocrop -svg " ++ filename ++ ".pdf " ++ filename ++ ".svg"
    readFile (filename ++ ".svg")

instance TexAble String where
  tex i = " \\text{" ++ i ++ "} "

instance TexAble Int where
  tex = show

-- | TeXing assignments as sets
instance TexAble a => TexAble [(a,Bool)] where
  tex ass = case filter snd ass of
    [] -> ""
    ps -> "$" ++ intercalate "," (map (tex.fst) ps) ++ "$"

runAndWait :: String -> IO ()
runAndWait command = do
  (_inp,_out,err,pid) <- runInteractiveCommand command
  exCode <- waitForProcess pid
  when (exCode /= ExitSuccess) $ do
    hGetContents err >>= (\x -> unless (null x) (putStrLn "STDERR:\n" >> putStrLn x))
    hGetContents _out >>= (\x -> unless (null x) (putStrLn "STDOUT:\n" >> putStrLn x))

runIgnoreAndWait :: String -> IO ()
runIgnoreAndWait command = do
  (_inp,_out,_err,pid) <- runInteractiveCommand command
  _ <- waitForProcess pid
  return ()

class KripkeLike a where
  getNodes :: a -> [(String,String)] -- nid,nlabel
  getEdges :: a -> [(String,String,String)] -- elabel,from,to
  getActuals :: a -> [String] -- nid
  getActuals = const []
  directed :: a -> Bool
  directed = const True
  nodeAts :: a -> Bool -> Attributes
  nodeAts _ True  = [shape DoubleCircle]
  nodeAts _ False = [shape Circle]
  toGraph :: a -> Data.GraphViz.Types.Generalised.DotGraph String
  toGraph x = (if directed x then digraph' else graph') $ do
    let nodes = getNodes x
    let actuals = filter (\n -> fst n `elem` getActuals x) nodes
    mapM_
      (\(nid,nlabel) -> node nid (toLabel nlabel : nodeAts x True))
      actuals
    mapM_
      (\(nid,nlabel) -> node nid (toLabel nlabel : nodeAts x False))
      (nodes \\ actuals)
    mapM_
      (\(elabel,from,to) -> edge from to [toLabel elabel])
      (getEdges x)
  dispDot :: a -> IO ()
  dispDot x = runGraphvizCanvas Dot (toGraph x) Xlib
  textDot :: a -> T.Text
  textDot = T.intercalate " " . T.lines . printDotGraph . toGraph
  svg :: a -> String
  svg x = unsafePerformIO $
    withSystemTempDirectory "smcdel" $ \tmpdir -> do
      _ <- runGraphvizCommand Dot (toGraph x) Svg (tmpdir ++ "/temp.svg")
      readFile (tmpdir ++ "/temp.svg")

newtype ViaDot a = ViaDot a
  deriving (Eq,Ord,Show)

dot2tex :: String -> IO ()
dot2tex args = do
  haveDot2tex <- findExecutable "dot2tex"
  case haveDot2tex of
    Nothing -> error "Please install dot2tex which is needed to show this."
    Just d2t -> runAndWait $ d2t ++ args

dot2texDefaultArgs :: String
dot2texDefaultArgs = " -ftikz -traw -p --autosize -w --usepdflatex "

instance (Ord a, Show a, KripkeLike a) => TexAble (ViaDot a) where
  tex (ViaDot x) = unsafePerformIO $
    withSystemTempDirectory "smcdel" $ \tmpdir -> do
      _ <- runGraphviz (toGraph x) DotOutput (tmpdir ++ "/temp.dot")
      dot2tex $ dot2texDefaultArgs ++ " --figonly " ++ tmpdir ++ "/temp.dot | sed '/^$/d' > " ++ tmpdir ++ "/temp.tex;"
      readFile (tmpdir ++ "/temp.tex")
  texTo (ViaDot x) filename = do
    _ <- runGraphviz (toGraph x) DotOutput (filename ++ ".dot")
    dot2tex $ dot2texDefaultArgs ++ " --figonly " ++ filename ++ ".dot | sed '/^$/d' > " ++ filename ++ ".tex;"
  texDocumentTo (ViaDot x) filename = do
    _ <- runGraphviz (toGraph x) DotOutput (filename ++ ".dot")
    dot2tex $ dot2texDefaultArgs ++ filename ++ ".dot -o " ++ filename ++ ".tex;"

-- | Save the SVG of something into the current folder.
makeSvg :: TexAble a => String -> a -> IO ()
makeSvg name x = let f = ("./" ++ name ++ ".svg")
                 in writeFile f (svgViaTex x) >> putStrLn f

-- | Save the SVG of something into the current folder - if it does not exist yet or is older than one hour.
refreshSvg :: TexAble a => String -> a -> IO ()
refreshSvg name x = do
  let f = "./" ++ name ++ ".svg"
  exists <- doesFileExist f
  todo <- if not exists then return True else do
    modTime <- getModificationTime f
    currentTime <- getCurrentTime
    return $ diffUTCTime currentTime modTime > 3600
  if todo then makeSvg name x else putStrLn (f ++ "already exists")

-- | Use Template Haskell to add markdown that shows the SVG from the @docs@ folder.
addSvg :: Name -> Q [Dec]
addSvg name = do
  oldDoc <- getDoc (DeclDoc name)
  let n = nameBase name
  let markdown = "\n\n![svgViaTex "++ n ++ "](docs/" ++ n ++ ".svg)\n"
  let newDoc = case oldDoc of
        Nothing -> markdown
        Just old -> old ++ markdown
  putDoc (DeclDoc name) newDoc
  return []
