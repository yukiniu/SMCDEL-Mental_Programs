import Distribution.Simple
import Distribution.Simple.Setup (HaddockFlags)
import Distribution.Types.HookedBuildInfo
import System.Process (callCommand)

main :: IO ()
main = defaultMainWithHooks simpleUserHooks { preHaddock = myPreHaddock }

myPreHaddock :: Args -> HaddockFlags -> IO HookedBuildInfo
myPreHaddock _ _ = do
  callCommand "cd docs && make -B"
  return emptyHookedBuildInfo
