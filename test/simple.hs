module Test (
    runTests,
) where

import qualified Text.Regex.PDeriv.ByteString.LeftToRight as LtoR

import qualified Data.ByteString.Char8 as S

import qualified Test.HUnit as Test

--Either ParseError (EPat, EState)

runLtoR :: S.ByteString      -- ^ regular expression
         -> S.ByteString -- ^ ByteString to match against
         -> (S.ByteString, S.ByteString, S.ByteString, [S.ByteString])
runLtoR p s =
    case LtoR.compile LtoR.defaultCompOpt LtoR.defaultExecOpt p of
      Left e -> error $ " compilation failed . " ++ show e
      Right r -> let out = LtoR.regexec r s
                 in case out of
                         (Left errString) -> error $ " run failed . " ++ errString
                         (Right Nothing) -> error "regexec returned nothing"
                         (Right (Just v)) -> v



mainpart :: (S.ByteString, S.ByteString, S.ByteString, [S.ByteString]) -> [String]
mainpart (_, m, _, _) = [S.unpack m]

prepart :: (S.ByteString, S.ByteString, S.ByteString, [S.ByteString]) -> [String]
prepart (p, _, _, _) = [S.unpack p]

postpart :: (S.ByteString, S.ByteString, S.ByteString, [S.ByteString]) -> [String]
postpart (_, _, p, _) = [S.unpack p]

matched :: (S.ByteString, S.ByteString, S.ByteString, [S.ByteString]) -> [String]
matched (_, _, _, m) = map S.unpack m

testLtoR :: String -> String -> ((S.ByteString, S.ByteString, S.ByteString, [S.ByteString]) -> [String]) -> [String] -> IO Test.Counts
testLtoR regex input get output =
  Test.runTestTT $ Test.TestLabel regex $ Test.TestCase (Test.assertEqual ("input: " ++ show input) output (get $ runLtoR (S.pack regex) (S.pack input)))

runTests :: IO ()
runTests = do {
    testLtoR ".*" "abc" mainpart ["abc"];
    testLtoR "a" "abc" mainpart ["a"];
    testLtoR "a|b" "abc" mainpart ["a"];
    testLtoR "b|a" "abc" mainpart ["a"];
    testLtoR "a|b" "bac" mainpart ["b"];
    testLtoR "b|a" "bac" mainpart ["b"];
    testLtoR ".*b" "bac" mainpart ["b"];
    testLtoR ".*b" "bac" postpart ["ac"];
    testLtoR "a.*" "bac" prepart ["b"];
    testLtoR ".*(b|a).*" "bac" matched ["a", ""];
    testLtoR ".*(b|a).*" "abc" matched ["b", ""];
    testLtoR ".*(bb|ab).*" "abc" matched ["ab", ""];
    testLtoR ".*(bb|ab).*" "abc" matched ["ab", ""];
    testLtoR ".*(bb|ab).*" "abc" matched ["ab", ""];
    testLtoR "(ab&c)" "abc" mainpart ["abc"];
    testLtoR "(c&ab)" "abc" mainpart ["abc"];
    return ()
}
