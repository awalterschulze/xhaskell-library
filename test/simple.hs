module Test (
    runTests,
    main,
) where

import qualified Text.Regex.PDeriv.ByteString.LeftToRight as LeftToRight
import qualified Text.Regex.PDeriv.ByteString.RightToLeft as RightToLeft
import qualified Text.Regex.PDeriv.ByteString.LeftToRightD as LeftToRightD
import qualified Text.Regex.PDeriv.ByteString.Posix as Posix
import qualified Text.Regex.PDeriv.ByteString.TwoPasses as TwoPasses

import qualified Data.ByteString.Char8 as S

import qualified Test.HUnit as Test

type RegexecFunc r = r      -- ^ Compiled regular expression
       -> S.ByteString -- ^ ByteString to match against
       -> Either String (Maybe (S.ByteString, S.ByteString, S.ByteString, [S.ByteString]))

type CompileFunc r =
    S.ByteString -- ^ The regular expression to compile
    -> Either String r -- ^ Returns: the compiled regular expression

type Runner = S.ByteString      -- ^ regular expression
         -> S.ByteString -- ^ ByteString to match against
         -> Result

type Result = (S.ByteString, S.ByteString, S.ByteString, [S.ByteString])

type Getter = (Result -> [String])

run :: CompileFunc r -> RegexecFunc r -> Runner
run compile regexec p s =
  case compile p of
    Left e -> error $ " compilation failed . " ++ show e
    Right r -> let out = regexec r s
             in case out of
                     (Left errString) -> error $ " run failed . " ++ errString
                     (Right Nothing) -> error "regexec returned nothing"
                     (Right (Just v)) -> v

test :: String -> String -> String -> Runner -> Getter -> [String] -> IO Test.Counts
test name regex input runner get output =
    Test.runTestTT $ Test.TestLabel name $ Test.TestCase (Test.assertEqual ("input: " ++ show input) output (get $ runner (S.pack regex) (S.pack input)))

testLtoR :: String -> String -> Getter -> [String] -> IO Test.Counts
testLtoR regex input = test ("LeftToRight("++regex++")") regex input (run (LeftToRight.compile LeftToRight.defaultCompOpt LeftToRight.defaultExecOpt) LeftToRight.regexec)

testLtoRD :: String -> String -> Getter -> [String] -> IO Test.Counts
testLtoRD regex input = test ("LeftToRightD("++regex++")") regex input (run (LeftToRightD.compile LeftToRightD.defaultCompOpt LeftToRightD.defaultExecOpt) LeftToRightD.regexec)

testRtoL :: String -> String -> Getter -> [String] -> IO Test.Counts
testRtoL regex input = test ("RightToLeft("++regex++")") regex input (run (RightToLeft.compile RightToLeft.defaultCompOpt RightToLeft.defaultExecOpt) RightToLeft.regexec)

testPosix :: String -> String -> Getter -> [String] -> IO Test.Counts
testPosix regex input = test ("Posix("++regex++")") regex input (run (Posix.compile Posix.defaultCompOpt Posix.defaultExecOpt) Posix.regexec)

test2Pass :: String -> String -> Getter -> [String] -> IO Test.Counts
test2Pass regex input = test ("TwoPasses("++regex++")") regex input (run (TwoPasses.compile TwoPasses.defaultCompOpt TwoPasses.defaultExecOpt) TwoPasses.regexec)

mainpart :: Getter
mainpart (_, m, _, _) = [S.unpack m]

prepart :: Getter
prepart (p, _, _, _) = [S.unpack p]

postpart :: Getter
postpart (_, _, p, _) = [S.unpack p]

matched :: Getter
matched (_, _, _, m) = map S.unpack m

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
    testLtoR "(ab%c)" "abc" mainpart ["abc"];
    testLtoR "(c%ab)" "abc" mainpart ["abc"];

    testLtoRD ".*" "abc" mainpart ["abc"];
    testLtoRD "a" "abc" mainpart ["a"];
    testLtoRD "a|b" "abc" mainpart ["a"];
    testLtoRD "b|a" "abc" mainpart ["a"];
    testLtoRD "a|b" "bac" mainpart ["b"];
    testLtoRD "b|a" "bac" mainpart ["b"];
    testLtoRD ".*b" "bac" mainpart ["b"];
    testLtoRD ".*b" "bac" postpart ["ac"];
    testLtoRD "a.*" "bac" prepart ["b"];
    testLtoRD ".*(b|a).*" "bac" matched ["a", ""];
    testLtoRD ".*(b|a).*" "abc" matched ["b", ""];
    testLtoRD ".*(bb|ab).*" "abc" matched ["ab", ""];
    testLtoRD ".*(bb|ab).*" "abc" matched ["ab", ""];
    testLtoRD ".*(bb|ab).*" "abc" matched ["ab", ""];
    testLtoRD "(ab%c)" "abc" mainpart ["abc"];
    testLtoRD "(c%ab)" "abc" mainpart ["abc"];

    testPosix ".*" "abc" mainpart ["abc"];
    testPosix "a" "abc" mainpart ["a"];
    testPosix "a|b" "abc" mainpart ["a"];
    testPosix "b|a" "abc" mainpart ["a"];
    testPosix "a|b" "bac" mainpart ["b"];
    testPosix "b|a" "bac" mainpart ["b"];
    testPosix ".*b" "bac" mainpart ["b"];
    testPosix ".*b" "bac" postpart ["ac"];
    testPosix "a.*" "bac" prepart ["b"];
    testPosix ".*(b|a).*" "bac" matched ["a"];
    testPosix ".*(b|a).*" "abc" matched ["b"];
    testPosix ".*(bb|ab).*" "abc" matched ["ab"];
    testPosix ".*(bb|ab).*" "abc" matched ["ab"];
    testPosix ".*(bb|ab).*" "abc" matched ["ab"];
    testPosix "(ab%c)" "abc" mainpart ["abc"];
    testPosix "(c%ab)" "abc" mainpart ["abc"];

    testRtoL ".*" "abc" mainpart [""];
    testRtoL "a" "abc" mainpart ["a"];
    testRtoL "a|b" "abc" mainpart ["b"];
    testRtoL "b|a" "abc" mainpart ["b"];
    testRtoL "a|b" "bac" mainpart ["a"];
    testRtoL "b|a" "bac" mainpart ["a"];
    testRtoL ".*b" "bac" mainpart ["b"];
    testRtoL ".*b" "bac" postpart ["ac"];
    testRtoL "a.*" "bac" prepart ["b"];
    testRtoL ".*(b|a).*" "bac" matched ["a", ""];
    testRtoL ".*(b|a).*" "abc" matched ["b", ""];
    testRtoL ".*(bb|ab).*" "abc" matched ["ab", ""];
    testRtoL ".*(bb|ab).*" "abc" matched ["ab", ""];
    testRtoL ".*(bb|ab).*" "abc" matched ["ab", ""];
    testRtoL "(ab%c)" "abc" mainpart ["abc"];
    testRtoL "(c%ab)" "abc" mainpart ["abc"];

    test2Pass ".*" "abc" mainpart ["abc"];
    test2Pass "a" "abc" mainpart ["a"];
    test2Pass "a|b" "abc" mainpart ["a"];
    test2Pass "b|a" "abc" mainpart ["a"];
    test2Pass "a|b" "bac" mainpart ["b"];
    test2Pass "b|a" "bac" mainpart ["b"];
    test2Pass ".*b" "bac" mainpart ["b"];
    test2Pass ".*b" "bac" postpart ["ac"];
    test2Pass "a.*" "bac" prepart ["b"];
    test2Pass ".*(b|a).*" "bac" matched ["a", ""];
    test2Pass ".*(b|a).*" "abc" matched ["b", ""];
    test2Pass ".*(bb|ab).*" "abc" matched ["ab", ""];
    test2Pass ".*(bb|ab).*" "abc" matched ["ab", ""];
    test2Pass ".*(bb|ab).*" "abc" matched ["ab", ""];
    test2Pass "(ab%c)" "abc" mainpart ["abc"];
    test2Pass "(c%ab)" "abc" mainpart ["abc"];
    return ()
}

main :: IO ()
main = runTests
