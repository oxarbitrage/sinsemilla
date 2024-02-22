{-|
Test vectors from https://github.com/ZcashFoundation/zebra/blob/main/zebra-chain/src/orchard/tests/vectors/sinsemilla.rs
-}
import TestVectors
import Sinsemilla

import Data.Word

-- Define a type synonym for test case tuple
type TestCase = ([Word8], [Bool], [Word8])

-- Define test cases
testCases :: [TestCase]
testCases =
    [ (tv1_domain, tv1_msg, tv1_hash)
    , (tv2_domain, tv2_msg, tv2_hash)
    , (tv3_domain, tv3_msg, tv3_hash)
    , (tv4_domain, tv4_msg, tv4_hash)
    , (tv5_domain, tv5_msg, tv5_hash)
    , (tv6_domain, tv6_msg, tv6_hash)
    , (tv7_domain, tv7_msg, tv7_hash)
    , (tv8_domain, tv8_msg, tv8_hash)
    , (tv9_domain, tv9_msg, tv9_hash)
    , (tv10_domain, tv10_msg, tv10_hash)
    , (tv11_domain, tv11_msg, tv11_hash)]

-- Test function
testSinsemillaHashToPoint :: TestCase -> IO ()
testSinsemillaHashToPoint (domain, msg, expectedHash) = do
  let output = sinsemillaHash domain msg
  putStrLn $ if output == expectedHash then "OK" else "FAIL!"

main :: IO ()
main = do
  putStrLn "Testing sinsemillaHashToPoint"
  mapM_ testSinsemillaHashToPoint testCases
