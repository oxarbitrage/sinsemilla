{-|
Test vectors from https://github.com/ZcashFoundation/zebra/blob/main/zebra-chain/src/orchard/tests/vectors/sinsemilla.rs
-}
import TestVectors
import Sinsemilla

main :: IO ()
main = do
    putStrLn "Testing sinsemillaHashToPoint"

    let output1 = sinsemillaHash tv1_domain tv1_msg
    putStrLn $ if output1 == tv1_hash then "OK" else "FAIL!"

    let output2 = sinsemillaHash tv2_domain tv2_msg
    putStrLn $ if output2 == tv2_hash then "OK" else "FAIL!"

    let output3 = sinsemillaHash tv3_domain tv3_msg
    putStrLn $ if output3 == tv3_hash then "OK" else "FAIL!"

    let output4 = sinsemillaHash tv4_domain tv4_msg
    putStrLn $ if output4 == tv4_hash then "OK" else "FAIL!"

    let output5 = sinsemillaHash tv5_domain tv5_msg
    putStrLn $ if output5 == tv5_hash then "OK" else "FAIL!"

    let output6 = sinsemillaHash tv6_domain tv6_msg
    putStrLn $ if output6 == tv6_hash then "OK" else "FAIL!"

    let output7 = sinsemillaHash tv7_domain tv7_msg
    putStrLn $ if output7 == tv7_hash then "OK" else "FAIL!"

    let output8 = sinsemillaHash tv8_domain tv8_msg
    putStrLn $ if output8 == tv8_hash then "OK" else "FAIL!"

    let output9 = sinsemillaHash tv9_domain tv9_msg
    putStrLn $ if output9 == tv9_hash then "OK" else "FAIL!"

    let output10 = sinsemillaHash tv10_domain tv10_msg
    putStrLn $ if output10 == tv10_hash then "OK" else "FAIL!"

    let output11 = sinsemillaHash tv11_domain tv11_msg
    putStrLn $ if output11 == tv11_hash then "OK" else "FAIL!"
