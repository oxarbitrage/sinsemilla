{-|
Test vectors from https://github.com/ZcashFoundation/zebra/blob/main/zebra-chain/src/orchard/tests/vectors/sinsemilla.rs
-}
import Sinsemilla
import Data.Word

tv1_domain :: [Word8]
tv1_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61]

tv1_msg :: [Bool]
tv1_msg = [
    False, False, False, True, False, True, True, False, True, False, True, False,
    False, True, True, False, False, False, True, True, False, True, True, False,
    False, False, True, True, False, True, True, False, True, True, True, True, False,
    True, True, False]

tv1_hash :: [Word8]
tv1_hash = [
    0x98, 0x54, 0xaa, 0x38, 0x43, 0x63, 0xb5, 0x70, 0x8e, 0x06, 0xb4, 0x19, 0xb6, 0x43,
    0x58, 0x68, 0x39, 0x65, 0x3f, 0xba, 0x5a, 0x78, 0x2d, 0x2d, 0xb1, 0x4c, 0xed, 0x13,
    0xc1, 0x9a, 0x83, 0x2b]

tv2_domain :: [Word8]
tv2_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61, 0x2d, 0x6c, 0x6f, 0x6e, 0x67, 0x65,
    0x72]

tv2_msg :: [Bool] 
tv2_msg = [
    True, True, False, True, False, False, True, False, True, False, False, False,
    False, True, False, True, False, False, True, False, True, True, True, False,
    False, False, False, True, True, False, False, True, False, True, False, True,
    False, True, True, True, False, False, False, True, False, True, True, True, False,
    True, False, True, False, True, True, True, False, True, True, True, True, True,
    True, True, False, True, False, False, True, True, True, False, True, True, True,
    True, False, False, True, False, True, False, False, False, False, False, True,
    False, True, False, False, True, True, False, True, False, False, False, False,
    True, True, False, True, False, True, False, True, True, False, True, False, False,
    False, True, True, False, False, False, True, True, False, True]

tv2_hash :: [Word8]
tv2_hash = [
    0xed, 0x5b, 0x98, 0x8e, 0x4e, 0x98, 0x17, 0x1f, 0x61, 0x8f, 0xee, 0xb1, 0x23, 0xe5,
    0xcd, 0x0d, 0xc2, 0xd3, 0x67, 0x11, 0xc5, 0x06, 0xd5, 0xbe, 0x11, 0x5c, 0xfe, 0x38,
    0x8f, 0x03, 0xc4, 0x00]

tv3_domain :: [Word8]
tv3_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61]

tv3_msg :: [Bool] 
tv3_msg = [
    True, False, True, True, False, True, False, True, False, True, False, True, True,
    True, True, True, True, True, False, True, False, True, True, False, True, False,
    True, False, True, False, True, False, False, True, False, True, True, False,
    False, False, True, True, False, True, False, False, True, True, True, True, True,
    False, True, True, False, False, True, False, False, False, True, True, False,
    False, False, False, True, False, False, True, True, False, False, True, False,
    False, True, False, True, True, False, True, True, False, False, True, True, True,
    True, True, False, False, False, True, False, False, True, False, False]
            
tv3_hash :: [Word8]
tv3_hash = [
    0xd9, 0x5e, 0xe5, 0x8f, 0xbd, 0xaa, 0x6f, 0x3d, 0xe5, 0xe4, 0xfd, 0x7a, 0xfc, 0x35,
    0xfa, 0x9d, 0xcf, 0xe8, 0x2a, 0xd1, 0x93, 0x06, 0xb0, 0x7e, 0x6c, 0xda, 0x0c, 0x30,
    0xe5, 0x98, 0x34, 0x07]

tv4_domain :: [Word8]
tv4_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61]

tv4_msg :: [Bool]
tv4_msg = [
    False, False, True, True, False, False, False, True, False, False, True, False,
    True, True, True, True, False, False, True, False, True, False, False, False, True,
    True, False, False, True, True, True, True, False, True, False, False, True, False,
    False, True, True, False, False, False, False, True, True, False, False, True,
    False, False, False, True, False, False, True, False, True, True, False, True,
    False, True, False, True, True, True, True, False, False, True, False, False, True,
    True, True, True, True, False, True, True, False, True, True, False, False, True,
    True, True, True, True, True, False, False, False, True, False, True, False, False,
    True, True, False, True, True, True, True, False, False, True, True, False, False,
    True, False, False, True, True, True, False, False, False, False, False, True,
    False, False, False, True, False, True, False, True, True, True, True, False, True,
    False, False, True, False, False, False, False, False, False, True, True, True,
    True, False, True, True, False, False, False, False, True, True, True, False, True,
    True, True, True, True, False, True, True, True, False, True, False, False, True,
    False, False, True, False, False, False, False, True, False, False, False, False,
    True, True, True, False, True, False, True, False, False, False, True, True, False,
    False, True, False, False, False, True, True, False, False]
            
tv4_hash :: [Word8]
tv4_hash = [
    0x6a, 0x92, 0x4b, 0x41, 0x39, 0x84, 0x29, 0x91, 0x0a, 0x78, 0x83, 0x2b, 0x61, 0x19,
    0x2a, 0x0b, 0x67, 0x40, 0xd6, 0x27, 0x77, 0xeb, 0x71, 0x54, 0x50, 0x32, 0xeb, 0x6c,
    0xe9, 0x3e, 0xc9, 0x38]

tv5_domain :: [Word8]
tv5_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61, 0x2d, 0x6c, 0x6f, 0x6e, 0x67, 0x65,
    0x72]

tv5_msg :: [Bool]
tv5_msg = [
    False, True, True, True, True, True, True, True, True, False, False, False, False,
    True, False, True, False, False, True, False, True, False, True, True, True, False,
    True, True, True, False, True, False, True, False, False, True, True, False, False,
    True, False, False, False, False, True, True, True, False, True, False, False,
    False, False, False, False, True, False, False, False, False, False]

tv5_hash :: [Word8]
tv5_hash = [
    0xdc, 0x5f, 0xf0, 0x5b, 0x6f, 0x18, 0xb0, 0x76, 0xb6, 0x12, 0x82, 0x37, 0xa7, 0x59,
    0xed, 0xc7, 0xc8, 0x77, 0x8c, 0x70, 0x22, 0x2c, 0x79, 0xb7, 0x34, 0x03, 0x7b, 0x69,
    0x39, 0x3a, 0xbf, 0x3e]

tv6_domain :: [Word8]
tv6_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61]

tv6_msg :: [Bool]
tv6_msg = [
    True, True, False, False, True, True, False, True, False, False, True, True, False,
    False, True, True, False, True, False, True, True, True, False, True, True, False,
    True, True, False, True, True, True, True, True, True, False, False, False, True,
    False, False, True, True, False, False, False, True, False, False, False, True,
    True, True, False, False, False, False, True, False, False, True, True, True, True,
    True, False, False, False, True, False, False, True, True, True, True, False, True,
    True, True, False, False, False, True, False, False, True, False, False, True,
    True, False, True, False, True, True, True, True, False, True, True, False, False,
    False, True, True, True, True, True, True, False, False, False, True, False, False,
    True, True, True, True, False, False, True, True, False, True, True, True, False,
    True, True, True, True, False, False, True, False, True, True, True, True, False,
    False, False, True, False, True, True, True, False, True, True, False, True, True,
    True, True, True, True, True, True, True, False, True, False, False, True, False,
    True, False, True, False, True, True, False, False, False, True, False, False,
    False, False, True, False, False, False, True, False, False, False, True, True,
    False, False, True, False, True, True, False, True, True, True, False, True, True,
    True, False, False, True, True]
            
tv6_hash :: [Word8]
tv6_hash = [
    0xc7, 0x6c, 0x8d, 0x7c, 0x43, 0x55, 0x04, 0x1b, 0xd7, 0xa7, 0xc9, 0x9b, 0x54, 0x86,
    0x44, 0x19, 0x6f, 0x41, 0x94, 0x56, 0x20, 0x75, 0x37, 0xc2, 0x82, 0x85, 0x8a, 0x9b,
    0x19, 0x2d, 0x07, 0x3b]
        
tv7_domain :: [Word8]
tv7_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61, 0x2d, 0x6c, 0x6f, 0x6e, 0x67, 0x65,
    0x72]

tv7_msg :: [Bool]
tv7_msg = [
    False, False, True, False, False, True, True, False, False, True, True, False,
    True, True, False, True, True, True, True, False, False, False, True, True, False,
    True, True, False, True, False, True, False, True, True, True, True, False, False,
    False, False, False, True, True, True, False, True, False, False, True, True, True,
    False, True, True, False, False, True, True, False, True, True, True, False, False,
    True, False, False, True, True, True, False, False, True, False, False, False,
    True, False, False, True, False, True, True, False, True, True, True, True, True,
    False, True, True, False, False, False, False, False, False, False, False]
    
tv7_hash :: [Word8]
tv7_hash = [
    0x1a, 0xe8, 0x25, 0xeb, 0x42, 0xd7, 0x4e, 0x1b, 0xca, 0x7e, 0xe8, 0xa1, 0xf8, 0xf3,
    0xde, 0xd8, 0x01, 0xff, 0xcd, 0x1f, 0x22, 0xba, 0x75, 0xc3, 0x4b, 0xd6, 0xe0, 0x6a,
    0x2c, 0x7c, 0x5a, 0x20]

tv8_domain :: [Word8]
tv8_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61, 0x2d, 0x6c, 0x6f, 0x6e, 0x67, 0x65,
    0x72]

tv8_msg :: [Bool]
tv8_msg = [
    True, True, False, True, True, True, False, False, True, False, False, False, True,
    True, False, False, True, True, True, False, False, True, False, True, True, True,
    True, False, True, True, True, False, False, True, True, False, True, True, True,
    True, True, False, True, True, True, True, True, False, True, True, False, True,
    True, True, False, True, False, True, False, False, True, False, True, True, True,
    True, True, False, True, True, False, True, True, False, False, False, True, False,
    True, True, False, False, False, True, False, False, False, False, True, False,
    False, True, False, False, False, False, True, False, False, False, False, False,
    True, True, True, False, False, False, True, True, False, False, False, False,
    True, False, False, True, True, True, False, True, False, False, True, True, False,
    False, False, True, False, False, True, False, False, False, False, False, True,
    False, False, True, True, True, False, False, True, False, False, False, True,
    False, False, False, True, False, False, False, False, True, False, True, False,
    True, False, False, False, False, True, True, False, False, False, True, True,
    True, True]
            
tv8_hash :: [Word8]
tv8_hash = [
    0x38, 0xcf, 0xa6, 0x00, 0xaf, 0xd8, 0x67, 0x0e, 0x1f, 0x9a, 0x79, 0xcb, 0x22, 0x42,
    0x5f, 0xa9, 0x50, 0xcc, 0x4d, 0x3a, 0x3f, 0x5a, 0xfe, 0x39, 0x76, 0xd7, 0x1b, 0xb1,
    0x11, 0x46, 0x0c, 0x2b]

tv9_domain :: [Word8]
tv9_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61]

tv9_msg :: [Bool]
tv9_msg = [
    False, False, True, False, True, False, True, False, False, True, True, False,
    True, True, True, True, True, False, False, True, True, False, True, False, True,
    True, True, False, False, False, False, True, False, False, True, True, False,
    False, False, False, True, True, True, True, True, True, True, True, False, False,
    True, False, True, False, False, False, False, True, False, True, True, True, True,
    True, True, False, True, True, True, True, False, True, False, True, False, False,
    False]

tv9_hash :: [Word8]
tv9_hash = [
    0x82, 0x6f, 0xcb, 0xed, 0xfc, 0x83, 0xb9, 0xfa, 0xa5, 0x71, 0x1a, 0xab, 0x59, 0xbf,
    0xc9, 0x1b, 0xd4, 0x45, 0x58, 0x14, 0x67, 0x72, 0x5d, 0xde, 0x94, 0x1d, 0x58, 0xe6,
    0x26, 0x56, 0x66, 0x15]

tv10_domain :: [Word8]
tv10_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61]

tv10_msg :: [Bool]
tv10_msg = [
    True, True, True, False, True, False, True, False, True, True, True, True, False,
    True, False, True, False, True, False, True, False, True, False, True, True, True,
    False, False, True, False, False, True, False, False, True, True, False, True,
    False, False, False, True, False, True, True, False, True, False, False, False,
    False, False, False, True, True, True, True, False, False, True, True, True, False,
    False, True, False, True, False, True, False, False, False, False, False, False,
    False, False, False, True, False, True, True, False, True, False, True, True, True,
    False, False, True, True, False, True, False, False, False, True, True, True,
    False, False, True, True, False, False, True, False, True, False, False, False,
    True, True, False]

tv10_hash :: [Word8]
tv10_hash = [
    0x0b, 0xf0, 0x6c, 0xe8, 0x10, 0x05, 0xb8, 0x1a, 0x14, 0x80, 0x9f, 0xa6, 0xeb, 0xcb,
    0x94, 0xe2, 0xb6, 0x37, 0x5f, 0x87, 0xce, 0x51, 0x95, 0x8c, 0x94, 0x98, 0xed, 0x1a,
    0x31, 0x3c, 0x6a, 0x14]

tv11_domain :: [Word8]
tv11_domain = [
    0x7a, 0x2e, 0x63, 0x61, 0x73, 0x68, 0x3a, 0x74, 0x65, 0x73, 0x74, 0x2d, 0x53, 0x69,
    0x6e, 0x73, 0x65, 0x6d, 0x69, 0x6c, 0x6c, 0x61]

tv11_msg :: [Bool]
tv11_msg = [
    True, False, True, True, True, False, True, False]

tv11_hash :: [Word8]
tv11_hash = [
    0x80, 0x6a, 0xcc, 0x24, 0x7a, 0xc9, 0xba, 0x90, 0xd2, 0x5f, 0x58, 0x3d, 0xad, 0xb5,
    0xe0, 0xee, 0x5c, 0x03, 0xe1, 0xab, 0x35, 0x70, 0xb3, 0x62, 0xb4, 0xbe, 0x5a, 0x8b,
    0xce, 0xb6, 0x0b, 0x00]

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
