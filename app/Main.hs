module Main (main) where

import Data.Word

import Data.Bits
import Data.Char
import Data.ByteString (ByteString, unpack, pack)
import Data.ByteString.Base64 (encode)

import Sinsemilla

main :: IO ()
main = do
    putStrLn "---Sinsemilla hash function---"
    putStrLn ""

    incoming_domain <- getInput "Insert a domain to be used:"
    incoming_message <- getInput "Insert message to be hashed:"

    let parsed_domain = intToWord8 $ stringToBytes incoming_domain
    let parsed_message = stringToBoolList incoming_message

    let hash = sinsemillaHash parsed_domain parsed_message
    let outcoming_hash = byteStringtoCharList $ encode $ pack hash

    printInfo ["", "B64 encoded ciphertext:", "", outcoming_hash, ""]

    return ()

    where
        getInput prompt = do
            putStrLn prompt
            getLine

        printInfo = mapM_ putStrLn

        stringToBytes :: String -> [Int]
        stringToBytes = map ord

        intToWord8 :: [Int] -> [Word8]
        intToWord8 = map fromIntegral

        stringToBoolList :: String -> [Bool]
        stringToBoolList = concatMap charToBoolList

        charToBoolList :: Char -> [Bool]
        charToBoolList c = map (testBit (ord c)) [7,6..0]

        byteStringtoCharList :: Data.ByteString.ByteString -> [Char]
        byteStringtoCharList = map (toEnum . fromEnum) . Data.ByteString.unpack
