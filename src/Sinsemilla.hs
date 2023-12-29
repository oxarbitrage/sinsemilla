{-|
Module      : Sinsemilla
Description : Implementation of the Sinsemilla hash in Haskell using PastaCurves.

This module provides an implementation of the Sinsemilla hash function using the PastaCurves library.

-}
module Sinsemilla
    ( sinsemillaHash
    ) where

import PastaCurves

import qualified Data.ByteString as BS
import Data.Word
import Data.Maybe (fromJust)
import Data.Bits ((.|.), shiftL)

-- | Performs incomplete point addition on two points on the Pallas curve.
incompleteAddition :: Maybe Pallas -> Maybe Pallas -> Maybe Pallas
incompleteAddition left right = case (left, right) of
    (Just l, Just r) -> if l == r || l == negatePt r then Nothing else Just (pointAddAffined l r)
    (_, _) -> Nothing

-- | Converts a byte array and a message to a point on the Pallas curve.
sinsemillaHashToPoint :: [Word8] -> [Bool] -> Maybe Pallas
sinsemillaHashToPoint d m = do
    let k = 10
        c = 253
    if Prelude.length m <= k * c
    then
        let initialAcc = Just (q d)
        in Prelude.foldl
            (\currentAcc chunk ->
                let updatedAcc = 
                        incompleteAddition 
                            (incompleteAddition
                                currentAcc
                                (Just (s (Prelude.take k (chunk ++ repeat False))))
                            )
                            currentAcc
                in updatedAcc
            )
        initialAcc
        (chunksOf k m)
    else
      Nothing

-- The function reverses and converts the hashed point to a byte array.
sinsemillaHash :: [Word8] -> [Bool] -> [Word8]
sinsemillaHash d m = init $ reverse $ BS.unpack $ toBytesC $ fromJust $ sinsemillaHashToPoint d m

-- | Hashes a byte array to a point on the Pallas curve using the SinsemillaQ construction.
q :: [Word8] -> Pallas
q m = hashToPallas "z.cash:SinsemillaQ" (BS.pack m)

-- | Hashes a boolean array to a point on the Pallas curve using the SinsemillaS construction.
--
-- The function pads the boolean array to be a multiple of 8 before hashing.
s :: [Bool] -> Pallas
s j =
    let leosp32j = map fromBoolToWord8 (take 4 (chunksOf 8 (padToMultipleOf8 j))) ++ [0, 0]
    in hashToPallas "z.cash:SinsemillaS" (BS.pack leosp32j)

-- | Converts a boolean array to a Word8 using little-endian ordering.
fromBoolToWord8 :: [Bool] -> Word8
fromBoolToWord8 = foldr (\b acc -> acc `shiftL` 1 .|. fromIntegral (fromEnum b)) 0

-- | Pads a boolean array to be a multiple of 8.
--
-- The function adds zeros to the end of the array to achieve the desired length.
padToMultipleOf8 :: [Bool] -> [Bool]
padToMultipleOf8 bits =
    let len = length bits
        padding = (8 - len `mod` 8) `mod` 8
    in bits ++ replicate padding False

-- | Splits a list into chunks of a specified size.
chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)
