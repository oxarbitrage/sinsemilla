module Main (main) where

import PastaCurves

main :: IO ()
main = do
    let a = 9 :: Fp
    let b =  a*a

    print b
    