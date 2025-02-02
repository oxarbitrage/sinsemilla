---- MODULE Invariants ----
(***************************************************************************)
(* Invariants used by the sinsemilla hash algorithm.                       *)
(*                                                                         *)
(* This module contains the invariants used by the sinsemilla hash         *)
(* algorithm.                                                              *)
(***************************************************************************)
EXTENDS TLC, Naturals, Integers, Sequences

\* Type invariants.
IsPoint(point) == point \in [a: Nat, b: Nat]
IsBytes(bytes) == bytes \in Seq(Nat)
IsBits(bits) == bits \in Seq({0, 1})
IsSlices(slices) == slices \in Seq(Seq({0, 1}))
IsNumber(n) == n \in Nat

\* Bytes should eiher be empty or a sequence of integers representing bytes.
BytesSequence(bytes) ==  \A index \in 1..Len(bytes) : bytes[index] \in 0..255
\* Slices should either be empty or a sequence of sequences of bits, each slice should have no length greater than k.
\* We only can have a slice with length < than k when we are building the slices in the "PadLastSlice" label of the
\* pad procedure.
SlicesSequence(slices, k) == \A index \in 1..Len(slices) : slices[index] \in Seq({0, 1}) /\ Len(slices[index]) <= k
\* The number of slices should be less than or equal to the maximum number of chunks allowed.
MaxChunks(n, c) == n <= c
\* Check that the plaintext is not equal to the ciphertext.
PlainIsNotCipherText(plain, cipher) == plain # cipher 

====