---- MODULE Invariants ----
EXTENDS TLC, Naturals, Integers, Sequences

\* Type invariants.
TypeInvariantPoint(point) == point \in [a: Nat, b: Nat]
TypeInvariantCharacters(characters) == characters \in Seq(STRING)
TypeInvariantBytes(bytes) == bytes \in Seq(Nat)
TypeInvariantAuxiliarBytes(bytes) == bytes \in Seq(Nat)
TypeInvariantBits(bits) == bits \in Seq({0, 1})
TypeInvariantSlices(slices) == slices \in Seq(Seq({0, 1}))

\* Bytes should always be a sequence of integers representing bytes.
SafetyBytesSequence(bytes) ==  /\ bytes = <<>> \/ (\A index \in 1..Len(bytes) : bytes[index] \in 0..255)
\* Slices should always be a sequence of sequences of bits and each slice should have no length greater than k.
\* We only can have a slice with length < than k when we are building the slices in the "PadLastSlice" label of the
\* pad procedure.
SafetySlicesSequence(slices, k) == 
    /\ slices = <<>> \/ (\A index \in 1..Len(slices) : slices[index] \in Seq({0, 1}) /\ Len(slices[index]) <= k)
\* The number of slices should be less than or equal to the maximum number of chunks allowed.
SafetyMaxChunks(n, c) == n <= c
\* Check that the ciphertext has the correct fixed size.
SafetyCipherSize(ciphertext) == Len(ciphertext) = 2

====