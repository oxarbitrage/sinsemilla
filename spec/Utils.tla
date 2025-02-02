-------------------------------- MODULE Utils -------------------------------
(***************************************************************************)
(* Utility functiuons used by the sinsemilla hash algorithm, they          *)
(* represent either functions that can probably be found in programming    *)
(* languages or functions that are specific to the sinsemilla hash         *)
(* algorithm that need to be coded.                                        *)
(***************************************************************************)
EXTENDS CharUtils, Community
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Randomization

\* Convert a byte to a sequence of bits.
ByteToBitSequence(b) ==
    LET
        Bit(i) == IF b \div (2^i) % 2 = 1 THEN 1 ELSE 0
    IN
        << Bit(7), Bit(6), Bit(5), Bit(4), Bit(3), Bit(2), Bit(1), Bit(0) >>

\* Convert a sequence of bits to a byte.
BitSequenceToByte(bits) ==
    LET
        BitValue(pos) == IF bits[pos + 1] = 1 THEN 2^(7-pos) ELSE 0
    IN
        BitValue(0) + BitValue(1) + BitValue(2) + BitValue(3) +
        BitValue(4) + BitValue(5) + BitValue(6) + BitValue(7)

\* Maximum of two numbers.
Max(a, b) == IF a >= b THEN a ELSE b

\* Convert a sequence of characters to a sequence of bytes.
CharactersToBytes(characters) == [char \in 1..Len(characters) |-> Ord(characters[char])]

\* Convert a sequence of bytes to a flat sequence of bits.
BytesToBits(bytes) == FlattenSeq([byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])])

\* Convert a sequence of bytes to a sequence of characters.
BytesToCharacters(bytes) == [b \in 1..Len(bytes) |-> Chr(bytes[b])]

\* Convert a Pallas point to a sequence of fixed bytes. Here we just use the point coordinates as bytes.
PointToBytes(point) == <<point.a, point.b>>

(* Integer to Little-Endian Octet String Pairing.

This procedure assumes k = 10, so we have 8 bits to build the first byte and 2 bits for the second.
The second byte is formed by the first two bits of the second byte of the input and 6 zeros.
We reach the 32 bytes by adding two zero bytes at the end.

This algorithm is the one implemented in Zebra.
*)
IntToLEOSP32(bits) == <<
    BitSequenceToByte(SubSeq(bits, 1, 8)),
    BitSequenceToByte(<<SubSeq(bits, 9, 10)[1], SubSeq(bits, 9, 10)[2], 0, 0, 0, 0, 0, 0>>),
    0,
    0>>

\* The incomplete addition operator. Sums the x and y coordinates of two points on the Pallas curve.
IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b]

\* Pad bits with zeros to make length a multiple of `k`
PadBits(bits, k) == bits \o [index \in 1..(k - (Len(bits) % k)) |-> 0]

\* Divide padded bits into chunks of `k` bits
DivideInChunks(paddedBits, k) == [index \in 1..(Len(paddedBits) \div k) |-> SubSeq(paddedBits, (index - 1) * k + 1, index * k)]

\* Produce a Pallas point with the separator and message bytes stored in separator and message_bytes.
\* Here we decouple the input message and separator from the outputs by choosing random coordinates.
\* From now on, in this model, we can't releate the original message with the ciphertext anymore.
HashToPallas(separator, message_bytes) == [
    a |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE,
    b |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE
]

\* Ceiling division.
CeilDiv(a, b) == IF a % b = 0 THEN a \div b ELSE (a \div b) + 1

=============================================================================
