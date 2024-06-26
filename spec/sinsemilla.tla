---- MODULE sinsemilla ----
(***************************************************************************)
(* Sinsemilla hash function specification                                  *)
(*                                                                         *)
(* Specifies what is needed to implement a sinsemilla hash function        *)
(* algorithm.                                                              *)
(*                                                                         *)
(***************************************************************************)
EXTENDS TLC, Naturals, Integers, Sequences, Utils, Randomization

(*--algorithm sinsemilla

variables
    \* Holder for a point on the Pallas curve.
    point = [a |-> 0, b |-> 0];
    \* Holder for a sequence of characters.
    characters = <<>>;
    \* Holder for a sequence of bytes.
    bytes = <<>>;
    \* Holder for a sequence of bytes when the bytes variable is already busy.
    auxiliar_bytes = <<>>;
    \* Holder for a sequence of bits.
    bits = <<>>;
    \* Holder for a sequence of slices.
    slices = <<>>;
    \* Holder for a number, in particular the number of slices.
    n = 0;
    \* Holder for a number used as the current slice index in the main loop.
    i = 1;
    \* Holder for a point used as an accumulator.
    accumulator = [a |-> 0, b |-> 0];
    \* Holder for the ciphertext produced by the hash function.
    ciphertext = <<"@", "@">>;
define
    \* The number of bits in a chunk.
    k == 10
    \* The maximum number of chunks allowed.
    c == 253
    \* The domain separator string for the Q point: "z.cash.SinsemillaQ".
    SinsemillaQ == 
        << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "Q" >>
    \* The domain separator string for the S point: "z.cash.SinsemillaS".
    SinsemillaS == 
        << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "S" >>
    \* A fixed domain to be used to hash the message.
    Domain == <<"t", "e", "s", "t", " ", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a">>
    \* A fixed message to be hashed.
    Message == <<"m", "e", "s", "s", "a", "g", "e">>

    \* The incomplete addition operator. Sums the x and y coordinates of two points on the Pallas curve.
    IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b]

    \* Type invariants.
    TypeInvariantPoint == point \in [a: Nat, b: Nat]
    TypeInvariantCharacters == characters \in Seq(STRING)
    TypeInvariantBytes == bytes \in Seq(Nat)
    TypeInvariantAuxiliarBytes == bytes \in Seq(Nat)
    TypeInvariantBits == bits \in Seq({0, 1})
    TypeInvariantSlices == slices \in Seq(Seq({0, 1}))
    \* Check all type invariants.
    InvType == TypeInvariantPoint /\ TypeInvariantCharacters /\ TypeInvariantBytes
        /\ TypeInvariantBytes /\ TypeInvariantBits /\ TypeInvariantSlices

    \* Point holder will eventually end up with a point different than the starting one.
    LivenessPoint == <> (point # [a |-> 0, b |-> 0])
    \* Accumulator accumulates.
    LivenessAccumulator == <> (accumulator # [a |-> 0, b |-> 0])
    \* Index should always be incremented.
    LivenessIndex == <> (i > 1)
    \* Slices should always be produced.
    LivenessSlices == <> (Len(slices) > 0)
    \* Ciphertext should be produced.
    LivenessCipherValue == <> (ciphertext # <<"@", "@">>)
    \* Check all liveness properties.
    Liveness == LivenessPoint /\ LivenessAccumulator /\ LivenessIndex /\ LivenessSlices /\ LivenessCipherValue

    \* Bytes should always be a sequence of integers representing bytes.
    SafetyBytesSequence ==  /\ bytes = <<>> \/ (\A index \in 1..Len(bytes) : bytes[index] \in 0..255)
    \* Slices should always be a sequence of sequences of bits and each slice should have no length greater than k.
    \* We only can have a slice with length < than k when we are building the slices in the "PadLastSlice" label of the
    \* pad procedure.
    SafetySlicesSequence == 
        /\ slices = <<>> \/ (\A index \in 1..Len(slices) : slices[index] \in Seq({0, 1}) /\ Len(slices[index]) <= k)
    \* The number of slices should be less than or equal to the maximum number of chunks allowed.
    SafetyMaxChunks == n <= c
    \* Check that the ciphertext has the correct fixed size.
    SafetyCipherSize == Len(ciphertext) = 2
    \* Check all safety properties.
    Safety == SafetyBytesSequence /\ SafetySlicesSequence /\ SafetyMaxChunks /\ SafetyCipherSize
end define;

\* Convert a sequence of characters to a sequence of bytes.
macro characters_to_bytes() 
begin
    bytes := [char \in 1..Len(characters) |-> Ord(characters[char])];
end macro;

\* Convert a sequence of bytes to a flat sequence of bits.
macro bytes_to_bits() 
begin
    bits := FlattenSeq([byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])]);
end macro;

\* Convert a sequence of bytes to a sequence of characters.
macro bytes_to_characters() 
begin
    characters := [b \in 1..Len(bytes) |-> Chr(bytes[b])];
end macro;

\* Convert a Pallas point to a sequence of fixed bytes. Here we just use the point coordinates as bytes.
macro point_to_bytes()
begin
    bytes := <<point.a, point.b>>;
end macro;

\* The starting procedure that do all the conversion needed with the domain and message constants,
\* call the main procedure to hash the message and decodes the resulting point coordinates to characters.
procedure sinsemilla_hash()
begin
    \* Encode the domain characters as bytes and store them in auxiliar_bytes for later use.
    EncodeDomain:
        characters := Domain;
        characters_to_bytes();
        auxiliar_bytes := bytes;
    \* Encode the message characters as bits and store them in bits for later use.
    EncodeMessage:
        characters := Message;
        characters_to_bytes();
        bytes_to_bits();
    \* With the domain bytes in bytes and the message bits in bits, call the main procedure to hash the message.
    SinsemillaHashToPoint:
        bytes := auxiliar_bytes;
        call sinsemilla_hash_to_point();
    \* Decode the point coordinates to characters.
    DecodeCipherText:
        point_to_bytes();
        bytes_to_characters();
    Ciphertext:
        ciphertext := characters;
        return;
end procedure;

\* the main procedure convert the message bits into a Pallas point, using the domain bytes stored in bytes as the
\* domain separator and the message bits stored in bits as the message.
procedure sinsemilla_hash_to_point()
begin
    CalculateN:
        \* Calculate the number of slices needed to hash the message.
        n := Len(bits) \div k;
    CallPad:
        \* Use the global bits as input and get slices in slices.
        call pad();
    CallQ:
        \* Produce a Pallas point with the bytes stored, these bytes are set in the caller as domain bytes.
        call q();
    InitializeAcc:
        \* With the point we got from calling q, initialize the accumulator. 
        accumulator := point;
    MainLoop:
        \* Loop over the slices.
        while i <= n do
            CallS:
                \* Produce a Pallas point calling s given the padded bits (10 bits).
                bits := slices[i];
                call s();
            Accumulate:
                \* Incomplete addition of the accumulator and the point.
                accumulator := 
                    IncompleteAddition(IncompleteAddition(accumulator, point), accumulator);
            IncrementIndex:
                i := i + 1;
        end while;
    AssignAccumulatorToPoint:
        point := accumulator;
    return;
end procedure;

\* Pad the message bits with zeros until the length is a multiple of k. Create chunks of k bits.
procedure pad()
begin
    GetSlices:
        slices := [index \in 1..n |-> IF (index * k + k) >= Len(bits) THEN 
            SubSeq(bits, index * k, Len(bits)) 
        ELSE SubSeq(bits, index * k, index * k + k - 1)];
    PadLastSlice:
        slices[Len(slices)] := [index \in 1..k |-> IF index <= Len(slices[Len(slices)]) THEN 
            slices[Len(slices)][index] 
        ELSE 0];
    return;
end procedure;

\* Produce a Pallas point with the bytes stored in bytes, these bytes are set in the caller as domain bytes.
procedure q()
begin
    Q:
        call hash_to_pallas(SinsemillaQ, bytes);
    return;
end procedure;

\* Produce a Pallas point given the padded bits (10 bits). First we call IntToLEOSP on the bits and
\* then we call hash_to_pallas with the result.
procedure s()
begin
    CallI2LEOSP:
        call IntToLEOSP32();
    S:
        call hash_to_pallas(SinsemillaS, bytes);
    return;
end procedure;

\* Produce a Pallas point with the separator and message bytes stored in separator and message_bytes.
procedure hash_to_pallas(separator, message_bytes)
begin
    HashToPallas:
        \* Here we decouple the input message and separator from the outputs by choosing random coordinates.
        \* From now on, in this model, we can't releate the original message with the ciphertext anymore. 
        point := [
            a |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE,
            b |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE
        ];
    return;
end procedure;

(* Integer to Little-Endian Octet String Pairing.

This procedure assumes k = 10, so we have 8 bits to build the first byte and 2 bits for the second.
The second byte is formed by the first two bits of the second byte of the input and 6 zeros.
We reach the 32 bytes by adding two zero bytes at the end.

This algorithm is the one implemented in Zebra.
*)
procedure IntToLEOSP32()
begin
    IntToLEOSP:
        bytes := <<
            BitSequenceToByte(SubSeq(bits, 1, 8)),
            BitSequenceToByte(<<SubSeq(bits, 9, 10)[1], SubSeq(bits, 9, 10)[2], 0, 0, 0, 0, 0, 0>>),
            0,
            0
        >>;
    return;
end procedure;

\* Single process that calls the starting procedure.
fair process main = "MAIN"
begin
    SinSemillaHashCall:
        call sinsemilla_hash();
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e42dec70" /\ chksum(tla) = "77d018cd")
CONSTANT defaultInitValue
VARIABLES point, characters, bytes, auxiliar_bytes, bits, slices, n, i, 
          accumulator, ciphertext, pc, stack

(* define statement *)
k == 10

c == 253

SinsemillaQ ==
    << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "Q" >>

SinsemillaS ==
    << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "S" >>

Domain == <<"t", "e", "s", "t", " ", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a">>

Message == <<"m", "e", "s", "s", "a", "g", "e">>


IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b]


TypeInvariantPoint == point \in [a: Nat, b: Nat]
TypeInvariantCharacters == characters \in Seq(STRING)
TypeInvariantBytes == bytes \in Seq(Nat)
TypeInvariantAuxiliarBytes == bytes \in Seq(Nat)
TypeInvariantBits == bits \in Seq({0, 1})
TypeInvariantSlices == slices \in Seq(Seq({0, 1}))

InvType == TypeInvariantPoint /\ TypeInvariantCharacters /\ TypeInvariantBytes
    /\ TypeInvariantBytes /\ TypeInvariantBits /\ TypeInvariantSlices


LivenessPoint == <> (point # [a |-> 0, b |-> 0])

LivenessAccumulator == <> (accumulator # [a |-> 0, b |-> 0])

LivenessIndex == <> (i > 1)

LivenessSlices == <> (Len(slices) > 0)

LivenessCipherValue == <> (ciphertext # <<"@", "@">>)

Liveness == LivenessPoint /\ LivenessAccumulator /\ LivenessIndex /\ LivenessSlices /\ LivenessCipherValue


SafetyBytesSequence ==  /\ bytes = <<>> \/ (\A index \in 1..Len(bytes) : bytes[index] \in 0..255)



SafetySlicesSequence ==
    /\ slices = <<>> \/ (\A index \in 1..Len(slices) : slices[index] \in Seq({0, 1}) /\ Len(slices[index]) <= k)

SafetyMaxChunks == n <= c

SafetyCipherSize == Len(ciphertext) = 2

Safety == SafetyBytesSequence /\ SafetySlicesSequence /\ SafetyMaxChunks /\ SafetyCipherSize

VARIABLES separator, message_bytes

vars == << point, characters, bytes, auxiliar_bytes, bits, slices, n, i, 
           accumulator, ciphertext, pc, stack, separator, message_bytes >>

ProcSet == {"MAIN"}

Init == (* Global variables *)
        /\ point = [a |-> 0, b |-> 0]
        /\ characters = <<>>
        /\ bytes = <<>>
        /\ auxiliar_bytes = <<>>
        /\ bits = <<>>
        /\ slices = <<>>
        /\ n = 0
        /\ i = 1
        /\ accumulator = [a |-> 0, b |-> 0]
        /\ ciphertext = <<"@", "@">>
        (* Procedure hash_to_pallas *)
        /\ separator = [ self \in ProcSet |-> defaultInitValue]
        /\ message_bytes = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "SinSemillaHashCall"]

EncodeDomain(self) == /\ pc[self] = "EncodeDomain"
                      /\ characters' = Domain
                      /\ bytes' = [char \in 1..Len(characters') |-> Ord(characters'[char])]
                      /\ auxiliar_bytes' = bytes'
                      /\ pc' = [pc EXCEPT ![self] = "EncodeMessage"]
                      /\ UNCHANGED << point, bits, slices, n, i, accumulator, 
                                      ciphertext, stack, separator, 
                                      message_bytes >>

EncodeMessage(self) == /\ pc[self] = "EncodeMessage"
                       /\ characters' = Message
                       /\ bytes' = [char \in 1..Len(characters') |-> Ord(characters'[char])]
                       /\ bits' = FlattenSeq([byte \in 1..Len(bytes') |-> ByteToBitSequence(bytes'[byte])])
                       /\ pc' = [pc EXCEPT ![self] = "SinsemillaHashToPoint"]
                       /\ UNCHANGED << point, auxiliar_bytes, slices, n, i, 
                                       accumulator, ciphertext, stack, 
                                       separator, message_bytes >>

SinsemillaHashToPoint(self) == /\ pc[self] = "SinsemillaHashToPoint"
                               /\ bytes' = auxiliar_bytes
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sinsemilla_hash_to_point",
                                                                        pc        |->  "DecodeCipherText" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "CalculateN"]
                               /\ UNCHANGED << point, characters, 
                                               auxiliar_bytes, bits, slices, n, 
                                               i, accumulator, ciphertext, 
                                               separator, message_bytes >>

DecodeCipherText(self) == /\ pc[self] = "DecodeCipherText"
                          /\ bytes' = <<point.a, point.b>>
                          /\ characters' = [b \in 1..Len(bytes') |-> Chr(bytes'[b])]
                          /\ pc' = [pc EXCEPT ![self] = "Ciphertext"]
                          /\ UNCHANGED << point, auxiliar_bytes, bits, slices, 
                                          n, i, accumulator, ciphertext, stack, 
                                          separator, message_bytes >>

Ciphertext(self) == /\ pc[self] = "Ciphertext"
                    /\ ciphertext' = characters
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                    bits, slices, n, i, accumulator, separator, 
                                    message_bytes >>

sinsemilla_hash(self) == EncodeDomain(self) \/ EncodeMessage(self)
                            \/ SinsemillaHashToPoint(self)
                            \/ DecodeCipherText(self) \/ Ciphertext(self)

CalculateN(self) == /\ pc[self] = "CalculateN"
                    /\ n' = (Len(bits) \div k)
                    /\ pc' = [pc EXCEPT ![self] = "CallPad"]
                    /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                    bits, slices, i, accumulator, ciphertext, 
                                    stack, separator, message_bytes >>

CallPad(self) == /\ pc[self] = "CallPad"
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pad",
                                                          pc        |->  "CallQ" ] >>
                                                      \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "GetSlices"]
                 /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                 bits, slices, n, i, accumulator, ciphertext, 
                                 separator, message_bytes >>

CallQ(self) == /\ pc[self] = "CallQ"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "q",
                                                        pc        |->  "InitializeAcc" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "Q"]
               /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, bits, 
                               slices, n, i, accumulator, ciphertext, 
                               separator, message_bytes >>

InitializeAcc(self) == /\ pc[self] = "InitializeAcc"
                       /\ accumulator' = point
                       /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                       /\ UNCHANGED << point, characters, bytes, 
                                       auxiliar_bytes, bits, slices, n, i, 
                                       ciphertext, stack, separator, 
                                       message_bytes >>

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ IF i <= n
                        THEN /\ pc' = [pc EXCEPT ![self] = "CallS"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "AssignAccumulatorToPoint"]
                  /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                  bits, slices, n, i, accumulator, ciphertext, 
                                  stack, separator, message_bytes >>

CallS(self) == /\ pc[self] = "CallS"
               /\ bits' = slices[i]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "s",
                                                        pc        |->  "Accumulate" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "CallI2LEOSP"]
               /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                               slices, n, i, accumulator, ciphertext, 
                               separator, message_bytes >>

Accumulate(self) == /\ pc[self] = "Accumulate"
                    /\ accumulator' = IncompleteAddition(IncompleteAddition(accumulator, point), accumulator)
                    /\ pc' = [pc EXCEPT ![self] = "IncrementIndex"]
                    /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                    bits, slices, n, i, ciphertext, stack, 
                                    separator, message_bytes >>

IncrementIndex(self) == /\ pc[self] = "IncrementIndex"
                        /\ i' = i + 1
                        /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                        /\ UNCHANGED << point, characters, bytes, 
                                        auxiliar_bytes, bits, slices, n, 
                                        accumulator, ciphertext, stack, 
                                        separator, message_bytes >>

AssignAccumulatorToPoint(self) == /\ pc[self] = "AssignAccumulatorToPoint"
                                  /\ point' = accumulator
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED << characters, bytes, 
                                                  auxiliar_bytes, bits, slices, 
                                                  n, i, accumulator, 
                                                  ciphertext, separator, 
                                                  message_bytes >>

sinsemilla_hash_to_point(self) == CalculateN(self) \/ CallPad(self)
                                     \/ CallQ(self) \/ InitializeAcc(self)
                                     \/ MainLoop(self) \/ CallS(self)
                                     \/ Accumulate(self)
                                     \/ IncrementIndex(self)
                                     \/ AssignAccumulatorToPoint(self)

GetSlices(self) == /\ pc[self] = "GetSlices"
                   /\ slices' =           [index \in 1..n |-> IF (index * k + k) >= Len(bits) THEN
                                    SubSeq(bits, index * k, Len(bits))
                                ELSE SubSeq(bits, index * k, index * k + k - 1)]
                   /\ pc' = [pc EXCEPT ![self] = "PadLastSlice"]
                   /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                   bits, n, i, accumulator, ciphertext, stack, 
                                   separator, message_bytes >>

PadLastSlice(self) == /\ pc[self] = "PadLastSlice"
                      /\ slices' = [slices EXCEPT ![Len(slices)] =                        [index \in 1..k |-> IF index <= Len(slices[Len(slices)]) THEN
                                                                       slices[Len(slices)][index]
                                                                   ELSE 0]]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                      bits, n, i, accumulator, ciphertext, 
                                      separator, message_bytes >>

pad(self) == GetSlices(self) \/ PadLastSlice(self)

Q(self) == /\ pc[self] = "Q"
           /\ /\ message_bytes' = [message_bytes EXCEPT ![self] = bytes]
              /\ separator' = [separator EXCEPT ![self] = SinsemillaQ]
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "hash_to_pallas",
                                                       pc        |->  Head(stack[self]).pc,
                                                       separator |->  separator[self],
                                                       message_bytes |->  message_bytes[self] ] >>
                                                   \o Tail(stack[self])]
           /\ pc' = [pc EXCEPT ![self] = "HashToPallas"]
           /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, bits, 
                           slices, n, i, accumulator, ciphertext >>

q(self) == Q(self)

CallI2LEOSP(self) == /\ pc[self] = "CallI2LEOSP"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "IntToLEOSP32",
                                                              pc        |->  "S" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "IntToLEOSP"]
                     /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                     bits, slices, n, i, accumulator, 
                                     ciphertext, separator, message_bytes >>

S(self) == /\ pc[self] = "S"
           /\ /\ message_bytes' = [message_bytes EXCEPT ![self] = bytes]
              /\ separator' = [separator EXCEPT ![self] = SinsemillaS]
              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "hash_to_pallas",
                                                       pc        |->  Head(stack[self]).pc,
                                                       separator |->  separator[self],
                                                       message_bytes |->  message_bytes[self] ] >>
                                                   \o Tail(stack[self])]
           /\ pc' = [pc EXCEPT ![self] = "HashToPallas"]
           /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, bits, 
                           slices, n, i, accumulator, ciphertext >>

s(self) == CallI2LEOSP(self) \/ S(self)

HashToPallas(self) == /\ pc[self] = "HashToPallas"
                      /\ point' =          [
                                      a |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE,
                                      b |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE
                                  ]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ separator' = [separator EXCEPT ![self] = Head(stack[self]).separator]
                      /\ message_bytes' = [message_bytes EXCEPT ![self] = Head(stack[self]).message_bytes]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << characters, bytes, auxiliar_bytes, bits, 
                                      slices, n, i, accumulator, ciphertext >>

hash_to_pallas(self) == HashToPallas(self)

IntToLEOSP(self) == /\ pc[self] = "IntToLEOSP"
                    /\ bytes' =          <<
                                    BitSequenceToByte(SubSeq(bits, 1, 8)),
                                    BitSequenceToByte(<<SubSeq(bits, 9, 10)[1], SubSeq(bits, 9, 10)[2], 0, 0, 0, 0, 0, 0>>),
                                    0,
                                    0
                                >>
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << point, characters, auxiliar_bytes, bits, 
                                    slices, n, i, accumulator, ciphertext, 
                                    separator, message_bytes >>

IntToLEOSP32(self) == IntToLEOSP(self)

SinSemillaHashCall == /\ pc["MAIN"] = "SinSemillaHashCall"
                      /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "sinsemilla_hash",
                                                                 pc        |->  "Done" ] >>
                                                             \o stack["MAIN"]]
                      /\ pc' = [pc EXCEPT !["MAIN"] = "EncodeDomain"]
                      /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                      bits, slices, n, i, accumulator, 
                                      ciphertext, separator, message_bytes >>

main == SinSemillaHashCall

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet:  \/ sinsemilla_hash(self)
                                     \/ sinsemilla_hash_to_point(self)
                                     \/ pad(self) \/ q(self) \/ s(self)
                                     \/ hash_to_pallas(self) \/ IntToLEOSP32(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(main)
           /\ WF_vars(sinsemilla_hash("MAIN"))
           /\ WF_vars(sinsemilla_hash_to_point("MAIN"))
           /\ WF_vars(pad("MAIN"))
           /\ WF_vars(q("MAIN"))
           /\ WF_vars(s("MAIN"))
           /\ WF_vars(hash_to_pallas("MAIN"))
           /\ WF_vars(IntToLEOSP32("MAIN"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
