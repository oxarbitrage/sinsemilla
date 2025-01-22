---- MODULE sinsemilla ----
(***************************************************************************)
(* Sinsemilla hash function specification                                  *)
(*                                                                         *)
(* Specifies what is needed to implement a sinsemilla hash function        *)
(* algorithm.                                                              *)
(*                                                                         *)
(***************************************************************************)
EXTENDS TLC, Naturals, Integers, Sequences, Utils, Randomization, Invariants

CONSTANT k, c, SinsemillaQ, SinsemillaS, Domain, Message

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
    \* The incomplete addition operator. Sums the x and y coordinates of two points on the Pallas curve.
    IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b]

    \* Check all type invariants.
    InvType == /\ TypeInvariantPoint(point) 
        /\ TypeInvariantCharacters(characters)
        /\ TypeInvariantBytes(bytes)
        /\ TypeInvariantAuxiliarBytes(bytes)
        /\ TypeInvariantBits(bits)
        /\ TypeInvariantSlices(slices)

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
    Liveness == /\ LivenessPoint
        /\ LivenessAccumulator
        /\ LivenessIndex
        /\ LivenessSlices
        /\ LivenessCipherValue

    \* Check all safety invariants.
    Safety == /\ SafetyBytesSequence(bytes)
        /\ SafetySlicesSequence(slices, k)
        /\ SafetyMaxChunks(n, c)
        /\ SafetyCipherSize(ciphertext)
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
    \* Encode the domain characters as bytes and store them in `auxiliar_bytes` for later use.
    EncodeDomain:
        characters := SetToSeq(Domain);
        characters_to_bytes();
        auxiliar_bytes := bytes;
    \* Encode the message characters as bits and store them in `bits` for later use.
    EncodeMessage:
        characters := SetToSeq(Message);
        characters_to_bytes();
        bytes_to_bits();
    \* With the domain bytes in `bytes` and the message bits in `bits`, call the main procedure to hash the message.
    SinsemillaHashToPoint:
        bytes := auxiliar_bytes;
        call sinsemilla_hash_to_point();
    \* Decode the point coordinates to characters.
    DecodeCipherText:
        point_to_bytes();
        bytes_to_characters();
        ciphertext := characters;
    return;
end procedure;

\* The main procedure convert the message bits into a Pallas point, using the domain bytes stored in `bytes` as the
\* domain separator and the message bits stored in `bits` as the message.
procedure sinsemilla_hash_to_point()
begin
    CallPad:
        \* Calculate the number of slices needed to hash the message.
        n := Max(Len(bits), k) \div k;
        \* Use the `bits` as input and get chunks in a padded `slices`.
        call pad();
    CallQ:
        \* Produce a Pallas point with the `bytes` stored, these bytes are set in the caller as domain bytes.
        call q();
    InitializeAcc:
        \* With the point we got from calling `q`, initialize the accumulator.
        accumulator := point;
    MainLoop:
        \* Loop over the slices.
        while i <= n do
            CallS:
                \* Produce a Pallas point calling `s` given the padded bits (10 bits).
                bits := slices[i];
                call s();
            Accumulate:
                \* Incomplete addition of the accumulator and the point.
                accumulator := 
                    IncompleteAddition(IncompleteAddition(accumulator, point), accumulator);
                \* Increment the index.
                i := i + 1;
        end while;
    AssignAccumulatorToPoint:
        point := accumulator;
    return;
end procedure;

\* Pad the message bits with zeros until the length is a multiple of k. Create chunks of k bits.
procedure pad()
variable paddedBits;
begin
    PadBits:
        \* Pad bits with zeros to make length a multiple of `k`
        paddedBits := bits \o [index \in 1..(k - (Len(bits) % k)) |-> 0];
    CreateChunks:
        \* Divide into chunks of `k` bits
        slices := [index \in 1..(Len(paddedBits) \div k) |->
            SubSeq(paddedBits, (index - 1) * k + 1, index * k)];
    return;
end procedure;

\* Produce a Pallas point with the bytes stored in `bytes`, these bytes are set in the caller as domain bytes.
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
        \* TODO:
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
\* BEGIN TRANSLATION (chksum(pcal) = "3c4c4b3f" /\ chksum(tla) = "a50d805")
CONSTANT defaultInitValue
VARIABLES point, characters, bytes, auxiliar_bytes, bits, slices, n, i, 
          accumulator, ciphertext, pc, stack

(* define statement *)
IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b]


InvType == /\ TypeInvariantPoint(point)
    /\ TypeInvariantCharacters(characters)
    /\ TypeInvariantBytes(bytes)
    /\ TypeInvariantAuxiliarBytes(bytes)
    /\ TypeInvariantBits(bits)
    /\ TypeInvariantSlices(slices)


LivenessPoint == <> (point # [a |-> 0, b |-> 0])

LivenessAccumulator == <> (accumulator # [a |-> 0, b |-> 0])

LivenessIndex == <> (i > 1)

LivenessSlices == <> (Len(slices) > 0)

LivenessCipherValue == <> (ciphertext # <<"@", "@">>)

Liveness == /\ LivenessPoint
    /\ LivenessAccumulator
    /\ LivenessIndex
    /\ LivenessSlices
    /\ LivenessCipherValue


Safety == /\ SafetyBytesSequence(bytes)
    /\ SafetySlicesSequence(slices, k)
    /\ SafetyMaxChunks(n, c)
    /\ SafetyCipherSize(ciphertext)

VARIABLES paddedBits, separator, message_bytes

vars == << point, characters, bytes, auxiliar_bytes, bits, slices, n, i, 
           accumulator, ciphertext, pc, stack, paddedBits, separator, 
           message_bytes >>

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
        (* Procedure pad *)
        /\ paddedBits = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure hash_to_pallas *)
        /\ separator = [ self \in ProcSet |-> defaultInitValue]
        /\ message_bytes = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "SinSemillaHashCall"]

EncodeDomain(self) == /\ pc[self] = "EncodeDomain"
                      /\ characters' = SetToSeq(Domain)
                      /\ bytes' = [char \in 1..Len(characters') |-> Ord(characters'[char])]
                      /\ auxiliar_bytes' = bytes'
                      /\ pc' = [pc EXCEPT ![self] = "EncodeMessage"]
                      /\ UNCHANGED << point, bits, slices, n, i, accumulator, 
                                      ciphertext, stack, paddedBits, separator, 
                                      message_bytes >>

EncodeMessage(self) == /\ pc[self] = "EncodeMessage"
                       /\ characters' = SetToSeq(Message)
                       /\ bytes' = [char \in 1..Len(characters') |-> Ord(characters'[char])]
                       /\ bits' = FlattenSeq([byte \in 1..Len(bytes') |-> ByteToBitSequence(bytes'[byte])])
                       /\ pc' = [pc EXCEPT ![self] = "SinsemillaHashToPoint"]
                       /\ UNCHANGED << point, auxiliar_bytes, slices, n, i, 
                                       accumulator, ciphertext, stack, 
                                       paddedBits, separator, message_bytes >>

SinsemillaHashToPoint(self) == /\ pc[self] = "SinsemillaHashToPoint"
                               /\ bytes' = auxiliar_bytes
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sinsemilla_hash_to_point",
                                                                        pc        |->  "DecodeCipherText" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "CallPad"]
                               /\ UNCHANGED << point, characters, 
                                               auxiliar_bytes, bits, slices, n, 
                                               i, accumulator, ciphertext, 
                                               paddedBits, separator, 
                                               message_bytes >>

DecodeCipherText(self) == /\ pc[self] = "DecodeCipherText"
                          /\ bytes' = <<point.a, point.b>>
                          /\ characters' = [b \in 1..Len(bytes') |-> Chr(bytes'[b])]
                          /\ ciphertext' = characters'
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << point, auxiliar_bytes, bits, slices, 
                                          n, i, accumulator, paddedBits, 
                                          separator, message_bytes >>

sinsemilla_hash(self) == EncodeDomain(self) \/ EncodeMessage(self)
                            \/ SinsemillaHashToPoint(self)
                            \/ DecodeCipherText(self)

CallPad(self) == /\ pc[self] = "CallPad"
                 /\ n' = (Max(Len(bits), k) \div k)
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pad",
                                                          pc        |->  "CallQ",
                                                          paddedBits |->  paddedBits[self] ] >>
                                                      \o stack[self]]
                 /\ paddedBits' = [paddedBits EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "PadBits"]
                 /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                 bits, slices, i, accumulator, ciphertext, 
                                 separator, message_bytes >>

CallQ(self) == /\ pc[self] = "CallQ"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "q",
                                                        pc        |->  "InitializeAcc" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "Q"]
               /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, bits, 
                               slices, n, i, accumulator, ciphertext, 
                               paddedBits, separator, message_bytes >>

InitializeAcc(self) == /\ pc[self] = "InitializeAcc"
                       /\ accumulator' = point
                       /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                       /\ UNCHANGED << point, characters, bytes, 
                                       auxiliar_bytes, bits, slices, n, i, 
                                       ciphertext, stack, paddedBits, 
                                       separator, message_bytes >>

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ IF i <= n
                        THEN /\ pc' = [pc EXCEPT ![self] = "CallS"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "AssignAccumulatorToPoint"]
                  /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                  bits, slices, n, i, accumulator, ciphertext, 
                                  stack, paddedBits, separator, message_bytes >>

CallS(self) == /\ pc[self] = "CallS"
               /\ bits' = slices[i]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "s",
                                                        pc        |->  "Accumulate" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "CallI2LEOSP"]
               /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                               slices, n, i, accumulator, ciphertext, 
                               paddedBits, separator, message_bytes >>

Accumulate(self) == /\ pc[self] = "Accumulate"
                    /\ accumulator' = IncompleteAddition(IncompleteAddition(accumulator, point), accumulator)
                    /\ i' = i + 1
                    /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                    /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                    bits, slices, n, ciphertext, stack, 
                                    paddedBits, separator, message_bytes >>

AssignAccumulatorToPoint(self) == /\ pc[self] = "AssignAccumulatorToPoint"
                                  /\ point' = accumulator
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED << characters, bytes, 
                                                  auxiliar_bytes, bits, slices, 
                                                  n, i, accumulator, 
                                                  ciphertext, paddedBits, 
                                                  separator, message_bytes >>

sinsemilla_hash_to_point(self) == CallPad(self) \/ CallQ(self)
                                     \/ InitializeAcc(self)
                                     \/ MainLoop(self) \/ CallS(self)
                                     \/ Accumulate(self)
                                     \/ AssignAccumulatorToPoint(self)

PadBits(self) == /\ pc[self] = "PadBits"
                 /\ paddedBits' = [paddedBits EXCEPT ![self] = bits \o [index \in 1..(k - (Len(bits) % k)) |-> 0]]
                 /\ pc' = [pc EXCEPT ![self] = "CreateChunks"]
                 /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                 bits, slices, n, i, accumulator, ciphertext, 
                                 stack, separator, message_bytes >>

CreateChunks(self) == /\ pc[self] = "CreateChunks"
                      /\ slices' =       [index \in 1..(Len(paddedBits[self]) \div k) |->
                                   SubSeq(paddedBits[self], (index - 1) * k + 1, index * k)]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ paddedBits' = [paddedBits EXCEPT ![self] = Head(stack[self]).paddedBits]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                      bits, n, i, accumulator, ciphertext, 
                                      separator, message_bytes >>

pad(self) == PadBits(self) \/ CreateChunks(self)

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
                           slices, n, i, accumulator, ciphertext, paddedBits >>

q(self) == Q(self)

CallI2LEOSP(self) == /\ pc[self] = "CallI2LEOSP"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "IntToLEOSP32",
                                                              pc        |->  "S" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "IntToLEOSP"]
                     /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                     bits, slices, n, i, accumulator, 
                                     ciphertext, paddedBits, separator, 
                                     message_bytes >>

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
                           slices, n, i, accumulator, ciphertext, paddedBits >>

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
                                      slices, n, i, accumulator, ciphertext, 
                                      paddedBits >>

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
                                    paddedBits, separator, message_bytes >>

IntToLEOSP32(self) == IntToLEOSP(self)

SinSemillaHashCall == /\ pc["MAIN"] = "SinSemillaHashCall"
                      /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "sinsemilla_hash",
                                                                 pc        |->  "Done" ] >>
                                                             \o stack["MAIN"]]
                      /\ pc' = [pc EXCEPT !["MAIN"] = "EncodeDomain"]
                      /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                      bits, slices, n, i, accumulator, 
                                      ciphertext, paddedBits, separator, 
                                      message_bytes >>

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
