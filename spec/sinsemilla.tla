---- MODULE sinsemilla ----
EXTENDS TLC, Naturals, Integers, Sequences, Utils, Randomization

(*--algorithm sinsemilla

\* GLOBAL VARIABLES

variables
    \* Store any point on the Pallas curve at any program state. A point is a structure with coordinates `a` and `b`.
    point = [a |-> 0, b |-> 0];
    \* Store any sequence of characters at any program state.
    characters = <<>>;
    \* Store any sequence of bytes at any program state.
    bytes = <<>>;
    \* Store any sequence of bytes at any program state where the `bytes` are already busy.
    auxiliar_bytes = <<>>;
    \* Store any sequence of bits at any program state.
    bits = <<>>;
    \* Store any sequence of slices at any program state.
    slices = <<>>;

define
    \* CONSTANTS:

    \* The number of bits in a chunk
    k == 10
    \* The domain separator string for the Q point: `z.cash.SinsemillaQ`
    SinsemillaQ == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "Q" >>
    \* The domain separator string for the S point: `z.cash.SinsemillaS`
    SinsemillaS == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "S" >>

    \* OPERATORS:

    \* The incomplete addition operator. Sums the x and y coordinates of two points on the Pallas curve.
    \* TODO: Consider x and y cases here?
    IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b]

    \* TYPE INVARIANTS:

    TypeInvariantPoint == point \in [a: Nat, b: Nat]
    TypeInvariantCharacters == characters \in Seq(STRING)
    TypeInvariantBytes == bytes \in Seq(Nat)
    TypeInvariantAuxiliarBytes == bytes \in Seq(Nat)
    TypeInvariantBits == bits \in Seq({0, 1})
    TypeInvariantSlices == slices \in Seq(Seq({0, 1}))

    InvType == TypeInvariantPoint /\ TypeInvariantCharacters /\ TypeInvariantBytes /\ TypeInvariantBytes /\ 
        TypeInvariantBits /\ TypeInvariantSlices

    \* PROPERTIES:

    \* Liveness property stating that `sinsemilla_hash` will eventually end up with a point different than the 
    \* starting one.
    Liveness == <> (point # [a |-> 0, b |-> 0])

    \* SAFETY PROPERTIES:

    \* Bytes should always be a sequence of integers representing bytes.
    SafetyBytesSequence ==  /\ bytes = <<>> \/ (\A i \in 1..Len(bytes) : bytes[i] \in 0..255)

    \* Slices should always be a sequence of sequences of bits (0 or 1) and each slice should have no length greater than k.
    \* We only can have a slice with length less than k when we are building the slices in the `PadLastSlice` label of the `pad` procedure.
    SafetySlicesSequence == /\ slices = <<>> \/ (\A i \in 1..Len(slices) : slices[i] \in Seq({0, 1}) /\ Len(slices[i]) <= k)

    Safety == SafetyBytesSequence /\ SafetySlicesSequence
end define;

\* MACROS:

\* Convert a sequence of characters to a sequence of bytes.
macro characters_to_bytes() begin
    bytes := [c \in 1..Len(characters) |-> Ord(characters[c])];
end macro;

\* Convert a sequence of bytes to a flat sequence of bits.
macro bytes_to_bits() begin
    bits := FlattenSeq([byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])]);
end macro;

\* Convert a sequence of bytes to a a sequence of characters.
macro bytes_to_characters() begin
    characters := [b \in 1..Len(bytes) |-> Chr(bytes[b])];
end macro;

\* Convert a Pallas point to a sequence of fixed bytes. Here we just use the point coordinates as bytes.
macro point_to_bytes() begin
    bytes := <<point.a, point.b>>;
end macro;

\* PROCEDURES:

\* The main procedure that hashes a message using the Sinsemilla hash function.
procedure sinsemilla_hash(domain, message)
begin
    \* Encode the domain characters as bytes and store them in `domain_bytes` for later use.
    EncodeDomain:
        characters := domain;
        characters_to_bytes();
        auxiliar_bytes := bytes;
    \* Encode the message characters as bits and store them in `bits` for later use.
    EncodeMessage:
        characters := message;
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
    Return:
        print characters;
    return;
end procedure;

\* Convert the message bits into a Pallas point, using the domain bytes stored in `bytes` as the domain separator
\* and the message bits stored in `bits` as the message.
procedure sinsemilla_hash_to_point()
variables
    \* The number of chunks in the message.
    n = Len(bits) \div k,
    \* The accumulator point.
    accumulator,
    \* The index of the current slice to be used in the main loop.
    i = 1;
begin
    CallPad:
        \* Use the global `bits` as input and get slices in `slices`.
        call pad(n);
    CallQ:
        \* Produce a Pallas point with the bytes stored, these bytes are set in the caller as domain bytes.
        call q();
    InitializeAcc:
        \* With the point we got from calling `q`, initialize the accumulator. 
        accumulator := point;
    MainLoop:
        \* Loop through the slices.
        while i <= n do
            CallS:
                \* Produce a Pallas point calling `s` given the padded bits (10 bits).
                bits := slices[i];
                call s();
            Accumulate:
                \* Incomplete addition of the accumulator and the point.
                accumulator := IncompleteAddition(IncompleteAddition(accumulator, point), accumulator);
            IncrementIndex:
                i := i + 1;
        end while;
    AssignAccumulatorToPoint:
        point := accumulator;
    return;
end procedure;

\* Pad the message bits with zeros until the length is a multiple of k. Create chunks of k bits.
procedure pad(n)
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

\* Produce a Pallas point with the bytes stored in `bytes`, these bytes are set in the caller as domain bytes.
procedure q()
begin
    Q:
        call hash_to_pallas(SinsemillaQ, bytes);
    return;
end procedure;

\* Produce a Pallas point given the padded bits (10 bits). First we call `IntToLEOSP` on the bits and
\* then we call `hash_to_pallas` with the result.
procedure s()
begin
    CallI2LEOSP:
        call IntToLEOSP32();
    S:
        call hash_to_pallas(SinsemillaS, bytes);
    return;
end procedure;

\* Produce a Pallas point with the separator and message bytes stored in `separator` and `message_bytes`.
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
We reach the 32 bytes by adding two zeros at the end.

This algorithm is the one implemented in [Zebra](https://github.com/ZcashFoundation/zebra/blob/v1.7.0/zebra-chain/src/orchard/sinsemilla.rs#L72-L74)
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

fair process main = "MAIN"
begin
    SinSemillaHashCall:
        \* Call the main procedure with the domain and message. Strings are represented as sequences of characters.
        call sinsemilla_hash(
            <<"z",".", "c", "a", "s", "h", ":", "t", "e", "s", "t", "-", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a">>,
            <<"m", "e", "s", "s", "a", "g", "e">>
        );
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "fcd52530" /\ chksum(tla) = "92c4d5b2")
\* Procedure variable n of procedure sinsemilla_hash_to_point at line 123 col 5 changed to n_
CONSTANT defaultInitValue
VARIABLES point, characters, bytes, auxiliar_bytes, bits, slices, pc, stack

(* define statement *)
k == 10

SinsemillaQ == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "Q" >>

SinsemillaS == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "S" >>





IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b]



TypeInvariantPoint == point \in [a: Nat, b: Nat]
TypeInvariantCharacters == characters \in Seq(STRING)
TypeInvariantBytes == bytes \in Seq(Nat)
TypeInvariantAuxiliarBytes == bytes \in Seq(Nat)
TypeInvariantBits == bits \in Seq({0, 1})
TypeInvariantSlices == slices \in Seq(Seq({0, 1}))

InvType == TypeInvariantPoint /\ TypeInvariantCharacters /\ TypeInvariantBytes /\ TypeInvariantBytes /\
    TypeInvariantBits /\ TypeInvariantSlices





Liveness == <> (point # [a |-> 0, b |-> 0])




SafetyBytesSequence ==  /\ bytes = <<>> \/ (\A i \in 1..Len(bytes) : bytes[i] \in 0..255)



SafetySlicesSequence == /\ slices = <<>> \/ (\A i \in 1..Len(slices) : slices[i] \in Seq({0, 1}) /\ Len(slices[i]) <= k)

Safety == SafetyBytesSequence /\ SafetySlicesSequence

VARIABLES domain, message, n_, accumulator, i, n, separator, message_bytes

vars == << point, characters, bytes, auxiliar_bytes, bits, slices, pc, stack, 
           domain, message, n_, accumulator, i, n, separator, message_bytes
        >>

ProcSet == {"MAIN"}

Init == (* Global variables *)
        /\ point = [a |-> 0, b |-> 0]
        /\ characters = <<>>
        /\ bytes = <<>>
        /\ auxiliar_bytes = <<>>
        /\ bits = <<>>
        /\ slices = <<>>
        (* Procedure sinsemilla_hash *)
        /\ domain = [ self \in ProcSet |-> defaultInitValue]
        /\ message = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure sinsemilla_hash_to_point *)
        /\ n_ = [ self \in ProcSet |-> Len(bits) \div k]
        /\ accumulator = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> 1]
        (* Procedure pad *)
        /\ n = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure hash_to_pallas *)
        /\ separator = [ self \in ProcSet |-> defaultInitValue]
        /\ message_bytes = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "SinSemillaHashCall"]

EncodeDomain(self) == /\ pc[self] = "EncodeDomain"
                      /\ characters' = domain[self]
                      /\ bytes' = [c \in 1..Len(characters') |-> Ord(characters'[c])]
                      /\ auxiliar_bytes' = bytes'
                      /\ pc' = [pc EXCEPT ![self] = "EncodeMessage"]
                      /\ UNCHANGED << point, bits, slices, stack, domain, 
                                      message, n_, accumulator, i, n, 
                                      separator, message_bytes >>

EncodeMessage(self) == /\ pc[self] = "EncodeMessage"
                       /\ characters' = message[self]
                       /\ bytes' = [c \in 1..Len(characters') |-> Ord(characters'[c])]
                       /\ bits' = FlattenSeq([byte \in 1..Len(bytes') |-> ByteToBitSequence(bytes'[byte])])
                       /\ pc' = [pc EXCEPT ![self] = "SinsemillaHashToPoint"]
                       /\ UNCHANGED << point, auxiliar_bytes, slices, stack, 
                                       domain, message, n_, accumulator, i, n, 
                                       separator, message_bytes >>

SinsemillaHashToPoint(self) == /\ pc[self] = "SinsemillaHashToPoint"
                               /\ bytes' = auxiliar_bytes
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sinsemilla_hash_to_point",
                                                                        pc        |->  "DecodeCipherText",
                                                                        n_        |->  n_[self],
                                                                        accumulator |->  accumulator[self],
                                                                        i         |->  i[self] ] >>
                                                                    \o stack[self]]
                               /\ n_' = [n_ EXCEPT ![self] = Len(bits) \div k]
                               /\ accumulator' = [accumulator EXCEPT ![self] = defaultInitValue]
                               /\ i' = [i EXCEPT ![self] = 1]
                               /\ pc' = [pc EXCEPT ![self] = "CallPad"]
                               /\ UNCHANGED << point, characters, 
                                               auxiliar_bytes, bits, slices, 
                                               domain, message, n, separator, 
                                               message_bytes >>

DecodeCipherText(self) == /\ pc[self] = "DecodeCipherText"
                          /\ bytes' = <<point.a, point.b>>
                          /\ characters' = [b \in 1..Len(bytes') |-> Chr(bytes'[b])]
                          /\ pc' = [pc EXCEPT ![self] = "Return"]
                          /\ UNCHANGED << point, auxiliar_bytes, bits, slices, 
                                          stack, domain, message, n_, 
                                          accumulator, i, n, separator, 
                                          message_bytes >>

Return(self) == /\ pc[self] = "Return"
                /\ PrintT(characters)
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ domain' = [domain EXCEPT ![self] = Head(stack[self]).domain]
                /\ message' = [message EXCEPT ![self] = Head(stack[self]).message]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, bits, 
                                slices, n_, accumulator, i, n, separator, 
                                message_bytes >>

sinsemilla_hash(self) == EncodeDomain(self) \/ EncodeMessage(self)
                            \/ SinsemillaHashToPoint(self)
                            \/ DecodeCipherText(self) \/ Return(self)

CallPad(self) == /\ pc[self] = "CallPad"
                 /\ /\ n' = [n EXCEPT ![self] = n_[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pad",
                                                             pc        |->  "CallQ",
                                                             n         |->  n[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "GetSlices"]
                 /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                 bits, slices, domain, message, n_, 
                                 accumulator, i, separator, message_bytes >>

CallQ(self) == /\ pc[self] = "CallQ"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "q",
                                                        pc        |->  "InitializeAcc" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "Q"]
               /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, bits, 
                               slices, domain, message, n_, accumulator, i, n, 
                               separator, message_bytes >>

InitializeAcc(self) == /\ pc[self] = "InitializeAcc"
                       /\ accumulator' = [accumulator EXCEPT ![self] = point]
                       /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                       /\ UNCHANGED << point, characters, bytes, 
                                       auxiliar_bytes, bits, slices, stack, 
                                       domain, message, n_, i, n, separator, 
                                       message_bytes >>

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ IF i[self] <= n_[self]
                        THEN /\ pc' = [pc EXCEPT ![self] = "CallS"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "AssignAccumulatorToPoint"]
                  /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                  bits, slices, stack, domain, message, n_, 
                                  accumulator, i, n, separator, message_bytes >>

CallS(self) == /\ pc[self] = "CallS"
               /\ bits' = slices[i[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "s",
                                                        pc        |->  "Accumulate" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "CallI2LEOSP"]
               /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                               slices, domain, message, n_, accumulator, i, n, 
                               separator, message_bytes >>

Accumulate(self) == /\ pc[self] = "Accumulate"
                    /\ accumulator' = [accumulator EXCEPT ![self] = IncompleteAddition(IncompleteAddition(accumulator[self], point), accumulator[self])]
                    /\ pc' = [pc EXCEPT ![self] = "IncrementIndex"]
                    /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                    bits, slices, stack, domain, message, n_, 
                                    i, n, separator, message_bytes >>

IncrementIndex(self) == /\ pc[self] = "IncrementIndex"
                        /\ i' = [i EXCEPT ![self] = i[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                        /\ UNCHANGED << point, characters, bytes, 
                                        auxiliar_bytes, bits, slices, stack, 
                                        domain, message, n_, accumulator, n, 
                                        separator, message_bytes >>

AssignAccumulatorToPoint(self) == /\ pc[self] = "AssignAccumulatorToPoint"
                                  /\ point' = accumulator[self]
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ n_' = [n_ EXCEPT ![self] = Head(stack[self]).n_]
                                  /\ accumulator' = [accumulator EXCEPT ![self] = Head(stack[self]).accumulator]
                                  /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED << characters, bytes, 
                                                  auxiliar_bytes, bits, slices, 
                                                  domain, message, n, 
                                                  separator, message_bytes >>

sinsemilla_hash_to_point(self) == CallPad(self) \/ CallQ(self)
                                     \/ InitializeAcc(self)
                                     \/ MainLoop(self) \/ CallS(self)
                                     \/ Accumulate(self)
                                     \/ IncrementIndex(self)
                                     \/ AssignAccumulatorToPoint(self)

GetSlices(self) == /\ pc[self] = "GetSlices"
                   /\ slices' =           [index \in 1..n[self] |-> IF (index * k + k) >= Len(bits) THEN
                                    SubSeq(bits, index * k, Len(bits))
                                ELSE SubSeq(bits, index * k, index * k + k - 1)]
                   /\ pc' = [pc EXCEPT ![self] = "PadLastSlice"]
                   /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                   bits, stack, domain, message, n_, 
                                   accumulator, i, n, separator, message_bytes >>

PadLastSlice(self) == /\ pc[self] = "PadLastSlice"
                      /\ slices' = [slices EXCEPT ![Len(slices)] =                        [index \in 1..k |-> IF index <= Len(slices[Len(slices)]) THEN
                                                                       slices[Len(slices)][index]
                                                                   ELSE 0]]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                      bits, domain, message, n_, accumulator, 
                                      i, separator, message_bytes >>

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
                           slices, domain, message, n_, accumulator, i, n >>

q(self) == Q(self)

CallI2LEOSP(self) == /\ pc[self] = "CallI2LEOSP"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "IntToLEOSP32",
                                                              pc        |->  "S" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "IntToLEOSP"]
                     /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                     bits, slices, domain, message, n_, 
                                     accumulator, i, n, separator, 
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
                           slices, domain, message, n_, accumulator, i, n >>

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
                                      slices, domain, message, n_, accumulator, 
                                      i, n >>

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
                                    slices, domain, message, n_, accumulator, 
                                    i, n, separator, message_bytes >>

IntToLEOSP32(self) == IntToLEOSP(self)

SinSemillaHashCall == /\ pc["MAIN"] = "SinSemillaHashCall"
                      /\ /\ domain' = [domain EXCEPT !["MAIN"] = <<"z",".", "c", "a", "s", "h", ":", "t", "e", "s", "t", "-", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a">>]
                         /\ message' = [message EXCEPT !["MAIN"] = <<"m", "e", "s", "s", "a", "g", "e">>]
                         /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "sinsemilla_hash",
                                                                    pc        |->  "Done",
                                                                    domain    |->  domain["MAIN"],
                                                                    message   |->  message["MAIN"] ] >>
                                                                \o stack["MAIN"]]
                      /\ pc' = [pc EXCEPT !["MAIN"] = "EncodeDomain"]
                      /\ UNCHANGED << point, characters, bytes, auxiliar_bytes, 
                                      bits, slices, n_, accumulator, i, n, 
                                      separator, message_bytes >>

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
