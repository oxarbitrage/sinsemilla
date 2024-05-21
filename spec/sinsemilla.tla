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
    \* Store any sequence of bits at any program state.
    bits = <<>>;
    \* Store any sequence of slices at any program state.
    slices = <<>>;

\* DEFINED OPERATORS:

define
    \* The number of bits in a chunk
    k == 10
    \* The incomplete addition operator. Sums the x and y coordinates of two points on the Pallas curve.
    \* TODO: Consider x and y cases here?
    IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b]
    \* The domain separator string for the Q point: `z.cash.SinsemillaQ`
    SinsemillaQ == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "Q" >>
    \* The domain separator string for the S point: `z.cash.SinsemillaS`
    SinsemillaS == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "S" >>
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
variables
    domain_bytes = <<>>;
begin
    \* Encode the domain characters as bytes and store them in `domain_bytes` for later use.
    EncodeDomain:
        characters := domain;
        characters_to_bytes();
        domain_bytes := bytes;
    \* Encode the message characters as bits and store them in `bits` for later use.
    EncodeMessage:
        characters := message;
        characters_to_bytes();
        bytes_to_bits();
    \* With the domain bytes in `bytes` and the message bits in `bits`, call the main procedure to hash the message.
    SinsemillaHashToPoint:
        bytes := domain_bytes;
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
        ELSE SubSeq(bits, index * k, index * k + k)];
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
        call IntToLEOSP();
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

\* Integer to Little-Endian Octet String Pairing
procedure IntToLEOSP()
variables byte1 = 0, byte2 = 0, internal_bits = <<>>;
begin
    DoIntToLEOSP:
        byte1 := BitSequenceToByte(SubSeq(bits, 1, 8));
        internal_bits := SubSeq(bits, 9, 10);
        bits := <<internal_bits[1], internal_bits[2], 0, 0, 0, 0, 0, 0>>;
        byte2 := BitSequenceToByte(bits);
    AssignToBytes:
        bytes := <<byte1, byte2, 0, 0>>;
    return;
end procedure;

begin
    SinSemillaHashCall:
        \* Call the main procedure with the domain and message. Strings are represented as sequences of characters.
        call sinsemilla_hash(
            <<"z",".", "c", "a", "s", "h", ":", "t", "e", "s", "t", "-", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a">>,
            <<"m", "e", "s", "s", "a", "g", "e">>
        );
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b362b92f" /\ chksum(tla) = "b3f0674c")
\* Procedure variable n of procedure sinsemilla_hash_to_point at line 91 col 5 changed to n_
CONSTANT defaultInitValue
VARIABLES point, characters, bytes, bits, slices, pc, stack

(* define statement *)
k == 10


IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b]

SinsemillaQ == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "Q" >>

SinsemillaS == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "S" >>

VARIABLES domain, message, domain_bytes, n_, accumulator, i, n, separator, 
          message_bytes, byte1, byte2, internal_bits

vars == << point, characters, bytes, bits, slices, pc, stack, domain, message, 
           domain_bytes, n_, accumulator, i, n, separator, message_bytes, 
           byte1, byte2, internal_bits >>

Init == (* Global variables *)
        /\ point = [a |-> 0, b |-> 0]
        /\ characters = <<>>
        /\ bytes = <<>>
        /\ bits = <<>>
        /\ slices = <<>>
        (* Procedure sinsemilla_hash *)
        /\ domain = defaultInitValue
        /\ message = defaultInitValue
        /\ domain_bytes = <<>>
        (* Procedure sinsemilla_hash_to_point *)
        /\ n_ = (Len(bits) \div k)
        /\ accumulator = defaultInitValue
        /\ i = 1
        (* Procedure pad *)
        /\ n = defaultInitValue
        (* Procedure hash_to_pallas *)
        /\ separator = defaultInitValue
        /\ message_bytes = defaultInitValue
        (* Procedure IntToLEOSP *)
        /\ byte1 = 0
        /\ byte2 = 0
        /\ internal_bits = <<>>
        /\ stack = << >>
        /\ pc = "SinSemillaHashCall"

EncodeDomain == /\ pc = "EncodeDomain"
                /\ characters' = domain
                /\ bytes' = [c \in 1..Len(characters') |-> Ord(characters'[c])]
                /\ domain_bytes' = bytes'
                /\ pc' = "EncodeMessage"
                /\ UNCHANGED << point, bits, slices, stack, domain, message, 
                                n_, accumulator, i, n, separator, 
                                message_bytes, byte1, byte2, internal_bits >>

EncodeMessage == /\ pc = "EncodeMessage"
                 /\ characters' = message
                 /\ bytes' = [c \in 1..Len(characters') |-> Ord(characters'[c])]
                 /\ bits' = FlattenSeq([byte \in 1..Len(bytes') |-> ByteToBitSequence(bytes'[byte])])
                 /\ pc' = "SinsemillaHashToPoint"
                 /\ UNCHANGED << point, slices, stack, domain, message, 
                                 domain_bytes, n_, accumulator, i, n, 
                                 separator, message_bytes, byte1, byte2, 
                                 internal_bits >>

SinsemillaHashToPoint == /\ pc = "SinsemillaHashToPoint"
                         /\ bytes' = domain_bytes
                         /\ stack' = << [ procedure |->  "sinsemilla_hash_to_point",
                                          pc        |->  "DecodeCipherText",
                                          n_        |->  n_,
                                          accumulator |->  accumulator,
                                          i         |->  i ] >>
                                      \o stack
                         /\ n_' = (Len(bits) \div k)
                         /\ accumulator' = defaultInitValue
                         /\ i' = 1
                         /\ pc' = "CallPad"
                         /\ UNCHANGED << point, characters, bits, slices, 
                                         domain, message, domain_bytes, n, 
                                         separator, message_bytes, byte1, 
                                         byte2, internal_bits >>

DecodeCipherText == /\ pc = "DecodeCipherText"
                    /\ bytes' = <<point.a, point.b>>
                    /\ characters' = [b \in 1..Len(bytes') |-> Chr(bytes'[b])]
                    /\ pc' = "Return"
                    /\ UNCHANGED << point, bits, slices, stack, domain, 
                                    message, domain_bytes, n_, accumulator, i, 
                                    n, separator, message_bytes, byte1, byte2, 
                                    internal_bits >>

Return == /\ pc = "Return"
          /\ PrintT(characters)
          /\ pc' = Head(stack).pc
          /\ domain_bytes' = Head(stack).domain_bytes
          /\ domain' = Head(stack).domain
          /\ message' = Head(stack).message
          /\ stack' = Tail(stack)
          /\ UNCHANGED << point, characters, bytes, bits, slices, n_, 
                          accumulator, i, n, separator, message_bytes, byte1, 
                          byte2, internal_bits >>

sinsemilla_hash == EncodeDomain \/ EncodeMessage \/ SinsemillaHashToPoint
                      \/ DecodeCipherText \/ Return

CallPad == /\ pc = "CallPad"
           /\ /\ n' = n_
              /\ stack' = << [ procedure |->  "pad",
                               pc        |->  "CallQ",
                               n         |->  n ] >>
                           \o stack
           /\ pc' = "GetSlices"
           /\ UNCHANGED << point, characters, bytes, bits, slices, domain, 
                           message, domain_bytes, n_, accumulator, i, 
                           separator, message_bytes, byte1, byte2, 
                           internal_bits >>

CallQ == /\ pc = "CallQ"
         /\ stack' = << [ procedure |->  "q",
                          pc        |->  "InitializeAcc" ] >>
                      \o stack
         /\ pc' = "Q"
         /\ UNCHANGED << point, characters, bytes, bits, slices, domain, 
                         message, domain_bytes, n_, accumulator, i, n, 
                         separator, message_bytes, byte1, byte2, internal_bits >>

InitializeAcc == /\ pc = "InitializeAcc"
                 /\ accumulator' = point
                 /\ pc' = "MainLoop"
                 /\ UNCHANGED << point, characters, bytes, bits, slices, stack, 
                                 domain, message, domain_bytes, n_, i, n, 
                                 separator, message_bytes, byte1, byte2, 
                                 internal_bits >>

MainLoop == /\ pc = "MainLoop"
            /\ IF i <= n_
                  THEN /\ pc' = "CallS"
                  ELSE /\ pc' = "AssignAccumulatorToPoint"
            /\ UNCHANGED << point, characters, bytes, bits, slices, stack, 
                            domain, message, domain_bytes, n_, accumulator, i, 
                            n, separator, message_bytes, byte1, byte2, 
                            internal_bits >>

CallS == /\ pc = "CallS"
         /\ bits' = slices[i]
         /\ stack' = << [ procedure |->  "s",
                          pc        |->  "Accumulate" ] >>
                      \o stack
         /\ pc' = "CallI2LEOSP"
         /\ UNCHANGED << point, characters, bytes, slices, domain, message, 
                         domain_bytes, n_, accumulator, i, n, separator, 
                         message_bytes, byte1, byte2, internal_bits >>

Accumulate == /\ pc = "Accumulate"
              /\ accumulator' = IncompleteAddition(IncompleteAddition(accumulator, point), accumulator)
              /\ pc' = "IncrementIndex"
              /\ UNCHANGED << point, characters, bytes, bits, slices, stack, 
                              domain, message, domain_bytes, n_, i, n, 
                              separator, message_bytes, byte1, byte2, 
                              internal_bits >>

IncrementIndex == /\ pc = "IncrementIndex"
                  /\ i' = i + 1
                  /\ pc' = "MainLoop"
                  /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                  stack, domain, message, domain_bytes, n_, 
                                  accumulator, n, separator, message_bytes, 
                                  byte1, byte2, internal_bits >>

AssignAccumulatorToPoint == /\ pc = "AssignAccumulatorToPoint"
                            /\ point' = accumulator
                            /\ pc' = Head(stack).pc
                            /\ n_' = Head(stack).n_
                            /\ accumulator' = Head(stack).accumulator
                            /\ i' = Head(stack).i
                            /\ stack' = Tail(stack)
                            /\ UNCHANGED << characters, bytes, bits, slices, 
                                            domain, message, domain_bytes, n, 
                                            separator, message_bytes, byte1, 
                                            byte2, internal_bits >>

sinsemilla_hash_to_point == CallPad \/ CallQ \/ InitializeAcc \/ MainLoop
                               \/ CallS \/ Accumulate \/ IncrementIndex
                               \/ AssignAccumulatorToPoint

GetSlices == /\ pc = "GetSlices"
             /\ slices' =           [index \in 1..n |-> IF (index * k + k) >= Len(bits) THEN
                              SubSeq(bits, index * k, Len(bits))
                          ELSE SubSeq(bits, index * k, index * k + k)]
             /\ pc' = "PadLastSlice"
             /\ UNCHANGED << point, characters, bytes, bits, stack, domain, 
                             message, domain_bytes, n_, accumulator, i, n, 
                             separator, message_bytes, byte1, byte2, 
                             internal_bits >>

PadLastSlice == /\ pc = "PadLastSlice"
                /\ slices' = [slices EXCEPT ![Len(slices)] =                        [index \in 1..k |-> IF index <= Len(slices[Len(slices)]) THEN
                                                                 slices[Len(slices)][index]
                                                             ELSE 0]]
                /\ pc' = Head(stack).pc
                /\ n' = Head(stack).n
                /\ stack' = Tail(stack)
                /\ UNCHANGED << point, characters, bytes, bits, domain, 
                                message, domain_bytes, n_, accumulator, i, 
                                separator, message_bytes, byte1, byte2, 
                                internal_bits >>

pad == GetSlices \/ PadLastSlice

Q == /\ pc = "Q"
     /\ /\ message_bytes' = bytes
        /\ separator' = SinsemillaQ
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         separator |->  separator,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ pc' = "HashToPallas"
     /\ UNCHANGED << point, characters, bytes, bits, slices, domain, message, 
                     domain_bytes, n_, accumulator, i, n, byte1, byte2, 
                     internal_bits >>

q == Q

CallI2LEOSP == /\ pc = "CallI2LEOSP"
               /\ stack' = << [ procedure |->  "IntToLEOSP",
                                pc        |->  "S",
                                byte1     |->  byte1,
                                byte2     |->  byte2,
                                internal_bits |->  internal_bits ] >>
                            \o stack
               /\ byte1' = 0
               /\ byte2' = 0
               /\ internal_bits' = <<>>
               /\ pc' = "DoIntToLEOSP"
               /\ UNCHANGED << point, characters, bytes, bits, slices, domain, 
                               message, domain_bytes, n_, accumulator, i, n, 
                               separator, message_bytes >>

S == /\ pc = "S"
     /\ /\ message_bytes' = bytes
        /\ separator' = SinsemillaS
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         separator |->  separator,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ pc' = "HashToPallas"
     /\ UNCHANGED << point, characters, bytes, bits, slices, domain, message, 
                     domain_bytes, n_, accumulator, i, n, byte1, byte2, 
                     internal_bits >>

s == CallI2LEOSP \/ S

HashToPallas == /\ pc = "HashToPallas"
                /\ point' =          [
                                a |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE,
                                b |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE
                            ]
                /\ pc' = Head(stack).pc
                /\ separator' = Head(stack).separator
                /\ message_bytes' = Head(stack).message_bytes
                /\ stack' = Tail(stack)
                /\ UNCHANGED << characters, bytes, bits, slices, domain, 
                                message, domain_bytes, n_, accumulator, i, n, 
                                byte1, byte2, internal_bits >>

hash_to_pallas == HashToPallas

DoIntToLEOSP == /\ pc = "DoIntToLEOSP"
                /\ byte1' = BitSequenceToByte(SubSeq(bits, 1, 8))
                /\ internal_bits' = SubSeq(bits, 9, 10)
                /\ bits' = <<internal_bits'[1], internal_bits'[2], 0, 0, 0, 0, 0, 0>>
                /\ byte2' = BitSequenceToByte(bits')
                /\ pc' = "AssignToBytes"
                /\ UNCHANGED << point, characters, bytes, slices, stack, 
                                domain, message, domain_bytes, n_, accumulator, 
                                i, n, separator, message_bytes >>

AssignToBytes == /\ pc = "AssignToBytes"
                 /\ bytes' = <<byte1, byte2, 0, 0>>
                 /\ pc' = Head(stack).pc
                 /\ byte1' = Head(stack).byte1
                 /\ byte2' = Head(stack).byte2
                 /\ internal_bits' = Head(stack).internal_bits
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << point, characters, bits, slices, domain, 
                                 message, domain_bytes, n_, accumulator, i, n, 
                                 separator, message_bytes >>

IntToLEOSP == DoIntToLEOSP \/ AssignToBytes

SinSemillaHashCall == /\ pc = "SinSemillaHashCall"
                      /\ /\ domain' = <<"z",".", "c", "a", "s", "h", ":", "t", "e", "s", "t", "-", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a">>
                         /\ message' = <<"m", "e", "s", "s", "a", "g", "e">>
                         /\ stack' = << [ procedure |->  "sinsemilla_hash",
                                          pc        |->  "Done",
                                          domain_bytes |->  domain_bytes,
                                          domain    |->  domain,
                                          message   |->  message ] >>
                                      \o stack
                      /\ domain_bytes' = <<>>
                      /\ pc' = "EncodeDomain"
                      /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                      n_, accumulator, i, n, separator, 
                                      message_bytes, byte1, byte2, 
                                      internal_bits >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == sinsemilla_hash \/ sinsemilla_hash_to_point \/ pad \/ q \/ s
           \/ hash_to_pallas \/ IntToLEOSP \/ SinSemillaHashCall
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
