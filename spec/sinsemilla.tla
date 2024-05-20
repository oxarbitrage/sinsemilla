---- MODULE sinsemilla ----
EXTENDS TLC, Naturals, Integers, Sequences, Utils, Randomization

(*--algorithm sinsemilla

variables
    \* Store any point on the Pallas curve at any program state.
    point = [a |-> 0, b |-> 0, baseX |-> 0, baseY |-> 0];
    \* Store any sequence of characters at any program state.
    characters = <<>>;
    \* Store any sequence of bytes at any program state.
    bytes = <<>>;
    \* Store any sequence of bits at any program state.
    bits = <<>>;
    \* Store any sequence of slices at any program state.
    slices = <<>>;

define
    \* Pallas base point x-coordinate: 0x01
    baseX == 1
    \* Pallas base point y-coordinate: 0xbb2aedca237acf1971473d33d45b658f54ee7863f0a9df537c93120aa3b5741b
    baseY == 187
    \* The number of bits in a chunk
    k == 10
    \* The incomplete addition operator. Sums the x and y coordinates of two points on the Pallas curve.
    \* TODO: Consider x and y cases here?
    IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b, baseX |-> baseX, baseY |-> baseY]
    \* The domain separator string for the Q point: `z.cash.SinsemillaQ`
    sinsemilla_q_separator == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "Q" >>
    \* The domain separator string for the S point: `z.cash.SinsemillaS`
    sinsemilla_s_separator == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "S" >>
end define;

procedure sinsemilla_hash(domain, message)
variables domain_bytes = <<>>;
begin
    DomainCharactersToBytesCall:
        characters := domain;
        call characters_to_bytes();
    DomainStringToBytesAssign:
        domain_bytes := bytes;
    MessageCharactersToBytesCall:
        characters := message;
        call characters_to_bytes();
    MessageBytesToBitsCall:
        call bytes_to_bits();
    SinsemillaHashToPoint:
        bytes := domain_bytes;
        call sinsemilla_hash_to_point();
    OutputPointToBytes:
        call point_to_bytes();
    OutputBytesToCharacters:
        call bytes_to_characters();
    Return:
        print characters;
        return;
end procedure;

\* Convert a sequence of characters to a sequence of bytes.
procedure characters_to_bytes()
begin
    FlushBytes:
        bytes := <<>>;
    StringToBytes:
        bytes := [c \in 1..Len(characters) |-> Ord(characters[c])];
        return;
end procedure;

\* Convert a sequence of bytes to a flat sequence of bits.
procedure bytes_to_bits()
begin
    FlushBits:
        bits := <<>>;
    BytesToBitSequence:
        bits := [byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])];
    Flatten:
        bits := FlattenSeq(bits);
        return;
end procedure;

\* Convert the message bits into a Pallas point, using the domain bytes stored in `bytes` as the domain separator
\* and the message bits stored in `bits` as the message.
procedure sinsemilla_hash_to_point()
variables 
    n = Len(bits) \div k,
    accumulator,
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
            DoIncompleteAddition:
                \* Incomplete addition of the accumulator and the point.
                accumulator := IncompleteAddition(IncompleteAddition(accumulator, point), accumulator);
                i := i + 1;
        end while;
        point := accumulator;
    ReturnFromSinsemillaHashToPoint:
        return;
end procedure;

\* Pad the message bits with zeros until the length is a multiple of k. Create chunks of k bits.
procedure pad(n)
begin
    GetSlices:
        \* Complicated expression to get the slices without looping.
        slices := [index \in 1..n |-> IF (index * k + k) >= Len(bits) THEN SubSeq(bits, index * k, Len(bits)) ELSE SubSeq(bits, index * k, index * k + k)];
    PadLastSlice:
        \* Complicated expression to pad the last slice with zeros.
        slices[Len(slices)] := [index \in 1..k |-> IF index <= Len(slices[Len(slices)]) THEN slices[Len(slices)][index] ELSE 0];
        return;
end procedure;

\* Produce a Pallas point with the bytes stored in `bytes`, these bytes are set in the caller as domain bytes.
procedure q()
begin
    Q:
        call hash_to_pallas(sinsemilla_q_separator, bytes);
        return;
end procedure;

\* Produce a Pallas point given the padded bits (10 bits). First we call `IntToLEOSP` on the bits and
\* then we call `hash_to_pallas` with the result.
procedure s()
begin
    CallI2LEOSP:
        call IntToLEOSP();
    S:
        call hash_to_pallas(sinsemilla_s_separator, bytes);
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
            b |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE, 
            baseX |-> baseX,
            baseY |-> baseY
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
        bytes := <<byte1, byte2, 0, 0>>;
    Return:
        return;
end procedure;

\* Convert a sequence of bytes to a a sequence of characters.
procedure bytes_to_characters()
begin
    FlushCharacters:
        characters := <<>>;
    BytesToCharacters:
        characters := [b \in 1..Len(bytes) |-> Chr(bytes[b])];
        return;
end procedure;

\* Convert a Pallas point to a sequence of fixed bytes. Here we just use the point coordinates as bytes.
procedure point_to_bytes()
begin
    PointToBytes:
        bytes := <<point.a, point.b>>;
        print bytes;    
    return;
end procedure;

begin
    SinSemillaHashCall:
        \* Call the main procedure with the domain and message. Strings are represented as sequences of characters.
        call sinsemilla_hash(<<"d", "o", "m", "a", "i", "n">>, <<"m", "e", "s", "s", "a", "g", "e">>);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "13c718c5" /\ chksum(tla) = "c90321ef")
\* Label Return of procedure sinsemilla_hash at line 55 col 9 changed to Return_
\* Procedure variable n of procedure sinsemilla_hash_to_point at line 85 col 5 changed to n_
CONSTANT defaultInitValue
VARIABLES point, characters, bytes, bits, slices, pc, stack

(* define statement *)
baseX == 1

baseY == 187

k == 10


IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b, baseX |-> baseX, baseY |-> baseY]

sinsemilla_q_separator == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "Q" >>

sinsemilla_s_separator == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "S" >>

VARIABLES domain, message, domain_bytes, n_, accumulator, i, n, separator, 
          message_bytes, byte1, byte2, internal_bits

vars == << point, characters, bytes, bits, slices, pc, stack, domain, message, 
           domain_bytes, n_, accumulator, i, n, separator, message_bytes, 
           byte1, byte2, internal_bits >>

Init == (* Global variables *)
        /\ point = [a |-> 0, b |-> 0, baseX |-> 0, baseY |-> 0]
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

DomainCharactersToBytesCall == /\ pc = "DomainCharactersToBytesCall"
                               /\ characters' = domain
                               /\ stack' = << [ procedure |->  "characters_to_bytes",
                                                pc        |->  "DomainStringToBytesAssign" ] >>
                                            \o stack
                               /\ pc' = "FlushBytes"
                               /\ UNCHANGED << point, bytes, bits, slices, 
                                               domain, message, domain_bytes, 
                                               n_, accumulator, i, n, 
                                               separator, message_bytes, byte1, 
                                               byte2, internal_bits >>

DomainStringToBytesAssign == /\ pc = "DomainStringToBytesAssign"
                             /\ domain_bytes' = bytes
                             /\ pc' = "MessageCharactersToBytesCall"
                             /\ UNCHANGED << point, characters, bytes, bits, 
                                             slices, stack, domain, message, 
                                             n_, accumulator, i, n, separator, 
                                             message_bytes, byte1, byte2, 
                                             internal_bits >>

MessageCharactersToBytesCall == /\ pc = "MessageCharactersToBytesCall"
                                /\ characters' = message
                                /\ stack' = << [ procedure |->  "characters_to_bytes",
                                                 pc        |->  "MessageBytesToBitsCall" ] >>
                                             \o stack
                                /\ pc' = "FlushBytes"
                                /\ UNCHANGED << point, bytes, bits, slices, 
                                                domain, message, domain_bytes, 
                                                n_, accumulator, i, n, 
                                                separator, message_bytes, 
                                                byte1, byte2, internal_bits >>

MessageBytesToBitsCall == /\ pc = "MessageBytesToBitsCall"
                          /\ stack' = << [ procedure |->  "bytes_to_bits",
                                           pc        |->  "SinsemillaHashToPoint" ] >>
                                       \o stack
                          /\ pc' = "FlushBits"
                          /\ UNCHANGED << point, characters, bytes, bits, 
                                          slices, domain, message, 
                                          domain_bytes, n_, accumulator, i, n, 
                                          separator, message_bytes, byte1, 
                                          byte2, internal_bits >>

SinsemillaHashToPoint == /\ pc = "SinsemillaHashToPoint"
                         /\ bytes' = domain_bytes
                         /\ stack' = << [ procedure |->  "sinsemilla_hash_to_point",
                                          pc        |->  "OutputPointToBytes",
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

OutputPointToBytes == /\ pc = "OutputPointToBytes"
                      /\ stack' = << [ procedure |->  "point_to_bytes",
                                       pc        |->  "OutputBytesToCharacters" ] >>
                                   \o stack
                      /\ pc' = "PointToBytes"
                      /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                      domain, message, domain_bytes, n_, 
                                      accumulator, i, n, separator, 
                                      message_bytes, byte1, byte2, 
                                      internal_bits >>

OutputBytesToCharacters == /\ pc = "OutputBytesToCharacters"
                           /\ stack' = << [ procedure |->  "bytes_to_characters",
                                            pc        |->  "Return_" ] >>
                                        \o stack
                           /\ pc' = "FlushCharacters"
                           /\ UNCHANGED << point, characters, bytes, bits, 
                                           slices, domain, message, 
                                           domain_bytes, n_, accumulator, i, n, 
                                           separator, message_bytes, byte1, 
                                           byte2, internal_bits >>

Return_ == /\ pc = "Return_"
           /\ PrintT(characters)
           /\ pc' = Head(stack).pc
           /\ domain_bytes' = Head(stack).domain_bytes
           /\ domain' = Head(stack).domain
           /\ message' = Head(stack).message
           /\ stack' = Tail(stack)
           /\ UNCHANGED << point, characters, bytes, bits, slices, n_, 
                           accumulator, i, n, separator, message_bytes, byte1, 
                           byte2, internal_bits >>

sinsemilla_hash == DomainCharactersToBytesCall \/ DomainStringToBytesAssign
                      \/ MessageCharactersToBytesCall
                      \/ MessageBytesToBitsCall \/ SinsemillaHashToPoint
                      \/ OutputPointToBytes \/ OutputBytesToCharacters
                      \/ Return_

FlushBytes == /\ pc = "FlushBytes"
              /\ bytes' = <<>>
              /\ pc' = "StringToBytes"
              /\ UNCHANGED << point, characters, bits, slices, stack, domain, 
                              message, domain_bytes, n_, accumulator, i, n, 
                              separator, message_bytes, byte1, byte2, 
                              internal_bits >>

StringToBytes == /\ pc = "StringToBytes"
                 /\ bytes' = [c \in 1..Len(characters) |-> Ord(characters[c])]
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << point, characters, bits, slices, domain, 
                                 message, domain_bytes, n_, accumulator, i, n, 
                                 separator, message_bytes, byte1, byte2, 
                                 internal_bits >>

characters_to_bytes == FlushBytes \/ StringToBytes

FlushBits == /\ pc = "FlushBits"
             /\ bits' = <<>>
             /\ pc' = "BytesToBitSequence"
             /\ UNCHANGED << point, characters, bytes, slices, stack, domain, 
                             message, domain_bytes, n_, accumulator, i, n, 
                             separator, message_bytes, byte1, byte2, 
                             internal_bits >>

BytesToBitSequence == /\ pc = "BytesToBitSequence"
                      /\ bits' = [byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])]
                      /\ pc' = "Flatten"
                      /\ UNCHANGED << point, characters, bytes, slices, stack, 
                                      domain, message, domain_bytes, n_, 
                                      accumulator, i, n, separator, 
                                      message_bytes, byte1, byte2, 
                                      internal_bits >>

Flatten == /\ pc = "Flatten"
           /\ bits' = FlattenSeq(bits)
           /\ pc' = Head(stack).pc
           /\ stack' = Tail(stack)
           /\ UNCHANGED << point, characters, bytes, slices, domain, message, 
                           domain_bytes, n_, accumulator, i, n, separator, 
                           message_bytes, byte1, byte2, internal_bits >>

bytes_to_bits == FlushBits \/ BytesToBitSequence \/ Flatten

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
                       /\ point' = point
                  ELSE /\ point' = accumulator
                       /\ pc' = "ReturnFromSinsemillaHashToPoint"
            /\ UNCHANGED << characters, bytes, bits, slices, stack, domain, 
                            message, domain_bytes, n_, accumulator, i, n, 
                            separator, message_bytes, byte1, byte2, 
                            internal_bits >>

CallS == /\ pc = "CallS"
         /\ bits' = slices[i]
         /\ stack' = << [ procedure |->  "s",
                          pc        |->  "DoIncompleteAddition" ] >>
                      \o stack
         /\ pc' = "CallI2LEOSP"
         /\ UNCHANGED << point, characters, bytes, slices, domain, message, 
                         domain_bytes, n_, accumulator, i, n, separator, 
                         message_bytes, byte1, byte2, internal_bits >>

DoIncompleteAddition == /\ pc = "DoIncompleteAddition"
                        /\ accumulator' = IncompleteAddition(IncompleteAddition(accumulator, point), accumulator)
                        /\ i' = i + 1
                        /\ pc' = "MainLoop"
                        /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                        stack, domain, message, domain_bytes, 
                                        n_, n, separator, message_bytes, byte1, 
                                        byte2, internal_bits >>

ReturnFromSinsemillaHashToPoint == /\ pc = "ReturnFromSinsemillaHashToPoint"
                                   /\ pc' = Head(stack).pc
                                   /\ n_' = Head(stack).n_
                                   /\ accumulator' = Head(stack).accumulator
                                   /\ i' = Head(stack).i
                                   /\ stack' = Tail(stack)
                                   /\ UNCHANGED << point, characters, bytes, 
                                                   bits, slices, domain, 
                                                   message, domain_bytes, n, 
                                                   separator, message_bytes, 
                                                   byte1, byte2, internal_bits >>

sinsemilla_hash_to_point == CallPad \/ CallQ \/ InitializeAcc \/ MainLoop
                               \/ CallS \/ DoIncompleteAddition
                               \/ ReturnFromSinsemillaHashToPoint

GetSlices == /\ pc = "GetSlices"
             /\ slices' = [index \in 1..n |-> IF (index * k + k) >= Len(bits) THEN SubSeq(bits, index * k, Len(bits)) ELSE SubSeq(bits, index * k, index * k + k)]
             /\ pc' = "PadLastSlice"
             /\ UNCHANGED << point, characters, bytes, bits, stack, domain, 
                             message, domain_bytes, n_, accumulator, i, n, 
                             separator, message_bytes, byte1, byte2, 
                             internal_bits >>

PadLastSlice == /\ pc = "PadLastSlice"
                /\ slices' = [slices EXCEPT ![Len(slices)] = [index \in 1..k |-> IF index <= Len(slices[Len(slices)]) THEN slices[Len(slices)][index] ELSE 0]]
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
        /\ separator' = sinsemilla_q_separator
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
        /\ separator' = sinsemilla_s_separator
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
                                b |-> CHOOSE r \in RandomSubset(1, 1..3) : TRUE,
                                baseX |-> baseX,
                                baseY |-> baseY
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
                /\ bytes' = <<byte1', byte2', 0, 0>>
                /\ pc' = "Return"
                /\ UNCHANGED << point, characters, slices, stack, domain, 
                                message, domain_bytes, n_, accumulator, i, n, 
                                separator, message_bytes >>

Return == /\ pc = "Return"
          /\ pc' = Head(stack).pc
          /\ byte1' = Head(stack).byte1
          /\ byte2' = Head(stack).byte2
          /\ internal_bits' = Head(stack).internal_bits
          /\ stack' = Tail(stack)
          /\ UNCHANGED << point, characters, bytes, bits, slices, domain, 
                          message, domain_bytes, n_, accumulator, i, n, 
                          separator, message_bytes >>

IntToLEOSP == DoIntToLEOSP \/ Return

FlushCharacters == /\ pc = "FlushCharacters"
                   /\ characters' = <<>>
                   /\ pc' = "BytesToCharacters"
                   /\ UNCHANGED << point, bytes, bits, slices, stack, domain, 
                                   message, domain_bytes, n_, accumulator, i, 
                                   n, separator, message_bytes, byte1, byte2, 
                                   internal_bits >>

BytesToCharacters == /\ pc = "BytesToCharacters"
                     /\ characters' = [b \in 1..Len(bytes) |-> Chr(bytes[b])]
                     /\ pc' = Head(stack).pc
                     /\ stack' = Tail(stack)
                     /\ UNCHANGED << point, bytes, bits, slices, domain, 
                                     message, domain_bytes, n_, accumulator, i, 
                                     n, separator, message_bytes, byte1, byte2, 
                                     internal_bits >>

bytes_to_characters == FlushCharacters \/ BytesToCharacters

PointToBytes == /\ pc = "PointToBytes"
                /\ bytes' = <<point.a, point.b>>
                /\ PrintT(bytes')
                /\ pc' = Head(stack).pc
                /\ stack' = Tail(stack)
                /\ UNCHANGED << point, characters, bits, slices, domain, 
                                message, domain_bytes, n_, accumulator, i, n, 
                                separator, message_bytes, byte1, byte2, 
                                internal_bits >>

point_to_bytes == PointToBytes

SinSemillaHashCall == /\ pc = "SinSemillaHashCall"
                      /\ /\ domain' = <<"d", "o", "m", "a", "i", "n">>
                         /\ message' = <<"m", "e", "s", "s", "a", "g", "e">>
                         /\ stack' = << [ procedure |->  "sinsemilla_hash",
                                          pc        |->  "Done",
                                          domain_bytes |->  domain_bytes,
                                          domain    |->  domain,
                                          message   |->  message ] >>
                                      \o stack
                      /\ domain_bytes' = <<>>
                      /\ pc' = "DomainCharactersToBytesCall"
                      /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                      n_, accumulator, i, n, separator, 
                                      message_bytes, byte1, byte2, 
                                      internal_bits >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == sinsemilla_hash \/ characters_to_bytes \/ bytes_to_bits
           \/ sinsemilla_hash_to_point \/ pad \/ q \/ s \/ hash_to_pallas
           \/ IntToLEOSP \/ bytes_to_characters \/ point_to_bytes
           \/ SinSemillaHashCall
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
