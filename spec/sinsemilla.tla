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
    acc,
    i = 1;
begin
    CallPad:
        \* Use the global `bits` as input and get slices in `slices`.
        call pad();
    CallQ:
        call q();
    InitializeAcc:
        acc := point;
    Loop:
        while i <= n do
            CallS:
                bits := slices[i];
                call s();
            IncompleteAdditions:
                acc := IncompleteAddition(IncompleteAddition(acc, point), acc);
            Inc:
                i := i + 1;
        end while;
        point := acc;
        print point;
        i := 1;
    ReturnFromSinsemillaHashToPoint:
        return;
end procedure;

\* Pad the message bits with zeros until the length is a multiple of k. Create chunks of k bits.
procedure pad()
variables
    i = 1;
begin
    GetSlices:
        while i <= Len(bits) do
            if i+k >= Len(bits) then
                slices := Append(slices, SubSeq(bits, i, Len(bits)));
                i := Len(bits) + 1;
            else
                slices := Append(slices, SubSeq(bits, i, i+k));
                i := i+k;
            end if;
        end while;

        if Len(slices[Len(slices)]) < k then
            PadLastSlice:
                while Len(slices[Len(slices)]) < k do
                    slices[Len(slices)] := Append(slices[Len(slices)], 0);
                end while;
        end if;
    ReturnFromPad:
        return;
end procedure;

\* Produce a Pallas point with the bytes stored, these bytes are set in the caller as domain bytes.
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

procedure hash_to_pallas(separator, message_bytes)
variables a_coordinate = 0, b_coordinate = 0;
begin
    HashToPallas:
        \* Here we decouple the input message and separator from the outputs by choosing random coordinates.
        a_coordinate := CHOOSE r \in RandomSubset(1, 1..3) : TRUE;
        b_coordinate := CHOOSE r \in RandomSubset(1, 1..3) : TRUE;
        point := [a |-> a_coordinate, b |-> b_coordinate, baseX |-> baseX, baseY |-> baseY];
    Return:
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
variables 
    i = 1;
begin
    FlushCharacters:
        characters := "";
    BytesToCharacters:
        \* Convert each byte to character
        characters := [b \in 1..Len(bytes) |-> Chr(bytes[b])];
        return;
end procedure;

procedure point_to_bytes()
begin
    PointToBytes:
        bytes := <<point.a, point.b, point.baseX, point.baseY>>;
        print bytes;    
    return;
end procedure;

begin
    SinSemillaHashCall:
        call sinsemilla_hash(<<"d", "o", "m", "a", "i", "n">>, <<"m", "e", "s", "s", "a", "g", "e">>);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6aeacd4a" /\ chksum(tla) = "2d422ec1")
\* Label Return of procedure sinsemilla_hash at line 55 col 9 changed to Return_
\* Label Return of procedure hash_to_pallas at line 167 col 9 changed to Return_h
\* Procedure variable i of procedure sinsemilla_hash_to_point at line 87 col 5 changed to i_
\* Procedure variable i of procedure pad at line 116 col 5 changed to i_p
CONSTANT defaultInitValue
VARIABLES point, characters, bytes, bits, slices, pc, stack

(* define statement *)
baseX == 1

baseY == 187

k == 10


IncompleteAddition(x, y) == [a |-> x.a + y.a, b |-> x.b + y.b, baseX |-> baseX, baseY |-> baseY]

sinsemilla_q_separator == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "Q" >>

sinsemilla_s_separator == << "z", ".", "c", "a", "s", "h", ".", "S", "i", "n", "s", "e", "m", "i", "l", "l", "a", "S" >>

VARIABLES domain, message, domain_bytes, n, acc, i_, i_p, separator, 
          message_bytes, a_coordinate, b_coordinate, byte1, byte2, 
          internal_bits, i

vars == << point, characters, bytes, bits, slices, pc, stack, domain, message, 
           domain_bytes, n, acc, i_, i_p, separator, message_bytes, 
           a_coordinate, b_coordinate, byte1, byte2, internal_bits, i >>

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
        /\ n = (Len(bits) \div k)
        /\ acc = defaultInitValue
        /\ i_ = 1
        (* Procedure pad *)
        /\ i_p = 1
        (* Procedure hash_to_pallas *)
        /\ separator = defaultInitValue
        /\ message_bytes = defaultInitValue
        /\ a_coordinate = 0
        /\ b_coordinate = 0
        (* Procedure IntToLEOSP *)
        /\ byte1 = 0
        /\ byte2 = 0
        /\ internal_bits = <<>>
        (* Procedure bytes_to_characters *)
        /\ i = 1
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
                                               n, acc, i_, i_p, separator, 
                                               message_bytes, a_coordinate, 
                                               b_coordinate, byte1, byte2, 
                                               internal_bits, i >>

DomainStringToBytesAssign == /\ pc = "DomainStringToBytesAssign"
                             /\ domain_bytes' = bytes
                             /\ pc' = "MessageCharactersToBytesCall"
                             /\ UNCHANGED << point, characters, bytes, bits, 
                                             slices, stack, domain, message, n, 
                                             acc, i_, i_p, separator, 
                                             message_bytes, a_coordinate, 
                                             b_coordinate, byte1, byte2, 
                                             internal_bits, i >>

MessageCharactersToBytesCall == /\ pc = "MessageCharactersToBytesCall"
                                /\ characters' = message
                                /\ stack' = << [ procedure |->  "characters_to_bytes",
                                                 pc        |->  "MessageBytesToBitsCall" ] >>
                                             \o stack
                                /\ pc' = "FlushBytes"
                                /\ UNCHANGED << point, bytes, bits, slices, 
                                                domain, message, domain_bytes, 
                                                n, acc, i_, i_p, separator, 
                                                message_bytes, a_coordinate, 
                                                b_coordinate, byte1, byte2, 
                                                internal_bits, i >>

MessageBytesToBitsCall == /\ pc = "MessageBytesToBitsCall"
                          /\ stack' = << [ procedure |->  "bytes_to_bits",
                                           pc        |->  "SinsemillaHashToPoint" ] >>
                                       \o stack
                          /\ pc' = "FlushBits"
                          /\ UNCHANGED << point, characters, bytes, bits, 
                                          slices, domain, message, 
                                          domain_bytes, n, acc, i_, i_p, 
                                          separator, message_bytes, 
                                          a_coordinate, b_coordinate, byte1, 
                                          byte2, internal_bits, i >>

SinsemillaHashToPoint == /\ pc = "SinsemillaHashToPoint"
                         /\ bytes' = domain_bytes
                         /\ stack' = << [ procedure |->  "sinsemilla_hash_to_point",
                                          pc        |->  "OutputPointToBytes",
                                          n         |->  n,
                                          acc       |->  acc,
                                          i_        |->  i_ ] >>
                                      \o stack
                         /\ n' = (Len(bits) \div k)
                         /\ acc' = defaultInitValue
                         /\ i_' = 1
                         /\ pc' = "CallPad"
                         /\ UNCHANGED << point, characters, bits, slices, 
                                         domain, message, domain_bytes, i_p, 
                                         separator, message_bytes, 
                                         a_coordinate, b_coordinate, byte1, 
                                         byte2, internal_bits, i >>

OutputPointToBytes == /\ pc = "OutputPointToBytes"
                      /\ stack' = << [ procedure |->  "point_to_bytes",
                                       pc        |->  "OutputBytesToCharacters" ] >>
                                   \o stack
                      /\ pc' = "PointToBytes"
                      /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                      domain, message, domain_bytes, n, acc, 
                                      i_, i_p, separator, message_bytes, 
                                      a_coordinate, b_coordinate, byte1, byte2, 
                                      internal_bits, i >>

OutputBytesToCharacters == /\ pc = "OutputBytesToCharacters"
                           /\ stack' = << [ procedure |->  "bytes_to_characters",
                                            pc        |->  "Return_",
                                            i         |->  i ] >>
                                        \o stack
                           /\ i' = 1
                           /\ pc' = "FlushCharacters"
                           /\ UNCHANGED << point, characters, bytes, bits, 
                                           slices, domain, message, 
                                           domain_bytes, n, acc, i_, i_p, 
                                           separator, message_bytes, 
                                           a_coordinate, b_coordinate, byte1, 
                                           byte2, internal_bits >>

Return_ == /\ pc = "Return_"
           /\ PrintT(characters)
           /\ pc' = Head(stack).pc
           /\ domain_bytes' = Head(stack).domain_bytes
           /\ domain' = Head(stack).domain
           /\ message' = Head(stack).message
           /\ stack' = Tail(stack)
           /\ UNCHANGED << point, characters, bytes, bits, slices, n, acc, i_, 
                           i_p, separator, message_bytes, a_coordinate, 
                           b_coordinate, byte1, byte2, internal_bits, i >>

sinsemilla_hash == DomainCharactersToBytesCall \/ DomainStringToBytesAssign
                      \/ MessageCharactersToBytesCall
                      \/ MessageBytesToBitsCall \/ SinsemillaHashToPoint
                      \/ OutputPointToBytes \/ OutputBytesToCharacters
                      \/ Return_

FlushBytes == /\ pc = "FlushBytes"
              /\ bytes' = <<>>
              /\ pc' = "StringToBytes"
              /\ UNCHANGED << point, characters, bits, slices, stack, domain, 
                              message, domain_bytes, n, acc, i_, i_p, 
                              separator, message_bytes, a_coordinate, 
                              b_coordinate, byte1, byte2, internal_bits, i >>

StringToBytes == /\ pc = "StringToBytes"
                 /\ bytes' = [c \in 1..Len(characters) |-> Ord(characters[c])]
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << point, characters, bits, slices, domain, 
                                 message, domain_bytes, n, acc, i_, i_p, 
                                 separator, message_bytes, a_coordinate, 
                                 b_coordinate, byte1, byte2, internal_bits, i >>

characters_to_bytes == FlushBytes \/ StringToBytes

FlushBits == /\ pc = "FlushBits"
             /\ bits' = <<>>
             /\ pc' = "BytesToBitSequence"
             /\ UNCHANGED << point, characters, bytes, slices, stack, domain, 
                             message, domain_bytes, n, acc, i_, i_p, separator, 
                             message_bytes, a_coordinate, b_coordinate, byte1, 
                             byte2, internal_bits, i >>

BytesToBitSequence == /\ pc = "BytesToBitSequence"
                      /\ bits' = [byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])]
                      /\ pc' = "Flatten"
                      /\ UNCHANGED << point, characters, bytes, slices, stack, 
                                      domain, message, domain_bytes, n, acc, 
                                      i_, i_p, separator, message_bytes, 
                                      a_coordinate, b_coordinate, byte1, byte2, 
                                      internal_bits, i >>

Flatten == /\ pc = "Flatten"
           /\ bits' = FlattenSeq(bits)
           /\ pc' = Head(stack).pc
           /\ stack' = Tail(stack)
           /\ UNCHANGED << point, characters, bytes, slices, domain, message, 
                           domain_bytes, n, acc, i_, i_p, separator, 
                           message_bytes, a_coordinate, b_coordinate, byte1, 
                           byte2, internal_bits, i >>

bytes_to_bits == FlushBits \/ BytesToBitSequence \/ Flatten

CallPad == /\ pc = "CallPad"
           /\ stack' = << [ procedure |->  "pad",
                            pc        |->  "CallQ",
                            i_p       |->  i_p ] >>
                        \o stack
           /\ i_p' = 1
           /\ pc' = "GetSlices"
           /\ UNCHANGED << point, characters, bytes, bits, slices, domain, 
                           message, domain_bytes, n, acc, i_, separator, 
                           message_bytes, a_coordinate, b_coordinate, byte1, 
                           byte2, internal_bits, i >>

CallQ == /\ pc = "CallQ"
         /\ stack' = << [ procedure |->  "q",
                          pc        |->  "InitializeAcc" ] >>
                      \o stack
         /\ pc' = "Q"
         /\ UNCHANGED << point, characters, bytes, bits, slices, domain, 
                         message, domain_bytes, n, acc, i_, i_p, separator, 
                         message_bytes, a_coordinate, b_coordinate, byte1, 
                         byte2, internal_bits, i >>

InitializeAcc == /\ pc = "InitializeAcc"
                 /\ acc' = point
                 /\ pc' = "Loop"
                 /\ UNCHANGED << point, characters, bytes, bits, slices, stack, 
                                 domain, message, domain_bytes, n, i_, i_p, 
                                 separator, message_bytes, a_coordinate, 
                                 b_coordinate, byte1, byte2, internal_bits, i >>

Loop == /\ pc = "Loop"
        /\ IF i_ <= n
              THEN /\ pc' = "CallS"
                   /\ UNCHANGED << point, i_ >>
              ELSE /\ point' = acc
                   /\ PrintT(point')
                   /\ i_' = 1
                   /\ pc' = "ReturnFromSinsemillaHashToPoint"
        /\ UNCHANGED << characters, bytes, bits, slices, stack, domain, 
                        message, domain_bytes, n, acc, i_p, separator, 
                        message_bytes, a_coordinate, b_coordinate, byte1, 
                        byte2, internal_bits, i >>

CallS == /\ pc = "CallS"
         /\ bits' = slices[i_]
         /\ stack' = << [ procedure |->  "s",
                          pc        |->  "IncompleteAdditions" ] >>
                      \o stack
         /\ pc' = "CallI2LEOSP"
         /\ UNCHANGED << point, characters, bytes, slices, domain, message, 
                         domain_bytes, n, acc, i_, i_p, separator, 
                         message_bytes, a_coordinate, b_coordinate, byte1, 
                         byte2, internal_bits, i >>

IncompleteAdditions == /\ pc = "IncompleteAdditions"
                       /\ acc' = IncompleteAddition(IncompleteAddition(acc, point), acc)
                       /\ pc' = "Inc"
                       /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                       stack, domain, message, domain_bytes, n, 
                                       i_, i_p, separator, message_bytes, 
                                       a_coordinate, b_coordinate, byte1, 
                                       byte2, internal_bits, i >>

Inc == /\ pc = "Inc"
       /\ i_' = i_ + 1
       /\ pc' = "Loop"
       /\ UNCHANGED << point, characters, bytes, bits, slices, stack, domain, 
                       message, domain_bytes, n, acc, i_p, separator, 
                       message_bytes, a_coordinate, b_coordinate, byte1, byte2, 
                       internal_bits, i >>

ReturnFromSinsemillaHashToPoint == /\ pc = "ReturnFromSinsemillaHashToPoint"
                                   /\ pc' = Head(stack).pc
                                   /\ n' = Head(stack).n
                                   /\ acc' = Head(stack).acc
                                   /\ i_' = Head(stack).i_
                                   /\ stack' = Tail(stack)
                                   /\ UNCHANGED << point, characters, bytes, 
                                                   bits, slices, domain, 
                                                   message, domain_bytes, i_p, 
                                                   separator, message_bytes, 
                                                   a_coordinate, b_coordinate, 
                                                   byte1, byte2, internal_bits, 
                                                   i >>

sinsemilla_hash_to_point == CallPad \/ CallQ \/ InitializeAcc \/ Loop
                               \/ CallS \/ IncompleteAdditions \/ Inc
                               \/ ReturnFromSinsemillaHashToPoint

GetSlices == /\ pc = "GetSlices"
             /\ IF i_p <= Len(bits)
                   THEN /\ IF i_p+k >= Len(bits)
                              THEN /\ slices' = Append(slices, SubSeq(bits, i_p, Len(bits)))
                                   /\ i_p' = Len(bits) + 1
                              ELSE /\ slices' = Append(slices, SubSeq(bits, i_p, i_p+k))
                                   /\ i_p' = i_p+k
                        /\ pc' = "GetSlices"
                   ELSE /\ IF Len(slices[Len(slices)]) < k
                              THEN /\ pc' = "PadLastSlice"
                              ELSE /\ pc' = "ReturnFromPad"
                        /\ UNCHANGED << slices, i_p >>
             /\ UNCHANGED << point, characters, bytes, bits, stack, domain, 
                             message, domain_bytes, n, acc, i_, separator, 
                             message_bytes, a_coordinate, b_coordinate, byte1, 
                             byte2, internal_bits, i >>

PadLastSlice == /\ pc = "PadLastSlice"
                /\ IF Len(slices[Len(slices)]) < k
                      THEN /\ slices' = [slices EXCEPT ![Len(slices)] = Append(slices[Len(slices)], 0)]
                           /\ pc' = "PadLastSlice"
                      ELSE /\ pc' = "ReturnFromPad"
                           /\ UNCHANGED slices
                /\ UNCHANGED << point, characters, bytes, bits, stack, domain, 
                                message, domain_bytes, n, acc, i_, i_p, 
                                separator, message_bytes, a_coordinate, 
                                b_coordinate, byte1, byte2, internal_bits, i >>

ReturnFromPad == /\ pc = "ReturnFromPad"
                 /\ pc' = Head(stack).pc
                 /\ i_p' = Head(stack).i_p
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                 domain, message, domain_bytes, n, acc, i_, 
                                 separator, message_bytes, a_coordinate, 
                                 b_coordinate, byte1, byte2, internal_bits, i >>

pad == GetSlices \/ PadLastSlice \/ ReturnFromPad

Q == /\ pc = "Q"
     /\ /\ message_bytes' = bytes
        /\ separator' = sinsemilla_q_separator
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         a_coordinate |->  a_coordinate,
                         b_coordinate |->  b_coordinate,
                         separator |->  separator,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ a_coordinate' = 0
     /\ b_coordinate' = 0
     /\ pc' = "HashToPallas"
     /\ UNCHANGED << point, characters, bytes, bits, slices, domain, message, 
                     domain_bytes, n, acc, i_, i_p, byte1, byte2, 
                     internal_bits, i >>

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
                               message, domain_bytes, n, acc, i_, i_p, 
                               separator, message_bytes, a_coordinate, 
                               b_coordinate, i >>

S == /\ pc = "S"
     /\ /\ message_bytes' = bytes
        /\ separator' = sinsemilla_s_separator
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         a_coordinate |->  a_coordinate,
                         b_coordinate |->  b_coordinate,
                         separator |->  separator,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ a_coordinate' = 0
     /\ b_coordinate' = 0
     /\ pc' = "HashToPallas"
     /\ UNCHANGED << point, characters, bytes, bits, slices, domain, message, 
                     domain_bytes, n, acc, i_, i_p, byte1, byte2, 
                     internal_bits, i >>

s == CallI2LEOSP \/ S

HashToPallas == /\ pc = "HashToPallas"
                /\ a_coordinate' = (CHOOSE r \in RandomSubset(1, 1..3) : TRUE)
                /\ b_coordinate' = (CHOOSE r \in RandomSubset(1, 1..3) : TRUE)
                /\ point' = [a |-> a_coordinate', b |-> b_coordinate', baseX |-> baseX, baseY |-> baseY]
                /\ pc' = "Return_h"
                /\ UNCHANGED << characters, bytes, bits, slices, stack, domain, 
                                message, domain_bytes, n, acc, i_, i_p, 
                                separator, message_bytes, byte1, byte2, 
                                internal_bits, i >>

Return_h == /\ pc = "Return_h"
            /\ pc' = Head(stack).pc
            /\ a_coordinate' = Head(stack).a_coordinate
            /\ b_coordinate' = Head(stack).b_coordinate
            /\ separator' = Head(stack).separator
            /\ message_bytes' = Head(stack).message_bytes
            /\ stack' = Tail(stack)
            /\ UNCHANGED << point, characters, bytes, bits, slices, domain, 
                            message, domain_bytes, n, acc, i_, i_p, byte1, 
                            byte2, internal_bits, i >>

hash_to_pallas == HashToPallas \/ Return_h

DoIntToLEOSP == /\ pc = "DoIntToLEOSP"
                /\ byte1' = BitSequenceToByte(SubSeq(bits, 1, 8))
                /\ internal_bits' = SubSeq(bits, 9, 10)
                /\ bits' = <<internal_bits'[1], internal_bits'[2], 0, 0, 0, 0, 0, 0>>
                /\ byte2' = BitSequenceToByte(bits')
                /\ bytes' = <<byte1', byte2', 0, 0>>
                /\ pc' = "Return"
                /\ UNCHANGED << point, characters, slices, stack, domain, 
                                message, domain_bytes, n, acc, i_, i_p, 
                                separator, message_bytes, a_coordinate, 
                                b_coordinate, i >>

Return == /\ pc = "Return"
          /\ pc' = Head(stack).pc
          /\ byte1' = Head(stack).byte1
          /\ byte2' = Head(stack).byte2
          /\ internal_bits' = Head(stack).internal_bits
          /\ stack' = Tail(stack)
          /\ UNCHANGED << point, characters, bytes, bits, slices, domain, 
                          message, domain_bytes, n, acc, i_, i_p, separator, 
                          message_bytes, a_coordinate, b_coordinate, i >>

IntToLEOSP == DoIntToLEOSP \/ Return

FlushCharacters == /\ pc = "FlushCharacters"
                   /\ characters' = ""
                   /\ pc' = "BytesToCharacters"
                   /\ UNCHANGED << point, bytes, bits, slices, stack, domain, 
                                   message, domain_bytes, n, acc, i_, i_p, 
                                   separator, message_bytes, a_coordinate, 
                                   b_coordinate, byte1, byte2, internal_bits, 
                                   i >>

BytesToCharacters == /\ pc = "BytesToCharacters"
                     /\ characters' = [b \in 1..Len(bytes) |-> Chr(bytes[b])]
                     /\ pc' = Head(stack).pc
                     /\ i' = Head(stack).i
                     /\ stack' = Tail(stack)
                     /\ UNCHANGED << point, bytes, bits, slices, domain, 
                                     message, domain_bytes, n, acc, i_, i_p, 
                                     separator, message_bytes, a_coordinate, 
                                     b_coordinate, byte1, byte2, internal_bits >>

bytes_to_characters == FlushCharacters \/ BytesToCharacters

PointToBytes == /\ pc = "PointToBytes"
                /\ bytes' = <<point.a, point.b, point.baseX, point.baseY>>
                /\ PrintT(bytes')
                /\ pc' = Head(stack).pc
                /\ stack' = Tail(stack)
                /\ UNCHANGED << point, characters, bits, slices, domain, 
                                message, domain_bytes, n, acc, i_, i_p, 
                                separator, message_bytes, a_coordinate, 
                                b_coordinate, byte1, byte2, internal_bits, i >>

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
                                      n, acc, i_, i_p, separator, 
                                      message_bytes, a_coordinate, 
                                      b_coordinate, byte1, byte2, 
                                      internal_bits, i >>

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
