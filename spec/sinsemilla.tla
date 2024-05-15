---- MODULE sinsemilla ----
EXTENDS TLC, Naturals, Integers, Sequences, Utils

(*--algorithm sinsemilla

variables
    point = [a |-> 0, b |-> 0, baseX |-> 0, baseY |-> 0];
    characters = <<>>;
    bytes = <<>>;
    bits = <<>>;
    string = "";
    slices = <<>>;
    
define
    \* Pallas base point x-coordinate
    baseX == "0x01"

    \* Pallas base point y-coordinate
    baseY == "0xbb2aedca237acf1971473d33d45b658f54ee7863f0a9df537c93120aa3b5741b"

    \* The number of bits in a chunk
    k == 10

    \* The incomplete addition operator
    IncompleteAddition(x, y) == [a |-> x.a \o "+" \o y.a, b |-> x.b \o "+" \o y.b, baseX |-> baseX, baseY |-> baseY]
end define;

procedure sinsemilla_hash(domain_string, message_string)
variables domain_bytes = <<>>;
begin
    DomainToCharacters: \* 1
        skip;
    DomainStringToBytesCall: \* 2
        characters := domain_string;
        call characters_to_bytes();
    DomainStringToBytesAssign: \* 3
        domain_bytes := bytes;
    MessageStringToCharactersCall: \* 4
        skip;
    MessageCharactersToBytesCall: \* 5
        characters := message_string;
        call characters_to_bytes();
    MessageBytesToBitsCall: \* 6
        call bytes_to_bits();
    SinsemillaHashToPoint: \* ...
        bytes := domain_bytes;
        call sinsemilla_hash_to_point();
    OutputPointToBytes:
        call point_to_bytes();
    OutputBytesToCharacters:
        skip;
    OutputCharactersToString:
        skip;
    Return:
        print string;
        return;
end procedure;

\* Convert a sequence of characters to a sequence of bytes.
procedure characters_to_bytes()
begin
    FlushBytes:
        bytes := <<>>;
    StringToBytes:
        \* Convert each ASCII character to its byte value
        bytes := [c \in 1..Len(characters) |-> Ord(characters[c])];
        return;
end procedure;

\* Convert a sequence of bytes to a flat sequence of bits.
procedure bytes_to_bits()
variables i = 1, j = 1, flatten1 = <<>>, flatten2 = <<>>;
begin
    InitializeBits:
        bits := <<>>;
    BytesToBitSequence:
        bits := [byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])];
    Flatten:
        bits := FlattenSeq(bits);
        return;
end procedure;

\* Convert the message bits into a Pallas point, using the domain bytes as the domain separator.
procedure sinsemilla_hash_to_point()
variables 
    n, 
    acc,
    i = 1,
    first_incomplete_addition,
    second_incomplete_addition;
begin
    CalculateN:
        n := Len(bits) \div k;
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
            FirstIncompleteAddition:
                print point;
                first_incomplete_addition := IncompleteAddition(acc, point);
            SecondIncompleteAddition: 
                second_incomplete_addition := IncompleteAddition(first_incomplete_addition, acc);
                acc := second_incomplete_addition;
            Inc:
                i := i + 1;
        end while;
    Results:
        point := second_incomplete_addition;
    CleanIndex:
        i := 1;
    Return:
        return;
end procedure;

\* Pad the message bits with zeros until the length is a multiple of k. Create chunks of k bits.
procedure pad()
variables
    i = 1,
    last_slice = <<>>,
    slice = <<>>;
begin
    Padding:
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
    Return:
        return;
end procedure;

procedure q()
begin
    Q:
        call hash_to_pallas("z.cash.SinsemillaQ", bytes);
        return;
end procedure;

procedure s()
begin
    CallI2LEOSP:
        call IntToLEOSP();
    S:
        call hash_to_pallas("z.cash:SinsemillaS", bytes);
        return;
end procedure;

procedure hash_to_pallas(domain_string, message_bytes)
begin
    BytesToString:
        bytes := message_bytes;
        call bytes_to_string();
    HashToPallas:
        point := [a |-> domain_string, b |-> string, baseX |-> baseX, baseY |-> baseY];
        \*print point;
        return;
end procedure;

\* Integer to Little-Endian Octet String Pairing
procedure IntToLEOSP()
variables one_byte = 0, second_byte = 0;
begin
    GetFirstByte:
        one_byte := BitSequenceToByte(SubSeq(bits, 1, 8));
    BuildSecondByte:
        bits := SubSeq(bits, 9, 10);
    AddZeroes:
        while Len(bits) < 8 do
            bits := Append(bits, 0);
        end while;
    GetSecondByte:
        second_byte := BitSequenceToByte(bits);
    Bytes:
        bytes := <<one_byte, second_byte, 0, 0>>;
    return;
end procedure;

\* Convert a sequence of bytes to a string
procedure bytes_to_string()
variables 
    i = 1;
begin
    FlushString:
        string := "";
    BytesToCharacters:
        \* Convert each byte to its ASCII character
        characters := [b \in 1..Len(bytes) |-> Chr(bytes[b])];
    CharactersToString:
        while i <= Len(characters) do
            string := string \o characters[i];
            i := i + 1;
        end while;
        \* print string;
        return;
end procedure;

procedure point_to_bytes()
begin
    PointToBytes:
        \*bytes := <<point.a, point.b, point.baseX, point.baseY>>;
        return;
end procedure;

begin
    SinSemillaHashCall:
        call sinsemilla_hash(<<"d", "o", "m", "a", "i", "n">>, <<"m", "e", "s", "s", "a", "g", "e">>);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "47f49989" /\ chksum(tla) = "df937d62")
\* Label Return of procedure sinsemilla_hash at line 55 col 9 changed to Return_
\* Label Return of procedure sinsemilla_hash_to_point at line 120 col 9 changed to Return_s
\* Procedure variable i of procedure bytes_to_bits at line 72 col 11 changed to i_
\* Procedure variable i of procedure sinsemilla_hash_to_point at line 88 col 5 changed to i_s
\* Procedure variable i of procedure pad at line 126 col 5 changed to i_p
\* Parameter domain_string of procedure sinsemilla_hash at line 28 col 27 changed to domain_string_
CONSTANT defaultInitValue
VARIABLES point, characters, bytes, bits, string, slices, pc, stack

(* define statement *)
baseX == "0x01"


baseY == "0xbb2aedca237acf1971473d33d45b658f54ee7863f0a9df537c93120aa3b5741b"


k == 10


IncompleteAddition(x, y) == [a |-> x.a \o "+" \o y.a, b |-> x.b \o "+" \o y.b, baseX |-> baseX, baseY |-> baseY]

VARIABLES domain_string_, message_string, domain_bytes, i_, j, flatten1, 
          flatten2, n, acc, i_s, first_incomplete_addition, 
          second_incomplete_addition, i_p, last_slice, slice, domain_string, 
          message_bytes, one_byte, second_byte, i

vars == << point, characters, bytes, bits, string, slices, pc, stack, 
           domain_string_, message_string, domain_bytes, i_, j, flatten1, 
           flatten2, n, acc, i_s, first_incomplete_addition, 
           second_incomplete_addition, i_p, last_slice, slice, domain_string, 
           message_bytes, one_byte, second_byte, i >>

Init == (* Global variables *)
        /\ point = [a |-> 0, b |-> 0, baseX |-> 0, baseY |-> 0]
        /\ characters = <<>>
        /\ bytes = <<>>
        /\ bits = <<>>
        /\ string = ""
        /\ slices = <<>>
        (* Procedure sinsemilla_hash *)
        /\ domain_string_ = defaultInitValue
        /\ message_string = defaultInitValue
        /\ domain_bytes = <<>>
        (* Procedure bytes_to_bits *)
        /\ i_ = 1
        /\ j = 1
        /\ flatten1 = <<>>
        /\ flatten2 = <<>>
        (* Procedure sinsemilla_hash_to_point *)
        /\ n = defaultInitValue
        /\ acc = defaultInitValue
        /\ i_s = 1
        /\ first_incomplete_addition = defaultInitValue
        /\ second_incomplete_addition = defaultInitValue
        (* Procedure pad *)
        /\ i_p = 1
        /\ last_slice = <<>>
        /\ slice = <<>>
        (* Procedure hash_to_pallas *)
        /\ domain_string = defaultInitValue
        /\ message_bytes = defaultInitValue
        (* Procedure IntToLEOSP *)
        /\ one_byte = 0
        /\ second_byte = 0
        (* Procedure bytes_to_string *)
        /\ i = 1
        /\ stack = << >>
        /\ pc = "SinSemillaHashCall"

DomainToCharacters == /\ pc = "DomainToCharacters"
                      /\ TRUE
                      /\ pc' = "DomainStringToBytesCall"
                      /\ UNCHANGED << point, characters, bytes, bits, string, 
                                      slices, stack, domain_string_, 
                                      message_string, domain_bytes, i_, j, 
                                      flatten1, flatten2, n, acc, i_s, 
                                      first_incomplete_addition, 
                                      second_incomplete_addition, i_p, 
                                      last_slice, slice, domain_string, 
                                      message_bytes, one_byte, second_byte, i >>

DomainStringToBytesCall == /\ pc = "DomainStringToBytesCall"
                           /\ characters' = domain_string_
                           /\ stack' = << [ procedure |->  "characters_to_bytes",
                                            pc        |->  "DomainStringToBytesAssign" ] >>
                                        \o stack
                           /\ pc' = "FlushBytes"
                           /\ UNCHANGED << point, bytes, bits, string, slices, 
                                           domain_string_, message_string, 
                                           domain_bytes, i_, j, flatten1, 
                                           flatten2, n, acc, i_s, 
                                           first_incomplete_addition, 
                                           second_incomplete_addition, i_p, 
                                           last_slice, slice, domain_string, 
                                           message_bytes, one_byte, 
                                           second_byte, i >>

DomainStringToBytesAssign == /\ pc = "DomainStringToBytesAssign"
                             /\ domain_bytes' = bytes
                             /\ pc' = "MessageStringToCharactersCall"
                             /\ UNCHANGED << point, characters, bytes, bits, 
                                             string, slices, stack, 
                                             domain_string_, message_string, 
                                             i_, j, flatten1, flatten2, n, acc, 
                                             i_s, first_incomplete_addition, 
                                             second_incomplete_addition, i_p, 
                                             last_slice, slice, domain_string, 
                                             message_bytes, one_byte, 
                                             second_byte, i >>

MessageStringToCharactersCall == /\ pc = "MessageStringToCharactersCall"
                                 /\ TRUE
                                 /\ pc' = "MessageCharactersToBytesCall"
                                 /\ UNCHANGED << point, characters, bytes, 
                                                 bits, string, slices, stack, 
                                                 domain_string_, 
                                                 message_string, domain_bytes, 
                                                 i_, j, flatten1, flatten2, n, 
                                                 acc, i_s, 
                                                 first_incomplete_addition, 
                                                 second_incomplete_addition, 
                                                 i_p, last_slice, slice, 
                                                 domain_string, message_bytes, 
                                                 one_byte, second_byte, i >>

MessageCharactersToBytesCall == /\ pc = "MessageCharactersToBytesCall"
                                /\ characters' = message_string
                                /\ stack' = << [ procedure |->  "characters_to_bytes",
                                                 pc        |->  "MessageBytesToBitsCall" ] >>
                                             \o stack
                                /\ pc' = "FlushBytes"
                                /\ UNCHANGED << point, bytes, bits, string, 
                                                slices, domain_string_, 
                                                message_string, domain_bytes, 
                                                i_, j, flatten1, flatten2, n, 
                                                acc, i_s, 
                                                first_incomplete_addition, 
                                                second_incomplete_addition, 
                                                i_p, last_slice, slice, 
                                                domain_string, message_bytes, 
                                                one_byte, second_byte, i >>

MessageBytesToBitsCall == /\ pc = "MessageBytesToBitsCall"
                          /\ stack' = << [ procedure |->  "bytes_to_bits",
                                           pc        |->  "SinsemillaHashToPoint",
                                           i_        |->  i_,
                                           j         |->  j,
                                           flatten1  |->  flatten1,
                                           flatten2  |->  flatten2 ] >>
                                       \o stack
                          /\ i_' = 1
                          /\ j' = 1
                          /\ flatten1' = <<>>
                          /\ flatten2' = <<>>
                          /\ pc' = "InitializeBits"
                          /\ UNCHANGED << point, characters, bytes, bits, 
                                          string, slices, domain_string_, 
                                          message_string, domain_bytes, n, acc, 
                                          i_s, first_incomplete_addition, 
                                          second_incomplete_addition, i_p, 
                                          last_slice, slice, domain_string, 
                                          message_bytes, one_byte, second_byte, 
                                          i >>

SinsemillaHashToPoint == /\ pc = "SinsemillaHashToPoint"
                         /\ bytes' = domain_bytes
                         /\ stack' = << [ procedure |->  "sinsemilla_hash_to_point",
                                          pc        |->  "OutputPointToBytes",
                                          n         |->  n,
                                          acc       |->  acc,
                                          i_s       |->  i_s,
                                          first_incomplete_addition |->  first_incomplete_addition,
                                          second_incomplete_addition |->  second_incomplete_addition ] >>
                                      \o stack
                         /\ n' = defaultInitValue
                         /\ acc' = defaultInitValue
                         /\ i_s' = 1
                         /\ first_incomplete_addition' = defaultInitValue
                         /\ second_incomplete_addition' = defaultInitValue
                         /\ pc' = "CalculateN"
                         /\ UNCHANGED << point, characters, bits, string, 
                                         slices, domain_string_, 
                                         message_string, domain_bytes, i_, j, 
                                         flatten1, flatten2, i_p, last_slice, 
                                         slice, domain_string, message_bytes, 
                                         one_byte, second_byte, i >>

OutputPointToBytes == /\ pc = "OutputPointToBytes"
                      /\ stack' = << [ procedure |->  "point_to_bytes",
                                       pc        |->  "OutputBytesToCharacters" ] >>
                                   \o stack
                      /\ pc' = "PointToBytes"
                      /\ UNCHANGED << point, characters, bytes, bits, string, 
                                      slices, domain_string_, message_string, 
                                      domain_bytes, i_, j, flatten1, flatten2, 
                                      n, acc, i_s, first_incomplete_addition, 
                                      second_incomplete_addition, i_p, 
                                      last_slice, slice, domain_string, 
                                      message_bytes, one_byte, second_byte, i >>

OutputBytesToCharacters == /\ pc = "OutputBytesToCharacters"
                           /\ TRUE
                           /\ pc' = "OutputCharactersToString"
                           /\ UNCHANGED << point, characters, bytes, bits, 
                                           string, slices, stack, 
                                           domain_string_, message_string, 
                                           domain_bytes, i_, j, flatten1, 
                                           flatten2, n, acc, i_s, 
                                           first_incomplete_addition, 
                                           second_incomplete_addition, i_p, 
                                           last_slice, slice, domain_string, 
                                           message_bytes, one_byte, 
                                           second_byte, i >>

OutputCharactersToString == /\ pc = "OutputCharactersToString"
                            /\ TRUE
                            /\ pc' = "Return_"
                            /\ UNCHANGED << point, characters, bytes, bits, 
                                            string, slices, stack, 
                                            domain_string_, message_string, 
                                            domain_bytes, i_, j, flatten1, 
                                            flatten2, n, acc, i_s, 
                                            first_incomplete_addition, 
                                            second_incomplete_addition, i_p, 
                                            last_slice, slice, domain_string, 
                                            message_bytes, one_byte, 
                                            second_byte, i >>

Return_ == /\ pc = "Return_"
           /\ PrintT(string)
           /\ pc' = Head(stack).pc
           /\ domain_bytes' = Head(stack).domain_bytes
           /\ domain_string_' = Head(stack).domain_string_
           /\ message_string' = Head(stack).message_string
           /\ stack' = Tail(stack)
           /\ UNCHANGED << point, characters, bytes, bits, string, slices, i_, 
                           j, flatten1, flatten2, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, i_p, last_slice, slice, 
                           domain_string, message_bytes, one_byte, second_byte, 
                           i >>

sinsemilla_hash == DomainToCharacters \/ DomainStringToBytesCall
                      \/ DomainStringToBytesAssign
                      \/ MessageStringToCharactersCall
                      \/ MessageCharactersToBytesCall
                      \/ MessageBytesToBitsCall \/ SinsemillaHashToPoint
                      \/ OutputPointToBytes \/ OutputBytesToCharacters
                      \/ OutputCharactersToString \/ Return_

FlushBytes == /\ pc = "FlushBytes"
              /\ bytes' = <<>>
              /\ pc' = "StringToBytes"
              /\ UNCHANGED << point, characters, bits, string, slices, stack, 
                              domain_string_, message_string, domain_bytes, i_, 
                              j, flatten1, flatten2, n, acc, i_s, 
                              first_incomplete_addition, 
                              second_incomplete_addition, i_p, last_slice, 
                              slice, domain_string, message_bytes, one_byte, 
                              second_byte, i >>

StringToBytes == /\ pc = "StringToBytes"
                 /\ bytes' = [c \in 1..Len(characters) |-> Ord(characters[c])]
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << point, characters, bits, string, slices, 
                                 domain_string_, message_string, domain_bytes, 
                                 i_, j, flatten1, flatten2, n, acc, i_s, 
                                 first_incomplete_addition, 
                                 second_incomplete_addition, i_p, last_slice, 
                                 slice, domain_string, message_bytes, one_byte, 
                                 second_byte, i >>

characters_to_bytes == FlushBytes \/ StringToBytes

InitializeBits == /\ pc = "InitializeBits"
                  /\ bits' = <<>>
                  /\ pc' = "BytesToBitSequence"
                  /\ UNCHANGED << point, characters, bytes, string, slices, 
                                  stack, domain_string_, message_string, 
                                  domain_bytes, i_, j, flatten1, flatten2, n, 
                                  acc, i_s, first_incomplete_addition, 
                                  second_incomplete_addition, i_p, last_slice, 
                                  slice, domain_string, message_bytes, 
                                  one_byte, second_byte, i >>

BytesToBitSequence == /\ pc = "BytesToBitSequence"
                      /\ bits' = [byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])]
                      /\ pc' = "Flatten"
                      /\ UNCHANGED << point, characters, bytes, string, slices, 
                                      stack, domain_string_, message_string, 
                                      domain_bytes, i_, j, flatten1, flatten2, 
                                      n, acc, i_s, first_incomplete_addition, 
                                      second_incomplete_addition, i_p, 
                                      last_slice, slice, domain_string, 
                                      message_bytes, one_byte, second_byte, i >>

Flatten == /\ pc = "Flatten"
           /\ bits' = FlattenSeq(bits)
           /\ pc' = Head(stack).pc
           /\ i_' = Head(stack).i_
           /\ j' = Head(stack).j
           /\ flatten1' = Head(stack).flatten1
           /\ flatten2' = Head(stack).flatten2
           /\ stack' = Tail(stack)
           /\ UNCHANGED << point, characters, bytes, string, slices, 
                           domain_string_, message_string, domain_bytes, n, 
                           acc, i_s, first_incomplete_addition, 
                           second_incomplete_addition, i_p, last_slice, slice, 
                           domain_string, message_bytes, one_byte, second_byte, 
                           i >>

bytes_to_bits == InitializeBits \/ BytesToBitSequence \/ Flatten

CalculateN == /\ pc = "CalculateN"
              /\ n' = (Len(bits) \div k)
              /\ pc' = "CallPad"
              /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                              stack, domain_string_, message_string, 
                              domain_bytes, i_, j, flatten1, flatten2, acc, 
                              i_s, first_incomplete_addition, 
                              second_incomplete_addition, i_p, last_slice, 
                              slice, domain_string, message_bytes, one_byte, 
                              second_byte, i >>

CallPad == /\ pc = "CallPad"
           /\ stack' = << [ procedure |->  "pad",
                            pc        |->  "CallQ",
                            i_p       |->  i_p,
                            last_slice |->  last_slice,
                            slice     |->  slice ] >>
                        \o stack
           /\ i_p' = 1
           /\ last_slice' = <<>>
           /\ slice' = <<>>
           /\ pc' = "Padding"
           /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                           domain_string_, message_string, domain_bytes, i_, j, 
                           flatten1, flatten2, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, domain_string, 
                           message_bytes, one_byte, second_byte, i >>

CallQ == /\ pc = "CallQ"
         /\ stack' = << [ procedure |->  "q",
                          pc        |->  "InitializeAcc" ] >>
                      \o stack
         /\ pc' = "Q"
         /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                         domain_string_, message_string, domain_bytes, i_, j, 
                         flatten1, flatten2, n, acc, i_s, 
                         first_incomplete_addition, second_incomplete_addition, 
                         i_p, last_slice, slice, domain_string, message_bytes, 
                         one_byte, second_byte, i >>

InitializeAcc == /\ pc = "InitializeAcc"
                 /\ acc' = point
                 /\ pc' = "Loop"
                 /\ UNCHANGED << point, characters, bytes, bits, string, 
                                 slices, stack, domain_string_, message_string, 
                                 domain_bytes, i_, j, flatten1, flatten2, n, 
                                 i_s, first_incomplete_addition, 
                                 second_incomplete_addition, i_p, last_slice, 
                                 slice, domain_string, message_bytes, one_byte, 
                                 second_byte, i >>

Loop == /\ pc = "Loop"
        /\ IF i_s <= n
              THEN /\ pc' = "CallS"
              ELSE /\ pc' = "Results"
        /\ UNCHANGED << point, characters, bytes, bits, string, slices, stack, 
                        domain_string_, message_string, domain_bytes, i_, j, 
                        flatten1, flatten2, n, acc, i_s, 
                        first_incomplete_addition, second_incomplete_addition, 
                        i_p, last_slice, slice, domain_string, message_bytes, 
                        one_byte, second_byte, i >>

CallS == /\ pc = "CallS"
         /\ bits' = slices[i_s]
         /\ stack' = << [ procedure |->  "s",
                          pc        |->  "FirstIncompleteAddition" ] >>
                      \o stack
         /\ pc' = "CallI2LEOSP"
         /\ UNCHANGED << point, characters, bytes, string, slices, 
                         domain_string_, message_string, domain_bytes, i_, j, 
                         flatten1, flatten2, n, acc, i_s, 
                         first_incomplete_addition, second_incomplete_addition, 
                         i_p, last_slice, slice, domain_string, message_bytes, 
                         one_byte, second_byte, i >>

FirstIncompleteAddition == /\ pc = "FirstIncompleteAddition"
                           /\ PrintT(point)
                           /\ first_incomplete_addition' = IncompleteAddition(acc, point)
                           /\ pc' = "SecondIncompleteAddition"
                           /\ UNCHANGED << point, characters, bytes, bits, 
                                           string, slices, stack, 
                                           domain_string_, message_string, 
                                           domain_bytes, i_, j, flatten1, 
                                           flatten2, n, acc, i_s, 
                                           second_incomplete_addition, i_p, 
                                           last_slice, slice, domain_string, 
                                           message_bytes, one_byte, 
                                           second_byte, i >>

SecondIncompleteAddition == /\ pc = "SecondIncompleteAddition"
                            /\ second_incomplete_addition' = IncompleteAddition(first_incomplete_addition, acc)
                            /\ acc' = second_incomplete_addition'
                            /\ pc' = "Inc"
                            /\ UNCHANGED << point, characters, bytes, bits, 
                                            string, slices, stack, 
                                            domain_string_, message_string, 
                                            domain_bytes, i_, j, flatten1, 
                                            flatten2, n, i_s, 
                                            first_incomplete_addition, i_p, 
                                            last_slice, slice, domain_string, 
                                            message_bytes, one_byte, 
                                            second_byte, i >>

Inc == /\ pc = "Inc"
       /\ i_s' = i_s + 1
       /\ pc' = "Loop"
       /\ UNCHANGED << point, characters, bytes, bits, string, slices, stack, 
                       domain_string_, message_string, domain_bytes, i_, j, 
                       flatten1, flatten2, n, acc, first_incomplete_addition, 
                       second_incomplete_addition, i_p, last_slice, slice, 
                       domain_string, message_bytes, one_byte, second_byte, i >>

Results == /\ pc = "Results"
           /\ point' = second_incomplete_addition
           /\ pc' = "CleanIndex"
           /\ UNCHANGED << characters, bytes, bits, string, slices, stack, 
                           domain_string_, message_string, domain_bytes, i_, j, 
                           flatten1, flatten2, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, i_p, last_slice, slice, 
                           domain_string, message_bytes, one_byte, second_byte, 
                           i >>

CleanIndex == /\ pc = "CleanIndex"
              /\ i_s' = 1
              /\ pc' = "Return_s"
              /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                              stack, domain_string_, message_string, 
                              domain_bytes, i_, j, flatten1, flatten2, n, acc, 
                              first_incomplete_addition, 
                              second_incomplete_addition, i_p, last_slice, 
                              slice, domain_string, message_bytes, one_byte, 
                              second_byte, i >>

Return_s == /\ pc = "Return_s"
            /\ pc' = Head(stack).pc
            /\ n' = Head(stack).n
            /\ acc' = Head(stack).acc
            /\ i_s' = Head(stack).i_s
            /\ first_incomplete_addition' = Head(stack).first_incomplete_addition
            /\ second_incomplete_addition' = Head(stack).second_incomplete_addition
            /\ stack' = Tail(stack)
            /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                            domain_string_, message_string, domain_bytes, i_, 
                            j, flatten1, flatten2, i_p, last_slice, slice, 
                            domain_string, message_bytes, one_byte, 
                            second_byte, i >>

sinsemilla_hash_to_point == CalculateN \/ CallPad \/ CallQ \/ InitializeAcc
                               \/ Loop \/ CallS \/ FirstIncompleteAddition
                               \/ SecondIncompleteAddition \/ Inc
                               \/ Results \/ CleanIndex \/ Return_s

Padding == /\ pc = "Padding"
           /\ IF i_p <= Len(bits)
                 THEN /\ IF i_p+k >= Len(bits)
                            THEN /\ slices' = Append(slices, SubSeq(bits, i_p, Len(bits)))
                                 /\ i_p' = Len(bits) + 1
                            ELSE /\ slices' = Append(slices, SubSeq(bits, i_p, i_p+k))
                                 /\ i_p' = i_p+k
                      /\ pc' = "Padding"
                 ELSE /\ IF Len(slices[Len(slices)]) < k
                            THEN /\ pc' = "PadLastSlice"
                            ELSE /\ pc' = "Return"
                      /\ UNCHANGED << slices, i_p >>
           /\ UNCHANGED << point, characters, bytes, bits, string, stack, 
                           domain_string_, message_string, domain_bytes, i_, j, 
                           flatten1, flatten2, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, last_slice, slice, 
                           domain_string, message_bytes, one_byte, second_byte, 
                           i >>

PadLastSlice == /\ pc = "PadLastSlice"
                /\ IF Len(slices[Len(slices)]) < k
                      THEN /\ slices' = [slices EXCEPT ![Len(slices)] = Append(slices[Len(slices)], 0)]
                           /\ pc' = "PadLastSlice"
                      ELSE /\ pc' = "Return"
                           /\ UNCHANGED slices
                /\ UNCHANGED << point, characters, bytes, bits, string, stack, 
                                domain_string_, message_string, domain_bytes, 
                                i_, j, flatten1, flatten2, n, acc, i_s, 
                                first_incomplete_addition, 
                                second_incomplete_addition, i_p, last_slice, 
                                slice, domain_string, message_bytes, one_byte, 
                                second_byte, i >>

Return == /\ pc = "Return"
          /\ pc' = Head(stack).pc
          /\ i_p' = Head(stack).i_p
          /\ last_slice' = Head(stack).last_slice
          /\ slice' = Head(stack).slice
          /\ stack' = Tail(stack)
          /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                          domain_string_, message_string, domain_bytes, i_, j, 
                          flatten1, flatten2, n, acc, i_s, 
                          first_incomplete_addition, 
                          second_incomplete_addition, domain_string, 
                          message_bytes, one_byte, second_byte, i >>

pad == Padding \/ PadLastSlice \/ Return

Q == /\ pc = "Q"
     /\ /\ domain_string' = "z.cash.SinsemillaQ"
        /\ message_bytes' = bytes
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         domain_string |->  domain_string,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ pc' = "BytesToString"
     /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                     domain_string_, message_string, domain_bytes, i_, j, 
                     flatten1, flatten2, n, acc, i_s, 
                     first_incomplete_addition, second_incomplete_addition, 
                     i_p, last_slice, slice, one_byte, second_byte, i >>

q == Q

CallI2LEOSP == /\ pc = "CallI2LEOSP"
               /\ stack' = << [ procedure |->  "IntToLEOSP",
                                pc        |->  "S",
                                one_byte  |->  one_byte,
                                second_byte |->  second_byte ] >>
                            \o stack
               /\ one_byte' = 0
               /\ second_byte' = 0
               /\ pc' = "GetFirstByte"
               /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                               domain_string_, message_string, domain_bytes, 
                               i_, j, flatten1, flatten2, n, acc, i_s, 
                               first_incomplete_addition, 
                               second_incomplete_addition, i_p, last_slice, 
                               slice, domain_string, message_bytes, i >>

S == /\ pc = "S"
     /\ /\ domain_string' = "z.cash:SinsemillaS"
        /\ message_bytes' = bytes
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         domain_string |->  domain_string,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ pc' = "BytesToString"
     /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                     domain_string_, message_string, domain_bytes, i_, j, 
                     flatten1, flatten2, n, acc, i_s, 
                     first_incomplete_addition, second_incomplete_addition, 
                     i_p, last_slice, slice, one_byte, second_byte, i >>

s == CallI2LEOSP \/ S

BytesToString == /\ pc = "BytesToString"
                 /\ bytes' = message_bytes
                 /\ stack' = << [ procedure |->  "bytes_to_string",
                                  pc        |->  "HashToPallas",
                                  i         |->  i ] >>
                              \o stack
                 /\ i' = 1
                 /\ pc' = "FlushString"
                 /\ UNCHANGED << point, characters, bits, string, slices, 
                                 domain_string_, message_string, domain_bytes, 
                                 i_, j, flatten1, flatten2, n, acc, i_s, 
                                 first_incomplete_addition, 
                                 second_incomplete_addition, i_p, last_slice, 
                                 slice, domain_string, message_bytes, one_byte, 
                                 second_byte >>

HashToPallas == /\ pc = "HashToPallas"
                /\ point' = [a |-> domain_string, b |-> string, baseX |-> baseX, baseY |-> baseY]
                /\ pc' = Head(stack).pc
                /\ domain_string' = Head(stack).domain_string
                /\ message_bytes' = Head(stack).message_bytes
                /\ stack' = Tail(stack)
                /\ UNCHANGED << characters, bytes, bits, string, slices, 
                                domain_string_, message_string, domain_bytes, 
                                i_, j, flatten1, flatten2, n, acc, i_s, 
                                first_incomplete_addition, 
                                second_incomplete_addition, i_p, last_slice, 
                                slice, one_byte, second_byte, i >>

hash_to_pallas == BytesToString \/ HashToPallas

GetFirstByte == /\ pc = "GetFirstByte"
                /\ one_byte' = BitSequenceToByte(SubSeq(bits, 1, 8))
                /\ pc' = "BuildSecondByte"
                /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                                stack, domain_string_, message_string, 
                                domain_bytes, i_, j, flatten1, flatten2, n, 
                                acc, i_s, first_incomplete_addition, 
                                second_incomplete_addition, i_p, last_slice, 
                                slice, domain_string, message_bytes, 
                                second_byte, i >>

BuildSecondByte == /\ pc = "BuildSecondByte"
                   /\ bits' = SubSeq(bits, 9, 10)
                   /\ pc' = "AddZeroes"
                   /\ UNCHANGED << point, characters, bytes, string, slices, 
                                   stack, domain_string_, message_string, 
                                   domain_bytes, i_, j, flatten1, flatten2, n, 
                                   acc, i_s, first_incomplete_addition, 
                                   second_incomplete_addition, i_p, last_slice, 
                                   slice, domain_string, message_bytes, 
                                   one_byte, second_byte, i >>

AddZeroes == /\ pc = "AddZeroes"
             /\ IF Len(bits) < 8
                   THEN /\ bits' = Append(bits, 0)
                        /\ pc' = "AddZeroes"
                   ELSE /\ pc' = "GetSecondByte"
                        /\ bits' = bits
             /\ UNCHANGED << point, characters, bytes, string, slices, stack, 
                             domain_string_, message_string, domain_bytes, i_, 
                             j, flatten1, flatten2, n, acc, i_s, 
                             first_incomplete_addition, 
                             second_incomplete_addition, i_p, last_slice, 
                             slice, domain_string, message_bytes, one_byte, 
                             second_byte, i >>

GetSecondByte == /\ pc = "GetSecondByte"
                 /\ second_byte' = BitSequenceToByte(bits)
                 /\ pc' = "Bytes"
                 /\ UNCHANGED << point, characters, bytes, bits, string, 
                                 slices, stack, domain_string_, message_string, 
                                 domain_bytes, i_, j, flatten1, flatten2, n, 
                                 acc, i_s, first_incomplete_addition, 
                                 second_incomplete_addition, i_p, last_slice, 
                                 slice, domain_string, message_bytes, one_byte, 
                                 i >>

Bytes == /\ pc = "Bytes"
         /\ bytes' = <<one_byte, second_byte, 0, 0>>
         /\ pc' = Head(stack).pc
         /\ one_byte' = Head(stack).one_byte
         /\ second_byte' = Head(stack).second_byte
         /\ stack' = Tail(stack)
         /\ UNCHANGED << point, characters, bits, string, slices, 
                         domain_string_, message_string, domain_bytes, i_, j, 
                         flatten1, flatten2, n, acc, i_s, 
                         first_incomplete_addition, second_incomplete_addition, 
                         i_p, last_slice, slice, domain_string, message_bytes, 
                         i >>

IntToLEOSP == GetFirstByte \/ BuildSecondByte \/ AddZeroes \/ GetSecondByte
                 \/ Bytes

FlushString == /\ pc = "FlushString"
               /\ string' = ""
               /\ pc' = "BytesToCharacters"
               /\ UNCHANGED << point, characters, bytes, bits, slices, stack, 
                               domain_string_, message_string, domain_bytes, 
                               i_, j, flatten1, flatten2, n, acc, i_s, 
                               first_incomplete_addition, 
                               second_incomplete_addition, i_p, last_slice, 
                               slice, domain_string, message_bytes, one_byte, 
                               second_byte, i >>

BytesToCharacters == /\ pc = "BytesToCharacters"
                     /\ characters' = [b \in 1..Len(bytes) |-> Chr(bytes[b])]
                     /\ pc' = "CharactersToString"
                     /\ UNCHANGED << point, bytes, bits, string, slices, stack, 
                                     domain_string_, message_string, 
                                     domain_bytes, i_, j, flatten1, flatten2, 
                                     n, acc, i_s, first_incomplete_addition, 
                                     second_incomplete_addition, i_p, 
                                     last_slice, slice, domain_string, 
                                     message_bytes, one_byte, second_byte, i >>

CharactersToString == /\ pc = "CharactersToString"
                      /\ IF i <= Len(characters)
                            THEN /\ string' = string \o characters[i]
                                 /\ i' = i + 1
                                 /\ pc' = "CharactersToString"
                                 /\ stack' = stack
                            ELSE /\ pc' = Head(stack).pc
                                 /\ i' = Head(stack).i
                                 /\ stack' = Tail(stack)
                                 /\ UNCHANGED string
                      /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                      domain_string_, message_string, 
                                      domain_bytes, i_, j, flatten1, flatten2, 
                                      n, acc, i_s, first_incomplete_addition, 
                                      second_incomplete_addition, i_p, 
                                      last_slice, slice, domain_string, 
                                      message_bytes, one_byte, second_byte >>

bytes_to_string == FlushString \/ BytesToCharacters \/ CharactersToString

PointToBytes == /\ pc = "PointToBytes"
                /\ pc' = Head(stack).pc
                /\ stack' = Tail(stack)
                /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                                domain_string_, message_string, domain_bytes, 
                                i_, j, flatten1, flatten2, n, acc, i_s, 
                                first_incomplete_addition, 
                                second_incomplete_addition, i_p, last_slice, 
                                slice, domain_string, message_bytes, one_byte, 
                                second_byte, i >>

point_to_bytes == PointToBytes

SinSemillaHashCall == /\ pc = "SinSemillaHashCall"
                      /\ /\ domain_string_' = <<"d", "o", "m", "a", "i", "n">>
                         /\ message_string' = <<"m", "e", "s", "s", "a", "g", "e">>
                         /\ stack' = << [ procedure |->  "sinsemilla_hash",
                                          pc        |->  "Done",
                                          domain_bytes |->  domain_bytes,
                                          domain_string_ |->  domain_string_,
                                          message_string |->  message_string ] >>
                                      \o stack
                      /\ domain_bytes' = <<>>
                      /\ pc' = "DomainToCharacters"
                      /\ UNCHANGED << point, characters, bytes, bits, string, 
                                      slices, i_, j, flatten1, flatten2, n, 
                                      acc, i_s, first_incomplete_addition, 
                                      second_incomplete_addition, i_p, 
                                      last_slice, slice, domain_string, 
                                      message_bytes, one_byte, second_byte, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == sinsemilla_hash \/ characters_to_bytes \/ bytes_to_bits
           \/ sinsemilla_hash_to_point \/ pad \/ q \/ s \/ hash_to_pallas
           \/ IntToLEOSP \/ bytes_to_string \/ point_to_bytes
           \/ SinSemillaHashCall
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
