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
                bytes := slices[i];
                call s();
            FirstIncompleteAddition:
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

        last_slice := slices[Len(slices)];
        if Len(last_slice) < k then
            PadLastSlice:
                while Len(slices[Len(slices)]) < k do
                    slices[Len(slices)] := Append(slices[Len(slices)], 0);
                end while;
        end if;
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
        return;
end procedure;

\* Integer to Little-Endian Octet String Pairing
procedure IntToLEOSP()
begin
    IntToLEOSP:
        skip;
    return;
end procedure;

\* Convert a sequence of bytes to a string
procedure bytes_to_string()
begin
    BytesToString:
        \* Convert each byte to its ASCII character
        string := [b \in 1..Len(bytes) |-> Chr(bytes[b])];
        return;
end procedure;

procedure point_to_bytes()
begin
    PointToBytes:
        print point;
        \*bytes := <<point.a, point.b, point.baseX, point.baseY>>;
        return;
end procedure;

begin
    SinSemillaHashCall:
        call sinsemilla_hash(<<"d", "o", "m", "a", "i", "n">>, <<"m", "e", "s", "s", "a", "g", "e">>);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "34b5562" /\ chksum(tla) = "4cd57225")
\* Label Return of procedure sinsemilla_hash at line 55 col 9 changed to Return_
\* Label BytesToString of procedure hash_to_pallas at line 173 col 9 changed to BytesToString_
\* Label IntToLEOSP of procedure IntToLEOSP at line 184 col 9 changed to IntToLEOSP_
\* Procedure variable i of procedure bytes_to_bits at line 72 col 11 changed to i_
\* Procedure variable i of procedure sinsemilla_hash_to_point at line 88 col 5 changed to i_s
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
          second_incomplete_addition, i, last_slice, slice, domain_string, 
          message_bytes

vars == << point, characters, bytes, bits, string, slices, pc, stack, 
           domain_string_, message_string, domain_bytes, i_, j, flatten1, 
           flatten2, n, acc, i_s, first_incomplete_addition, 
           second_incomplete_addition, i, last_slice, slice, domain_string, 
           message_bytes >>

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
        /\ i = 1
        /\ last_slice = <<>>
        /\ slice = <<>>
        (* Procedure hash_to_pallas *)
        /\ domain_string = defaultInitValue
        /\ message_bytes = defaultInitValue
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
                                      second_incomplete_addition, i, 
                                      last_slice, slice, domain_string, 
                                      message_bytes >>

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
                                           second_incomplete_addition, i, 
                                           last_slice, slice, domain_string, 
                                           message_bytes >>

DomainStringToBytesAssign == /\ pc = "DomainStringToBytesAssign"
                             /\ domain_bytes' = bytes
                             /\ pc' = "MessageStringToCharactersCall"
                             /\ UNCHANGED << point, characters, bytes, bits, 
                                             string, slices, stack, 
                                             domain_string_, message_string, 
                                             i_, j, flatten1, flatten2, n, acc, 
                                             i_s, first_incomplete_addition, 
                                             second_incomplete_addition, i, 
                                             last_slice, slice, domain_string, 
                                             message_bytes >>

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
                                                 second_incomplete_addition, i, 
                                                 last_slice, slice, 
                                                 domain_string, message_bytes >>

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
                                                second_incomplete_addition, i, 
                                                last_slice, slice, 
                                                domain_string, message_bytes >>

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
                                          second_incomplete_addition, i, 
                                          last_slice, slice, domain_string, 
                                          message_bytes >>

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
                                         flatten1, flatten2, i, last_slice, 
                                         slice, domain_string, message_bytes >>

OutputPointToBytes == /\ pc = "OutputPointToBytes"
                      /\ stack' = << [ procedure |->  "point_to_bytes",
                                       pc        |->  "OutputBytesToCharacters" ] >>
                                   \o stack
                      /\ pc' = "PointToBytes"
                      /\ UNCHANGED << point, characters, bytes, bits, string, 
                                      slices, domain_string_, message_string, 
                                      domain_bytes, i_, j, flatten1, flatten2, 
                                      n, acc, i_s, first_incomplete_addition, 
                                      second_incomplete_addition, i, 
                                      last_slice, slice, domain_string, 
                                      message_bytes >>

OutputBytesToCharacters == /\ pc = "OutputBytesToCharacters"
                           /\ TRUE
                           /\ pc' = "OutputCharactersToString"
                           /\ UNCHANGED << point, characters, bytes, bits, 
                                           string, slices, stack, 
                                           domain_string_, message_string, 
                                           domain_bytes, i_, j, flatten1, 
                                           flatten2, n, acc, i_s, 
                                           first_incomplete_addition, 
                                           second_incomplete_addition, i, 
                                           last_slice, slice, domain_string, 
                                           message_bytes >>

OutputCharactersToString == /\ pc = "OutputCharactersToString"
                            /\ TRUE
                            /\ pc' = "Return_"
                            /\ UNCHANGED << point, characters, bytes, bits, 
                                            string, slices, stack, 
                                            domain_string_, message_string, 
                                            domain_bytes, i_, j, flatten1, 
                                            flatten2, n, acc, i_s, 
                                            first_incomplete_addition, 
                                            second_incomplete_addition, i, 
                                            last_slice, slice, domain_string, 
                                            message_bytes >>

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
                           second_incomplete_addition, i, last_slice, slice, 
                           domain_string, message_bytes >>

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
                              second_incomplete_addition, i, last_slice, slice, 
                              domain_string, message_bytes >>

StringToBytes == /\ pc = "StringToBytes"
                 /\ bytes' = [c \in 1..Len(characters) |-> Ord(characters[c])]
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << point, characters, bits, string, slices, 
                                 domain_string_, message_string, domain_bytes, 
                                 i_, j, flatten1, flatten2, n, acc, i_s, 
                                 first_incomplete_addition, 
                                 second_incomplete_addition, i, last_slice, 
                                 slice, domain_string, message_bytes >>

characters_to_bytes == FlushBytes \/ StringToBytes

InitializeBits == /\ pc = "InitializeBits"
                  /\ bits' = <<>>
                  /\ pc' = "BytesToBitSequence"
                  /\ UNCHANGED << point, characters, bytes, string, slices, 
                                  stack, domain_string_, message_string, 
                                  domain_bytes, i_, j, flatten1, flatten2, n, 
                                  acc, i_s, first_incomplete_addition, 
                                  second_incomplete_addition, i, last_slice, 
                                  slice, domain_string, message_bytes >>

BytesToBitSequence == /\ pc = "BytesToBitSequence"
                      /\ bits' = [byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])]
                      /\ pc' = "Flatten"
                      /\ UNCHANGED << point, characters, bytes, string, slices, 
                                      stack, domain_string_, message_string, 
                                      domain_bytes, i_, j, flatten1, flatten2, 
                                      n, acc, i_s, first_incomplete_addition, 
                                      second_incomplete_addition, i, 
                                      last_slice, slice, domain_string, 
                                      message_bytes >>

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
                           second_incomplete_addition, i, last_slice, slice, 
                           domain_string, message_bytes >>

bytes_to_bits == InitializeBits \/ BytesToBitSequence \/ Flatten

CalculateN == /\ pc = "CalculateN"
              /\ n' = (Len(bits) \div k)
              /\ pc' = "CallPad"
              /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                              stack, domain_string_, message_string, 
                              domain_bytes, i_, j, flatten1, flatten2, acc, 
                              i_s, first_incomplete_addition, 
                              second_incomplete_addition, i, last_slice, slice, 
                              domain_string, message_bytes >>

CallPad == /\ pc = "CallPad"
           /\ stack' = << [ procedure |->  "pad",
                            pc        |->  "CallQ",
                            i         |->  i,
                            last_slice |->  last_slice,
                            slice     |->  slice ] >>
                        \o stack
           /\ i' = 1
           /\ last_slice' = <<>>
           /\ slice' = <<>>
           /\ pc' = "Padding"
           /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                           domain_string_, message_string, domain_bytes, i_, j, 
                           flatten1, flatten2, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, domain_string, 
                           message_bytes >>

CallQ == /\ pc = "CallQ"
         /\ stack' = << [ procedure |->  "q",
                          pc        |->  "InitializeAcc" ] >>
                      \o stack
         /\ pc' = "Q"
         /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                         domain_string_, message_string, domain_bytes, i_, j, 
                         flatten1, flatten2, n, acc, i_s, 
                         first_incomplete_addition, second_incomplete_addition, 
                         i, last_slice, slice, domain_string, message_bytes >>

InitializeAcc == /\ pc = "InitializeAcc"
                 /\ acc' = point
                 /\ pc' = "Loop"
                 /\ UNCHANGED << point, characters, bytes, bits, string, 
                                 slices, stack, domain_string_, message_string, 
                                 domain_bytes, i_, j, flatten1, flatten2, n, 
                                 i_s, first_incomplete_addition, 
                                 second_incomplete_addition, i, last_slice, 
                                 slice, domain_string, message_bytes >>

Loop == /\ pc = "Loop"
        /\ IF i_s <= n
              THEN /\ pc' = "CallS"
              ELSE /\ pc' = "Results"
        /\ UNCHANGED << point, characters, bytes, bits, string, slices, stack, 
                        domain_string_, message_string, domain_bytes, i_, j, 
                        flatten1, flatten2, n, acc, i_s, 
                        first_incomplete_addition, second_incomplete_addition, 
                        i, last_slice, slice, domain_string, message_bytes >>

CallS == /\ pc = "CallS"
         /\ bytes' = slices[i_s]
         /\ stack' = << [ procedure |->  "s",
                          pc        |->  "FirstIncompleteAddition" ] >>
                      \o stack
         /\ pc' = "CallI2LEOSP"
         /\ UNCHANGED << point, characters, bits, string, slices, 
                         domain_string_, message_string, domain_bytes, i_, j, 
                         flatten1, flatten2, n, acc, i_s, 
                         first_incomplete_addition, second_incomplete_addition, 
                         i, last_slice, slice, domain_string, message_bytes >>

FirstIncompleteAddition == /\ pc = "FirstIncompleteAddition"
                           /\ first_incomplete_addition' = IncompleteAddition(acc, point)
                           /\ pc' = "SecondIncompleteAddition"
                           /\ UNCHANGED << point, characters, bytes, bits, 
                                           string, slices, stack, 
                                           domain_string_, message_string, 
                                           domain_bytes, i_, j, flatten1, 
                                           flatten2, n, acc, i_s, 
                                           second_incomplete_addition, i, 
                                           last_slice, slice, domain_string, 
                                           message_bytes >>

SecondIncompleteAddition == /\ pc = "SecondIncompleteAddition"
                            /\ second_incomplete_addition' = IncompleteAddition(first_incomplete_addition, acc)
                            /\ acc' = second_incomplete_addition'
                            /\ pc' = "Inc"
                            /\ UNCHANGED << point, characters, bytes, bits, 
                                            string, slices, stack, 
                                            domain_string_, message_string, 
                                            domain_bytes, i_, j, flatten1, 
                                            flatten2, n, i_s, 
                                            first_incomplete_addition, i, 
                                            last_slice, slice, domain_string, 
                                            message_bytes >>

Inc == /\ pc = "Inc"
       /\ i_s' = i_s + 1
       /\ pc' = "Loop"
       /\ UNCHANGED << point, characters, bytes, bits, string, slices, stack, 
                       domain_string_, message_string, domain_bytes, i_, j, 
                       flatten1, flatten2, n, acc, first_incomplete_addition, 
                       second_incomplete_addition, i, last_slice, slice, 
                       domain_string, message_bytes >>

Results == /\ pc = "Results"
           /\ point' = second_incomplete_addition
           /\ pc' = "CleanIndex"
           /\ UNCHANGED << characters, bytes, bits, string, slices, stack, 
                           domain_string_, message_string, domain_bytes, i_, j, 
                           flatten1, flatten2, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, i, last_slice, slice, 
                           domain_string, message_bytes >>

CleanIndex == /\ pc = "CleanIndex"
              /\ i_s' = 1
              /\ pc' = "Return"
              /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                              stack, domain_string_, message_string, 
                              domain_bytes, i_, j, flatten1, flatten2, n, acc, 
                              first_incomplete_addition, 
                              second_incomplete_addition, i, last_slice, slice, 
                              domain_string, message_bytes >>

Return == /\ pc = "Return"
          /\ pc' = Head(stack).pc
          /\ n' = Head(stack).n
          /\ acc' = Head(stack).acc
          /\ i_s' = Head(stack).i_s
          /\ first_incomplete_addition' = Head(stack).first_incomplete_addition
          /\ second_incomplete_addition' = Head(stack).second_incomplete_addition
          /\ stack' = Tail(stack)
          /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                          domain_string_, message_string, domain_bytes, i_, j, 
                          flatten1, flatten2, i, last_slice, slice, 
                          domain_string, message_bytes >>

sinsemilla_hash_to_point == CalculateN \/ CallPad \/ CallQ \/ InitializeAcc
                               \/ Loop \/ CallS \/ FirstIncompleteAddition
                               \/ SecondIncompleteAddition \/ Inc
                               \/ Results \/ CleanIndex \/ Return

Padding == /\ pc = "Padding"
           /\ IF i <= Len(bits)
                 THEN /\ IF i+k >= Len(bits)
                            THEN /\ slices' = Append(slices, SubSeq(bits, i, Len(bits)))
                                 /\ i' = Len(bits) + 1
                            ELSE /\ slices' = Append(slices, SubSeq(bits, i, i+k))
                                 /\ i' = i+k
                      /\ pc' = "Padding"
                      /\ UNCHANGED last_slice
                 ELSE /\ last_slice' = slices[Len(slices)]
                      /\ IF Len(last_slice') < k
                            THEN /\ pc' = "PadLastSlice2"
                            ELSE /\ pc' = "Printit"
                      /\ UNCHANGED << slices, i >>
           /\ UNCHANGED << point, characters, bytes, bits, string, stack, 
                           domain_string_, message_string, domain_bytes, i_, j, 
                           flatten1, flatten2, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, slice, domain_string, 
                           message_bytes >>

PadLastSlice2 == /\ pc = "PadLastSlice2"
                 /\ IF Len(slices[Len(slices)]) < k
                       THEN /\ slices' = [slices EXCEPT ![Len(slices)] = Append(slices[Len(slices)], 0)]
                            /\ pc' = "PadLastSlice2"
                       ELSE /\ pc' = "Printit"
                            /\ UNCHANGED slices
                 /\ UNCHANGED << point, characters, bytes, bits, string, stack, 
                                 domain_string_, message_string, domain_bytes, 
                                 i_, j, flatten1, flatten2, n, acc, i_s, 
                                 first_incomplete_addition, 
                                 second_incomplete_addition, i, last_slice, 
                                 slice, domain_string, message_bytes >>

Printit == /\ pc = "Printit"
           /\ PrintT(slices)
           /\ pc' = Head(stack).pc
           /\ i' = Head(stack).i
           /\ last_slice' = Head(stack).last_slice
           /\ slice' = Head(stack).slice
           /\ stack' = Tail(stack)
           /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                           domain_string_, message_string, domain_bytes, i_, j, 
                           flatten1, flatten2, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, domain_string, 
                           message_bytes >>

pad == Padding \/ PadLastSlice2 \/ Printit

Q == /\ pc = "Q"
     /\ /\ domain_string' = "z.cash.SinsemillaQ"
        /\ message_bytes' = bytes
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         domain_string |->  domain_string,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ pc' = "BytesToString_"
     /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                     domain_string_, message_string, domain_bytes, i_, j, 
                     flatten1, flatten2, n, acc, i_s, 
                     first_incomplete_addition, second_incomplete_addition, i, 
                     last_slice, slice >>

q == Q

CallI2LEOSP == /\ pc = "CallI2LEOSP"
               /\ stack' = << [ procedure |->  "IntToLEOSP",
                                pc        |->  "S" ] >>
                            \o stack
               /\ pc' = "IntToLEOSP_"
               /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                               domain_string_, message_string, domain_bytes, 
                               i_, j, flatten1, flatten2, n, acc, i_s, 
                               first_incomplete_addition, 
                               second_incomplete_addition, i, last_slice, 
                               slice, domain_string, message_bytes >>

S == /\ pc = "S"
     /\ /\ domain_string' = "z.cash:SinsemillaS"
        /\ message_bytes' = bytes
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         domain_string |->  domain_string,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ pc' = "BytesToString_"
     /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                     domain_string_, message_string, domain_bytes, i_, j, 
                     flatten1, flatten2, n, acc, i_s, 
                     first_incomplete_addition, second_incomplete_addition, i, 
                     last_slice, slice >>

s == CallI2LEOSP \/ S

BytesToString_ == /\ pc = "BytesToString_"
                  /\ bytes' = message_bytes
                  /\ stack' = << [ procedure |->  "bytes_to_string",
                                   pc        |->  "HashToPallas" ] >>
                               \o stack
                  /\ pc' = "BytesToString"
                  /\ UNCHANGED << point, characters, bits, string, slices, 
                                  domain_string_, message_string, domain_bytes, 
                                  i_, j, flatten1, flatten2, n, acc, i_s, 
                                  first_incomplete_addition, 
                                  second_incomplete_addition, i, last_slice, 
                                  slice, domain_string, message_bytes >>

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
                                second_incomplete_addition, i, last_slice, 
                                slice >>

hash_to_pallas == BytesToString_ \/ HashToPallas

IntToLEOSP_ == /\ pc = "IntToLEOSP_"
               /\ TRUE
               /\ pc' = Head(stack).pc
               /\ stack' = Tail(stack)
               /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                               domain_string_, message_string, domain_bytes, 
                               i_, j, flatten1, flatten2, n, acc, i_s, 
                               first_incomplete_addition, 
                               second_incomplete_addition, i, last_slice, 
                               slice, domain_string, message_bytes >>

IntToLEOSP == IntToLEOSP_

BytesToString == /\ pc = "BytesToString"
                 /\ string' = [b \in 1..Len(bytes) |-> Chr(bytes[b])]
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << point, characters, bytes, bits, slices, 
                                 domain_string_, message_string, domain_bytes, 
                                 i_, j, flatten1, flatten2, n, acc, i_s, 
                                 first_incomplete_addition, 
                                 second_incomplete_addition, i, last_slice, 
                                 slice, domain_string, message_bytes >>

bytes_to_string == BytesToString

PointToBytes == /\ pc = "PointToBytes"
                /\ PrintT(point)
                /\ pc' = Head(stack).pc
                /\ stack' = Tail(stack)
                /\ UNCHANGED << point, characters, bytes, bits, string, slices, 
                                domain_string_, message_string, domain_bytes, 
                                i_, j, flatten1, flatten2, n, acc, i_s, 
                                first_incomplete_addition, 
                                second_incomplete_addition, i, last_slice, 
                                slice, domain_string, message_bytes >>

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
                                      second_incomplete_addition, i, 
                                      last_slice, slice, domain_string, 
                                      message_bytes >>

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
