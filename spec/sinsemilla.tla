---- MODULE sinsemilla ----
EXTENDS TLC, Naturals, Integers, Sequences, Randomization, ascii

(*--algorithm sinsemilla
variables
    point = [a |-> 0, b |-> 0, baseX |-> 0, baseY |-> 0];
    characters = <<>>;
    bytes = <<>>;
    bits = <<>>;
    string = "";

    padded_message = <<>>;

    output_hash = "";

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
variables domain_bytes = <<>>, message_bits = <<>>;
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
    MessageBytesToBitsAssign: \* 7
        message_bits := bits;
    SinsemillaHashToPoint: \* ...
        call sinsemilla_hash_to_point(domain_bytes, message_bits);
    OutputPointToBytes:
        call point_to_bytes();
    OutputBytesToCharacters:
        skip;
    OutputCharactersToString:
        skip;
    Return:
        output_hash := string;
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
        \* TODO: simplify the flattening process.
        Flatten1:
            while i <= Len(bits) do
                Flatten2:
                    while j <= Len(bits[i]) do
                        flatten2 := Append(flatten1, bits[i][j]);
                        flatten1 := flatten2;
                        j := j + 1;
                    end while;
                j := 1;
                i := i + 1;
            end while;
            bits := flatten2;
            return;
end procedure;

\* Convert the message bits into a Pallas point, using the domain bytes as the domain separator.
procedure sinsemilla_hash_to_point(domain_bytes, message_bits)
variables 
    n, 
    acc,
    i = 1,
    first_incomplete_addition,
    second_incomplete_addition;
begin
    CalculateN:
        n := Len(message_bits) \div k;
    CallPad:
        call pad();
    CallQ:
        call q();
    InitializeAcc:
        acc := point;
    Loop:
        while i <= n do
            CallS:
                bytes := padded_message[i];
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
    slice = <<>>;
begin
    Pad:
        \* Iterate through bits to collect slices of k bits
        while i <= Len(bits) do
            \* Check if adding another bit would exceed the slice size
            if Len(slice) < k then
                \* Add the bit to the current slice
                slice := Append(slice, bits[i]);
            end if;
            
            \* If the slice is full, or it's the last bit and we're finishing up
            if Len(slice) = k \/ i = Len(bits) then
                \* Add the slice to padded_message
                padded_message := Append(padded_message, slice);
                \* Reset the slice for the next batch of bits
                ResetSlice:
                    slice := <<>>;
                PadLastSlice:
                    \* If it's the last slice and not full, pad it with zeros until it is k bits long
                    while Len(padded_message[Len(padded_message)]) < k do
                        padded_message[Len(padded_message)] := Append(padded_message[Len(padded_message)], 0);
                    end while;
            end if;
            IncrementIndex:
                i := i + 1;
        end while;
        return;
end procedure;

procedure q()
begin
    Q:
        call hash_to_pallas("z.cash.SinsemillaQ", domain_bytes);
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
\* BEGIN TRANSLATION (chksum(pcal) = "6830df6a" /\ chksum(tla) = "7710ff0f")
\* Label Return of procedure sinsemilla_hash at line 58 col 9 changed to Return_
\* Label BytesToString of procedure hash_to_pallas at line 188 col 9 changed to BytesToString_
\* Label IntToLEOSP of procedure IntToLEOSP at line 199 col 9 changed to IntToLEOSP_
\* Procedure variable domain_bytes of procedure sinsemilla_hash at line 31 col 11 changed to domain_bytes_
\* Procedure variable message_bits of procedure sinsemilla_hash at line 31 col 32 changed to message_bits_
\* Procedure variable i of procedure bytes_to_bits at line 75 col 11 changed to i_
\* Procedure variable i of procedure sinsemilla_hash_to_point at line 102 col 5 changed to i_s
\* Parameter domain_string of procedure sinsemilla_hash at line 30 col 27 changed to domain_string_
CONSTANT defaultInitValue
VARIABLES point, characters, bytes, bits, string, padded_message, output_hash, 
          pc, stack

(* define statement *)
baseX == "0x01"


baseY == "0xbb2aedca237acf1971473d33d45b658f54ee7863f0a9df537c93120aa3b5741b"


k == 10


IncompleteAddition(x, y) == [a |-> x.a \o "+" \o y.a, b |-> x.b \o "+" \o y.b, baseX |-> baseX, baseY |-> baseY]

VARIABLES domain_string_, message_string, domain_bytes_, message_bits_, i_, j, 
          flatten1, flatten2, domain_bytes, message_bits, n, acc, i_s, 
          first_incomplete_addition, second_incomplete_addition, i, slice, 
          domain_string, message_bytes

vars == << point, characters, bytes, bits, string, padded_message, 
           output_hash, pc, stack, domain_string_, message_string, 
           domain_bytes_, message_bits_, i_, j, flatten1, flatten2, 
           domain_bytes, message_bits, n, acc, i_s, first_incomplete_addition, 
           second_incomplete_addition, i, slice, domain_string, message_bytes
        >>

Init == (* Global variables *)
        /\ point = [a |-> 0, b |-> 0, baseX |-> 0, baseY |-> 0]
        /\ characters = <<>>
        /\ bytes = <<>>
        /\ bits = <<>>
        /\ string = ""
        /\ padded_message = <<>>
        /\ output_hash = ""
        (* Procedure sinsemilla_hash *)
        /\ domain_string_ = defaultInitValue
        /\ message_string = defaultInitValue
        /\ domain_bytes_ = <<>>
        /\ message_bits_ = <<>>
        (* Procedure bytes_to_bits *)
        /\ i_ = 1
        /\ j = 1
        /\ flatten1 = <<>>
        /\ flatten2 = <<>>
        (* Procedure sinsemilla_hash_to_point *)
        /\ domain_bytes = defaultInitValue
        /\ message_bits = defaultInitValue
        /\ n = defaultInitValue
        /\ acc = defaultInitValue
        /\ i_s = 1
        /\ first_incomplete_addition = defaultInitValue
        /\ second_incomplete_addition = defaultInitValue
        (* Procedure pad *)
        /\ i = 1
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
                                      padded_message, output_hash, stack, 
                                      domain_string_, message_string, 
                                      domain_bytes_, message_bits_, i_, j, 
                                      flatten1, flatten2, domain_bytes, 
                                      message_bits, n, acc, i_s, 
                                      first_incomplete_addition, 
                                      second_incomplete_addition, i, slice, 
                                      domain_string, message_bytes >>

DomainStringToBytesCall == /\ pc = "DomainStringToBytesCall"
                           /\ characters' = domain_string_
                           /\ stack' = << [ procedure |->  "characters_to_bytes",
                                            pc        |->  "DomainStringToBytesAssign" ] >>
                                        \o stack
                           /\ pc' = "FlushBytes"
                           /\ UNCHANGED << point, bytes, bits, string, 
                                           padded_message, output_hash, 
                                           domain_string_, message_string, 
                                           domain_bytes_, message_bits_, i_, j, 
                                           flatten1, flatten2, domain_bytes, 
                                           message_bits, n, acc, i_s, 
                                           first_incomplete_addition, 
                                           second_incomplete_addition, i, 
                                           slice, domain_string, message_bytes >>

DomainStringToBytesAssign == /\ pc = "DomainStringToBytesAssign"
                             /\ domain_bytes_' = bytes
                             /\ pc' = "MessageStringToCharactersCall"
                             /\ UNCHANGED << point, characters, bytes, bits, 
                                             string, padded_message, 
                                             output_hash, stack, 
                                             domain_string_, message_string, 
                                             message_bits_, i_, j, flatten1, 
                                             flatten2, domain_bytes, 
                                             message_bits, n, acc, i_s, 
                                             first_incomplete_addition, 
                                             second_incomplete_addition, i, 
                                             slice, domain_string, 
                                             message_bytes >>

MessageStringToCharactersCall == /\ pc = "MessageStringToCharactersCall"
                                 /\ TRUE
                                 /\ pc' = "MessageCharactersToBytesCall"
                                 /\ UNCHANGED << point, characters, bytes, 
                                                 bits, string, padded_message, 
                                                 output_hash, stack, 
                                                 domain_string_, 
                                                 message_string, domain_bytes_, 
                                                 message_bits_, i_, j, 
                                                 flatten1, flatten2, 
                                                 domain_bytes, message_bits, n, 
                                                 acc, i_s, 
                                                 first_incomplete_addition, 
                                                 second_incomplete_addition, i, 
                                                 slice, domain_string, 
                                                 message_bytes >>

MessageCharactersToBytesCall == /\ pc = "MessageCharactersToBytesCall"
                                /\ characters' = message_string
                                /\ stack' = << [ procedure |->  "characters_to_bytes",
                                                 pc        |->  "MessageBytesToBitsCall" ] >>
                                             \o stack
                                /\ pc' = "FlushBytes"
                                /\ UNCHANGED << point, bytes, bits, string, 
                                                padded_message, output_hash, 
                                                domain_string_, message_string, 
                                                domain_bytes_, message_bits_, 
                                                i_, j, flatten1, flatten2, 
                                                domain_bytes, message_bits, n, 
                                                acc, i_s, 
                                                first_incomplete_addition, 
                                                second_incomplete_addition, i, 
                                                slice, domain_string, 
                                                message_bytes >>

MessageBytesToBitsCall == /\ pc = "MessageBytesToBitsCall"
                          /\ stack' = << [ procedure |->  "bytes_to_bits",
                                           pc        |->  "MessageBytesToBitsAssign",
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
                                          string, padded_message, output_hash, 
                                          domain_string_, message_string, 
                                          domain_bytes_, message_bits_, 
                                          domain_bytes, message_bits, n, acc, 
                                          i_s, first_incomplete_addition, 
                                          second_incomplete_addition, i, slice, 
                                          domain_string, message_bytes >>

MessageBytesToBitsAssign == /\ pc = "MessageBytesToBitsAssign"
                            /\ message_bits_' = bits
                            /\ pc' = "SinsemillaHashToPoint"
                            /\ UNCHANGED << point, characters, bytes, bits, 
                                            string, padded_message, 
                                            output_hash, stack, domain_string_, 
                                            message_string, domain_bytes_, i_, 
                                            j, flatten1, flatten2, 
                                            domain_bytes, message_bits, n, acc, 
                                            i_s, first_incomplete_addition, 
                                            second_incomplete_addition, i, 
                                            slice, domain_string, 
                                            message_bytes >>

SinsemillaHashToPoint == /\ pc = "SinsemillaHashToPoint"
                         /\ /\ domain_bytes' = domain_bytes_
                            /\ message_bits' = message_bits_
                            /\ stack' = << [ procedure |->  "sinsemilla_hash_to_point",
                                             pc        |->  "OutputPointToBytes",
                                             n         |->  n,
                                             acc       |->  acc,
                                             i_s       |->  i_s,
                                             first_incomplete_addition |->  first_incomplete_addition,
                                             second_incomplete_addition |->  second_incomplete_addition,
                                             domain_bytes |->  domain_bytes,
                                             message_bits |->  message_bits ] >>
                                         \o stack
                         /\ n' = defaultInitValue
                         /\ acc' = defaultInitValue
                         /\ i_s' = 1
                         /\ first_incomplete_addition' = defaultInitValue
                         /\ second_incomplete_addition' = defaultInitValue
                         /\ pc' = "CalculateN"
                         /\ UNCHANGED << point, characters, bytes, bits, 
                                         string, padded_message, output_hash, 
                                         domain_string_, message_string, 
                                         domain_bytes_, message_bits_, i_, j, 
                                         flatten1, flatten2, i, slice, 
                                         domain_string, message_bytes >>

OutputPointToBytes == /\ pc = "OutputPointToBytes"
                      /\ stack' = << [ procedure |->  "point_to_bytes",
                                       pc        |->  "OutputBytesToCharacters" ] >>
                                   \o stack
                      /\ pc' = "PointToBytes"
                      /\ UNCHANGED << point, characters, bytes, bits, string, 
                                      padded_message, output_hash, 
                                      domain_string_, message_string, 
                                      domain_bytes_, message_bits_, i_, j, 
                                      flatten1, flatten2, domain_bytes, 
                                      message_bits, n, acc, i_s, 
                                      first_incomplete_addition, 
                                      second_incomplete_addition, i, slice, 
                                      domain_string, message_bytes >>

OutputBytesToCharacters == /\ pc = "OutputBytesToCharacters"
                           /\ TRUE
                           /\ pc' = "OutputCharactersToString"
                           /\ UNCHANGED << point, characters, bytes, bits, 
                                           string, padded_message, output_hash, 
                                           stack, domain_string_, 
                                           message_string, domain_bytes_, 
                                           message_bits_, i_, j, flatten1, 
                                           flatten2, domain_bytes, 
                                           message_bits, n, acc, i_s, 
                                           first_incomplete_addition, 
                                           second_incomplete_addition, i, 
                                           slice, domain_string, message_bytes >>

OutputCharactersToString == /\ pc = "OutputCharactersToString"
                            /\ TRUE
                            /\ pc' = "Return_"
                            /\ UNCHANGED << point, characters, bytes, bits, 
                                            string, padded_message, 
                                            output_hash, stack, domain_string_, 
                                            message_string, domain_bytes_, 
                                            message_bits_, i_, j, flatten1, 
                                            flatten2, domain_bytes, 
                                            message_bits, n, acc, i_s, 
                                            first_incomplete_addition, 
                                            second_incomplete_addition, i, 
                                            slice, domain_string, 
                                            message_bytes >>

Return_ == /\ pc = "Return_"
           /\ output_hash' = string
           /\ pc' = Head(stack).pc
           /\ domain_bytes_' = Head(stack).domain_bytes_
           /\ message_bits_' = Head(stack).message_bits_
           /\ domain_string_' = Head(stack).domain_string_
           /\ message_string' = Head(stack).message_string
           /\ stack' = Tail(stack)
           /\ UNCHANGED << point, characters, bytes, bits, string, 
                           padded_message, i_, j, flatten1, flatten2, 
                           domain_bytes, message_bits, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, i, slice, domain_string, 
                           message_bytes >>

sinsemilla_hash == DomainToCharacters \/ DomainStringToBytesCall
                      \/ DomainStringToBytesAssign
                      \/ MessageStringToCharactersCall
                      \/ MessageCharactersToBytesCall
                      \/ MessageBytesToBitsCall \/ MessageBytesToBitsAssign
                      \/ SinsemillaHashToPoint \/ OutputPointToBytes
                      \/ OutputBytesToCharacters
                      \/ OutputCharactersToString \/ Return_

FlushBytes == /\ pc = "FlushBytes"
              /\ bytes' = <<>>
              /\ pc' = "StringToBytes"
              /\ UNCHANGED << point, characters, bits, string, padded_message, 
                              output_hash, stack, domain_string_, 
                              message_string, domain_bytes_, message_bits_, i_, 
                              j, flatten1, flatten2, domain_bytes, 
                              message_bits, n, acc, i_s, 
                              first_incomplete_addition, 
                              second_incomplete_addition, i, slice, 
                              domain_string, message_bytes >>

StringToBytes == /\ pc = "StringToBytes"
                 /\ bytes' = [c \in 1..Len(characters) |-> Ord(characters[c])]
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << point, characters, bits, string, 
                                 padded_message, output_hash, domain_string_, 
                                 message_string, domain_bytes_, message_bits_, 
                                 i_, j, flatten1, flatten2, domain_bytes, 
                                 message_bits, n, acc, i_s, 
                                 first_incomplete_addition, 
                                 second_incomplete_addition, i, slice, 
                                 domain_string, message_bytes >>

characters_to_bytes == FlushBytes \/ StringToBytes

InitializeBits == /\ pc = "InitializeBits"
                  /\ bits' = <<>>
                  /\ pc' = "BytesToBitSequence"
                  /\ UNCHANGED << point, characters, bytes, string, 
                                  padded_message, output_hash, stack, 
                                  domain_string_, message_string, 
                                  domain_bytes_, message_bits_, i_, j, 
                                  flatten1, flatten2, domain_bytes, 
                                  message_bits, n, acc, i_s, 
                                  first_incomplete_addition, 
                                  second_incomplete_addition, i, slice, 
                                  domain_string, message_bytes >>

BytesToBitSequence == /\ pc = "BytesToBitSequence"
                      /\ bits' = [byte \in 1..Len(bytes) |-> ByteToBitSequence(bytes[byte])]
                      /\ pc' = "Flatten1"
                      /\ UNCHANGED << point, characters, bytes, string, 
                                      padded_message, output_hash, stack, 
                                      domain_string_, message_string, 
                                      domain_bytes_, message_bits_, i_, j, 
                                      flatten1, flatten2, domain_bytes, 
                                      message_bits, n, acc, i_s, 
                                      first_incomplete_addition, 
                                      second_incomplete_addition, i, slice, 
                                      domain_string, message_bytes >>

Flatten1 == /\ pc = "Flatten1"
            /\ IF i_ <= Len(bits)
                  THEN /\ pc' = "Flatten2"
                       /\ UNCHANGED << bits, stack, i_, j, flatten1, flatten2 >>
                  ELSE /\ bits' = flatten2
                       /\ pc' = Head(stack).pc
                       /\ i_' = Head(stack).i_
                       /\ j' = Head(stack).j
                       /\ flatten1' = Head(stack).flatten1
                       /\ flatten2' = Head(stack).flatten2
                       /\ stack' = Tail(stack)
            /\ UNCHANGED << point, characters, bytes, string, padded_message, 
                            output_hash, domain_string_, message_string, 
                            domain_bytes_, message_bits_, domain_bytes, 
                            message_bits, n, acc, i_s, 
                            first_incomplete_addition, 
                            second_incomplete_addition, i, slice, 
                            domain_string, message_bytes >>

Flatten2 == /\ pc = "Flatten2"
            /\ IF j <= Len(bits[i_])
                  THEN /\ flatten2' = Append(flatten1, bits[i_][j])
                       /\ flatten1' = flatten2'
                       /\ j' = j + 1
                       /\ pc' = "Flatten2"
                       /\ i_' = i_
                  ELSE /\ j' = 1
                       /\ i_' = i_ + 1
                       /\ pc' = "Flatten1"
                       /\ UNCHANGED << flatten1, flatten2 >>
            /\ UNCHANGED << point, characters, bytes, bits, string, 
                            padded_message, output_hash, stack, domain_string_, 
                            message_string, domain_bytes_, message_bits_, 
                            domain_bytes, message_bits, n, acc, i_s, 
                            first_incomplete_addition, 
                            second_incomplete_addition, i, slice, 
                            domain_string, message_bytes >>

bytes_to_bits == InitializeBits \/ BytesToBitSequence \/ Flatten1
                    \/ Flatten2

CalculateN == /\ pc = "CalculateN"
              /\ n' = (Len(message_bits) \div k)
              /\ pc' = "CallPad"
              /\ UNCHANGED << point, characters, bytes, bits, string, 
                              padded_message, output_hash, stack, 
                              domain_string_, message_string, domain_bytes_, 
                              message_bits_, i_, j, flatten1, flatten2, 
                              domain_bytes, message_bits, acc, i_s, 
                              first_incomplete_addition, 
                              second_incomplete_addition, i, slice, 
                              domain_string, message_bytes >>

CallPad == /\ pc = "CallPad"
           /\ stack' = << [ procedure |->  "pad",
                            pc        |->  "CallQ",
                            i         |->  i,
                            slice     |->  slice ] >>
                        \o stack
           /\ i' = 1
           /\ slice' = <<>>
           /\ pc' = "Pad"
           /\ UNCHANGED << point, characters, bytes, bits, string, 
                           padded_message, output_hash, domain_string_, 
                           message_string, domain_bytes_, message_bits_, i_, j, 
                           flatten1, flatten2, domain_bytes, message_bits, n, 
                           acc, i_s, first_incomplete_addition, 
                           second_incomplete_addition, domain_string, 
                           message_bytes >>

CallQ == /\ pc = "CallQ"
         /\ stack' = << [ procedure |->  "q",
                          pc        |->  "InitializeAcc" ] >>
                      \o stack
         /\ pc' = "Q"
         /\ UNCHANGED << point, characters, bytes, bits, string, 
                         padded_message, output_hash, domain_string_, 
                         message_string, domain_bytes_, message_bits_, i_, j, 
                         flatten1, flatten2, domain_bytes, message_bits, n, 
                         acc, i_s, first_incomplete_addition, 
                         second_incomplete_addition, i, slice, domain_string, 
                         message_bytes >>

InitializeAcc == /\ pc = "InitializeAcc"
                 /\ acc' = point
                 /\ pc' = "Loop"
                 /\ UNCHANGED << point, characters, bytes, bits, string, 
                                 padded_message, output_hash, stack, 
                                 domain_string_, message_string, domain_bytes_, 
                                 message_bits_, i_, j, flatten1, flatten2, 
                                 domain_bytes, message_bits, n, i_s, 
                                 first_incomplete_addition, 
                                 second_incomplete_addition, i, slice, 
                                 domain_string, message_bytes >>

Loop == /\ pc = "Loop"
        /\ IF i_s <= n
              THEN /\ pc' = "CallS"
              ELSE /\ pc' = "Results"
        /\ UNCHANGED << point, characters, bytes, bits, string, padded_message, 
                        output_hash, stack, domain_string_, message_string, 
                        domain_bytes_, message_bits_, i_, j, flatten1, 
                        flatten2, domain_bytes, message_bits, n, acc, i_s, 
                        first_incomplete_addition, second_incomplete_addition, 
                        i, slice, domain_string, message_bytes >>

CallS == /\ pc = "CallS"
         /\ bytes' = padded_message[i_s]
         /\ stack' = << [ procedure |->  "s",
                          pc        |->  "FirstIncompleteAddition" ] >>
                      \o stack
         /\ pc' = "CallI2LEOSP"
         /\ UNCHANGED << point, characters, bits, string, padded_message, 
                         output_hash, domain_string_, message_string, 
                         domain_bytes_, message_bits_, i_, j, flatten1, 
                         flatten2, domain_bytes, message_bits, n, acc, i_s, 
                         first_incomplete_addition, second_incomplete_addition, 
                         i, slice, domain_string, message_bytes >>

FirstIncompleteAddition == /\ pc = "FirstIncompleteAddition"
                           /\ first_incomplete_addition' = IncompleteAddition(acc, point)
                           /\ pc' = "SecondIncompleteAddition"
                           /\ UNCHANGED << point, characters, bytes, bits, 
                                           string, padded_message, output_hash, 
                                           stack, domain_string_, 
                                           message_string, domain_bytes_, 
                                           message_bits_, i_, j, flatten1, 
                                           flatten2, domain_bytes, 
                                           message_bits, n, acc, i_s, 
                                           second_incomplete_addition, i, 
                                           slice, domain_string, message_bytes >>

SecondIncompleteAddition == /\ pc = "SecondIncompleteAddition"
                            /\ second_incomplete_addition' = IncompleteAddition(first_incomplete_addition, acc)
                            /\ acc' = second_incomplete_addition'
                            /\ pc' = "Inc"
                            /\ UNCHANGED << point, characters, bytes, bits, 
                                            string, padded_message, 
                                            output_hash, stack, domain_string_, 
                                            message_string, domain_bytes_, 
                                            message_bits_, i_, j, flatten1, 
                                            flatten2, domain_bytes, 
                                            message_bits, n, i_s, 
                                            first_incomplete_addition, i, 
                                            slice, domain_string, 
                                            message_bytes >>

Inc == /\ pc = "Inc"
       /\ i_s' = i_s + 1
       /\ pc' = "Loop"
       /\ UNCHANGED << point, characters, bytes, bits, string, padded_message, 
                       output_hash, stack, domain_string_, message_string, 
                       domain_bytes_, message_bits_, i_, j, flatten1, flatten2, 
                       domain_bytes, message_bits, n, acc, 
                       first_incomplete_addition, second_incomplete_addition, 
                       i, slice, domain_string, message_bytes >>

Results == /\ pc = "Results"
           /\ point' = second_incomplete_addition
           /\ pc' = "CleanIndex"
           /\ UNCHANGED << characters, bytes, bits, string, padded_message, 
                           output_hash, stack, domain_string_, message_string, 
                           domain_bytes_, message_bits_, i_, j, flatten1, 
                           flatten2, domain_bytes, message_bits, n, acc, i_s, 
                           first_incomplete_addition, 
                           second_incomplete_addition, i, slice, domain_string, 
                           message_bytes >>

CleanIndex == /\ pc = "CleanIndex"
              /\ i_s' = 1
              /\ pc' = "Return"
              /\ UNCHANGED << point, characters, bytes, bits, string, 
                              padded_message, output_hash, stack, 
                              domain_string_, message_string, domain_bytes_, 
                              message_bits_, i_, j, flatten1, flatten2, 
                              domain_bytes, message_bits, n, acc, 
                              first_incomplete_addition, 
                              second_incomplete_addition, i, slice, 
                              domain_string, message_bytes >>

Return == /\ pc = "Return"
          /\ pc' = Head(stack).pc
          /\ n' = Head(stack).n
          /\ acc' = Head(stack).acc
          /\ i_s' = Head(stack).i_s
          /\ first_incomplete_addition' = Head(stack).first_incomplete_addition
          /\ second_incomplete_addition' = Head(stack).second_incomplete_addition
          /\ domain_bytes' = Head(stack).domain_bytes
          /\ message_bits' = Head(stack).message_bits
          /\ stack' = Tail(stack)
          /\ UNCHANGED << point, characters, bytes, bits, string, 
                          padded_message, output_hash, domain_string_, 
                          message_string, domain_bytes_, message_bits_, i_, j, 
                          flatten1, flatten2, i, slice, domain_string, 
                          message_bytes >>

sinsemilla_hash_to_point == CalculateN \/ CallPad \/ CallQ \/ InitializeAcc
                               \/ Loop \/ CallS \/ FirstIncompleteAddition
                               \/ SecondIncompleteAddition \/ Inc
                               \/ Results \/ CleanIndex \/ Return

Pad == /\ pc = "Pad"
       /\ IF i <= Len(bits)
             THEN /\ IF Len(slice) < k
                        THEN /\ slice' = Append(slice, bits[i])
                        ELSE /\ TRUE
                             /\ slice' = slice
                  /\ IF Len(slice') = k \/ i = Len(bits)
                        THEN /\ padded_message' = Append(padded_message, slice')
                             /\ pc' = "ResetSlice"
                        ELSE /\ pc' = "IncrementIndex"
                             /\ UNCHANGED padded_message
                  /\ UNCHANGED << stack, i >>
             ELSE /\ pc' = Head(stack).pc
                  /\ i' = Head(stack).i
                  /\ slice' = Head(stack).slice
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED padded_message
       /\ UNCHANGED << point, characters, bytes, bits, string, output_hash, 
                       domain_string_, message_string, domain_bytes_, 
                       message_bits_, i_, j, flatten1, flatten2, domain_bytes, 
                       message_bits, n, acc, i_s, first_incomplete_addition, 
                       second_incomplete_addition, domain_string, 
                       message_bytes >>

IncrementIndex == /\ pc = "IncrementIndex"
                  /\ i' = i + 1
                  /\ pc' = "Pad"
                  /\ UNCHANGED << point, characters, bytes, bits, string, 
                                  padded_message, output_hash, stack, 
                                  domain_string_, message_string, 
                                  domain_bytes_, message_bits_, i_, j, 
                                  flatten1, flatten2, domain_bytes, 
                                  message_bits, n, acc, i_s, 
                                  first_incomplete_addition, 
                                  second_incomplete_addition, slice, 
                                  domain_string, message_bytes >>

ResetSlice == /\ pc = "ResetSlice"
              /\ slice' = <<>>
              /\ pc' = "PadLastSlice"
              /\ UNCHANGED << point, characters, bytes, bits, string, 
                              padded_message, output_hash, stack, 
                              domain_string_, message_string, domain_bytes_, 
                              message_bits_, i_, j, flatten1, flatten2, 
                              domain_bytes, message_bits, n, acc, i_s, 
                              first_incomplete_addition, 
                              second_incomplete_addition, i, domain_string, 
                              message_bytes >>

PadLastSlice == /\ pc = "PadLastSlice"
                /\ IF Len(padded_message[Len(padded_message)]) < k
                      THEN /\ padded_message' = [padded_message EXCEPT ![Len(padded_message)] = Append(padded_message[Len(padded_message)], 0)]
                           /\ pc' = "PadLastSlice"
                      ELSE /\ pc' = "IncrementIndex"
                           /\ UNCHANGED padded_message
                /\ UNCHANGED << point, characters, bytes, bits, string, 
                                output_hash, stack, domain_string_, 
                                message_string, domain_bytes_, message_bits_, 
                                i_, j, flatten1, flatten2, domain_bytes, 
                                message_bits, n, acc, i_s, 
                                first_incomplete_addition, 
                                second_incomplete_addition, i, slice, 
                                domain_string, message_bytes >>

pad == Pad \/ IncrementIndex \/ ResetSlice \/ PadLastSlice

Q == /\ pc = "Q"
     /\ /\ domain_string' = "z.cash.SinsemillaQ"
        /\ message_bytes' = domain_bytes
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         domain_string |->  domain_string,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ pc' = "BytesToString_"
     /\ UNCHANGED << point, characters, bytes, bits, string, padded_message, 
                     output_hash, domain_string_, message_string, 
                     domain_bytes_, message_bits_, i_, j, flatten1, flatten2, 
                     domain_bytes, message_bits, n, acc, i_s, 
                     first_incomplete_addition, second_incomplete_addition, i, 
                     slice >>

q == Q

CallI2LEOSP == /\ pc = "CallI2LEOSP"
               /\ stack' = << [ procedure |->  "IntToLEOSP",
                                pc        |->  "S" ] >>
                            \o stack
               /\ pc' = "IntToLEOSP_"
               /\ UNCHANGED << point, characters, bytes, bits, string, 
                               padded_message, output_hash, domain_string_, 
                               message_string, domain_bytes_, message_bits_, 
                               i_, j, flatten1, flatten2, domain_bytes, 
                               message_bits, n, acc, i_s, 
                               first_incomplete_addition, 
                               second_incomplete_addition, i, slice, 
                               domain_string, message_bytes >>

S == /\ pc = "S"
     /\ /\ domain_string' = "z.cash:SinsemillaS"
        /\ message_bytes' = bytes
        /\ stack' = << [ procedure |->  "hash_to_pallas",
                         pc        |->  Head(stack).pc,
                         domain_string |->  domain_string,
                         message_bytes |->  message_bytes ] >>
                     \o Tail(stack)
     /\ pc' = "BytesToString_"
     /\ UNCHANGED << point, characters, bytes, bits, string, padded_message, 
                     output_hash, domain_string_, message_string, 
                     domain_bytes_, message_bits_, i_, j, flatten1, flatten2, 
                     domain_bytes, message_bits, n, acc, i_s, 
                     first_incomplete_addition, second_incomplete_addition, i, 
                     slice >>

s == CallI2LEOSP \/ S

BytesToString_ == /\ pc = "BytesToString_"
                  /\ bytes' = message_bytes
                  /\ stack' = << [ procedure |->  "bytes_to_string",
                                   pc        |->  "HashToPallas" ] >>
                               \o stack
                  /\ pc' = "BytesToString"
                  /\ UNCHANGED << point, characters, bits, string, 
                                  padded_message, output_hash, domain_string_, 
                                  message_string, domain_bytes_, message_bits_, 
                                  i_, j, flatten1, flatten2, domain_bytes, 
                                  message_bits, n, acc, i_s, 
                                  first_incomplete_addition, 
                                  second_incomplete_addition, i, slice, 
                                  domain_string, message_bytes >>

HashToPallas == /\ pc = "HashToPallas"
                /\ point' = [a |-> domain_string, b |-> string, baseX |-> baseX, baseY |-> baseY]
                /\ pc' = Head(stack).pc
                /\ domain_string' = Head(stack).domain_string
                /\ message_bytes' = Head(stack).message_bytes
                /\ stack' = Tail(stack)
                /\ UNCHANGED << characters, bytes, bits, string, 
                                padded_message, output_hash, domain_string_, 
                                message_string, domain_bytes_, message_bits_, 
                                i_, j, flatten1, flatten2, domain_bytes, 
                                message_bits, n, acc, i_s, 
                                first_incomplete_addition, 
                                second_incomplete_addition, i, slice >>

hash_to_pallas == BytesToString_ \/ HashToPallas

IntToLEOSP_ == /\ pc = "IntToLEOSP_"
               /\ TRUE
               /\ pc' = Head(stack).pc
               /\ stack' = Tail(stack)
               /\ UNCHANGED << point, characters, bytes, bits, string, 
                               padded_message, output_hash, domain_string_, 
                               message_string, domain_bytes_, message_bits_, 
                               i_, j, flatten1, flatten2, domain_bytes, 
                               message_bits, n, acc, i_s, 
                               first_incomplete_addition, 
                               second_incomplete_addition, i, slice, 
                               domain_string, message_bytes >>

IntToLEOSP == IntToLEOSP_

BytesToString == /\ pc = "BytesToString"
                 /\ string' = [b \in 1..Len(bytes) |-> Chr(bytes[b])]
                 /\ pc' = Head(stack).pc
                 /\ stack' = Tail(stack)
                 /\ UNCHANGED << point, characters, bytes, bits, 
                                 padded_message, output_hash, domain_string_, 
                                 message_string, domain_bytes_, message_bits_, 
                                 i_, j, flatten1, flatten2, domain_bytes, 
                                 message_bits, n, acc, i_s, 
                                 first_incomplete_addition, 
                                 second_incomplete_addition, i, slice, 
                                 domain_string, message_bytes >>

bytes_to_string == BytesToString

PointToBytes == /\ pc = "PointToBytes"
                /\ PrintT(point)
                /\ pc' = Head(stack).pc
                /\ stack' = Tail(stack)
                /\ UNCHANGED << point, characters, bytes, bits, string, 
                                padded_message, output_hash, domain_string_, 
                                message_string, domain_bytes_, message_bits_, 
                                i_, j, flatten1, flatten2, domain_bytes, 
                                message_bits, n, acc, i_s, 
                                first_incomplete_addition, 
                                second_incomplete_addition, i, slice, 
                                domain_string, message_bytes >>

point_to_bytes == PointToBytes

SinSemillaHashCall == /\ pc = "SinSemillaHashCall"
                      /\ /\ domain_string_' = <<"d", "o", "m", "a", "i", "n">>
                         /\ message_string' = <<"m", "e", "s", "s", "a", "g", "e">>
                         /\ stack' = << [ procedure |->  "sinsemilla_hash",
                                          pc        |->  "Done",
                                          domain_bytes_ |->  domain_bytes_,
                                          message_bits_ |->  message_bits_,
                                          domain_string_ |->  domain_string_,
                                          message_string |->  message_string ] >>
                                      \o stack
                      /\ domain_bytes_' = <<>>
                      /\ message_bits_' = <<>>
                      /\ pc' = "DomainToCharacters"
                      /\ UNCHANGED << point, characters, bytes, bits, string, 
                                      padded_message, output_hash, i_, j, 
                                      flatten1, flatten2, domain_bytes, 
                                      message_bits, n, acc, i_s, 
                                      first_incomplete_addition, 
                                      second_incomplete_addition, i, slice, 
                                      domain_string, message_bytes >>

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
