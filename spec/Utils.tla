-------------------------------- MODULE Utils -------------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Randomization

Ord(c) ==
    CASE
        c = "/x00" -> 0   \* Null character
        [] c = "/x01" -> 1
        [] c = "/x02" -> 2
        [] c = "/x03" -> 3
        [] c = "/x04" -> 4
        [] c = "/x05" -> 5
        [] c = "/x06" -> 6
        [] c = "/x07" -> 7
        [] c = "/x08" -> 8
        [] c = "/x09" -> 9   \* Tab
        [] c = "/x0A" -> 10  \* Line Feed
        [] c = "/x0B" -> 11
        [] c = "/x0C" -> 12
        [] c = "/x0D" -> 13  \* Carriage Return
        [] c = "/x0E" -> 14
        [] c = "/x0F" -> 15
        [] c = "/x10" -> 16
        [] c = "/x11" -> 17
        [] c = "/x12" -> 18
        [] c = "/x13" -> 19
        [] c = "/x14" -> 20
        [] c = "/x15" -> 21
        [] c = "/x16" -> 22
        [] c = "/x17" -> 23
        [] c = "/x18" -> 24
        [] c = "/x19" -> 25
        [] c = "/x1A" -> 26
        [] c = "/x1B" -> 27  \* Escape
        [] c = "/x1C" -> 28
        [] c = "/x1D" -> 29
        [] c = "/x1E" -> 30
        [] c = "/x1F" -> 31
        [] c = " " -> 32
        [] c = "!" -> 33
        [] c = "\"" -> 34
        [] c = "#" -> 35
        [] c = "$" -> 36
        [] c = "%" -> 37
        [] c = "&" -> 38
        [] c = "'" -> 39
        [] c = "(" -> 40
        [] c = ")" -> 41
        [] c = "*" -> 42
        [] c = "+" -> 43
        [] c = "," -> 44
        [] c = "-" -> 45
        [] c = "." -> 46
        [] c = "/" -> 47
        [] c = "0" -> 48
        [] c = "1" -> 49
        [] c = "2" -> 50
        [] c = "3" -> 51
        [] c = "4" -> 52
        [] c = "5" -> 53
        [] c = "6" -> 54
        [] c = "7" -> 55
        [] c = "8" -> 56
        [] c = "9" -> 57
        [] c = ":" -> 58
        [] c = ";" -> 59
        [] c = "<" -> 60
        [] c = "=" -> 61
        [] c = ">" -> 62
        [] c = "?" -> 63
        [] c = "@" -> 64
        [] c = "A" -> 65
        [] c = "B" -> 66
        [] c = "C" -> 67
        [] c = "D" -> 68
        [] c = "E" -> 69
        [] c = "F" -> 70
        [] c = "G" -> 71
        [] c = "H" -> 72
        [] c = "I" -> 73
        [] c = "J" -> 74
        [] c = "K" -> 75
        [] c = "L" -> 76
        [] c = "M" -> 77
        [] c = "N" -> 78
        [] c = "O" -> 79
        [] c = "P" -> 80
        [] c = "Q" -> 81
        [] c = "R" -> 82
        [] c = "S" -> 83
        [] c = "T" -> 84
        [] c = "U" -> 85
        [] c = "V" -> 86
        [] c = "W" -> 87
        [] c = "X" -> 88
        [] c = "Y" -> 89
        [] c = "Z" -> 90
        [] c = "[" -> 91
        [] c = "\\" -> 92
        [] c = "]" -> 93
        [] c = "^" -> 94
        [] c = "_" -> 95
        \*[] c = "`" -> 96
        [] c = "a" -> 97
        [] c = "b" -> 98
        [] c = "c" -> 99
        [] c = "d" -> 100
        [] c = "e" -> 101
        [] c = "f" -> 102
        [] c = "g" -> 103
        [] c = "h" -> 104
        [] c = "i" -> 105
        [] c = "j" -> 106
        [] c = "k" -> 107
        [] c = "l" -> 108
        [] c = "m" -> 109
        [] c = "n" -> 110
        [] c = "o" -> 111
        [] c = "p" -> 112
        [] c = "q" -> 113
        [] c = "r" -> 114
        [] c = "s" -> 115
        [] c = "t" -> 116
        [] c = "u" -> 117
        [] c = "v" -> 118
        [] c = "w" -> 119
        [] c = "x" -> 120
        [] c = "y" -> 121
        [] c = "z" -> 122
        [] c = "{" -> 123
        [] c = "|" -> 124
        [] c = "}" -> 125
        [] c = "~" -> 126
        [] c = "/x7F" -> 127
        [] c = "/x80" -> 128
        [] c = "/x81" -> 129
        [] c = "/x82" -> 130
        [] c = "/x83" -> 131
        [] c = "/x84" -> 132
        [] c = "/x85" -> 133
        [] c = "/x86" -> 134
        [] c = "/x87" -> 135
        [] c = "/x88" -> 136
        [] c = "/x89" -> 137
        [] c = "/x8A" -> 138
        [] c = "/x8B" -> 139
        [] c = "/x8C" -> 140
        [] c = "/x8D" -> 141
        [] c = "/x8E" -> 142
        [] c = "/x8F" -> 143
        [] c = "/x90" -> 144
        [] c = "/x91" -> 145
        [] c = "/x92" -> 146
        [] c = "/x93" -> 147
        [] c = "/x94" -> 148
        [] c = "/x95" -> 149
        [] c = "/x96" -> 150
        [] c = "/x97" -> 151
        [] c = "/x98" -> 152
        [] c = "/x99" -> 153
        [] c = "/x9A" -> 154
        [] c = "/x9B" -> 155
        [] c = "/x9C" -> 156
        [] c = "/x9D" -> 157
        [] c = "/x9E" -> 158
        [] c = "/x9F" -> 159
        [] c = "/xA0" -> 160
        [] c = "/xA1" -> 161
        [] c = "/xA2" -> 162
        [] c = "/xA3" -> 163
        [] c = "/xA4" -> 164
        [] c = "/xA5" -> 165
        [] c = "/xA6" -> 166
        [] c = "/xA7" -> 167
        [] c = "/xA8" -> 168
        [] c = "/xA9" -> 169
        [] c = "/xAA" -> 170
        [] c = "/xAB" -> 171
        [] c = "/xAC" -> 172
        [] c = "/xAD" -> 173
        [] c = "/xAE" -> 174
        [] c = "/xAF" -> 175
        [] c = "/xB0" -> 176
        [] c = "/xB1" -> 177
        [] c = "/xB2" -> 178
        [] c = "/xB3" -> 179
        [] c = "/xB4" -> 180
        [] c = "/xB5" -> 181
        [] c = "/xB6" -> 182
        [] c = "/xB7" -> 183
        [] c = "/xB8" -> 184
        [] c = "/xB9" -> 185
        [] c = "/xBA" -> 186
        [] c = "/xBB" -> 187
        [] c = "/xBC" -> 188
        [] c = "/xBD" -> 189
        [] c = "/xBE" -> 190
        [] c = "/xBF" -> 191
        [] c = "/xC0" -> 192
        [] c = "/xC1" -> 193
        [] c = "/xC2" -> 194
        [] c = "/xC3" -> 195
        [] c = "/xC4" -> 196
        [] c = "/xC5" -> 197
        [] c = "/xC6" -> 198
        [] c = "/xC7" -> 199
        [] c = "/xC8" -> 200
        [] c = "/xC9" -> 201
        [] c = "/xCA" -> 202
        [] c = "/xCB" -> 203
        [] c = "/xCC" -> 204
        [] c = "/xCD" -> 205
        [] c = "/xCE" -> 206
        [] c = "/xCF" -> 207
        [] c = "/xD0" -> 208
        [] c = "/xD1" -> 209
        [] c = "/xD2" -> 210
        [] c = "/xD3" -> 211
        [] c = "/xD4" -> 212
        [] c = "/xD5" -> 213
        [] c = "/xD6" -> 214
        [] c = "/xD7" -> 215
        [] c = "/xD8" -> 216
        [] c = "/xD9" -> 217
        [] c = "/xDA" -> 218
        [] c = "/xDB" -> 219
        [] c = "/xDC" -> 220
        [] c = "/xDD" -> 221
        [] c = "/xDE" -> 222
        [] c = "/xDF" -> 223
        [] c = "/xE0" -> 224
        [] c = "/xE1" -> 225
        [] c = "/xE2" -> 226
        [] c = "/xE3" -> 227
        [] c = "/xE4" -> 228
        [] c = "/xE5" -> 229
        [] c = "/xE6" -> 230
        [] c = "/xE7" -> 231
        [] c = "/xE8" -> 232
        [] c = "/xE9" -> 233
        [] c = "/xEA" -> 234
        [] c = "/xEB" -> 235
        [] c = "/xEC" -> 236
        [] c = "/xED" -> 237
        [] c = "/xEE" -> 238
        [] c = "/xEF" -> 239
        [] c = "/xF0" -> 240
        [] c = "/xF1" -> 241
        [] c = "/xF2" -> 242
        [] c = "/xF3" -> 243
        [] c = "/xF4" -> 244
        [] c = "/xF5" -> 245
        [] c = "/xF6" -> 246
        [] c = "/xF7" -> 247
        [] c = "/xF8" -> 248
        [] c = "/xF9" -> 249
        [] c = "/xFA" -> 250
        [] c = "/xFB" -> 251
        [] c = "/xFC" -> 252
        [] c = "/xFD" -> 253
        [] c = "/xFE" -> 254
        [] c = "/xFF" -> 255
        [] OTHER -> 0   \* Default to 0 for unspecified characters

Chr(b) ==
    CASE
        b = 0 -> "/x00"
        [] b = 1 -> "/x01"
        [] b = 2 -> "/x02"
        [] b = 3 -> "/x03"
        [] b = 4 -> "/x04"
        [] b = 5 -> "/x05"
        [] b = 6 -> "/x06"
        [] b = 7 -> "/x07"
        [] b = 8 -> "/x08"
        [] b = 9 -> "/x09"
        [] b = 10 -> "/x0A"
        [] b = 11 -> "/x0B"
        [] b = 12 -> "/x0C"
        [] b = 13 -> "/x0D"
        [] b = 14 -> "/x0E"
        [] b = 15 -> "/x0F"
        [] b = 16 -> "/x10"
        [] b = 17 -> "/x11"
        [] b = 18 -> "/x12"
        [] b = 19 -> "/x13"
        [] b = 20 -> "/x14"
        [] b = 21 -> "/x15"
        [] b = 22 -> "/x16"
        [] b = 23 -> "/x17"
        [] b = 24 -> "/x18"
        [] b = 25 -> "/x19"
        [] b = 26 -> "/x1A"
        [] b = 27 -> "/x1B"
        [] b = 28 -> "/x1C"
        [] b = 29 -> "/x1D"
        [] b = 30 -> "/x1E"
        [] b = 31 -> "/x1F"
        [] b = 32 -> " "
        [] b = 33 -> "!"
        [] b = 34 -> "\""
        [] b = 35 -> "#"
        [] b = 36 -> "$"
        [] b = 37 -> "%"
        [] b = 38 -> "&"
        [] b = 39 -> "'"
        [] b = 40 -> "("
        [] b = 41 -> ")"
        [] b = 42 -> "*"
        [] b = 43 -> "+"
        [] b = 44 -> ","
        [] b = 45 -> "-"
        [] b = 46 -> "."
        [] b = 47 -> "/"
        [] b = 48 -> "0"
        [] b = 49 -> "1"
        [] b = 50 -> "2"
        [] b = 51 -> "3"
        [] b = 52 -> "4"
        [] b = 53 -> "5"
        [] b = 54 -> "6"
        [] b = 55 -> "7"
        [] b = 56 -> "8"
        [] b = 57 -> "9"
        [] b = 58 -> ":"
        [] b = 59 -> ";"
        [] b = 60 -> "<"
        [] b = 61 -> "="
        [] b = 62 -> ">"
        [] b = 63 -> "?"
        [] b = 64 -> "@"
        [] b = 65 -> "A"
        [] b = 66 -> "B"
        [] b = 67 -> "C"
        [] b = 68 -> "D"
        [] b = 69 -> "E"
        [] b = 70 -> "F"
        [] b = 71 -> "G"
        [] b = 72 -> "H"
        [] b = 73 -> "I"
        [] b = 74 -> "J"
        [] b = 75 -> "K"
        [] b = 76 -> "L"
        [] b = 77 -> "M"
        [] b = 78 -> "N"
        [] b = 79 -> "O"
        [] b = 80 -> "P"
        [] b = 81 -> "Q"
        [] b = 82 -> "R"
        [] b = 83 -> "S"
        [] b = 84 -> "T"
        [] b = 85 -> "U"
        [] b = 86 -> "V"
        [] b = 87 -> "W"
        [] b = 88 -> "X"
        [] b = 89 -> "Y"
        [] b = 90 -> "Z"
        [] b = 91 -> "["
        [] b = 92 -> "\\"
        [] b = 93 -> "]"
        [] b = 94 -> "^"
        [] b = 95 -> "_"
        \*[] b = 96 -> "`"
        [] b = 97 -> "a"
        [] b = 98 -> "b"
        [] b = 99 -> "c"
        [] b = 100 -> "d"
        [] b = 101 -> "e"
        [] b = 102 -> "f"
        [] b = 103 -> "g"
        [] b = 104 -> "h"
        [] b = 105 -> "i"
        [] b = 106 -> "j"
        [] b = 107 -> "k"
        [] b = 108 -> "l"
        [] b = 109 -> "m"
        [] b = 110 -> "n"
        [] b = 111 -> "o"
        [] b = 112 -> "p"
        [] b = 113 -> "q"
        [] b = 114 -> "r"
        [] b = 115 -> "s"
        [] b = 116 -> "t"
        [] b = 117 -> "u"
        [] b = 118 -> "v"
        [] b = 119 -> "w"
        [] b = 120 -> "x"
        [] b = 121 -> "y"
        [] b = 122 -> "z"
        [] b = 123 -> "{"
        [] b = 124 -> "|"
        [] b = 125 -> "}"
        [] b = 126 -> "~"
        [] b = 127 -> "/x7F"
        [] b = 128 -> "/x80"
        [] b = 129 -> "/x81"
        [] b = 130 -> "/x82"
        [] b = 131 -> "/x83"
        [] b = 132 -> "/x84"
        [] b = 133 -> "/x85"
        [] b = 134 -> "/x86"
        [] b = 135 -> "/x87"
        [] b = 136 -> "/x88"
        [] b = 137 -> "/x89"
        [] b = 138 -> "/x8A"
        [] b = 139 -> "/x8B"
        [] b = 140 -> "/x8C"
        [] b = 141 -> "/x8D"
        [] b = 142 -> "/x8E"
        [] b = 143 -> "/x8F"
        [] b = 144 -> "/x90"
        [] b = 145 -> "/x91"
        [] b = 146 -> "/x92"
        [] b = 147 -> "/x93"
        [] b = 148 -> "/x94"
        [] b = 149 -> "/x95"
        [] b = 150 -> "/x96"
        [] b = 151 -> "/x97"
        [] b = 152 -> "/x98"
        [] b = 153 -> "/x99"
        [] b = 154 -> "/x9A"
        [] b = 155 -> "/x9B"
        [] b = 156 -> "/x9C"
        [] b = 157 -> "/x9D"
        [] b = 158 -> "/x9E"
        [] b = 159 -> "/x9F"
        [] b = 160 -> "/xA0"
        [] b = 161 -> "/xA1"
        [] b = 162 -> "/xA2"
        [] b = 163 -> "/xA3"
        [] b = 164 -> "/xA4"
        [] b = 165 -> "/xA5"
        [] b = 166 -> "/xA6"
        [] b = 167 -> "/xA7"
        [] b = 168 -> "/xA8"
        [] b = 169 -> "/xA9"
        [] b = 170 -> "/xAA"
        [] b = 171 -> "/xAB"
        [] b = 172 -> "/xAC"
        [] b = 173 -> "/xAD"
        [] b = 174 -> "/xAE"
        [] b = 175 -> "/xAF"
        [] b = 176 -> "/xB0"
        [] b = 177 -> "/xB1"
        [] b = 178 -> "/xB2"
        [] b = 179 -> "/xB3"
        [] b = 180 -> "/xB4"
        [] b = 181 -> "/xB5"
        [] b = 182 -> "/xB6"
        [] b = 183 -> "/xB7"
        [] b = 184 -> "/xB8"
        [] b = 185 -> "/xB9"
        [] b = 186 -> "/xBA"
        [] b = 187 -> "/xBB"
        [] b = 188 -> "/xBC"
        [] b = 189 -> "/xBD"
        [] b = 190 -> "/xBE"
        [] b = 191 -> "/xBF"
        [] b = 192 -> "/xC0"
        [] b = 193 -> "/xC1"
        [] b = 194 -> "/xC2"
        [] b = 195 -> "/xC3"
        [] b = 196 -> "/xC4"
        [] b = 197 -> "/xC5"
        [] b = 198 -> "/xC6"
        [] b = 199 -> "/xC7"
        [] b = 200 -> "/xC8"
        [] b = 201 -> "/xC9"
        [] b = 202 -> "/xCA"
        [] b = 203 -> "/xCB"
        [] b = 204 -> "/xCC"
        [] b = 205 -> "/xCD"
        [] b = 206 -> "/xCE"
        [] b = 207 -> "/xCF"
        [] b = 208 -> "/xD0"
        [] b = 209 -> "/xD1"
        [] b = 210 -> "/xD2"
        [] b = 211 -> "/xD3"
        [] b = 212 -> "/xD4"
        [] b = 213 -> "/xD5"
        [] b = 214 -> "/xD6"
        [] b = 215 -> "/xD7"
        [] b = 216 -> "/xD8"
        [] b = 217 -> "/xD9"
        [] b = 218 -> "/xDA"
        [] b = 219 -> "/xDB"
        [] b = 220 -> "/xDC"
        [] b = 221 -> "/xDD"
        [] b = 222 -> "/xDE"
        [] b = 223 -> "/xDF"
        [] b = 224 -> "/xE0"
        [] b = 225 -> "/xE1"
        [] b = 226 -> "/xE2"
        [] b = 227 -> "/xE3"
        [] b = 228 -> "/xE4"
        [] b = 229 -> "/xE5"
        [] b = 230 -> "/xE6"
        [] b = 231 -> "/xE7"
        [] b = 232 -> "/xE8"
        [] b = 233 -> "/xE9"
        [] b = 234 -> "/xEA"
        [] b = 235 -> "/xEB"
        [] b = 236 -> "/xEC"
        [] b = 237 -> "/xED"
        [] b = 238 -> "/xEE"
        [] b = 239 -> "/xEF"
        [] b = 240 -> "/xF0"
        [] b = 241 -> "/xF1"
        [] b = 242 -> "/xF2"
        [] b = 243 -> "/xF3"
        [] b = 244 -> "/xF4"
        [] b = 245 -> "/xF5"
        [] b = 246 -> "/xF6"
        [] b = 247 -> "/xF7"
        [] b = 248 -> "/xF8"
        [] b = 249 -> "/xF9"
        [] b = 250 -> "/xFA"
        [] b = 251 -> "/xFB"
        [] b = 252 -> "/xFC"
        [] b = 253 -> "/xFD"
        [] b = 254 -> "/xFE"
        [] b = 255 -> "/xFF"
        [] OTHER -> "@"  \* Default to "@" for unspecified byte values

ByteToBitSequence(b) ==
    LET
        Bit(i) == IF b \div (2^i) % 2 = 1 THEN 1 ELSE 0
    IN
        << Bit(7), Bit(6), Bit(5), Bit(4), Bit(3), Bit(2), Bit(1), Bit(0) >>

BitSequenceToByte(bits) ==
    LET
        BitValue(pos) == IF bits[pos + 1] = 1 THEN 2^(7-pos) ELSE 0
    IN
        BitValue(0) + BitValue(1) + BitValue(2) + BitValue(3) +
        BitValue(4) + BitValue(5) + BitValue(6) + BitValue(7)

Max(a, b) == IF a >= b THEN a ELSE b

\* Community modules imported stuff

\* A flatten operator copied from https://github.com/tlaplus/CommunityModules/blob/master/modules/SequencesExt.tla
FlattenSeq(seqs) ==
(**************************************************************************)
(* A sequence of all elements from all sequences in the sequence  seqs  . *)
(*                                                                        *)
(* Examples:                                                              *)
(*                                                                        *)
(*  FlattenSeq(<< <<1,2>>, <<1>> >>) = << 1, 2, 1 >>                      *)
(*  FlattenSeq(<< <<"a">>, <<"b">> >>) = <<"a", "b">>                     *)
(*  FlattenSeq(<< "a", "b" >>) = "ab"                                     *)
(**************************************************************************)
IF Len(seqs) = 0 THEN seqs ELSE
    \* Not via  FoldSeq(\o, <<>>, seqs)  here to support strings with TLC.
    LET flatten[i \in 1..Len(seqs)] ==
        IF i = 1 THEN seqs[i] ELSE flatten[i-1] \o seqs[i]
    IN flatten[Len(seqs)]

(***************************************************************************)
(* A function is injective iff it maps each element in its domain to a     *)
(* distinct element.                                                       *)
(*                                                                         *)
(* This definition is overridden by TLC in the Java class Functions.java   *)
(* The operator is overridden by the Java method with the same name.       *)
(***************************************************************************)
IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b

ToSet(s) ==
  (*************************************************************************)
  (* The image of the given sequence s. Cardinality(ToSet(s)) <= Len(s)    *)
  (* see https://en.wikipedia.org/wiki/Image_(mathematics)                 *)
  (*************************************************************************)
  { s[i] : i \in DOMAIN s }

SetToSeq(S) == 
(**************************************************************************)
(* Convert a set to some sequence that contains all the elements of the   *)
(* set exactly once, and contains no other elements.                      *)
(**************************************************************************)
CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

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


=============================================================================
