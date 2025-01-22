---- MODULE sinsemilla ----
(***************************************************************************)
(* Sinsemilla hash function specification                                  *)
(*                                                                         *)
(* Specifies what is needed to implement a sinsemilla hash function        *)
(* algorithm.                                                              *)
(*                                                                         *)
(***************************************************************************)
EXTENDS TLC, Naturals, Integers, Sequences, Utils, Invariants

CONSTANT k, c, SinsemillaQ, SinsemillaS, Domain, Message

(*--algorithm sinsemilla

variables
    \* The algorithm state holds all the variables needed to run the algorithm.
    state = [
        \* Holder for a point on the Pallas curve.
        point |-> [a |-> 0, b |-> 0],
        \* Holder for a sequence of characters.
        characters |-> <<>>,
        \* Holder for a sequence of bytes.
        bytes |-> <<>>,
        \* Holder for a sequence of bytes when the bytes variable is already busy.
        domain_bytes |-> <<>>,
        \* Holder for a sequence of bits.
        bits |-> <<>>,
        \* Holder for a sequence of slices.
        slices |-> <<>>,
        \* Holder for a number, in particular the number of slices.
        n |-> 0,
        \* Holder for a number used as the current slice index in the main loop.
        i |-> 1,
        \* Holder for a point used as an accumulator.
        accumulator |-> [a |-> 0, b |-> 0],
        \* Holder for the ciphertext produced by the hash function.
        ciphertext |-> <<"@", "@">>
    ];

define
    \* Check all type invariants.
    InvType == /\ TypeInvariantPoint(state.point) 
        /\ TypeInvariantCharacters(state.characters)
        /\ TypeInvariantBytes(state.bytes)
        /\ TypeInvariantAuxiliarBytes(state.bytes)
        /\ TypeInvariantBits(state.bits)
        /\ TypeInvariantSlices(state.slices)

    \* Point holder will eventually end up with a point different than the starting one.
    LivenessPoint == <> (state.point # [a |-> 0, b |-> 0])
    \* Accumulator accumulates.
    LivenessAccumulator == <> (state.accumulator # [a |-> 0, b |-> 0])
    \* Index should always be incremented.
    LivenessIndex == <> (state.i > 1)
    \* Slices should always be produced.
    LivenessSlices == <> (Len(state.slices) > 0)
    \* Ciphertext should be produced.
    LivenessCipherValue == <> (state.ciphertext # <<"@", "@">>)
    \* Check all liveness properties.
    Liveness == /\ LivenessPoint
        /\ LivenessAccumulator
        /\ LivenessIndex
        /\ LivenessSlices
        /\ LivenessCipherValue

    \* Check all safety invariants.
    Safety == /\ SafetyBytesSequence(state.bytes)
        /\ SafetySlicesSequence(state.slices, k)
        /\ SafetyMaxChunks(state.n, c)
        /\ SafetyCipherSize(state.ciphertext)
        /\ SafetyPlainIsNotCipherText(SetToSeq(Message), state.ciphertext)
end define;

\* The starting procedure that do all the conversion needed with the domain and message constants,
\* call the main procedure to hash the message and decodes the resulting point coordinates to characters.
procedure sinsemilla_hash()
begin
    \* Encode the domain characters as bytes and store them in `domain_bytes` for later use.
    EncodeDomain:
        state.domain_bytes := CharactersToBytes(SetToSeq(Domain));
    \* Encode the message characters as bits and store them in `bits` for later use.
    EncodeMessage:
        state.bits := BytesToBits(CharactersToBytes(SetToSeq(Message)));
    \* With the domain bytes in `bytes` and the message bits in `bits`, call the main procedure to hash the message.
    SinsemillaHashToPoint:
        call sinsemilla_hash_to_point();
    \* Decode the point coordinates to characters.
    DecodeCipherText:
        state.ciphertext := BytesToCharacters(<<state.point.a, state.point.b>>);
    return;
end procedure;

\* The main procedure convert the message bits into a Pallas point, using the domain bytes stored in `bytes` as the
\* domain separator and the message bits stored in `bits` as the message.
procedure sinsemilla_hash_to_point()
begin
    Pad:
        \* Use the `bits` as input and get chunks in a padded `slices`.
        state.slices := DivideInChunks(PadBits(state.bits, k), k);
    Q:
        \* Produce a Pallas point with the state `domain_bytes`.
        state.point := HashToPallas(SinsemillaQ, state.domain_bytes);
    InitializeAcc:
        \* With the point we got from calling `q`, initialize the accumulator.
        state.accumulator := state.point;
    CalculateN:
        \* Calculate the number of slices needed to hash the message.
        state.n := Max(Len(state.bits), k) \div k;
    MainLoop:
        \* Loop over the slices.
        while state.i <= state.n do
            S:
                state.point := HashToPallas(SinsemillaS, IntToLEOSP32(state.slices[state.i]));
            Accumulate:
                \* Incomplete addition of the accumulator and the point.
                state := [state EXCEPT
                    !.accumulator = IncompleteAddition(IncompleteAddition(state.accumulator, state.point), state.accumulator),
                    !.i = state.i + 1
                ];
        end while;
    AssignAccumulatorToPoint:
        state.point := state.accumulator;
    return;
end procedure;

\* Single process that calls the starting procedure.
fair process main = "MAIN"
begin
    SinSemillaHashCall:
        call sinsemilla_hash();
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f72bec9c" /\ chksum(tla) = "21ac1bf3")
VARIABLES state, pc, stack

(* define statement *)
InvType == /\ TypeInvariantPoint(state.point)
    /\ TypeInvariantCharacters(state.characters)
    /\ TypeInvariantBytes(state.bytes)
    /\ TypeInvariantAuxiliarBytes(state.bytes)
    /\ TypeInvariantBits(state.bits)
    /\ TypeInvariantSlices(state.slices)


LivenessPoint == <> (state.point # [a |-> 0, b |-> 0])

LivenessAccumulator == <> (state.accumulator # [a |-> 0, b |-> 0])

LivenessIndex == <> (state.i > 1)

LivenessSlices == <> (Len(state.slices) > 0)

LivenessCipherValue == <> (state.ciphertext # <<"@", "@">>)

Liveness == /\ LivenessPoint
    /\ LivenessAccumulator
    /\ LivenessIndex
    /\ LivenessSlices
    /\ LivenessCipherValue


Safety == /\ SafetyBytesSequence(state.bytes)
    /\ SafetySlicesSequence(state.slices, k)
    /\ SafetyMaxChunks(state.n, c)
    /\ SafetyCipherSize(state.ciphertext)
    /\ SafetyPlainIsNotCipherText(SetToSeq(Message), state.ciphertext)


vars == << state, pc, stack >>

ProcSet == {"MAIN"}

Init == (* Global variables *)
        /\ state =         [
                   
                       point |-> [a |-> 0, b |-> 0],
                   
                       characters |-> <<>>,
                   
                       bytes |-> <<>>,
                   
                       domain_bytes |-> <<>>,
                   
                       bits |-> <<>>,
                   
                       slices |-> <<>>,
                   
                       n |-> 0,
                   
                       i |-> 1,
                   
                       accumulator |-> [a |-> 0, b |-> 0],
                   
                       ciphertext |-> <<"@", "@">>
                   ]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "SinSemillaHashCall"]

EncodeDomain(self) == /\ pc[self] = "EncodeDomain"
                      /\ state' = [state EXCEPT !.domain_bytes = CharactersToBytes(SetToSeq(Domain))]
                      /\ pc' = [pc EXCEPT ![self] = "EncodeMessage"]
                      /\ stack' = stack

EncodeMessage(self) == /\ pc[self] = "EncodeMessage"
                       /\ state' = [state EXCEPT !.bits = BytesToBits(CharactersToBytes(SetToSeq(Message)))]
                       /\ pc' = [pc EXCEPT ![self] = "SinsemillaHashToPoint"]
                       /\ stack' = stack

SinsemillaHashToPoint(self) == /\ pc[self] = "SinsemillaHashToPoint"
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sinsemilla_hash_to_point",
                                                                        pc        |->  "DecodeCipherText" ] >>
                                                                    \o stack[self]]
                               /\ pc' = [pc EXCEPT ![self] = "Pad"]
                               /\ state' = state

DecodeCipherText(self) == /\ pc[self] = "DecodeCipherText"
                          /\ state' = [state EXCEPT !.ciphertext = BytesToCharacters(<<state.point.a, state.point.b>>)]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

sinsemilla_hash(self) == EncodeDomain(self) \/ EncodeMessage(self)
                            \/ SinsemillaHashToPoint(self)
                            \/ DecodeCipherText(self)

Pad(self) == /\ pc[self] = "Pad"
             /\ state' = [state EXCEPT !.slices = DivideInChunks(PadBits(state.bits, k), k)]
             /\ pc' = [pc EXCEPT ![self] = "Q"]
             /\ stack' = stack

Q(self) == /\ pc[self] = "Q"
           /\ state' = [state EXCEPT !.point = HashToPallas(SinsemillaQ, state.domain_bytes)]
           /\ pc' = [pc EXCEPT ![self] = "InitializeAcc"]
           /\ stack' = stack

InitializeAcc(self) == /\ pc[self] = "InitializeAcc"
                       /\ state' = [state EXCEPT !.accumulator = state.point]
                       /\ pc' = [pc EXCEPT ![self] = "CalculateN"]
                       /\ stack' = stack

CalculateN(self) == /\ pc[self] = "CalculateN"
                    /\ state' = [state EXCEPT !.n = Max(Len(state.bits), k) \div k]
                    /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                    /\ stack' = stack

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ IF state.i <= state.n
                        THEN /\ pc' = [pc EXCEPT ![self] = "S"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "AssignAccumulatorToPoint"]
                  /\ UNCHANGED << state, stack >>

S(self) == /\ pc[self] = "S"
           /\ state' = [state EXCEPT !.point = HashToPallas(SinsemillaS, IntToLEOSP32(state.slices[state.i]))]
           /\ pc' = [pc EXCEPT ![self] = "Accumulate"]
           /\ stack' = stack

Accumulate(self) == /\ pc[self] = "Accumulate"
                    /\ state' =          [state EXCEPT
                                    !.accumulator = IncompleteAddition(IncompleteAddition(state.accumulator, state.point), state.accumulator),
                                    !.i = state.i + 1
                                ]
                    /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                    /\ stack' = stack

AssignAccumulatorToPoint(self) == /\ pc[self] = "AssignAccumulatorToPoint"
                                  /\ state' = [state EXCEPT !.point = state.accumulator]
                                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

sinsemilla_hash_to_point(self) == Pad(self) \/ Q(self)
                                     \/ InitializeAcc(self)
                                     \/ CalculateN(self) \/ MainLoop(self)
                                     \/ S(self) \/ Accumulate(self)
                                     \/ AssignAccumulatorToPoint(self)

SinSemillaHashCall == /\ pc["MAIN"] = "SinSemillaHashCall"
                      /\ stack' = [stack EXCEPT !["MAIN"] = << [ procedure |->  "sinsemilla_hash",
                                                                 pc        |->  "Done" ] >>
                                                             \o stack["MAIN"]]
                      /\ pc' = [pc EXCEPT !["MAIN"] = "EncodeDomain"]
                      /\ state' = state

main == SinSemillaHashCall

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet:  \/ sinsemilla_hash(self)
                                     \/ sinsemilla_hash_to_point(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(main)
           /\ WF_vars(sinsemilla_hash("MAIN"))
           /\ WF_vars(sinsemilla_hash_to_point("MAIN"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
