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
    \* The bytes of the message to be hashed.
    plaintext_bytes = CharactersToBytes(SetToSeq(Message)),
    \* The bytes of the domain.
    domain_bytes = CharactersToBytes(SetToSeq(Domain)),
    \* The bits of the message.
    plaintext_bits = BytesToBits(plaintext_bytes),
    \* The padded slices of the message.
    plaintext_slices = DivideInChunks(PadBits(plaintext_bits, k), k),
    \* The point Q.
    point_q = HashToPallas(SinsemillaQ, domain_bytes),
    \* The accumulator.
    accumulator = point_q,
    \* The number of slices.
    n = CeilDiv(Len(plaintext_bits), k),
    \* The point S.
    point_s = [a |-> 0, b |-> 0],
    \* The bytes of the ciphertext.
    ciphertext_bytes = <<0, 0>>
define
    \* Check all type invariants.
    TypeInvariant == /\ IsBytes(plaintext_bytes) 
        /\ IsBytes(domain_bytes)
        /\ IsBits(plaintext_bits)
        /\ IsSlices(plaintext_slices)
        /\ IsPoint(point_q)
        /\ IsPoint(accumulator)
        /\ IsNumber(n)
        /\ IsPoint(point_s)
        /\ IsBytes(ciphertext_bytes)
    \* Accumulator accumulates.
    LivenessAccumulator == <> (accumulator # [a |-> 0, b |-> 0])
    \* The point S should eventually be different from the neutral element.
    LivenessS == <> (point_s # [a |-> 0, b |-> 0])
    \* The ciphertext should be the result of the hash function.
    LivenessCiphertext == <> (plaintext_bytes # ciphertext_bytes /\ ciphertext_bytes # <<0, 0>>)
    \* Check all liveness properties.
    Liveness == /\ LivenessAccumulator
        /\ LivenessS
        /\ LivenessCiphertext
    \* Check all safety invariants.
    Safety == /\ BytesSequence(plaintext_bytes)
        /\ BytesSequence(domain_bytes)
        /\ SlicesSequence(plaintext_slices, k)
        /\ MaxChunks(n, c)
        /\ PlainIsNotCipherText(plaintext_bytes, ciphertext_bytes)
end define;

\* The main process hash a given message using the Sinsemilla hash function. 
fair process main = "MAIN"
variables i = 1
begin
    Hash:
        point_s := HashToPallas(SinsemillaS, IntToLEOSP32(plaintext_slices[i]));
        accumulator := IncompleteAddition(IncompleteAddition(accumulator, point_s), accumulator);
        i := i + 1;
        if i > n then
            goto Decode;
        else 
            goto Hash;
        end if;
    \* Decode the hashed point coordinates to bytes.
    Decode:
        ciphertext_bytes := <<accumulator.a, accumulator.b>>;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f1a52f70" /\ chksum(tla) = "dd539d04")
VARIABLES plaintext_bytes, domain_bytes, plaintext_bits, plaintext_slices, 
          point_q, accumulator, n, point_s, ciphertext_bytes, pc

(* define statement *)
TypeInvariant == /\ IsBytes(plaintext_bytes)
    /\ IsBytes(domain_bytes)
    /\ IsBits(plaintext_bits)
    /\ IsSlices(plaintext_slices)
    /\ IsPoint(point_q)
    /\ IsPoint(accumulator)
    /\ IsNumber(n)
    /\ IsPoint(point_s)
    /\ IsBytes(ciphertext_bytes)

LivenessAccumulator == <> (accumulator # [a |-> 0, b |-> 0])

LivenessS == <> (point_s # [a |-> 0, b |-> 0])

LivenessCiphertext == <> (plaintext_bytes # ciphertext_bytes /\ ciphertext_bytes # <<0, 0>>)

Liveness == /\ LivenessAccumulator
    /\ LivenessS
    /\ LivenessCiphertext

Safety == /\ BytesSequence(plaintext_bytes)
    /\ BytesSequence(domain_bytes)
    /\ SlicesSequence(plaintext_slices, k)
    /\ MaxChunks(n, c)
    /\ PlainIsNotCipherText(plaintext_bytes, ciphertext_bytes)

VARIABLE i

vars == << plaintext_bytes, domain_bytes, plaintext_bits, plaintext_slices, 
           point_q, accumulator, n, point_s, ciphertext_bytes, pc, i >>

ProcSet == {"MAIN"}

Init == (* Global variables *)
        /\ plaintext_bytes = CharactersToBytes(SetToSeq(Message))
        /\ domain_bytes = CharactersToBytes(SetToSeq(Domain))
        /\ plaintext_bits = BytesToBits(plaintext_bytes)
        /\ plaintext_slices = DivideInChunks(PadBits(plaintext_bits, k), k)
        /\ point_q = HashToPallas(SinsemillaQ, domain_bytes)
        /\ accumulator = point_q
        /\ n = CeilDiv(Len(plaintext_bits), k)
        /\ point_s = [a |-> 0, b |-> 0]
        /\ ciphertext_bytes = <<0, 0>>
        (* Process main *)
        /\ i = 1
        /\ pc = [self \in ProcSet |-> "Hash"]

Hash == /\ pc["MAIN"] = "Hash"
        /\ point_s' = HashToPallas(SinsemillaS, IntToLEOSP32(plaintext_slices[i]))
        /\ accumulator' = IncompleteAddition(IncompleteAddition(accumulator, point_s'), accumulator)
        /\ i' = i + 1
        /\ IF i' > n
              THEN /\ pc' = [pc EXCEPT !["MAIN"] = "Decode"]
              ELSE /\ pc' = [pc EXCEPT !["MAIN"] = "Hash"]
        /\ UNCHANGED << plaintext_bytes, domain_bytes, plaintext_bits, 
                        plaintext_slices, point_q, n, ciphertext_bytes >>

Decode == /\ pc["MAIN"] = "Decode"
          /\ ciphertext_bytes' = <<accumulator.a, accumulator.b>>
          /\ pc' = [pc EXCEPT !["MAIN"] = "Done"]
          /\ UNCHANGED << plaintext_bytes, domain_bytes, plaintext_bits, 
                          plaintext_slices, point_q, accumulator, n, point_s, 
                          i >>

main == Hash \/ Decode

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(main)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
