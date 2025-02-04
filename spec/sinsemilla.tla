---- MODULE sinsemilla ----
(***************************************************************************)
(* Sinsemilla hash function spec.                                          *)
(*                                                                         *)
(* Specifies the Sinsemilla hash function algorithm.                       *)
(*                                                                         *)
(* All variables defined represent the state of the algorithm at any given *)
(* time. The algorithm is composed of a single process that hashes a       *)
(* message using the Sinsemilla hash function and predefined constants.    *)
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
    \* The type invariant.
    TypeInvariant == /\ IsBytes(plaintext_bytes) /\ IsBytes(domain_bytes) /\ IsBits(plaintext_bits)
        /\ IsSlices(plaintext_slices) /\ IsPoint(point_q)  /\ IsPoint(accumulator) /\ IsNumber(n)
        /\ IsPoint(point_s) /\ IsBytes(ciphertext_bytes)
    \* The liveness properties.
    Liveness == /\ <> (accumulator # [a |-> 0, b |-> 0]) /\ <> (point_s # [a |-> 0, b |-> 0])
        /\ <> (plaintext_bytes # ciphertext_bytes /\ ciphertext_bytes # <<0, 0>>)
    \* The safety invariants.
    Safety == /\ BytesSequence(plaintext_bytes) /\ BytesSequence(domain_bytes)
        /\ SlicesSequence(plaintext_slices, k) /\ MaxChunks(n, c)
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
\* BEGIN TRANSLATION (chksum(pcal) = "4507b428" /\ chksum(tla) = "f7ed0fa5")
VARIABLES pc, plaintext_bytes, domain_bytes, plaintext_bits, plaintext_slices, 
          point_q, accumulator, n, point_s, ciphertext_bytes

(* define statement *)
TypeInvariant == /\ IsBytes(plaintext_bytes) /\ IsBytes(domain_bytes) /\ IsBits(plaintext_bits)
    /\ IsSlices(plaintext_slices) /\ IsPoint(point_q)  /\ IsPoint(accumulator) /\ IsNumber(n)
    /\ IsPoint(point_s) /\ IsBytes(ciphertext_bytes)

Liveness == /\ <> (accumulator # [a |-> 0, b |-> 0]) /\ <> (point_s # [a |-> 0, b |-> 0])
    /\ <> (plaintext_bytes # ciphertext_bytes /\ ciphertext_bytes # <<0, 0>>)

Safety == /\ BytesSequence(plaintext_bytes) /\ BytesSequence(domain_bytes)
    /\ SlicesSequence(plaintext_slices, k) /\ MaxChunks(n, c)
    /\ PlainIsNotCipherText(plaintext_bytes, ciphertext_bytes)

VARIABLE i

vars == << pc, plaintext_bytes, domain_bytes, plaintext_bits, 
           plaintext_slices, point_q, accumulator, n, point_s, 
           ciphertext_bytes, i >>

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
