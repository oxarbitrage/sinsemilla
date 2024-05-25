# Sinsemilla specification

## Motivation

This specification outlines a potential design for implementing the Sinsemilla hash function.

The Sinsemilla hash function is normatively specified in the [Sinsemilla Hash Function](https://zips.z.cash/protocol/protocol.pdf#concretesinsemillahash) section of the Zcash protocol spec and is also described in the [Halo2 Sinsemilla](https://zcash.github.io/halo2/design/gadgets/sinsemilla.html) section of the Halo2 book.

There are two known implementations used in production, although there might be more:

- The [Zebra implementation](https://github.com/ZcashFoundation/zebra/blob/v1.7.0/zebra-chain/src/orchard/sinsemilla.rs): Used in Zebra only for verification. 
- The [Halo2 gadget implementation](https://github.com/zcash/halo2/blob/halo2_proofs-0.3.0/halo2_gadgets/src/sinsemilla.rs): Designed for efficiency within circuits.

Both implementations are written in Rust and produce the same hash output. The Halo2 implementation is more efficient by design within circuits, whereas the Zebra implementation, used outside any circuit context, is less efficient but secure.

Any Sinsemilla hash function implementation depends on Pallas elliptic curve operations, specifically converting bytes into valid Pallas points, adding points, and converting back from a valid point into bytes. The [Pasta Curves](https://github.com/zcash/pasta_curves) library is well-known for this in Rust and is a dependency in both mentioned implementations.

Our goal is to provide a specification that aids in understanding the requirements for implementing the Sinsemilla hash function in any programming language with a Pasta Curves library. For Haskell, there is a similar [Haskell Pasta Curves library](https://github.com/nccgroup/pasta-curves), and we will use this specification to build a Haskell version of the Sinsemilla hash function.

This specification focuses on the less efficient version of the Sinsemilla hash function, suitable for implementation outside a circuit.

## The specification

The specification is written as a PlusCal algorithm, which is then translated to TLA+.

- PlusCal and TLA+ spec code: [sinsemilla.tla](sinsemilla.tla)
- Configuration: [sinsemilla.cfg](sinsemilla.cfg)
- Generated PDF: [sinsemilla.pdf](sinsemilla.pdf)

### General Structure

The spec has a well-defined structure:

- **Global variables**: Named memory holders available in any of the program states.

- **Constants**: Values that never change, such as the maximum number of allowed slices and the domain separator strings used in different parts of the algorithm.

- **Operators**: Defines the `IncompleteAddition` operator for summing coordinates of two points on the Pallas curve.

- **Type invariants**: Ensures global variables are of specific types across the algorithm's behavior, which is important in untyped environments.

- **Liveness property**: Ensures certain global variables evolve as the algorithm runs.

- **Safety properties**: Checks properties of global variables that must hold across different parts of the algorithm during execution.

- **Macros**: Standard conversion functions defined as macros, likely available in programming environments and may not need coding in Rust or Haskell except for the `point_to_bytes` which is a Pasta Curves library function.

- **Procedures**: Contains the main algorithm, including the main loop and all necessary procedures. The starting procedure `sinsemilla_hash` encodes domain and message strings in the right variables and calls the main procedure `sinsemilla_hash_to_point`. This procedure processes message slices, converting them into Pallas points using `q` and `s` procedures. The slices are accumulated by the `IncompleteAddition` operator to finally get a point, which is then decoded into bytes to produce a hashed string.

- **Processes**: The algorithm runs as a single `MAIN` process that calls the `sinsemilla_hash` procedure with given arguments.

## Conclusion

This specification was created for learning purposes, to refine specification writing skills, and to improve the [Haskell Sinsemilla](https://github.com/oxarbitrage/sinsemilla) implementation by better understanding the system. It is shared in the hope that it will help others as well.
