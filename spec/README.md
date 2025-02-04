# Sinsemilla specification

## Motivation

This specification outlines all pieces needed for implementing the Sinsemilla hash function.

The Sinsemilla hash function is normatively specified in the [Sinsemilla Hash Function](https://zips.z.cash/protocol/protocol.pdf#concretesinsemillahash) section of the Zcash protocol spec and is also described in the [Halo2 Sinsemilla](https://zcash.github.io/halo2/design/gadgets/sinsemilla.html) section of the Halo2 book.

There are three known implementations used in production, although there might be more:

- The [Zebra implementation](https://github.com/ZcashFoundation/zebra/blob/v2.0.0/zebra-chain/src/orchard/sinsemilla.rs): Used in Zebra only for verification.
- The [Zcash implementation](https://github.com/zcash/sinsemilla): Sinsemilla primitives.
- The [Halo2 gadget implementation](https://github.com/zcash/halo2/blob/halo2_gadgets-0.3.0/halo2_gadgets/src/sinsemilla.rs): Designed for efficiency within circuits, it uses the Zcash implementation as a dependency.

A Sinsemilla hash function implementation depends on Pallas elliptic curve operations, specifically converting bytes into valid Pallas points, adding points, and converting back from a valid point into bytes. The [Pasta Curves](https://github.com/zcash/pasta_curves) library is well-known for this in Rust and is a dependency in the mentioned implementations.

Our goal is to provide a specification that aids in understanding the requirements for implementing the Sinsemilla hash function in any programming language with a Pasta Curves library. For Haskell, there is a similar [Haskell Pasta Curves library](https://github.com/nccgroup/pasta-curves), and we will use this specification to build a Haskell version of the Sinsemilla hash function.

This specification focuses on the less efficient version of the Sinsemilla hash function, suitable for implementation outside a circuit.

## The specification

The algorithm is a single process written in PlusCal, which is translated to TLA+ in the same file. Additional modules are pure TLA+ code. Here are the most important files:

- PlusCal and translated TLA+ spec: [Spec](sinsemilla.tla), [PDF](sinsemilla.pdf)
- Operators: [Spec](Utils.tla), [PDF](Utils.pdf)
- Configuration file: [sinsemilla.cfg](sinsemilla.cfg)

### General Structure

The spec has a well-defined structure:

- **Constants**: Values that never change, such as the maximum number of allowed slices and the domain separator strings used in different parts of the algorithm.

- **State variables**: Variables the algorithm need for executions, declared and initialized.

- **Properties**: The invariant and properties we want the algorithm to hold.

- **Process**: The hashing algorithm.

## Conclusion

This specification was created for learning purposes, to refine specification writing skills, and to improve the [Haskell Sinsemilla](https://github.com/oxarbitrage/sinsemilla) implementation by better understanding the system. It is shared in the hope that it will help others as well.
