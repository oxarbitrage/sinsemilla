# Sinsemilla haskell implementation

A haskell sinsemilla hash function implementation using [PastaCurves](https://github.com/nccgroup/pasta-curves) and inspired by the [Zebra sinsemilla implementation in Rust](https://github.com/ZcashFoundation/zebra/blob/main/zebra-chain/src/orchard/sinsemilla.rs).

This is experimental/proof of concept code.

## Demo

```bash
stack run
```

or

```bash
cabal run
```

### Example:

```bash
% stack run 
---Sinsemilla hash function---

Insert a domain to be used:
test1
Insert message to be hashed:
this is a test

B64 encoded ciphertext:

VHCDjVMz9uY6bVLBE6/MM9vRZvxNRe3IIlyzVkky5Ro=

% 
```

## Tests

```bash
stack test
```

or

```bash
cabal test
```