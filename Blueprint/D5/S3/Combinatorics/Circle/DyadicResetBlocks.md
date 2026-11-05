# Reset decomposition of arbitrary legal words

## Abstract

Reset decomposition of arbitrary legal words.

**Theorem 1.1 (Reset decomposition of arbitrary legal words).**

Lean statement: `D5/S3/Combinatorics/Circle/DyadicResetBlocks.reset_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/DyadicResetBlocks.reset_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any label type, integer-valued step function f, and integer height M, suppose each step is positive or equals -M. Every list W satisfying InStrip(f,M,0,W) decomposes exactly as packets(P) followed by a positive tail T. Each packet consists of a positive physical list of mass M and its actual reset label of value -M. The tail has mass between zero and M. This is a conclusion from every-prefix legality; no block placement or arrival gate is a premise.

The proof appends one actual label at a time. A positive label extends the tail. A reset is legal only when that tail has reached exactly M, and then closes a complete packet. Each complete packet has total zero. Positive monotonicity proves every interior prefix and the actual reset returns its endpoint to zero. Existing positive_block_strip is reused at its original owner.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/DyadicResetBlocks.reset_decomposition`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeBitSource](ThreeBitSource.md)
- Dependency: [D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange](TwoOppositeLargeExchange.md)
