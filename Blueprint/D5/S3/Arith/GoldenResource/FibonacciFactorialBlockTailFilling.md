# Fibonacci Factorial Block Tail Filling

## Abstract

Separated factorial blocks fill every rational tail despite vanishing coordinate masses.

Write G_n = fib(n+2), so the row begins 1, 2, 3, 5. For every positive j, choose a finite index set I_j of cardinality j times j!, with j! dividing G_n on I_j, and place each block strictly before all later blocks. The blocks need not be intervals; set I_0 to the empty set. Define A_n = G_n/j! on I_j and zero outside the blocks. Separation makes the block index unique, and each capacity is a finite natural number.

**Theorem 1.1 (Exact filling without a fixed cofinal threshold).**

Lean statement: `D5/S3/Arith/GoldenResource/FibonacciFactorialBlockTailFilling.factorial_block_tail_filling`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/FibonacciFactorialBlockTailFilling.factorial_block_tail_filling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Such a block family exists, and every such family fills each nonnegative rational q by a finite legal state supported strictly after any prescribed cutoff. Choose a sufficiently late block whose factorial is divisible by the denominator of q and whose index is at least q. Filling exactly q times j! coordinates to capacity gives reading q with weights exactly 1/G_n. The zero target uses empty support. Each active coordinate has normalized capacity 1/j!, and outside the blocks the capacity is zero. These normalized capacities tend to zero, so no positive threshold can meet every cutoff even for modulus one. Existence follows by recursively choosing finitely many factorial-divisible Fibonacci indices beyond the preceding block.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/FibonacciFactorialBlockTailFilling.factorial_block_tail_filling`
- Dependency: [D5/S3/Arith/GoldenResource/RationalCapacityTailRealization](RationalCapacityTailRealization.md)
