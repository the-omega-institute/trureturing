# Golden Fibonacci Partition

## Abstract

Consecutive Fibonacci weights on inverse golden powers partition one exactly.

**Theorem 1.1 (Fibonacci-weighted inverse golden powers partition one).**

$$\forall n \in \mathbb{N},\ F_{n+1}\varphi^{-n}+F_{n}\varphi^{-(n+1)}=1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GoldenPartition.fibonacci_golden_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural index n, F_(n+1) times phi to the power -n plus F_n times phi to the power -(n+1) equals one exactly. The proof embeds the GoldenInt Fibonacci-coordinate identity into the reals and clears a nonzero golden power.

## References

- Truth anchor: `D5/S1/Recurrence/GoldenPartition.fibonacci_golden_partition`
- Dependency: [D5/S1/Scale/Embedding](../Scale/Embedding.md)
