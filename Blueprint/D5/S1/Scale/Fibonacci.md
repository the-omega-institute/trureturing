# Fibonacci Coordinates of Golden Powers

## Abstract

Golden powers have Fibonacci coordinates and yield an exact inverse-power partition.

**Theorem 1.1 (Golden powers have Fibonacci coordinates).**

$$\forall n \in \mathbb{N},\ \varphi^{n+1}=\langleF_{n},F_{n+1}\rangle$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Fibonacci.golden_phi_pow_eq_fib_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural index n, the integral and golden coordinates of phi to the power n + 1 are F_n and F_(n+1), respectively.

**Theorem 1.2 (Fibonacci-weighted inverse golden powers partition one).**

$$\forall n \in \mathbb{N},\ F_{n+1}\varphi^{-n}+F_{n}\varphi^{-(n+1)}=1$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Fibonacci.fibonacci_golden_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural index n, F_(n+1) times phi to the power -n plus F_n times phi to the power -(n+1) equals one exactly. The proof embeds the preceding integral coordinate identity into the reals and clears the nonzero golden power.

## References

- Truth anchor: `D5/S1/Scale/Fibonacci.fibonacci_golden_partition`
- Truth anchor: `D5/S1/Scale/Fibonacci.golden_phi_pow_eq_fib_pair`
- Dependency: [D5/S0/Carrier/Units](../../S0/Carrier/Units.md)
- Dependency: [D5/S1/Scale/Embedding](Embedding.md)
