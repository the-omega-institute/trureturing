# Equivalent Binary Carryless Multiplier Conditions

## Abstract

Two ordinary versus binary carryless multiplier equations define the same natural numbers.

Every variable ranges over the natural numbers, including zero. Ordinary multiplication and binary carryless multiplication are different operations. The carryless product C uses the binary digits as polynomial coefficients over GF(2). Bit(n,i) is the i-th binary digit, indexed from zero at the least significant bit, and has value zero or one.

**Definition 1.1 (Binary convolution).**

$$\forall u \in Nat,\; \forall k \in Nat,\; \forall t \in Nat,\; bit\left(C\left(u, k\right), t\right) = mod\left(\sum_{0 \le i \le t} bit\left(u, i\right) \cdot bit\left(k, t - i\right), 2\right)$$

*Formalization.* `D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.carryless` (`✓ std3`).

*Citation.* OEIS Foundation (2026). *OEIS A115801: ordinary and binary carryless multiplier conditions*. URL: <https://oeis.org/A115801>.

*Commentary.*

For each degree t, the sum runs through all pairs i and t-i of nonnegative indices. Taking its remainder modulo two gives the output digit. Finite binary support makes these digits the expansion of a unique natural number.

**Theorem 1.2 (The two conditions agree).**

$$\forall k \in Nat,\; 9 \cdot k = C\left(25, k\right) \Leftrightarrow 15 \cdot k = C\left(19, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a115801-carryless-multiplier-equivalence` (proved) by `D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a115801-carryless-multiplier-equivalence","declaration_gid":"D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation (2026). *OEIS A115801: ordinary and binary carryless multiplier conditions*. URL: <https://oeis.org/A115801>.

*Commentary.*

A binary digit step records the ordinary multiplication carry and the remaining exclusive-OR mask. A finite relation between the two pairs of states has matching terminal conditions and is closed under both input digits. Binary induction therefore establishes both implications for every natural number. There is no upper bound on the input; at zero both equalities read zero equals zero.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.carryless`
- Truth anchor: `D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence.result`
