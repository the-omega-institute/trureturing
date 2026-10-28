# Containment of Binary Carryless Multiplier Conditions

## Abstract

The seventeen-times binary carryless condition implies the nine-times condition.

Every variable ranges over the natural numbers, including zero. C(u,k) is the natural number whose binary coefficients are the convolution of the binary digits of u and k over GF(2), as in A048720. All multiplication outside C is ordinary natural-number multiplication.

**Theorem 1.1 (The containment implication).**

$$\forall k \in Nat,\; 17 \cdot k = C\left(49, k\right) \Rightarrow 9 \cdot k = C\left(25, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/CarrylessSeventeenNineContainment.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Antti Karttunen (2006). *OEIS A115809: seventeen-times binary carryless multiplier condition*. URL: <https://oeis.org/A115809>.

*Commentary.*

A state records the ordinary multiplication carry and the remaining exclusive-OR mask; a failed low-digit comparison gives a rejecting state. A relation with 101 paired states contains the initial pair and is closed under both binary input digits. At input zero, acceptance by the first state implies acceptance by the second. Binary induction transports this implication to every natural input. Thus the same k satisfying the condition defining A115809 also satisfies the condition defining A115801. No upper bound on k is imposed.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/CarrylessSeventeenNineContainment.result`
- Dependency: [D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence](CarrylessMultiplierEquivalence.md)
