# A115805 to A115803 carryless containment

## Abstract

The carryless-multiplier equation for 13 and 29 implies the equation for 11 and 31.

Every variable ranges over the natural numbers, including zero. Ordinary multiplication and binary carryless multiplication are different operations. The carryless product C uses binary digits as polynomial coefficients over GF(2).

**Theorem 1.1 (Containment of the solution sets).**

$$\forall k \in Nat,\; 13 \cdot k = C\left(29, k\right) \Rightarrow 11 \cdot k = C\left(31, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a115803-carryless-thirteen-eleven-containment` (proved) by `D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a115803-carryless-thirteen-eleven-containment","declaration_gid":"D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation (2026). *OEIS A115803 and A115805: carryless multiplier containment*. URL: <https://oeis.org/A115803>.

*Commentary.*

A finite relation of 50 state pairs has the required terminal implication and is closed under both input digits. The original binary-product recursion and its holds_step theorem turn this finite certificate into an induction over every natural number. The certificate is a proof component; its bounded enumeration is not used as a substitute for the all-natural-number induction.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/CarrylessThirteenElevenContainment.result`
- Dependency: [D5/S1/Digit/Admissibility/CarrylessMultiplierEquivalence](CarrylessMultiplierEquivalence.md)
