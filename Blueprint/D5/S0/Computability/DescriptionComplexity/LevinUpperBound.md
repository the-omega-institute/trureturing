# Levin Upper Bound

## Abstract

A finite scaled-Kraft mass with a complexity ceiling bounds the candidate count.

**Theorem 1.1 (A scaled Kraft ceiling bounds the candidate count).**

$$|C_{Q}(R)| \le 2^{Q - K(y|x) + c}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/LevinUpperBound.levin_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source's prefix-machine argument selects one shortest witness for each candidate, assigns every witness a budget-scaled power-of-two weight, and then applies the conditional coding ceiling. This declaration exposes those two numerical premises directly.

The lower-weight premise says every candidate contributes at least 2^K after scaling; the total-weight premise says the entire finite family is at most 2^(Q + overhead). Natural-number factorization then gives the displayed cardinality bound. Universal-machine and conditional-complexity semantics are kept as upstream data rather than re-proved here.

Mathlib's Kraft inequality and finite-program results were checked first, but no matching universal-machine model is present. The Lean proof therefore reuses only finite sums, power factorization, and Nat cancellation.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/LevinUpperBound.levin_upper_bound`
