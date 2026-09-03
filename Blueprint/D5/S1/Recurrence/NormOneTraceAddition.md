# Norm-One Trace Addition and Recurrence

## Abstract

Norm-one power sums satisfy an addition law and its two-step recurrence.

**Theorem 1.1 (Trace addition law).**

$$\begin{gathered}\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall a, b: R,\\{a \cdot b = 1} \implies\\\forall m, n: \mathbb{N},\\{a}^{m + 2 \cdot n} + {b}^{m + 2 \cdot n} = {{a}^{m + n} + {b}^{m + n}} \cdot {{a}^{n} + {b}^{n}} - {{a}^{m} + {b}^{m}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/NormOneTraceAddition.trace_add_two_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing T k for a ^ k + b ^ k, shifting the index by twice a step multiplies by the value at that step and subtracts the unshifted term. The law is stated with m + 2 * n rather than a difference of indices so that no truncated subtraction on Nat is needed.

The norm-one hypothesis is what makes the identity work: the cross terms of the product collect as (a ^ m + b ^ m) * (a ^ n * b ^ n), and the latter factor is one exactly because a * b = 1.

Two cases already exist in this repository: m = 0 is the frozen doubling identity in NormOneLucasDouble, and n = 1 at one concrete real transfer matrix is a private lemma in the Chebyshev transfer-matrix file; neither file is restated or amended.

**Theorem 1.2 (Two-step trace recurrence).**

$$\begin{gathered}\forall R: Type, [\operatorname{CommRing}\left(R\right)],\\\forall a, b: R,\\{a \cdot b = 1} \implies\\\forall m: \mathbb{N},\\{a}^{m + 2} + {b}^{m + 2} = {a + b} \cdot {{a}^{m + 1} + {b}^{m + 1}} - {{a}^{m} + {b}^{m}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/NormOneTraceAddition.trace_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the two-step recurrence obtained from the addition law in the case n = 1.

## References

- Truth anchor: `D5/S1/Recurrence/NormOneTraceAddition.trace_add_two_mul`
- Truth anchor: `D5/S1/Recurrence/NormOneTraceAddition.trace_recurrence`
- Dependency: [D5/S1/Recurrence/NormOneLucasDouble](NormOneLucasDouble.md)
