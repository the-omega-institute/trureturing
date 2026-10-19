# Perfect Matching Count

## Abstract

Count fixed-point-free involutions using the pinned Mathlib cycle-type formula.

The proof specializes Equiv.Perm.card_of_cycleType_mul_eq to h cycles of length two. It supplies the cross-edge factor for the proposed MatchingMonomialFiber equivalence.

**Theorem 1.1 (Pairing involutions and their cycle type).**

$$\forall (A: \operatorname{Type}*) [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)], (\forall (h: \mathbb{N}), ((\operatorname{Fintype.card}\left(A\right) = 2 \cdot h) \Rightarrow (\forall (p: \operatorname{Equiv.Perm}\left(A\right)), (((\operatorname{Function.Involutive}\left(p\right)) \land (\forall (x: A), (p\left(x\right) \ne x))) \Leftrightarrow (\operatorname{Equiv.Perm.cycleType}\left(p\right) = \operatorname{Multiset.replicate}\left(h, 2\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/PerfectMatchingCount.involution_iff_cycleType` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite type of cardinality 2h, a permutation is an involution without fixed points exactly when its cycle type consists of h copies of two. The type and its decidable equality are arbitrary.

**Theorem 1.2 (Exact Product Count).**

Lean statement: `D5/S3/Zeros/Convolution/PerfectMatchingCount.card_fixedPointFreeInvolution_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/PerfectMatchingCount.card_fixedPointFreeInvolution_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite type of cardinality 2h, its number of fixed-point-free involutions times h! times 2^h equals (2h)!.

**Theorem 1.3 (Factorial Quotient Count).**

Lean statement: `D5/S3/Zeros/Convolution/PerfectMatchingCount.card_fixedPointFreeInvolution`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/PerfectMatchingCount.card_fixedPointFreeInvolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of the denominator turns the product equality into the exact natural-number factorial quotient, including h = 0.

## References

- Truth anchor: `D5/S3/Zeros/Convolution/PerfectMatchingCount.card_fixedPointFreeInvolution`
- Truth anchor: `D5/S3/Zeros/Convolution/PerfectMatchingCount.card_fixedPointFreeInvolution_mul`
- Truth anchor: `D5/S3/Zeros/Convolution/PerfectMatchingCount.involution_iff_cycleType`
