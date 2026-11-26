# Derivative-free harmonic congruence

## Abstract

Orthogonality of modified Jordan ranges gives a quadratic and a harmonic bound for a positive matrix congruence.

**Definition 1.1 (Sector mass).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.harmonicB`

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.harmonicB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For square complex matrices X and Q, let X₊ and X₋ denote the positive and negative parts. The sector matrix B is Q X₊ Q + (I − Q) X₋ (I − Q).

**Definition 1.2 (Input gap).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.harmonicDelta`

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.harmonicDelta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write n(X) for the real trace of the positive part of −X. The input gap δ is n(X) plus the real trace of QX.

**Definition 1.3 (Congruence gap).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.harmonicValue`

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.harmonicValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For square matrices S, X and Q on the same finite index type, the congruence gap is n(SXS) plus the real trace of QSXS.

**Theorem 1.4 (The quadratic bound for every real parameter).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.derivative_free_harmonic_congruence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.derivative_free_harmonic_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Acknowledgement.* Ian George; Christoph Hirche; Theshani Nuradha; Mark M. Wilde (2026). *Quantum Doeblin Coefficients: Interpretations and Applications*. DOI: [10.22331/q-2026-05-22-2115](https://doi.org/10.22331/q-2026-05-22-2115). URL: <https://arxiv.org/html/2503.22823v3>.

*Commentary.*

On any finite decidable index type, take square complex matrices W, X and Q. Suppose W is positive definite, X is Hermitian, Q is Hermitian and idempotent, and W commutes with Q. Put S = W¹ᐟ² and c equal to the real trace of W⁻¹B. For every real t, the congruence gap is at least 2tδ − t²c. The bound includes singular X and zero input gap.

The independent algebraic derivation (6b07dfb8b836dbbd608458f9) uses M₊ = S(I − Q) + tS⁻¹Q, M₋ = SQ + tS⁻¹(I − Q), and D = S − tS⁻¹. The modified filters have product tI. The ranges of M₊√X₊ and M₋√X₋ are orthogonal, since the two Jordan square roots multiply to zero. Test the negative trace with the orthogonal projection onto the second range. Removing the vanishing modified-filter terms and contracting by the projection and its complement bounds the two trace losses by the real trace of D²B. Subtracting this from the real trace of WB gives the quadratic, using W − D² = 2tI − t²W⁻¹ and the identity between the real trace of B and δ.

Hirche, George, Nuradha and Wilde define the conditional expansion coefficient in arXiv:2608.27171v1, Definition 3, Eq. (2.42). Their Proposition 9 reduces the trace-distance optimization to orthogonal pairs. George, Hirche, Nuradha and Wilde (arXiv:2503.22823v3, Proposition 33) bound the complete expansion coefficient, where reference marginals agree. The effect test here uses the positive-part variational principle of Eq. (5.2), applied to the negative of the congruence. The modified-filter argument retains the reference-effect term. Probabilistic exact correction is treated by Kukulski, Pawela and Puchała, arXiv:2206.05232, Theorem 1 and Eq. (7), which characterize the successful composite by scalar Kraus operators. The present statement concerns the matrix congruence.

**Theorem 1.5 (The optimized harmonic bound).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.derivative_free_harmonic_congruence_optimized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.derivative_free_harmonic_congruence_optimized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same matrix hypotheses, assume δ > 0. The sector matrix B is positive semidefinite and has real trace δ, so it is nonzero. Since W⁻¹ is positive definite, its trace pairing c with B is strictly positive. Substituting the maximizing real parameter t = δ/c in the quadratic lower bound gives the congruence gap at least δ²/c.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.derivative_free_harmonic_congruence`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.derivative_free_harmonic_congruence_optimized`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.harmonicB`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.harmonicDelta`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence.harmonicValue`
- Dependency: [D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation](../CompleteHockeyStickRefutation.md)
