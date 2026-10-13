# GenericLieLength

## Abstract

Generic Lie-length in the traceless skew-Hermitian matrix Lie algebra grows logarithmically for every fixed generator count at least two.

**Theorem 1.1 (ae_mvPolynomial_ne_zero).**

$$\forall (n : \mathbb{N}) (p : \operatorname{MvPolynomial} (\operatorname{Fin} n) \mathbb{R}) , p \neq 0 \to \forall^{m} (x : \operatorname{Fin} n \to \mathbb{R}) , \operatorname{MvPolynomial} . \operatorname{eval} x p \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLength.ae_mvPolynomial_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero real multivariate polynomial vanishes only on a Lebesgue null set. AnalyticOnNhd.eval_mvPolynomial gives analyticity, MvPolynomial.funext supplies a nonzero value, and AnalyticZeroSetNull.ae_ne_zero_of_analytic gives nonvanishing almost everywhere.

**Theorem 1.2 (ae_span_top_of_witness).**

$$\forall (M : \operatorname{Type} *) [ \operatorname{LieRing} M ] [ \operatorname{LieAlgebra} \mathbb{R} M ] [ \operatorname{FiniteDimensional} \mathbb{R} M ] (g d L : \mathbb{N}) (b : \operatorname{Module} . \operatorname{Basis} (\operatorname{Fin} d) \mathbb{R} M) (S0 : \operatorname{Fin} g \to M) , \operatorname{rightSpan} (K := \mathbb{R}) S0 L = \operatorname{Top}.\operatorname{top} \to \forall^{m} (x : \operatorname{Fin} g \to \operatorname{Fin} d \to \mathbb{R}) , \operatorname{rightSpan} (K := \mathbb{R}) (\operatorname{fun} (i : \operatorname{Fin} g) \mapsto b . \operatorname{equivFun} . \operatorname{symm} (x i)) L = \operatorname{Top}.\operatorname{top}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLength.ae_span_top_of_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One spanning tuple supplies coefficients for a determinant polynomial which evaluates to one. Its nonzero evaluations give full span for almost all tuples of real basis coordinates.

**Definition 1.3 (claim).**

$$\operatorname{claim} \iff (\forall (g : \mathbb{N}) , 2 \leq g \to \exists (c C : \mathbb{R}) , 0 < c \land 0 < C \land \forall (n : \mathbb{N}) , 2 \leq n \to \operatorname{Filter} . \operatorname{Eventually} (\operatorname{fun} (S : \operatorname{Fin} g \to \operatorname{Fin} n \to \operatorname{Fin} n \to \mathbb{C}) \mapsto (c * \operatorname{Real} . \operatorname{log} (n : \mathbb{R}) \leq (\operatorname{lieLength} n (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} S) : \mathbb{R}) \land (\operatorname{lieLength} n (\operatorname{Finset} . \operatorname{univ} . \operatorname{image} S) : \mathbb{R}) \leq C * \operatorname{Real} . \operatorname{log} (n : \mathbb{R}))) (\operatorname{MeasureTheory} . \operatorname{ae} (\operatorname{suPairMeasure} g n)))$$

*Formalization.* `D5/S3/Quantum/Algebra/GenericLieLength.claim` (`✓ std3`).

*Citation.* Yifan Jia; Angela Capel (2024). *A generic quantum Wielandt's inequality*. DOI: [10.22331/q-2024-05-02-1331](https://doi.org/10.22331/q-2024-05-02-1331). URL: <https://arxiv.org/abs/2301.08241>.

*Commentary.*

Conjecture 6 (arXiv:2301.08241v3, p. 19): “Let S be a random Lie-generating set of su(n), then Lieℓ(S) = Θ(log n) almost surely.” The number g of generators is fixed, with g ≥ 2, and the positive real constants depend on g but not on n ≥ 2. Lie-length counts generator letters in right-nested brackets and cumulative layers. Filter.Eventually under suPairMeasure gives the source almost-sure qualifier.

**Theorem 1.4 (result).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericLieLength.result` (`✓ std3`). ∎

*Resolves.* `Problems/jia-capel-2023-generic-lie-length` (proved) by `D5/S3/Quantum/Algebra/GenericLieLength.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jia-capel-2023-generic-lie-length","declaration_gid":"D5/S3/Quantum/Algebra/GenericLieLength.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yifan Jia; Angela Capel (2024). *A generic quantum Wielandt's inequality*. DOI: [10.22331/q-2024-05-02-1331](https://doi.org/10.22331/q-2024-05-02-1331). URL: <https://arxiv.org/abs/2301.08241>.

*Acknowledgement.* Seth Lloyd; Reevu Maity (2019). *Efficient implementation of unitary transformations*. DOI: [10.48550/arXiv.1901.03431](https://doi.org/10.48550/arXiv.1901.03431). URL: <https://arxiv.org/abs/1901.03431>.

*Commentary.*

For each fixed g ≥ 2 the constants c = 1/log(g + 1) and C = 32/log 2 work. The anchored heap produces a spanning pair in 16(1 + Nat.log 2 (n − 1)) letters; the determinant argument gives the same bound almost everywhere. The word-count dimension bound gives the lower estimate. The optimal upper constant and Lloyd–Maity Conjecture III remain open.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLength.ae_mvPolynomial_ne_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLength.ae_span_top_of_witness`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLength.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericLieLength.result`
- Dependency: [D5/S3/Analytic/NullSets/AnalyticZeroSetNull](../../Analytic/NullSets/AnalyticZeroSetNull.md)
- Dependency: [D5/S3/Quantum/Algebra/GenericLieLengthConstruction](GenericLieLengthConstruction.md)
