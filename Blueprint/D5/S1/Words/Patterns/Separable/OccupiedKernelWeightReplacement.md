# Summed weight replacement on the positive lattice

## Abstract

Actual Schröder jump weights admit a uniform summable replacement by their leading power.

**Definition 1.1 (Paired second difference of the shifted power).**

$$\operatorname{secondDiff}\left(\beta, n, m\right)=(2+\left\lvert n+m\right\rvert)^{-\beta}+(2+\left\lvert n-m\right\rvert)^{-\beta}-2(2+\left\lvert n\right\rvert)^{-\beta}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.secondDiff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two jump directions use the same even power profile centered at n.

**Definition 1.2 (Actual positive jump coefficient minus its leading power).**

$$\operatorname{weightError}\left(A, m\right)=\operatorname{kernelWeight}\left(m-1\right)-\frac{A}{m\cdot \sqrt{m}}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.actualWeightError` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The variable m is natural. The theorem only uses positive jump sizes m=i+1, where the zero-based kernel index is exactly i.

**Theorem 1.3 (Exact homogeneity of the regularized Mellin sample).**

$$\operatorname{sample}\left(\beta, \frac{2}{n}, \frac{m}{n}\right)=n^{\beta+\frac{3}{2}}\cdot m^{-\frac{3}{2}}\cdot \operatorname{secondDiff}\left(\beta, n, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.sample_eq_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real beta and both positive real lattice scales n and m, the actual shifted sample is exactly the scaled power profile difference, including the absolute value across m=n. This identity is used when replacing weights and again when converting the later generator sum to the Mellin mesh.

**Theorem 1.4 (Uniform absolute replacement bound).**

$$\exists A>0, \exists E\ge0, \forall \beta,n, \frac{1}{2}\le \beta\le\frac{3}{4} \land 0<n \longrightarrow ( \operatorname{Summable}\left(i\mapsto \left\lvert \operatorname{weightError}\left(A, i+1\right)\cdot \operatorname{secondDiff}\left(\beta, n, i+1\right)\right\rvert\right) \land \sum_{i=0}^{\infty} \left\lvert \operatorname{weightError}\left(A, i+1\right)\cdot \operatorname{secondDiff}\left(\beta, n, i+1\right)\right\rvert \le 298E n^{-\beta-\frac{3}{2}})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.actual_global_weight_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the displayed bound, beta ranges over [1/2,3/4] and n over positive natural mesh sizes. The same A and E work for all of them. The error constant absorbs the actual singleton separately from the m>=2 coefficient theorem.

For m<=n/2, the origin majorant and exact lattice homogeneity give the second-difference estimate; monotone comparison controls the inverse square-root sum. On the remaining positive lattice, 1/m<=2/n and the full absolute sample sum follows from the discrete origin, center, transition and far bands. This bounds the sum of absolute errors, not merely the signed sum.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.actualWeightError`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.actual_global_weight_replacement`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.sample_eq_lattice`
- Truth anchor: `D5/S1/Words/Patterns/Separable/OccupiedKernelWeightReplacement.secondDiff`
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedKernelCoefficient](OccupiedKernelCoefficient.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteCenter](OccupiedMellinDiscreteCenter.md)
- Dependency: [D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteTails](OccupiedMellinDiscreteTails.md)
