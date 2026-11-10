# Measurable Maximal Coupling Kernels

## Abstract

Two probability kernels on a standard Borel state space have one measurable coupling family attaining their event total variation at every parameter.

**Definition 1.1 (The common part and the residual product).**

Lean statement: `D5/S3/Estimation/DataProcessing/MeasurableMaximalCoupling.maximalCoupling`

*Formalization.* `D5/S3/Estimation/DataProcessing/MeasurableMaximalCoupling.maximalCoupling` (`✓ std3`).

*Citation.* Alessandro Abate; Frank Redig; Ilya Tkachev (2013). *On the effect of perturbation of conditional probabilities in total variation*. DOI: [10.1016/j.spl.2014.01.009](https://doi.org/10.1016/j.spl.2014.01.009). URL: <https://arxiv.org/abs/1311.3066v1>.

*Commentary.*

Let Z be any measurable space, let X be a standard Borel measurable space, and let P and Q be Markov probability kernels from Z to X. At parameter z use the reference measure P(z)+Q(z). Mathlib's kernel Radon--Nikodym derivatives give jointly measurable densities f and g relative to this varying reference. Their minimum defines a common-part kernel M. Subtracting M from P and Q gives two nonnegative residual kernels U and V with the same total mass r(z).

When r(z)=0, maximalCoupling(P,Q)(z) is the diagonal image of P(z). Otherwise it is the diagonal image of M(z) plus the product U(z) times V(z), scaled by the inverse of r(z). The zero-mass set and the scalar weight are measurable, so this formula defines one kernel from Z to X times X.

**Theorem 1.2 (Exact marginals and pointwise optimal mismatch).**

Lean statement: `D5/S3/Estimation/DataProcessing/MeasurableMaximalCoupling.maximal_coupling`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/MeasurableMaximalCoupling.maximal_coupling` (`✓ std3`). ∎

*Citation.* Alessandro Abate; Frank Redig; Ilya Tkachev (2013). *On the effect of perturbation of conditional probabilities in total variation*. DOI: [10.1016/j.spl.2014.01.009](https://doi.org/10.1016/j.spl.2014.01.009). URL: <https://arxiv.org/abs/1311.3066v1>.

*Commentary.*

For every measurable parameter space Z, every standard Borel state space X and all Markov kernels P,Q from Z to X, the constructed kernel C=maximalCoupling(P,Q) is Markov. Its first marginal kernel C.map(fst) equals P and its second marginal kernel C.map(snd) equals Q. For every z, C(z) assigns the off-diagonal {(x,y) : x differs from y} exactly measurableTotalVariation(P(z),Q(z)).

Here measurableTotalVariation is the supremum over measurable events E of max(P(z)(E)-Q(z)(E),Q(z)(E)-P(z)(E)), with truncated nonnegative subtraction. It lies between zero and one for these probability laws. It is half the full variation norm of their signed difference.

The statement holds for all parameters, including equal and mutually singular rows. It imposes no finite-support or fixed-reference assumption. Empty parameter spaces are allowed. The standard Borel hypothesis is required only on X, so the result also applies when both Z and X are standard Borel.

Exact row identities identify the measurable construction with the individual-law overlap coupling. Its marginal and agreement identities then give the probability and marginal conclusions. For any coupling, each measurable event discrepancy is at most its mismatch mass. Combining this lower bound with the common-part agreement bound gives the stated equality.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/MeasurableMaximalCoupling.maximalCoupling`
- Truth anchor: `D5/S3/Estimation/DataProcessing/MeasurableMaximalCoupling.maximal_coupling`
- Dependency: [D5/S3/Estimation/DataProcessing/DeclaredSourceInverseLimitMinimum](DeclaredSourceInverseLimitMinimum.md)
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction](MeasurablePostprocessingDefectContraction.md)
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables](../../ObserverMemory/Algorithms/KBonacciAcquisition/OriginalScheduledWitnessTables.md)
