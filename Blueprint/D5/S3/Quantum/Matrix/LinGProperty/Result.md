# The geometric-mean comparison for trace augmentation

## Abstract

Trace augmentation gives the geometric-mean comparison in every dimension.

**Theorem 1.1 (Every parameter at least one).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/Result.parameter_family`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/Result.parameter_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every natural dimension n, every positive semidefinite complex block matrix with blocks A, X, X-adjoint and B, every real c at least one and every decreasing index j, the singular value s_j(X+c trace(X) I) is bounded by the corresponding eigenvalue of the geometric mean of A+c trace(A) I and B+c trace(B) I.

The zero diagonal block case forces X to vanish. Otherwise both diagonal traces are positive. A block diagonal congruence normalizes them to one, the trace-overlap arithmetic and difference-square bounds give the normalized comparison, and the separate homogeneity of the geometric mean restores the original traces. The same actual block matrix supplies all estimates.

**Theorem 1.2 (The trace-augmentation conjecture).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/lin-2016-trace-augmentation-g-property` (proved) by `D5/S3/Quantum/Matrix/LinGProperty/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lin-2016-trace-augmentation-g-property","declaration_gid":"D5/S3/Quantum/Matrix/LinGProperty/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

The proposition conjecture quantifies over every n, all three complex n by n blocks A, X and B, positivity of their full block matrix and every j in Fin n. It states s_j(Phi(X)) at most lambda_j(Phi(A) geometric-mean Phi(B)), with Phi(T)=T+trace(T) I. Both spectral lists decrease. The geometric mean has its positive definite inverse-square-root formula on nonzero diagonal inputs and is zero when either diagonal input is zero. No commutation, invertibility or rank condition is imposed on the original blocks.

Apply the parameter family at c=1. The intermediate trace-overlap bounds retain the common Gram realization of the two diagonal blocks and the cross block, while the harmonic comparison respects noncommutative multiplication order.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/Result.parameter_family`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/Result.result`
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound](ArithmeticBound.md)
- Dependency: [D5/S3/Quantum/Matrix/LinGProperty/SpectralConclusion](SpectralConclusion.md)
