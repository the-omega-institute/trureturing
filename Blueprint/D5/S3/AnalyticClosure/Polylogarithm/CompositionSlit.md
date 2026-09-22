# CompositionSlit

## Abstract

Every positive-composition source series has its normalized holomorphic branch on the full slit domain.

**Theorem 1.1 (All positive compositions on the full slit domain).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionSlit.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/CompositionSlit.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Acknowledgement.* Will (Ziang) Li (2026). *Primitives of Holomorphic Functions on Star-Shaped Domains*. URL: <https://github.com/will1491/RiemannDynamics/blob/b3fa37cc0f18a23ea66b654ea3f73eb472129010/RiemannDynamics/Hyperbolic/PlaneGeometry/StarShapedPrimitive.lean>.

*Commentary.*

The recursively defined continued family is holomorphic on omega={z:1-z belongs to Complex.slitPlane}, which excludes the real ray [1,infinity). The empty word equals one. Every nonempty positive composition vanishes at zero, agrees with the actual strict nested source series on |z|<1, has exact zero order equal to its depth, and commutes with conjugation.

For leading one, the derivative is the continued tail divided by 1-z. For leading exponent greater than one it is the predecessor branch divided by z off zero; at zero the derivative is one for an empty tail and zero otherwise. The proof establishes openness and star convexity of omega, constructs removable integrands using Mathlib's dslope theorem, and applies the attributed primitive on the live nested induction path. The frozen source recurrences and normalization identify the disk germ; analytic identity extends both recurrences and conjugation on the connected domain.

This intermediate source bridge receives zero solved-problem credit. It does not assert global slit nonvanishing, admissible boundary summability, MZV limits, bank estimates, a zero-free collar or coefficient-sign transfer. Xu-Zhao Conjecture 1.3 remains open. The classical primitive is a local attributed supplier, with no standalone generic theorem claim.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionSlit.result`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation](CompositionContinuation.md)
