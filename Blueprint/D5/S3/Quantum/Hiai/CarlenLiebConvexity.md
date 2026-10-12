# CarlenLiebConvexity

## Abstract

Carlen-Lieb fixed-congruence trace convexity by explicit optimizer interpolation.

**Theorem 1.1 (Full fixed-congruence convexity supplier).**

$$\forall u: \operatorname{Level}(), d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ a: \mathbb{R}, Z: \operatorname{Matrix}(d, d, \mathbb{C}),\ 1\le a\le 2\land \operatorname{IsUnit}(Z)\implies\ \operatorname{ConvexOn}(\mathbb{R}, \operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \Lambda X\mapsto\operatorname{tracePower}(\frac{1}{a}, \operatorname{adjoint}(Z)\operatorname{rpow}(X, a)Z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/CarlenLiebConvexity.fixed_congruence_trace_convex` (`✓ std3`). ∎

*Citation.* Eric A. Carlen and Elliott H. Lieb (2008). *A Minkowski Type Trace Inequality and Strong Subadditivity of Quantum Entropy II*. URL: <https://arxiv.org/abs/0710.4167v3>.

*Commentary.*

For 1 <= a <= 2 and every fixed invertible complex square Z, X maps to Re Tr((Z* X to exponent a Z) to exponent 1/a) is convex on the positive definite cone. X and Z need not commute, Z need not be selfadjoint, and every finite dimension including the empty one is covered. All powers use spectral continuous functional calculus.

For each endpoint X choose the attained Young optimizer W=(Z* X to exponent a Z) to exponent 1/a. Invertibility of Z ensures this congruence and W are positive definite. Their affine mixture remains positive definite. Bound the target at the mixture by the reverse Young objective there, then apply joint trace perspective convexity and the affine trace penalty. Endpoint equality gives the weighted endpoint values; cancellation of a > 0 finishes convexity. No convexity supplier is assumed as a theorem hypothesis.

The trace perspective consumes the new generic C-star power-convexity proof, its all-Hilbert CondIciAll, the public Jensen perspective and the existing phiK bridge. The Young bound and minimum consume general Schatten Holder at positive exponents, including those below one. Only helpers on these real proof paths are retained.

This is classical Carlen-Lieb Theorem 1.1 at q=1, not an original mathematical inequality. For Hiai take a=2p; the entire required 1/2 <= p < 1 range lies in this supplier's interval. The other curvature supplier, inverse geometric-mean identification, full parameter assembly and source support constraint at the semidefinite boundary remain required. Original problem count is unchanged. Native four-slot audit remains unfinished under #5214: no faithful enrolled template supplies the complete universe-polymorphic matrix telescope with original source reconstruction and variation/sensitivity evidence. No declared_validated status is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/CarlenLiebConvexity.fixed_congruence_trace_convex`
- Dependency: [D5/S3/Quantum/Hiai/ReverseTraceYoung](ReverseTraceYoung.md)
- Dependency: [D5/S3/Quantum/Lieb/MatrixTracePerspective](../Lieb/MatrixTracePerspective.md)
