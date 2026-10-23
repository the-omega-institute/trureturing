# MatrixTracePerspective

## Abstract

Joint trace perspective convexity for noncommuting finite matrices.

**Theorem 1.1 (Matrix trace perspective with both adjoints).**

$$\forall u: \operatorname{Level}(), d: \operatorname{Type}(u), [\operatorname{Fintype}(d)], [\operatorname{DecidableEq}(d)],\ a: \mathbb{R}, Z: \operatorname{Matrix}(d, d, \mathbb{C}),\ 1\le a\le 2\implies\ \operatorname{JointlyConvexOn}(\operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \operatorname{PosDefCone}(\operatorname{Matrix}(d, d, \mathbb{C})), \Lambda X, W\mapsto\operatorname{ReTr}(\operatorname{adjoint}(Z)\operatorname{rpow}(X, a)Z\operatorname{rpow}(W, 1-a)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/MatrixTracePerspective.trace_perspective_jointly_convex` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

For every finite complex square dimension, 1 <= a <= 2 and arbitrary complex Z, Re Tr(Z* X to exponent a Z W to exponent 1-a) is jointly convex on positive definite X and W. Z need not be selfadjoint or invertible. Empty dimension is split before the Hilbert Nontrivial instances.

The star algebra equivalence Matrix.toEuclideanCLM transports positivity, CFC spectral powers, products, both adjoints, trace and affine mixtures. Apply the consumed trace perspective theorem with K=star Z, then cyclically move the adjoint in the trace. The proof reuses the original phiK spectral bridge and does not change its multiplication order.

This is a consumed interface for the Carlen-Lieb convexity proof, not new mathematics independent of that proof. Native audit exception #5214 applies to the missing lawful matrix-telescope template, full source reconstruction and variation/sensitivity evidence; no declared_validated status is claimed. Classical source attribution is Apache-2.0.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/MatrixTracePerspective.trace_perspective_jointly_convex`
- Dependency: [D5/S3/Quantum/Lieb/TracePerspectiveConvexity](TracePerspectiveConvexity.md)
