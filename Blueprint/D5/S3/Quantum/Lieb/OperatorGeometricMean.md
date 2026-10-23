# OperatorGeometricMean

## Abstract

Attributed reusable operator API: OperatorGeometricMean.

Consumed Apache-2.0 Physlib source at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and Hayata Yamasaki. Retire each supplier when an equivalent consumed declaration is available in the repository-pinned Mathlib.

**Theorem 1.1 (Joint concavity of the operator power mean).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], \alpha, \beta: \mathbb{R},\ \alpha \in \operatorname{Icc}(0, 1) \land \beta \in \operatorname{Icc}(0, 1) \implies \operatorname{JointlyConcaveOn}(\operatorname{pdSet}(H), \operatorname{pdSet}(H), \operatorname{operatorPowerMean}(H, \alpha, \beta)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/OperatorGeometricMean.operatorPowerMean_jointlyConcaveOn_pdSet` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The carrier is a nontrivial complete complex Hilbert space. Both exponents alpha,beta belong to [0,1], including endpoints. The operatorPowerMean is the generalized perspective with f(x)=x^alpha and h(x)=x^beta.

Both inputs are self-adjoint with strictly positive real spectra. The mean is jointly concave under a common mixture coefficient, with no A/B commutation and no finite-dimensionality requirement. This endpoint has PD inputs in both positions; PSD-first/PD-second belongs to the consumed generalized-perspective theorem.

**Theorem 1.2 (Joint convexity of the operator power mean).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], \alpha, \beta: \mathbb{R},\ \alpha \in \operatorname{Icc}(1, 2) \land \beta \in \operatorname{Icc}(0, 1) \implies \operatorname{JointlyConvexOn}(\operatorname{pdSet}(H), \operatorname{pdSet}(H), \operatorname{operatorPowerMean}(H, \alpha, \beta)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/OperatorGeometricMean.operatorPowerMean_jointlyConvexOn_pdSet` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The exact Physlib supplier at original line 89 has alpha in [1,2] and beta in [0,1], including all endpoints, on every complete nontrivial complex Hilbert space. Both inputs are strictly positive; no commutation or finite dimension is assumed. The source proof is retained, with its uniform power condition supplied by the consumed PowerConvexity adapter. LiebAndoTrace consumes this endpoint at beta=1. This is attributed reuse, not new mathematics.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/OperatorGeometricMean.operatorPowerMean_jointlyConcaveOn_pdSet`
- Truth anchor: `D5/S3/Quantum/Lieb/OperatorGeometricMean.operatorPowerMean_jointlyConvexOn_pdSet`
- Dependency: [D5/S3/Quantum/Lieb/GeneralizedPerspectiveFunction](GeneralizedPerspectiveFunction.md)
- Dependency: [D5/S3/Quantum/Lieb/PowerConvexity](PowerConvexity.md)
