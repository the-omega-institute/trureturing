# HSPowerProduct

## Abstract

HSPowerProduct

**Theorem 1.1 (Full HS perspective identity).**

$$\forall u: \operatorname{Level}(),\ \forall H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], \forall s: \mathbb{R},\ \forall A, B: \operatorname{L}(H),\ \operatorname{pdSet}(A)\land \operatorname{pdSet}(B)\implies\ \operatorname{operatorPowerMean}(s, 1, \operatorname{leftMulHS}(A), \operatorname{rightMulHS}(B))=\operatorname{leftMulHS}(\operatorname{rpow}(A, s))\operatorname{rightMulHS}(\operatorname{rpow}(B, (1-s)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/HSPowerProduct.perspective_lr_eq` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

On a finite nontrivial complex Hilbert space and for every real s, the perspective of leftMulHS A and rightMulHS B equals leftMulHS(A^s) rightMulHS(B^(1-s)). The public arbitrary-K scalar bridge is applied with K=V adjoint for every HS vector V. Selfadjointness and complex polarization convert equality of real quadratic forms to operator equality. This supplies the product powers used by the common-right-factor mean.

These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension. The native four-slot audit remains unfinished under issue #5214; no declared_validated registration is claimed.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/HSPowerProduct.perspective_lr_eq`
- Dependency: [D5/S3/Quantum/Hiai/GeometricMeanOrder](GeometricMeanOrder.md)
