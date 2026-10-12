# HilbertSchmidtOperatorSpace

## Abstract

Attributed reusable operator API: HilbertSchmidtOperatorSpace.

Consumed Apache-2.0 Physlib source at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and Hayata Yamasaki. Retire each supplier when an equivalent consumed declaration is available in the repository-pinned Mathlib.

**Theorem 1.1 (Left and right Hilbert-Schmidt multiplication commute).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], A, B: \operatorname{L}(H),\ \operatorname{Commute}(\operatorname{leftMulHS}(H, A), \operatorname{rightMulHS}(H, B)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace.leftMulHS_rightMulHS_commute` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The carrier is a finite-dimensional complex inner-product space. HSOp equips its bounded operators with Hilbert-Schmidt coordinates. Left multiplication sends T to A T, and right multiplication sends T to T B.

These operators commute for arbitrary A,B by associativity. No A/B commutation, positivity, self-adjointness or nontriviality is assumed. This declaration omits completeness of the underlying carrier.

**Theorem 1.2 (Real CFC commutes with left multiplication).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], [\operatorname{ContinuousFunctionalCalculus}(\mathbb{R}, \operatorname{L}(H), \operatorname{IsSelfAdjoint})], [\operatorname{Nontrivial}(\operatorname{L}(H))],\ f: \mathbb{R} \to \mathbb{R}, A: \operatorname{L}(H),\ \operatorname{IsSelfAdjoint}(A) \land \operatorname{ContinuousOn}(f, \operatorname{spectrum}(\mathbb{R}, A)) \implies \operatorname{leftMulHS}(H, \operatorname{cfcR}(H, f, A)) = \operatorname{cfcR}(\operatorname{HSOp}(H), f, \operatorname{leftMulHS}(H, A)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace.leftMulHS_cfcR` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The carrier is a complete finite-dimensional complex Hilbert space. The exact statement also requires real CFC and nontriviality for its bounded-operator algebra. A is self-adjoint, and f is continuous on its real spectrum; no global continuity or positivity of A is required.

Left multiplication by f(A) equals real CFC of the Hilbert-Schmidt left-multiplication operator of A. The left-multiplication star algebra homomorphism and finite-dimensional continuity supply the bridge.

**Theorem 1.3 (Real CFC commutes with right multiplication).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{FiniteDimensional}(\mathbb{C}, H)], [\operatorname{ContinuousFunctionalCalculus}(\mathbb{R}, \operatorname{L}(H), \operatorname{IsSelfAdjoint})], [\operatorname{ContinuousFunctionalCalculus}(\mathbb{R}, \operatorname{MulOpposite}(\operatorname{L}(H)), \operatorname{IsSelfAdjoint})], [\operatorname{Nontrivial}(\operatorname{L}(H))],\ f: \mathbb{R} \to \mathbb{R}, A: \operatorname{L}(H),\ \operatorname{IsSelfAdjoint}(A) \land \operatorname{ContinuousOn}(f, \operatorname{spectrum}(\mathbb{R}, A)) \implies \operatorname{rightMulHS}(H, \operatorname{cfcR}(H, f, A)) = \operatorname{cfcR}(\operatorname{HSOp}(H), f, \operatorname{rightMulHS}(H, A)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace.rightMulHS_cfcR` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The carrier is a complete finite-dimensional complex Hilbert space. The exact statement requires real CFC for both its bounded-operator algebra and the opposite algebra, and nontriviality of the bounded-operator algebra. A is self-adjoint and f is continuous on its real spectrum.

Right multiplication by f(A) equals real CFC of the Hilbert-Schmidt right-multiplication operator of A. The opposite-algebra star homomorphism handles reversed multiplication; original A and B need not commute.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace.leftMulHS_cfcR`
- Truth anchor: `D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace.leftMulHS_rightMulHS_commute`
- Truth anchor: `D5/S3/Quantum/Lieb/HilbertSchmidtOperatorSpace.rightMulHS_cfcR`
- Dependency: [D5/S3/Quantum/Lieb/GeneralizedPerspectiveFunction](GeneralizedPerspectiveFunction.md)
- Dependency: [D5/S3/Quantum/Lieb/LownerHeinzTheorem](LownerHeinzTheorem.md)
