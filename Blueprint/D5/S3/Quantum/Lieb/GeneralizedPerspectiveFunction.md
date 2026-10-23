# GeneralizedPerspectiveFunction

## Abstract

Attributed reusable operator API: GeneralizedPerspectiveFunction.

Consumed Apache-2.0 Physlib source at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and Hayata Yamasaki. Retire each supplier when an equivalent consumed declaration is available in the repository-pinned Mathlib.

**Theorem 1.1 (Joint concavity of the generalized perspective).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], f, h: \mathbb{R} \to \mathbb{R},\ \operatorname{OperatorConcaveOnAll}(u, \operatorname{Ici}(0), f) \land \operatorname{ContinuousOn}(f, \operatorname{Ici}(0)) \land 0 \le \operatorname{f}(0) \land \operatorname{OperatorConcaveOn}(H, \operatorname{Ioi}(0), h) \land \operatorname{ContinuousOn}(h, \operatorname{Ioi}(0)) \land (\forall x: \mathbb{R}, x \in \operatorname{Ioi}(0) \implies 0 < \operatorname{h}(x)) \implies \operatorname{JointlyConcaveOn}(\operatorname{psdSet}(H), \operatorname{pdSet}(H), \operatorname{GeneralizedPerspective}(H, f, h)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/GeneralizedPerspectiveFunction.theorem_2_6_forward_jointlyConcaveOn_psd_pd_Ici` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The carrier is a nontrivial complete complex Hilbert space. The function f is operator concave on [0,infinity) uniformly over all such Hilbert spaces in the same universe, continuous there, and satisfies f(0) at least zero. The function h is operator concave on (0,infinity) on the fixed carrier, continuous there, and strictly positive at every positive real argument.

The first argument A is self-adjoint with nonnegative spectrum (PSD); the second B is self-adjoint with strictly positive spectrum (PD). The generalized perspective is h(B)^(1/2) f(h(B)^(-1/2) A h(B)^(-1/2)) h(B)^(1/2), using real CFC. It is jointly concave under the same mixture coefficient in both arguments, with no A/B commutation and no finite-dimensionality requirement.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/GeneralizedPerspectiveFunction.theorem_2_6_forward_jointlyConcaveOn_psd_pd_Ici`
- Dependency: [D5/S3/Quantum/Lieb/JensenOperatorInequality](JensenOperatorInequality.md)
- Dependency: [D5/S3/Quantum/Lieb/LownerHeinzTheorem](LownerHeinzTheorem.md)
