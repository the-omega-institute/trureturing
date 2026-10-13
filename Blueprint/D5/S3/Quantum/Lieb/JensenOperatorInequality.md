# JensenOperatorInequality

## Abstract

Attributed reusable operator API: JensenOperatorInequality.

Consumed Apache-2.0 Physlib source at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and Hayata Yamasaki. Retire each supplier when an equivalent consumed declaration is available in the repository-pinned Mathlib.

**Theorem 1.1 (Localized Jensen for two operator terms).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], f: \mathbb{R} \to \mathbb{R},\ \operatorname{CondIciAll}(u, f) \implies \operatorname{CondV}(H, f).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/JensenOperatorInequality.theorem_2_5_2_i_ici_all_imp_v` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The carrier is a nontrivial complete complex Hilbert space. CondIciAll includes uniform operator convexity of f on [0,infinity) over all nontrivial complete complex Hilbert spaces in the same universe, continuity there, and f(0) at most zero.

For self-adjoint A,B with nonnegative real spectra and arbitrary X,Y satisfying X* X + Y* Y at most I, CondV gives f(X* A X + Y* B Y) at most X* f(A) X + Y* f(B) Y. The normalization is an inequality, so a nonzero defect is allowed. No A/B commutation is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/JensenOperatorInequality.theorem_2_5_2_i_ici_all_imp_v`
- Dependency: [D5/S3/Quantum/Lieb/JensenOperatorInequalityIImpIV](JensenOperatorInequalityIImpIV.md)
