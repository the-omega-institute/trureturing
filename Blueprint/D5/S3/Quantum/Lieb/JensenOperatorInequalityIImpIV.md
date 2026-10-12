# JensenOperatorInequalityIImpIV

## Abstract

Attributed reusable operator API: JensenOperatorInequalityIImpIV.

Consumed Apache-2.0 Physlib source at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, credited to Kei Tsukamoto, Kento Mori and Hayata Yamasaki. Retire each supplier when an equivalent consumed declaration is available in the repository-pinned Mathlib.

**Theorem 1.1 (Localized Jensen under one contraction).**

$$\forall u: \operatorname{Level},\ H: \operatorname{Type}(u),\ [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(\mathbb{C}, H)], [\operatorname{CompleteSpace}(H)], [\operatorname{Nontrivial}(H)], f: \mathbb{R} \to \mathbb{R},\ \operatorname{CondIciAll}(u, f) \implies \operatorname{CondIV}(H, f).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/JensenOperatorInequalityIImpIV.theorem_2_5_2_i_ici_all_imp_iv` (`✓ std3`). ∎

*Citation.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

The fixed carrier is a nontrivial complete complex Hilbert space. CondIciAll requires operator convexity of f on [0,infinity) uniformly over every nontrivial complete complex Hilbert space in the same universe, continuity there, and f(0) at most zero. Fixed-space convexity alone is not the hypothesis.

For self-adjoint A with nonnegative real spectrum and arbitrary X with norm at most one, CondIV gives f(X* A X) at most X* f(A) X, using real CFC. The proof applies the uniform hypothesis on the direct sum of the carrier with itself.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/JensenOperatorInequalityIImpIV.theorem_2_5_2_i_ici_all_imp_iv`
- Dependency: [D5/S3/Quantum/Lieb/BlockDiagonal](BlockDiagonal.md)
- Dependency: [D5/S3/Quantum/Lieb/LownerHeinzTheorem](LownerHeinzTheorem.md)
