# The actual canonical spectral test

## Abstract

The actual spectral reverse test attains the quadratic minimum and has an exact hockey profile.

**Theorem 1.1 (Attainment and all thresholds for one test).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.quadratic_reverse_test_attained_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.quadratic_reverse_test_attained_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every finite pair of positive semidefinite complex matrices, one actual test with card(n) labels attains quadraticValue. For S=A+B and C=normalize(S,A), its hockey profile equals Tr A - Re Tr(S canonicalOverlap(C,t)) for every real t. Both assertions come from the spectral preparation itself. There is no inference from cost equality alone, and there are no faithfulness, nonzero or nonempty-carrier hypotheses.

**Theorem 1.2 (The attained quadratic cost projection).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.quadratic_reverse_test_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.quadratic_reverse_test_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every finite PSD A,B, an actual ReverseTest with card(n) labels attains quadraticValue A B. This is the cost projection of the same all-threshold spectral test. Hiai canonical spectral and quadratic optimality are known antecedents; this finite source statement retains singular, zero and empty cases.

**Theorem 1.3 (The genuine finite quadratic infimum).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.maximal_quadratic_eq_value`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.maximal_quadratic_eq_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every finite PSD A,B, maximalQuadratic A B equals the EReal embedding of quadraticValue A B. The universal lower bound and the actual attained spectral test sandwich the defining all-k infimum. QuadraticEquality uses the exact finite value. This realizes known quadratic optimality and asserts no general-convex attainment theorem.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.maximal_quadratic_eq_value`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.quadratic_reverse_test_attained`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical.quadratic_reverse_test_attained_profile`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickComponents](MaximalHockeyStickComponents.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair](MaximalHockeyStickOriginalPair.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound](MaximalHockeyStickQuadraticBound.md)
