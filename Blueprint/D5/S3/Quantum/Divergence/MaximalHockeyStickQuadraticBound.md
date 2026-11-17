# A lower bound for every actual finite quadratic reverse test

## Abstract

A lower bound for every actual finite quadratic reverse test

The lower bound proves known quadratic optimality in the exact singular finite preparation model used here. Canonical spectral and operator-convex optimality are credited to Hiai as antecedents; no arbitrary general-convex attainment is inferred.

**Definition 1.1 (quadraticValue).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.quadraticValue`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.quadraticValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For S=A+B and T=normalize S (A-B), quadraticValue A B is Re Tr(S T^2). The generalized inverse support keeps singular and zero pairs in scope.

**Theorem 1.2 (quadratic value le test).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.quadratic_value_le_test`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.quadratic_value_le_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For any PSD A,B and any actual finite ReverseTest, quadraticValue A B <= starCost R. The proof normalizes the actual state components, handles zero total label masses, and applies the subunital square inequality.

**Theorem 1.3 (quadratic value le maximal).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.quadratic_value_le_maximal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.quadratic_value_le_maximal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B, the EReal embedding of quadraticValue is a lower bound for the infimum over all actual finite quadratic tests. QuadraticCanonical combines it with a spectral witness to identify the true infimum.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.quadraticValue`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.quadratic_value_le_maximal`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticBound.quadratic_value_le_test`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest](MaximalHockeyStickReverseTest.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickSupport](MaximalHockeyStickSupport.md)
