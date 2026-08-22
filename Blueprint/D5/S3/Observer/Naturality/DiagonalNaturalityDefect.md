# Diagonal Naturality Defect

## Abstract

The worst diagonal naturality defect is exactly the semiconjugacy defect.

**Theorem 1.1 (Diagonal naturality defect equals semiconjugacy defect).**

$$(\forall E: A \times A \to Y, \forall a \in A,\ d_{Z}(Q_{\pi}(\Delta_{\tau}(E))(a), \Delta_{\sigma}(P_{\pi}(E))(a)) \leq \delta(\pi; \tau, \sigma)) \land\ \operatorname{sup}_{E} \operatorname{sup}_{a \in A} d_{Z}(Q_{\pi}(\Delta_{\tau}(E))(a), \Delta_{\sigma}(P_{\pi}(E))(a)) = \delta(\pi; \tau, \sigma).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Naturality/DiagonalNaturalityDefect.diagonal_naturality_defect_eq_semiconjugacy_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a nonempty address type, Y a finite state type, and Z an observed space. Let tau and sigma update Y and Z, and let pi project Y to Z. Apply pi pointwise to tables and output vectors, and read a table diagonally before applying its update.

For every table E and address a, the observed distance between projecting after the Y-update and applying the Z-update after projection is bounded by the uniform semiconjugacy defect. The supremum over all tables and addresses is exactly that defect.

The upper bound applies the imported semiconjugacy-defect definition pointwise. For the reverse bound, each state y is placed in a constant table and evaluated at an address supplied by nonemptiness. Loogle supplied the exact le_iSup and iSup_le declarations used for both supremum directions. LeanSearch returned HTTP 404 for the full query, and pinned-library and repository searches found no complete theorem with this statement.

## References

- Truth anchor: `D5/S3/Observer/Naturality/DiagonalNaturalityDefect.diagonal_naturality_defect_eq_semiconjugacy_defect`
- Dependency: [D5/S3/Observer/MetricGeometry/SemiconjugacyComposition](../MetricGeometry/SemiconjugacyComposition.md)
