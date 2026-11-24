# Anchor convexity for faithful qubit–qutrit product states

## Abstract

Anchor convexity for faithful qubit–qutrit product states.

Qian arXiv:2608.14806v2, Lemma 7.1, equation (39), and Definition 7.2 specify the faithful-product quadratic form. Section 11(1) asks separately for its nonnegativity in dimensions two and three and for the full complementary quantum correlations inequality. Proposition 7.6 covers the case where either marginal is diagonal in either of its measured bases. The earlier sharp two-ray discrimination bound S ≤ 8/3 appears in the separate candidate release DOI 10.5281/zenodo.23933731 and has an orthogonal two-ray state restriction. The full qubit–qutrit complementary-correlation inequality remains open.

**Theorem 1.1 (Nonnegativity of the anchor quadratic).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/QubitQutritAnchorConvexity.qubit_qutrit_anchor_convexity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/QubitQutritAnchorConvexity.qubit_qutrit_anchor_convexity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lilong Qian (2026). *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*. URL: <https://arxiv.org/abs/2608.14806v2>.

*Commentary.*

For every faithful product state and Hermitian tangent with both partial traces zero, the BKM quadratic form dominates the sum of the two measured Fisher forms. Each subsystem may use any pair of rank-one mutually unbiased bases. Normalizing the two local pairs preserves faithfulness, the tangent conditions, and the quadratic itself. In the standard bases, the exact diagonal–circulant covariance estimate controls the Simpson upper bound on the dual BKM form.

## References

- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/QubitQutritAnchorConvexity.qubit_qutrit_anchor_convexity`
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalForm](AnchorMUBNormalForm.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementCovariance](AnchorMeasurementCovariance.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter](Certificate/CovarianceMatrixAdapter.md)
