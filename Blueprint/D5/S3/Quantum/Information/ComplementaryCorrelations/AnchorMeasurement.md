# The product-anchor quadratic

## Abstract

The product-anchor quadratic.

Definition 7.2 and equation (39) of Qian use a quadratic form at a faithful product state. The quantum term is the actual Kubo–Mori trace pairing of the tangent with the derivative of the logarithm.

**Definition 1.1 (Fixed-marginal directions).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.MarginalFree`

*Formalization.* `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.MarginalFree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lilong Qian (2026). *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*. URL: <https://arxiv.org/abs/2608.14806v2>.

*Commentary.*

The joint tangent is Hermitian and both partial traces vanish.

**Definition 1.2 (Fisher form of the measured distribution).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.measurementFisher`

*Formalization.* `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.measurementFisher` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lilong Qian (2026). *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*. URL: <https://arxiv.org/abs/2608.14806v2>.

*Commentary.*

The diagonal entries of the tangent and state in the product basis give the outcome derivatives and probabilities. The form sums the squares of the derivatives divided by those probabilities.

**Definition 1.3 (The term in equation (39)).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.anchorQuadraticIn`

*Formalization.* `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.anchorQuadraticIn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lilong Qian (2026). *Separable Counterexamples to Complementary Quantum Correlations, and Why Random Search Missed Them*. URL: <https://arxiv.org/abs/2608.14806v2>.

*Commentary.*

At the product state the trace pairing of the tangent with its log resolvent derivative is reduced by the two measured Fisher forms.

## References

- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.MarginalFree`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.anchorQuadraticIn`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement.measurementFisher`
- Dependency: [D5/S3/Divergence/LogDerivTrace](../../../Divergence/LogDerivTrace.md)
- Dependency: [D5/S3/Quantum/Dynamics/PolygonalFourierCouplings](../../Dynamics/PolygonalFourierCouplings.md)
- Dependency: [D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation](../../Entanglement/NandiMutualPredictabilityLOCCRefutation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTrace/Isometries](../PartialTrace/Isometries.md)
