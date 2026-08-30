# Golden Realization Certificate

## Abstract

One certificate packages the quadratic, Fibonacci, rotation-trace, Mobius-fixed, and projective-attraction realizations of the golden structure while exhibiting a repelling countermodel.

**Theorem 1.1 (Canonical Golden Cross Representation Certificate).**

$$(GoldenCrossRepresentationCertificate).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.canonical_golden_cross_representation_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical golden structure satisfies the full cross-representation certificate.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Golden Repelling Affine Fixed).**

$$(Function.IsFixedPt goldenRepellingAffine Real.goldenRatio).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.golden_repelling_affine_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same golden point can be fixed in a different dynamical system.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Golden Repelling Affine Has Deriv At).**

$$(HasDerivAt goldenRepellingAffine (Real.goldenRatio ^2) Real.goldenRatio).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.golden_repelling_affine_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine countermodel has derivative φ² at the fixed point.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Golden Repelling Affine Multiplier Gt One).**

$$(1 < |Real.goldenRatio ^2|).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.golden_repelling_affine_multiplier_gt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The affine countermodel is strictly repelling.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Golden Fixed Does Not Force Attraction).**

$$(Function.IsFixedPt goldenRepellingAffine Real.goldenRatio \land 1 < |Real.goldenRatio ^2|).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.golden_fixed_does_not_force_attraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hence fixedness of the golden point alone does not imply attraction.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.canonical_golden_cross_representation_certificate`
- Truth anchor: `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.golden_fixed_does_not_force_attraction`
- Truth anchor: `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.golden_repelling_affine_fixed`
- Truth anchor: `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.golden_repelling_affine_hasDerivAt`
- Truth anchor: `D5/S3/Observer/WorldModel/GoldenRealizationCertificate.golden_repelling_affine_multiplier_gt_one`
- Dependency: [D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge](../GoldenCoding/GoldenAngleTraceBridge.md)
- Dependency: [D5/S3/Observer/WorldModel/FixedPointStabilityProfile](FixedPointStabilityProfile.md)
