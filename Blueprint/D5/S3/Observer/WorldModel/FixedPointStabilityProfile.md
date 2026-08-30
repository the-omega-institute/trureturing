# Fixed Point Stability Profile

## Abstract

Uniform fixed-point stability is a separate multiplier profile whose canonical golden projective radius is positive, strictly below one, and sharper than the ambient stable ratio.

**Theorem 1.1 (Uniform Radius Bound Each Attracting).**

$$\forall Index: Type, multiplier: Index \to \mathbb{R}, radius: \mathbb{R}, i: Index,\\{}(UniformRadiusBound multiplier radius) \Rightarrow\\{}(|multiplier i| < 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.uniform_radius_bound_each_attracting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coordinate of a uniformly bounded profile is strictly attracting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Uniform Radius Bound Mono).**

$$\forall Index: Type, multiplier: Index \to \mathbb{R}, small: \mathbb{R}, large: \mathbb{R},\\{}(UniformRadiusBound multiplier small) \land (small \leq large) \land (large < 1) \Rightarrow\\{}(UniformRadiusBound multiplier large).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.uniform_radius_bound_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Enlarging a valid radius below one preserves validity.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Golden Projective Radius pos).**

$$(0 < goldenProjectiveRadius).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_projective_radius_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden projective radius is positive.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Abs Golden Multiplier eq Radius).**

$$(|goldenProjectiveMultiplier| = goldenProjectiveRadius).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.abs_golden_multiplier_eq_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute golden completion multiplier is exactly its positive radius.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Golden Projective Radius lt One).**

$$(goldenProjectiveRadius < 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_projective_radius_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical projective golden system is strictly attracting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Golden Projective Multiplier neg).**

$$(goldenProjectiveMultiplier < 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_projective_multiplier_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Its multiplier is negative, recording the alternating side of approach.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.7 (Golden Projective Radius lt Ambient Radius).**

$$(goldenProjectiveRadius < Real.goldenRatio^{-1}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_projective_radius_lt_ambient_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projective normalization contracts more strongly than the ambient stable ratio φ⁻¹.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.8 (Golden Constant Profile Uniform).**

$$\forall Index: Type,\\{}(UniformRadiusBound (\lambda value : Index \mapsto goldenProjectiveMultiplier) goldenProjectiveRadius).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_constant_profile_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A world-model family whose every local multiplier is the canonical golden projective multiplier has the exact uniform radius φ⁻².

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.9 (Golden Constant Profile Is Uniformly Attracting).**

$$\forall Index: Type,\\{}(IsUniformlyAttracting (\lambda value : Index \mapsto goldenProjectiveMultiplier)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_constant_profile_is_uniformly_attracting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical golden constant profile is uniformly attracting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.abs_golden_multiplier_eq_radius`
- Truth anchor: `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_constant_profile_is_uniformly_attracting`
- Truth anchor: `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_constant_profile_uniform`
- Truth anchor: `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_projective_multiplier_neg`
- Truth anchor: `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_projective_radius_lt_ambient_radius`
- Truth anchor: `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_projective_radius_lt_one`
- Truth anchor: `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.golden_projective_radius_pos`
- Truth anchor: `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.uniform_radius_bound_each_attracting`
- Truth anchor: `D5/S3/Observer/WorldModel/FixedPointStabilityProfile.uniform_radius_bound_mono`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative](../../CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.md)
