# Ordinary external coefficients of affine Gaussians

## Abstract

NativeAffineExternalCoefficient

Finite ordinary coordinate differentiation identifies every full row occupation with its native affineCoefficient. The cutoff for the finite exponential polynomial bounds the whole occupation degree. Cauchy estimates justify every fixed finite external derivative of a normally bounded family on a positive external neighborhood. The parameterized normal estimate is uniform only over the specified family; it makes no claim of a source radius uniform across frequency cutoffs. All external index types and occupations may be empty. The calculus is classical, with no novelty or physical-realization claim.

**Definition 1.1 (Ordinary coordinate derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateDerivative`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The derivative varies exactly one coordinate through Function.update.

**Definition 1.2 (Finite ordered coordinate derivatives).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty derivative word evaluates the original function.

**Definition 1.3 (Occupation of a derivative word).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.jetOccupation`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.jetOccupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinate multiplicities record the complete finite derivative degree.

**Definition 1.4 (Ordinary multivariate coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordinary finite coordinate jet at zero is divided by the full product of coordinate factorials.

**Definition 1.5 (Two external row extractions).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPairCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPairCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left and right external occupations are extracted consecutively, with both complete factorial denominators.

**Theorem 1.6 (Finite exponential jet comparison).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.external_jet_expCut`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.external_jet_expCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vanishing of sufficiently high powers at zero proves the exact finite exponential polynomial comparison, with a genuine differentiated recurrence.

**Theorem 1.7 (Native affine row from an ordinary jet).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.native_affine_external_jet`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.native_affine_external_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full derivative occupation is used in the finite native Taylor comparison.

**Theorem 1.8 (Full ordinary affine coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.native_affine_external_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.native_affine_external_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every full external occupation, including zero, equals the native affine coefficient. No equality of replacement source arrays is assumed.

**Theorem 1.9 (Constant factors through finite jets).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_const_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_const_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constants remain literal through every finite ordinary derivative.

**Theorem 1.10 (Composition of finite jets).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_append`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Concatenation applies the two finite derivative words in their specified order.

**Theorem 1.11 (Full mixed row extraction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.native_mixed_external_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.native_mixed_external_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Internal native extraction followed by external ordinary extraction gives the native coefficient at the sum of the two full occupations.

**Theorem 1.12 (Local equality preserves finite jets).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_congrOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_congrOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality on an open neighborhood preserves all finite ordinary coordinate derivatives.

**Theorem 1.13 (Normal finite derivative interchange).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_tsum_normal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_tsum_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cauchy bounds and normally summable derivative families justify the finite derivative interchange on a smaller positive neighborhood.

**Theorem 1.14 (Ordinary coefficient interchange).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalCoefficient_tsum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalCoefficient_tsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normal interchange retains the complete external factorial denominator.

**Theorem 1.15 (Collected exponential extraction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_affine`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two external ordinary extractions give the full native affine coefficient of the actual symmetric collected kernel and mean.

**Theorem 1.16 (Parameterized normal external extraction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_normal_family`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_normal_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A summable bound uniform over an arbitrary parameter family survives both fixed external extractions. The proof uses actual derivatives and Cauchy estimates.

**Theorem 1.17 (External germ equality).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_congr_ball`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_congr_ball` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality throughout a positive external norm ball preserves the two fixed ordinary coefficient extractions.

**Theorem 1.18 (Full mixed occupation extraction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual left and right mixed affine factors give the two full native rows, multiplied by exactly one internal factorial.

**Theorem 1.19 (Entire external occupation summands).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.mixed_external_contDiff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.mixed_external_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual mixed occupation factor is entire in the external coordinates because its native affine coefficient has finite polynomial dependence on the means.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_append`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_congrOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_const_mul`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.coordinateJet_tsum_normal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalCoefficient_tsum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPairCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_affine`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_congr_ball`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_mixed`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.externalPair_normal_family`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.external_jet_expCut`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.jetOccupation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.mixed_external_contDiff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.native_affine_external_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.native_affine_external_jet`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient.native_mixed_external_coefficient`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/NativeAffineTransport](NativeAffineTransport.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients](OriginalGaussianOccupationCoefficients.md)
