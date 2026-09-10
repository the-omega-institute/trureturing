# GeometricLiNegativeType

## Abstract

The original Li geometric energy as an exact integrated Gram distance on every integer sample.

**Definition 1.1 (Integer continuation on the whole circle).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric`

*Formalization.* `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original finite geometric polynomial is continued to negative indices with its removable identity value n.

**Theorem 1.2 (The zero index has zero value).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cocycle origin agrees on and off the identity.

**Theorem 1.3 (Retain the original polynomial).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_nat`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Natural indices agree exactly with the existing geometricPolynomial definition.

**Theorem 1.4 (One integer cocycle).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_add`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same formula obeys b(m+n)=b(m)+z^m b(n), including negative indices and the identity.

**Theorem 1.5 (Negative indices retain the energy).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_neg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative branch is a unit-modulus factor times the negative positive branch.

**Theorem 1.6 (Continuity through the removable point).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural polynomial and negative-index identity prove continuity everywhere.

**Theorem 1.7 (The original absolute-index energy).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both integer branches have exactly the old geometric energy at the absolute index.

**Theorem 1.8 (Exact cocycle distance).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A difference of two cocycle values has the original geometric energy at their integer difference.

**Definition 1.9 (Construct the original integrated Gram matrix).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram`

*Formalization.* `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix integrates real inner products of the same integer geometric functions under the original finite measure.

**Theorem 1.10 (A concrete squared-integral identity).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real Gram quadratic form is the original nonnegative-scale integral of the squared coefficient sum.

**Theorem 1.11 (The constructed Gram matrix is positive).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity follows from the explicit integral, without a supplied embedding or positivity field.

**Theorem 1.12 (Gram distance equals the original Li value).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix distance is exactly reconstructedLi at the absolute integer difference.

**Theorem 1.13 (Exact negative-type identity).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.reconstructed_li_zero_sum_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.reconstructed_li_zero_sum_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every zero-sum real vector the Li form is minus twice the same scaled squared integral.

**Theorem 1.14 (Conditional negative type on all integer samples).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.reconstructed_li_conditionally_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.reconstructed_li_conditionally_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full arbitrary finite integer sample is allowed, with repeated indices, empty samples and the identity atom.

**Theorem 1.15 (Derive the actual exponential positivity).**

Lean statement: `D5/S3/Weil/Probability/GeometricLiNegativeType.reconstructed_li_exponential_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/GeometricLiNegativeType.reconstructed_li_exponential_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Gram Schoenberg theorem proves complex-coefficient positivity for all nonnegative times without an exponential-positivity premise.

## References

- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram_distance`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram_posSemidef`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.geometricLiGram_quadratic`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_add`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_continuous`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_distance`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_energy`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_nat`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_neg`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.integerGeometric_zero`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.reconstructed_li_conditionally_negative`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.reconstructed_li_exponential_posSemidef`
- Truth anchor: `D5/S3/Weil/Probability/GeometricLiNegativeType.reconstructed_li_zero_sum_identity`
- Dependency: [D5/S3/Weil/Probability/FiniteGaussianSchoenberg](FiniteGaussianSchoenberg.md)
- Dependency: [D5/S3/Weil/Probability/LiCurvatureProbabilityCompletion](LiCurvatureProbabilityCompletion.md)
