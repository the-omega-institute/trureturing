# ActualRangeTensor

## Abstract

These declarations construct coordinate and smoothness helpers for actual complex tensor range bundles from Mathlib tensor coordinates and the existing range prebundle. The cited reversible-channel literature supplies application context; the abstract bundle construction is the repository proof.

**Theorem 1.1 (smooth range lift).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_range_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_range_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

A map into the actual range prebundle is smooth when its base map and ambient fiber value are smooth. The result uses the existing local Gram coordinates and the topology selected by the range prebundle.

**Theorem 1.2 (coefficients tmul).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_tmul`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_tmul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

The fixed canonical complex tensor coordinate equivalence evaluates a pure tensor u tensor w at i as w(i) times u. This algebraic identity is consumed by the tensor chart and coefficient calculations.

**Theorem 1.3 (coefficients map).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_map`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Canonical tensor coefficients commute with a complex linear map on the first factor. The proof checks zero, pure tensors and addition, preserving the complete tensor product.

**Theorem 1.4 (coefficients expand).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_expand`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Every tensor is the finite sum of its first-factor coefficients tensored with the standard complex Euclidean basis. This exact expansion is used to prove smoothness of the actual tensor equivalence.

**Theorem 1.5 (coordinates intoRange).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coordinates_intoRange`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coordinates_intoRange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

The coordinate map after the inverse chart map is the identity over the original column-chart base set. It follows on the full tensor product from the original range coordinate inverse law.

**Theorem 1.6 (intoRange coordinates).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.intoRange_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.intoRange_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

The inverse chart map after coordinates is the identity in each actual tensor fiber over the chart base set. No global frame or trivialization is assumed.

**Theorem 1.7 (symm eq).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.symm_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.symm_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

The inverse of the tensor pretrivialization over its base set is exactly the stated base point together with the tensor inverse coordinate map. This supplies the formula used in smooth overlap calculations.

**Theorem 1.8 (transition apply).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.transition_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.transition_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

The overlap map of the actual tensor charts is the original range transition tensored with the identity on the Euclidean factor. The result identifies the full chart maps, retaining the canonical tensor norm and inner product.

**Theorem 1.9 (smooth coefficient).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

Every ambient canonical tensor coefficient is a smooth function on the actual tensor total space. The proof uses the selected range charts and their smooth transition matrices.

**Theorem 1.10 (smooth tensor sum).**

Lean statement: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_tensor_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_tensor_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

A finite family of ambient-smooth sections over a smooth base map gives a smooth total-space map into the actual tensor bundle by summing u_i tensor e_i. The source manifold is arbitrary, and zero rank and empty bases are included.

## References

- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_expand`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_map`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_tmul`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coordinates_intoRange`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.intoRange_coordinates`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_coefficient`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_range_lift`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_tensor_sum`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.symm_eq`
- Truth anchor: `D5/S3/Geometry/ProjectionRange/ActualRangeTensor.transition_apply`
- Dependency: [D5/S3/Geometry/ProjectionRange/Prebundle](Prebundle.md)
