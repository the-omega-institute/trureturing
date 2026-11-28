# Self-duality and the four-dimensional instanton

## Abstract

Euclidean Hodge duality, Yang-Mills action bounds, and exact BPST normalization.

Use three electric and three oriented magnetic coordinates for each color. The oriented pairs are 01, 02, 03, 23, 31, 12. The Euclidean pairing uses unit color weights. The BPST trace pairing multiplies this pairing by one half.

**Definition 1.1 (Hodge duality).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Exchange the electric and magnetic coordinates.

**Definition 1.2 (Euclidean pairing).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.inner4`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.inner4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Sum the products of matching electric and magnetic coordinates over all colors.

**Definition 1.3 (Squared length).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.normSq`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.normSq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Pair a two-form with itself.

**Definition 1.4 (Topological density).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.topDensity`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.topDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Pair the two-form with its Hodge dual.

**Definition 1.5 (Self-dual projection).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.selfDualPart`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.selfDualPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Take one half of the sum of the form and its dual.

**Definition 1.6 (Anti-self-dual projection).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.antiSelfDualPart`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.antiSelfDualPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Take one half of the difference of the form and its dual.

**Theorem 1.7 (Dimension selection).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4_coordinate_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4_coordinate_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

The complementary degree of a two-form is two exactly when the coordinate index is equivalent to four coordinates.

**Theorem 1.8 (Involution).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Applying the Hodge exchange twice gives the original form.

**Theorem 1.9 (Isometry).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Hodge exchange preserves the pairing of any two forms.

**Theorem 1.10 (Orthogonality).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.sd_asd_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.sd_asd_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

The inner product of the two projected parts is zero.

**Theorem 1.11 (Orthogonal splitting).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.sd_asd_orthogonal_split`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.sd_asd_orthogonal_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

The projected parts sum to the original form, have Hodge eigenvalues one and minus one respectively, and are orthogonal.

**Theorem 1.12 (Action density decomposition).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.norm_sq_eq_sd_add_asd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.norm_sq_eq_sd_add_asd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Squared length is the sum of the squared lengths of the two projected parts.

**Theorem 1.13 (Charge density decomposition).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.topological_density_eq_sd_sub_asd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.topological_density_eq_sd_sub_asd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Topological density is the squared length of the self-dual part minus that of the anti-self-dual part.

**Theorem 1.14 (Bogomolny identities).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_pointwise_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_pointwise_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Squared length equals half the squared length of the difference with the dual plus the topological density. It also equals half the squared length of the sum with the dual minus that density.

**Theorem 1.15 (Pointwise bound).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_pointwise_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_pointwise_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Absolute topological density is bounded by squared length.

**Theorem 1.16 (Pointwise equality).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_equality_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_equality_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Equality with positive signed density holds exactly for self-dual forms. Equality with negative signed density holds exactly for anti-self-dual forms.

**Theorem 1.17 (Integrated bound).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_action_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_action_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

For a measurable field of finite action on four-dimensional Euclidean space, absolute integrated charge density is bounded by the integrated squared length.

**Theorem 1.18 (Integrated equality).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_action_equality_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_action_equality_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

For a continuous field of finite action, equality with the signed charge integral holds exactly when the field is self-dual everywhere. A nonnegative continuous difference with zero integral is identically zero.

**Definition 1.19 (Antisymmetric tensor).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.toTwoForm`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.toTwoForm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Place the electric and oriented magnetic entries into their indicated coordinate pairs and fill the reversed pairs with the negative entries.

**Theorem 1.20 (Antisymmetry).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.toTwoForm_antisymmetric`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.toTwoForm_antisymmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Swapping the two tensor indices negates each component.

**Theorem 1.21 (Tensor pairing normalization).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.normSq_tensor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.normSq_tensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Squared length equals one half of the sum of squares over all colors and both tensor indices.

**Definition 1.22 (Stress tensor).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ymStress`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ymStress` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Contract the tensor over its second index and color, subtracting one quarter of the full norm sum times the Kronecker delta.

**Theorem 1.23 (Trace cancellation).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_stress_trace_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_stress_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

The sum of the four diagonal stress entries is zero.

**Theorem 1.24 (Self-dual stress cancellation).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.selfDual_ym_stress_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.selfDual_ym_stress_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Every stress entry vanishes for a self-dual form.

**Theorem 1.25 (Anti-self-dual stress cancellation).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.antiSelfDual_ym_stress_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.antiSelfDual_ym_stress_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Every stress entry vanishes for an anti-self-dual form.

**Definition 1.26 (Self-dual eta symbols).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.thooftEta`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.thooftEta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Both sets of three coordinates are the color Kronecker delta.

**Theorem 1.27 (Eta self-duality).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.thooftEta_selfDual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.thooftEta_selfDual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Hodge exchange fixes the eta symbols.

**Definition 1.28 (BPST profile).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpstField`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpstField` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Multiply eta by four times the squared scale divided by the square of the sum of squared radius and squared scale.

**Theorem 1.29 (BPST self-duality).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_selfDual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_selfDual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

The profile is self-dual at every point and scale.

**Theorem 1.30 (BPST stress).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_stress_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_stress_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

All stress entries of the profile vanish.

**Definition 1.31 (Trace action density).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.traceActionDensity`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.traceActionDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Use half the unit-pairing squared length.

**Definition 1.32 (Trace charge density).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.traceTopDensity`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.traceTopDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Use half the unit-pairing topological density.

**Theorem 1.33 (Exact radial density).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

The trace action density is 48 times the fourth power of the scale divided by the fourth power of the sum of squared radius and squared scale.

**Definition 1.34 (Action).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpstAction`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpstAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Integrate trace action density over all four Euclidean coordinates.

**Definition 1.35 (Normalized charge).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpstCharge`

*Formalization.* `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpstCharge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

Divide integrated trace charge density by eight pi squared.

**Theorem 1.36 (Finite action).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_finite_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_finite_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

The trace action density is integrable for every strictly positive scale.

**Theorem 1.37 (Exact action).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_exact_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_exact_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

For every strictly positive scale the action equals eight pi squared. The radial integral equals one twelfth and the round three-sphere contributes two pi squared.

**Theorem 1.38 (Unit charge).**

Lean statement: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_exact_charge_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_exact_charge_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. A. Belavin, A. M. Polyakov, A. S. Schwartz, and Yu. S. Tyupkin (1975). *Pseudoparticle solutions of the Yang-Mills equations*. DOI: [10.1016/0370-2693(75)90163-X](https://doi.org/10.1016/0370-2693(75)90163-X). URL: <https://doi.org/10.1016/0370-2693(75)90163-X>.

*Commentary.*

For every strictly positive scale the normalized charge equals one by self-duality and the exact action integral.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.antiSelfDualPart`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.antiSelfDual_ym_stress_zero`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpstAction`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpstCharge`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpstField`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_density`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_exact_action`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_exact_charge_one`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_finite_action`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_selfDual`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.bpst_instanton_stress_zero`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4_coordinate_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4_involutive`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.hodge4_isometry`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.inner4`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.normSq`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.normSq_tensor`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.norm_sq_eq_sd_add_asd`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.sd_asd_orthogonal`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.sd_asd_orthogonal_split`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.selfDualPart`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.selfDual_ym_stress_zero`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.thooftEta`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.thooftEta_selfDual`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.toTwoForm`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.toTwoForm_antisymmetric`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.topDensity`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.topological_density_eq_sd_sub_asd`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.traceActionDensity`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.traceTopDensity`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ymStress`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_action_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_action_equality_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_equality_iff`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_pointwise_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_bps_pointwise_identity`
- Truth anchor: `D5/S3/Quantum/Gauge/YangMillsBPSSelfDual4D.ym_stress_trace_zero`
- Dependency: [D5/S3/Geometry/Lorentz/DimensionSelection4D](../../Geometry/Lorentz/DimensionSelection4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D](../Analysis/NullConeGravity/NullDiamondSphere5D.md)
