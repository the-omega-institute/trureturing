# Quark flavor mixing and the Jarlskog invariant

## Abstract

Flavor parameter counts, Cabibbo rephasing, and the three-generation Jarlskog invariant.

Independent quark phases act on the rows and columns of a unitary flavor mixing matrix. For two generations the action brings every matrix to a real rotation. For three generations an imaginary quartet detects the phase contribution of the standard mixing matrix.

**Definition 1.1 (Unitary parameter count).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.unitaryParamCount`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.unitaryParamCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The count for N generations is the square of N.

**Definition 1.2 (Orthogonal angle count).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.orthogonalAngleCount`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.orthogonalAngleCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The angle count is half the product of N and N minus one.

**Definition 1.3 (Relative phase count).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.relativePhaseCount`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.relativePhaseCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The two sets of quark phases share a common phase, giving twice N minus one relative phases.

**Definition 1.4 (Physical phase count).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.physicalPhaseCount`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.physicalPhaseCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The count is half the product of N minus one and N minus two, with subtraction in the natural numbers.

**Theorem 1.5 (Physical parameter count).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckm_physical_parameter_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckm_physical_parameter_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

For at least one generation, the unitary count minus the relative phase count equals the square of N minus one.

**Theorem 1.6 (Parameter count decomposition).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckm_parameter_decomp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckm_parameter_decomp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

For at least one generation, the sum of the angle and physical phase counts equals the unitary count minus the relative phase count. Both expressions reduce to the square of N minus one.

**Theorem 1.7 (Minimum generations for a physical phase).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.cp_phase_pos_iff_three_generations`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.cp_phase_pos_iff_three_generations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The physical phase count is positive exactly when there are at least three generations.

**Theorem 1.8 (Counts for one to three generations).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckm_small_generation_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckm_small_generation_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The angle and phase counts are zero and zero for one generation, one and zero for two, and three and one for three.

**Definition 1.9 (Independent row and column rephasing).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rephase`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rephase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

Multiply each entry by the phase of its row and the conjugate phase of its column.

**Definition 1.10 (Imaginary quartet).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskogQuartet`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskogQuartet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

Take one entry from each corner of a plaquette and conjugate the entries at the opposite cross corners. The quartet is the imaginary part of their product.

**Theorem 1.11 (Quartet invariance under rephasing).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskogQuartet_rephase_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskogQuartet_rephase_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

For any square complex matrix and any four indices, the phase of each row and column cancels with its conjugate in the quartet.

**Theorem 1.12 (Two-generation reduction to a real rotation).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.u2_rephasing_to_real_rotation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.u2_rephasing_to_real_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

Every two-by-two unitary matrix admits diagonal row and column phase matrices and a real rotation angle. The first row becomes nonnegative by removing the arguments of its entries, including zero entries. The determinant determines the remaining phase.

**Theorem 1.13 (Two-generation quartets vanish).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.u2_jarlskog_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.u2_jarlskog_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

For every two-by-two unitary matrix and all indices, the imaginary quartet is zero because the rephased real rotation has real plaquette products.

**Definition 1.14 (Rotation in the second and third directions).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rot23`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rot23` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The real rotation acts on the second and third directions and fixes the first.

**Definition 1.15 (Complex rotation in the first and third directions).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rot13`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rot13` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The rotation fixes the second direction. The off-diagonal sine entries carry opposite phases, with the negative phase in the first row.

**Definition 1.16 (Rotation in the first and second directions).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rot12`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rot12` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The real rotation acts on the first and second directions and fixes the third.

**Definition 1.17 (Standard three-generation mixing matrix).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckmStandard`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckmStandard` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

Multiply the second-third rotation, the complex first-third rotation, and the first-second rotation in that order.

**Theorem 1.18 (Special unitarity of the standard matrix).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckmStandard_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckmStandard_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

For every choice of the three angles and phase, the conjugate transpose times the matrix is the identity and the determinant equals one.

**Definition 1.19 (Cyclic orientation sign).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.leviSign`

*Formalization.* `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.leviSign` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

An equal-index pair has sign zero. A positively oriented consecutive pair in the cyclic order of three indices has sign one and its reversal has sign minus one.

**Theorem 1.20 (Universal signed quartet identity).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskogQuartet_unitary_universal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskogQuartet_unitary_universal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

Every quartet of a three-by-three unitary matrix equals its first two rows and columns quartet times the row-pair and column-pair orientation signs. The complex orthogonality sums close both sets of triangles, and the imaginary product is alternating.

**Theorem 1.21 (Standard quartet formula).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_ckmStandard_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_ckmStandard_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

For the first two rows and columns, the quartet equals the product of the sines of the three angles and the phase, the cosines of the first-second and second-third angles, and the squared cosine of the first-third angle. The sign is positive with the stated plaquette convention.

**Theorem 1.22 (Exact zero criterion).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_zero_iff_no_cp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_zero_iff_no_cp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The standard quartet vanishes exactly when the sine of either doubled real rotation angle, the sine or cosine of the first-third angle, or the sine of the phase vanishes.

**Theorem 1.23 (Sharp bound on the standard quartet).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_sharp_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_sharp_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The magnitude is at most one over six times the square root of three. Each real rotation contributes at most one half. For the first-third rotation, putting x equal to squared sine factors the gap from four over twenty-seven as the square of x minus one third times four thirds minus x.

**Theorem 1.24 (Angles attaining the bound).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_bound_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_bound_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

The first-second and second-third angles equal pi over four, the first-third angle equals the arcsine of one over the square root of three, and the phase equals pi over two. The quartet attains the positive bound.

**Theorem 1.25 (Column unitarity triangle area).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.unitarity_triangle_area_eq_half_jarlskog`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.unitarity_triangle_area_eq_half_jarlskog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

For any distinct column pair of a three-by-three unitary matrix, the three side products sum to zero. The oriented area from the first two products is minus half their quartet. Its absolute value is half the magnitude of the reference quartet.

**Theorem 1.26 (Row unitarity triangle area).**

Lean statement: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.row_unitarity_triangle_area_eq_half_jarlskog`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.row_unitarity_triangle_area_eq_half_jarlskog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Ceccucci, Z. Ligeti and Y. Sakai (2024). *CKM Quark-Mixing Matrix*. URL: <https://pdg.lbl.gov/2024/reviews/rpp2024-rev-ckm-matrix.pdf>.

*Commentary.*

For any distinct row pair of a three-by-three unitary matrix, the three side products sum to zero. The oriented area from the first two products is minus half their quartet. Its absolute value is half the magnitude of the reference quartet.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckmStandard`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckmStandard_unitary`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckm_parameter_decomp`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckm_physical_parameter_square`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.ckm_small_generation_counts`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.cp_phase_pos_iff_three_generations`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskogQuartet`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskogQuartet_rephase_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskogQuartet_unitary_universal`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_bound_attained`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_ckmStandard_formula`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_sharp_upper_bound`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.jarlskog_zero_iff_no_cp`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.leviSign`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.orthogonalAngleCount`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.physicalPhaseCount`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.relativePhaseCount`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rephase`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rot12`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rot13`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.rot23`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.row_unitarity_triangle_area_eq_half_jarlskog`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.u2_jarlskog_zero`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.u2_rephasing_to_real_rotation`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.unitarity_triangle_area_eq_half_jarlskog`
- Truth anchor: `D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D.unitaryParamCount`
