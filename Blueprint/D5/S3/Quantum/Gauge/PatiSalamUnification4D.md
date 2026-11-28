# Pati–Salam unification in four dimensions

## Abstract

The fourth color, the half-spin generation, and the orthogonal vector action.

The fourth color is the lepton. Its different color charge separates the off-diagonal blocks of the adjoint and fixes the hypercharge of each member of the left-handed generation. The vector action combines the real exterior square and the quaternion representation.

**Definition 1.1 (Baryon number minus lepton number).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.bMinusLGen`

*Formalization.* `D5/S3/Quantum/Gauge/PatiSalamUnification4D.bMinusLGen` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The first three diagonal entries are one third. The fourth is minus one.

**Theorem 1.2 (Fourth-color generator normalization).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_bMinusL_traceless_and_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_bMinusL_traceless_and_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The trace vanishes, the trace of the square is four thirds, and multiplying by the square root of three eighths brings the quadratic trace to one half.

**Theorem 1.3 (Color and baryon minus lepton commute).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_sm_subalgebra_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_sm_subalgebra_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The generator is scalar on the three color coordinates, so its commutator with the color block vanishes.

**Theorem 1.4 (Compact color and abelian Lie embedding).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_sm_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_sm_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

A traceless skew-Hermitian color block and an imaginary multiple of the baryon-minus-lepton generator define an injective real Lie algebra map into the traceless skew-Hermitian four by four matrices.

**Theorem 1.5 (Adjoint block decomposition).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_adjoint_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_adjoint_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

Each traceless four by four complex matrix has unique coordinates in a color octet, a singlet, a column and a row. The complex dimensions are eight, one, three and three.

**Theorem 1.6 (Charges of the adjoint blocks).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_adjoint_leptoquark_bMinusL`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_adjoint_leptoquark_bMinusL` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The commutator with the diagonal generator has eigenvalue zero on the two diagonal blocks, four thirds on the upper-right column, and minus four thirds on the lower-left row.

**Theorem 1.7 (Irreducibility of the summands).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_adjoint_blocks_irreducible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_adjoint_blocks_irreducible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The traceless color block carries its adjoint action. The column and row carry the fundamental and dual actions. The remaining summand is one-dimensional.

**Theorem 1.8 (Left-handed Weyl state counts).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_left_right_dims`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_left_right_dims` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The color fundamental with left weak weight contributes eight states. The color antifundamental with right weak weight contributes a further eight.

**Theorem 1.9 (Linear and cubic charge traces).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_anomalies_vanish`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_anomalies_vanish` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The left and right weak weights sum to zero. The baryon-minus-lepton, hypercharge, electric charge, and specified mixed and cubic traces also vanish.

**Theorem 1.10 (Quadratic traces and coupling matching).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_traces_and_gut_matching`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_traces_and_gut_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The squared left and right weak weights each sum to two. The square of half the baryon-minus-lepton weight sums to four thirds. Hypercharge and electric charge have quadratic traces ten thirds and sixteen thirds. At equal positive Pati–Salam couplings, the normalized couplings agree and the weak mixing fraction is three eighths.

**Theorem 1.11 (Even half-spin weight correspondence).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_matches_so10_spinor16`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_matches_so10_spinor16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

An explicit permutation of the sixteen weight labels preserves both weak weights, baryon minus lepton, hypercharge, and electric charge.

**Theorem 1.12 (Embedding of the oriented blocks).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.so6SO4ToSO10_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.so6SO4ToSO10_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The two diagonal blocks are recovered by restricting both matrix indices to their respective summands.

**Theorem 1.13 (Ten-dimensional special orthogonal action).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamToSO10_special_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamToSO10_special_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

The exterior-square and quaternion blocks act on orthogonal summands. Each preserves the Euclidean form and orientation.

**Theorem 1.14 (Multiplicativity).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamToSO10_hom`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamToSO10_hom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

Componentwise multiplication in the three factors gives matrix multiplication in the direct-sum action.

**Theorem 1.15 (Central kernel).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamToSO10_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamToSO10_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

An element acts identically exactly when its color factor is one of the two scalar signs and its two weak factors have a common scalar sign.

**Theorem 1.16 (Faithful quotient action).**

Lean statement: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamQuotientToSO10_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamQuotientToSO10_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jogesh C. Pati and Abdus Salam (1974). *Lepton number as the fourth "color"*. DOI: [10.1103/PhysRevD.10.275](https://doi.org/10.1103/PhysRevD.10.275). URL: <https://doi.org/10.1103/PhysRevD.10.275>.

*Commentary.*

Quotienting the three factors by the four central elements in the kernel gives an injective map into the ten-dimensional special orthogonal group.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.bMinusLGen`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamQuotientToSO10_injective`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamToSO10_hom`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamToSO10_kernel`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.patiSalamToSO10_special_orthogonal`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_anomalies_vanish`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_left_right_dims`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_matches_so10_spinor16`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.ps16_traces_and_gut_matching`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.so6SO4ToSO10_injective`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_adjoint_blocks_irreducible`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_adjoint_decomposition`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_adjoint_leptoquark_bMinusL`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_bMinusL_traceless_and_norm`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_sm_embedding`
- Truth anchor: `D5/S3/Quantum/Gauge/PatiSalamUnification4D.su4_sm_subalgebra_commute`
- Dependency: [D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D](SU5SO10GrandUnification4D.md)
