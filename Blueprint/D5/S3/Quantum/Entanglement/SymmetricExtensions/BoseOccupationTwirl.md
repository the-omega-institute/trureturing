# Actual diagonal-unitary occupation twirl

## Abstract

Actual diagonal-unitary occupation twirl

The twirl is prior work of Gulati-Nechita-Park, Corollary 8.18, and Gulati-Nechita-Pellegrini, Lemma 5.8. The source application from star witnesses is by Haobo Ma and Wenlin Zhang. Matrices use the original computational tensor basis and unnormalized marginals. Averaging can change the witness.

**Definition 1.1 (tensorPhase).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.tensorPhase`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.tensorPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal entry of the repeated local tensor operator is the product of the local entries at every register.

**Definition 1.2 (diagonalAction).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is genuine matrix conjugation by the repeated local diagonal operator, not an abstract occupation projection.

**Theorem 1.3 (diagonalAction posSemidef).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every such conjugation preserves positive semidefiniteness.

**Definition 1.4 (cutPhase).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.cutPhase`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.cutPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At transposed registers the local diagonal entry is complex conjugated; at other registers it is unchanged.

**Theorem 1.5 (partialTranspose diagonalAction).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.partialTranspose_diagonalAction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.partialTranspose_diagonalAction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every subset of registers, including the empty and full subsets, the partial transpose of a summand equals conjugation of the same cut of the input by the cut diagonal. This is the actual product-basis transpose.

**Theorem 1.6 (diagonalAction fullyPPT).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_fullyPPT`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_fullyPPT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All nonempty proper PPT inequalities of the input survive each summand.

**Theorem 1.7 (tensor diagonal unitary).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.tensor_diagonal_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.tensor_diagonal_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When each local entry has norm one, the repeated local diagonal is an element of the actual matrix unitary group.

**Theorem 1.8 (Unitary conjugation at every cut).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.cut_diagonal_unitary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.cut_diagonal_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual cutPhase diagonal is unitary for norm-one local phases. Together with partialTranspose_diagonalAction, this proves that each transposed summand is a unitary conjugation of the corresponding cut of E, including empty and full cuts.

**Theorem 1.9 (edgeMarginal diagonalAction).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.edgeMarginal_diagonalAction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.edgeMarginal_diagonalAction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For norm-one local phases, every ordered two-register marginal transforms by the corresponding two-site local diagonal conjugation. Complement factors cancel exactly and no dimension factor occurs.

**Theorem 1.10 (diagonalAction bose).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_bose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_bose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual full Bose support is retained, using column symmetry and the canonical symmetric projector.

**Definition 1.11 (diagonalAverage).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum of actual diagonal conjugations is divided by the cardinality of its indexing type. Trace normalization of the input is never assumed.

**Theorem 1.12 (diagonalAverage posSemidef).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The average is positive semidefinite when the input is positive semidefinite.

**Theorem 1.13 (diagonalAverage fullyPPT).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage_fullyPPT`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage_fullyPPT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original proper PPT cut survives averaging.

**Theorem 1.14 (diagonalAverage bose).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage_bose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage_bose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full symmetric-projector sandwich is retained by averaging a Bose-supported positive operator.

**Theorem 1.15 (edgeMarginal diagonalAverage).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.edgeMarginal_diagonalAverage`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.edgeMarginal_diagonalAverage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty averaging type, any prescribed ordered marginal fixed by every local diagonal conjugation remains exactly the same marginal of the average.

**Definition 1.16 (occupationPhase).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationPhase`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Independent local phases are sampled from the (r+1)-st roots of unity. Counts in words of length r are strictly smaller than r+1, so occupation characters cannot alias.

**Theorem 1.17 (occupation character orthogonality).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupation_character_orthogonality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupation_character_orthogonality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite character sum is the group cardinality for equal occupations and zero for distinct occupations. Separation is proved from actual occupation counts.

**Definition 1.18 (occupationTwirl).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit finite diagonal-unitary average uses these independent root-of-unity phases on r actual tensor registers.

**Theorem 1.19 (occupationTwirl apply).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An entry between words with equal occupations is unchanged; an entry between distinct occupations is exactly zero. This finite average has precisely the occupation dephasing action of the diagonal torus.

**Theorem 1.20 (occupationTwirl occupation offdiag).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl_occupation_offdiag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl_occupation_offdiag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All off-diagonal entries between distinct normalized uniform Dicke occupation vectors vanish. These are the existing repository sectorVector definitions.

**Theorem 1.21 (twirl star core).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.twirl_star_core`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.twirl_star_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every genuine no-PPT star witness for the actual Dicke operator has a complete Bose witness given by this explicit average, diagonal in the occupation basis. All ordered prescribed marginals are retained. No inverse, strict positivity, coefficient sum, or trace-one assumption is used.

**Theorem 1.22 (twirl star).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.twirl_star`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.twirl_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same construction retains every fully PPT cut as well. The existence conclusion follows from this witness construction; the averaged matrix need not equal the original matrix.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.cutPhase`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.cut_diagonal_unitary`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_bose`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_fullyPPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_posSemidef`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage_bose`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage_fullyPPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage_posSemidef`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.edgeMarginal_diagonalAction`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.edgeMarginal_diagonalAverage`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationPhase`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl_apply`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl_occupation_offdiag`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupation_character_orthogonality`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.partialTranspose_diagonalAction`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.tensorPhase`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.tensor_diagonal_unitary`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.twirl_star`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.twirl_star_core`
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../OccupancyWordSectors.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension](DickeExtension.md)
