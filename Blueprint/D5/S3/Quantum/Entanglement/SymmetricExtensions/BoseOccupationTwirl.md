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

## Application: unitary conjugation at every cut

Let I and L be arbitrary finite types and u : L to Complex satisfy norm(u(a))=1 for every a. For each computational word x : I to L, tensorPhase u x is the product over i of u(x(i)). The norm-product identity gives norm(tensorPhase u x)=1, and Complex.mul_conj' gives tensorPhase u x times its complex conjugate equal to one. Matrix.diagonal_conjTranspose and Matrix.diagonal_mul_diagonal therefore give D D-adjoint=1 for D=diagonal(tensorPhase u). Matrix.mem_unitaryGroup_iff identifies D as an actual unitary matrix.

For every S : Finset I, cutPhase S u x instead conjugates u(x(i)) exactly when i belongs to S. Conjugation preserves the norm, so the same norm-product and Complex.mul_conj' calculation gives norm(cutPhase S u x)=1 and cutPhase S u x times its conjugate equal to one. The same diagonal identities and Matrix.mem_unitaryGroup_iff make diagonal(cutPhase S u) unitary. The existing partialTranspose_diagonalAction identity thus expresses every cut of diagonalAction u E as a unitary conjugation of that same cut of E, for arbitrary E, including empty and full cuts.

These applications of the existing scalar and matrix results include empty index types and require no inverse of E, positivity, nonsingularity or trace normalization. In occupationTwirl the required local norm-one premise is supplied by occupationPhase_norm, so the finite average is an average of actual tensor unitaries. Its exact occupation action is proved by occupation_character_orthogonality and occupationTwirl_apply.

**Theorem 1.7 (edgeMarginal diagonalAction).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.edgeMarginal_diagonalAction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.edgeMarginal_diagonalAction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For norm-one local phases, every ordered two-register marginal transforms by the corresponding two-site local diagonal conjugation. Complement factors cancel exactly and no dimension factor occurs.

**Theorem 1.8 (diagonalAction bose).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_bose`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_bose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual full Bose support is retained, using column symmetry and the canonical symmetric projector.

**Definition 1.9 (diagonalAverage).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum of actual diagonal conjugations is divided by the cardinality of its indexing type. Trace normalization of the input is never assumed.

The finite diagonal average preserves positivity term by term; this property is used by the retained occupation twirl application.

Each retained proper PPT cut is transported through the actual diagonal conjugations before averaging.

The full symmetric-projector sandwich is preserved by the diagonal average whenever the input has it.

A prescribed ordered marginal fixed by every local diagonal conjugation is preserved by the finite average, with its original unnormalized trace.

**Definition 1.10 (occupationPhase).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationPhase`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Independent local phases are sampled from the (r+1)-st roots of unity. Counts in words of length r are strictly smaller than r+1, so occupation characters cannot alias.

**Theorem 1.11 (occupation character orthogonality).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupation_character_orthogonality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupation_character_orthogonality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite character sum is the group cardinality for equal occupations and zero for distinct occupations. Separation is proved from actual occupation counts.

**Definition 1.12 (occupationTwirl).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl`

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit finite diagonal-unitary average uses these independent root-of-unity phases on r actual tensor registers.

**Theorem 1.13 (occupationTwirl apply).**

Lean statement: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An entry between words with equal occupations is unchanged; an entry between distinct occupations is exactly zero. This finite average has precisely the occupation dephasing action of the diagonal torus.

Entrywise occupation dephasing also makes distinct normalized uniform Dicke occupation vectors orthogonal under the averaged matrix.

For a genuine no-PPT Dicke star witness, the explicit occupation twirl is diagonal in the occupation basis, preserves every ordered marginal fixed by the local action, and retains positivity and full Bose support. No inverse, strict positivity, coefficient-sum or trace-one premise is used; zero and singular witnesses remain in scope.

The same finite average transports every fully PPT cut and supplies an existence witness; the averaged matrix need not equal the input.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.cutPhase`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_bose`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_fullyPPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAction_posSemidef`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.diagonalAverage`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.edgeMarginal_diagonalAction`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationPhase`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupationTwirl_apply`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.occupation_character_orthogonality`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.partialTranspose_diagonalAction`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseOccupationTwirl.tensorPhase`
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../OccupancyWordSectors.md)
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricExtensions/DickeExtension](DickeExtension.md)
