# Actual Leech Sector Characters

## Abstract

Absolute graded traces and modular transformations of the four literal Leech sectors.

**Definition 1.1 (Lattice parity grades).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.latticeSectorGrade`

*Formalization.* `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.latticeSectorGrade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed and anti-fixed parts of a lattice Sugawara eigenspace are the literal lattice sector grades.

**Definition 1.2 (Twisted parity grades).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.twistedSectorGrade`

*Formalization.* `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.twistedSectorGrade` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At degree n the literal twisted stress eigenspace of weight 3/2 + n/2 is intersected with the selected oscillator-parity eigenspace.

**Definition 1.3 (Normalized finite-grade trace).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorTerm`

*Formalization.* `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each term is the identity trace on the corresponding parity-projected grade times its energy exponential with vacuum shift c/24 = 1.

**Definition 1.4 (Ordered sector characters).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorCharacter`

*Formalization.* `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four trace series are ordered as the fixed lattice sector, the anti-fixed lattice sector, the oscillator-odd twisted sector and the oscillator-even twisted sector.

**Theorem 1.5 (Absolute sums and the holonomy basis).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sector_trace_series`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sector_trace_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the upper half-plane each literal graded trace series converges absolutely. The lattice pair is the half-sum and half-difference of the untwisted holonomy traces. The twisted pair is the half-sum and half-difference of the twisted holonomy traces with physical insertion equal to minus oscillator parity.

**Definition 1.6 (Sector S matrix).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorS`

*Formalization.* `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient matrix is one half of the symmetric four by four sign matrix with rows ++++, ++--, +-+- and +--+.

**Definition 1.7 (Sector T matrix).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorT`

*Formalization.* `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shifted T matrix is diagonal with entries 1, 1, 1 and -1.

**Theorem 1.8 (S action on the literal characters).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorCharacter_S`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorCharacter_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Swapping the spatial and temporal holonomies yields the sector S matrix after the parity-trace identities are applied.

**Theorem 1.9 (T action on the literal characters).**

Lean statement: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorCharacter_T`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorCharacter_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging the twisted holonomy entries fixes their half-sum and reverses their half-difference. Both untwisted entries are fixed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.latticeSectorGrade`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorCharacter`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorCharacter_S`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorCharacter_T`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorS`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorT`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sectorTerm`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.sector_trace_series`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/ActualLeechSectorCharacters.twistedSectorGrade`
