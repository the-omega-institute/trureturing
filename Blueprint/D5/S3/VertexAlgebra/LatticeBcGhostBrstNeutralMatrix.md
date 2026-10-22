# The Original Neutral BRST Matrix

## Abstract

The original BRST charge has an exact neutral vacuum and one-oscillator matrix action on the original algebraic lattice-ghost state space.

D and H remain arbitrary original inputs. The state space is the original Carrier(D) tensor over Complex with Fock(Complex). The vectors vacuumState, uState, jState and kState are the actual definitions in the neutral matrix module; no inverse-Gram, positivity, nondegeneracy, intercept or rank-26 premise is added.

**Theorem 1.1 (The original vacuum is closed).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D and arbitrary complex H, the actual vacuumState D is annihilated by Q D H. This is the neutral endpoint specialization of the original vacuum-class proof.

**Theorem 1.2 (The c0 vacuum action).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_c0_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_c0_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D and arbitrary H, Q applied to uState D equals -2 times zState D. The proof uses the actual c-current variation at mode zero, whose V row is the ghost-only weighted c-current row rather than a Sugawara boundary mode, and the already proved vacuum action.

**Theorem 1.3 (The uniform neutral one-oscillator matrix).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_one_oscillator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_one_oscillator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D, arbitrary complex H and t in Fin(D.rank), Q applied to jState D t is the sum over s of (neutralCoefficient D H s t minus kronecker D s t) times kState D s. Here neutralCoefficient is exactly one half of the symmetrized H contraction with gramComplex D.

The proof retains the complete statewise finite Q_tmul summand support reduction to modes -1, 0 and 1. After that support reduction, the boundary matter contributions at modes -1 and 1 vanish; the exact zero-mode matter calculation gives the matrix coefficient, and the surviving ghost outer terms at n=-1 and n=0 give the Kronecker subtraction. The V row used by the c-current action is the ghost-only weighted c-current row, not a Sugawara boundary mode. Both unbounded ordering tails are handled on the actual state.

**Theorem 1.4 (The c0 one-oscillator states are closed).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_c0_one_oscillator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_c0_one_oscillator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D, arbitrary H and t, Q applied to kState D t is zero. This consumes the one-oscillator matrix law, the actual c-current variation and the exact vanishing of the ghost-only V-zero row on this state.

**Theorem 1.5 (The canonical z state is closed).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_z`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_z` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D and arbitrary H, Q applied to zState D is zero. The proof uses the c-action commutator and the exact ghost-only V-one and V-minus-one row evaluations, including the ghost anticommutation sign relating C-minus-one C-one C-zero to wState.

**Theorem 1.6 (The canonical w state is closed).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_w`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_w` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D and arbitrary H, Q applied to wState D is zero. The proof uses the exact ghost-only V-zero and V-minus-one row vanishings on the nested c-state together with the c-action commutator.

This document makes no assertion for neutral exhaustion, full cohomology, nonzero charges, no-ghost results, string completion or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_c0_one_oscillator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_c0_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_one_oscillator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_w`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstNeutralMatrix.Q_z`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstCAction](LatticeBcGhostBrstCAction.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass](LatticeBcGhostBrstVacuumClass.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraConformal](LatticeSugawaraConformal.md)
