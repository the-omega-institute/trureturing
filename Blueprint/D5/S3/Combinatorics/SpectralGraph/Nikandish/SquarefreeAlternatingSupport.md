# SquarefreeAlternatingSupport

## Abstract

Full squarefree alternating spectral construction

Source: PR3 b93becea662a746badeadba42fdc3d3eb3db9382, paper/sections/squarefree.tex, blob2cd18d52cd3f4581d624bb94006480340756a5c3. Original Nikandish graph/problem attribution and manuscript Ma/Nikandish/Zhang credit, prerequisites, reports, failed methods and rights boundaries are preserved. All alternating pairs and all tail supports are retained; nonzero vectors lift to the genuine ideal-intersection graph for arbitrary injective prime assignments. This is the full spectral construction, separately from the already-delivered stronger unit-entry nonintegrality theorem. General Q3, exact n7/paused exclusions, a6 certification and finite-enumeration reproducibility limits are unchanged. Unfinished escape audits are disclosed at issue28398; disclosure is not proof, audit completion or a waiver of other gates.

**Theorem 1.1 (Full diagonal pair action).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.E_action`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.E_action` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every alternating pair contributes determinant2 to the full E action, for arbitrary finite remaining coordinate index and every real-valued tail vector.

**Theorem 1.2 (Full disjoint-support pair action).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.F_action`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.F_action` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every alternating pair contributes determinant-1 to the entire disjoint-support operator, including all cells outside the nonzero paired support.

**Theorem 1.3 (Scalar transport).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.lift_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.lift_smul` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Scalar multiplication commutes with every recursively paired lift; this helper is consumed by full eigenpair transport.

**Theorem 1.4 (Additive transport).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.lift_add`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.lift_add` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Addition commutes with every recursively paired lift; the actual reduced-operator intertwining consumes this helper.

**Theorem 1.5 (All nonzero vectors survive).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.lift_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.lift_nonzero` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every number of alternating pairs and every nonzero real vector on the full remaining support set, its complete lift is nonzero.

**Theorem 1.6 (All diagonal factors).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.E_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.E_lift` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every pair count r, the full E action is2^r times the lift of the residual E action.

**Theorem 1.7 (All disjoint-support factors).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.F_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.F_lift` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every pair count r, the full F action is(-1)^r times the lift of the residual F action.

**Theorem 1.8 (Full repeated-pair restriction).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.K_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.K_lift` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The two actual operator summands reduce with their exact2^(r+1) and(-1)^r coefficients; no compressed energy or unproved invariance premise replaces the operator equation.

**Theorem 1.9 (Full invariant-subspace identity).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.reduced_intertwining`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.reduced_intertwining` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every residual vector, applying the entire repeated-pair operator to its lift is exactly the lift of the residual operator action.

**Theorem 1.10 (Actual squarefree graph lift).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.actual_eigenvalue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.actual_eigenvalue` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every nonzero eigenpair of the complete residual operator lifts to a genuine Laplacian eigenvalue of the squarefree ideal-intersection graph, with every paired coordinate and arbitrary distinct prime values. The source cardinal expression and reflected endpoint are retained.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.E_action`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.E_lift`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.F_action`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.F_lift`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.K_lift`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.actual_eigenvalue`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.lift_add`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.lift_nonzero`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.lift_smul`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SquarefreeAlternatingSupport.reduced_intertwining`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport](RepeatedPairSupport.md)
