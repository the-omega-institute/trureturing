# The original zero-momentum relative shell and its actual operators

## Abstract

The original zero-momentum relative shell and its actual operators

Let D : LatticeData have arbitrary natural rank, including zero, and let H be a complex matrix indexed by Fin D.rank. The operator and shell-basis results state both equations H * gramComplex D = 1 and gramComplex D * H = 1 explicitly. No signature, positive form, distinguished null frame, nonzero light-cone component or rank 26 condition is imposed.

State D is the original all-charge Carrier D tensor the countable occupation Fock space. The shell is literally fixedMomentum D 0 intersect ker(ghostB D 0) intersect ker(totalL0 D H), where totalL0 is the unshifted original matter-plus-ghost zero mode. Its original labels satisfy oscillatorEnergy d + relativeEnergy S = 1 and exclude ghost site 3. relativeEnergy S = energy S + 1 rewrites this original equation; it does not change the operator or add an intercept.

The actual site energies force every allowed low occupation into {1,5}: even sites have energy at least two, and every odd site other than 1,3,5 has energy at least two. Site 1 has energy minus one, site 3 is excluded by b(0), and site 5 has energy one. Thus relative energy zero has exactly occupation {1}, while relative energy one has exactly the empty occupation and {1,5}. Oscillator energy one has exactly one original frequency-zero current. These exhaust all original zero-shell labels.

Write g for the existing neutral ground and J_i for the existing currentState. The original shell basis consists of g tensor ket empty, J_i tensor ket {1} for every i, and g tensor ket {1,5}. Its actual basis representation gives shellEquiv with coefficient space Complex x ((Fin D.rank -> Complex) x Complex). Its inverse followed by the original inclusion is Psi(A,v,C) = A*(g tensor ket empty) + (sum_i v(i)*J_i) tensor ket {1} + C*(g tensor ket {1,5}). Surjectivity concerns the entire literal original shell.

The original charge is exactly LatticeBRST.totalCharge = T + ghostCharge with the original cubic Qg. For odd occupations the pure-c Ward sum at integer r is captured on the finite interval [r-1,1]; outside this interval one c-mode annihilates the occupation, directly or after CAR. The actual cubic action on ket {1} is -c(0) ket {1}. The actual matter sum on J_i tensor ket {1} retains exactly its m=0 term J_i tensor c(0) ket {1}, so these two original terms cancel. The original ground and two-ghost basis branches are also annihilated. Exhaustion then proves totalCharge x = 0 for every literal zero-shell state, without assuming nilpotence.

The number operator is the existing LatticeMatterGhostDegree.tensorNumber, the identity on matter tensored with BcGhostCharge.ghostNumber. It is actual signed occupation charge and has basis eigenvalues 0,1,2. Hence its coordinate action is (A,v,C) -> (0,v,2*C). This is neither a longitudinal filtration nor a shifted degree.

The original carrier and operators retain their repository supplier definitions. Basis reindexing and finite coordinate equivalences reuse Mathlib under Apache 2.0. The conclusions are algebraic prerequisites. They assert no cohomology computation, positivity, no-ghost theorem, Monster or moonshine construction, full VOA/CFT or string model, or AdS/CFT correspondence.

**Theorem 1.1 (relativeEnergy_empty).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.relativeEnergy_empty`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.relativeEnergy_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty original occupation has relative energy one.

**Theorem 1.2 (relativeEnergy_down).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.relativeEnergy_down`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.relativeEnergy_down` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original occupation {1} has relative energy zero.

**Theorem 1.3 (relativeEnergy_top).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.relativeEnergy_top`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.relativeEnergy_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original occupation {1,5} has relative energy one.

**Theorem 1.4 (ghost_level_zero_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ghost_level_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ghost_level_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite occupation S excluding site 3, relativeEnergy S = 0 if and only if S = {1}.

**Theorem 1.5 (ghost_level_one_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ghost_level_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ghost_level_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite occupation S excluding site 3, relativeEnergy S = 1 if and only if S is empty or {1,5}.

**Theorem 1.6 (oscillatorEnergy_one_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.oscillatorEnergy_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.oscillatorEnergy_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lattice datum D and original exponent d, oscillatorEnergy d = 1 if and only if d is single (i,0) 1 for some i : Fin D.rank.

**Definition 1.7 (ZeroIndex).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ZeroIndex`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ZeroIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index type Unit + (Fin D.rank + Unit) includes both scalar states and every original current, including when rank is zero.

**Definition 1.8 (zeroLabel).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroLabel`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The labels are ((0,0),empty), ((0,single (i,0) 1),{1}) and ((0,0),{1,5}) in the original tensor label type.

**Theorem 1.9 (allowed_zero_iff).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.allowed_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.allowed_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original tensor label l, l belongs to allowedLabels D 0 if and only if l is zeroLabel D k for an index k. This proves exhaustion.

**Definition 1.10 (zeroIndexEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroIndexEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroIndexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Injectivity of the displayed labels and their exhaustion give an equivalence with the original ShellIndex D 0.

**Definition 1.11 (ground).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ground`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ground` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This abbreviation refers to the existing original charge-zero vacuum in LatticeAllStateField.

**Definition 1.12 (current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.current`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.current` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This abbreviation refers to the existing currentState of LatticeActualConformalState; its original oscillator frequency is zero and its energy is one.

**Definition 1.13 (zeroVector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroVector`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each index gives its original matter vector tensored with the displayed occupation ket.

**Definition 1.14 (zeroBasis).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroBasis`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under both inverse-Gram equations, reindexing the original shellBasis gives a basis of the literal original zero-momentum relative shell.

**Theorem 1.15 (zeroBasis_coe).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroBasis_coe`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroBasis_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every basis index, coercion into the original tensor carrier gives exactly zeroVector D k.

**Definition 1.16 (Coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Coordinates`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient space is Complex x ((Fin D.rank -> Complex) x Complex).

**Definition 1.17 (shellEquiv).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.shellEquiv`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.shellEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The basis representation and the splitting of its finite index give a linear equivalence from the entire original shell to Coordinates D.

**Definition 1.18 (Psi).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Psi`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse coordinate equivalence followed by the original submodule inclusion maps coordinates into the original State D.

**Theorem 1.19 (Psi_formula).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Psi_formula`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Psi_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coordinate tuple (A,v,C), Psi is A times the original vacuum tensor ket empty, plus the sum of v(i) times the original currents tensor ket {1}, plus C times the original vacuum tensor ket {1,5}. Both inverse-Gram equations are explicit.

**Theorem 1.20 (Qg_down).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Qg_down`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Qg_down` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original cubic charge on ket {1} is minus c(0) applied to ket {1}. The full Ward sum is evaluated using its all-integer annihilation tail and CAR.

**Theorem 1.21 (c_minus_one_down).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.c_minus_one_down`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.c_minus_one_down` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual occupation creation phase gives c(-1) ket {1} = -ket {1,5}.

**Theorem 1.22 (Qg_top).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Qg_top`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Qg_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original cubic charge annihilates ket {1,5}; the c(-1) Ward identity and the actual occupation phase determine the cancellation.

**Theorem 1.23 (sugawara_ground).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.sugawara_ground`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.sugawara_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, every complex rank-indexed matrix H, and every integer m >= -1, the actual Sugawara mode kills the original neutral ground. Positive and zero modes use the existing charged-ground formulas; the minus-one mode has vanishing neutral contractions.

**Theorem 1.24 (T_current_down).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.T_current_down`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.T_current_down` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both inverse-Gram equations, the full matter coupling on current(i) tensor ket {1} is current(i) tensor c(0) ket {1}. Every summation index other than zero is proved to vanish.

**Theorem 1.25 (totalCharge_zeroVector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalCharge_zeroVector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalCharge_zeroVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under both inverse-Gram equations, the actual totalCharge annihilates every displayed basis vector. On the current branch the actual matter zero term cancels the original cubic term.

**Theorem 1.26 (totalCharge_on_zero_shell).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalCharge_on_zero_shell`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalCharge_on_zero_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original tensor state x in the literal unshifted zero-momentum relative shell, totalCharge D H x = 0 under the two inverse-Gram equations. Basis exhaustion supplies the arbitrary-state conclusion.

**Definition 1.27 (shellGhostDegree).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.shellGhostDegree`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.shellGhostDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three branches have degrees zero, one and two respectively. These are actual signed occupation numbers on the allowed occupations.

**Theorem 1.28 (totalGhostNumber_zeroVector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalGhostNumber_zeroVector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalGhostNumber_zeroVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing tensorNumber acts on each original zeroVector by its displayed degree, with no grading shift.

**Theorem 1.29 (totalGhostNumber_Psi).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalGhostNumber_Psi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalGhostNumber_Psi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all coordinates (A,v,C), the existing actual tensorNumber sends Psi(A,v,C) to Psi(0,v,2*C), under both inverse-Gram equations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Coordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Psi`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Psi_formula`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Qg_down`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.Qg_top`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.T_current_down`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ZeroIndex`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.allowed_zero_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.c_minus_one_down`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.current`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ghost_level_one_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ghost_level_zero_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.ground`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.oscillatorEnergy_one_iff`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.relativeEnergy_down`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.relativeEnergy_empty`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.relativeEnergy_top`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.shellEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.shellGhostDegree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.sugawara_ground`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalCharge_on_zero_shell`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalCharge_zeroVector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalGhostNumber_Psi`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.totalGhostNumber_zeroVector`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroBasis_coe`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroIndexEquiv`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroLabel`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeZeroMomentumBRST.zeroVector`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](LatticeBRSTWard.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree](LatticeMatterGhostDegree.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell](LatticeRelativeMassShell.md)
