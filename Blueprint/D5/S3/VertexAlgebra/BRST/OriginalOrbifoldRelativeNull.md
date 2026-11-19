# Native relative BRST exactness at nonzero null momentum

## Abstract

The native relative BRST complex at integral null momentum

Use the actual Golay–Leech orbifold of central charge 24 and the ordered hyperbolic lattice of central charge 2 as matter. The state space tensors that matter with the native bc occupation Fock space. For an integral charge a = (a₀, a₁), the ordered Gram matrix has off-diagonal entries 1 and diagonal entries 0, so the charge half-norm is a₀a₁. The relative mass shell at a is the intersection of the fixed-charge space with the kernels of b₀ and total L₀. Its d is the restriction of the original Q. Charge preservation, the b₀ Ward identity, and commutation with total L₀ make that restriction well-defined. The critical-matter square identity gives d² = 0.

**Theorem 1.1 (Relative ghost level zero).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.levelOccupationSets_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.levelOccupationSets_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The level-zero occupation set contains only {1}. The relative condition excludes site 3, the c₀ site.

**Theorem 1.2 (Relative ghost level one).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.levelOccupationSets_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.levelOccupationSets_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The level-one occupations are ∅ and {1, 5}.

**Theorem 1.3 (Complete null-shell labels).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.allowedLabels_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.allowedLabels_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At half-norm zero the orbifold weight, hyperbolic oscillator energy and relative ghost level must sum to 1. The actual orbifold has no weight-one states and its weight-zero line is the vacuum line. Thus either there is exactly one first-frequency hyperbolic oscillator with occupation {1}, or there are no oscillators and the ghost occupation is ∅ or {1, 5}. In all cases the momentum is the original a.

**Definition 1.4 (Literal tensor representatives).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellVector`

*Formalization.* `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At fixed charge a, write B for the actual orbifold vacuum tensored with the charged oscillator monomial 1 and the empty ghost ket. Write Mᵢ for the same vacuum with charged monomial X(i,0) and ket {1}, where i is 0 or 1. Write T for the vacuum with charged monomial 1 and ket {1, 5}. The polynomial index 0 is frequency one.

**Definition 1.5 (Basis of the actual relative mass shell).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellBasis`

*Formalization.* `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shell basis restricts the ambient basis to the allowed labels and normalizes the common nonzero vacuum scalar. The order is B, M₀, M₁, T.

**Theorem 1.6 (Basis tensors in the original carrier).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellBasis_coe`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellBasis_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the inclusion of the relative mass shell into the state space, each basis vector is the corresponding literal tensor representative.

**Theorem 1.7 (Four-dimensional null shell).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shell_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shell_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex dimension is 4 at every integral zero-half-norm charge.

**Definition 1.8 (Shell ghost numbers).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.ghostNumber`

*Formalization.* `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.ghostNumber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The basis labels B, M₀, M₁, T have ghost numbers 0, 1, 1, 2 respectively.

**Theorem 1.9 (Native grading on the tensors).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.ghostNumber_shellVector`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.ghostNumber_shellVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original lifted ghost-number operator acts on each literal tensor by its designated ghost number.

On these tensors Q is the statewise finite sum of Lₘ ⊗ c(−m) plus the native cubic ghost term Qg acting on the ghost factor. For m ≥ −1 the orbifold mode kills the vacuum by translation at m = −1 and creativity at m ≥ 0. For m < −1 the ghost mode annihilates each of the three occupations. The remaining matter modes therefore act through the actual hyperbolic Sugawara operators.

**Theorem 1.10 (Native action on the bottom tensor).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.Q_bottom`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.Q_bottom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Qg kills the empty ket. Hyperbolic L₀ gives the half-norm, which vanishes, and all positive modes kill the charged ground monomial. At m = −1 the Sugawara mode creates the current with coefficients (a₀, a₁), and c(1) takes the empty ket to ket {1} with sign +1. Thus Q B = a₀ M₀ + a₁ M₁.

**Theorem 1.11 (Native action on the one-oscillator tensors).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.Q_middle`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.Q_middle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At m = −1, c(1) repeats the occupied site 1 and vanishes. At m = 0 the matter eigenvalue is 1 and the contribution with c(0) cancels Qg on ket {1}. For m > 0, the Sugawara–current commutator reduces the matter action to current mode m−1 on the charged ground. This vanishes for m > 1. At m = 1 the current zero mode gives the Gram pairing of the i-th ordered basis vector with a, namely a₁ for i = 0 and a₀ for i = 1. The native occupation sign is c(−1) ket {1} = −ket {1, 5}, so Q M₀ = −a₁ T and Q M₁ = −a₀ T.

**Theorem 1.12 (Native action on the top tensor).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.Q_top`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.Q_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Qg kills ket {1, 5}. The m = −1 term repeats site 1, L₀ kills the null charged ground, and positive matter modes kill that ground. Thus Q T = 0.

**Theorem 1.13 (The three graded maps).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.differential_on_basis`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.differential_on_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the ordered basis the maps in ghost degrees 0, 1 and 2 are t ↦ (a₀t, a₁t), (v₀, v₁) ↦ −a₁v₀ − a₀v₁, and the zero map. The basis inclusions identify these maps with Q on the actual tensors. These formulas also hold at a = 0.

**Definition 1.14 (Explicit differential in four coordinates).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateDifferential`

*Formalization.* `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateDifferential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write a vector as (t, v₀, v₁, w) in the order B, M₀, M₁, T. The differential sends it to (0, a₀t, a₁t, −a₁v₀ − a₀v₁).

**Definition 1.15 (Explicit degree-lowering homotopy).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateHomotopy`

*Formalization.* `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateHomotopy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the same order, h sends (t, v₀, v₁, w) to (a₀⁻¹v₀ + a₁⁻¹v₁, −a₁⁻¹w, −a₀⁻¹w, 0). The inverse of zero in ℂ is zero.

**Theorem 1.16 (Square zero on the null axes).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateDifferential_squared`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateDifferential_squared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The only possible entry of the square is the top coordinate −2a₀a₁t. It vanishes for every integral charge on either null axis.

**Theorem 1.17 (Contraction in coordinates).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateHomotopy_contracts`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateHomotopy_contracts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero integral null charge, exactly one of a₀ and a₁ is nonzero. Its product with its inverse is 1, giving dh + hd = 1 on all four coordinates.

**Theorem 1.18 (Range equals kernel in coordinates).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateDifferential_exact`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateDifferential_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square-zero identity puts the range in the kernel. For a closed vector x the homotopy gives x = d(hx), proving the reverse inclusion.

**Definition 1.19 (Linear equivalence given by the shell basis).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellCoordinates`

*Formalization.* `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence sends each native basis vector to its coordinate unit vector.

**Theorem 1.20 (Conjugacy with the native differential).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.differential_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.differential_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking shell coordinates after applying the restricted Q agrees with applying the explicit differential after taking shell coordinates. This equality holds at every integral null charge, including zero.

**Theorem 1.21 (Contraction on either nonzero null axis).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.exists_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.exists_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a ≠ 0 with a₀a₁ = 0, take j to be the sole index with aⱼ ≠ 0 and k the other index. Define h(Mⱼ) = B/aⱼ and h(T) = −Mₖ/aⱼ, with h(B) = h(Mₖ) = 0. Extend complex-linearly. On B and Mₖ the term hd is the identity. On Mⱼ and T the term dh is the identity. This proves dh + hd = 1 on the relative mass shell.

**Theorem 1.22 (Vanishing relative cohomology at nonzero null charge).**

Lean statement: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.differential_exact`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.differential_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integral a with chargeEnergy hyperbolicData a = 0 and a ≠ 0, Lean proves LinearMap.range (differential a) = LinearMap.ker (differential a). The shell-coordinate equivalence transports the equality of range and kernel to the restricted native operator. At a = 0 the same four-dimensional shell has d = 0, so its kernel is the entire shell and its range is zero. Exactness here concerns the native relative complex of this particular orbifold and hyperbolic plane at nonzero null charge.

The shell calculation and contraction are repository derivations from the original lattice, orbifold and occupation-ghost operators. The Virasoro BRST construction supplies the mode conventions and Ward identities.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.Q_bottom`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.Q_middle`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.Q_top`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.allowedLabels_iff`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateDifferential`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateDifferential_exact`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateDifferential_squared`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateHomotopy`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.coordinateHomotopy_contracts`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.differential_conjugate`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.differential_exact`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.differential_on_basis`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.exists_contraction`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.ghostNumber`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.ghostNumber_shellVector`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.levelOccupationSets_one`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.levelOccupationSets_zero`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellBasis`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellBasis_coe`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellCoordinates`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shellVector`
- Truth anchor: `D5/S3/VertexAlgebra/BRST/OriginalOrbifoldRelativeNull.shell_finrank`
