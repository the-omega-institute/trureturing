# Original EnergyBasis

## Abstract

The actual original Sobolev completions acquire a full energy basis from their finite completed grades and an exact weighted quadratic certificate.

The fixed Model retains the actual LatticeData D of arbitrary rank, including zero, positive definiteness of gramReal D, the complex inverse matrix, and both inverse-Gram equations. Carrier D, Hm, normD, grade, completedGrade, Sobolev and embed are reused. Within a grade the full mixed-colour Hermitian Gram form remains; monomial coefficients are never declared orthogonal. The algebraic Sugawara theorem supplies L0-energy E, while the Sobolev norm uses 1+L0.

**Definition 1.1 (energyIndex).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyIndex`

*Formalization.* `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each k, the index type is the sigma over integer E of Fin(finrank Complex (completedGrade k E)). Every fiber is therefore the dimension of the actual completed grade. No spectral basis or dimension-growth hypothesis is added.

**Definition 1.2 (energyGradeBasis).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyGradeBasis`

*Formalization.* `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyGradeBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use Mathlib stdOrthonormalBasis on each actual finite-dimensional completedGrade k E. This basis is orthonormal for its inherited original Sobolev norm, not for the monomial coordinate metric.

**Definition 1.3 (energyVector).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyVector`

*Formalization.* `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Include the finite grade orthonormal basis by its actual submodule inclusion into Sobolev k. Since completedGrade is the range of the original gradeMap and already closed by finite dimensionality, each energyVector has an actual original finite preimage.

**Theorem 1.4 (completedGrade negative).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.completedGrade_negative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.completedGrade_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Model, every natural k and integer E<0, completedGrade k E is bottom. Lift a member to its original algebraic grade and use OriginalWordEnergy.negative_grade_eq_zero, which follows from actual charge-energy positivity and coefficient support. Its embedding is zero. Thus the construction retains empty negative fibers instead of assuming away negative integers.

The proof sobolev_embed_inner identifies the completion pairing with Hm((1+L0)^k u,(1+L0)^k v). OriginalNeutralEnergy.energy_power_grade moves each power to its scalar grade weight. Hm_grade_orthogonal then proves orthogonality of different completed grades. This is the missing original-metric bridge, including the two inverse equations; it is not a generic diagonal metric assumption.

**Definition 1.5 (energyBasis).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyBasis`

*Formalization.* `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite-dimensional grade bases span each original grade by OrthonormalBasis.toBasis.span_eq and span induction. The original sum_gradeProjections then shows that their joint algebraic span equals exactly embed k range. Completion density proves that span is dense. OrthogonalFamily.orthonormal_sigma_orthonormal and HilbertBasis.mk assemble the full Hilbert basis. OriginalHeat actually consumes this basis.

**Theorem 1.6 (energyBasis coe).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyBasis_coe`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyBasis_coe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every k the constructed Hilbert basis has exactly the included original completed-grade vectors. This consumed constructor identity is used in the heat completed-grade expansion; it is not an independent novelty claim.

**Theorem 1.7 (finiteCore eq energyBasis span).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.finiteCore_eq_energyBasis_span`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.finiteCore_eq_energyBasis_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, the span of the actual energy Hilbert basis is exactly the original finite carrier image. One inclusion uses finite grade expansions and sum_gradeProjections; the reverse uses each grade basis vector actual original preimage. The actual heat inclusion proof consumes this equality to obtain density from the Hilbert basis.

**Theorem 1.8 (energyIndex nonnegative).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyIndex_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyIndex_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k and every actual energy-basis index i, the energy i.1 is nonnegative. A negative energy would force its completed grade to bottom, its finrank to zero and its Fin index to be impossible. No positive-rank assumption is introduced; rank zero keeps its nonzero original vacuum line.

**Theorem 1.9 (finite grade quadratic).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.finite_grade_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.finite_grade_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite F of integer energies and arbitrary original u(E) in grade E and arbitrary complex b(E), the squared k-th Sobolev norm of embed k of the finite weighted sum is the sum of |b(E)| squared times (1+E)^(2k) times normD(u(E)) squared. OriginalNeutralEnergy.normD_orthogonal_sum supplies finite Pythagoras after applying the actual energy power. For E>=0 each term is evaluated with sobolev_grade_norm; for E<0 the actual negative-grade theorem gives u(E)=0. No restriction on F is required, and all off-diagonal contributions inside normD(u(E)) remain intact.

**Theorem 1.10 (finite multiplier bound).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.finite_multiplier_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.finite_multiplier_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural source and target orders j,k, B>=0, original finite v and scalar family b on all integer energies, a pointwise bound |b(E)|(1+E)^k <= B(1+E)^j on stateEnergies v implies the actual original norm bound. Square the scalar inequality, multiply by the nonnegative original grade norm-square, sum using finite_grade_quadratic and the original decomposition, then use nonnegative square roots. This consumed comparison proves both global smoothing and cutoff tails.

Attribution: original lattice/Sugawara energy and full-frame Hermitian suppliers retain their Bakalov--Kac and original source citations. All completion, finite-dimensional basis and HilbertBasis machinery is Mathlib under Apache 2.0. This module claims original-model bridge content, with no literature novelty or accepted physical realization claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.completedGrade_negative`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyBasis_coe`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyGradeBasis`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyIndex`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyIndex_nonnegative`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.energyVector`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.finiteCore_eq_energyBasis_span`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.finite_grade_quadratic`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis.finite_multiplier_bound`
- Dependency: [D5/S3/VertexAlgebra/Analysis/OriginalSobolev](OriginalSobolev.md)
