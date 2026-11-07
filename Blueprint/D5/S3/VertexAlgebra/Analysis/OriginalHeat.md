# Original Heat

## Abstract

Actual original unshifted cylinder heat on whole Sobolev completions, with literal core and inclusion bridges and quantitative original finite-rank approximation.

**Definition 1.1 (heat).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat`

*Formalization.* `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every natural order k and every nonnegative-real time t, apply the existing DiagonalHeat.heat to the actual energyBasis k, with coefficient energy i.1 cast to Real. energyIndex_nonnegative proves the needed sign premise. The map is bounded and complex-linear on the entire original Sobolev space. The exponent is -t*E, not -t*(1+E).

**Theorem 1.2 (heat completedGrade).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_completedGrade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_completedGrade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original completed grade E, every k, nonnegative t and actual member x, heat k t x equals exp(-tE) times x. Expand x using its finite OrthonormalBasis.sum_repr, include that expansion into the actual Sobolev completion, and use the existing DiagonalHeat.heat_basis, supplied by multiplier_basis, for each of those genuine basis vectors. The grade membership, metric and actual basis are proved, not assumed.

**Theorem 1.3 (heat embed).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_embed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_embed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original finite v, every natural k and nonnegative t, heat k t(embed k v) is literally embed k of the finite sum over stateEnergies D v of exp(-tE) times gradeProjection D E v. Rewrite v with sum_gradeProjections, commute the actual linear maps with the finite sum and apply heat_completedGrade. No assumption about transformed supports or completed Hamiltonian domains appears.

The consumed heat_semigroup selects the strong contraction semigroup and its equality to the existing heat from DiagonalHeat.diagonal_heat. Its zero and addition laws, together with the public supplier contraction and continuity proofs, give the whole-space heat laws. Positivity comes from the same supplier theorem and its multiplier_positive proof.

**Theorem 1.4 (heat inclusion).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all original j<=k and t>=0, the actual inclusion j k intertwines heat k t and heat j t. On embed k v, the literal core formula and OriginalSobolev.inclusion_embed identify both maps with the same original finite energy sum in Sobolev j. Continuity and the dense original core extend the equality to every completed input.

**Theorem 1.5 (heat projection).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_projection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer E, arbitrary completed x, k and t>=0, heat after the genuine original projection and projection after heat both equal exp(-tE) times that projection. The first identity applies heat_completedGrade to the actual starProjection range member. The second uses the dense original grade decomposition and OriginalSobolev.projection_grade. Negative grades give zero maps by actual positivity.

**Definition 1.6 (energyCutoff).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.energyCutoff`

*Formalization.* `D5/S3/VertexAlgebra/Analysis/OriginalHeat.energyCutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite cutoff is the integer interval {0,...,N}, including zero at N=0. These sets are not asserted cofinal among all finite subsets of the integers.

**Definition 1.7 (cutoffSpace).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.cutoffSpace`

*Formalization.* `D5/S3/VertexAlgebra/Analysis/OriginalHeat.cutoffSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Finset.sup of the actual completedGrade k E over the original nonnegative cutoff is the finite sum of original completed grades. Mathlib finiteDimensional_finset_sup supplies its finite dimension; no multiplicity-growth estimate is assumed.

**Definition 1.8 (heatTruncation).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heatTruncation`

*Formalization.* `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heatTruncation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose original truncation k {0,...,N} after the actual whole-space heat. The input is arbitrary in the original Sobolev completion, and the output is in a finite sum of actual original grades.

**Theorem 1.9 (heatTruncation range).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heatTruncation_range`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heatTruncation_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original k,t,N, the range of heatTruncation is contained in cutoffSpace and is finite dimensional. Each projection has range in its actual completed grade, Finset.le_sup embeds it into the finite sum and Submodule.sum_mem recombines the output. Mathlib finiteDimensional_of_le proves the finite rank.

**Theorem 1.10 (heat tail bound).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_tail_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all k, nonnegative t and natural N, the operator-norm difference between heat and heatTruncation is at most exp(-t*(N+1)). On the dense finite core the tail coefficient is zero inside the cutoff and exp(-tE) outside. stateEnergies_nonneg and integrality give E>=N+1 for each surviving term. Exponential monotonicity and finite_multiplier_bound give the exact original norm estimate. A closed inequality set and completion density extend it to arbitrary inputs before taking operator norm.

The private cutoff_strong proves convergence of these nonnegative cutoffs without a false cofinality argument. Approximate an arbitrary completed vector by embed k v, choose the maximum of E.toNat over stateEnergies v, and use actual nonnegativity to put that finite support in every later cutoff. OriginalSobolev.truncation_embed_of_subset fixes the approximating core vector, while truncation_norm bounds the two approximation errors. This also explains why negative-grade vanishing is essential.

**Theorem 1.11 (heat compact).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_compact`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At t>0 the tail bound tends to zero by the geometric sequence with ratio exp(-t)<1, giving operator-norm convergence of the specific original heatTruncation sequence. CodRestrict into each finite-dimensional actual range proves those maps compact using Mathlib locally compact finite-dimensional spaces. The existing isCompactOperator_of_tendsto proves compactness of heat. Its generic norm-limit compactness proof is reused, not copied.

**Theorem 1.12 (original heat).**

Lean statement: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.original_heat`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Analysis/OriginalHeat.original_heat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual original core bridge carries the whole-space consequences of the existing semigroup: heat at zero is identity; heat(s+t)=heat(s) composed with heat(t); every vector norm and every operator norm are contractive; every nonnegative-time orbit is continuous; every heat operator is positive. It also records actual negative projections zero, strong nonnegative cutoff convergence and the unshifted vacuum fixed at every time. The vacuum proof uses original grade_zero and heat_completedGrade. Zero-time smoothing and zero-time compactness are not asserted.

Attribution: DiagonalHeat remains the unique generic heat implementation. Its selected Scott Armstrong/MarkovProcess semigroup material is Apache 2.0 at dbade0d12c4f84179441a9df7d7147df7a8bcaa0. Its EigenbasisClosure supplier retains PhysLean attribution and its existing trace imports retain their licensing; those imports imply no original-model thermal trace claim here. Original lattice energy, Hm full-frame and Mathlib source attributions remain. No Hamiltonian self-adjointness/domain result, trace class, thermal trace, maximal field adjoint, strong locality or complex holomorphy is used or concluded.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.cutoffSpace`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.energyCutoff`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heatTruncation`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heatTruncation_range`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_compact`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_completedGrade`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_embed`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_projection`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.heat_tail_bound`
- Truth anchor: `D5/S3/VertexAlgebra/Analysis/OriginalHeat.original_heat`
- Dependency: [D5/S3/Quantum/Analysis/DiagonalHeat](../../Quantum/Analysis/DiagonalHeat.md)
- Dependency: [D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis](OriginalEnergyBasis.md)
