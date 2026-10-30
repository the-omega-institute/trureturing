# Compact normal convergence in a radial chamber

## Abstract

Compact normal convergence of the original labelled integer Hahn collision coefficients on strict radial chambers.

**Theorem 1.1 (One summable coefficientwise majorant on each compact).**

Lean statement: `D5/S3/VertexAlgebra/CollisionAnalytic/NormalConvergence.chamber_compact_summable_majorant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionAnalytic/NormalConvergence.chamber_compact_summable_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Fix any number n of labels, a permutation sigma, and an arbitrary complex coefficient family indexed by Fin n to the integers. Assume its Laurent monomial terms are absolutely summable at every nonzero point with strictly decreasing norms in sigma order. Every compact subset K of that chamber has one nonnegative summable real family u(e) bounding the norm of each original coefficient times its monomial at every point of K.

Around each point choose a box of positive radii whose every corner remains in the ordered-radius domain. For each exponent, select the upper endpoint for a nonnegative exponent and the lower endpoint for a negative exponent. The resulting monomial norm bounds the term throughout the annular box. Summing over all finitely many corners gives a nonnegative summable coefficientwise bound, since pointwise absolute summability holds at each corner. A finite compact subcover and finite sum of these bounds give u. No interchange of a supremum and an infinite sum is assumed.

**Theorem 1.2 (The native collision series converges normally to its exact quotient).**

Lean statement: `D5/S3/VertexAlgebra/CollisionAnalytic/NormalConvergence.collision_normal_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionAnalytic/NormalConvergence.collision_normal_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

For an arbitrary finite labelled Laurent numerator L and arbitrary natural pair pole orders m, take literally the frozen orderedRationalFor Hahn coefficients at orderExponents n sigma e. On every compact K in the chamber, the continuous term maps T(e) in C(K, complex) have summable supremum norms and HasSum T F, where F is the restriction of laurentValue L divided by the original product of labelled collision differences to their pole orders. The finite-subset net converges uniformly on K to that exact quotient.

The compact majorant is consumed with collision_absolute_evaluation as its pointwise hypothesis. Continuous signed powers give the term maps; the continuous-map norm comparison gives norm summability. Evaluation of the Banach sum and uniqueness of the frozen pointwise HasSum identify its value. Mathlib's M-test gives uniform convergence. These packaging steps are reuse; the finite annular-vertex and compact-cover majorant is the analytic increment.

All signed exponents and fixed labels are retained. The result includes n=0, empty compact sets, zero pole orders, and arbitrary negative powers in the finite numerator. It assumes pointwise strict radial order on K, never global separation between the largest inner radius and smallest outer radius over different points. For example, (2,1) and (200,100) lie in the same two-label chamber while such global separation fails.

Applied on every compact, the uniform conclusion and the openness of the strict radial chamber yield local uniform convergence through mathlib's hasSumLocallyUniformlyOn_of_forall_compact. No separate rationality or holomorphy adapter is retained. An actual matrix coefficient is covered when its original modes and functional have an established genuine finite Laurent numerator and equality with these Hahn coefficients. No all-n lattice numerator is assumed here; the frozen lattice scalar numerator supplier has its stated two-field scope.

This is scalar chamber normal convergence in the correlation and sewing program. It does not prove operator-valued convergence, energy-uniform bounds, a joint occupation and mode rearrangement, analytic sewing equality, or full VOA/CFT, Moonshine, string or AdS completion. A joint sewing-parameter and occupation majorant remains a further obligation. The fixed-offset canonical sewing summability theorem alone does not supply it.

The compactness, signed-power inequalities, infinite sums and continuous-map norm machinery are reused from mathlib under Apache 2.0. The M-test interfaces are by Chris Birkbeck and mathlib contributors. Matsuo--Nagatomo supplies local-field background, not this compact-majorant proof. No literature novelty is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CollisionAnalytic/NormalConvergence.chamber_compact_summable_majorant`
- Truth anchor: `D5/S3/VertexAlgebra/CollisionAnalytic/NormalConvergence.collision_normal_evaluation`
- Dependency: [D5/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation](AbsoluteEvaluation.md)
