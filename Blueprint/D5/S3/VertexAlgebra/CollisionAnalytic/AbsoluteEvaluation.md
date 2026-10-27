# Absolute evaluation of ordered collision expansions

## Abstract

Absolute numerical evaluation of finite collision-localized Laurent expressions in each ordered radial chamber.

Let P be a finite labelled Laurent polynomial over the complex numbers, and let each pair of distinct labels have its own nonnegative integer pole order. For a permutation sigma, take nonzero complex coordinates whose norms strictly decrease in the sigma order. The coefficients are those of the existing complete ordered Hahn expansion of P divided by the product of the fixed-label collision differences raised to these orders.

**Theorem 1.1 (Formal coefficient fibers and absolute numerical regrouping).**

Lean statement: `D5/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation.monomial_family`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation.monomial_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

A formally summable family of Hahn monomials has finite nonzero coefficient fibers. If the numerical monomials form an absolutely summable family, each formal coefficient times its numerical Laurent weight equals the topological sum over the corresponding exponent fiber. Grouping an absolutely summable family by this map preserves its sum, and the triangle inequality bounds the grouped absolute sum by the ungrouped absolute sum.

**Theorem 1.2 (All integer coefficients evaluate to the Laurent quotient).**

Lean statement: `D5/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation.collision_absolute_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation.collision_absolute_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The sum ranges over all labelled integer exponent vectors. It is absolutely summable and has value P(z) divided by the collision denominator, which is nonzero on the chamber. Its absolute sum is at most the finite absolute Laurent numerator value multiplied by the inverse pole powers of the radial gaps abs(norm(z_i)-norm(z_j)). These are radial gaps, not complex collision distances. Zero pole orders contribute one; negative numerator exponents require the stated nonzero coordinates. Reversing the order of a fixed-label difference retains its minus sign before taking its pole power.

The argument reuses mathlib formal Hahn sums and their finite antidiagonal multiplication, together with complex geometric-series convergence and absolute product sums. Finite powers of the geometric inverse supply every pole order, so no additional one-variable binomial convergence theorem is needed. Hahn series and their summable families are by Aaron Anderson; the numerical infinite-sum machinery includes work by Anatole Dedecker and the mathlib contributors, under Apache 2.0. Matsuo--Nagatomo is local-field background and does not supply this Lean evaluation theorem. No claim of literature novelty is made.

The chamber is nonempty: assign the coordinate with sigma position i the positive integer n-i. Collision avoidance alone is insufficient for a chosen ordered series. No evaluation homomorphism on the entire fraction field is asserted. Homogeneous matrix-coefficient slices may be evaluated by this result when their coefficients equal the displayed ordered expansion. Convergence of an infinite sum over all homogeneous slices requires a further finite-energy or growth argument.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation.collision_absolute_evaluation`
- Truth anchor: `D5/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation.monomial_family`
- Dependency: [D5/S3/VertexAlgebra/CollisionRationalExpansions](../CollisionRationalExpansions.md)
