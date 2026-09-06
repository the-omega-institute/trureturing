# Sequential sparsification inside a product family

## Abstract

A first compression preserves all joint moments with the right law fixed. A second compression uses the new left law and preserves the same moment vector. Both endpoints remain products of normalized rational component laws.

**Theorem 1.1 (Exact fixed-right linear slice).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.product_linearObjective_eq_left`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.product_linearObjective_eq_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite sum expansion treats any rational joint coefficient, including signed moments, as a linear objective in the left law.

**Theorem 1.2 (Exact fixed-left linear slice).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.product_linearObjective_eq_right`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.product_linearObjective_eq_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The symmetric sum identity supplies the second compression after the first component has been replaced.

**Theorem 1.3 (Preserve joint moments with sparse independent factors).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.productLaw_moment_sparse_replacements`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.productLaw_moment_sparse_replacements` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d nominated joint moments, each factor can be replaced by a law with at most d+1 nonzero masses. The second feature map is recomputed using the compressed first law. Global convexity is unnecessary.

**Theorem 1.4 (Preserve all data rows and the target in the product family).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.product_linear_problem_sparse_witness`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.product_linear_problem_sparse_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keeping m rational constraint values and one objective value gives at most m+2 support points per factor. The original linear feasibility predicate and objective remain unchanged, while the product restriction is retained explicitly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.productLaw_moment_sparse_replacements`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.product_linearObjective_eq_left`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.product_linearObjective_eq_right`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/ProductLawMomentSparsification.product_linear_problem_sparse_witness`
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/ReducedResponseTableMoments](ReducedResponseTableMoments.md)
