# General cost probability transport

## Abstract

General cost probability transport

**Theorem 1.1 (Symmetry of coupling cost).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_comm`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_comm` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

For any measurable symmetric real cost, swapping both coordinates sends every actual coupling to a coupling of the reversed marginals with exactly the same lower-integral cost. This proves equality of the two ENNReal infima without moment or finiteness assumptions.

**Theorem 1.2 (An actual glued coupling with a cost bound).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.exists_coupling_glue`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/CostCoupling.exists_coupling_glue` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

Let alpha be a standard Borel measurable space, mu and rho probability measures, and pi1 and pi2 actual couplings of (mu,rho) and (rho,nu). A measurable real cost satisfying the triangle inequality admits an actual coupling of (mu,nu) whose ENNReal lower integral is bounded by the sum of the two original lower integrals. Disintegrating pi2 over rho and integrating its conditional kernel along the second coordinate of pi1 gives a law on triples; its outer projection has the required exact marginals. No optimizer, finite cost, or probability assumption on nu is added.

**Theorem 1.3 (Triangle inequality for the infimum).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_triangle` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

Under the gluing hypotheses, the coupling infimum for (mu,nu) is at most the sum of those for (mu,rho) and (rho,nu). The proof selects epsilon-optimal actual couplings only when the sum is finite and then applies the glued-law construction; no general attainment is asserted.

**Theorem 1.4 (A graph coupling).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_map_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_map_le` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

The pushforward of mu by x maps to (x,T x) is an actual coupling of mu and the measurable pushforward T of mu. Its cost equals the integrated cost of the map. The continuous-cost hypothesis ensures that the lower-integral change of variables uses the original product sigma-algebra.

**Theorem 1.5 (Dual stability under two measurable maps).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCost_dual_le_add_map`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCost_dual_le_add_map` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

For probability measures on a second-countable Borel pseudometric space, a continuous nonnegative self-zero symmetric cost and an explicit basepoint with finite cost moments bound the dual value of the two pushforwards by the original dual value plus both map errors. The single-map proof derives continuity and integrability of each admissible potential from its oscillation bound and the cost moment.

**Theorem 1.6 (Finite-range approximation from a cost moment).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.exists_finiteRange_map_cost_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/CostCoupling.exists_finiteRange_map_cost_le` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

A continuous nonnegative symmetric triangular self-zero cost dominated by ambient distance defines a pseudometric on a type copy of alpha. The copy retains the original measurable structure. The identity into this cost topology is continuous, so the original sigma-algebra contains its open sets and the cost topology is separable. Native simple-function approximation has finite range, pointwise cost error tending to zero, and error at most the given basepoint cost. ENNReal dominated convergence therefore gives a measurable finite-range map with any prescribed positive cost error. Only the cost moment is used; no equality of Borel structures or ambient-distance moment is asserted.

## References

- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.exists_coupling_glue`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.exists_finiteRange_map_cost_le`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_comm`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_map_le`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_triangle`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCost_dual_le_add_map`
