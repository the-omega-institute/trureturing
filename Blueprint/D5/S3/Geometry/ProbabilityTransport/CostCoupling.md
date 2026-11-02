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

**Theorem 1.7 (Finite equality and attained maximum).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.finite_kr_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/CostCoupling.finite_kr_attained` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

Let I be any finite type, a and b nonnegative real weights of total mass one, and c a nonnegative symmetric triangular self-zero cost. There exist an actual nonnegative matrix P with exactly these row and column sums and a real potential f with absolute oscillation bounded by c. The matrix cost equals the signed weighted potential difference; it is no larger than the cost of any other feasible matrix, and the potential difference is no smaller than that of any other admissible potential. Zero coordinates are allowed, and the empty-type contradiction follows from mass one. The frozen finite strong-duality theorem supplies unrestricted u and v and the actual optimal matrix; the finite c-transform is the maximum of u(a)-c(x,a), rather than an unsupported substitution v=-u. Finite marginal identities prove the weak comparison and force equality.

**Theorem 1.8 (General cost Kantorovich Rubinstein inequality).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_le_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_le_dual` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

For every second-countable Borel standard-Borel pseudometric space, every continuous nonnegative self-zero symmetric triangular cost c bounded above by distance, any probability measures mu and nu, and any explicit basepoint x0 with integrable c(.,x0) for both measures, the ENNReal infimum over all actual coupling measures of the lower integral of ofReal(c) is at most the supremum over all real functions f with absolute oscillation bounded by c of ofReal(integral f mu minus integral f nu). Both finite-range pushforwards are decomposed into their actual atom masses on the union of their finite ranges. The attained finite KR theorem supplies its matrix and single potential on this common support. A finite c-transform extends the potential without changing its values there; the weighted Dirac law has exact marginals and lower-integral cost exactly equal to the signed integral objective. Cost approximation, actual coupling gluing, and dual map stability then give the inequality by an epsilon limit. Degenerate and truncated costs are included. No compactness, finite support, distance moment, strict separation, general optimizer, or general-cost equality is required or asserted.

## References

- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.exists_coupling_glue`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.exists_finiteRange_map_cost_le`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.finite_kr_attained`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_comm`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_le_dual`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_map_le`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCostCoupling_triangle`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/CostCoupling.wassersteinCost_dual_le_add_map`
- Dependency: [D5/S3/Analytic/Convexity/FiniteStrongDuality](../../Analytic/Convexity/FiniteStrongDuality.md)
