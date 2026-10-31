# General cost probability transport

## Abstract

General cost probability transport

**Theorem 1.1 (Finite equality and attained maximum).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/FiniteCostKR.finite_kr_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/FiniteCostKR.finite_kr_attained` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

Let I be any finite type, a and b nonnegative real weights of total mass one, and c a nonnegative symmetric triangular self-zero cost. There exist an actual nonnegative matrix P with exactly these row and column sums and a real potential f with absolute oscillation bounded by c. The matrix cost equals the signed weighted potential difference; it is no larger than the cost of any other feasible matrix, and the potential difference is no smaller than that of any other admissible potential. Zero coordinates are allowed, and the empty-type contradiction follows from mass one. The frozen finite strong-duality theorem supplies unrestricted u and v and the actual optimal matrix; the finite c-transform is the maximum of u(a)-c(x,a), rather than an unsupported substitution v=-u. Finite marginal identities prove the weak comparison and force equality.

**Theorem 1.2 (General cost Kantorovich Rubinstein inequality).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/FiniteCostKR.wassersteinCostCoupling_le_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/FiniteCostKR.wassersteinCostCoupling_le_dual` (`✓ std3`). ∎

*Citation.* Joseph K. Miller (2026). *General-cost optimal transport in the Vlasov formalization*. URL: <https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714/LeanPool/Vlasov/OT>.

*Commentary.*

For every second-countable Borel standard-Borel pseudometric space, every continuous nonnegative self-zero symmetric triangular cost c bounded above by distance, any probability measures mu and nu, and any explicit basepoint x0 with integrable c(.,x0) for both measures, the ENNReal infimum over all actual coupling measures of the lower integral of ofReal(c) is at most the supremum over all real functions f with absolute oscillation bounded by c of ofReal(integral f mu minus integral f nu). Finite-range pushforwards are decomposed into their actual atom masses; an attained finite LP matrix produces a sum of weighted Dirac measures with exact marginals and exactly the matrix cost. A finite c-transform supplies a globally admissible single potential. Cost approximation, actual coupling gluing, and dual map stability then give the inequality by an epsilon limit. Degenerate and truncated costs are included. No compactness, finite support, distance moment, strict separation, general optimizer, or general-cost equality is required or asserted.

## References

- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/FiniteCostKR.finite_kr_attained`
- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/FiniteCostKR.wassersteinCostCoupling_le_dual`
- Dependency: [D5/S3/Analytic/Convexity/FiniteStrongDuality](../../Analytic/Convexity/FiniteStrongDuality.md)
- Dependency: [D5/S3/Geometry/ProbabilityTransport/CostCoupling](CostCoupling.md)
