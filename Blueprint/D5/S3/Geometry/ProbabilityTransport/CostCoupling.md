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

## Application to coupled generators and uniform Poincare bounds

The finite attained KR result also supplies a transport comparison for a sum of Markov generators. Let S be a finite nonempty state set, including the singleton case, let I be any finite clock set, possibly empty, and let G be a connected simple graph on S with shortest-path distance d_G. Write N = |S| and m = |I|. For each i in I, take a real matrix T_i with T_i(x,z) >= 0, sum_z T_i(x,z) = 1 and T_i(x,z) = T_i(z,x) for every x,z in S. Its action is (T_i g)(x) = sum_z T_i(x,z)g(z).

For every oriented adjacent pair x,y and every clock i, assume an actual matrix gamma_{x,y,i}(v,w) >= 0 with row sums sum_w gamma_{x,y,i}(v,w) = T_i(x,v) and column sums sum_v gamma_{x,y,i}(v,w) = T_i(y,w). Set C_i(x,y) = sum_v sum_w gamma_{x,y,i}(v,w)d_G(v,w). Require the summed drift condition sum_i (C_i(x,y)-1) <= -1 on every such oriented edge, equivalently sum_i C_i(x,y) <= m-1. No coupling or drift condition is required away from adjacent pairs.

Define A = sum_i (Id-T_i) and mean(f) = (sum_y f(y))/N. Under these assumptions, every complex function f on S satisfies sum_x |f(x)-mean(f)|^2 <= sum_i sum_x Re(conj(f(x))*(f(x)-sum_z T_i(x,z)f(z))). Dividing both sides by N gives the Poincare inequality for uniform probability measure, with gap at least one on the mean-zero subspace. The generator is the sum over clocks; there is no division by m.

To see the eigenfunction comparison, first take a nonconstant real g satisfying Ag = lambda*g. The finite maximum L = max_{G.Adj(x,y)} |g(x)-g(y)| is attained. Connectedness and nonconstancy imply L > 0. Reversing an attaining edge if necessary gives adjacent a,b with g(a)-g(b) = L. Along a shortest walk from v to w, the triangle inequality and the bound L on each edge give |g(v)-g(w)| <= L*d_G(v,w) for all v,w.

Apply CostTransport.finite_kr_attained with weights p(v) = T_i(a,v), q(w) = T_i(b,w) and cost c(v,w) = L*d_G(v,w). Nonnegativity, symmetry, self-zero and the triangle inequality for this cost follow from L > 0 and the connected graph metric. The global oscillation bound makes g an admissible potential. Dual maximality bounds its signed expectation difference by the optimal matrix cost, and primal minimality bounds that cost by the cost of the supplied gamma_{a,b,i}. Thus (T_i g)(a)-(T_i g)(b) <= L*C_i(a,b), using the actual two marginal laws and their actual coupling.

Subtract the eigenfunction equations at a and b and sum the transport comparisons over i. They give (m-lambda)*L = sum_i ((T_i g)(a)-(T_i g)(b)) <= L*sum_i C_i(a,b) <= L*(m-1). Since L > 0, lambda >= 1. This real nonconstant eigenfunction implication uses the stochastic rows and coupled drift but does not require symmetry of the kernels.

Symmetry enters the passage to a uniform quadratic bound: A is a real Hermitian matrix and has a finite orthonormal eigenbasis. For a real zero-mean vector u, every constant basis direction has zero coefficient, while every nonconstant basis direction has eigenvalue at least one by the preceding comparison. Summing the coefficientwise inequalities with the orthonormal-basis identities sum_sq_inner_right and sum_inner_mul_inner yields sum_x u(x)^2 <= sum_x u(x)(Au)(x). The graph steps use the finite maximum, shortest-walk and distance-sum facts; the spectral steps use Mathlib's real Hermitian eigenbasis and orthonormal-basis identities.

The row sums give A1 = 0. Symmetry also gives column sums one, hence sum_x (Ag)(x) = 0 for every real g. Consequently u = g-mean(g) is zero-mean, Au = Ag, and sum_x u(x)(Au)(x) = sum_x g(x)(Ag)(x): centering preserves the energy. This proves the real Poincare bound. Because all kernels are real, applying it separately to Re(f) and Im(f) and adding gives the displayed complex inequality, since complex squared modulus and the real part of the conjugate energy split into these two real contributions.

If S is a singleton, every function is constant, each stochastic kernel is the identity and both sides vanish, even when I is empty. The gap assertion in that case is only the inequality on the zero mean-zero subspace; it asserts no positive eigenvalue exists. If S has more than one element, connectedness supplies an edge, so I empty would make the drift condition 0 <= -1 and is impossible.

This is an application of the finite KR result attributed above and the existing finite graph and Hermitian spectral facts, without a claim of novelty. Its hypotheses must be verified for any proposed model. In particular, the argument does not identify an indexed interval-block kernel, its count or variance, does not establish a gap for such an actual model before those identifications and the drift bound, and does not supply a physical or Rauzy realization. A nonuniform stationary law requires its own weighted argument; it is not covered by this uniform-measure passage.

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
