# Optimal overlaps and finite Loewner slopes

## Abstract

Actual optimal PSD overlaps give a finite Loewner-secant criterion, necessary for original-L1 equality and sufficient for every finite interpolation problem.

Let n be any finite type, including the empty type, and let A,B be arbitrary positive semidefinite complex n by n matrices. There is no trace normalization or invertibility assumption. O(t) is the supremum of Re Tr(X) over 0<=X<=A and X<=tB. A private uniqueness argument concerns these constrained PSD trace maximizers, rather than the unconstrained Hermitian lower-bound problem. It uses the existing subunital quadratic Jensen theorem: the square of half the difference of two maximizers can be added to their midpoint after positive scaling. Optimality forces its trace to vanish, so the two matrices coincide. Finite-dimensional compactness then turns convergence of feasible traces into convergence to this unique optimum.

**Definition 1.1 (The actual matrix optimum).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.optimalOverlap`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.optimalOverlap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For t>=0, optimalOverlap A B hA hB t chooses an attained maximum from positiveOverlaps A (t B); for negative t its value is zero and is unused. The optimizer is uniquely determined by the PSD constrained problem. It is not a postulated profile or a chosen reverse-test optimizer.

**Theorem 1.2 (Feasibility and optimal trace).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.optimalOverlap_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.optimalOverlap_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

At every nonnegative t the chosen matrix lies between zero and each of A,tB, and its real trace is overlapValue A (tB). These facts supply the matrix endpoints of every interpolation tuple.

**Theorem 1.3 (The virtual initial knot).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.optimalOverlap_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.optimalOverlap_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

The actual optimum at zero is zero, also for singular pairs and empty matrix dimension. Zero is used as an initial interpolation knot; curvature is a measure on the strictly positive threshold space and has no zero or infinity point.

**Definition 1.4 (Matrix secants).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.secant`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.secant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For a matrix function X, secant X s t is (t-s)^(-1) times (X(t)-X(s)). Each ordered pair of distinct tuple knots therefore defines an actual matrix, compared in Loewner order.

**Definition 1.5 (The exact arbitrary-support condition).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.FiniteLoewnerSlopes`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.FiniteLoewnerSlopes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For every natural m and every strictly increasing tuple t:Fin(m+1)->R with t(0)=0 and every positive node belonging to K, form D_i=(X(t_(i+1))-X(t_i))/(t_(i+1)-t_i), where X is optimalOverlap. Require 0<=D_i<=B for every i and Antitone D. These are matrix inequalities, not inequalities of traces. The tuple with m=0 is included. K may be empty, finite, disconnected or unbounded; the classifier uses the actual Stieltjes support of the generator.

**Theorem 1.6 (Trace of an actual prepared overlap).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.trace_prepared`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.trace_prepared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For every actual finite ReverseTest R and every real t, Re Tr(R.preparedOverlap t) is the sum of min(R.p_i,t R.q_i). The component trace identities give this formula, which expresses the tail hinge profiles in terms of prepared overlaps.

**Theorem 1.7 (The actual gap is an overlap deficit).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.gap_eq_overlap_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.gap_eq_overlap_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

At each positive threshold, gap R t equals O(t)-Re Tr(R.preparedOverlap t). Both original equality necessity and the dominated-convergence sufficiency proof consume this identity.

**Theorem 1.8 (Bounds for prepared slopes).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.prepared_secant_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.prepared_secant_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For any finite actual reverse test and s<t, its prepared-overlap secant is PSD and bounded above by B. The scalar min(p,tq) secants lie in [0,q], and the same density states prepare B. No optimum or full-support assumption is needed.

**Theorem 1.9 (Ordered prepared secants).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.prepared_secant_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.prepared_secant_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For r<s<=t<v, the prepared secant over [t,v] is bounded above in Loewner order by the secant over [r,s]. This follows from the scalar concavity of min(p,tq), with the common actual preparation retained.

**Theorem 1.10 (From vanishing gap to the actual optimum).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.prepared_overlap_tendsto_of_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.prepared_overlap_tendsto_of_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For any sequence of actual finite tests with gap tending to zero at a fixed positive t, their prepared overlap matrices converge to optimalOverlap(t). Compactness is only in the finite-dimensional feasible matrix set. Uniqueness identifies every limiting optimizer; no test attaining the general convex infimum is assumed.

**Theorem 1.11 (Necessity for the original whole-complex-L1 values).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.original_eq_implies_finiteLoewnerSlopes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.original_eq_implies_finiteLoewnerSlopes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For any real f convex on Ioi 0 and any real c with originalL1Value hf A B=c, equality originalL1Value=originalHockeyValue implies FiniteLoewnerSlopes on the actual curvature support. The source universe u is arbitrary and independent of the matrix universe. originalL1Value ranges over all sigma-finite sources and positive complex-linear TP maps defined on their entire complex L1 spaces. The original operational hockey infima are identified by the previously proved source bridges. Finite-cost near-minimizers have nonnegative uniformly Lipschitz gaps whose curvature integrals tend to zero. The analytic support transfer gives pointwise vanishing at each actual support knot; optimizer convergence and closed Loewner order pass the finite prepared-slope conditions to the actual optimal-overlap slopes. Full curvature support, normalization, faithfulness and a nonempty output type are unnecessary.

**Theorem 1.12 (Positive hockey as trace minus overlap).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.hockey_eq_trace_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.hockey_eq_trace_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

For each actual finite test and real threshold, its positive hockey sum equals Tr(A)-Re Tr(preparedOverlap). This gives the positive branch of the test kernel used in the dominated-convergence argument. A general closed-perspective cost is represented by a curvature integral of test kernels.

**Theorem 1.13 (Finite interpolation by explicit PSD blocks).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.finite_test_interpolating_slopes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.finite_test_interpolating_slopes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

Given a finite strictly increasing tuple starting at zero, actual optimal feasible matrices X_j with X_0=0, and an antitone extended slope tuple d ending at zero with d_0<=B and (t_(i+1)-t_i)d_i=X_(i+1)-X_i, the proof constructs an actual finite ReverseTest with preparedOverlap(t_j)=X_j for every j. Its PSD blocks are the slope differences d_i-d_(i+1), the lower residual B-d_0 and the upper residual A-X_last. Summation by parts proves both original matrix marginals and every interpolation identity. Empty output dimension uses the empty alphabet, and zero blocks use the existing weighted-component convention.

**Theorem 1.14 (Every compatible finite tuple is realizable).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.finiteLoewnerSlopes_realizes_knots`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.finiteLoewnerSlopes_realizes_knots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Acknowledgement.* Keiji Matsumoto (2018). *A New Quantum Version of f-Divergence*. DOI: [10.1007/978-981-13-2487-1_10](https://doi.org/10.1007/978-981-13-2487-1_10). URL: <https://arxiv.org/abs/1311.4722v4>.

*Commentary.*

FiniteLoewnerSlopes A B hA hB K supplies an actual finite test interpolating optimalOverlap at every knot of any specified tuple in K with virtual initial zero. Appending a final zero slope supplies the preceding block construction. The alphabet may depend on the tuple. This gives neither a uniform alphabet size nor one finite test simultaneously optimal on an infinite support.

Attribution: Hiai, Mosonyi and Tomamichel, arXiv:2607.08760v1, Proposition V.1, supply the actual positive-overlap hockey formulas and one-threshold three-component construction. Their final equality question motivates this extension. Matsumoto, arXiv:1311.4722v4, p. 8, Lemma 4.1, already supplies one-cost finite-source compression. The previous source-class equivalence and original-L1 operational profile identification are reused at their exact scopes. The finite interpolation and arbitrary-support classification are repository derivations; worldwide novelty remains unverified.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.FiniteLoewnerSlopes`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.finiteLoewnerSlopes_realizes_knots`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.finite_test_interpolating_slopes`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.gap_eq_overlap_trace`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.hockey_eq_trace_sub`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.optimalOverlap`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.optimalOverlap_spec`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.optimalOverlap_zero`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.original_eq_implies_finiteLoewnerSlopes`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.prepared_overlap_tendsto_of_gap`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.prepared_secant_antitone`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.prepared_secant_bounds`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.secant`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes.trace_prepared`
- Dependency: [D5/S3/Analytic/Measure/FullSupportProfileTransfer](../../Analytic/Measure/FullSupportProfileTransfer.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickAllL1Convex](MaximalHockeyStickAllL1Convex.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickComponents](MaximalHockeyStickComponents.md)
