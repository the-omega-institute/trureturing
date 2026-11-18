# Support-local and full-support integral transfer

## Abstract

Vanishing integrals of uniformly Lipschitz nonnegative profiles force convergence on the actual measure support; full support and a global bound also give transfer to every finite measure.

**Theorem 1.1 (Pointwise convergence on the actual measure support).**

Lean statement: `D5/S3/Analytic/Measure/FullSupportProfileTransfer.tendsto_zero_at_support_of_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Measure/FullSupportProfileTransfer.tendsto_zero_at_support_of_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On any pseudo-metric space with measurable open sets, let mu be locally finite and let real profiles g_j be nonnegative, mu-integrable and uniformly K-Lipschitz, with K>=0. If their integrals tend to zero, then g_j(x) tends to zero for every x in mu.support. A nonvanishing value and the common Lipschitz bound force a positive lower integral on a finite open neighbourhood of a support point. No global bound, full-support hypothesis or second measure is required. The full-support theorem below follows by taking the support to be the entire space. Applied to actual reverse-test gaps, the support conclusion gives the knotwise convergence in MaximalHockeyStickLoewnerSlopes.original_eq_implies_finiteLoewnerSlopes. The converse approximation uses mathlib's EquicontinuousAt.tendsto_of_mem_closure to extend convergence from dense knots to their closure.

**Theorem 1.2 (Pointwise and finite-measure convergence).**

Lean statement: `D5/S3/Analytic/Measure/FullSupportProfileTransfer.tendsto_zero_of_full_support_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Measure/FullSupportProfileTransfer.tendsto_zero_of_full_support_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a pseudo-metric space with measurable open sets, let mu be locally finite and positive on every nonempty open set. Let continuous real g_j be nonnegative, uniformly bounded by a fixed M>=0 and Lipschitz with the same K>=0. Assume every g_j is mu-integrable and its mu-integral tends to zero. Then g_j(x) tends to zero at every x, and its integral against any measure nu of finite total mass tends to zero. A nonvanishing point and the uniform Lipschitz constant force a fixed positive lower integral on a finite open neighbourhood, contradicting the hypothesis. The second conclusion follows by dominated convergence. No compactness, optimizer, probability normalization or finiteness of mu is assumed. MaximalHockeyStickApproximate.actual_tests_full_support_transfer consumes the theorem with actual reverse-test gaps. This is a repository analytic supplier, rather than a claim of new literature priority.

## References

- Truth anchor: `D5/S3/Analytic/Measure/FullSupportProfileTransfer.tendsto_zero_at_support_of_integral`
- Truth anchor: `D5/S3/Analytic/Measure/FullSupportProfileTransfer.tendsto_zero_of_full_support_integral`
