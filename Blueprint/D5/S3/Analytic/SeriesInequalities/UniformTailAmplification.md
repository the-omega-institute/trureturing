# Uniform Tail Amplification

## Abstract

One common diverging natural multiplier preserves uniform nonnegative series tails and has an arbitrarily small additive mass cost.

**Theorem 1.1 (A common staircase multiplier from uniform tail control).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/UniformTailAmplification.exists_uniform_tail_amplification`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/UniformTailAmplification.exists_uniform_tail_amplification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be any type and a(x,n) an extended nonnegative real sequence for each x in X. Suppose that for every positive nonnegative-real epsilon there is one natural cutoff N such that sum over k>=0 of a(x,N+k)<=epsilon for every x. For every positive nonnegative-real delta there is one natural-valued sequence w, chosen before x, such that w(n)>=1, w is nondecreasing, and w(n) tends to infinity.

For every x, the weighted sum sum over n>=0 of w(n)a(x,n) is at most the original sum plus delta. The weighted tails also vanish uniformly over X: for every positive epsilon there is one cutoff M such that sum over k>=0 of w(M+k)a(x,M+k)<=epsilon for every x. There is no assumption that the original total masses are uniformly bounded. Empty X, zero entries and infinite head terms are included, with all series inequalities interpreted in extended nonnegative reals.

Choose strictly increasing thresholds N(j)>=j+1 for which every original tail is at most b(j)=delta*2^(-(j+1)). Set w(n)=1+card{j<n : N(j)<=n}. The lower bound on N(j) makes this a finite count of every threshold active at n. The weight is nondecreasing, and beyond N(J) its value is at least J+2. Expand the count into threshold indicators and interchange nonnegative sums: the added mass is the sum of the original tails at the selected thresholds, bounded by sum b(j)=delta.

For any M and J, the weighted tail is at most (J+1) times the original tail at M plus sum over k>=0 of b(k+J). First choose J so that the geometric budget tail is at most epsilon/2, then use the original uniform-tail assumption with epsilon/(2*(J+1)). This controls the same weighted tail for every x without a summable pointwise envelope.

If an individual original total is finite, its weighted total is finite. If the original totals have an additional uniform bound B, the weighted totals are bounded by B+delta. The family a(m,0)=m and a(m,n)=0 for n>0 shows why uniform tail control alone does not imply a uniform total-mass bound. The family with a(m,n)=1/(m+1) only at n=m has uniformly small tails, while its pointwise envelope is the nonsummable harmonic sequence, so a common summable envelope cannot be assumed.

The proof reuses Mathlib's monotone cutoff extraction, ENNReal nonnegative double-sum interchange, geometric series and finite series-tail convergence. The new composition is the common weight construction for arbitrary families. No literature novelty or resolution of the common-Hamiltonian entropy conjecture is claimed. A scalar Gibbs application would add a preliminary summable Boltzmann series; a full quantum application additionally requires an actual operator and trace/energy bridge.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/UniformTailAmplification.exists_uniform_tail_amplification`
