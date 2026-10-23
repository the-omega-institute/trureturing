# Inverse-Power Tails from Raw Weighted Counts

## Abstract

Classical partial summation converts raw finite weighted power counts into convergence and an explicit inclusive inverse-power tail.

**Theorem 1.1 (Raw counting implies a convergent inclusive tail).**

Lean statement: `D5/S3/Weil/ZetaTail/PowerCountTail.inverse_power_tail_of_raw_count`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaTail/PowerCountTail.inverse_power_tail_of_raw_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index type is arbitrary. Ordinates g and real nonnegative masses m need neither countability nor local finiteness. Assume Y>0, C>=0, p>0 and a<p. For every real u>=Y and every finite set s whose ordinates satisfy g(i)<u, the total mass is at most C*u^a. Then the series with terms m(i)*g(i)^(-p) for g(i)>=Y and zero otherwise is summable, and its sum is at most (p*C/(p-a))*Y^(a-p). The tail includes its cutoff ordinate, whereas the count is strict.

For each finite subset of the inclusive tail, integrate the indicator of g(i)<u against p*m(i)*u^(-p-1) over u>Y. The intersection of the two open rays is u>g(i), even when g(i)=Y, so each atom has its full mass. The raw count bounds the finite kernel sum by p*C*u^(a-p-1). Mathlib's improper real-power integral evaluates both the individual moments and the majorant. Uniform bounds for all finite subsets then give summability and the same bound for the total sum. Neither convergence nor a tail estimate occurs among the hypotheses.

This is a repository inference by classical partial summation, without a novelty claim. The existing logarithmic count proof in LogarithmicPhaseStiffness covers the special square and cube tails; its theorem-local helper does not supply this general weighted power-density estimate. Unit-window and actual fourth-moment estimates likewise have different hypotheses and scope.

Applying this theorem to a selected family of zeta zeros requires proving the stated raw weighted density bound for that same family. No Ingham or Guth-Maynard density input, weak-psi formula, favorable signed comparison, or RH conclusion is supplied here. The parent RH and unrestricted Robin goals remain unproved.

## References

- Truth anchor: `D5/S3/Weil/ZetaTail/PowerCountTail.inverse_power_tail_of_raw_count`
