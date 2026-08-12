# Exponential Bound for Repeated Failure Factors

## Abstract

A repeated failure factor is at most its exponential envelope on the probability interval.

**Theorem 1.1 (A repeated failure factor has an exponential envelope).**

$$\begin{gathered}\forall \varepsilon \in \mathbb{R}, \forall m \in \mathbb{N},\\(0\le \varepsilon \land \varepsilon \le 1) \Rightarrow \\(1-\varepsilon)^{m} \le \exp (-\varepsilon m).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/IndependentSamplingExponentialBound.independent_sampling_exponential_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a probability threshold epsilon and a natural sample count m, the m-fold factor (1-epsilon)^m is no larger than exp(-epsilon m). The two displayed assumptions record exactly that epsilon lies in the closed probability interval.

Pinned Mathlib was searched first for one-subtraction exponential bounds and natural powers of the real exponential. The exact library results Real.one_sub_le_exp_neg and Real.exp_nat_mul were found. The proof is a thin wrapper: it raises the first inequality to m using nonnegativity of 1-epsilon, then rewrites the resulting power with the second result.

This is an honest partial closure of only the second inequality in the recovery clause of the source theorem. It does not formalize the preceding probability inequality, independent-sampling semantics, the distribution-match caveat, the co-selection collapse clause, or the final phase-change interpretation. Those source subitems remain unresolved.

The nonnegativity assumption on epsilon records the source probability domain, although the elementary upper estimate itself only needs epsilon at most one. No event space, random variable, or probability law is introduced by this analytic partial closure.

## References

- Truth anchor: `D5/S3/TotalVariation/IndependentSamplingExponentialBound.independent_sampling_exponential_bound`
