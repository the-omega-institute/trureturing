---
bibkey: mathlib2026absoluteintegralsum
authors: The mathlib Community
year: 2026
title: Integral and countable sum under summable integral norms
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean
claim: The existing integral-sum theorem requires summability of the integrals of norms; summability of the norms of the integrals is not a substitute for that premise.
strata_touched: []
license: Citation only; the cited mathlib source is Apache-2.0.
triage: anchor
---

# Absolute convergence before exchanging the integral and the series

The inspected source is the repository's pinned mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`, with input tag `v4.33.0`.
The file `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` has
SHA256 `18b709ea5c9ef9136e3e75ded82a6135641e6e19688e0ca3abcb0af45648ab84`.
This note records the source declaration and its premises; it does not
claim a new compilation of the FIB application.

The existing declarations
`MeasureTheory.hasSum_integral_of_summable_integral_norm` and
`MeasureTheory.integral_tsum_of_summable_integral_norm`, source lines
96–114, apply to a countable family of integrable functions $F_i$ when

$$
\sum_i\int\|F_i(t)\|\,d\mu(t)<\infty.
$$

They then identify the integral of the pointwise series with the series
of integrals. This is the classical absolute-convergence form of
integral-sum interchange. The theorem is reused, not reproved or
retained as a new wrapper.

For the [FIB volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
§397, the functions are the same-source responses

$$
F_m(t)=H_m[R(t/m)-R(t/(m+1))]w(t)
$$

on the measure restricted to $t\ge x>1$. The individual integrability
and the summable integral norm must be verified for these actual
functions. In particular, the integrated variation bound for
$|J_x(m)|=|\int[R(t/m)-R(t/(m+1))]w(t)dt|$ is not by itself the required
bound on $\int|R(t/m)-R(t/(m+1))|w(t)dt$.

The actual jump intervals of $K$ and the low-quotient continuous term
of $R$ pay the missing premises in the manuscript's §397 argument.
The theorem's hypotheses are distinguished from that paper
application; no complete Lean verification of the latter, critical
growth estimate for $H$, or Robin/RH conclusion is asserted here.
