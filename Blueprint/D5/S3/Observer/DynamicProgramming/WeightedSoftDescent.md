# Weighted Soft Dynamic-Programming Descent

## Abstract

Weighted fiber comparison controls both soft recurrences at every finite horizon.

**Theorem 1.1 (Positive weighted exponential partition).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.partition_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.partition_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative finite row with one positive entry has a strictly positive partition for every real input. The exponential is always positive. This helper is consumed by row_nonexp, one_step and full_certificate.

**Theorem 1.2 (Exponential comparison becomes additive error).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.log_sandwich`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.log_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both multiplicative exponential bounds and positive logarithm arguments imply the absolute soft-value bound, using monotonicity of log and positive tau. It is consumed by row_nonexp and one_step.

**Theorem 1.3 (Row comparison survives positive summation).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.partition_compare`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.partition_compare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two coefficient bounds hold at every index, including zero coefficients. Multiplication by the same positive input exponential and finite summation give both partition bounds. This is consumed by one_step.

**Theorem 1.4 (A soft row preserves a uniform coordinate bound).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.row_nonexp`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.row_nonexp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pointwise absolute input bound passes through the same weighted row without requiring its mass to be one. The proof uses the exponential sandwich and log_sandwich. It is consumed by soft_nonexp and the live horizon induction in value_bound.

**Theorem 1.5 (Nonexpansion in the finite function norm).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.soft_nonexp`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.soft_nonexp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row estimate yields nonexpansion in the finite function supremum norm. Empty index types remain in scope. The coarse and microscopic nonexpansion clauses of full_certificate use this theorem.

**Theorem 1.6 (The actual microscopic log argument).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.micro_argument`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.micro_argument` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splitting exp(-(c+v)/tau) gives exactly R times exp(-c/tau) times exp(-v/tau), with no assumption on the sign of c. This identity is consumed by micro_eq_soft and full_certificate.

**Theorem 1.7 (Microscopic Bellman update as a weighted soft update).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.micro_eq_soft`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.micro_eq_soft` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The microscopic operation is the soft operation with weight R(x,y) exp(-c(x,y)/tau). No normalization is introduced. This equality is used in one_step, value_bound and full_certificate.

**Theorem 1.8 (Stochastic microscopic rows yield positive weighted rows).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.weight_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.weight_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Stochasticity and nonnegativity imply that each indexed microscopic row has a positive entry; multiplying by a positive exponential preserves it. Zero transitions contribute zero regardless of the cost assigned there. The row facts are consumed by one_step, value_bound and full_certificate.

**Theorem 1.9 (Regrouping along the same quotient map).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.fiber_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.fiber_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted microscopic partition of a pulled-back coarse input is exactly the partition of the same-q weighted fiber kernel. The proof regroups the finite sum; one_step consumes the identity.

**Theorem 1.10 (Zero fiber weight means every fiber transition vanishes).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.kernel_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.kernel_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fiber sum is zero exactly when all microscopic transition weights on that fiber vanish. The positive cost exponential does not alter zero support. full_certificate uses both directions.

**Theorem 1.11 (The same coarse matrix has exactly the fiber support).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.support_match`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.support_match` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower and upper exponential comparisons, together with nonnegativity, force the weighted fiber kernel and K at q(x),j to vanish together. This includes zero entries rather than restricting to positive support. full_certificate consumes the result.

**Theorem 1.12 (The actual one-step microscopic and coarse comparison).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.one_step`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.one_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real coarse input, regrouping along q and the supplied coefficient sandwich bound the actual microscopic update against the same unnormalized K update by delta. This feeds the arbitrary-horizon induction and the full certificate.

**Theorem 1.13 (Linear accumulated error at every remaining horizon).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.value_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.value_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof constructs the live invariant for every natural n and every microscopic state: the absolute error of the two actual recurrences is at most n times delta. The base case uses identical terminal data. The arbitrary successor uses its induction hypothesis through row_nonexp, then one_step and the triangle inequality. This is the substantive all-horizon estimate, consumed by original194; a generic induction principle is not an existing error theorem.

**Theorem 1.14 (Backward-time horizon estimate).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.original194`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.original194` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same surjective q, every real terminal g, every finite horizon H and t at most H, value_bound at n=H-t gives the norm bound (H-t) times delta. The underlying estimate is stronger and does not need surjectivity, but the original quantified hypothesis is retained. full_certificate consumes this theorem.

**Theorem 1.15 (Complete weighted soft-descent certificate).**

Lean statement: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.full_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.full_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate derives positive actual log arguments, both zero-support equivalences, microscopic and coarse nonexpansion, and the one-step estimate for every real coarse input. It also gives both terminal equalities, both actual backward recurrences for t<H and the full norm bound for every g,H,t with t<=H. R is nonnegative and stochastic, costs are arbitrary real numbers, tau is positive, delta is nonnegative, and K is the same nonnegative row-positive matrix without normalization. Finite X and Y may be empty. The cases H=0, t=H, delta=0, negative costs and zero coefficients are preserved. This is a mathematical implication under the displayed assumptions; it asserts no empirical realization, resource bound or literature novelty.

## References

- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.fiber_partition`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.full_certificate`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.kernel_zero_iff`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.log_sandwich`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.micro_argument`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.micro_eq_soft`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.one_step`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.original194`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.partition_compare`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.partition_pos`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.row_nonexp`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.soft_nonexp`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.support_match`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.value_bound`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/WeightedSoftDescent.weight_rows`
