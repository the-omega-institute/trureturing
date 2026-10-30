# CDSO actual-array core remainder

## Abstract

Actual incidence arrays and the common-tail producer for CDSO Lemmas 13.4–13.5.

One nonnegative normalized law on every nonempty subset supplies all marginals, cardinalities and energies. For every tied-allowed smallest tail, the private implementation derives nonnegative actual-incidence residuals, their sum Q(L), the actual-core Jensen gap and the exact lower certificate. LocalizationBootstrap imports this implementation on its live proof path; no producer certificate is an input assumption.

**Definition 1.1 (One actual finite incidence array).**

Lean statement: `D5/S3/Combinatorics/CDSO/ArrayCore.JointArray`

*Formalization.* `D5/S3/Combinatorics/CDSO/ArrayCore.JointArray` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

JointArray preserves the original law on all nonempty subsets, normalization, nonnegative masses, positive actual marginals, and the single actual expectation EK=a. No separate marginal vector, support condition, independence premise, certificate, near-minimizer premise, or graph condition is introduced.

**Definition 1.2 (Actual common-tail producer target).**

Lean statement: `D5/S3/Combinatorics/CDSO/ArrayCore.Lemma134ProducerStatement`

*Formalization.* `D5/S3/Combinatorics/CDSO/ArrayCore.Lemma134ProducerStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full producer statement includes delta≤p≤u≤hp, the core rank bounds, the nonnegative discrete remainder Q, the nonnegative actual-core Jensen gap, and d≥H_D−u A_a(u)+E Q(L)+S_f under a²≥3h(2a+1). The implementation obtains the remainder by summing nonnegative actual-incidence residuals. A rational tangent inequality supplies Jensen; no producer certificate is added to the hypotheses of the localization theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/CDSO/ArrayCore.JointArray`
- Truth anchor: `D5/S3/Combinatorics/CDSO/ArrayCore.Lemma134ProducerStatement`
