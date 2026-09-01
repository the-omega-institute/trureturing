# The Submodular Greedy Approximation Guarantee

## Abstract

Cardinality-greedy maximization of a monotone submodular function attains the classical one-minus-one-over-e guarantee.

**Theorem 1.1 (Cardinality greedy attains one minus one over e).**

$$\left(1 - \frac{1}{e}\right) f(O) \leq f(S_{k})$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SubmodularGreedyApproximation.cardinality_greedy_one_sub_inv_exp_guarantee` (`✓ std3`). ∎

*Citation.* G. L. Nemhauser; L. A. Wolsey; M. L. Fisher (1978). *An Analysis of Approximations for Maximizing Submodular Set Functions—I*. DOI: [10.1007/BF01588971](https://doi.org/10.1007/BF01588971).

*Commentary.*

Let f be a real-valued function on finite subsets, normalized by f(empty) = 0, monotone under inclusion, and submodular in diminishing-returns form. At each of k steps, choose a fresh element whose marginal value is maximal among all unchosen elements.

For every comparison set O with at most k elements, submodularity bounds the remaining gap f(O) - f(S_t) by the sum of O's marginals at S_t. Greedy maximality bounds every summand by the next greedy gain, giving a geometric contraction by 1 - 1/k.

After k steps, Mathlib's exponential power bound places the residual factor below exp(-1). The theorem does not require O to be globally optimal, so the displayed guarantee applies in particular to every optimal feasible set.

## References

- Truth anchor: `D5/S3/Resource/SubmodularGreedyApproximation.cardinality_greedy_one_sub_inv_exp_guarantee`
