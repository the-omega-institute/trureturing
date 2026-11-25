---
bibkey: trureturing2026fibonacciqutritoptimum
authors: trureturing research synthesis
year: 2026
title: Exact Fibonacci qutrit Umegaki optimum
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: The fixed four-class commuting pair has an exact attained Umegaki relative entropy maximum over all CPTP qutrit encoders.
strata_touched:
  - D5/S3/Quantum/Divergence/FibonacciQutritOptimum
license: Apache-2.0
triage: anchor
---

# Exact Fibonacci qutrit Umegaki optimum

## Verified locator

The native theorem `FibonacciQutritOptimum.isGreatest_channel` uses
`FibonacciQutritSingularSupport.singular_support_reduction`,
`FibonacciMixedQubit.traceLog_le_benchmark_sub_margin`,
`FibonacciQutritBenchmark.full_rank_benchmark_comparison` and
`FibonacciQutritBenchmark.classical_benchmark_attained`.
`FinitePreparationChannel.finite_preparation_quantum_channel` realizes the
attaining tuple. [trureturing](https://github.com/the-omega-institute/trureturing)

John N. Tsitsiklis, *Extremal Properties of Likelihood-Ratio Quantizers*
(1993), studies classical likelihood-ratio quantizers.
[DOI 10.1109/26.223779](https://doi.org/10.1109/26.223779)

Mario Berta, Omar Fawzi and Marco Tomamichel, *On Variational Expressions for
Quantum Relative Entropies*, give the variational expression for rank-one
projective relative entropy in Lemma 1 and prove its equality with POVM
relative entropy in Theorem 2.
[arXiv:1512.02615](https://arxiv.org/abs/1512.02615)

Péter E. Frenkel and Mihály Weiner, *Classical Information Storage in an
(n)-Level Quantum System*, Theorem 3, identifies the convex hull of the
classical stochastic matrices obtained by encoding and measurement with
that for classical storage of the same dimension.
[arXiv:1304.5723](https://arxiv.org/abs/1304.5723)

## Formalization scope

The objective here is Umegaki relative entropy of the retained quantum
states for one fixed commuting input pair. The diagonal weights are
((88,25,28,0)/141) and ((66,15,12,48)/141). The output dimension is
three, and the optimization includes every completely positive
trace-preserving encoder of the diagonal pair. The attained value is
((113/141)log(113/81)+(28/141)log(7/3)).
