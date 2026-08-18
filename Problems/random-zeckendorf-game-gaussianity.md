---
slug: random-zeckendorf-game-gaussianity
bibkey: cheigh2022towards
arxiv_id: 2210.11038
triage: window
motivation_gids:
  - D5/S1/Digit/Raw
  - D5/S1/Digit/Carry
  - D5/S1/Digit/Normalize
  - D5/S0/Rewriting/NewmanConfluence
  - D5/S0/Rewriting/NormalFormFunction
  - D5/S0/Asymptotics/WeightedProbability/FiniteProductCapture
  - D5/S0/Asymptotics/WeightedProbability/ExactCaptureCount
  - D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion
  - D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity
  - D5/S0/Asymptotics/WeightedProbability/SecondMomentCoherence
---

# Gaussianity of random Zeckendorf game lengths via mixing

## Problem

The unordered Zeckendorf game starts from `N` copies of `F_1`; at each step it
combines consecutive Fibonacci terms or splits a repeated term until the
Zeckendorf decomposition is reached. Let `L_N` be the number of moves.

Conjecture 1.7, quoted from arXiv:2210.11038v1:

> “In the limit \(N\to\infty\), the distribution of the number of moves in a
> random Zeckendorf game on input \(N\) converges to a Gaussian, with
> expectation and variance approximately \(0.215N\).”

The paper studies both the uniform measure `mu_N` on complete games and the path
measure `P_N` obtained by choosing uniformly among legal moves at each state.
Because "approximately" and the measure are not fixed inside the conjecture
sentence, the first declaration-ready target should be the paper's exact mixing
Question 6.5 for the locally uniform path measure.

Let `d_N` be the longest game length and let `X_{N,i}` be the Bernoulli
indicator that move `i` is a split, padded by zero after termination. With
`alpha_N(k)` the strong-mixing coefficient between the sigma-algebras before `m`
and after `m+k`, the paper asks whether there exist `delta, C > 0` such that for
all `N`, the sum over `k >= 0` of `(k+1)^2 alpha_N(k)^(delta/(4+delta))` is less
than `C`.

It states that an affirmative answer immediately yields the Gaussianity
conjecture via the cited mixing central limit theorem. Question 6.6 proposes the
stronger pointwise bound `|P_N(A ∩ B) - P_N(A) P_N(B)| <= C/k^(2+epsilon)`.

The paper states the difficulty:

> “The scope of this result is admittedly restricted...”

> “...it is unclear how to extend this to the entirety of \(\Omega_N\).”

The paper obtains Gaussianity only on certain natural partition components. Its
full-space obstacle is dependence between separated move indicators; the open
section explicitly turns that into Questions 6.5 and 6.6.

## Motivation

- Game states are finite raw Fibonacci multiplicities and game moves are
  value-preserving local rewrites ending at a unique Zeckendorf normal form.
- The weighted-probability family already supports exact finite product
  probabilities, event capture counts, inclusion-exclusion, and moments. It is
  suitable for finite `Omega_N` certificates once paths are encoded.
- The missing theoretical bridge is a locality/regeneration theorem: a
  sufficiently wide canonical digit barrier should make early and late split
  indicators nearly independent. Frozen carry normalization is a plausible
  source of such a barrier.

## Gap

- The frozen rewrite relation is not the paper's game relation and carries no
  random path measure.
- No enumeration of complete paths, local branching weights, stopping time,
  sigma-algebra, mixing coefficient, or weak convergence API exists.
- Finite exact moment identities do not imply uniform-in-`N` mixing or a central
  limit theorem.
- Conjecture 1.7's intended measure and the mathematical meaning of
  "approximately `0.215N`" require an owner choice before formalization.

## Route

1. Define the finite game DAG and both measures exactly. For `P_N`, use the
   recursion `G_S(z) = z * average over successors of G_T(z)`; for `mu_N`,
   weight successors by their number of terminal suffix paths.
2. Prove the invariant that the number of combine moves is fixed, so game length
   differs from a constant by the split count, matching the paper's triangular
   array.
3. Search for regenerative barriers in the bin representation: an interval of
   empty or canonical bins may prevent carry/split influence from crossing
   except through a rare sequence of moves.
4. Bound the probability that influence crosses a gap of width `k`; a polynomial
   exponent greater than 2 would establish Question 6.6, while exponential decay
   would be stronger.
5. Use existing finite probability and moment declarations for exact small-`N`
   checks; import a mixing central limit theorem only after the uniform bound is
   formal.

## Falsifier

The Gaussian limit and the existential mixing constants have no single finite
falsifier. A claimed explicit bound with fixed `epsilon`, `C`, `N0` is falsified
by exact `N, m, k, A, B` violating it.

A structural regeneration lemma is finitely falsified by two legal histories
agreeing on the proposed barrier but producing different reachability or
conditional distributions beyond it. Such history pairs should be emitted as
minimal counterexamples.

## Evidence

For every `N <= 35`, use dynamic programming on the exact game DAG to compute
under both `mu_N` and `P_N`:

1. the full rational probability generating function of `L_N`;
2. exact mean, variance, skewness, and fourth standardized moment;
3. distributions of each split indicator and selected two-block joint events;
4. lower bounds on `alpha_N(k)` obtained by exhaustive event search for small
   sigma-algebras;
5. normalized histograms and Kolmogorov-Smirnov distance, explicitly separated
   by measure.

The main Evidence output should be whether a candidate digit barrier predicts
the observed dependence decay. Gaussian-looking histograms alone are
insufficient.

## Triage

`window`. Exact finite distributions and candidate regeneration lemmas are
reachable; a uniform mixing theorem across all game paths is a genuine new
probabilistic layer.

## ASSUMED-UNVERIFIED

- Conjecture 1.7 is intended for `P_N`, for `mu_N`, or for both; the sentence
  itself is ambiguous.
- The coefficient `0.215` has a limiting exact value rather than being only a
  finite-simulation fit.
- A canonical-bin barrier yields decay strong enough for Question 6.5 or 6.6.
- Whether the conjecture was resolved after arXiv v1 is unverified; novelty of
  the regeneration route is unassessed.
