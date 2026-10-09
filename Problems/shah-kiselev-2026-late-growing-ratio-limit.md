---
slug: shah-kiselev-2026-late-growing-ratio-limit
bibkey: shahkiselev2026lategrowing
doi: 10.48550/arXiv.2610.08636
url: https://arxiv.org/abs/2610.08636v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/LateGrowingRatioLimit.result
---

# Shah–Kiselev Conjecture 3.1: the late growing ratio

## Problem

Kian C. Shah and Arthemy V. Kiselev, arXiv:2610.08636v1, §3:

> Definition 3.1. For σ ∈ S_N define the partial sums
> T_k := Σ_{i=N−k+1}^{N} (σ(i) − 1 − p), k = 1, …, N − 1.
> … We denote by Φ_p the set of all permutations σ ∈ S_N with
> σ(1) = 1 and T_k ⩾ 0 for all k = 1, …, N − 1.

Here N = 2p. The conjecture states:

> Conjecture 3.1. As p → +∞, the ratio |Φ_p|/(2p − 2)!
> converges from above to 1 + 0.

The Lean `claim` uses the existing zero-based `PhiTailEncoding.phi` and
asserts convergence to 1 together with
`∀ n : ℕ, 2 ≤ n → (2*n-2).factorial < (phi n).card`.
At p = 1 the ratio equals 1. “From above” means the stated strict
inequality, without an additional monotonicity assertion.

## Motivation

The factorial normalization counts circular orderings of the residual
alphabet. The question is whether multiple admissible cuts in a circular
ordering have a vanishing effect on the total normalized count.

## Gap

The supplied literature extract identifies Conjecture 3.1 in v1 as open.
The expanded extract of arXiv:2605.11137 contains no proof of this limit,
and the supplied reading of OEIS A147681 contains no asymptotic proof.
The cycle lemma and Spitzer's combinatorial lemma provide classical
background for rotation arguments. This is a scoped literature result,
not an exhaustive priority determination.

## Route

For a finite integer alphabet S with distinct letters and sum zero, let
L(S) count orderings with nonnegative prefix sums and P(S) count orderings
with positive nonempty proper prefix sums. Set m = |S|. Reversing the tail
of an admissible permutation and subtracting p gives the residual alphabet
S_p = {1−p,…,p−1}, so |Φ_p| = L(S_p) and m = 2p−1.

Cut a nonnegative word after its last proper zero prefix. Its prefix has
alphabet A, is nonnegative, and has sum zero; the remaining word is strict.
This gives

$$
L(S)\leq\sum_{\substack{A\subsetneq S\\\sum A=0}} L(A)P(S\setminus A).
$$

Rotating to a fixed letter gives one representative per circular ordering.
A zero-sum word has a nonnegative rotation, obtained by cutting at a
minimum prefix sum. Two different strict rotations are impossible: the
segment between their starting positions would have both positive and
negative sum. Thus, for nonempty zero-sum alphabets,

$$
(m-1)!\leq L(S),\qquad P(S)\leq(m-1)!.
$$

Let z_k(S) count zero-sum k-subsets. Removing a marked letter from such a
subset is injective, since the deleted letter is minus the remaining sum.
Consequently k z_k(S) ≤ binom(m,k−1). Complementation gives z_k = z_{m−k}.
Together these imply

$$
(m+2)z_k(S)\leq 2\binom{m}{k},\qquad
z_k(S)(k-1)!(m-k-1)!\leq
\frac{2(m-1)!}{k(m-k)}
$$

for 1 ≤ k < m. Writing R(S) = L(S)/(m−1)!, the last-zero decomposition
and these bounds give

$$
R(S)\leq 1+C\frac{4H_{m-1}}{m}
$$

whenever all smaller nonempty zero-sum alphabets have R ≤ C. Since
4H_{m−1}/m tends to zero, choose a threshold N beyond which it is at most
1/2. Strong induction, the trivial bound R(S) ≤ m below N, and
C = max(2,N) give a single finite C for every such alphabet. The displayed
bound then holds uniformly, and squeezing with R ≥ 1 proves the limit.
The harmonic bound H_j ≤ 1 + log j also gives error O(log p/p).

For p ≥ 2, choose a nonnegative ordering w of S_p without zero. The words
0::w and w++[0] are distinct nonnegative rotations. They have the same
circular representative, so the surjection onto circular orderings is
not injective. Therefore L(S_p) > (2p−2)!.

## Falsifier

The proof would fail if the residual alphabet or prefix index range differed
from the source suffix budgets, if last-zero cutting did not produce a
strict tail, if marked deletion were not injective, or if the induction
constant depended on the individual alphabet. The Lean proof checks the
full reversal/decoding bijection, all suffix lengths 1 through 2p−1, the
decomposition, deletion and rotation maps, and the uniform strong induction.

## Evidence

`D5/S1/Words/Compositions/LateGrowingRatioLimit.result : claim` is compiled
with Lean v4.33.0 and the pinned Mathlib. General counting and analytic
lemmas are in `ZeroSumWordCount.lean`; the permutation bridge and exact
conjecture are in `LateGrowingRatioLimit.lean`. The final axiom closure is
`propext`, `Classical.choice`, `Quot.sound`. Neither module contains `sorry`,
a new axiom, `native_decide`, or an unrestricted heartbeat setting.

Exact subset dynamic programming gives Table 2's counts for p = 1,…,7:
1, 3, 35, 1001, 53109, 4605271, 589809987. The recurrence assigns count 1
to the empty subset, count 0 to a subset with negative sum, and otherwise
sums the counts after deleting each possible last letter. These computed
values support the finite comparison; the uniform limit uses symbolic
proofs rather than finite enumeration.

## Triage

- [proved] The ratio tends to 1 and exceeds 1 for every p ≥ 2. A uniform
  bound is 1 < ratio ≤ 1 + 4C H_{2p−2}/(2p−1), for a finite C independent
  of p; hence the excess is O(log p/p).
- [computed] The exact counts for p ≤ 7 agree with Table 2.
- [open] Determine the exact second-order asymptotics of the ratio.
- [open] Prove the even-index analogue: footnote 8 states that the
  even-index ratios over (2ℓ−1)! also tend to 1, faster. This theorem does
  not settle that separate alphabet and normalization.

## ASSUMED-UNVERIFIED

Literature status is attributed to the supplied v1 quotation and extracts;
no network retrieval or independent priority search was performed. The
classical background attribution does not claim an exact published theorem
already supplies the stated asymptotic estimate. Generated Blueprint
projections, frozen states, and official repository acceptance are separate
from this source-only mathematical verification.
