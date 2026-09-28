---
slug: davis-width-k-descent-difference-coprime-formula
bibkey: davis2017widthk
doi: 10.48550/arXiv.1701.04788
url: https://cs.uwaterloo.ca/journals/JIS/VOL20/Davis/davis6.pdf
triage: theorem
motivation_gids:
  - D5/S1/Words/DavisWidthDescentDifferenceCoprime.result
---

# Davis's coprime width-descent difference formula

## Problem

Robert Davis, *Width-k Generalizations of Classical Permutation Statistics*,
JIS 20 (2017), gives the following descent-set line, generating function, and
MacMahon identification together at the top of printed page 2. Printed page
1 ends with the preceding descent-count formula:

> where Des σ = {i ∈ [n − 1] | a_i > a_{i+1}}.
> Given any statistic st, one may form the generating function
> F_n^{st}(q) = Σ_{σ∈S_n} q^{st σ}.
> A famous result due to MacMahon [6] states that F_n^{des}(q) =
> F_n^{exc}(q), and that both are equal to the Eulerian polynomial A_n(q).
> The Eulerian polynomials themselves may be defined via the identity
> Σ_{j≥0} (1 + j)^n q^j = A_n(q)/(1 − q)^{n+1}.

Printed page 2 defines width-k descents:

> For each of the following definitions, we assume n ∈ Z_{>0}, k ∈ [n − 1],
> ∅ ≠ K ⊆ [n − 1], and σ = a_1 a_2 ··· a_n ∈ S_n. We define a width-k
> descent of σ to be an index i ∈ [n − k] for which a_i > a_{i+k}. Thus the
> width-1 descents are the usual descents of a permutation. Let
> Des_k(σ) = {i ∈ [n − k] | a_i > a_{i+k}} denote the set of all width-k
> descents of σ, and set des_k(σ) = |Des_k(σ)|.

Printed page 6 introduces the Laurent polynomial and the named conjecture:

> We now show that interesting behavior occurs when considering the function
> G_{n,k}(q) = Σ_{σ∈S_n} q^{des_k(σ)−des_{n−k}(σ)}.
> According to computational data, the following conjecture holds for all
> n ≤ 9 and 1 ≤ k < n for which gcd(k, n) = 1.
>
> Conjecture 9. If gcd(k, n) = 1, then
> G_{n,k}(q) = n q^{1−k} A_{n−1}(q).

The formal theorem makes the surrounding range explicit: for all natural
`n` and `k`, if `1 <= k`, `k < n`, and `Nat.Coprime k n`, then

```text
G(n,k) = n * q^(1-k) * eulerian(n-1).
```

Here `eulerian(m)` is the descent generating function that the paper
identifies with `A_m` by MacMahon's theorem. The paper's separate
infinite-series definition of the Eulerian polynomials is not formalized.
One-based positions are transported to `Fin n`, and signed exponents live in
the Laurent polynomial ring over the integers.

## Motivation

The question asks for a uniform identity over every coprime pair, rather than
a finite verification or a coefficientwise approximation.

## Gap

The primary source, arXiv:1701.04788, labels the identity Conjecture 9.
The two identified citing papers, arXiv:1912.08551 and arXiv:2402.16251, do
not address it. MathDB `/p/335077` records the same statement and displayed
`Solutions 0` on 2026-09-28. The pinned Mathlib contains no matching
width-descent or cyclic-distribution result. These bounded searches do not
establish worldwide priority.

## Route

The source proof has two live local deductions inside `result`.

W1, `cyclic_reindexing_sum`, uses coprimality to reindex positions along the
single cycle induced by multiplication by `k` modulo `n`. The width-`k` and
width-`(n-k)` counts combine into the cyclic descent count minus `k`, and the
permutation equivalence transports the whole Laurent sum.

W2, `cyclic_descent_distribution`, uses the equivalence
`S_n ~= Fin n x S_(n-1)`: rotate each permutation until its maximum is last,
then restrict to the first `n-1` positions. Cyclic descents become ordinary
descents plus one, so their generating function is
`n * q * eulerian(n-1)`. This identity requires `2 <= n`; its `n = 1`
extension is false. The hypotheses `1 <= k < n` supply that bound.

Combining W1 and W2 gives
`q^(-k) * (n * q * eulerian(n-1))`, and Laurent monomial multiplication
normalizes the exponent to `1-k`.

## Falsifier

A natural pair `1 <= k < n` with `Nat.Coprime k n` for which the two Laurent
polynomials differ would refute the theorem. A mismatch between the formal
`widthDescents`, `G`, or `eulerian` definitions and the quoted source
definitions would invalidate the source-to-formal resolution claim even if
the Lean theorem remained true. Non-coprime pairs are not counterexamples.

## Formal Result

The formal source is
[`DavisWidthDescentDifferenceCoprime.lean`](../D5/S1/Words/DavisWidthDescentDifferenceCoprime.lean).
The public surface consists of the definitions `widthDescents`, `eulerian`,
`G`, and `claim`, followed by the theorem `result`. Both W1 and W2
are local deductions within that theorem's proof; there are no named private
theorem companions.

The theorem proves the universal identity. Its axiom closure is
`[propext, Classical.choice, Quot.sound]`. The Scribe result carries
`OpenProblemResolutionClaim(Proved)`, and the source-bound `DependentFamily`
registration has a `declared_validated` source-equivalence bridge.

## Triage

First tier: a numbered conjecture in a published paper. The exact universal
symbolic identity has `utility: none`.

## ASSUMED-UNVERIFIED

The bounded literature checks do not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
