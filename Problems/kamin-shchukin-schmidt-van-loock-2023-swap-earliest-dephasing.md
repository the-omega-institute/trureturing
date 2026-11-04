---
slug: kamin-shchukin-schmidt-van-loock-2023-swap-earliest-dephasing
bibkey: kaminshchukinschmidtvanloock2023repeaters
doi: 10.1103/PhysRevResearch.5.023086
url: https://arxiv.org/abs/2203.10318v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.result
---

# Swapping an earliest adjacent pair minimizes dephasing for every number of segments

## Problem

L. Kamin, E. Shchukin, F. Schmidt and P. van Loock, *Exact rate analysis for quantum repeaters with imperfect memories and entanglement swapping as soon as possible*, arXiv:2203.10318v1 (Phys. Rev. Research 5, 023086, 2023), subsection “Optimal swapping scheme”, state in the TeX source `skr.tex`, lines 1082–1084:

> Our conjecture is that the statement is valid for all $n \geqslant 2$, but in this work we consider repeaters with up to eight segments only, and for such $n$ we have verified this statement directly.

The statement is the displayed equality at line 1080:

$\tilde{D}_n(N_1, \ldots, N_n) = D^\star_n(N_1, \ldots, N_n)$.

Here $N_i$ is the positive integer ready time of segment $i$. Swapping adjacent segments adds $|N_i-N_{i+1}|$ and replaces their ready times by $\max(N_i,N_{i+1})$. The source defines $\tilde D_n$ by repeatedly choosing an adjacent pair with least maximum, allowing arbitrary ties (`skr.tex`, lines 1033–1044). It defines $D^\star_n$ by minimizing the swap cost plus the recursively optimal cost of the shortened list over every adjacent first pair, with $D^\star_2(N_1,N_2)=|N_1-N_2|$ (lines 1049–1065).

Issue [#25201](https://github.com/the-omega-institute/trureturing/issues/25201) fixes the reading: for every list of $n\ge2$ positive integers and every complete greedy history, its accumulated cost equals $D^\star_n$. This is proved. The formal statement also includes zero ready times and terminal lists.

## Motivation

The paper studies linear repeaters with parallel entanglement distribution, deterministic swapping and memory dephasing. Among the parallel schemes without memory cut-off considered in its “Optimal swapping scheme” subsection, the raw rates agree; selecting a swapping order therefore concerns accumulated dephasing (`skr.tex`, lines 1013–1031). The conjecture asks whether a local earliest-pair rule attains the global minimum for every chain length, beyond the source's verification through eight segments.

The [literature note](../Library/Observer/kaminshchukinschmidtvanloock2023repeaters.md) identifies the source and its two recurrences.

## Gap

Issue #25201 records the bounded literature check:

- The arXiv v1 source states the quoted conjecture in `skr.tex`, lines 1082–1084.
- The search seat reports that the journal PDF retains the conjecture and that its screening of 54 Semantic Scholar citing records, including full readings of the closest works, found no proof.
- The orchestrator reports that F. Schmidt's 2024 thesis, *Repeater-based quantum communication with advanced optical encoding* (handle 20.500.12030/9790), retains the conjecture in its reprint of the article; web, Zenodo and repository searches found no settlement in their searched scope.

`not-found-in-searched-scope`.

## Route

Use zero-based indices for a natural-number list $x$ of length $n$. Write $m_i(x)$ for `merge x i` and $c_i(x)$ for `swapCost x i`. At a valid index $i+1<n$, these replace $x_i,x_{i+1}$ by their maximum and charge their absolute difference. A greedy step (`IsGreedyStep`) requires both $i+1<n$ and $\max(x_i,x_{i+1})\le\max(x_j,x_{j+1})$ for every $j+1<n$. A complete greedy history (`IsGreedyRun`) requires such a step at each changing list and ends with length at most one; `runCost` adds its successive charges.

Let $M(x)$ be the maximum, taking $M([])=0$, and define the integer-valued private `potential` by

$F(x)=M(x)+\sum_{i=0}^{n-2}\max(x_i,x_{i+1})-\sum_{i=0}^{n-1}x_i$,

with an empty sum equal to zero. `bellman v x` is zero when $n\le1$ and otherwise the finite minimum of $c_i(x)+v(m_i(x))$ over $0\le i<n-1$. `dstar x` applies this Bellman operator $n$ times to the constant zero function and evaluates at $x$.

1. **Length and terminal cases.** For $x:\mathrm{List}\,\mathbb N$, $i:\mathbb N$ and $i+1<n$, `merge_length` gives $|m_i(x)|+1=n$, and `maximum_merge` gives $M(m_i(x))=M(x)$. For $n\le1$, `potential_terminal` gives $F(x)=0$.
2. **One-step certificate.** For $x:\mathrm{List}\,\mathbb N$, $i:\mathbb N$ and $i+1<n$, `potential_step_le` gives $F(x)\le c_i(x)+F(m_i(x))$, with the natural cost cast to the integers. Under `IsGreedyStep x i`, including validity and comparison with every valid adjacent pair, `potential_step_eq` gives equality.
3. **An attained finite minimum.** For $x:\mathrm{List}\,\mathbb N$ with $1<n$, `greedy_exists` supplies an index satisfying `IsGreedyStep x i`. The Bellman index set is the nonempty finite range $0,\ldots,n-2$; `bellman` explicitly carries its nonemptiness proof, and the proof uses an index attaining its minimum.
4. **Bellman value.** For $k:\mathbb N$ and $x:\mathrm{List}\,\mathbb N$ with $n\le k$, `bellman_potential` identifies the integer cast of the $k$-fold Bellman value at $x$ with $F(x)$. The greedy equality supplies the upper bound, and the valid-step inequality supplies the lower bound. Taking $k=n$ gives `dstar_potential`: $(\operatorname{dstar}(x):\mathbb Z)=F(x)$ for every natural-number list $x$.
5. **Every tie choice.** For $x,hs:\mathrm{List}\,\mathbb N$ with `IsGreedyRun x hs`, `greedy_cost_potential` gives $(\operatorname{runCost}(x,hs):\mathbb Z)=F(x)$ by induction on $hs$. Combining it with `dstar_potential` and injectivity of the natural-to-integer cast yields `result : claim`.

The named auxiliary lemmas are private declarations in the canonical module.

## Falsifier

A list and a complete greedy history whose cost differed from the source's optimal recurrence would falsify the preregistered claim. An identification with another greedy criterion, a chosen tie rule, or an incomplete history would not settle that claim. The module uses the source's minimum of adjacent maxima, retains every tie choice, and requires completion.

The minimum is a nonempty finite minimum whenever the list has at least two entries. Each valid merge decreases length by one, so the length-many Bellman iterations reach the terminal zero case and implement the source's recurrence, including its two-segment base case. Empty and singleton lists have value zero. Although `merge` and `swapCost` read absent entries as zero, every index used by the greedy predicate or Bellman minimum is valid, so those defaults do not change the source's problem.

## Evidence

The canonical source is `D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.lean`.

- **Proof.** It proves `result : claim`, where `claim` quantifies over every natural-number list and every complete greedy history.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality.lean.json`.

Declaration statements:

- `result`: `sha256:6ca9775ab40ad04e8a65b30c316733d27cef802f4cb29e8b0ff2b64747d10ed3`;
- `claim`: `sha256:2a40d7d312c40f84f5ea46e4e493fe85601be4238d3484360199433472db1d60`.

## Triage

Tier 1 conjecture of a 2022 preprint published in 2023, preregistered in issue #25201 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every finite list $x$ of natural ready times and every list $hs$ of successive indices, if $hs$ is a complete greedy history of $x$, then $\operatorname{runCost}(x,hs)=\operatorname{dstar}(x)$, including zero ready times, empty and singleton lists, and every greedy tie choice.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Decisive mechanism.* For a natural-number list $x$ and a valid pair index $i+1<|x|$, `potential_step_le` gives a nonnegative one-step excess $c_i(x)+F(m_i(x))-F(x)$. When that pair also minimizes the maximum among all valid adjacent pairs, `potential_step_eq` makes the excess zero. Thus the potential is an attained certificate of the Bellman minimum rather than an estimate with a remaining error term; the route's `bellman_potential`, with $|x|\le k$, and `greedy_cost_potential`, with a complete greedy history, express the two sides of that certificate. No readiness probability law or independence assumption enters `claim`.
- *Greediness is sufficient, not a characterization of every minimizer.* For natural ready times $a<b$, consider $(a,a,b,b)$. Merging the two $b$ entries first is not greedy, since the pair of $a$ entries has smaller maximum. That merge and the subsequent merge of the two $a$ entries each cost zero, and the final merge costs $b-a$. Merging the two $a$ entries first, then the two $b$ entries, gives a greedy history with the same cost. Every complete history must at some point merge an $a$-ready segment with a $b$-ready segment and pay $b-a$, so both histories attain the minimum. The converse and this nonuniqueness argument are not statements of `result`.
- *Effect on the paper.* For positive integer ready times, the settlement supplies the all-length equality of the two swapping recurrences conjectured in `skr.tex`, lines 1080–1084. It therefore justifies identifying the earliest-pair cost with the recurrence's optimal dephasing beyond eight segments. It supplies no general probability generating function, secret-key-rate calculation or comparison with another entanglement-distribution protocol. In particular, the source's separate conjecture about the highest secret key rate among all schemes for more than three segments under channel loss and memory dephasing (`skr.tex`, line 2034), and its extrapolated comparison with fully sequential dephasing for $n>8$ (line 1683), remain unsettled here.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches reported in #25201 and does not establish exhaustive worldwide novelty or priority. The journal PDF, Schmidt thesis, 54-record citation screening and closest citing works, the comparison with Shchukin–van Loock arXiv:2109.00793, and the orchestrator's web, Zenodo and repository searches were not independently reproduced. The report that arXiv has only v1 was not independently checked.

The arguments labelled “Argued, not formalized” add no formalized converse, uniqueness classification, probabilistic result or physical interpretation. The identification of the finite Bellman iteration with the paper's recurrence is explained in prose rather than supplied as a separate Lean equivalence theorem. The module formalizes neither the physical derivation of the swap-cost model nor arbitrary real ready times, probability generating functions, secret-key rates, memory cut-offs, probabilistic swapping, entanglement distillation or the source's comparisons with sequential and fixed distribution schemes.
