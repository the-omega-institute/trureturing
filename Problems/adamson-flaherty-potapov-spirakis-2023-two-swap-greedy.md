---
slug: adamson-flaherty-potapov-spirakis-2023-two-swap-greedy
bibkey: adamsonflahertypotapovspirakis2024twoswap
doi: 10.1007/978-3-031-55601-2_5
url: https://arxiv.org/abs/2307.01648v3
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.result
---

## Problem

Adamson, Flaherty, Potapov and Spirakis, *Structural and Combinatorial Properties
of 2-swap Word Permutation Graphs*, arXiv:2307.01648v3, Section 5, page 23:

> For the 2-swap graph specifically, we leave open the problem of determining the shortest path between two given words w and v. We conjecture that the simple greedy algorithm used to derive the upper bound in Lemma 4 can be used to find the shortest path between any pair of vertices.

The target is the greedy optimality conjecture, preregistered in
[issue #19317](https://github.com/the-omega-institute/trureturing/issues/19317).
For words with the same Parikh vector, the formal claim asks whether some
admissible order makes the number of generated pairs with distinct indices equal
the configuration-graph distance. An admissible order omits any maximal-count
reference symbol and lists every other symbol once in non-increasing count.
All tied choices are allowed. The count does not require that the generated
swaps be legal at application time or reach the target, so refuting this
necessary condition also refutes the stronger shortest-path assertion.

### Statement echo

| Source clause | Formal counterpart and fidelity |
| --- | --- |
| Words in $\Sigma^n$ | Functions `Fin n → Fin s`; zero-based relabelling of the source's positions and alphabet. |
| Definition 1 exchanges positions $i<j$ holding different symbols | `twoSwap` precomposes with `Equiv.swap`; `IsTwoSwapOf` imposes both restrictions. |
| $P(w)[a]$ counts occurrences of $a$ | `parikh` counts the filtered finite set of positions. |
| $G(P)$ has exactly the words of Parikh vector $P$ | `configGraph` induces `swapGraph` on that subtype; the equality binder puts both endpoints in the same graph. |
| Algorithm 1 pairs corresponding occurrences | `occurrences` lists positions increasingly; `stageSwaps` zips the lists before the stage is applied. |
| Apply a stage and continue over the remaining symbols | `applySwaps` folds the transpositions; `greedySwaps` recursively concatenates stages. |
| $P[1]\ge\cdots\ge P[\sigma]$, processing $\Sigma\setminus\{1\}$ | `AdmissibleOrder` permits every maximal reference and every count-compatible order. |
| A shortest path for any pair of vertices | `claim` universally quantifies alphabet size, length and both words; its conclusion requires only equality of count and distance. |
| Refutation | `result` proves the negation of the full universal claim. |

`swapGraph` on all words, list application order and `greedyLength` are explicit
encoding conventions. They introduce no extra hypothesis on the source's
vertices. List application order cannot alter the count in the binary family,
which has only one stage. No positivity restriction is added on alphabet size
or length.

## Motivation

A pair of adjacent words for which every admissible run generates more than one
nontrivial pair suffices. An unbounded family also separates the greedy count
from the optimum by an unbounded additive gap and ratio.

## Gap

The literature screen recorded in #19317 covers the paper's versions v1–v3,
the LATIN chapter and accepted manuscript, and the related works listed there.
The source retains the conjecture. Flaherty's thesis, *Graph Theoretic Concepts
and Algorithms Motivated by Chemistry Applications*, University of Liverpool,
Chapter 3, repeats the algorithm and cycle-cover characterization; the recorded
reading identifies no settlement there or in its concluding directions.
These are attributed source and literature readings, not a completeness proof.
Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

For every natural $k\ge2$, over the binary alphabet set

$$
w_k=0^k1^k,\qquad v_k=1\,0^{k-1}1^{k-1}0.
$$

Both words have Parikh vector $(k,k)$. Exchanging positions $0$ and $2k-1$
turns $w_k$ into $v_k$, and the words differ, so their distance is one.
The zero occurrences in $w_k$ occupy $0,\ldots,k-1$; in $v_k$ they occupy
$1,\ldots,k-1,2k-1$. Every equal-rank pair is nontrivial. The one occurrences
occupy $k,\ldots,2k-1$ and $0,k,\ldots,2k-2$, respectively, again giving
$k$ nontrivial pairs. The only admissible binary orders are the two singleton
orders, so every allowed run has count $k$. At $k=2$, count two contradicts
distance one.

## Falsifier

A faithful admissible order with count one on any $F_k$ would contradict
`family_all_runs`. A failure of the endpoint transposition, equality of Parikh
vectors or the two-order classification would invalidate the family argument.
The compiled declarations check these obligations without extra axioms.

## Evidence

The module is
`D5/S3/Combinatorics/Permutation/AdamsonFlahertyPotapovSpirakisTwoSwapGreedy.lean`.
Its namespace is the dotted version of that path. `result` is the sole public
theorem; its compiled type is literally the negation of `claim`. The private
`family_theorem` establishes the uniform distance and count statements on the
live proof path to `result`. All theorem classifications are `bind-only`;
admission is `open-problem-resolution (#19317; Refuted)`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
No Reg source or `declared_validated` registration is claimed. The audit
reference is [#19440](https://github.com/the-omega-institute/trureturing/issues/19440).

### Experiment

The independent finite check is in
[the experiments repository, pinned directory](https://github.com/the-omega-institute/trureturing-experiments/tree/995dd5c17c9dc8f5dfdcfe1fc921644e36f489a1/docs/reports/adamson-flaherty-potapov-spirakis-2023-two-swap-greedy).
Command: `python3 check.py` in that directory, exit 0, `RESULT PASS`.
Script SHA-256: `64fcb9c8957d1d5274a546bc69eff1d61da07791187867257cf3c4710536d34e`.
The tested scope is $F_k$ for $2\le k\le7$, $G_m$ for $2\le m\le6$,
the binary census at lengths 2 through 9, and the ternary census at lengths 2
through 6. Each $F_k$ has breadth-first distance one and both counts $k$.
For those tested $F_k$, at least one of forward/reverse application orders gives
a legal path for each reference; for reference 2 only reverse application is legal.
Each tested $G_m$ has distance one and greedy count $m$ with a legal path to the
target. The census counts pairs without any shortest admissible run: binary
lengths 2 and 3 have zero, length 4 has $4/70$, and length 9 has $23952/48620$;
ternary length 4 has $12/639$ and length 6 has $7020/35169$.
These finite computations make no claim about larger census ranges or uniform
legality of stage application orders.

## Triage

### What the settlement shows

- **Kernel-checked:** `family_theorem` proves distance one and count $k$ for every
  admissible run on every $F_k$, $k\ge2$. `result` refutes the universal claim.
  Thus the complete $F_k$ target is closed.
- **Proved in prose:** subtracting the distance from the count gives $k-1$;
  dividing the count by the positive distance gives $k$. These gaps and ratios
  are unbounded as $k$ ranges over the naturals at least two.
- **Explanation:** equal-rank occurrence matching commits to all displaced
  occurrences even when the endpoint transposition already reaches the target.
  This is the failure mechanism of the greedy rule. The source's Corollary 6
  gives a cycle-cover characterization; no Lean cycle-cover theorem is claimed here.
- **Proved in prose:** for any binary words with equal Parikh vectors, distance
  equals the number $r$ of positions changing from 0 to 1. The number changing
  from 1 to 0 is also $r$. A swap decreases the first count by at most one, so
  at least $r$ swaps are necessary. Pairing one mismatch of each type fixes both
  and leaves all other positions unchanged; repeating gives $r$ legal swaps.
  This proves the binary distance formula, while the kth-occurrence rule can
  fail to realize it. The Lean family theorem proves the special distance-one
  case only.
- **Computed:** the experiment entry establishes the stated finite $F_k$ and
  $G_m$ ranges, application-order legality and binary/ternary census values.
  Census extensions and uniform application-order legality beyond those ranges
  are open here.
- **Open:** no shortest-path algorithm over unbounded alphabets or complexity
  classification is established by this delivery. The attribution of NP-hardness
  to Amir, Hartman, Kapah, Levy and Porat, DOI `10.1137/080712969`, is
  `ASSUMED-UNVERIFIED`; the refutation does not depend on it.
- **Source scope:** the conjecture is in the closing discussion; Lemma 4 asserts
  an upper bound. The family does not refute that bound. No change to the paper's
  independent diameter or Hamiltonian results follows from this refutation.
- **Verification boundary:** validation is scoped to this module and its imports;
  no repository-wide Lean build or local full gate is claimed. No Reg compilation
  is claimed, because the sole public theorem has the designated-result exemption.
- **Attribution boundary:** the mathematical inference is kernel-checked; the
  source and literature readings are attributed in #19317. No GPT Pro call is
  part of this implementation's verification evidence.

## ASSUMED-UNVERIFIED

Literature-screen completeness and the recalled NP-hardness attribution are
`ASSUMED-UNVERIFIED`. The unbounded-alphabet shortest-path problem, its complexity,
uniform legality claims beyond the finite experiment, and larger censuses are
open here. The source quotes and zero-based correspondence are distinct from
an assertion that every generated list is a legal shortest path.
