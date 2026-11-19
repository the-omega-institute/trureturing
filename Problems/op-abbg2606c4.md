---
slug: op-abbg2606c4
bibkey: anholcer2026epistemic
doi: null
url: https://arxiv.org/abs/2606.11494v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.result
---

## Problem

Conjecture 4 of Anholcer–Bartkowiak–Bosek–Grytczuk, *Epistemic fair division of independence structures*, arXiv:2606.11494v1, Section 5, page 21, asks for an ordinary EF1 complete allocation under individual matroid constraints when each matroid has chromatic number at most the number of agents. Preregistration: [#25693](https://github.com/the-omega-institute/trureturing/issues/25693).

### Statement echo

The finite ground set is `Fin m` and the agents are `Fin n`, with $n>0$. Every native Mathlib matroid has ground `Set.univ`. Its chromatic number is the infimum in $\mathbb N\cup\{\infty\}$ of the numbers of parts in complete independent partitions. Singleton weights are arbitrary nonnegative reals; `value` is their additive extension. `Feasible` requires disjointness, completeness and independence of each bundle in its own agent's matroid. Goods EF1 deletes an item from the compared bundle, with an explicit empty-bundle alternative. Chores EF1 deletes from the envying agent's own bundle and compares distinct agents. The two existence assertions may use different allocations. There is no epistemic imaginary-allocation quantifier.

## Motivation

The settling declaration is `D5/S3/Combinatorics/Matroids/AnholcerEpistemicEF1Refutation.result`, with literal type $\neg\mathrm{claim}$. The module has generality I, utility `kind=certified-instance` with `basis=refutes`, and admission basis `open-problem-resolution (#25693; Refuted)`. Its only public theorem is this result; the other public declarations express the source definitions.

## Gap

Separate two-colorings of heterogeneous matroids do not supply the exchanges needed for a fair complete allocation. The example has two capacity-one blocks per matroid, with different block partitions. This realizes the complementary-item obstruction credited to Dror–Feldman–Segal-Halevi, JAIR 76 (2023), Section 8.3, DOI 10.1613/JAIR.1.13779, through individual matroids. That prior obstruction uses a common nonmatroid constraint.

## Route

On items $0,1,2,3$, the first matroid has blocks $\{0,1\},\{2,3\}$ and the second has blocks $\{1,2\},\{3,0\}$. Native `Matroid.freeOn` and `Matroid.comap` construct the matroids; `matroids_indep_iff` identifies independence with injectivity of the corresponding block map. Both admit the coloring $\{0,2\},\{1,3\}$. The finite certificate in `feasible_rigid` restricts every complete feasible allocation to these bundles in one of two orders. Both agents have weights $(3,1,3,1)$. The bundle values are $6$ and $2$, and any deletion from the high bundle leaves $3>2$. `feasible_not_fair` excludes both fairness predicates for either order. `result` specializes the closed universal claim and derives a contradiction from its goods existence assertion.

## Falsifier

A feasible goods-EF1 allocation in the four-item instance would contradict `feasible_not_fair`. The finite independent-partition upper bound and full-ground equality are supplied by `two_colorable` and `matroids_ground`. The claim's two separate existential quantifiers and nonnegative additive valuations agree with the preregistered source statement.

## Evidence

Kernel-checked declarations: `result` refutes `claim`; private `feasible_rigid` classifies all feasible allocations and private `feasible_not_fair` excludes goods and chores EF1. All are in `D5.S3.Combinatorics.Matroids.AnholcerEpistemicEF1Refutation`. Proof shape is bind-only for all seven theorems: finite decision, instantiation, projection and normalization. No escape witness is claimed. The designated external open-problem settlement supplies the admission basis.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact computation

[Experiment directory at immutable revision 303ffbbcfe85204772f3485d4c7025c4b3ad6802](https://github.com/the-omega-institute/trureturing-experiments/tree/303ffbbcfe85204772f3485d4c7025c4b3ad6802/docs/reports/anholcer-et-al-epistemic-ef1-matroids).

The program is `docs/reports/anholcer-et-al-epistemic-ef1-matroids/check.py`. Command: `python3 /tmp/op-abbg2606c4/stageb-3661/check.py`, using the byte-identical file extracted from that revision. Exit code: 0. SHA-256: `ac1642dbebff4e088af5316ca68302de06914a6a8ee0346553bf393507b2def7`. Exact rational enumeration covers ranks $r=2,\ldots,8$, nine strict positive parameter pairs per rank, equality and lower-side threshold controls, and all $256$ corners of the independent eight-coordinate radius-$1/10$ perturbation box. Heredity and exchange are exhaustively checked for $r=2,3,4$. The output concludes `ALL_CHECKS_OK`.

## Triage

### What the settlement shows

1. **Proved, kernel-checked:** the two heterogeneous matroid constraints force parity rigidity; the value-$6$/value-$2$ split fails goods and chores EF1 after every deletion from the high bundle. Evidence: private `feasible_rigid` and `feasible_not_fair`; the public `result` refutes the universal assertion.
2. **Computed:** the witness has equal rank $2$, no loops, exact chromatic number $2$ and strictly positive identical valuations. These restrictions do not repair this instance. Evidence: the exact computation above at $r=2$.
3. **Computed:** for $r=2,\ldots,8$, exactly two feasible allocations and nine strict parameter choices per rank fail both EF1 notions. Equality and lower-side threshold controls satisfy EF1. Evidence: the same computation; no inference to unbounded $r$ is made.
4. **Computed:** all $256$ corners of the independent eight-coordinate radius-$1/10$ perturbation box fail both EF1 notions. Evidence: the same computation. This is a corner enumeration, not a Lean theorem about the full real box.
5. **Open:** the unbounded $r$-family and full real perturbation region are not formalized by this module. The finite enumerations do not supply those uniform Lean statements.
6. **Open:** general common-matroid and epistemic variants, additional compatibility hypotheses, and the source's Conjecture 2 and Problem 3 are not settled by this refutation.

The nearest surviving assertions are the existence of complete feasible parity allocations in this witness and the equality/lower-side EF1 controls, both computed by the checker. The constraints are heterogeneous, so the counterexample does not refute the source's common-matroid Conjectures 1 or 2 or either main theorem. Problem 3 asks whether Conjecture 4 follows from Conjecture 2; this refutation rules out Conjecture 4 as stated and does not independently settle the truth value of that implication. These are scope statements about the counterexample, not additional kernel-checked theorems.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The screen recorded in #25693 covers the versioned source, the cited JAIR obstruction, exact-author post-source papers and selected heterogeneous-matroid EF1 searches; it identifies no settlement of the exact assertion among accessible material read. OpenAlex and Semantic Scholar citation discovery, MathOverflow access, live MathDB status, exhaustive broad-query pagination and freshness of public-Lean mirrors remain unverified. The literature classification for the exact settlement is suspected-novel; the common-nonmatroid obstruction is literature-attested. No global priority claim follows.
