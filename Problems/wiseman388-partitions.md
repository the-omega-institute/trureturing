---
slug: wiseman388-partitions
bibkey: oeis2025wisemanpartitions
doi: null
url: https://oeis.org/A388712
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/WisemanA388712
---

# Wiseman's nonchoosable partition identity

## Problem

OEIS A388712 states: “Triangle read by rows where T(n,k) is the number of integer partitions of n into k parts without choosable initial intervals.” Its conjecture is: “Also the number of non-superdiagonal reversed partitions of n into k parts, where a sequence (y_1, ..., y_k) is superdiagonal iff y_i >= i for all i = 1..k.” The question is preregistered in [#18601](https://github.com/the-omega-institute/trureturing/issues/18601).

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| Partitions of $n$ into $k$ positive parts | `Nat.Partition n`, filtered by `p.parts.card = k` |
| Initial intervals admit distinct positive representatives | The imported `ChoosableInitial` predicate on descending parts |
| Without choosable initial intervals | Negation in `WisemanA388712.T` |
| Reversed partition, weakly increasing | `p.parts.sort (· ≤ ·)` |
| $y_i\ge i$ with one-based indices | The imported `Superdiagonal` predicate uses zero-based index plus one |
| Non-superdiagonal, with the same number of parts | Negation and the same cardinality filter in `WisemanA388712.nonSuperdiagonal` |
| Equality for every $n,k$ | `WisemanA388712.claim`, proved by `WisemanA388712.result` |

All declaration names above have namespace prefix `D5.S1.Words.Compositions.`. The source expressions are retained in the two count definitions. The existing predicates are reused without new aliases. Classical finite cardinalities do not restrict the quantified natural numbers.

## Motivation

This is an externally named OEIS conjecture with admission basis `open-problem-resolution (#18601; Proved)`. The conclusion is a new settlement of that named assertion; its proof shape is bind-only and no escape witness is claimed. The source is documented in `Library/PermutationPatterns/oeis2025wisemanpartitions.md`.

## Gap

The frozen A388711 module already supplies permutation invariance and the increasing-list criterion. What remains for A388712 is their application under negation, with the common number-of-parts filter. The distinct-representative criterion is not claimed as a new theorem here. Completeness of the literature screen is `ASSUMED-UNVERIFIED`.

## Route

`ChoosableInitialIntervals.choosableInitial_congr_perm` transports choosability between the descending and ascending multiset sorts. `ChoosableInitialIntervals.choosableInitial_iff_superdiagonal` applies to the ascending sort. Their composition is `WisemanA388712.sorted_choosable_iff_superdiagonal`. Negation preserves this equivalence, and adjoining the same part-count condition gives identical finite filters. `WisemanA388712.result` concludes equality of their cardinalities. These are actual imported proof dependencies.

## Falsifier

A multiset for which choosability of its descending sort differs from weak superdiagonality of its ascending sort would contradict the pointwise theorem. A pair $(n,k)$ with different count values would contradict `result`. Neither theorem has a finite cutoff. Strict superdiagonality and subdiagonality are different predicates and do not satisfy the same pointwise statement.

## Evidence

The delivered mathematical module is `D5/S1/Words/Compositions/WisemanA388712.lean`. Its public theorems are `sorted_choosable_iff_superdiagonal` and `result`; both are bind-only, and the former is used by the latter. The Blueprint Scribe expands the equality rather than displaying only the name `claim`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The escape audit is unfinished for both public theorems; [#22068](https://github.com/the-omega-institute/trureturing/issues/22068) records the missing typed infinite-family source reconstruction, equivalence bridge, enrolled readout, intervention/sensitivity and observational-dependence evidence. No `declared_validated` registration is claimed.

### Finite comparison

The pinned experiment is [oeis-a388712-a387118-a388713-choosable-initial-intervals](https://github.com/the-omega-institute/trureturing-experiments/tree/29dcaf8a7cfd8f069c88eff27acd8735cfdfc4d1/docs/reports/oeis-a388712-a387118-a388713-choosable-initial-intervals). At that revision, `check.py` has SHA-256 `2d3874df9fddbc803aa9b2465993e883039fff3da1b51691245f6297ffa335c1`. Running `python3 /Users/auric/trureturing-experiments/docs/reports/oeis-a388712-a387118-a388713-choosable-initial-intervals/check.py 22` exits 0 and reports `RESULT PASS`. The program checks the pointwise criterion on every positive partition of $1\le n\le22$. It compares the A388712 published prefix through $n=7$, A387118 values through $n=22$, and A388713 published prefix through $n=11$. Its row-zero arrays use the source convention. The empty multiset is covered by the universal pointwise theorem.

Evaluating the checker's `choosable` and `superdiagonal` functions at the three ascending lists below, and comparing respectively $z_i>i+1$ and $z_i\le i+1$ in zero-based indexing, exits 0. The command is `python3 /Users/auric/.sshx/7635f5420cd09019b1eca52c/attempt-1/check-pinned-experiment.py`, exit 0; it loads the immutable script with `git show` and checks the same SHA-256. The local reproduction wrapper has SHA-256 `2e650995981f05681d19974dd403fa3257af6591b5a7b64f012377036b23cc4b`; its publication is unverified.

| Ascending parts | Choosable | Weak superdiagonal | Strict superdiagonal | Subdiagonal |
| --- | --- | --- | --- | --- |
| $[1]$ | true | true | false | true |
| $[2]$ | true | true | true | false |
| $[1,1]$ | false | false | false | true |

These computations distinguish the predicates; they do not settle another OEIS conjecture.

## Triage

1. **Proved, kernel-checked:** the shared pointwise equivalence holds for every multiset of natural numbers, including empty multisets and zero entries, by `D5.S1.Words.Compositions.WisemanA388712.sorted_choosable_iff_superdiagonal`.
2. **Proved, kernel-checked:** A388712 follows by negating that equivalence and retaining the common number-of-parts filter, by `D5.S1.Words.Compositions.WisemanA388712.result`.
3. **Proved in prose:** A387118 follows without a further statistic. For every partition $p$, the pointwise theorem gives $\neg C(p)\leftrightarrow\neg S(p)$. Hence the subsets $\{p\mid\neg C(p)\}$ and $\{p\mid\neg S(p)\}$ of the same finite set of partitions coincide and have equal cardinalities. This consequence is not a separate kernel-checked declaration in this delivery.
4. **Proved in prose:** A388713 follows with the common maximum-part condition. For each $p$, $M(p)=k\land S(p)\leftrightarrow M(p)=k\land C(p)$ by the reverse pointwise equivalence, so the two finite filters and their cardinalities agree. Here $M(p)$ is the multiset supremum. The empty partition has maximum zero and contributes 1 to each count at $(0,0)$; the printed source triangle instead has 0 there. The identity survives this common convention. This consequence is not a separate kernel-checked declaration in this delivery.
5. **Computed:** the pinned checker exhausts positive partitions through $n=22$, verifies the pointwise equivalence and matches all three published prefixes at the exact scopes in the finite-comparison entry; `python3 check.py 22`, exit 0, script SHA-256 as above.
6. **Computed:** replacing weak superdiagonality by strict superdiagonality or subdiagonality fails on the listed small examples. The finite-comparison entry specifies the command, script identity, exit 0 and tested lists $[1]$, $[2]$, $[1,1]$.
7. **Open:** no new settlement is claimed for A388724, A387880 or other neighbouring conjectures. The altered predicates above do not follow from this equivalence.
8. **Open as a separately formalized corollary:** the arbitrary-statistic counting theorem is not separately declared or kernel-checked here. The prose filter argument explains the two sibling refinements; the A388712 refinement is kernel-checked.

### What the settlement shows

The decisive mechanism is equality of predicates on each individual partition, transported between its two sort orders. It needs neither positive entries nor nonemptiness at the multiset level. Positive parts enter only through `Nat.Partition`. Negation and a shared filter preserve the equivalence. The two prose consequences above identify the total and maximum-part refinements; the strict and subdiagonal examples show why changing the predicate is outside this mechanism. The source material quoted in #18601 identifies no further dependent theorem; no additional source dependency is certified here.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are `ASSUMED-UNVERIFIED`. The preregistration records source, repository and public Lean-index searches; it is not an exhaustive search of all mathematical literature. The four-slot escape audit remains unfinished at #22068. The finite computation establishes only its stated ranges and prefixes. Neither the two prose consequences nor the arbitrary-statistic explanation is represented as an additional Lean theorem in this delivery.
