---
slug: wiseman388-partitions
bibkey: oeis2025wisemanpartitions
doi: null
url: https://oeis.org/A388712
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/WisemanA388712
  - D5/S1/Words/Compositions/WisemanA387118
  - D5/S1/Words/Compositions/WisemanA388713
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

This dossier records the three externally named OEIS conjectures with admission bases `open-problem-resolution (#18601; Proved)`, `open-problem-resolution (#18602; Proved)`, and `open-problem-resolution (#18603; Proved)`. The delivered conclusions are kernel-checked and bind-only; no escape witness is claimed. The source is documented in `Library/PermutationPatterns/oeis2025wisemanpartitions.md`.

## Gap

The frozen `ChoosableInitialIntervals` owner supplies permutation invariance and the increasing-list criterion. The three delivered modules apply that pointwise equivalence under negation, with a common number-of-parts filter, with no further statistic, and with a common maximum-part filter. The distinct-representative criterion is not claimed as a new theorem here. Completeness of the literature screen is `ASSUMED-UNVERIFIED`.

## Route

`ChoosableInitialIntervals.choosableInitial_congr_perm` transports choosability between the descending and ascending multiset sorts. `ChoosableInitialIntervals.choosableInitial_iff_superdiagonal` applies to the ascending sort. Their composition is `WisemanA388712.sorted_choosable_iff_superdiagonal`. Negation preserves this equivalence, and adjoining the same part-count condition gives identical finite filters. `WisemanA388712.result` concludes equality of their cardinalities. These are actual imported proof dependencies.

## Falsifier

A multiset for which choosability of its descending sort differs from weak superdiagonality of its ascending sort would contradict the pointwise theorem. A pair $(n,k)$ with different count values would contradict `result`. Neither theorem has a finite cutoff. Strict superdiagonality and subdiagonality are different predicates and do not satisfy the same pointwise statement.

## Evidence

The delivered mathematical modules are `D5/S1/Words/Compositions/WisemanA388712.lean`, `WisemanA387118.lean`, and `WisemanA388713.lean`. Their public declarations are bind-only: the shared pointwise helper is used by all three settling results, and each result is a live consumer of that helper. The Blueprint Scribes expand the equalities rather than displaying only the names `claim`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The escape audit is unfinished for the four public theorems; [#22068](https://github.com/the-omega-institute/trureturing/issues/22068) records the missing typed infinite-family source reconstruction, equivalence bridge, enrolled readout, intervention/sensitivity and observational-dependence evidence. No `declared_validated` registration is claimed.

The GPT Pro search contribution (Nyx broker task `0b18b509-0582-4147-96a3-bfda5936001f`) checked the three preregistrations, the imported owner, pinned Mathlib and relevant literature. It found Hall's finite representative criterion, its Lean formalization, and the 2025 superdiagonal-partition enumeration as prior context; it found no prior settlement of these three OEIS identities in the searched scope. Its reasoning confirms that the shared pointwise equivalence survives negation and common filters, and flags the A388713 empty-partition row-zero convention. The broker did not run Lean or the finite computation.

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
3. **Proved, kernel-checked:** A387118 follows without a further statistic by `D5.S1.Words.Compositions.WisemanA387118.result`; negation of the shared pointwise equivalence gives equal finite filters.
4. **Proved, kernel-checked:** A388713 follows with the common maximum-part condition by `D5.S1.Words.Compositions.WisemanA388713.result`. **Proved in prose:** the unique partition of zero is empty; both predicates hold vacuously and its totalized supremum is zero, so it contributes $1$ to each formal count at $(0,0)$. The printed source row is $0$.
5. **Computed:** the pinned checker exhausts positive partitions through $n=22$, verifies the pointwise equivalence and matches all three published prefixes at the exact scopes in the finite-comparison entry; `python3 check.py 22`, exit 0, script SHA-256 as above.
6. **Computed:** replacing weak superdiagonality by strict superdiagonality or subdiagonality fails on the listed small examples. The finite-comparison entry specifies the command, script identity, exit 0 and tested lists $[1]$, $[2]$, $[1,1]$.
7. **Open:** no new settlement is claimed for A388724, A387880 or other neighbouring conjectures. The altered predicates above do not follow from this equivalence.
8. **Open as a separately formalized corollary:** the arbitrary-statistic counting theorem is not separately declared or kernel-checked here. The prose filter argument explains the two sibling refinements; the A388712 refinement is kernel-checked.

### What the settlement shows

The decisive mechanism is equality of predicates on each individual partition, transported between its two sort orders. It needs neither positive entries nor nonemptiness at the multiset level. Positive parts enter only through `Nat.Partition`. Negation and shared filters preserve the equivalence, including the total and maximum-part refinements. The strict and subdiagonal examples show why changing the predicate is outside this mechanism. The source material quoted in #18601, #18602 and #18603 identifies no further dependent theorem; no additional source dependency is certified here.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are `ASSUMED-UNVERIFIED`. The preregistrations record source, repository and public Lean-index searches; they are not exhaustive searches of all mathematical literature. The four-slot escape audit remains unfinished at #22068. The finite computation establishes only its stated ranges and prefixes. The arbitrary-statistic extension is not represented as an additional Lean theorem in this delivery.
