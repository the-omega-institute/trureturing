---
slug: oeis-a378495-terminal-difference
bibkey: kagey2024a378495
doi: null
url: https://oeis.org/A378495
triage: theorem
motivation_gids:
  - D5/S3/Zeros/Convolution/PerfectMatchingCount.card_fixedPointFreeInvolution_mul
---

# The terminal difference of OEIS A378495

## Problem

The FORMULA field of OEIS A378495, revision 70, states verbatim:

> Conjecture: T(n,n-2) - T(n,n)   = (n-3)!*(n-4)*(n-1)/2 for n >= 5.

$T(n,k)$ counts all derangements in $S_n$ with no $k$-cycle,
$1\le k\le n$. The triangle is read by rows, with offset `1,5`.
Both cardinalities are cast to $\mathbb Q$ before ordinary subtraction;
the division by two is rational division.

### Statement echo

| Source clause | Exact formal counterpart |
| --- | --- |
| Every natural $n\ge5$ | `result (n : Nat) (hn : 5 <= n)`, with no upper bound |
| All permutations in $S_n$ | `Equiv.Perm (Fin n)`, relabelled from zero through $n-1$ |
| No fixed point | `D n` filters by `forall x, p x != x` |
| No $k$-cycle | `T n k` counts the filter by every cycle factor's support size differing from $k$ |
| Cycle-factor interpretation | Consumed `noCycle_iff` connects this predicate to cycle-type membership |
| Columns $n-2$ and $n$ | Exactly `T n (n-2)` and `T n n` |
| $(n-3)!(n-4)(n-1)/2$ | Natural factorial and natural index subtractions, then rational casts and division |
| No assumed counting identity | Only `5 <= n` is a hypothesis of `result` |

## Motivation

This is the tier-one externally published question preregistered in
[#23899](https://github.com/the-omega-institute/trureturing/issues/23899#issuecomment-6508953630).
The source is Peter Kagey's 2024 triangle, with the terminal formula
introduced in revision 60. The frozen motivation theorem above is a
related application of permutation cycle-type counting to perfect
matchings. It is an analogous mathematical anchor, not a dependency or
an asserted substitute for the present settlement.

## Gap

The exact mathematical gap is closed by
`D5.S3.Combinatorics.Derangements.TerminalDifference.result`.
The [source note](../Library/FiniteGroups/kagey2024a378495.md) records the
fixed-pin repository and bounded external searches. No exact prior
settlement was found in that successful scope. Kallat v1, section 9.2
and supplementary `sec:open`, does not settle this stronger identity.
OpenAlex search and Semantic Scholar HTTP 429 responses leave literature
coverage incomplete; absence of a result in those endpoints is not claimed.

## Route

Partition the actual finite set of derangements into permutations with
and without a $k$-cycle. The retained count plus the excluded count is
$|D(n)|$. Among derangements an $n$-cycle forces cycle type $\{n\}$,
and an $(n-2)$-cycle forces $\{n-2,2\}$ when $n\ge5$.
The latter follows because the remaining lengths sum to two and every
nontrivial cycle length is at least two.

Pinned Mathlib counts these cycle types: the excluded terminal count is
$(n-1)!$, while the other excluded count multiplied by $2(n-2)$ is $n!$.
Subtract the two partition equalities over $\mathbb Q$, expand factorials
and cancel the nonzero factor $n-2$. This gives
$T(n,n-2)-T(n,n)=(n-3)!(n-4)(n-1)/2$.
The lower bound justifies every natural subtraction and rational cast.
No finite positive table is used to infer the universal conclusion.

## Falsifier

A natural $n\ge5$ whose actual permutation cardinalities violate the
displayed rational equality would contradict the stated formal result.
A different triangle, a truncated natural subtraction between counts,
or an extra assumption on cycle multiplicities would change the question.

## Evidence

The independent scientific terminal is
[6509681032](https://github.com/the-omega-institute/trureturing/issues/23899#issuecomment-6509681032).
It accepts the original universal identity. Its compiled result statement
identity is `sha256:c63f5c740b67d90f69fd542bf3d6e5bd57e53b6f35910ac068920bcddf197a0a`.
The proof source is `D5/S3/Combinatorics/Derangements/TerminalDifference.lean`;
its typed descriptions and generated mirror are under the corresponding
Blueprint path. The accepted axiom closure is contained in
`Classical.choice`, `Quot.sound`, `propext`; no new axiom is introduced.

### Declaration form and actual consumers

Names below are relative to `TerminalDifference`; `Adjacent` means
`AdjacentDifferenceRefutation`. No declaration supplies an escape witness.

| Declaration | proof_shape | Live consumers |
| --- | --- | --- |
| `D` | definition; not applicable | `T`, `excluded`, `Adjacent.result` |
| `T` | definition; not applicable | `T_add_excluded`, `result`, `Adjacent.claim`, `Adjacent.result` |
| `excluded` | definition; not applicable | `T_add_excluded`, `excluded_terminal_card`, `excluded_penultimate_mul`, `result`, `Adjacent.result` |
| `noCycle_iff` | bind-only | `T_add_excluded` |
| `T_add_excluded` | bind-only | `result`, `Adjacent.result` |
| `noFixed_iff_sum` | bind-only | `terminal_cycleType`, `penultimate_cycleType`, `Adjacent.result` |
| `sum_two` | bind-only | `penultimate_cycleType` |
| `terminal_cycleType` | bind-only | `excluded_terminal_card` |
| `penultimate_cycleType` | bind-only | `excluded_penultimate_mul` |
| `excluded_terminal_card` | bind-only | `result` |
| `excluded_penultimate_mul` | bind-only | `result`, `Adjacent.result` |
| `result` | bind-only | Exact external question in #23899 |

`sum_two`'s induction hypothesis is unused in the compiled proof; it is
not an escape argument. The actual suppliers are the pinned Mathlib
cycle-type cardinalities, support identities and finite-set partition,
combined by logical decomposition and factorial/rational normalization.
There is no frozen project theorem on the terminal proof's dependency
path. The intended admission basis is `open-problem-resolution`, with
the exact preregistration above. Admission is pending independent
pre-freeze review and the later canonical doors and typed Proved claim.
This source is unfrozen; the dossier asserts no publication completion.

### Utility and unfinished audit

The module's utility classification is `none`: every definition describes
the full unbounded counting family, and every theorem is a general
structural or symbolic identity. No bounded enumeration, checker,
numeric reduction or certified finite instance is a delivered result.
The admission exception concerns the external named problem, not a
fabricated computational consumer or escape witness.

The nine public theorems in the table have an unfinished four-slot audit
under the concrete [section 3.9 issue exception](https://github.com/the-omega-institute/trureturing/issues/23899#issuecomment-6509479812).
The faithful design attempt inspected `Reg.Support.DependentFamily` and
its typed family contract. Missing are complete source reconstruction
and selection, an enrolled readout, and full-family realization,
variation, sensitivity and observational dependence for each target.
No compiling Reg source or `declared_validated` registration is claimed.
The linked issue permits the mathematical unit to proceed to review;
it does not discharge those audit obligations.

The first-event research readings remain unproduced: the existing
execution-start fence is rejected by the readout parser, as recorded in
[6509713581](https://github.com/the-omega-institute/trureturing/issues/23899#issuecomment-6509713581).
Missing counts are not zeros. The original pre-mathematics full native
closure ordering is unestablished. Neither limitation changes the
separate kernel-checked mathematical conclusion.

## Triage

### What the settlement shows

- **Proved:** the exact original terminal identity for every $n\ge5$,
  from actual cardinalities, with only the original lower bound.
- **Mechanism:** the two complete cycle types $\{n\}$ and $\{n-2,2\}$
  give a symbolic count and rational cancellation, rather than a table.
- **Computed:** no independent finite experiment is needed or credited
  for this universal identity.
- **Open:** extensions below five or a corrected adjacent shift are not
  settled here. The separate literal adjacent question has its own
  [refutation dossier](oeis-a378495-adjacent-difference.md).
- **Boundary:** pre-freeze review, canonical admission and publication
  remain pending; no delivery or discovery KPI follows from this dossier.

## ASSUMED-UNVERIFIED

Global literature completeness, novelty and priority are not established.
The source qualification is bounded, including the named HTTP 429 gaps.
Historical execution times are recorded workflow assertions supported
by unchanged server evidence, not recovered process telemetry.
The original pre-mathematics closure ordering remains unestablished.
The unfinished escape audit and unproduced research readings remain
explicit limitations; neither is claimed repaired or validated.
