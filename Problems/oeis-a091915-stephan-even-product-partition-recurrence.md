---
slug: oeis-a091915-stephan-even-product-partition-recurrence
bibkey: perry2004a091915
doi: null
url: https://oeis.org/A091915
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.result
  - D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.classicalMaximumProduct_isGreatest
---

# Stephan's A091915 maximum even partition-product conjecture

## Problem

OEIS A091915 states (`%N`, `%F`, `%A`, `%O`, and `%Y`, verbatim):

> %N A091915 Maximum of even products of partitions of n.
> %F A091915 For n>6, a(n+3) = 3a(n) (conjectured). - _Ralf Stephan_, Dec 02 2004
> %A A091915 _Jon Perry_, Feb 12 2004
> %O A091915 1,2
> %Y A091915 Cf. A000792, A091916.

The literal proved statement is

```lean
theorem result (n : ℕ) (hn : 6 < n) :
    ∃ a : ℕ,
      IsGreatest
          {q : ℕ | ∃ p : Nat.Partition n, Even p.parts.prod ∧ p.parts.prod = q} a ∧
        IsGreatest
          {q : ℕ | ∃ p : Nat.Partition (n + 3), Even p.parts.prod ∧ p.parts.prod = q}
          (3 * a)
```

For `n = 1`, no partition has an even product, so the feasible set is empty.
The existential formulation avoids assigning an arbitrary total-function value there:
for every `n > 6`, it supplies a greatest even product `a` at total `n` and proves that
`3*a` is the greatest even product at `n+3`. It retains attainment and the upper
bound through `IsGreatest`, rather than asserting only membership.

Not claimed here are any odd-product statement or result about A091916; any
generating-function form; any parity result about the number of partitions; an
exhaustive literature result or priority claim; or a greatest-even-product value
for an empty feasible set.

## Motivation

Ralf Stephan dated the conjecture December 2, 2004. From that date through the
September 15, 2026 check is 21 years, 9 months, and 13 days. Revision #12,
dated January 17, 2016 at 09:04:01, still marks the formula `(conjectured)`.
The nearby A091916 entry does not settle this problem: it concerns odd products
and has Ron Knott's March 18, 2020 closed forms, a generating function with
denominator `3*x^3-1`, and a linear-recurrence index entry with signature
`(0,0,3)`, while A091915 has none of those three.

## Gap

Apart from the conjectural `%F`, revision #12 contains two Mathematica programs
and one `%e`, but no closed-form `%F`, no `%H` link, no linear-recurrence index
entry, and no settlement comment. A000792's reference list covers the
unconstrained maximum-product theorem and other partition-norm variants; the
checked references state no parity-constrained recurrence.

Bercov and Moser, *On Abelian Permutation Groups*, DOI
`10.4153/CMB-1965-045-6`, is cited by A000792 for the abelian-subgroup
interpretation and concerns the unconstrained problem. The title-level ambiguity
in chapter 75 of Bollobás, *The Art of Mathematics - Take Two*, whose title is
literally "Partitions - Maximum and Parity", was resolved from the page-219
snippet: its subject is parity classes of partition counts `p_{o,e}(n)`,
`p_{e,o}(n)`, `p_{o,o}(n)`, and `p_{e,e}(n)` and their differences, not maximum
products.

OpenAlex autocomplete returned HTTP 200 and count 0 for each of `A091915` and
`maximum even product partition`. The full OpenAlex works endpoint returned
HTTP 429 because its daily budget was exhausted, so that endpoint was not
checked. Crossref queries `A091915 maximum even product partitions` and
`maximum product partition parity constraint` produced no relevant settlement
in the reviewed results. The arXiv queries `all:A091915` and
`all:"maximum even product" partition` both returned explicit no-results pages.
MathOverflow returned 0 items for `A091915` and for `"product of parts"`
partition maximum parity even`; its broader `maximum even product partition`
query returned 3 items, each inspected and unrelated. The resolved appendix of
the OEIS Open benchmark arXiv:2608.11941v2 lists 110 distinct A-numbers and
omits A091915. Code searches for `A091915`, `091915`, and `Maximum of even products`
in `epoch-research/LeanOpenProblems` were issued in two searches and returned 0.
These findings are `not-found-in-searched-scope`, not an exhaustive claim.

## Route

The unconstrained A000792 optimum is `3^k`, `2*3^k`, or `4*3^k`, according to
the residue class. For `n` congruent to 2 modulo 3, the optimum
`2*3^((n-2)/3)` is already even. For `n` congruent to 1 modulo 3 with `n >= 7`,
the optimum `4*3^((n-4)/3)` is already even. For `n` congruent to 0 modulo 3,
the unconstrained optimum `3^(n/3)` is odd; the constraint binds, and the sharp
value is `8*3^(n/3-2)`. Each closed form is multiplied by three after adding
three to `n`.

The public theorem `classicalMaximumProduct_isGreatest` proves the unconstrained
upper bound and constructs an attaining partition for every `n`. For the even
problem, pinned Mathlib's `Prime.exists_mem_multiset_dvd`, instantiated at two
using `Nat.Prime.prime Nat.prime_two`, extracts an even factor inline. Removing
that factor permits the unconstrained upper-bound argument to bound the remaining
parts, while `evenFactor_mul_classicalMaximumProduct_le` supplies the sharp
parity-sensitive estimate. Explicit witness partitions attain the recursive
bound. The non-reductive core is this three-branch extremal argument, especially
the residue-zero branch where the unconstrained optimum is unavailable.

## Falsifier

A natural `n > 6` for which the greatest even partition products at `n` and
`n+3` exist but the latter is not three times the former would contradict
`result`. A partition of some `n` whose parts have product larger than
`classicalMaximumProduct n`, or the failure of every partition of `n` to attain
that value, would contradict `classicalMaximumProduct_isGreatest`.

## Evidence

- Lean module:
  `D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.lean`.
- Public theorem `classicalMaximumProduct_isGreatest`: std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Public theorem `result`: std3 axiom closure `[propext, Classical.choice, Quot.sound]`.
- The three removed v1 bind-only recurrence declarations remain inlined at their
  consumers, and the v2 bind-only even-factor extraction is replaced by the
  pinned-Mathlib instantiation above; no named wrapper is present.
- Independently deleting each of
  `Mathlib.Combinatorics.Enumerative.Partition.Basic`,
  `Mathlib.Tactic.IntervalCases`, `Mathlib.Algebra.BigOperators.Associated`, and
  `Mathlib.Data.Nat.Prime.Defs` makes the module fail to compile with exit 1.
- The probe's independent exact-integer unbounded-knapsack partition dynamic
  program covered sums `0..6000`: 0 recurrence mismatches for `n = 7..5997`,
  0 mismatches against the three residue-class closed forms for `n = 2..6000`,
  and 0 mismatches against A000792 for `n = 0..6000`.
- It computed `EvenMax(1..14) =
  [null,2,2,4,6,8,12,18,24,36,54,72,108,162]`; the `n = 1` feasible set is
  empty, and residue-zero samples are `9 -> 24`, `12 -> 72`, and `15 -> 216`.
- The orchestrator's independent exact-integer check through `n = 3997`
  agrees term for term.
- The finite computations do not prove the universal theorem.

## Triage

`theorem`. The greatest even product of partition parts triples when the
partitioned integer increases by three after `n = 6`; the resolution is
`proved`, not `refuted`. The public classical theorem also settles the
unconstrained extremal prerequisite for every natural `n`.

## ASSUMED-UNVERIFIED

Literature completeness outside the bounded searches of A091915, A091916 and
A000792; the named Bercov-Moser paper and Bollobás chapter; OpenAlex
autocomplete; Crossref; arXiv; MathOverflow; arXiv:2608.11941v2; the two
`epoch-research/LeanOpenProblems` code searches; this repository; and pinned
Mathlib is unverified. The OpenAlex works endpoint was not verified because it
returned HTTP 429 after the daily budget was exhausted. No exhaustive literature
or priority claim is made. The finite exact-integer checks through `n = 6000`
and `n = 3997` do not establish the universal statement.
