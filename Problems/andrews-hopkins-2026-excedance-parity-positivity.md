---
slug: andrews-hopkins-2026-excedance-parity-positivity
bibkey: andrewshopkins2026excedances
doi: 10.48550/arXiv.2611.00435
url: https://arxiv.org/abs/2611.00435v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation
---

# Andrews–Hopkins excedance parity positivity

## Problem

George Andrews and Brian Hopkins, *Excedances and Deficiencies of Integer
Partitions*, arXiv:2611.00435v1, Section 2, immediately after Corollary 7
and Table 1 (HTML anchor S2.p7.1), state:

> Computations suggest that the difference remains positive for n ≥ 12.

This is a published numerical belief, without a formal Conjecture label.
For every natural n, let P(n) be all finite weakly decreasing lists of
positive integers summing to n. For λ in P(n), let exc(λ) count the
one-based indices i with 1 ≤ i ≤ length(λ) and λᵢ > i. Write E(n) and
O(n) for the cardinalities with even and odd exc, respectively. The exact
assertion is: for every natural n ≥ 12, E(n) > O(n).

The carrier retains every repeated part. Equality λᵢ = i is excluded
from excedances. Table 1 explicitly uses even count minus odd count;
its n = 12 entries are 40, 37 and 3. The printed Corollary 7 even/odd
generating-function labels are inconsistent with its displayed difference.
The original statistic and Table 1 fix the target convention; none of
those generating-function identities is assumed by the refutation.

## Motivation

This tier-one target is an explicit unrestricted numerical belief in a
recent partition paper. It asks whether initial parity bias persists for
every later integer. One certified counterexample settles precisely this
universal assertion.

## Gap

The inspected source supplies initial values through n = 15 and no proof
of the universal belief. The bounded source and prior-answer screen in
[preregistration #28251](https://github.com/the-omega-institute/trureturing/issues/28251)
found no whole prior answer in its successfully inspected scope. The
exact-title arXiv search returned only this source; a related-statistic
query returned an unrelated abstract. OpenAlex source metadata reported
zero citations, but actual citing-work enumeration and Semantic Scholar
were rate-limited; MathDB was inaccessible. Those unavailable surfaces
are not evidence of absence. No worldwide openness or priority follows.

## Route

The Lean claim uses the full Nat.Partition n carrier, decreasing multiset
sorting, and cardinalities of its actual even and odd subtypes. A recursive
generator of positive decreasing lists is proved sound, complete and
duplicate-free. Positivity proves that every partition of n has length at
most n, so fuel n imposes no extra restriction. Sorted-list uniqueness
makes the conversion to Nat.Partition injective. The original Fin-indexed
statistic is transported exactly through this conversion.

The complete filtered cardinalities at n = 28 are E(28) = 1850 and
O(28) = 1868. Since 12 ≤ 28 and 1850 < 1868, the literal theorem
`result : ¬ claim` refutes the original assertion. These are full carrier
counts, with no recurrence proxy, sampling or assumed numerical answer.

## Falsifier

A counterexample outside the original carrier or a statistic differing
from λᵢ > i would not refute this assertion. The soundness, completeness,
duplicate-freedom and statistic-preservation proofs close those specific
obligations. A proof of the unchanged universal assertion would contradict
the kernel-checked negation.

## Evidence

- Source: [versioned primary HTML](https://arxiv.org/html/2611.00435v1),
  Section 1 and Section 2 after Corollary 7/Table 1; CC BY 4.0.
- Preregistration: [#28251](https://github.com/the-omega-institute/trureturing/issues/28251);
  the unchanged [strict truth forecasts](https://github.com/the-omega-institute/trureturing/issues/28251#issuecomment-6727538574)
  precede mathematical execution.
- Lean: `D5/S3/Combinatorics/Partitions/AndrewsHopkinsExcedanceParityRefutation.lean`,
  with `claim : Prop`, the private consumed `actual_counts28`, and
  the public `result : ¬ claim`. The compiled closure consists of
  `Classical.choice`, `Quot.sound` and `propext`.
- The corresponding Blueprint Scribe binds its Refuted resolution claim
  to this same result. The [Library note](../Library/PermutationPatterns/andrewshopkins2026excedances.md) records the source sign caveat.

The public result is the designated refutation result (`basis=refutes`)
and is exempt from four-slot escape registration (CLAUDE.md §3.9).
There is no other authored public theorem in the module.

## Triage

`theorem`. Admission basis: open-problem-resolution (#28251; Refuted).
The result settles the exact published suggested universal positivity
belief, under its original one-based statistic and table convention.

### What the settlement shows

- **Proved in the module:** at n = 28 the odd class exceeds the even
  class by 18. Initial positive differences do not extend to the asserted
  all-n strict inequality. The same counterexample also rules out its
  non-strict E(n) ≥ O(n) variant with the same threshold.
- **Source reading:** the inspected paper states this belief after
  Corollary 7; its later proofs do not use universal positivity as a
  hypothesis. Refuting the belief supplies no refutation of those proofs.
  The generating-function sign/label inconsistency is a separate source
  issue, and the proof here relies on actual partition counts.
- **Open:** a structural explanation of the later sign pattern, an
  eventual-sign theorem, infinitely many sign changes, and a replacement
  threshold are not established by this finite counterexample. They are
  separate research questions, without new declarations in this module.

## ASSUMED-UNVERIFIED

The literature screen is bounded; inaccessible citation and MathDB
surfaces remain unverified. No worldwide first solution or globally least
counterexample is claimed. No general asymptotic sign assertion follows
from the n = 28 certificate.
