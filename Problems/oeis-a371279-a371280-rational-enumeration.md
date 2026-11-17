---
slug: oeis-a371279-a371280-rational-enumeration
bibkey: kimberling2024a371279a371280
doi: null
url: https://oeis.org/A371279
triage: theorem
motivation_gids:
  - D5/S3/Arith/CounterSequences/KimberlingA371279.result
---

# Kimberling's first-retention enumeration of rational numbers

## Problem

Clark Kimberling, OEIS A371279 and A371280, states:

> Conjecture: every rational number in the interval (0,1] occurs exactly once in T.

The complete source rule is:

> Starting with g(1) = (1), write the numbers in the ordered union of g(1), g(2), ..., g(n) as (x(1),x(2),...,x(m)). Then for i = 1..m, write x(i)/(1 + x(j)) for j = 1..m, and expel all the numbers that have previously occurred. The result is ordered union of g(1), g(2), ..., g(n+1).

### Exact model and statement correspondence

Work over exact rational numbers. Put $U_1=g_1=[1]$. For every positive
$n$, form $P_n=[x_i/(1+x_j)]_{i=1,\ldots,m;\ j=1,\ldots,m}$ from the
entire cumulative list $U_n=[x_1,\ldots,x_m]$, with $i$ outermost and $j$
innermost, including $i=j$. Retain the first occurrence of each value in
$U_n$ followed by $P_n$, without reordering, to obtain $U_{n+1}$. Its new
suffix is $g_{n+1}$. Let $T$ concatenate every $g_n$ in order.

For every rational $r$ with $0<r\le1$, there exists exactly one positive
pair $(n,k)$ with $1\le k\le |g_n|$ and $g_n[k]=r$. There is no generation
cutoff or restricted pairing rule. Lean's `cumulative 0` is $U_1$,
`generation n` is $g_n$ for positive $n$, and `Occurs` enforces both positive
indices and a valid optional lookup. `fraction 0` is the first flattened
entry. `flatIndex (n,k)+1` is its one-based source position.

A371279 and A371280 are the canonical reduced numerator and denominator
arrays of this same $T$. Neither coordinate is asserted individually unique.
A371353 is a positions cross-reference, not a second problem.

## Motivation

The enumeration connects an explicit ordered rational operation with every
rational in $(0,1]$. Its finite-prefix and position bridges make the source
arrays interpretable as coordinates of one infinite sequence. This supplies
an exact enumeration theorem, with no efficiency or complexity guarantee.

## Gap

The formal obligation is coverage and uniqueness for the complete infinite
source process, together with the literal update and coordinate bridges.
Finite observations alone do not imply coverage. The Library note fixes the
original OEIS clauses and an immutable official data mirror. The independent
source review found no exact supplier in its bounded repository, pinned
Mathlib and external Lean searches. Those searches establish neither
exhaustive literature coverage nor priority. The denominator-induction route
is attributed to the supplied GPT Pro search candidate; no independent
discovery or difficult-research claim is made.

## Route

A left-to-right seen-value scan implements first retention. `source_update`
identifies the prefix-plus-fresh-suffix update with `eraseDups` of the full
concatenation. The cumulative lists are duplicate-free and nested.

Strong induction on a positive denominator $q$ covers every $p/q$ with
$1\le p\le q$. The seed covers $p=q$. For $p<q$, if $2p\le q$, the allowed
diagonal pair at $p/(q-p)$ produces $p/q$; otherwise the pair
$(1,(q-p)/p)$ produces $p/q$. Each recursive denominator is smaller, and
nesting puts both inputs into one common actual cumulative list. Canonical
rational numerator/denominator representation transfers this to every target
rational. Fresh suffixes exclude all older values, and each suffix is
itself duplicate-free, proving uniqueness of both position coordinates.

Unbounded coherent finite prefixes define the infinite reading. The
position-to-flat and unique-owner bridges identify its entries; injectivity
and the reduced coordinate identities follow in the complete `result`.

## Falsifier

A rational $0<r\le1$ absent from every valid source position would refute
coverage. Two distinct valid position pairs containing the same $r$ would
refute uniqueness. A disagreement between the retained update and the literal
source concatenation, between finite prefixes and the infinite reading, or
between that reading and its reduced numerator/denominator records would
refute the corresponding bridge. The theorem ranges over all such inputs.

## Evidence

The formal source is `D5/S3/Arith/CounterSequences/KimberlingA371279.lean`.
Its public `source_update` proves the literal retention identity; `result`
contains all ten clauses, including the original universal exactly-once
statement and the infinite coordinate bridge. Its Blueprint Scribe displays
the definitions, source update and complete result. The axiom closure of
every public declaration is contained in
`{propext, Classical.choice, Quot.sound}`; no new axiom or `sorry` is used.

The source-faithfulness/form review is independent of the mathematical
producer. The Reg mirror retains compiled source-family evidence for both
public theorems. Neither registration is `declared_validated`: the
`source_update` binding reports `residual_requires_open/unclassified_form`,
and `result` reports `source.selection_missing`. The unfinished audits are
tracked at https://github.com/the-omega-institute/trureturing/issues/29606
under the CLAUDE section 3.9 linked-issue exception.

## Triage

- **Proved:** the full literal cumulative update and first-retention order,
  by `source_update` and the first conjunct of `result`.
- **Proved:** every rational in $(0,1]$ occurs at exactly one positive
  generation/index position, with no finite cutoff, by `result`.
- **Proved:** ordered finite flattening, unbounded prefixes, coherent infinite
  reading, the bidirectional position ownership bridge and injectivity,
  by `result`.
- **Proved:** A371279/A371280's interpretation as reduced numerator and
  denominator coordinates of this same reading, by `result` and the literal
  `numerator`/`denominator` definitions; no separate coordinate uniqueness.
- **Unverified:** the published finite digits, reported generation
  cardinalities, numeric A371353 positions and Mathematica execution.
  No computation is claimed for these items.
- **Unresolved:** the two registration binding audits in issue #29606.
  Their unfinished status does not change the kernel-checked theorem.

## ASSUMED-UNVERIFIED

The original OEIS finite data and the source program's execution are not
certified by this theorem. A371353's numeric sequence is not a separately
proved claim. Global literature completeness, originality, computational
complexity and empirical applications are not established. Registration
completion, independent post-publication three-seat approval, required CI
and delivery are separate obligations; mathematical proof alone does not
certify them.
