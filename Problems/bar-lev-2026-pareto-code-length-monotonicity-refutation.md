---
slug: bar-lev-2026-pareto-code-length-monotonicity-refutation
bibkey: barlev2026blockretrieval
doi: 10.48550/arXiv.2603.17154
url: https://arxiv.org/html/2603.17154v2
triage: theorem
motivation_gids:
  - D5/S3/Resource/MinimumRetrievalTime.result
---

# The finite-length Pareto conjecture

## Problem

Bar-Lev, arXiv:2603.17154v2, Section VII-A, Conjecture 2, asks whether every
rank-`k` length-`n` code over `F_q` admits a rank-`k` length-`n+1` code with
both actual expected file-retrieval times no larger, whenever `n>=k`,
`s1,s2>0`, `s1+s2=k`, and `max(s1,s2)>=2`. The expected time is the minimum
number of independent uniform-with-replacement draws required for the
sampled columns to span the whole coordinate file. Issue #11618 fixes this
target before the proof probe.

## Motivation

The arbitrary-successor Pareto question asks whether increasing code length
can preserve both files' retrieval performance simultaneously. Its value
lies in quantifying over every legal successor, rather than restricting
the successor to appending a column or reproducing an exact pair.

## Gap

There is no remaining mathematical gap in the full Lean refutation.
The escape audit remains unfinished under issue #11659. Freezing and
admission are separate from the mathematical result and do not replace
merged delivery.

## Route

### Counterexample

Take `k=3`, `n=4`, file dimensions `(1,2)`, and generator columns
`e0,e0,e1,e2` over `F_2`. The old expectations are exactly `(2,6)`:
the first file requires a draw from the two physical `e0` indices; the
second requires both singleton physical indices `e1` and `e2`.

For every rank-three five-column successor, either its first expectation
is strictly larger than `2` or its second expectation is strictly larger
than `6`. This obstruction is proved over an arbitrary field, so allowing
a different finite field would not rescue this particular witness.
The binary specialization suffices to negate the published universal
assertion. No zero or duplicate columns are discarded.

### Universal exclusion

Project along `e0` to the `e1,e2` coordinate plane. Full rank ensures two
projected columns are linearly independent. Choose their physical indices
`left,right`.

If every other projected column is zero, recovering the second file
requires seeing both `left` and `right`. The probability of missing at
least one after `t` draws is `2(4/5)^t-(3/5)^t`. Summing only `t=0,...,8`
already gives `2415241/390625>6`.

Otherwise choose a third physical index with nonzero projection. Its
column cannot alone span `e0`. Independence excludes recovery of `e0`
from the `left,right` pair, and a linear relation shows at least one
third-containing pair also fails. These two bad pairs share an index.
At every `t`, words confined to either pair give failure probability at
least `2(2/5)^t-(1/5)^t`. The Lean certificate sums `t=0,...,4`, giving
`1281/625>2`.

The two branches are exhaustive without enumeration, normalization of
column positions, or a permutation-invariance premise. The inequalities
are connected to actual stopping-time integrals by the probability bridge.

## Falsifier

The refutation fails to settle the literal target if its source contract
misstates the published field domain, file dimensions, rank condition, or
successor quantifiers, or if its probability bridge does not describe the
actual minimum iid uniform-with-replacement stopping-time expectation.
An allowed successor weakly dominating the stated old code would refute
the universal exclusion. These are source, semantics, and quantifier
failure criteria, not a change to the preregistered target.

## Evidence

The canonical result is `D5/S3/Resource/MinimumRetrievalTime.result :
not claim`. The source contract includes finite fields, full matrix rank,
positive file sizes, the exact coordinate files, all legal old generators,
and unrestricted successors. The result is a source-faithful refutation,
not an append-only obstruction or a failure of exact-pair reproduction.

The six reusable probability and obstruction theorems have substantive
probability/geometric content. The final theorem composes that content
with the binary witness and the complete quantified claim. Its intended
admission basis is `open-problem-resolution`, preregistration #11618;
the auxiliary theorems use `escape-witness` admission. All same-delivery
helpers must be inlined when assessing proof shape.

The escape audit is unfinished. The mirrored Reg source proves the
counterexample bridge, law variation, and slot sensitivity using the
enrolled `counterexampleRealization` template. The existing E2 classifier
reports `E2.unknown_constant` at `FiniteFieldModel` for the final result,
with a null certificate and classification `declared_unresolved`. The six
generic probability and obstruction declarations separately require their
full-telescope bridges, actual laws, whole-family variation, sensitivity,
observational dependence, and current source-binding evidence; the final
result's diagnostic does not establish their classifications. The source-bound
probability-bridge registration is `declared_validated`. The old-code,
three-kernel, bad-pairs, and projected registrations have compiled audit
proofs but are `declared_unresolved`, with null certificates and the separate
`source.unsafe_or_external` diagnostic at `Nat.mul`. The universal
obstruction has a compiled full-telescope law, actual realization, variation,
observational dependence, and source selector, but no registration record:
its whole-family rejected realization changes both readouts, whereas
per-role sensitivity must hold the other readout fixed. Those sensitivity
proofs and its current source-binding evidence remain unfinished.
[Issue #11659](https://github.com/the-omega-institute/trureturing/issues/11659)
tracks this unfinished audit under the registration-obstacle exception.
Issue #11618 is the distinct mathematical preregistration. No judge change
is part of this result.

## Triage

The candidate is a theorem: a full Lean refutation of the literal
Conjecture 2. No merged KPI or novelty claim is made. The unfinished audit
and delivery obligations remain as stated above.

## ASSUMED-UNVERIFIED

The source and scoped title/id searches establish only bounded negative
literature evidence, not a global priority certificate. Priority, normal
admission, freezing, and merged delivery are separate from the
kernel-checked mathematical refutation.
