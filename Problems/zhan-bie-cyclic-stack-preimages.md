---
slug: zhan-bie-cyclic-stack-preimages
bibkey: zhanbie2026cyclicstack
doi: 10.5281/zenodo.18154216
url: https://math.colgate.edu/~integers/aa15/aa15.pdf
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence
---

# Zhan–Bie consecutive cyclic-stack fibres

## Problem

Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26
(2026), A15, Conjectures 3 and 4 on page 12 ask for the complete fibre of the
consecutive cyclic `[123]` stack map. Write the stack top-first. For an
incoming value `x` and top entries `a,b`, pop `a` exactly when
`x<a<b`, `b<x<a`, or `a<b<x`; repeat until pushing `x` is allowed.
Read the input left-to-right and flush the remaining stack top-first.
The definition and Figure 3 on page 4 fix this orientation by `3124 -> 4213`.

For every integer `n >= 4`, let `m=floor(n/2)`, let
`y_n=(1,...,m,n,...,m+1)`, and let `S_n` contain every permutation of
`1,...,n`. The two claims are

`|{p in S_n : cyclicStackSort(p)=y_n}| = 1` for every even `n >= 4`,

`|{p in S_n : cyclicStackSort(p)=y_n}| = ceil(n/2)` for every odd `n >= 4`.

Equivalently, for every natural `m >= 2`, the cardinalities at `2*m` and
`2*m+1` are `1` and `m+1`. There is no additional condition on the input
beyond being a permutation, and no finite upper bound on `n`.

## Motivation

Exact enumeration of pattern-constrained objects requires both a construction
and a converse classification. The frozen graph-avoidance recurrence in
the motivation GID supplies this methodological connection: a literal
source domain is counted through an explicit structural decomposition.
It is not a theorem dependency or a claim that graph avoidance and stack
avoidance are the same operation.

## Gap

The primary article states the two counts as conjectures. Constructing one
even preimage and `m+1` odd preimages alone does not exclude other
permutations. The full converse must determine the chronological high
entries even when the empty odd gap is not final. The repository proof
addresses both the final-empty-gap and final-low cases.

## Route

Put `m=floor(n/2)`. Successful inputs start high and have at most one low
after each high. A high cannot be emitted before any low still due in the
target; this barrier forces the lows to occur in increasing order.
Permutation preservation identifies them as `1,...,m`.

At size `2*m` every high gap is filled. The highs increase, giving the
unique word `(m+1,1,m+2,2,...,2*m,m)`. At size `2*m+1` exactly one of the
`m+1` high gaps is empty. If it is final, the filled-gap invariant orders
the highs. Otherwise the word ends low; the final stack contains the
reversed chronological high sequence, which must be the reversed complete
high range. In both cases the highs are `m+1,...,2*m+1` in order.

Conversely, omit any one of the gaps after these odd highs and fill the
others with `1,...,m` in order. Each word produces the target, and decoding
the empty gap distinguishes all `m+1` words. The full fibre, defined
independently by filtering all permutations, therefore has the stated size.

## Falsifier

An admissible permutation producing the target outside these normal forms,
a normal-form word failing to produce the target, or two different omitted
gaps producing the same word would refute the classification route. A
different top/bottom orientation, nonconsecutive pattern test, or failure
to retest after each pop would invalidate the source-to-formal mapping.

## Evidence

The five Lean modules `CyclicStackPreimagesCore`,
`CyclicStackPreimagesCandidates`, `CyclicStackPreimagesInvariants`,
`CyclicStackPreimagesFinalLow`, and `CyclicStackPreimages`, all under
`D5/S1/Words/Patterns/`, contain the literal map and symbolic all-size proof.
The public result is
`D5/S1/Words/Patterns/CyclicStackPreimages.zhan_bie_conjectures_3_4`.
Its statement quantifies `m : Nat` with `2 <= m` and proves both equalities
without assuming the classification. The fibre uses all permutations of
`List.range' 1 n`, not a candidate enumeration.

The source identity and declaration mapping are in the Library note.
The primary PDF SHA-256 is
`874a257ffcfa64e0ede1c8e1f3c502c5d456d463610f021a89ec30a3536b55a3`.
The mathematical statement and proof are also presented by the matching
Scribe documents. The problem source is external; the proof is
repository-derived.

## Triage

`theorem` denotes the target class, and the problem belongs to the recent
published-conjecture tier. Both conjectures are addressed in their full
`n >= 4` scope. This dossier makes no typed resolution claim: first Freeze
and its independent quality and admission obligations remain separate.

## ASSUMED-UNVERIFIED

The earlier bounded prior-resolution and Lean-library searches are
caller-supplied; issue #8660 is the supplied preregistration locator.
These searches do not certify absence of a
proof in all literature. No worldwide priority is claimed. Independent
review of source fidelity and helper admission, first Freeze, and required
delivery checks remain obligations outside this mathematical dossier.
