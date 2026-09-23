---
bibkey: zhanbie2026cyclicstack
authors: Alex Zhan and Stella Bie
year: 2026
title: Cyclic-Pattern-Avoiding Stacks
doi: 10.5281/zenodo.18154216
url: https://math.colgate.edu/~integers/aa15/aa15.pdf
claim: "Conjectures 3 and 4 give the exact full fibre over the layered target for the consecutive cyclic [123]-avoiding stack: cardinality one in even size and ceiling(n/2) in odd size, for every n at least four."
strata_touched:
  - D5/S1/Words/Patterns/CyclicStackPreimagesCore
  - D5/S1/Words/Patterns/CyclicStackPreimagesCandidates
  - D5/S1/Words/Patterns/CyclicStackPreimagesInvariants
  - D5/S1/Words/Patterns/CyclicStackPreimagesFinalLow
  - D5/S1/Words/Patterns/CyclicStackPreimages
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Words/zhanbie2026cyclicstack -->

# Cyclic-pattern-avoiding stacks

Zhan and Bie study deterministic stacks that avoid a set of consecutive
patterns. For the cyclic set `[123] = {123, 231, 312}`, an incoming entry is
handled by repeatedly popping the existing top entry whenever the incoming
entry and the top two stack entries, read from incoming to deeper stack,
realize one of those three patterns. The incoming entry is then pushed, and
the residual stack is flushed from top to bottom after the input is exhausted.

Figure 3 calibrates this convention by mapping `3124` to `4213`. This rules
out readings that test a nonconsecutive stack pattern, reverse the stack
orientation, or pop more than the shortest forced prefix at one time.

For `m = floor(n/2)`, Conjectures 3 and 4 concern the complete inverse image
of

`(1, 2, ..., m, n, n-1, ..., m+1)`

among all permutations of `(1, 2, ..., n)`. They assert that for every
`n >= 4` the fibre has cardinality `1` when `n` is even and
`ceil(n/2)` when `n` is odd. Equivalently, for every `m >= 2`, the respective
cardinalities at sizes `2m` and `2m+1` are `1` and `m+1`.

## Verified locator

- DOI: https://doi.org/10.5281/zenodo.18154216.
- Journal: *INTEGERS* 26 (2026), article A15.
- Volume index: https://math.colgate.edu/~integers/vol26.html, entry A15.
- Article PDF: https://math.colgate.edu/~integers/aa15/aa15.pdf.
- Authors and title: Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*.
- Mathematical locators: the consecutive-stack definition and Figure 3 on
  page 4; Conjectures 3 and 4 on page 12.
- Repository preregistration: issue #8660.
- Locally checked PDF SHA-256:
  `874a257ffcfa64e0ede1c8e1f3c502c5d456d463610f021a89ec30a3536b55a3`.

The source states these cardinalities as conjectures; it does not supply the
all-size inverse classification proved by the repository theorem.

## Source-to-formal mapping

The source convention is represented literally by `forbidden`, `drain`,
`process`, and `cyclicStackSort` in
`D5/S1/Words/Patterns/CyclicStackPreimagesCore.lean`. The three inequalities
are respectively `x < a < b`, `b < x < a`, and `a < b < x`, with `x` the
incoming value and `a,b` the top two existing stack entries. Each drain
retests after one pop; processing flushes the stack when input is empty.
The same module's `target n` uses integer division `n / 2` for the floor.

`fibre n` in `CyclicStackPreimagesCandidates.lean` filters
`(List.range' 1 n).permutations` by `cyclicStackSort input = target n`.
It does not filter the proposed candidates. The range has no duplicates,
and Mathlib's permutation enumeration and filtering preserve this fact,
so its list length is the cardinality of the complete source fibre.
The candidate family is used to prove lower bounds and the converse
classification, not to define the domain.

`CyclicStackPreimagesInvariants.lean` proves the gap and low-order
invariants. `CyclicStackPreimagesFinalLow.lean` identifies the high range
when the input ends low. `CyclicStackPreimages.lean` combines this with
the final-empty-gap case and proves
`zhan_bie_conjectures_3_4`: for every natural `m >= 2`, the lengths at
`2*m` and `2*m+1` are respectively `1` and `m+1`. These cases cover every
`n >= 4`, with the odd count equal to `ceil(n/2)`.

The definitions of the map, Figure 3, and the conjecture statements are
literature-attested. The barrier argument, inverse classification, and
proof of the counts are repository-derived; the source is acknowledged
without attributing that proof to the authors.

## Formal resolution binding

The Scribe description binds the joint theorem
`D5/S1/Words/Patterns/CyclicStackPreimages.zhan_bie_conjectures_3_4`
to `Problems/zhan-bie-cyclic-stack-preimages.md` with the typed resolution
`Proved`. Its immutable declaration statement ID is
`sha256:db5ab1d9a85662064ffdfe8a739232e53fc152542d42c244e79aa9280cd9bd87`.
The two conjuncts resolve Conjectures 3 and 4 in the full scope above.

This is a local formal binding. Required remote CI and integration of
PR #8705 into `dev`, together with prior-resolution and novelty accounting,
remain caller-owned obligations.

## Bounded prior-art and reuse scope

The earlier repository, pinned Mathlib, and admissible Lean-library searches
and the all-size proof design are caller-supplied prior evidence; issue
#8660 is the supplied preregistration locator. In the named local scope,
the exact conjecture theorem is the five-module implementation listed
above; Mathlib supplies the reused list permutation, no-duplicates,
ordering, and cardinality machinery. The primary article presents the two
claims as conjectures. Its bytes were independently fetched on 2026-09-20
with HTTP 200 and the SHA-256 above.

This is a bounded source and reuse statement. The earlier external
prior-resolution search is caller-supplied; no exhaustive absence of a
later proof or worldwide priority is asserted.
