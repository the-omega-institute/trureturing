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
- Mathematical locators: Figure 3 and Conjectures 3 and 4.
- Repository preregistration: issue #8660.
- Locally checked PDF SHA-256:
  `874a257ffcfa64e0ede1c8e1f3c502c5d456d463610f021a89ec30a3536b55a3`.

The source states these cardinalities as conjectures; it does not supply the
all-size inverse classification proved by the repository theorem.
