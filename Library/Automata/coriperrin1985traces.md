---
bibkey: coriperrin1985traces
authors: Robert Cori, Dominique Perrin
year: 1985
title: Automates et commutations partielles
doi: 10.1051/ita/1985190100211
claim: Proposition 1.1 characterizes partial commutation by ordered projections onto dependent pairs.
strata_touched:
  - D5/S1/Words/TraceProjection
license: citation-only
triage: anchor
---

# Automates et commutations partielles

Robert Cori and Dominique Perrin, *Automates et commutations partielles*,
RAIRO Informatique theorique **19** (1), 21–32 (1985).
The unique DOI is [10.1051/ita/1985190100211](https://doi.org/10.1051/ita/1985190100211).
The [publisher's source](https://www.numdam.org/item/ITA_1985__19_1_21_0/)
locates Proposition 1.1 on printed page 23 and its complete proof on page 24.
The inspected source PDF has SHA-256
`ed93e2e1693dcf2e3f417de89acdd39026c10e047a3ffa2fe95f7301f1e1a9aa`.
This note redistributes no PDF or source text.

The paper works with a finite alphabet and a reflexive symmetric commutation
relation. For the irreflexive independence relation `I` used in the associated
Lean module, the corresponding reflexive relation is
`theta(a,b) := a = b or I(a,b)`. The ordered two-letter projections retain the
relative order of dependent letters. Diagonal projections additionally record
the multiplicity of each letter; omitting them loses information even for
one-letter words.

The Lean statement quantifies over an arbitrary alphabet in every universe and
over native finite lists, including the empty alphabet, empty words, and repeated
letters. It assumes only symmetry and irreflexivity of `I`. Its swap relation
independently permits an adjacent exchange in arbitrary unchanged left and right
contexts, and its observation is a native list filter. No occurrence matching,
partial order, linear extension, or swap schedule is an input.

The recovery argument selects the first target occurrence of the source head.
If a preceding letter were dependent on that head, their two-letter projection
would begin with the wrong letter. Thus every preceding letter commutes with
the head. Moving the head across that prefix preserves every dependent-pair
projection, and cancellation leaves the residual observation equality needed
for induction. This finite-word argument requires no finite ambient alphabet.
The associated result is an implementation of established trace mathematics;
no originality, operational complexity, or effective reconstruction bound is
asserted.

## Verified locator

- DOI: https://doi.org/10.1051/ita/1985190100211
- Publisher: https://www.numdam.org/item/ITA_1985__19_1_21_0/
- Proposition 1.1 on printed page 23; proof on page 24.
