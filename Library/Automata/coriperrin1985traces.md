---
bibkey: coriperrin1985traces
authors: Robert Cori, Dominique Perrin
year: 1985
title: Automates et commutations partielles
doi: 10.1051/ita/1985190100211
claim: For finite alphabets with reflexive symmetric commutation, Proposition 1.1 characterizes congruence by dependent-pair projections and Proposition 1.3 gives a four-factor decomposition of xy congruent to zt; Corollary 1.4 refines a two-factor product against any finite ordered product.
strata_touched:
  - D5/S1/Words/TraceProjection
  - D5/S1/Words/TraceLevi
  - D5/S1/Words/TraceMultiCut
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

## Four-factor source statement

Proposition 1.3 and its complete proof are on printed page 25. Under the
paper's standing assumptions that A is finite and theta is reflexive and
symmetric, it states that xy is congruent to zt if and only if there are
words u,v,r,s such that x is congruent to uv, y to rs, z to ur, and t to vs,
with v and r commuting absolutely. Absolute commutation requires theta(a,b)
for every letter a occurring in v and every letter b occurring in r.
These are simultaneous common factors. The proof of Proposition 1.3 itself,
including both directions and the induction cases, is contained on that page.

The native strict formulation has two separate obligations beyond this
source telescope: relating the finite-alphabet congruence formulation to
contextual adjacent-swap closure on an arbitrary alphabet, and obtaining
factors whose crossing pairs satisfy the irreflexive relation I itself.
The substitution theta(a,b) := a = b or I(a,b) permits equality on crossing
pairs and alone does not imply that stricter condition. This source citation
establishes neither a native Lean theorem nor the discharge of either
obligation. It supplies no claim of novelty, effective reconstruction,
complexity, or physical-history interpretation.

## Finite-product refinement

Corollary 1.4 is stated on printed page 25 and proved on printed page 26,
including the case of zero columns. With the same finite alphabet A and
reflexive symmetric theta, a congruence between uv and x_1 ... x_n admits
words p_i,q_i such that u is congruent to p_1 ... p_n, v to q_1 ... q_n,
and x_i = p_i q_i. Each q_i commutes absolutely with the later upper product
p_(i+1) ... p_n. Thus the factors are one simultaneous pair of rows, with
all earlier-lower/later-upper crossings constrained together.

The native two-row formulation uses x,y,zs[i],p(i),r(i) for u,v,x_i,p_i,q_i.
Its column conditions are native connections rather than literal list
equalities. Symmetry aligns the source's bottom-to-later-top commutation
with I(a,b) for a in p(k), b in r(j), j < k. The source convention remains
a real boundary: theta(a,b) := a = b or I(a,b) does not imply strict I(a,b),
and finite-alphabet congruence is not itself the native arbitrary-alphabet
closure. The native proof applies the strict binary Levi refinement
recursively and transports membership through native connections. It
requires no finite alphabet, equality oracle, nonempty word, supplied
matching or schedule. This is an established classical analogue, without
an originality or published-open-problem-resolution claim.

## Verified locator

- DOI: https://doi.org/10.1051/ita/1985190100211
- Publisher: https://www.numdam.org/item/ITA_1985__19_1_21_0/
- Proposition 1.1 on printed page 23; proof on page 24.
- Proposition 1.3 and its complete proof on printed page 25; finite A and reflexive symmetric theta are the standing assumptions on printed page 23.
- Corollary 1.4 on printed page 25, with proof on page 26, including zero columns.
