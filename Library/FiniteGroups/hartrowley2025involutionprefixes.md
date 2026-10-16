---
bibkey: hartrowley2025involutionprefixes
authors: Sarah B. Hart and Peter J. Rowley
year: 2025
title: A note on involution prefixes in Coxeter groups
doi: 10.48550/arXiv.2502.00777
url: https://arxiv.org/abs/2502.00777v1
claim: "Section 3, page 5 tentatively suggests equality of the greedy prefix and suffix involution lengths of every element."
strata_touched:
  - D5/S3/FiniteGroups/HartRowleyGreedyRefutation
license: CC-BY-4.0
triage: anchor
---

# Involution prefixes and the tentative orientation equality

Sarah B. Hart and Peter J. Rowley, *A note on involution prefixes in Coxeter
groups*, arXiv:2502.00777v1, submitted 2 February 2025, five pages.
The original is https://arxiv.org/abs/2502.00777v1 and its text is
https://arxiv.org/pdf/2502.00777v1.
The article identifies the Creative Commons Attribution 4.0 International
license: https://creativecommons.org/licenses/by/4.0/ . The quotations below
retain the wording with PDF line wrapping and typographic ligatures normalized.
Attribution and this normalization notice apply to the quoted passages; no
endorsement by the source authors is implied.

## Exact target and definitions

Section 3, page 5, the unnumbered paragraph immediately before References:

> We suspect that the involution length of any element always equals its
> ‘suffix’ involution length, but have not tested this extensively enough to
> make a firm conjecture.

This is an explicitly tentative assertion, with no source conjecture number.
It is separate from Conjecture 1.2 (the Ancestor Conjecture) and Conjecture 1.3
(the finite-group rank bound).

Pages 1–2 define Coxeter length as the minimum word length in the distinguished
simple reflections. A prefix u of w means w = uv with length(w) = length(u) +
length(v). The displayed IP(w) on page 2 restricts u to order exactly two,
excluding identity. The set A(w) consists of prefixes maximizing Coxeter length
over every such competitor. Property 1.1 says that each nonidentity element has
one ancestor when A(w) is a singleton; the group has the ancestor property when
this holds for every nonidentity element.

The paragraph after Conjecture 1.2 defines the ancestor decomposition by removing
the unique longest involution prefix and repeating on the residual. Its number
of factors is the involution length, with value zero at identity. The suffix
construction removes the corresponding right factor. These are greedy counts,
not minima over arbitrary involution factorizations. The page-5 assertion has
no finite-group, rank or Coxeter-element restriction. Its domain includes
infinite systems when the group-wide ancestor property holds.

The last sentence of the page-5 paragraph observes that the involution suffixes
of w are the involution prefixes of its inverse. This transports uniqueness and
any rank bound between orientations. It does not assert that the prefix counts
of an element and its inverse are equal.

## Bounded known-status and supplier evidence

The accepted qualification inspected all five pages of this original and all
pages of Hart–Kelsey–Rowley, *The Excess Zero Graph of a Coxeter Group*,
arXiv:2504.15994v1 (19 pages), and Harrison Gimenez, *On the Weak Right Order of
Right-Angled Coxeter Systems*, arXiv:2606.21104v1 (15 pages). The first later
work treats excess-zero graphs. The second establishes ancestor-property
results for fully commutative elements and right-angled systems. Neither
inspected original resolves the exact greedy-count equality. Bounded arXiv
author/relation searches likewise supplied no exact resolution. Rate-limited,
failed or nonresponsive channels provide no absence evidence. Unindexed,
differently worded, unpublished and outside-scope resolutions remain unexcluded;
there is no worldwide novelty or priority certificate.

Project public/private sources, pinned Mathlib and the inspected immutable
surfaces of mlyean/lean-coxeter and dicipler-pixel/coxeter-rank2-lean supplied no
located exact greedy-count result. The third-party surfaces are inspection and
citation only, with no dependency or code port. Mathlib supplies the Coxeter
presentation, word products, length and reduced-word API. Concrete presentation,
length and greedy certificates are separate proof obligations of the refutation.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2502.00777
- URL: https://arxiv.org/abs/2502.00777v1
- Target: section 3, printed page 5, unnumbered tentative assertion immediately
  before References; definitions and Property 1.1 on printed pages 1–2.
