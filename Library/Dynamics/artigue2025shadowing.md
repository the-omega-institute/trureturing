---
bibkey: artigue2025shadowing
authors: Alfonso Artigue
year: 2025
title: Shadowing maps
doi: null
url: https://arxiv.org/abs/2504.00171v1
claim: Section 2.1 defines closed-error pseudo-orbits at all integer times; Proposition 5.2 proves that self-tuning pseudo-orbit maps are L-shadowing maps.
strata_touched: []
license: citation-only
triage: anchor
---

# Closed bi-infinite pseudo-orbits

Section 2.1 uses sequences indexed by the integers, with every step error at most the fixed nonnegative scale. The phase space is compact metric and the sequence space has its product topology. Definition 2.3 requires a continuous map on that closed pseudo-orbit domain fixing every true orbit. Definitions 3.1, 4.5 and 5.1 impose shadowing, L-shadowing and self-tuning conditions on that same prescribed map. Proposition 5.2 proves the implication from self-tuning to L-shadowing; the following paragraph leaves its converse unresolved in this version.

The rational interval marker classification is a separate estimate for the map u to 2u/(1+u). It preserves the closed-error and all-integer conventions. It constructs no pseudo-orbit selector and proves no converse counterexample. The marker estimates are not claims of the cited paper.

`CompactPseudoOrbitSelector` uses the same full closed domain, product topology,
true-orbit identity and exact integer-shift convention. Its compactness argument
derives a finite error window from continuity of a fixed true-orbit retraction.
Exact shift equivariance then gives global tracing on every smaller accuracy
scale and cofinite two-sided limit tracing on the original domain for that same
map. These are separate derivations, rather than results attributed to Artigue;
the supplier assumes the selector and constructs neither the interval R nor T.
Its canonical Scribe and mathematical source are reused from the owning interval
commit `5c2269ceb35eac4b8cf436d183defc9e2a1ffbc3`. The source-bound audit remains
unfinished under [issue #28187](https://github.com/the-omega-institute/trureturing/issues/28187);
the tracing registration's logical bridge supplies no source-selection certificate,
and the supplier's other public theorem registrations remain unfinished.

## Verified locator

[arXiv v1](https://arxiv.org/abs/2504.00171v1).
