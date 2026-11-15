---
bibkey: hatcher2017vectorbundles
authors: Allen Hatcher
year: 2017
title: Vector Bundles & K-Theory, version 2.2
doi: null
url: https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf
claim: "The Mobius bundle is the canonical line bundle over RP^1; a rank-n vector bundle is trivial exactly when it has n everywhere linearly independent sections."
strata_touched: []
license: citation-only
triage: anchor
---

# Line bundles and continuous frame selection

The [author-hosted version 2.2](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf),
Section 1.1, printed p. 7 (PDF page 11), identifies the Mobius bundle
with the canonical line bundle over $\mathbb{RP}^1\cong S^1$ through
the endpoint relation $(0,x)\sim(\pi,-x)$. Printed p. 8 (PDF page 12)
states that a rank-$n$ vector bundle is isomorphic to the trivial bundle
exactly when it has $n$ sections that are linearly independent in every
fiber. The same page distinguishes the Mobius bundle from the product
bundle using the complement of the zero section.

This supplies classical bundle context for the distinction between
pointwise factors and globally continuous frame selection in
[CircleDoubleCoverNoSection](../../Blueprint/D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection.md).
The application proves its obstruction using the existing Lean circle
no-section theorem, without assuming a bundle classification theorem.
Neither these locators nor the application assert physical realization
or a dynamics law. Only bibliographic attribution and paraphrase are used;
no source text or proof is copied into Lean.
