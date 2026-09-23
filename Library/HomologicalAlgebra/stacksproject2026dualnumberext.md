---
bibkey: stacksproject2026dualnumberext
authors: "The Stacks Project Authors"
year: 2026
title: "Dual numbers, long exact Ext sequences, and Yoneda extensions"
doi: null
url: https://stacks.math.columbia.edu/tag/0A5Q
claim: "The dual-number residue module has a periodic epsilon resolution; short exact module sequences induce contravariant Hom/Ext long exact sequences; degree-one Ext classes represent Yoneda extensions."
strata_touched:
  - D5/S3/HomologicalAlgebra/DualNumberResidueExtension
license: citation-only
triage: anchor
---

# Stacks Project ingredients for the dual-number extension

The Stacks Project, Example 15.70.3, tag `0A5Q`, was read on
23 September 2026. It takes a field `k`, the dual-number ring
`R = k[x]/(x^2)`, `epsilon` the class of `x`, and the residue module
`M = R/(epsilon)`. It states that `M` is quasi-isomorphic to the periodic
complex whose differentials are multiplication by `epsilon`, and concludes
that `M` does not have finite projective dimension.

The Stacks Project, Lemma 10.71.7, tag `065P`, gives the contravariant long
exact sequence beginning with `Hom` and continuing through `Ext^1` for a short
exact sequence of modules. Lemma 13.27.5, tag `06XU`, identifies Ext classes in
an abelian category with equivalence classes of Yoneda extensions.

These results support ingredients of the repository theorem. They do not state
the combined rational nonvanishing theorem or its retraction contradiction.
No source text or proof body is vendored.

## Verified locator

- URL: https://stacks.math.columbia.edu/tag/0A5Q
- Related tag: https://stacks.math.columbia.edu/tag/065P
- Related tag: https://stacks.math.columbia.edu/tag/06XU
