---
bibkey: fangfukitaevlisusun2026mesh
authors: Q. Fang, S. Fu, S. Kitaev, H. Li, X. Su, Z. Sun
year: 2026
title: "On mesh patterns of short length: Equidistribution and enumeration"
doi: 10.48550/arXiv.2606.14367
url: https://arxiv.org/abs/2606.14367v1
claim: "Concluding remarks, Conjecture 1: the four Class 69 length-2 mesh patterns are equidistributed on involutions."
strata_touched:
  - D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation
license: citation-only
triage: anchor
---

# Class 69 mesh patterns on involutions

## Verified locator

DOI: 10.48550/arXiv.2606.14367

URL: https://arxiv.org/abs/2606.14367v1

Locator: Concluding remarks, Conjecture 1; the Class 69 pattern list in Remark
`class-69-remark-equivalence`; the preamble definition of the `\pattern` macro.

Fang, Fu, Kitaev, Li, Su and Sun state in Concluding remarks that the remaining Class 69 equidistribution should continue when restricted to involutions, and Conjecture 1 names the four length-2 mesh patterns
`\pattern{scale=0.5}{2}{1/1,2/2}{1/2,1/1,2/1,0/0}`, `\pattern{scale=0.5}{2}{1/1,2/2}{2/2,0/1,1/1,1/0}`, `\pattern{scale=0.5}{2}{1/1,2/2}{0/2,1/1,2/1,1/0}`, and `\pattern{scale=0.5}{2}{1/1,2/2}{1/2,0/1,1/1,2/0}`. Their macro shades the box whose lower-left corner is each `x/y` in the fourth argument and places dots at `(1,1)` and `(2,2)`.

The kernel-checked settlement evaluates the quantified claim at `n = 3`, `k = 0`, and patterns `R 0` and `R 2`. Among the involutions `123`, `132`, `213`, and `321`, two avoid `R 0` while one avoids `R 2`, so the universal equidistribution claim is false.
