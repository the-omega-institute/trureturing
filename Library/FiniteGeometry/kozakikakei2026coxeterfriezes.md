---
bibkey: kozakikakei2026coxeterfriezes
authors: Yuta Kozaki and Saburo Kakei
year: 2026
title: "Coxeter Group Symmetries of Frieze Patterns"
doi: 10.48550/arXiv.2611.25785
url: https://arxiv.org/abs/2611.25785v1
claim: "Outside six columns, the allowable column permutations of the double-normalized even frieze matrices are exactly the dihedral group."
strata_touched:
  - D5/S3/Geometry/KozakiKakeiMatching
  - D5/S3/Geometry/KozakiKakeiNormalization
  - D5/S3/Geometry/KozakiKakeiConjecture13
  - D5/S3/Geometry/Polygons/KozakiKakeiFourNormal
license: citation-only
triage: anchor
---

# Kozaki and Kakei on even frieze symmetry

## Verified locator

DOI `10.48550/arXiv.2611.25785` · [arXiv edition](https://arxiv.org/abs/2611.25785v1)

Yuta Kozaki and Saburo Kakei, *Coxeter Group Symmetries of Frieze Patterns*,
arXiv:2611.25785v1, §3, printed p. 9, Conjecture 13, state:

> If $m \ne 3$, the symmetry group of $\widehat{\widehat{\mathcal{M}\,}}_{2m}$ coincides with the dihedral group $\mathcal{D}_{2m}$.

The surrounding construction uses even order at least four and matrices over the field of
complex rational functions. The source reports computer verification at $m=2,4,5,6$.
[Conjecture 13](https://arxiv.org/html/2611.25785v1#Thmproposition13)

The level-one equation equates $D_{2,3}D_{4,5}\cdots D_{2m-2,2m-1}D_{1,2m}$
and $D_{1,2}D_{3,4}\cdots D_{2m-1,2m}$. Admissibility requires that all
two-column minors are nonzero. The normal form fixes the first three columns to
$(0,-1),(1,0),(1,1)$ and every consecutive minor and $D_{1,2m}$ to one.
Reordering columns is followed by normalization within the equivalence class under
invertible left multiplication and invertible right diagonal rescaling.
[Matrix definitions and multi-ratio](https://arxiv.org/html/2611.25785v1#S2) ·
[Column action](https://arxiv.org/html/2611.25785v1#S3)

The Lean endpoint classifies the allowable permutations of the column labels for all
$m\ge2$ with $m\ne3$. For $m=2$ the allowable subgroup has eight elements and its
action on the singleton normal-form space has one-element image.

## Related results

- Morier-Genoud, *Counting Coxeter's friezes over a finite field*, §2.2, Theorem 2.3 and
  Lemma 2.7, treats a cyclic ratio at level minus one and the even-order scaling
  recurrence. The moduli problem allows repetitions at nonconsecutive positions.
  [Morier-Genoud](https://doi.org/10.5802/alco.140)
- Affolter, George and Ramassamy, §4, Lemma 4.2, prove invariance of the six-point
  cyclic multi-ratio equation at level minus one under permutations of the three
  opposite pairs. Reversing the closing orientation and inverting the ratio as needed
  gives the corresponding six-column level in Kozaki and Kakei's convention.
  [Affolter–George–Ramassamy](https://doi.org/10.3842/SIGMA.2025.040)
- Boalch, *Wild Character Varieties*, §3, Proposition 9 and Lemma 11, treats Sibuya
  level varieties and formal monodromy. The Sibuya locus in that convention is at level
  $(-1)^{m+1}$ on pairwise distinct points. The quotient construction also allows
  repetitions at nonconsecutive positions. [Boalch](https://arxiv.org/pdf/1501.00930v5)
- Bobenko, Hoffmann and Suris use the fractional-linear dependence on one coordinate
  in the even multi-ratio and the six-point level minus one. Bobenko and Hoffmann's
  Proposition 2.1 concerns six cyclically ordered points on a circle in a flower.
  Atkinson studies the six-point equation and its pair-triple relabeling.
  [Bobenko–Hoffmann–Suris](https://arxiv.org/pdf/math/0104244v1) ·
  [Bobenko–Hoffmann](https://arxiv.org/pdf/math/0005245v1) ·
  [Atkinson](https://arxiv.org/pdf/1407.5468v2)
- Igusa and Schiffler's Theorem 3.2 concerns Coxeter mutation on components of an
  acyclic-quiver frieze variety. [Igusa–Schiffler](https://arxiv.org/pdf/1906.00106v2)

## Bounded prior-resolution evidence

The qualification examined one exact-author arXiv title hit, 15 arXiv topic hits,
two ten-record Crossref result sets, and one exact-title DataCite hit. No item in
those result sets or the related primary texts above gave the full in-range
classification for all admissible matrices. The qualification also checked the
pinned repository and Mathlib and selected third-party Lean repositories.

OpenAlex title search and Semantic Scholar citation search returned HTTP 429.
The restricted scan of Sibuya's monograph was assessed through later Sibuya-space
coverage. King–Schief was checked bibliographically, with HTTP 403 on the publisher
full-text routes. Priority outside the inspected scope remains unverified.
[Preregistration and qualification](https://github.com/the-omega-institute/trureturing/issues/32810)
