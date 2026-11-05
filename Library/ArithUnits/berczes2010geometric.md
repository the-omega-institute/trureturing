---
bibkey: berczes2010geometric
authors: Attila Bérczes
year: 2010
title: On the sumset of geometric progressions
doi: 10.5486/PMD.2010.4683
url: https://doi.org/10.5486/PMD.2010.4683
claim: Theorems 2.2 and 2.3 classify the diagonal and non-diagonal collisions for powers of the positive root of x³ − x − 1; Theorem 1.1 counts sumsets of consecutive powers.
strata_touched:
  - D5/S3/Arith/Additive/PlasticPowerCollisions
license: citation-only
triage: anchor
---

# Plastic power collisions

## Verified locator

DOI: 10.5486/PMD.2010.4683

Source: https://doi.org/10.5486/PMD.2010.4683

Publisher PDF: https://publi.math.unideb.hu/paper/1503/download/

Theorem 1.1 is on pp. 262–263; Theorems 2.2 and 2.3 are on p. 264.
The plastic-root cases are Theorem 2.3(1)–(3) with r = 1.

The publication is in *Publicationes Mathematicae Debrecen* 77/3–4,
pp. 261–276. On p. 264, Theorem 2.3(1)–(3) gives the non-diagonal
quadrinomials with exponent triples (4,3,2), (9,8,5), and (6,5,3),
sharing a root with x⁷ − 2x⁵ + 1. The common non-unit root has minimal
polynomial x³ − x − 1. Theorem 2.2, attributed to A. Schinzel,
excludes two distinct diagonal trinomials with a common non-unit root.

For a real r > 1 with r³ = r + 1, the four normalized equal sums are
1 + r⁴ = r² + r³, 1 + r⁶ = r³ + r⁵,
1 + r⁷ = 2r⁵, and 1 + r⁹ = r⁵ + r⁸.
Translation gives the collisions for arbitrary integer exponents,
including negative exponents. The Lean proof uses the elementary
integer difference equation in the repository source rather than
formalizing the paper's general polynomial classification.

The finite-subset application keeps sorted exponent pairs. Their gaps
are 4 ↔ 1, 6 ↔ 2, 7 ↔ 0, and 9 ↔ 3. These distinct gaps prevent
three unordered representations of the same real sum. Removing the
outer representation of each present translated template leaves one
representative of each sum. This application does not by itself count
the templates in the particular nested family or establish its comparison
with the golden-ratio power set.

No literature novelty is asserted for the collision classification.
