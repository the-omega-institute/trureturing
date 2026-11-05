---
bibkey: schrijver2017coursecombinatorialoptimization
authors: Alexander Schrijver
year: 2017
title: A Course in Combinatorial Optimization
doi: null
url: https://homepages.cwi.nl/~lex/files/dict.pdf
claim: The maximum cardinality of a common independent set of two finite matroids equals the minimum of their rank cut sums.
strata_touched:
  - D5/S3/Combinatorics/Matroids/FiniteIntersection
license: citation-only
triage: anchor
---

# Finite matroid intersection

## Verified locator

Source: https://homepages.cwi.nl/~lex/files/dict.pdf

The title page identifies Alexander Schrijver and the version of March 23, 2017.
Page 173 begins the definition with a finite set X and a collection of its subsets;
the empty-set, hereditary and augmentation axioms continue on page 174. Page 174
defines rank as the common cardinality of bases of a subset.

Page 188, Theorem 10.9, “Edmonds’ matroid intersection theorem,” states that for
M1 = (X, I1) and M2 = (X, I2),

$$
\max_{Y\in I_1\cap I_2}|Y|
=\min_{U\subseteq X}\bigl(r_{M_1}(U)+r_{M_2}(X\setminus U)\bigr).
$$

The Lean theorem takes X to be a finite subset E of an arbitrary ambient type.
Its two matroids have native grounds equal to E. It supplies one set independent
in both matroids, one attaining cut contained in E, and the universal
common-independent upper bound. The upper bound also permits cuts extending
outside E. Native extended ranks are finite under these ground hypotheses, so
conversion to natural numbers preserves them. Empty grounds and loops remain
included.

This course attests the classical mathematical statement. The Lean proof source
is Peter Nelson's apnelson1/Matroid at immutable revision
8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b; its source locations and Apache-2.0
license accompany the Lean module. The course PDF is cited and is not
redistributed. The original Edmonds 1970 full text has not been read here;
no original-paper pagination is asserted.
