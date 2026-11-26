---
bibkey: brawleycarlitz1987composed
authors: J. V. Brawley and L. Carlitz
year: 1987
title: Irreducibles and the composed product for polynomials over a finite field
doi: 10.1016/0012-365X(87)90135-X
claim: "Composed addition forms a polynomial by taking every sum of a root of the first polynomial with a root of the second, including multiplicities."
strata_touched:
  - D5/S3/Analytic/Polynomial/PairSumStability
license: citation-only
triage: anchor
---

# Composed addition

## Verified locator

Brawley and Carlitz study composed products over finite fields. The indexed
review explicitly identifies composed addition as the product of the linear
factors indexed by all pairs of roots, with sums as the new roots.
[Paper DOI](https://doi.org/10.1016/0012-365X(87)90135-X)
· [zbMATH review](https://zbmath.org/?q=ti%3AIrreducibles+and+the+composed+product+for+polynomials+over+a+finite+field)

## Resultant normalization

For the integral polynomial used here, put $d=\deg p$ and let $a$ be its
leading coefficient. The Sylvester resultant $\operatorname{Res}_Y(p(Y),p(T-Y))$
is $a^{2d}$ times the monic product over the ordered root pairs. SageMath
documents this resultant convention and its normalization for composed sums
over integral domains, citing Bostan, Flajolet, Salvy and Schost,
*Fast computation of special resultants* (2006).
[Composed operations](https://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/polynomial_element.html#sage.rings.polynomial.polynomial_element.Polynomial.composed_op)
· [Special resultants DOI](https://doi.org/10.1016/j.jsc.2005.07.001)

The cited sources establish the composed-addition construction. The proof of
the coefficient test uses real conjugate pairing. The bounded literature check
did not determine priority for the test or its use on Ferrers graphs.
