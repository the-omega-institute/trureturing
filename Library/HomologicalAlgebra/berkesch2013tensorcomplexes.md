---
bibkey: berkesch2013tensorcomplexes
authors: Christine Berkesch Zamaere, Daniel Erman, Manoj Kummini, Steven V. Sam
year: 2013
title: "Tensor complexes: Multilinear free resolutions constructed from higher tensors"
doi: 10.4171/JEMS/421
url: https://arxiv.org/abs/1101.4604v5
claim: "Proposition 9.1 identifies the boundary-format integral hyperdeterminant with the determinant of the two-term tensor complex, up to sign."
strata_touched: []
license: citation-only
triage: anchor
---

# Integral boundary-format determinant

## Verified locator

DOI: 10.4171/JEMS/421.

Immutable version: https://arxiv.org/abs/1101.4604v5.
The primary text is https://arxiv.org/html/1101.4604v5,
Section 9, Proposition 9.1 (`S9.E1`).
The article appears in *Journal of the European Mathematical Society*
15 (2013), 2257–2295.

Immediately before Proposition 9.1 the boundary format is
$a=1+\sum_i(b_i-1)$. Its hyperdeterminant is regarded as an integral
polynomial not divisible by any prime, determined up to sign.
Proposition 9.1 states that for every pinching weight the tensor complex
has length one and its square differential has determinant equal to this
hyperdeterminant up to sign. Its proof compares that differential to
Gelfand–Kapranov–Zelevinsky, *Discriminants, Resultants, and Multidimensional
Determinants*, Proposition 14.3.2.

## Finite specification and scope

For faces $M_0,M_1$ with $k+1$ rows and $k$ columns, the relevant
coefficient map is multiplication by the pencil of linear forms.
In the binary monomial bases its matrix is indexed by rows $(j,t)$,
$j<k$, $t\leq k$, and columns $(s,r)$, $s<k$, $r\leq k$:

$$
C_{(j,t),(s,r)}
 = \delta_{t,s}(M_0)_{r,j}
   + \delta_{t,s+1}(M_1)_{r,j}.
$$

The source-defined polynomial is the determinant of this integral
coefficient matrix with independent tensor entries. This finite
specification fixes the object being counted; its nonzero locus is
unchanged by the integral sign convention. Reduction of an equality up to
sign is valid in every characteristic, including two.

This note cites the source determinant specification. It does not assert
that a distinct geometric object, an independently chosen polynomial, or
an arbitrary matrix with the same dimensions has been identified with it.
The entry and basis correspondence is a separate mathematical obligation.
