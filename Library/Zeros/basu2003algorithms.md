---
bibkey: basu2003algorithms
authors: Saugata Basu; Richard Pollack; Marie-Françoise Roy
year: 2003
title: Algorithms in Real Algebraic Geometry
doi: 10.1007/978-3-662-05355-3
url: https://www.math.purdue.edu/~sbasu/bpr-posted1.pdf
claim: Hermite signatures compute Tarski queries; real interpolation extends this classical formula to arbitrary conjugation-compatible weights on finite conjugate-stable node sets.
strata_touched:
  - D5/S3/QuadraticForms/ConjugateHankelSignature
license: citation-only
triage: anchor
---

# Hermite signatures for conjugate-stable nodes

The numbered statements and page numbers here refer to the author-posted
2003 manuscript at the URL below, rather than to another edition.

Section 4.3.2, pp.135–139, defines the Hermite matrix Her(P,Q) using the
roots of P with their multiplicities. Proposition 4.53 identifies the
associated quadratic form with the multiplication trace. Theorem 4.57
states Sign(Her(P,Q)) = TaQ(Q,P), where the Tarski query sums sign(Q(x))
over the distinct real roots of P. Its proof on p.139 splits each nonzero
complex conjugate contribution into one positive and one negative real
square. Roots at which Q vanishes contribute zero.

For a nonempty finite conjugation-stable set S in C with compatible
weights w, let p(X) be the product of X-z over z in S. This polynomial is
squarefree with real coefficients. Lagrange interpolation gives the unique
polynomial q of degree less than |S| satisfying q(z)=w(z). Conjugating its
coefficients gives the same interpolant, so q also has real coefficients.
The |S|-dimensional Hermite matrix Her(p,q) therefore has entries
Re(sum over z in S of w(z) z^(i+j)). Theorem 4.57 gives its signature as
the sum of the signs of the real weights at the real nodes.

For every d>=|S|, taking the polynomial remainder modulo p is a surjection
from real polynomials of degree less than d onto those of degree less than
|S| and preserves evaluation at every node. The d-dimensional Hankel form
is its pullback, hence is congruent to Her(p,q) plus a zero form of
dimension d-|S|. Its signature is unchanged. Empty S and identically zero
weights give the zero form directly. This comparison includes complex,
negative and zero weights, singular matrices, and admissible dimension
zero; it requires no positivity assumption on the weights.

This is the classical Hermite signature formula expressed for a finite
node set through real interpolation and a zero-block extension. The source
does not print this exact finite-set statement verbatim.

## Verified locator

- DOI: https://doi.org/10.1007/978-3-662-05355-3
- Author-posted manuscript: https://www.math.purdue.edu/~sbasu/bpr-posted1.pdf
- Section 4.3.2, Proposition 4.53 and Theorem 4.57, printed pp.135–139.
- Author-posted PDF SHA-256: 01ab763368db41c0760c60ee41760f9f23b4d0cb3edfa9ad41628d5f38c5e70c
