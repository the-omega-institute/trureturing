---
bibkey: tanaka2026maass
authors: Daichi Tanaka
year: 2026
title: Explicit Construction of Maass Wave Forms and Their Petersson Inner Products
doi: 10.48550/arXiv.2601.21588
claim: Theorem 1.1 constructs Maass cusp forms from the specified primitive real-quadratic Hecke characters, including parameter zero; it does not supply a missing golden ring-class character.
strata_touched: []
license: citation-only
triage: anchor
---

# Real-quadratic Hecke construction and the complete golden tower

## Primary source and exact scope

Daichi Tanaka, *Explicit Construction of Maass Wave Forms and Their Petersson
Inner Products*, arXiv:2601.21588v3, revised February 3, 2026.

https://arxiv.org/abs/2601.21588
https://arxiv.org/html/2601.21588v3

The source passages used here are equation (1.1), the cosine/sine definition
immediately following it, Theorem 1.1, and the subsequent discussion of
spectral parameter zero. The theorem assumes a primitive Hecke character of
specified archimedean type that does not factor through the norm and a
Dirichlet character. It constructs a Maass cusp form at the displayed
quadratic-discriminant and conductor level. For the finite odd-order
anticyclotomic characters in the WSS dossier, the real components are
trivial, the parameter is zero, and the non-norm condition is satisfied.

The source's cosine form has first exponential Fourier coefficient one half.
The WSS dossier uses twice that form, with first exponential coefficient one.
The complete-tower arguments below depend on these coefficients and their
Hecke eigenvalues. No Petersson norm formula or earlier normalization
correction is an input to CTG.

## Actual mathematical consumer

`Problems/wall-sun-sun-golden-unit-lift.md`, ROC and CTG.1, starts with an
ACTUAL golden ordinary ring-class character eta of order p^k. This is an
arithmetic hypothesis, equivalent in ROC to h_p>=k+1. Its nontrivial powers
have primitive conductors appropriate to their orders. Apply the cited
construction at each primitive conductor and then include the unscaled
oldvector g(z) at the common level. This gives the complete tower, including
all smaller nontrivial p-power character orders.

CTG.1-CTG.6 then prove, by integer polynomial and trace-dual arguments, the
following statements about that already-existing tower:

- its good-Hecke order is Z[X]/Q_k, where
  Q_k=product_(j=1)^k Psi_(p^j), with Q_k(2)=p^k;
- adjacent primitive packets are glued over a nonreduced quotient of
  characteristic p, rather than being an integral direct product;
- its scalar Eisenstein congruence module is Z/p^k, although every individual
  primitive packet has module Z/p;
- a specified integral trace combination attains precisely this congruence
  depth, and its normalized mod-p^r class exists exactly for r<=k.

These complete-tower formulas are proved in the dossier and are not
attributed to Tanaka. Their independent priority is unconfirmed. They do not
construct eta at a new target prime and do not prove a new WSS family.

The existing arithmetic source
`D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.lean` already states the
integer-image and unique-reconstruction theorem for modulus 2n+3, without a
primality hypothesis. CTG.3 identifies the actual complete-tower trace matrix
with that template at 2n+3=p^k. Its companion Scribe records this ordinary
application and the cited ambient construction. The spectral identification
is not an additional kernel-certified conclusion of that Lean source.
