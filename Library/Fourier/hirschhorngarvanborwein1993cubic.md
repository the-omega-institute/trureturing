---
bibkey: hirschhorngarvanborwein1993cubic
authors: "Michael Hirschhorn, Frank Garvan and Jon Borwein"
year: 1993
title: "Cubic Analogues of the Jacobian Theta Function theta(z, q)"
doi: 10.4153/CJM-1993-038-2
url: https://doi.org/10.4153/CJM-1993-038-2
claim: "Classical cubic theta four-dissections and the odd coefficient recurrence for the three-core Euler quotient."
strata_touched:
  - D5/S3/Arith/ModularForms/CubicThetaOddParity
license: citation-only
triage: anchor
---

# Classical cubic theta four-dissections

Hirschhorn, Garvan and Borwein, *Canadian Journal of Mathematics* 45(4),
673-694, DOI [10.4153/CJM-1993-038-2](https://doi.org/10.4153/CJM-1993-038-2).
The publisher metadata and Crossref record agree on the authors, title,
volume, issue and page range. The publisher's version of record is
[the Cambridge PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/3C89D1FD88B80DB576E5413003F0D0BD/S0008414X00015443a.pdf/cubic-analogues-of-the-jacobian-theta-function-8z-q.pdf),
SHA-256 `3795f6f3b9ce07f56d12fa67a698516fe8e12a9123c136446e7360a19c0b8615`.

## Identities and normalization

Identities (1.35) and (1.36), page 676, give the four-dissections of
the cubic theta functions b and c. Their proofs are (9.7)-(9.13),
pages 689-691: (9.7)-(9.9) establish the b identity, and
(9.10)-(9.13) establish the c identity. The sums range over the full
integer lattice, as specified on page 674.

Write E(q) for the product of 1-q^m over positive integers m, and put
T(q)=E(q^3)^3/E(q). The paper uses c(q)=3*T(q). Identity (1.36),
repeated as (9.13), has the form c(q)=q*c(q^4)+3*R(q^2), where
R is an integral Euler product quotient with unit denominator.
Consequently, for every natural n,

- the coefficient of q^(4*n+1) in T is the coefficient of q^n in T;
- the coefficient of q^(4*n+3) in T is zero.

## Formal correspondence

`D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT` is the
integer formal series T, defined using the pentagonal Euler series
and its constant-term-one inverse.
`D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four`
states precisely the two odd coefficient identities, including n=0.
It does not state the even part of (1.36) or the companion (1.35).

The proof directly reuses
`D5/S3/Arith/ModularForms/CubicThetaCoreProduct.coeff_core_product`,
which counts the complete finite lattice fibre
3*(x^2+x*y+y^2)-2*x-y=n. The map (x,y) -> (1-2*x,-2*y)
identifies the fibres at n and 4*n+1; residue-three fibres are empty.
Compatibility of the integral unit inverse with the rational embedding
transfers those cardinality equalities to T.

The related [Huang et al. note](huang2025signpatterns.md) supplies
context for the existing cubic theta product chain. The classical
four-dissection cited here is attributed to the primary HGB source.
This is a formal proof of a classical coefficient consequence, with
no claim of mathematical novelty or resolution of a divisibility problem.
Only bibliographic information and mathematical correspondence are retained;
the source PDF and its text are not vendored.
