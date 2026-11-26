---
bibkey: nist2010schwarzian
authors: Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors
year: 2010
title: "NIST Digital Library of Mathematical Functions: Schwarzian derivatives and the hypergeometric differential equation"
doi: null
url: https://dlmf.nist.gov/1.13
claim: "DLMF 1.13.20 defines the Schwarzian as t'''/t' minus three halves of (t''/t') squared; DLMF 15.10.1 gives the Gauss differential equation."
strata_touched: []
license: citation-only
triage: anchor
---

# Schwarzian and Gauss equation

## Verified locator

In [DLMF §1.13](https://dlmf.nist.gov/1.13),
[equation 1.13.20](https://dlmf.nist.gov/1.13.E20) uses the convention
$S(t)=t'''/t'-(3/2)(t''/t')^2$.
[DLMF 15.10.1](https://dlmf.nist.gov/15.10.E1) gives
$z(1-z)y''+(c-(a+b+1)z)y'-aby=0$.

## Application

Taking $a=b=1/2$ and $c=1$ gives the differential equation used by
the original half-binomial-square period.

For $y''+py'+qy=0$ and $t'=W/y^2$ with $W'=-pW$, the classical
calculation puts $L=y'/y$ and $G=-p-2L$. Then
$L'=-pL-q-L^2$, $t''=Gt'$, and $t'''=(G'+G^2)t'$, giving
$S(t)=2q-p'-p^2/2$. The repository proof establishes this inference
from actual derivatives on an open set, without assuming $q'$ or $y'''$.
It is a formal implementation of the classical calculation, with no claim
of literature novelty.

The native instance identifies the literal repository function
$t(r)=iP(1-r)/P(r)$ using its already proved derivative and ODE.
The canonical Gaussian correction $k=r(1-r)P'/P$ is then related to
the actual derivative quotient. Those object identifications are repository
derivations; the DLMF equations alone do not establish them.

This local calculation makes no continuation, monodromy, covering,
uniformization, positivity, operator transport, anomaly or spacetime claim.
