---
bibkey: nist2026dlmfmodifiedbessel
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: "Modified Bessel Functions: Definitions and Basic Properties; Connection Formulas"
doi: null
url: https://dlmf.nist.gov/10.25
claim: The first-kind modified Bessel function has its Gamma-denominator defining series; the second-kind function has a connection formula at noninteger orders.
strata_touched:
  - D5/S3/Analytic/BesselProductOrderLogConvexity/Result
license: citation-only
triage: anchor
---

# Modified Bessel functions: definitions and connection formulas

## Verified locator

https://dlmf.nist.gov/10.25

DLMF §10.25(ii), equation 10.25.2
(https://dlmf.nist.gov/10.25.E2):

> I_ν(z) = (½z)^ν Σ_{k=0}^∞ (¼z²)^k / (k! Γ(ν+k+1)).

The page states that the principal branch of I_ν(z)

> is analytic in ℂ∖(−∞,0]

DLMF §10.27(ii), equation 10.27.4
(https://dlmf.nist.gov/10.27.E4):

> K_ν(z) = ½π (I_{−ν}(z) − I_ν(z)) / sin(νπ)

followed by

> When ν is an integer limiting values are taken

Equation 10.27.1 (https://dlmf.nist.gov/10.27.E1):

> I_{−n}(z) = I_n(z), n an integer.

## Mathematical correspondence

At real $u>0$, the principal-branch power in equation 10.25.2 is the
positive-real power. For $k\in\mathbb{N}$,
$(u/2)^\nu(u^2/4)^k=(u/2)^{2k+\nu}$. This identifies the defining series
with the frozen owner's
`D5.S3.Analytic.BesselRatioLogConcavity.Result.besselI`.

For real noninteger $\nu$, the denominator $\sin(\nu\pi)$ is nonzero,
and equation 10.27.4 identifies
`D5.S3.Analytic.BesselProductOrderLogConvexity.Result.besselK` with the
standard second-kind function at $u>0$. The formal assertion uses only
noninteger orders. It makes no identification of Lean's totalized quotient
at integer orders with the limiting values prescribed by DLMF.

The consumer is the
[settling Scribe](../../Blueprint/D5/S3/Analytic/BesselProductOrderLogConvexity/Result.scribe.cs).
