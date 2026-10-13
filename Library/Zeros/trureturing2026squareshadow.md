---
bibkey: trureturing2026squareshadow
authors: trureturing contributors
year: 2026
title: Square descent of entire-function growth order
doi: null
url: https://raw.githubusercontent.com/the-omega-institute/trureturing/ad7ed967c5cf013e1c08f2b598928ba81d2f4a5d/Meta/Digestion/atoms/sha256/02442d2ab1d0fe1f273e0f69b93b84d85cdc6876f384b45bee09778d12f1882c
claim: For the entire square shadow satisfying F(z)=G(z squared), the circular maximum moduli satisfy M_G(r)=M_F(sqrt(r)), and the logarithmic limsup defining growth order gives rho(G)=rho(F)/2, hence order one descends to one half.
strata_touched:
  - D5/S3/Analytic/Entire/SquareShadowOrderHalving
license: citation-only
triage: anchor
---

# Square descent of growth order

The source states the maximum-modulus identity and proves the order-halving
formula by the substitution of the square root of the radius. The surrounding
source section constructs the entire function G from the even Taylor
coefficients of F and establishes F(z)=G(z squared).

The Lean formalization takes that identity as a hypothesis, proves both
maximum-modulus inequalities using attained maxima, and transports the actual
logarithmic quotient through the square-root filter map. It uses continuity,
which is weaker than entire differentiability, and EReal for the limsup so that
infinite order remains represented. The logarithm is Lean's total real
logarithm; in particular, the zero function has order zero in this convention.
The Taylor-series construction, uniqueness, and the source's subsequent
canonical-product claim are outside this formalization.

## Verified locator

- URL: https://raw.githubusercontent.com/the-omega-institute/trureturing/ad7ed967c5cf013e1c08f2b598928ba81d2f4a5d/Meta/Digestion/atoms/sha256/02442d2ab1d0fe1f273e0f69b93b84d85cdc6876f384b45bee09778d12f1882c

The public URL returned HTTP 200 and its bytes matched the local atom.
The complete surrounding square-shadow section was also read in the source
volume. The mathematical statements are attributed to this source; no
mathematical novelty is claimed.
