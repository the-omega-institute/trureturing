---
bibkey: bariczponnusamy2013turan
authors: Á. Baricz and S. Ponnusamy
year: 2013
title: On Turán type inequalities for modified Bessel functions
doi: null
url: https://arxiv.org/abs/1010.3346
claim: "The final conjecture asserts log-convexity of the modified Bessel product in its order on (-1,infinity) for every positive argument."
strata_touched:
  - D5/S3/Analytic/BesselProductOrderLogConvexity/Result
license: citation-only
triage: anchor
---

# Order log-convexity of the modified Bessel product

## Verified locator

https://arxiv.org/abs/1010.3346

arXiv:1010.3346v1, *On Turán type inequalities for modified Bessel
functions*, Á. Baricz and S. Ponnusamy. Published in Proceedings of the
American Mathematical Society 141(2) (2013), 523–532.
The arXiv identifier is the verified locator; the supplied source text
does not give this paper's DOI. Page numbers below are printed pages
of the arXiv version.

## Source statements

The identification and definition referral in §1, printed p. 1:

> Let us denote with Iν and Kν the modified Bessel functions of the first and second kind, respectively. For definitions, recurrence formulas and other properties of modified Bessel functions of the first and second kind we refer to the classical book of G.N. Watson [Wa].

Theorem 1(4), printed p. 4:

> the function ν ↦ I_{√ν}(u)K_{√ν}(u) is log-convex on (0, ∞) for all u > 0 fixed;

Theorem 2, printed p. 6, equation (19):

> Moreover, for all ν ≥ 1/2 and u > 0 we have
>
> $2I_\nu(u)K_\nu(u)\le I_{\nu-1}(u)K_{\nu-1}(u)+I_{\nu+1}(u)K_{\nu+1}(u).$

The final Conjecture in §3, printed p. 7:

> Motivated by Theorems 1 and 2 we conjecture the following.
>
> Conjecture. The function ν ↦ I_ν(u)K_ν(u) is log-convex on (−1, ∞) for all u > 0 fixed.

## Mathematical correspondence

The defining reference is the
[DLMF modified-Bessel note](nist2026dlmfmodifiedbessel.md), which quotes
the first-kind series in equation 10.25.2 and the second-kind connection
formula in equation 10.27.4, including the principal branch and the
integer-order limiting convention. At real u > 0, the frozen owner's
`D5.S3.Analytic.BesselRatioLogConcavity.Result.besselI` uses that series
with its positive-real principal-branch normalization. The second-kind
definition agrees with the quoted connection formula at noninteger orders;
its totalized quotient at integer orders is not used.
The paper's p. 1 passage identifies the functions and refers to Watson,
rather than supplying either defining formula. The formal assertion keeps
only the three-point inequality at noninteger orders. A positive
log-convex function satisfies this inequality, so its failure refutes
the stated conjecture.

At u=1 the orders −1/2, 1/2 and 3/2 give the products
$(1+t)/2$, $(1-t)/2$ and $2t$, respectively, with $t=e^{-2}$.
Their midpoint log-convexity difference is
$(1+t)t-(1-t)^2/4<0$.
The dossier `Problems/baricz-ponnusamy-2013-bessel-product-order-log-convexity.md`
distinguishes this assertion from the square-root parametrization of
Theorem 1(4), the separate assertions of Theorem 2, and numerical
observations at other arguments.
