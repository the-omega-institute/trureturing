---
bibkey: burnol1999scattering
authors: Jean-François Burnol
year: 1999
title: Scattering on the p-adic field and a trace formula
doi: null
url: https://arxiv.org/abs/math/9901051v2
claim: Local time delay is nonnegative, but the conductor contribution to the explicit formula is represented by a supertrace with an identity correction. Time-delay positivity alone does not supply the needed full Weil upper bound on the signed defect.
strata_touched: []
license: citation-only
triage: anchor
---

# Local time delay and the arithmetic sign

The inspected primary manuscript is [arXiv:math/9901051v2](https://arxiv.org/pdf/math/9901051v2), 17 pages, SHA-256 `353f16b36139650a5221c0c6f6416a0da0bc5a47ff2d08a46c5468b9989d2c49`. The PDF carries a 1 February 1999 arXiv stamp and an internal v2 label of 31 January 1999. Locators below refer to this version. The source is reused without a new proof, numerical reproduction or Lean declaration; selected statement and normalization inspection is not a complete proof audit.

## Local field and measures

The source treats a nonarchimedean local field with residue cardinality $q$ and differential exponent $\delta$. Printed pp.4–5 fix the self-dual additive measure and a multiplicative measure $d^*t$ giving the units volume one. The trace formulas use $d^\times t=\log(q)\,d^*t$. The unitary additive-to-multiplicative identification includes the half-density $|t|^{1/2}$ and the source normalization constant.

The distinction between the unit-character sector and the ramified sectors is essential. Specializing the source to $\mathbb Q_p$ with its stated additive character gives $q=p$, $\delta=0$. This is the unramified sector relevant to the ordinary zeta prime factor.

## Nonnegative time delay is not the conductor sign

Theorem VII, printed p.11, gives the nonnegative time-delay operator. Its symbol on the trivial-unit-character sector, with $z=e^{it\log p}$, is

$$
\tau_p(t)=\log p\,
\frac{1-p^{-1}}{|1-p^{-1/2}e^{it\log p}|^2}.
$$

Theorem VIII on the same page relates time delay to the conductor operator $H$. On this sector its symbol is

$$
H_p(t)=\log p-\tau_p(t).
$$

The formula retains the full local factor. Its phase dependence cannot be replaced by a constant positive energy, or by only one prime-power sample, when transporting the explicit formula.

Theorem X, printed p.14, represents the local explicit-formula contribution as

$$
\operatorname{sTr}(Z(v))+v(1)\log q=H(v)(1).
$$

Here $v$ is the source local Schwartz–Bruhat integrating test. The odd part of the source interacting space is the line spanned by its Tate vector $\omega$; the even part is its orthogonal complement. Thus the supertrace and its identity correction are material parts of the source formula, rather than an ordinary nonnegative compressed trace. The source counts zeros positively and poles negatively, with its half-shift convention.

## Remaining same-test interface

The [project common Weil form](frankliebseiringer2006hardy.md) has its own positivity sign and additive Fourier convention. Using this local supplier requires transporting that sign, the Haar normalization and the integrating test, while retaining every support-relevant prime power. No compiled project application or independent arithmetic trace evaluation is claimed here.

Time-delay positivity supplies no upper bound on its combination with the [archimedean correction](connesconsani2021archimedean.md) and the orthogonal projection correction in the [semilocal Euler-factor metric](connesconsanimoscovici2024semilocal.md). That combined signed comparison, on the same actual test, remains unresolved. The local scattering formula is reusable input, not a proof of full Weil positivity or RH.
