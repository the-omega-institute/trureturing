---
bibkey: mahmoudmortici2026wallisratio
authors: M. Mahmoud and C. Mortici
year: 2026
title: "Structural Properties, Complete Monotonicity, Bounds, and Analytic Approximations with Bounded Remainders for a Wallis-Type Gamma Ratio"
doi: 10.1007/s00025-026-02697-2
url: https://link.springer.com/article/10.1007/s00025-026-02697-2
claim: "Section 4 asks whether mu and chi are strictly increasing and theta is strictly decreasing for every positive real argument."
strata_touched:
  - D5/S3/Analytic/WallisRemainder/Defs
  - D5/S3/Analytic/WallisRemainder/Result
license: CC-BY-4.0
triage: anchor
---

# Wallis gamma remainder monotonicity

## Verified locator

DOI: 10.1007/s00025-026-02697-2

Source: https://link.springer.com/article/10.1007/s00025-026-02697-2

Version of record: *Results in Mathematics* 81 (2026), article 141,
published 2026-06-30. Section 4, Open Question; Section 5 restates it.
The article is open access under Creative Commons Attribution 4.0.

## Mathematical correspondence

For $x>0$, let $B(x)=\sqrt{x}\,\Gamma(x+1/2)/\Gamma(x+1)$ and define

$$\mu(x)=-x^2-\left\{\frac3x[\ln B(x)]^{-1}+24\right\}^{-1},$$

$$\theta(x)=\frac{23040x^5}{31}\left\{\frac{3x}{24x^2+1}+\ln B(x)\right\},$$

$$\chi(x)=\frac{358400x^7}{257}\left\{\frac{120x^2+31}{96x(10x^2+3)}+\ln B(x)\right\}.$$

`Defs.wallisB`, `Defs.mu`, `Defs.theta` and `Defs.chi` in
`D5/S3/Analytic/WallisRemainder/Defs` are these exact real functions.
`Defs.claim` includes the two nonvanishing assertions implicit in the
reciprocals and all three strict monotonicity comparisons.
`D5/S3/Analytic/WallisRemainder/Result.result` proves this claim.
The source proves continuity and boundedness of these remainders in
Theorems 2.1–2.3 and leaves their strict monotonicity as the question above.

The bounded literature scope and its limitations are stated in
`Problems/mahmoud-mortici-2026-wallis-remainder-monotonicity.md`.
