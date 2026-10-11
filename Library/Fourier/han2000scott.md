---
bibkey: han2000scott
authors: Guo-Niu Han
year: 2000
title: "Généralisation de l'identité de Scott sur les permanents"
doi: 10.1016/S0024-3795(00)00035-5
url: https://doi.org/10.1016/S0024-3795(00)00035-5
claim: "The cycle-geodesic product is a specialization of the generalized Scott permanent identity."
strata_touched:
  - D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1016/S0024-3795(00)00035-5

Source: https://doi.org/10.1016/S0024-3795(00)00035-5

## Identity and specialization

Linear Algebra and its Applications 311, pages 25–34. Han–Krattenthaler's exposition, arXiv:math/0003072v3, Section 5, prints the specialization

$$\mathrm{PER}(x^n-1,y^n+a+b)=(-1)^{n+1}\frac{\prod_{i=1}^n(i-(n-i)(a+b))}{(a+b+1)^n}.$$

Putting $a+b=-q$ and including the cycle-geodesic row factors yields

$$\operatorname{perm}\gamma_n(t)=n^{-n}\prod_{k=0}^{n-1}(n-k+kq),\qquad q=e^{2\pi it}.$$

This exact product is literature-attested. Its Lean proof uses a Cauchy permanent expressed as a Gaudin determinant and evaluates the latter on a weighted Vandermonde basis. The literature identity is not an axiom of that proof.

Related source: https://arxiv.org/abs/math/0003072v3. Lascoux's discussion at https://arxiv.org/abs/1002.3785 attributes this case to Han.
