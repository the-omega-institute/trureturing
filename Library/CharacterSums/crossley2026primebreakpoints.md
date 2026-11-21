---
bibkey: crossley2026primebreakpoints
authors: Lee Crossley
year: 2026
title: Positivity at every scale for dilation 151/100
doi: 10.5281/zenodo.24410847
url: https://doi.org/10.5281/zenodo.24410847
claim: At dilation 151/100, a finite calculation at the breakpoints proves positivity of an ordinary-prime sum's deficit for all positive real scales up to 100000.
strata_touched: []
license: citation-only
triage: anchor
---

# Prime breakpoints

Omega’s character-weighted Mangoldt sum is affine between successive prime powers with nonzero coefficient. To bound its absolute value by a concave function on a closed interval, it suffices to check those interior points and the two endpoints. [Window theorem](https://github.com/the-omega-institute/trureturing/blob/25a809bcf56ebdde962304d52207b6a4fe6d5d88/D5/S3/CharacterSums/DirichletRampWindow.lean#L77).

Crossley gives a numerical example for a tent-weighted sum over ordinary primes. At dilation $b=151/100$, the deficit from the main term changes slope only at $p/b^2$, $p/b$ and $p$. The deficit is zero at the origin and positive at all 43,786 points checked. Affine interpolation proves positivity throughout $0<y\le 10^5$ unconditionally. [Proof and certificate](https://github.com/leecrossley/prime-band-151-100-all-scales/blob/ce7d8f07b426e529c47c6748a5c919faf3d7d8cb/PROOF.md#L45) and [archived result](https://doi.org/10.5281/zenodo.24410847).
