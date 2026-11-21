---
bibkey: crossley2026criticalprimewindow
authors: Lee Crossley
year: 2026
title: The critical prime window stays positive at every scale
doi: 10.5281/zenodo.24410843
url: https://github.com/leecrossley/prime-band-critical-all-scales/blob/99f0a80a6f332a43942344c470ab410eba0eb2f7/PROOF.md
claim: Under RH the ordinary-prime deficit at the critical dilation is at least 0.035 times the cube root of the scale whenever log(y) is at least 96.
strata_touched: []
license: citation-only
triage: anchor
---

# Critical prime windows

Under RH, Omega proves that $M\sqrt{x}-U(x)$ tends to infinity for the complete integrated von Mangoldt remainder $U$ at its sharp coefficient $M$. The proof uses a second difference of the Mangoldt ramp and the trivial-zero terms in its explicit formula. [Omega’s theorem](https://github.com/the-omega-institute/trureturing/blob/c62e9628679dd0bb28f376f9d5198448c7b7400e/D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtCriticalGap.lean#L349).

Robert Polak’s equation (4) defines the same remainder, $F(x)=U(x)$. Under RH, his equation (6) and Lemma 3.1 give $M\sqrt{x}-U(x)>(\log x)^2/250-\log(2\pi)$ for $x\ge e^{10}$, since the correction $T(1/x)$ in (6) is negative. [Polak, 20 November 2026, §§2–3](https://doi.org/10.5281/zenodo.24406562).

## Verified locator

Crossley studies a tent-weighted sum over ordinary primes in $(y,b^2 y)$. At the critical dilation $b=b_\ast$, the contribution from prime squares equals the total magnitude of the zero terms at order $\sqrt y$. Under RH, the prime cubes give a lower bound of $0.035y^{1/3}$ for the deficit from the main term whenever $\log y\ge 96$. [Proof and bound](https://github.com/leecrossley/prime-band-critical-all-scales/blob/99f0a80a6f332a43942344c470ab410eba0eb2f7/PROOF.md#L9) and [archived result](https://doi.org/10.5281/zenodo.24410843).
