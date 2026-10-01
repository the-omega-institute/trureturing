---
bibkey: polak2026finite_robin_ca
authors: Robert Polak
year: 2026
title: A Finite Computer-Assisted Verification of Robin's Inequality via Colossally Abundant Profiles, with Exact Prime-Power Residual Dynamics
doi: 10.5281/zenodo.21808589
url: https://doi.org/10.5281/zenodo.21808589
claim: The preprint reports an unconditional finite computer-assisted verification of Robin's inequality for 5041 <= n <= 10^(7.1*10^22), plus an exact prime-power residual reformulation; the finite result does not extend to all integers or prove RH.
strata_touched: []
license: citation-only
triage: anchor
---

# Finite CA-profile verification and the signed residual

The source is Robert Polak, Zenodo preprint, record
[21808589](https://doi.org/10.5281/zenodo.21808589), version 1.0, published 5 August 2026. It reports source code and interval archives, but no Lean verification is claimed here.

## Finite theorem and residual interface

The preprint claims Robin's strict inequality for every

$$
5041\le n\le 10^{7.1\times10^{22}}.
$$

Its certificate exhausts 3,341,978 colossally abundant exponent profiles, uses an analytic prime-power reduction and a finite-height zero verification, and transfers certified CA endpoints to intervening integers by Robin's convexity proposition. The stated CA support computation reaches $1.64967\times10^{23}$.

After the finite theorem, the source derives exact prime-power cell and signed-triangular identities. Its exploratory event scan is explicitly separated from the finite proof: the universal eventwise target needed for an infinite Robin proof remains unproved.

## Boundary for FIB

This is a larger finite verification range, not a replacement for the FIB source bridge. The certificate is organized by CA exponent profiles and consecutive-CA interpolation, whereas the FIB family is specified by additive Zeckendorf windows or congruence classes. No result in the source maps those addresses to the certified CA profiles or supplies the same-integer signed residual estimate required by §250. The finite range can be cited as an external boundary check, but repeating its computation would be duplicate work and would not advance RH.
