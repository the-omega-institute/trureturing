---
bibkey: capelcostarico2026geodesic
authors: Ángela Capel; Pablo Costa Rico
year: 2026
title: Geodesic Quantum f-Divergences
doi: null
url: https://arxiv.org/abs/2608.15833v1
claim: Equations (52), (59), (62), (63) and (357) give the geodesic modular action, the divergence, its commuting reduction and the three ordered CMI deficits.
strata_touched:
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicBoundary
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence
license: citation-only
triage: anchor
---

# Geodesic quantum relative entropy and conditional mutual information

## Verified locator

[arXiv:2608.15833v1](https://arxiv.org/abs/2608.15833v1).

Equation (52) acts on Hilbert–Schmidt matrices by left multiplication by the
first matrix to the power $1-t$ and right multiplication by its $t$-th power
conjugated by the inverse square root of the reference. Equation (59) evaluates
the spectral function on the reference square root. Equation (63) takes
$f(z)=z\log z$, and (62) gives the commuting reduction. The base definitions in
Lean are in `CapelCostaRicoGeodesicModular`.
[Eqs. (52)–(63)](https://arxiv.org/html/2608.15833v1#S3.E52)

Equation (357) uses the ordered pair $(\rho_{ABC},\rho_{AB}\otimes\tau_C)$ and
its images under $\operatorname{Tr}_A$ for the one-sided forward deficit. The
two-sided forward deficit chooses $\tau_C=\rho_C$. The reverse deficit swaps
the arguments in both divergences.
[Eq. (357)](https://arxiv.org/html/2608.15833v1#S8.E357)

## Implications of the preprint

For the reverse modulus clause of Open questions 6, fix $0<q<1/2$ and a
faithful reference $\tau_C=\operatorname{diag}(u,1-u)$ in (381)–(384).
Set $e=1-x$ and $e'=1-x^2$ in the two binary laws. Both marginals agree,
their trace distance is $q(x-x^2)$, and the reverse value at $e'$ minus the
value at $e$ is $(u/2)\log(1/x)+O(x)$. The other logarithm in (384) is
regular at $e=1$ for this $q$. The calculation applies for every $t\in[0,1]$
and a choice of eigenbasis for any faithful qubit reference. Tensoring a fixed
faithful qubit $B$ leaves the quantities and distance the same. The repository's
diagonal parity family supplies a correlated three-qubit example with all three
pair marginals fixed throughout, and local unitary covariance transports it
to the native coordinates of the reference.
[Eq. (384)](https://arxiv.org/html/2608.15833v1#S8.E384) ·
[Proposition 4.3](https://arxiv.org/html/2608.15833v1#S4.Thmdefinition3) ·
[Issue #32390](https://github.com/the-omega-institute/trureturing/issues/32390)

For the forward fixed-conditioning clause, Theorem 10.16 and its faithful
regularization provide pairs with a balanced classical label. Rename the
signal $A$ and the label $C$, and tensor an independent fixed faithful state on
a new $B$. Equation (357) and tensor additivity from Proposition 4.3 give both
forward values as $D^t(\omega_{CA}\Vert\pi_C\otimes\omega_A)=
\log 2-H_t^\downarrow(C\mid A)_\omega$, with $\pi_C=I/2$. The inherited
conditional-entropy gap rules out a modulus at fixed $B$ for each $0<t\le 1$.
The $AC$ marginal in that reduction carries the varying two-qubit input.
[Open questions 6](https://arxiv.org/html/2608.15833v1#S12.I1.i6) ·
[Theorem 10.16](https://arxiv.org/html/2608.15833v1#S10.Thmdefinition16)

## Matched-marginal extension

Issue #32416 asks for a single sequence of faithful three-qubit pairs that
agree on all two-body marginals within each pair, with $AC$ and $BC$ equal to
$I/4$ throughout and with trace distance tending to zero. The common $AB$
marginal varies across the sequence. Both signed forward gaps tend to $\log 2$
for every fixed $0<t\le 1$, with one-sided reference $I/2$. Lemma 10.14,
equation (593), gives the rank-one antecedent for the boundary value, and
Proposition 4.6, equation (123), gives the common-flag rule in the paper.
Remark 3.5 gives the supported first-argument regularization. The Lean route
uses a global projection calculation and compact-interval regularization.
[Lemma 10.14](https://arxiv.org/html/2608.15833v1#S10.Thmdefinition14) ·
[Proposition 4.6](https://arxiv.org/html/2608.15833v1#S4.Thmdefinition6) ·
[Remark 3.5](https://arxiv.org/html/2608.15833v1#S3.Thmdefinition5) ·
[Issue #32416](https://github.com/the-omega-institute/trureturing/issues/32416)
