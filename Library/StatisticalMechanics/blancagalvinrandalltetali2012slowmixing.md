---
bibkey: blancagalvinrandalltetali2012slowmixing
authors: Antonio Blanca; David Galvin; Dana Randall; Prasad Tetali
year: 2012
title: Phase Coexistence and Slow Mixing for the Hard-Core Model on Z^2
doi: 10.1007/978-3-642-40328-6_27
url: https://arxiv.org/abs/1211.6182v1
claim: Cut conductance bounds the gap of hard-core Metropolis dynamics; the method transfers only after recomputing the flux for the actual carrier and transition rates.
strata_touched: []
license: citation-only
triage: anchor
---

# A cut as a variational slow direction

The primary source is [arXiv:1211.6182v1](https://arxiv.org/pdf/1211.6182v1),
Section 4.1 and Theorem 4.1. This note does not redistribute source
text or the PDF.

The source studies hard-core independent sets on two-dimensional
lattice regions. Its Metropolis transition rate for a legal one-site
change is the smaller of one and the activity ratio, divided by twice
the region size. It bounds the spectral gap from above by twice the
conductance and from below by half the squared conductance.

For an arbitrary finite reversible chain, a centered cut indicator
has variance p(A)(1-p(A)) and Dirichlet energy equal to the stationary
flux across the cut. Its Rayleigh quotient is therefore that flux
divided by p(A)(1-p(A)). This is the variational principle used in
the FIB collective occupation-cylinder calculation.

The FIB open-path heat-bath insertion rate is w_i lambda_i/(1+lambda_i).
Its cylinder flux must be calculated with that rate, the constrained
activity law and the original open endpoints. Deleting vertices
evaluates event probabilities; it does not replace the chain.
The source's lattice phase-coexistence and slow-mixing conclusions
do not establish the FIB comparison of its two spectral edges.

## Verified locator

- DOI: https://doi.org/10.1007/978-3-642-40328-6_27
- Source: https://arxiv.org/abs/1211.6182v1
