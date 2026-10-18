---
bibkey: friedlandgaubert2019spectral
authors: Shmuel Friedland and Stephane Gaubert
year: 2019
title: "Spectral inequalities for nonnegative tensors and their tropical analogues"
doi: null
url: https://arxiv.org/html/1804.00204v3
claim: "Finite supported normalized circulations give the log spectral radius variational formula; positive left/right Perron vectors give an attainer."
strata_touched:
  - D5/S3/Combinatorics/Graph/Pressure/StationaryVariational
  - D5/S3/Combinatorics/Graph/Pressure/PerronDoob
  - D5/S3/Combinatorics/Graph/Pressure/PeriodicGrowth
license: citation-only
triage: anchor
---

# Finite supported pressure

Friedland and Gaubert, v3, section 6.1, Lemmas 15–18 and Theorem 17,
equations (6.1)–(6.4), pages 14–17, give the finite supported circulation
variational formula. Set mu(i,j)=pi(i)Q(i,j) and scale the entropy maximum
to obtain mean cost minus temperature times entropy. Zero-mass rows can
be completed on original graph successors.

The Lean development uses the actual exponential adjacency, a positive
Perron eigenpair from the Apache-2.0 MCMC source, full-row KL nonnegativity
and stationarity to obtain an attained variational minimum. Positive-vector
bounds give every-state matrix-power growth without aperiodicity; zero
supported costs give the actual counting adjacency. Explicit unrestricted
weighted-walk enumeration and counting, the minimum directed-cycle mean,
the maximum-outdegree bracket and the zero-temperature limit remain open
in this development. These classical results carry no new priority claim.
