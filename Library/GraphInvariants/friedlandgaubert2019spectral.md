---
bibkey: friedlandgaubert2019spectral
authors: Shmuel Friedland and Stephane Gaubert
year: 2019
title: "Spectral inequalities for nonnegative tensors and their tropical analogues"
doi: null
url: https://arxiv.org/html/1804.00204v3
claim: "Finite supported normalized circulations give the log spectral radius variational formula; positive left/right Perron vectors give an attainer."
strata_touched:
  - D5/S3/Combinatorics/Graph/Pressure/WeightedWalks
  - D5/S3/Combinatorics/Graph/Pressure/CyclePressure
license: citation-only
triage: anchor
---

# Finite supported pressure

## Verified locator

Primary source: https://arxiv.org/html/1804.00204v3, version 3,
section 6.1, "Entropic characterization of the spectral radius of a nonnegative matrix".
Lemma 15 identifies normalized circulations as convex combinations of supported
cycle occupation measures. Lemma 16 relates occupation measures to stationary
row-stochastic matrices, including reducible measures. Theorem 17, equation (6.2),
gives the entropy maximum for the actual nonnegative matrix spectral radius;
equation (6.1) specifies the normalized circulation constraints. Lemma 18,
equations (6.3) and (6.4), gives the inequality and positive left/right Perron
attainer under its stated irreducibility and common-support hypotheses.
This locator was checked against that declared primary HTML version on 2026-10-18.

## Application and formal scope

Set mu(i,j)=pi(i)Q(i,j), and use W(i,j)=exp(-c(i,j)/tau) on the original
support. Multiplying Theorem 17's entropy maximum by -tau gives mean cost
minus tau times stationary entropy. Zero-mass rows can be completed on
original graph successors. The owning WeightedWalks exposition gives the
zero-aware KL derivation and attained minimum using existing finite stationary
existence and KL nonnegativity; this application has no separate retained API.

The Lean content constructs the actual Perron data from the attributed
Apache-2.0 MCMC source and relates unrestricted, repeated supported walks to
real weighted matrix powers at every length, including zero. Positive-vector
bounds give growth at every start without aperiodicity, and zero supported
costs count the same walk type. CyclePressure constructs an actual minimizing
simple cycle, bounds every nonempty closed walk, and proves the actual maximum
outdegree bracket and right-hand zero-temperature limit using a potential
comparison and a Perron estimate along walks. These are formalizations of
classical mathematics and carry no new priority claim. The cited section is
the literature anchor for the variational formulation; it is not asserted to
state the Lean unrestricted-walk encoding or every subsequent comparison step.
