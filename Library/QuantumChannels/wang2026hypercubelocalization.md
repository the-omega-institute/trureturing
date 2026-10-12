---
bibkey: wang2026hypercubelocalization
authors: Ce Wang
year: 2026
title: "Spectral Criterion for Disorder-Free Localization of Quantum Walks on Hypercube: QBN Approach"
doi: null
url: https://arxiv.org/abs/2609.07267v1
claim: "Conjecture 4.1 asserts a nonuniform fixed point for the all-plus spin-coupled Grover walk on every even hypercube of dimension at least four."
strata_touched:
  - D5/S3/Quantum/Dynamics/SpinCoupledEvenHypercubeGroverFixedPoint
license: citation-only
triage: anchor
---

# Spectral Criterion for Disorder-Free Localization of Quantum Walks on Hypercube: QBN Approach

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2609.07267v1

Section 3, page 6, Proposition 3.4 (`prop:reduced_evolution`) gives the reduced evolution operator (3.14). Section 4, page 11, Proposition 4.3 gives the fixed-point equation (4.4), and Corollary 4.4 (`cor:fixed_point_DFL`) gives the implication from a nonzero fixed point with nonconstant position weights to disorder-free localization. Page 12 defines the Grover coin and the distance-dependent coupling. Propositions 4.5–4.6, pages 12–13, treat dimensions four and six. Conjecture 4.1 (`conj:DFL_general`) is on page 13.

Crossref title search for the full title returned no exact title match among its five results; no Crossref DOI was found for this source.

## Source statement

> For every even \(d\ge 4\), the spin-coupled Grover walk on the \(d\)-dimensional hypercube with coupling \(\phi_\sigma=|\sigma|\pi/d\) and all \(+1\) spin configuration exhibits disorder-free localization. Equivalently, the reduced evolution operator \(\tilde W_{\mathbf s}\) possesses a fixed point whose position distribution is non-uniform.

With all spins equal to +1, the coin-amplitude form of the reduced operator is

$$
(Wu)(\tau,k)=\exp\left(-i\pi|\tau\triangle\{k\}|/d\right)
\left(\frac{2}{d}\sum_j u(\tau\triangle\{k\},j)-u(\tau\triangle\{k\},k)\right).
$$

A position vertex is a subset of the d coordinate indices. Its unnormalized position weight is the sum over coin coordinates of the squared complex norm. Corollary 4.4 normalizes a nonzero fixed point; division by its total squared norm preserves nonconstancy.

The construction in `SpinCoupledEvenHypercubeGroverFixedPoint.result` proves the equivalent fixed-point clause using paired-coordinate signs and three adjacent Hamming layers. The implication to disorder-free localization uses Corollary 4.4 of the paper. The Lean claim does not formalize the quantum Bernoulli noise Hilbert-space presentation or the full spectral criterion.
