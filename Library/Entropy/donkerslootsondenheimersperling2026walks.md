---
bibkey: donkerslootsondenheimersperling2026walks
authors: Emil K. F. Donkersloot; René Sondenheimer; Jan Sperling
year: 2026
title: "Multipartite entanglement dynamics in quantum walks"
doi: 10.48550/arXiv.2603.24679
url: https://arxiv.org/abs/2603.24679v1
claim: "The paper computes the geometric measure of multipartite entanglement of single-walker quantum walks in linear optical networks, where one photon in M modes is a generalized W state, studies the Hadamard walk on a circle of P positions with localized initial coins, and, from numerics for all tested graph sizes and times, expects the symmetric coin (|-> + i|+>)/sqrt 2 to always yield the maximum entanglement for the partition into individual modes."
strata_touched:
  - D5/S3/Quantum/Walks/SymmetricCoinMaximalWalkEntanglement
license: citation-only
triage: anchor
---

# Donkersloot, Sondenheimer and Sperling, multipartite entanglement of quantum walks

E. K. F. Donkersloot, R. Sondenheimer and J. Sperling, arXiv:2603.24679v1 [quant-ph] (25 March 2026), DOI 10.48550/arXiv.2603.24679 (the arXiv DataCite DOI); the arXiv record gives no journal reference. Quotations are from the v1 TeX source, with macros expanded and cross-references omitted.

The Hadamard walk on a circle (Section II A): the coin space is $\mathrm{span}\{|-\rangle,|+\rangle\}$, the coin is $\hat H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, the step operator moves $|-,x\rangle$ to $|-,x-1\rangle$ and $|+,x\rangle$ to $|+,x+1\rangle$ with periodic positions $x\in\{0,\dots,P-1\}$, and $|\Psi(n)\rangle=\hat T^n|\psi_0\rangle$ with $\hat T=\hat S(\hat H\otimes\mathbb 1)$. A single walker is one photon in the $M=2P$ optical modes.

Entanglement (Sections II B–C): $g_{\max}$ is the supremum of $|\langle\vec\chi|\psi\rangle|^2$ over normalized product states for the partition, $E_g=1-g_{\max}$, and single-photon states are the generalized W states $|\psi\rangle=\sum_{i=1}^M\lambda_i|1_i\rangle$.

The expectation (Section III C 2), for localized initial states $\big(\cos\frac\theta2|-\rangle+e^{i\phi}\sin\frac\theta2|+\rangle\big)\otimes|0\rangle$ and the partition into individual modes:

> The choice $\theta=\pi/2,\, \phi=\pi/2$ for the angles that define the initial coin corresponds to a symmetric walk as the evolutions of the two components of the initial state, $|-,0\rangle$ and $i|+,0\rangle$, do not interfere. Hence, we expect this walk to always yield the maximum entanglement. This is indeed the observed behavior for all graph sizes and time steps we have tested.

## Verified locator

Source: https://arxiv.org/abs/2603.24679v1
- DOI: https://doi.org/10.48550/arXiv.2603.24679 (the arXiv-issued DataCite DOI; no journal version is listed).
- URL: https://arxiv.org/abs/2603.24679v1 (the e-print is a gzipped tar archive; member `arxiv-v1.tex`, 1099 lines, md5 `d663ab8d3f72affb6922ca126d775cee`):
  - the Hadamard walk on a circle, l. 139–166;
  - the optical modes of a single walker, l. 168–213;
  - entanglement, $g_{\max}$ and $E_g$, l. 223–279;
  - generalized W states, l. 286–295;
  - localized initial states, l. 423–425;
  - the expectation, l. 651–654.
- The author list and the version date are from the arXiv metadata.
