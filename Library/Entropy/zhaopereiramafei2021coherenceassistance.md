---
bibkey: zhaopereiramafei2021coherenceassistance
authors: Ming-Jing Zhao; Rajesh Pereira; Teng Ma; Shao-Ming Fei
year: 2021
title: "Coherence of assistance and assisted maximally coherent states"
doi: 10.1038/s41598-021-85273-8
url: https://arxiv.org/abs/2103.08818v1
claim: "For a real symmetric concave function f on the probability simplex vanishing at the vertices, the pure-state coherence C_f is f of the coherence vector. Its convex roof C_c and its coherence of assistance C_a take the minimum and maximum of the decomposition averages over pure-state decompositions of a mixed state. The paper proves that equal roofs force the pure-state function to be a quadratic form on the range of the state, deduces C_c < C_a for full-rank states, and asks whether C_c < C_a holds for all mixed states."
strata_touched:
  - D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality
license: citation-only
triage: anchor
---

# Zhao, Pereira, Ma and Fei, Coherence of assistance and assisted maximally coherent states

M.-J. Zhao, R. Pereira, T. Ma and S.-M. Fei, arXiv:2103.08818v1 [quant-ph]; Scientific Reports 11, 5935 (2021). Quotations are from the v1 TeX source.

The class of functions:

> Let ${\mathfrak{{F}}}=\{f\}$ be the set of functions on the probability simplex $\Omega=\{\vec{x}=(x_0,x_1,\cdots,x_{n-1})^T|\sum_{i=0}^{n-1} x_i =1 \ \text {and} \ x_i\geq0 \}$ such that (i) $f$ is a real symmetric concave function; (ii) $f((1,0,\cdots,0)^T)=0$.

For $f\in\mathfrak F\setminus\{0\}$ the pure-state measure is $C_f(|\psi\rangle)=f(\mu(|\psi\rangle))$, with the coherence vector $\mu(|\psi\rangle)=(|\psi_0|^2,\dots,|\psi_{n-1}|^2)^T$. The coherence of convex roof $C_c(\rho)$ and the coherence of assistance $C_a(\rho)$ are the minimum and the maximum of $\sum_kp_kC_f(|\psi_k\rangle)$ over all pure-state decompositions $\rho=\sum_kp_k|\psi_k\rangle\langle\psi_k|$.

Theorem `th ca=cc`:

> Let $\mathcal{H}$ be a finite-dimensional Hilbert space and $F$ a nonnegative function defined on the pure states in $\mathcal{H}$. Let $\rho_o$ be a density matrix on $\mathcal{H}$ and $R(\rho_o)$ the range of $\rho_o$. If $F_a(\rho_o)=F_c(\rho_o)$, then there exists a positive semidefinite operator $Q$ on $R(\rho_o)$ such that $F(|\psi\rangle)=\langle \psi |Q| \psi \rangle$ for all pure states $|\psi\rangle$ in $R(\rho_o)$.

Corollary `cor coh`:

> For full rank quantum states $\rho$, the coherence of assistance is strictly larger than the coherence of convex roof, $C_c(\rho)< C_a(\rho)$.

The question, in the paragraph "Relation between the convex roof extension and the least concave majorant extension":

> The strict relation between the coherence of convex roof and the coherence of assistance, that is, whether $C_c(\rho)< C_a(\rho)$ holds for all mixed quantum states is an interesting topic.

## Verified locator

Source: https://arxiv.org/abs/2103.08818v1
- DOI: https://doi.org/10.1038/s41598-021-85273-8 (Scientific Reports 11, 5935; published online 15 March 2021; title, authors, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/2103.08818v1. The e-print is a single gzipped file `ZhaoMJ-AMC4.tex` (502 lines, md5 `91c15498f4ee964803bd2694ee500287`). Locations:
  - the class $\mathfrak F$, l. 189;
  - $C_f$, the coherence vector and the two roofs, l. 207–236;
  - the question, l. 303;
  - Theorem `th ca=cc`, l. 314–317;
  - Corollary `cor coh`, l. 324–326.
- The arXiv record lists one version (v1, 16 March 2021) and the journal reference "Scientific Reports (2021) 11:5935" (arXiv API metadata).
