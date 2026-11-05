---
bibkey: aksoyetal2023asynchrony
authors: Sinan G. Aksoy; Ryan Bennink; Yuzhou Chen; José Frías; Yulia R. Gel; Bill Kay; Uwe Naumann; Carlos Ortiz Marrero; Anthony V. Petyuk; Sandip Roy; Ignacio Segovia-Dominguez; Nate Veldt; Stephen J. Young
year: 2023
title: "Seven open problems in applied combinatorics"
doi: 10.4310/JOC.2023.v14.n4.a8
url: https://arxiv.org/abs/2303.11464v1
claim: "The section on the price of asynchrony models delayed block updates of x ↦ Mx by a linear operator M^(δ) on the stacked history, shows that its spectral radius does not depend on the history length and equals ρ(M)^(1/(k+1)) for uniform delay k, and asks whether ρ(M^(δ)) ≤ ρ(M)^(1/(k+1)) for every delay pattern with entries in [k], or at least whether ρ(M^(δ)) ≤ f(ρ(M), k) for some f with values in (0,1)."
strata_touched:
  - D5/S3/Quantum/Matrix/AsynchronousIterationSpectralRadiusRefutation
license: citation-only
triage: anchor
---

# Seven open problems in applied combinatorics

S. G. Aksoy, R. Bennink, Y. Chen, J. Frías, Y. R. Gel, B. Kay, U. Naumann, C. Ortiz Marrero, A. V. Petyuk, S. Roy, I. Segovia-Dominguez, N. Veldt and S. J. Young, arXiv:2303.11464v1 [math.CO]; Journal of Combinatorics 14(4), 559–601 (2023). Quotations are from the section "Price of Asynchrony" of the v1 TeX source.

The model:

> To build a simple model of asynchronous updates for $M$, we partition the matrix $M$ into an $\ell \times \ell$ array of blocks and for each $i \in [\ell]$ define the update scheme $\tilde{x}_i^{(k+1)} = \sum_j M_{ij}\tilde{x}_j^{(k - \delta_{ji})}$ where $\delta_{ji}$ represents the ``delay" in information from compute node $j$ reaching compute node $i$ (and so we assume that $\delta_{ii}=0$).

(the display is written inline here).

The open problem:

> Let $M$ be a $n \times n$ real matrix with $p(M)= \lambda < 1$ partitioned into an $\ell \times \ell$ array of blocks.  Is it the case that for all elements $\delta$ of $[k]^{\ell \times \ell}$ with zero diagonals, $\rho(M^{(\delta)}) \leq \lambda^{\nicefrac{1}{k+1}}?$  If not, is there some function $f \colon (0,1) \times \N \rightarrow (0,1)$ such that $\rho(M^{(\delta)}) \leq f(\lambda,k)$?

## Verified locator

Source: https://arxiv.org/abs/2303.11464v1
- URL: https://arxiv.org/abs/2303.11464v1 (source `Sections/ratfish.tex`, md5 `08f1f56ce6f899219ee74094fe3c0e53`):
  - the model and the operator $M^{(\delta,\kappa)}$, l. 46–49;
  - Lemma `L:spectra` (independence of $\kappa$), l. 51–64;
  - Lemma `L:uniform` (uniform delays), l. 66–72;
  - the open problem, l. 75–77;
  - the experiments and the variant $\rho(M^{(\delta)})\le\rho(M)^{1/\max\delta}$, l. 148.
- DOI: 10.4310/JOC.2023.v14.n4.a8 (https://doi.org/10.4310/JOC.2023.v14.n4.a8; Crossref lists Journal of Combinatorics, volume 14, issue 4, pages 559–601).
