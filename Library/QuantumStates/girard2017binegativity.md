---
bibkey: girard2017binegativity
authors: Mark W. Girard; Gilad Gour
year: 2017
title: "The binegativity of two qubits"
doi: 10.48550/arXiv.1701.02724
url: https://arxiv.org/abs/1701.02724v3
claim: "For a two-qubit state sigma with partial transpose sigma^Gamma, the negativity is N(sigma) = 2 Tr[(sigma^Gamma)_-] and the binegativity is N_2(sigma) = Tr[(sigma^Gamma)_-] + 2 Tr[(((sigma^Gamma)_-)^Gamma)_-], where X_+ and X_- are the positive and negative components of a self-adjoint X. Based on randomly generated states, the paper conjectures that nu (c + nu)(nu + 1)/((c + nu)^2 + 2c(1 - c)) <= N_2(sigma) <= (nu/2)(c + nu)^2/(c^2 + nu^2) for all states with negativity nu and concurrence c."
strata_touched:
  - D5/S3/Quantum/Entanglement/TwoQubitBinegativityUpperBoundRefutation
license: citation-only
triage: anchor
---

# The binegativity of two qubits

Mark W. Girard, Gilad Gour, arXiv:1701.02724v3 (quant-ph), 2017. No journal
version is listed on arXiv. Quotations are from the arXiv v3 source, with its
macros kept as printed (`\Gammaminus` is $\Gamma_{\!-}$).

The negativity:

> The negativity can be written as $N(\sigma) = 2\Tr[\sigma^{\Gammaminus}]$, where we use the notation $\sigma^{\Gammaplus}:=(\sigma^\Gamma)_+ \quad\text{ and }\quad \sigma^{\Gammaminus}:=(\sigma^\Gamma)_-$ to denote the positive and negative components of the partially transposed $\sigma$, respectively.

The binegativity:

> In this paper we introduce a computable quantity that we call \emph{binegativity} given by $N_2(\sigma):=\Tr[\sigma^{\Gammaminus}] + 2\Tr[\sigma^{\Gammaminus\Gammaminus}],$ where $\sigma^{\Gammaminus\Gammaminus} = ((\sigma^\Gammaminus)^\Gamma)_-$.

The conjecture (Eq. (9)):

> In general, based on numerical evidence from randomly generated states, we conjecture that the the binegativity of two-qubit states is bounded by $\nu\frac{(c+\nu)(\nu+1)}{(c+\nu)^2+2c(1-c)}\leq N_2(\sigma)\leq \frac{\nu}{2}\frac{(c+\nu)^2}{c^2+\nu^2}$ for all states $\sigma$ with fixed negativity $N(\sigma)=\nu$ and concurrence $C(\sigma)=c$.

The concurrence is the standard two-qubit concurrence (the paper cites
Hill–Wootters and Wootters): the infimum of $\sum_ip_iC(\psi_i)$ over the
decompositions $\sigma=\sum_ip_i|\psi_i\rangle\langle\psi_i|$, with
$C(\psi)=2|\psi_{00}\psi_{11}-\psi_{01}\psi_{10}|$.

The encoding indexes two-qubit matrices by `Fin 2 × Fin 2`, takes the
partial transposition on the second qubit (the binegativity does not depend
on which qubit is transposed), uses Mathlib's negative part of a self-adjoint
matrix, and reads the negativity as twice the sum of the absolute values of
the negative eigenvalues of $\sigma^\Gamma$, which equals
$2\Tr[\sigma^{\Gamma}_-]$.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1701.02724 (the arXiv DOI; no
  journal version is listed).
- URL: https://arxiv.org/abs/1701.02724v3 (v3, 2017-02-10, the latest
  version; arXiv comment "v3: previous versions contained an erroneous proof
  claiming that the binegativity is a monotone"; source
  `binegativity_v9.tex`, md5 `377c42f23d1a50af36324a4ea5bfd221`): the
  negativity (l. 178–186), the binegativity (l. 188–192) and the conjecture
  (l. 277–281).
