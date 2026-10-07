---
bibkey: nandi2025genuine
authors: S. Nandi
year: 2025
title: "Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)"
doi: 10.48550/arXiv.2509.24045
url: https://arxiv.org/abs/2509.24045v1
claim: "The correlation I2 = C(a,b) + C(a',b'), summed over equal outcomes of local measurements in two mutually unbiased bases, is conjectured to be monotonically non-increasing under LOCC operations."
strata_touched:
  - D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation
license: citation-only
triage: anchor
---

# Nandi, genuine multipartite entanglement detection with MUBs

S. Nandi, *Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)*,
arXiv:2509.24045v1 (28 September 2025, quant-ph); published in EPL 154 (2026),
DOI 10.1209/0295-5075/ae6f48.

## Verified locator

DOI: 10.48550/arXiv.2509.24045.
Primary version: https://arxiv.org/abs/2509.24045v1 (the only arXiv version).
The TeX source `main.tex` of v1 supplies §II (Eqs. (pAB), (cAB), the definition of
$I_2$, the Conjecture and Eq. (10)).

## Source statements (§II)

Mutual predictability: "We denote the joint probability that the outcome of $a$ is $i$ and
the outcome of $b$ is $j$ by $P_{a,b}(i,j)$ given by
\(P_{a,b}(i,j)=\langle i_a|\otimes\langle j_b|\rho|i_a\rangle\otimes|j_b\rangle\)",
"\(C_{a,b}=\sum_{i=0}^{d-1}P_{a,b}(i,i)\)", and, for observables
"\(\{a^\prime, b^\prime\}\in B_2\) which is mutually unbiased to \(B_1\)",
"\(C_{a^\prime,b^\prime}=\sum_{i=0}^{d-1}P_{a^\prime,b^\prime}(i,i)\)" and
"\(I_{2}=C_{a^\prime,b^\prime}+C_{a,b}\)".

Conjecture: "The quantity \(I_2\) is monotonically non-increasing under LOCC operations."
The test that follows considers "POVMs \(\{E_1, E_2\}\) acting locally on a particular
subsystem of a bipartite density matrix \(\rho\)" with
"\(E_1^\dagger E_1+E_2^\dagger E_2=\mathbb{I}\)" and the inequality
"\(I_2(\rho)-p_1I_2(\rho_1)-(1-p)I_2(\rho_2)\ge0\)" (Eq. (10)), where
"\(\rho_k=\frac{(E_k\otimes I).\rho.(E_k\otimes I)^\dagger}{p_k}\),
\(p_k=Tr[\rho (E_k\otimes I)(E_k\otimes I)^\dagger]\)".

## Scope

The paper's numerical check of Eq. (10) (its Fig. 1) uses the Bell state only. For pure
bipartite states it evaluates $I_2$ in the Schmidt basis.
