---
bibkey: fannes2011fidelity
authors: M. Fannes, F. de Melo, W. Roga, K. Życzkowski
year: 2011
title: "Matrices of fidelities for ensembles of quantum states and the Holevo quantity"
doi: null
url: https://arxiv.org/abs/1104.2271v1
claim: "Conjecture 1 bounds the Holevo quantity of every three-state ensemble by the entropy of its root-fidelity matrix."
strata_touched:
  - D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy
  - D5/S3/Quantum/Divergence/FannesRootFidelityHolevo
license: citation-only
triage: anchor
---

# Three-state root-fidelity Holevo bound

## Verified locator

Source: https://arxiv.org/abs/1104.2271v1

The arXiv version's page 10, Conjecture 1, states:

> For any ensemble E₃ = {(pᵢ, ϱᵢ)} with K = 3 three states of arbitrary dimension d the corresponding Holevo quantity χ(E₃) is bounded from above by the entropy of the matrix C√F(E₃) defined in (16): χ(E₃) ≤ S(C√F(E₃)).

Equation (2) defines χ(Eₖ) = S(ϱ) − ∑ᵢ pᵢ S(ϱᵢ), with ϱ = ∑ᵢ pᵢϱᵢ and S(σ) = −Tr(σ log σ). Equation (16) defines C√F(E₃) = [√(pᵢpⱼ)√Fᵢⱼ]ᵢⱼ. Root fidelity is Tr|√ϱᵢ√ϱⱼ|. The logarithm is natural; singular states and zero weights are included.

## Scope and evidence

The source establishes positivity of the three-state fidelity matrix, the pure-state entropy bound, and damped bounds. The unrestricted mixed-state proof uses simultaneous rank-one decompositions, a three-by-three modulus entropy comparison, and channel data processing.

The numerical experiment is in the-omega-institute/trureturing-experiments at commit f3702d38787bb44e22335abf5746e5768e6b7d18, path docs/reports/fannes-demelo-roga-zyczkowski-2012-root-fidelity-holevo-bound/check.py, SHA256 e4a6970946d8482e8326b1200461dba8ddef55290a04b22b7e69536960474984; its recorded exit code is 0. No program text is reproduced here.

The preregistration's literature screen found partial results in Zhang–Wu–Fei, arXiv:1110.5979, and Roga's thesis, arXiv:1108.5065. Completeness of the search for prior settlements is ASSUMED-UNVERIFIED. No equality classification or extension to four states is asserted.
