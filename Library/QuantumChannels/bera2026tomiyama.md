---
bibkey: bera2026tomiyama
authors: A. Bera, B. Bhattacharya, D. Chruściński
year: 2026
title: "Tomiyama-type maps with a diagonal perturbation"
doi: 10.48550/arXiv.2604.18600
url: https://arxiv.org/abs/2604.18600v1
claim: "Conjecture 2.4: the k-positive maps of the family Φ_{α,β} = (1−α−β) id + α τ₀ + β Δ on M_d form the quadrilateral conv{Ψ₀, Ψ₁, Ψ₂, 𝒯_k}; proved by the authors for β ≤ 0, for k dividing d and for k = d − 1, and stated as open in general."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity
license: citation-only
triage: anchor
---

# Bera, Bhattacharya and Chruściński, Tomiyama-type maps with a diagonal perturbation

A. Bera, B. Bhattacharya and D. Chruściński, *Tomiyama-type maps with a diagonal
perturbation*, arXiv:2604.18600v1 (9 April 2026; math.RA, cross-listed math.OA and quant-ph).

## Verified locator

DOI: 10.48550/arXiv.2604.18600.
Primary version: https://arxiv.org/abs/2604.18600v1 (the only arXiv version).
The TeX source `Tomiyama_plus.tex` of v1 supplies Eq. (6) (the family), §2.1 (positivity,
complete positivity and the parameter points), §2.2 (Conjecture 2.4 and Propositions 2.5, 2.6
and 2.8) and §4. Numbering is the printed one; the caption of Figure 2 calls the conjecture
"Conjecture 3.1".

## Source statements

Eq. (6): "$\Phi_{\alpha,\beta} = (1-\alpha-\beta)\, \mathcal{I} + \alpha \,\tau_0 + \beta\, \Delta ,~~~\alpha,\beta \in \mathbb{R}$",
with "$\tau_0(X) = \frac{\I}{d} \Tr\, X$" and "$\Delta(X)$ denotes a projection to the diagonal of $X \in \Md$".

Parameter points (§2.1): "$\Psi_0 \leftrightarrow (0,0) \ , \Psi_1 \leftrightarrow \left(0,\frac{d}{d-1}\right) \ , \ \Psi_2 \leftrightarrow \left(\frac{d}{d-1},-\frac{1}{d-1}\right)$";
"$\mathcal{T}_1 \leftrightarrow \left(\frac{d}{d-1},0\right) \ , \ \mathcal{P} \leftrightarrow \left(\frac{d}{d-1},-\frac{2}{d-1}\right)$";
and from Tomiyama's theorem "$\alpha_k := \frac{kd}{kd-1}$", "$\mathcal{T}_k := \Phi_{\alpha_k}$".

Corollary 2.3: "a set of positive maps forms a quadrilateral containing CP triangle
$\mathcal{P}_1 = {\rm conv} \{\Psi_0,\Psi_1,\mathcal{T}_1,\mathcal{P}\}$".

Conjecture 2.4: "A set of $k$-positive maps $\Phi_{\alpha,\beta}$ forms a quadrilateral
$\mathcal{P}_k = {\rm conv} \{\Psi_0,\Psi_1,\Psi_2,\mathcal{T}_k\}$." Followed by: "Since CP maps
$\{\Psi_0,\Psi_1,\Psi_2\}$ are $k$-positive the above set contains $k$-positive maps only. Our goal
is to show that if $\Phi_{\alpha,\beta}$ is $k$-positive it must belong to $\mathcal{P}_k$. For
$k=1$ it reduces to Corollary \ref{cor1}."

§4: "The full proof of the conjectured characterization of $k$--positive maps for arbitrary $k$
and $d$ is still missing."

## Scope

The authors prove the conjecture for $\beta\le0$ (Proposition 2.5, using the vector
$\sum_{i\le k}e_i\otimes e_i$), for $k\mid d$ (Proposition 2.6, using block vectors of $\ell=d/k$
coordinates) and for $k=d-1$ (Proposition 2.8). The open part is $\beta\ge0$ for the other
$k$. The sentence about $k=1$ does not hold as printed: $\mathcal P\in\mathcal P_1$ violates
$\alpha/d+\beta\ge0$, so $\mathcal P_1\ne\mathrm{conv}\{\Psi_0,\Psi_1,\Psi_2,\mathcal T_1\}$.
