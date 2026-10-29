---
bibkey: reyes2023tokenspectra
authors: M. A. Reyes and C. Dalfó and M. À. Fiol
year: 2024
title: On the spectra and spectral radii of token graphs
doi: 10.1007/s40590-023-00583-3
url: https://arxiv.org/html/2310.16929v1
claim: "Definition 3.1 takes extrema of consecutive Laplacian spectral multiset differences; Conjecture 3.3 proposes monotonicity of their maxima."
strata_touched:
  - D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation
license: citation-only
triage: anchor
---

# On the spectra and spectral radii of token graphs

The introduction defines F_k(G) on the k-element subsets of V(G).
Two configurations are adjacent exactly when their symmetric difference
is an edge of G, or equivalently one token moves to an unoccupied vertex
along an edge. Section 2.1 fixes simple connected graphs and the ordinary
Laplacian L = D − A. Section 3 explicitly uses Laplacian spectra, sets
F_0(G) = K_1, and records multiplicity-preserving spectral containment (5).

Definition 3.1 defines α_k and ρ_k as the minimum and maximum of the
**multiset** sp F_k(G) minus sp F_(k−1)(G), for 1 ≤ k ≤ floor(n/2).
The following sentence justifies nonemptiness using the strict inequality
choose(n,k) > choose(n,k−1). Conjecture 3.3 states:

> For any graph G, ρ₁(G) ≤ ρ₂(G) ≤ ⋯ ≤ ρ⌊n/2⌋(G).

Primary source: [arXiv:2310.16929v1](https://arxiv.org/html/2310.16929v1),
Section 3, Definition 3.1 and Conjecture 3.3;
[versioned PDF](https://arxiv.org/pdf/2310.16929v1).
The [journal article](https://doi.org/10.1007/s40590-023-00583-3),
*São Paulo Journal of Mathematical Sciences* (2024), Section 3, retains
Definition 3.1 and Conjecture 3.3.
The neighboring Conjecture 3.2 concerns minima, and is a different claim.
The full-sector spectral radii in equation (7) are different quantities
from these new-layer maxima.

Dongsheng Wei, *Generators of stability-preserving semigroups, spectral
gaps, and classical ground-state computation*, [arXiv:2609.26802v1](https://arxiv.org/html/2609.26802v1) §4.6
and [v2](https://arxiv.org/html/2609.26802v2) §7, supplies prior star K₁,₃ / two-token C₆ and full-sector spectral
interpolation ingredients. The inspected passages distinguish full-sector
and new-layer quantities; no novelty of these ingredients or of the
spectral method is asserted. The residual-layer conjecture is the target
here, rather than the full-radius equality characterization in
arXiv:2610.00500 Conjecture 1.1.
