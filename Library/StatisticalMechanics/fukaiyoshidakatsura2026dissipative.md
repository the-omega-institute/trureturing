---
bibkey: fukaiyoshidakatsura2026dissipative
authors: K. Fukai; H. Yoshida; H. Katsura
year: 2026
title: "Dissipative free fermions in disguise"
doi: 10.48550/arXiv.2603.22163
url: https://arxiv.org/abs/2603.22163v1
claim: "The expectation after Eq. (17) places every root of the plus dissipative independence polynomial in the open upper half-plane for ECF graphs, under the standing shared-root exclusion after Eq. (26)."
strata_touched:
  - D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation
license: citation-only
triage: anchor
---

# Fukai, Yoshida and Katsura, dissipative free fermions in disguise

Printed p. 4, after Eq. (17):

> We expect Im ũ_k > 0 to hold for general ECF graphs, as observed numerically in the boundary-driven Fendley model, so that ε̃_k ≡ 1/ũ_k satisfies Im ε̃_k < 0.

The roots ũ_k are those of the plus polynomial in Eq. (16), printed p. 4:

$$
\widetilde P_G^{\pm}(u)\equiv P_G(u^2)\pm i\gamma u P_{G\setminus K_s}(u^2).
$$

Printed p. 3, Eq. (7):

> The independence polynomial is defined as

$$
P_G(x)\equiv\sum_{S\in\mathcal S_G}(-x)^{|S|}\prod_{j\in S}b_j^2,
$$

> where S_G denotes the collection of all independent sets.

Printed p. 2:

> A graph is claw-free if it has no claw as an induced subgraph (Fig. 1(a)), and even-hole-free if it has no even hole as an induced subgraph (Fig. 1(b)).

The couplings b_j are real and γ > 0 is the dissipation rate in the jump operator ℓ = √γ χ. ECF means even-hole-free and claw-free. Printed p. 3:

> The edge operator χ is associated with a clique K_s ⊆ V(G), i.e., a subset of mutually adjacent vertices.

> Equivalently, denoting the closed neighborhood of j by Γ[j] ≡ {j} ∪ {ℓ ∈ V(G) | A_jℓ = 1}, K_s is simplicial if and only if Γ[j] \ K_s is a clique for all j ∈ K_s.

Printed p. 7, after Eq. (26):

> Equation (26) shows that N_k = 0 if P_G and P_{G\K_s} share the root u_k². Throughout this work, we exclude this nongeneric case [80].

The root statement retains this exclusion. Its proof uses finite-clique deletion and a positive-imaginary multiplier for points in the lower half-plane. Even-hole-freeness is retained in the source statement but is unused by the proof. The Liouvillian spectral interpretation and gap formula are the paper's derivation; they are not separate Lean statements here. Common-root cases and quantitative uniform root-height bounds remain separate questions.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2603.22163
- URL: https://arxiv.org/abs/2603.22163v1
- Version 1, printed pp. 3–4 (Eqs. (7), (16), simpliciality and the expectation), printed p. 7 (Eq. (26) and the standing exclusion).
