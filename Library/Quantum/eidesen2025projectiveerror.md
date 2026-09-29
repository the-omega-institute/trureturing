---
bibkey: eidesen2025projectiveerror
authors: Jonas Eidesen
year: 2025
title: "Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes"
doi: 10.48550/arXiv.2506.01843
url: https://arxiv.org/abs/2506.01843v3
claim: "The paper models quantum errors by projectively faithful irreducible projective representations of finite groups, compares stabilizer codes, Clifford codes and weak stabilizer codes, characterizes weak stabilizer Clifford codes for nice error bases, and asks (Question 11.3) whether a code with |G| = |L(W)| |S(W)| and a non-normal stabilizer group S(W) exists when |G| = (dim V)^2."
strata_touched:
  - D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer
license: citation-only
triage: anchor
---

# Projective error models: Stabilizer codes, Clifford codes, and weak stabilizer codes

Eidesen works with finite groups and unitary representations on
finite-dimensional complex Hilbert spaces. A projective representation of `G`
on `V` is a map `π : G → U(V)` whose composite with the quotient
`q : U(V) → PU(V)` is a homomorphism, equivalently
`π(x)π(y) = σ(x, y)π(xy)` with `σ` in the circle group; it is projectively
faithful if `q ∘ π` is injective. A projective error model on `V` is a pair
`(G, π)` with `π` a projectively faithful irreducible projective
representation (Definition 3.2). For a subspace `W` with orthogonal projection
`P_W`, the paper defines the logical operators and the stabilizers

> L_{(G,π)}(W) := { x ∈ G : P_W π(x) = π(x) P_W },
> S_{(G,π)}(W) := { x ∈ G : P_W π(x) P_W ∈ 𝕋 P_W }.

Proposition 8.1 gives, for every `n ≥ 2`, the projective error model
`G = C₂ × D_{2n} = ⟨a, b, c | a^{2n} = b² = c² = [a, c] = [b, c] = 1, bab = a⁻¹⟩`
on `ℂ⁴` with `π(cᵏ bˡ aᵐ)` the product of the `k`-th power of the block swap,
the `l`-th power of `X ⊕ X` and the `m`-th power of `P ⊕ (−P)`, where `X` is
the Pauli matrix and `P = diag(1, ζ_{2n})`; for `n = 2` the dihedral factor has
order 8 and `P = diag(1, i)`. Section 11 records that the author has been unable to
produce a code that is both a Clifford code and a weak stabilizer code but not
a stabilizer code, and restates this for `|G| = (dim V)^2` as Question 11.3:

> Does there exist a Hilbert space V, a subspace W ⊂ V, and a projective error
> model (G, π) ∈ PEM_V with |G| = (dim V)^2, such that the equation
> |G| = |L_{(G,π)}(W)| · |S_{(G,π)}(W)| holds, but S_{(G,π)}(W) is not normal
> in G?

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2506.01843
- URL: https://arxiv.org/abs/2506.01843v3
- Version and location: arXiv:2506.01843v3 (v1 2025-06-02, v3 2026-02-25), source file `Projective_error_models.tex`: §2 for projective representations and projective faithfulness; §3 for Definition 3.2 (projective error model); §6 for `L_{(G,π)}(W)` and `S_{(G,π)}(W)`; §8 for Proposition 8.1; §11 for Question 11.3 (the `question` environment labelled `Q3`, numbered with the definition counter within sections).
