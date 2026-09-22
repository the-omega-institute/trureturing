---
bibkey: pronko2025fredkin
authors: Andrei G. Pronko
year: 2025
title: 'Symmetries of the periodic Fredkin chain'
doi: 10.1088/1751-8121/ae1644
url: https://doi.org/10.1088/1751-8121/ae1644
claim: The paper defines the periodic Fredkin Hamiltonian and the operators Sigma plus and minus, then states as Conjecture 1 that they annihilate every non-cyclic invariant eigenstate.
strata_touched:
  - D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation
license: citation-only
triage: anchor
---

# Symmetries of the Periodic Fredkin Chain

Pronko works on the state space `(ℂ²)^{⊗N}` with basis vectors indexed by
spin words. In section 2.1, printed p. 3, the paper states:

> We denote basis vectors in ℂ² by |↑⟩ = (1, 0)ᵀ, |↓⟩ = (0, 1)ᵀ. The basis in
> End(ℂ²) is provided by the Pauli matrices σ⁺ = [[0, 1], [0, 0]], σ⁻ =
> [[0, 0], [1, 0]], σᶻ = [[1, 0], [0, −1]]. We will also use projectors onto
> the spin-up and spin-down states: n↑ = ½(1 + σᶻ), n↓ = ½(1 − σᶻ).

The same section, printed p. 3, identifies the `j`th tensor factor with the
`j`th site, defines `P_{j,j+1}` as the operator exchanging adjacent copies, and
sets

> Π_{j,j+1} = ½(1 − P_{j,j+1}).

It then gives the Hamiltonian density and periodic Hamiltonian:

> F_{j,j+1,j+2} = n↑_j Π_{j+1,j+2} + Π_{j,j+1} n↓_{j+2}. (2.2)
>
> H = Σ_{j=1}^{N} F_{j,j+1,j+2}. (2.3)

with site indices identified modulo `N`. Across printed pp. 3-4, the cyclic
operator is given in ordered product form:

> C = P_{1,2} · · · P_{N−2,N−1} P_{N−1,N}

and is described as acting on sites by `i ↦ i + 1`.

Theorem 2, equation (3.1), printed pp. 6-7, defines

> Σ^± = Σ_{r₁,...,r_N ∈ {−1,0,1}, r₁+···+r_N = ±1}
> σ₁^{r₁} · · · σ_N^{r_N}. (3.1)

where `σ_i^0 = 1` and `σ_i^{±1} = σ_i^±`. Conjecture 1,
printed p. 7, is:

> The operators Σ^± annihilate all non-cyclic invariant (C ≠ 1)
> eigenstates of the Hamiltonian.

The formal statement uses complex scalars, the convention `0 = up` and
`1 = down`, sites modulo `N`, and `N >= 3`. An eigenstate is a nonzero vector
that is an eigenvector of both `H` and `C`; non-cyclic means that its
`C`-eigenvalue differs from one. The formal proof retains the Hamiltonian
eigenvector hypothesis but establishes annihilation from the `C`-eigenvector
hypothesis alone.

## Verified locator

- DOI: 10.1088/1751-8121/ae1644
- URL: https://doi.org/10.1088/1751-8121/ae1644
- Source locations: section 2.1, printed pp. 3-4; Theorem 2, equation (3.1), printed pp. 6-7; Conjecture 1, printed p. 7.
