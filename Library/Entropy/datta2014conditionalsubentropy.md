---
bibkey: datta2014conditionalsubentropy
authors: Nilanjana Datta, Tony Dorlas, Richard Jozsa, Fabio Benatti
year: 2014
title: "Properties of subentropy"
doi: 10.48550/arXiv.1310.1312
url: https://arxiv.org/abs/1310.1312v1
claim: "Conjecture 2 bounds conditional subentropy of every finite classical-quantum state by minus the natural logarithm of its optimal guessing probability."
strata_touched:
  - D5/S3/Quantum/Measurement/ConditionalSubentropyGuessingBound
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.1310.1312

Source: https://arxiv.org/abs/1310.1312v1

The versioned source is the original paper, published as J. Math. Phys. 55,
062203, DOI 10.1063/1.4882935. The simplex-integral expression is equation (4), PDF page 2;
conditional subentropy is equation (13), PDF page 8; Conjecture 2 is on PDF
page 9.

## Source definitions

Equation (2): “Q(ρ) = ⟨H(M(ρ))⟩_M − C_n where C_n := 1/2 + 1/3 + … + 1/n.”

Equation (3): “this uniform measure (normalised to have total volume unity) is given by dx = (n − 1)! dx_1 … dx_{n−1}.”

Equation (4): “Introducing η(y) := −y ln y, we then obtain a third expression for the subentropy from eq.(2): Q(ρ) = n ∫_{Δn} η(λ · x) dx − C_n.”

Equation (13): “we define the conditional subentropy to be Q(A|B)_ρ := Q(ρ_AB) − Q(ρ_B)”.

The source uses natural logarithms. The simplex has coordinates
$y\in\mathbb R^{n-1}$ with nonnegative entries and sum at most one; its
last barycentric coordinate is one minus their sum. Zero and repeated
eigenvalues are included in equation (4).

## Conjecture 2

“For a c-q state ρ_XB, the conditional subentropy Q(X|B) satisfies the following bound: Q(X|B) ≤ H_min(X|B) = − ln p_guess(X|B).”

“p_guess(X|B) = max_{{E_x}:POVM} Σ_x p_x Tr(E_x ρ^x_B), where the maximization is over all possible POVMs: {E_x : E_x ≥ 0 ∀ x; Σ_x E_x = I}.”

The matrix family $A_x=p_x\rho_B^x$ is positive semidefinite and has total
trace one. Its classical-quantum state is the block diagonal matrix, and
its marginal is the sum of the blocks. The Lean expression uses the
supremum of exactly these POVM scores.

## Attribution boundary

The source definitions and conjecture are literature statements. The
simplex-to-Gaussian correspondence and the resulting proof are repository
derivations. Completeness of the literature screen remains
ASSUMED-UNVERIFIED; the cited source proves the two-pure-signal-state case
in Proposition 6.
