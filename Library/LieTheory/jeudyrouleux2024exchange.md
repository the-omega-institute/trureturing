---
bibkey: jeudyrouleux2024exchange
authors: C. Jeudy; M. Rouleux
year: 2024
title: Generalized exchange operators for a system of spin-1 particles
doi: 10.1088/1742-6596/2912/1/012043
url: https://arxiv.org/abs/2411.03952v1
claim: Section 3.1 expects the spin-1 three-particle Schrödinger Hamiltonian to belong to the Lie algebra of the global-label Q-representation.
strata_touched:
  - D5/S3/Quantum/Algebra/JeudyRouleuxGlobalPermutationLie
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1088/1742-6596/2912/1/012043

Source: https://arxiv.org/abs/2411.03952v1

## Source statements

Section 3.1, Definition 4, p. 6:

“We call Q-representation the product representation (S(2S+1), ℋ, Q), ℋ = ℂ^{(2S+1)^N} the N-lift of Q̃, defined on transpositions (ij) by Q(ij) = Q̃(ij) ⊗ ⋯ ⊗ Q̃(ij) (N times).”

Section 3.1, pp. 6–7:

“At least in case of (S,N) = (1/2,N) and (S,N) = (1,3) it is easy to see that the Q(ij) span a Lie algebra L of operators on the total space ℋ and that the Cayley table for [Q(α), Q(β)] is identical to this of [Q̃(α), Q̃(β)].”

“Moreover since that the CSCO of the P- and Q-reps are the same in this case (see [Jin], p.70), we expect that Schrödinger Hamiltonian P_S, as well as other Hamiltonians, belongs to L.”

Section 2, equation (7), p. 4:

“We can then form the multi-particle (non-linear) Hamiltonian (Schrödinger Hamiltonian) H_S(S,N) = Σ_{⟨i,j⟩} P_S(S_i · S_j).”

## Encoding and boundary

The basis labels are functions Fin 3 → Fin 3, with zero-based particle and state indices. The entry of Q α at (x,y) is 1 exactly when x = α ∘ y. The entry of exchange i j is 1 exactly when x = y ∘ Equiv.swap i j. The Hamiltonian is exchange 0 1 + exchange 0 2 + exchange 1 2. The Lie algebra is LieSubalgebra.lieSpan over ℂ of Set.range Q, so all six permutations of the three labels are included. The claim is that this Hamiltonian belongs to that Lie algebra.

The refutation separates these operators by the diagonal projector onto x 0 = x 1. Section 6's enlarged space L̂ = L₁ + L₁* is outside the claim. The source's other spectral and representation statements are outside this result.

## Numerical comparison

The independent finite checker is in the-omega-institute/trureturing-experiments, commit 352da164a5a41fe1a3ac2513708bc49b3f6458a1, at docs/reports/jeudy-rouleux-2024-global-permutation-lie-algebra/check.py. Its SHA-256 is 52f066d07dbde5dad272df429584deeb0c40cf5b230c994825cd3a0d8a0c3240. The command python3 check.py exits 0 with RESULT PASS. This numerical evidence is distinct from the Lean proof.

## Literature boundary

The preregistration at https://github.com/the-omega-institute/trureturing/issues/19130 reports zero citing works in OpenAlex and a Semantic Scholar HTTP 429 response. Completeness of the literature screen is ASSUMED-UNVERIFIED.
