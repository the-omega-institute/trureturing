---
slug: hivert-scott-2026-okada-discriminant-refutation
bibkey: hivert2026okada
doi: 10.48550/arXiv.2609.01440
url: https://arxiv.org/abs/2609.01440v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Combinatorics/OkadaDiscriminantRefutation.result
---

# Refutation of the Okada regular-trace discriminant identity

## Problem

Florent Hivert and Jeanne Scott, *Diagrammatic Okada monoid and cellularity of the Okada algebra*, arXiv:2609.01440v1, Conjecture 7.9, page 60:

> det G_N = ∏_{S ∈ 𝕐𝔽𝕊_N} [det G^S_N]^{2 dim(Fib(S))}.

The preamble defines G_N(σ,τ) as tr[ϱ^reg(E_σ)ϱ^reg(E_τ)], where ϱ^reg is the left-regular representation of the Okada algebra. The parameters are a positive integer N, an arbitrary field K, X = (x₁,…,x_{N−1}) and Y = (y₁,…,y_{N−2}). The algebra has relations E_i² = x_i E_i, distant commutation, and E_{i+1}E_iE_{i+1} = y_i E_{i+1}. The conjecture concerns exact equality with this regular trace.

## Motivation

The conjecture connects the discriminant in the permutation-word basis to the Gram determinants of the half-diagram cell forms. The settling declaration is `D5/S0/Certificates/Combinatorics/OkadaDiscriminantRefutation.result`.

## Gap

This is a tier-1 published named conjecture, preregistered in #11538. The scoped literature check there distinguishes the exact equality from the factorization up to an unspecified constant discussed in MathOverflow question 454343. The search reported there finds no settlement of this exact equality in the checked arXiv version and citing papers; it is not an exhaustive publication-priority claim.

## Route

Use the quotient of the free algebra by the paper's three relations. Over Q with N = 3, X = (1,2), Y = (1), the words (1,E₁,E₂,E₁E₂,E₂E₁,E₁E₂E₁) span the quotient by induction. Their images in Q × Q × M₂(Q) are independent, using E₁ ↦ (0,1,((1,0),(0,0))) and E₂ ↦ (0,0,((1,1),(1,1))). This proves a quotient basis and provides regular-trace coordinates.

Half diagrams use finite incidence maps with zero-based labels. Gluing pairs equal propagating-label sets. Recursive flattening produces the six quotient words at the witness. Coordinate extraction uses `Fintype.linearCombination` and its inverse when bijective. Bijectivity is proved at the witness, and the source's ket-independent cell action and complete defining form equation are checked there. The cell form is defined as the scalar satisfying that action equation; the proof identifies it with the computed coordinate before evaluating the Gram matrices.

## Falsifier

The refutation requires a basis of the actual presented quotient, exhaustive enumeration of the rank-three diagrams and cells, the source's cell-form equation at the witness, and unequal determinants computed from these objects. The proof establishes these obligations. Merely choosing an unrelated Gram matrix, or replacing regular trace by a normalized trace, would not settle the conjecture.

## Evidence

The sole public theorem has type `result : ¬ claim`. Within its proof, the regular Gram matrix is

```
6 3 4 2 2 2
3 3 2 2 2 2
4 2 8 4 4 2
2 2 4 2 4 2
2 2 4 4 2 2
2 2 2 2 2 2
```

Its determinant is −16. The three cell Gram matrices are (1), (1), and ((2,1),(1,1)); their determinants are all 1 and their dimensions are 1,1,2. Thus the conjectured product is 1. All these computations occur in the settling proof, rather than as additional public numerical theorems. The private content theorem `rank3_basis_exists` supplies the basis used by that proof.

## Triage

Refuted, with `admission_basis: open-problem-resolution` and preregistration #11538. There is no digestion atom or coverage claim.

### What the settlement shows

- **Proved in this module:** the exact identity fails at rank three over Q even though all three cell determinants are 1. Cell nondegeneracy does not make the proposed exact regular-trace formula hold.
- **Proved in this module:** the quotient basis and its explicit product/matrix model allow regular trace and the diagram-cell coefficients to be computed from the same algebra. The discrepancy is not caused by substituting a different algebra or a normalized trace.
- **Open:** a general correction by matrix-block dimension and sign factors. The rank-three discrepancy is compatible with the factor −16 of a two-dimensional matrix block's regular trace form; the universal corrected formula and its dependence on characteristic are not proved here.
- **Open in this module:** lower-rank identities, the source's separate cell-determinant Conjecture 7.8, and an equality up to a parameter-independent scalar. The counterexample refutes none of these restricted or modified statements.
- **Open:** the relationship with the Gram determinant of Okada's other un-normalized trace in Section 9.4.2. Statements there or in the preceding trace discussion that use Conjecture 7.9 as an exact identity cannot use that equality. The basis and cellularity theorems do not acquire a refutation from this result.

## ASSUMED-UNVERIFIED

General flattening correctness, diagram-expansion bijectivity and cell-action laws for arbitrary ranks, fields and parameters are not proved here. Coefficient extraction is zero outside its bijective branch. The action-defined cell form is zero if its scalar equation has no solution; the proof establishes a solution and the coordinate agreement at the rational witness. General scalar existence is not proved here. The literature search is scoped and does not establish exhaustive priority. Model-family distinctness of codex-cli and ChatGPT Pro is ASSUMED-UNVERIFIED. Information-escape registration is paused under CLAUDE.md §3.9.
