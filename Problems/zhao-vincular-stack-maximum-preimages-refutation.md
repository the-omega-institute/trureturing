---
slug: zhao-vincular-stack-maximum-preimages-refutation
bibkey: zhao2024vincular
doi: 10.1016/j.disc.2025.114834
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultMaximum
---

# Refutation of Zhao's maximum preimage conjecture

## Problem

Zhao, arXiv:2410.17057v1, Conjecture 4.14 (Section 4.1.4, printed page 17), states:

> For n ≥ 2, it holds that max over π in 𝔖ₙ of |SC₁₂̲₃̲⁻¹(π)| equals max over π in 𝔖ₙ of |SC₃₂̲₁̲⁻¹(π)| equals 2ⁿ⁻².

The formal claim uses the paper's one-based permutation entries and the right-greedy stack convention fixed by its four worked figures. The flag `false` denotes 1-underline(23), and `true` denotes 3-underline(21).

## Motivation

The claimed maximum for the 1-underline(23) map at n = 9 is at most 2⁷ = 128. The explicit fibre of 765432819 contains 129 distinct input permutations, so the universal maximum claim is false.

## Gap

The journal version is Discrete Mathematics 349(3) (2026) 114834, DOI 10.1016/j.disc.2025.114834. Its full text was not opened; publisher search-index excerpts reported by a literature seat indicate that it retains Conjectures 4.14 and 5.2. The settled statement is the arXiv v1 statement quoted above.

The source prints no formal definition of the stack rule. The Cerbai–Claesson–Ferrari right-greedy convention, with stack words read top to bottom, is pinned by the paper's four figures.

## Route

The Lean definition `Fibre false 9 [7,6,5,4,3,2,8,1,9]` contains the 129 listed permutations. Each membership and each image under `SC false` is checked by kernel reduction; the finite-set cardinality is 129. Applying the claimed upper bound at n = 9 yields 129 ≤ 128, and arithmetic closes the contradiction.

## Falsifier

A correction showing that one listed input is not a permutation of 1 through 9, does not map to 765432819, or that the finite-set cardinality is below 129 would invalidate this refutation. A source-level correction to the stack convention or to the quoted arXiv statement would also require re-evaluation.

## Evidence

- Lean module GID: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations`.
- Resolution theorem: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultMaximum`.
- Freeze event: `sha256:4c6377b1ebff4ad50f2584bf557c8cba9482535ae158a9d7bf381d646fed4937`.
- Module statement identity: `sha256:6abc010646ae824ed9272bf3813b0f9a2cc7347b23b748977bfb5bfa0983f6f7`.
- Result declaration identity: `sha256:02801b0677319441c9831c5ea2de38e8326487c557bae8a329302e5604373a9a`.
- `proof_shape: bind-only`; `escape_witness: none`; `admission_basis: open-problem-resolution (issue #8634)`.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. The finite counterexample refutes the universal conjecture.

## ASSUMED-UNVERIFIED

The journal-version retention of the conjectures is based on search-index excerpts rather than an opened article. The source-to-code identification of the stack rule follows the four figures because the source gives no formal rule definition. No exhaustive citation-index result is asserted.
