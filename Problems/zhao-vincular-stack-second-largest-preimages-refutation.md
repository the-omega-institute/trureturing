---
slug: zhao-vincular-stack-second-largest-preimages-refutation
bibkey: zhao2024vincular
doi: 10.1016/j.disc.2025.114834
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultSecondLargest
---

# Refutation of Zhao's second-largest preimage conjecture

## Problem

Zhao, arXiv:2410.17057v1, Conjecture 5.2 (Section 5, printed page 20), states:

> The second-largest number of preimages under SC₁₂̲₃̲ that a permutation in 𝔖ₙ can have is 2ⁿ⁻³, for n ≥ 3. Furthermore, the number of permutations π in 𝔖ₙ satisfying |SC₁₂̲₃̲⁻¹(π)| = 2ⁿ⁻³ is 2n − 2.

The formal claim retains both clauses under the same universal quantifier. The flag `false` denotes 1-underline(23), with one-based permutation entries and the right-greedy convention fixed by the paper's figures.

## Motivation

At n = 5 the asserted second-largest value is 2² = 4. The computed fibres at outputs 32415 and 43215 have sizes 5 and 8, two distinct values above 4. Therefore the uniqueness condition in the first clause fails, which refutes the conjunction without making a separate claim about the multiplicity clause.

## Gap

The journal version is Discrete Mathematics 349(3) (2026) 114834, DOI 10.1016/j.disc.2025.114834. Its full text was not opened; publisher search-index excerpts reported by a literature seat indicate that it retains Conjectures 4.14 and 5.2. The settled statement is the arXiv v1 statement quoted above.

The source prints no formal definition of the stack rule. The Cerbai–Claesson–Ferrari right-greedy convention, with stack words read top to bottom, is pinned by the paper's four figures.

## Route

Kernel-decided enumeration of the 120 input permutations at n = 5 gives `F false 5 [3,2,4,1,5] = 5` and `F false 5 [4,3,2,1,5] = 8`. Under the conjecture's first clause, every fibre value strictly above 4 must equal one common larger value. Applying that condition to both outputs forces 5 = 8, and arithmetic closes the contradiction.

## Falsifier

A correction to either finite fibre computation, to permutation membership, or to the source statement's quantifiers would invalidate this refutation. The multiplicity clause is not separately settled by this result.

## Evidence

- Lean module GID: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations`.
- Resolution theorem: `D5/S1/Words/Patterns/ZhaoVincularPreimageRefutations.resultSecondLargest`.
- Freeze event: `sha256:4c6377b1ebff4ad50f2584bf557c8cba9482535ae158a9d7bf381d646fed4937`.
- Module statement identity: `sha256:6abc010646ae824ed9272bf3813b0f9a2cc7347b23b748977bfb5bfa0983f6f7`.
- Result declaration identity: `sha256:f2b6bb79cf00e17111995627f44f17f2973be6f571faf8d954ea70be4b936eea`.
- `proof_shape: bind-only`; `escape_witness: none`; `admission_basis: open-problem-resolution (issue #8634)`.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. Two distinct finite fibre values above the claimed second-largest value refute the first clause and hence the conjunction.

## ASSUMED-UNVERIFIED

The journal-version retention of the conjectures is based on search-index excerpts rather than an opened article. The source-to-code identification of the stack rule follows the four figures because the source gives no formal rule definition. No exhaustive citation-index result is asserted.
