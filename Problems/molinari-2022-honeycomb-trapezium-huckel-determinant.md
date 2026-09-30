---
slug: molinari-2022-honeycomb-trapezium-huckel-determinant
bibkey: molinari2022graphene
doi: 10.48550/arXiv.2206.14428
url: https://arxiv.org/abs/2206.14428v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.result
---

# Molinari's honeycomb trapezium determinant

## Problem

Molinari's Conjecture 2 in *Graphene nanocones and Pascal matrices* (arXiv:2206.14428v2, section 5, page 9) asks whether the determinant of the Hückel matrix of a honeycomb trapezium with rows of lengths `2k+1, 2k+3, ..., 2n+1` equals the determinant of the displayed reduced Pascal matrix of size `n+1-k`. The weights are arbitrary boundary parameters.

The formal statement is

```
claim := ∀ (R : Type) [CommRing R] (k n : ℕ), k ≤ n → ∀ (x y : ℕ → R),
  (huckel k n x y).det = (reducedPascal k n x y).det
result : claim
```

## Motivation

The paper proves palindromy, degree, and square-coefficient properties and reports only finite hand reductions for the determinant identity. Issue #11470 preregistered this named open problem and its literature check before Lean work. The frozen declaration `D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.result` settles Conjecture 2 as proved.

## Gap

The paper is the latest arXiv version and no citing work or published version was found in the bounded checks recorded in issue #11470. Those checks do not establish exhaustive worldwide novelty or publication priority.

## Route

1. **Proved — decisive mechanism.** The red-to-blue incidence has the kernel lift
   `U_(m,j),l = (-1)^j C(j, m-l)` for `l ≤ m`, with zero entries otherwise. Pascal's recurrence gives `B U = 0`, while the left endpoints give the identity. Reordering the two colours and applying the Schur-complement reduction gives
   `det H_(k,n) = (-1)^q det(Uᵀ X U)`, where `q` is the number of red sites.
2. **Proved — extension.** The identity holds over every commutative ring and for arbitrary row weights; no positivity or genericity is assumed. Setting `k = 0` gives the paper's Conjecture 1 for triangles.
3. **Open — adjacent question.** The paper's Conjecture 3, asserting permanent = determinant, is not claimed or settled by this module.
4. **Proved — consequences.** The paper's proposition `det H_n(x,y) = x^(n+1) det(Q_n + (y/x) I)` and its palindromy and degree facts now have a proved determinant identity as their foundation.

The proof separates blue and red sites, constructs the binomial kernel lift, proves its incidence cancellation and endpoint identities, compresses the boundary block through a Schur complement, and identifies the resulting matrix with reduced Pascal after column signs and reversal. Every step is carried out in an arbitrary commutative ring.

## Falsifier

A commutative ring, `k ≤ n`, and weight functions `x,y` for which the two displayed determinants differ would refute the formal claim. Conjecture 3 is a separate open statement.

## Evidence

The Lean build and freeze use the declaration above. The result is repository-produced; the literature supplies the conjecture. The freeze event records no prerequisite frozen project nodes. The axiom closure is reported with the delivered verification readings.

## Triage

First tier: a named conjecture displayed in Molinari (2022), preregistered in issue #11470. Resolution: `proved`. Utility is `none`; the theorem is a general identity rather than a finite computation.

| Declaration | proof_shape | direct frozen dependencies | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| `result` | bind-only | none | none | open-problem-resolution |

The public surface is the definitions needed by the settlement (`sourceT`, `sourceR`, `sourceTriangle`, `huckel`, `reducedPascal`), together with `claim` and `result`.

## ASSUMED-UNVERIFIED

The bounded literature search does not certify exhaustive worldwide novelty, priority, or absence of an independent proof. The Lean kernel does not authenticate the external paper or its publication history.
