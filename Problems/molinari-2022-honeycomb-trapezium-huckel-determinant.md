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

### What the settlement shows

- [proved: D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.result] The decisive structure is the incidence kernel, not inversion of a boundary-weight block: for source rows `m,l = k,...,n`, the lift `U_(m,j),l = (-1)^j C(j,m-l)` (zero for `l > m`) satisfies `B U = 0` by Pascal recurrence and is the identity at the left endpoints. The incidence tail has determinant 1. The proof compresses `H` to `Uᵀ X U` with sign `(-1)^q`, where `q = Σ_(m=k)^n m`; the endpoint values identify the compression with reduced Pascal after column signs and simultaneous row/column reversal. The column-sign determinant is the same `(-1)^q`, giving the stated equality.
- [proved: D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.result] The algebraic range is every commutative ring and arbitrary independent row weights, including zero weights, zero divisors and positive characteristic. Neither positivity, uniform weights, invertible weights nor invertibility of `H` is required. In particular, the proof remains applicable when a source row has `x_m + y_m = 0`; the invertible Schur block comes from the unit incidence tail rather than division by this sum.
- [proved: D5/S3/Combinatorics/Graph/HoneycombTrapeziumHuckelDeterminant.result] Setting `k = 0` settles the paper's Conjecture 1 for every triangle size and boundary-weight choice. Thus the triangle reduction used as the first equality in the paper's subsequent symmetric-Pascal factorization is also available without the paper's finite-size restriction.
- [computed: python3/SymPy script reconstructing source H and M for k=0,n=1,x=y=1 and replacing both entries of the edge (row 1,site 0)↔(row 1,site 1) by 2; det H=5, det modified H=9, det M=5] Arbitrary boundary weights do not license this bulk-edge change while keeping the same reduced Pascal matrix: this four-site example already breaks that extension.
- [computed: python3/SymPy script forming M_(0,n)(x,y) and Q_n=(C(i+j,j))_(i,j=0)^n and expanding det M-det(x Q_n+y I) for n=0,...,5; differences=[0,0,0,0,0,0], total degrees=[1,2,3,4,5,6], palindromic=[true,true,true,true,true,true], coefficients of y^(n+1)=[1,1,1,1,1,1]] The paper's uniform-weight factorization agrees with the reduced matrix in these six symbolic cases, including `x = 0` in its division-free form. In increasing powers of `y`, the coefficient vectors are `(1,1)`, `(1,3,1)`, `(1,9,9,1)`, `(1,29,72,29,1)`, `(1,99,626,626,99,1)` and `(1,351,6084,13869,6084,351,1)`. This is a finite check of the neighbouring degree and palindromy properties, not a universal certification of them.
- [open] Kernel certification of the paper's full factorization `det H_n(x,y) = det(x Q_n + y I)`, its homogeneous palindromic degree `n+1-k`, its square coefficients for independent weights, and its analytic nanocone/graphannulene consequences requires the respective algebraic or spectral bridges. The settlement supplies the conjectural determinant reduction used by the factorization; those other conclusions are not additional results of this module. Their proofs reported in the paper remain literature results, rather than additional open problems settled here.
- [computed: python3/SymPy exact determinant and assignment-mask dynamic-programming permanent of source H with x=y=1 for 0≤k≤n≤3; (k,n,det,per)=[(0,0,2,2),(0,1,5,5),(1,1,2,2),(0,2,20,20),(1,2,8,8),(2,2,2,2),(0,3,132,132),(1,3,52,52),(2,3,13,13),(3,3,2,2)], mismatches=0] Conjecture 3 agrees with the settled determinant in these ten finite specializations, including single-row trapezia. These values supply controls for a separate permanent argument.
- [open] The paper's Conjecture 3, `per H_(k,n)(x,y) = det H_(k,n)(x,y)` for all sizes and arbitrary boundary weights, remains a separate question: determinant-preserving basis changes and the Schur complement do not supply a permanent reduction. A proof must additionally control the signs of contributing permutations or provide a corresponding combinatorial identity; the source paper's loop-covering interpretation therefore has no new universal permanent certificate from this settlement.

## ASSUMED-UNVERIFIED

The bounded literature search does not certify exhaustive worldwide novelty, priority, or absence of an independent proof. The Lean kernel does not authenticate the external paper or its publication history.
