---
slug: koprowski-lewis-2026-conjecture-3-1-hypermatrix-count
bibkey: koprowski2026enumeration
doi: 10.48550/arXiv.2602.22129
url: https://arxiv.org/abs/2602.22129v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs
  - D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount
  - D5/S3/Combinatorics/Hypermatrix/PencilParameterFibers
  - D5/S3/Combinatorics/Hypermatrix/SoutheastFactorization
  - D5/S3/Combinatorics/Hypermatrix/MaskedTensorWeightedReduction
  - D5/S3/Combinatorics/Hypermatrix/MaskedHypermatrixCount
---

# Koprowski–Lewis Conjecture 3.1: the original masked hypermatrix count

## Problem

For every finite field `F` of cardinality `q`, every positive integer `k`, and
nonincreasing nonnegative masks `lambda, mu : Fin k -> Nat` satisfying
`mu j <= lambda j`, `lambda j <= k - j`, and `mu j < k - j`, count the pairs of
actual `(k+1) x k` matrices `(M1, M2)` that respect the two zero regions and
are nondegenerate. The source's nondegeneracy condition is the nonvanishing of
Cayley's second hyperdeterminant; equivalently, every nonzero linear
combination of the two faces has rank `k` over the algebraic closure.

The resolved formula is

```text
q^(k*k) * (q-1)^(2*k)
  * product (q-bracket (k+1-j-lambda j))
  * product (q-bracket (k-j-mu j)),
```

where the products range over `j : Fin k` and
`[r]_q = sum_{e=0}^{r-1} q^e`. The count is over the literal matrix-pair
subtype, with no count, bijection, inverse, normalization, or rational-combination
premise added.

## Motivation

Koprowski and Lewis state this as Conjecture 3.1 in *Enumeration of
Nondegenerate 2 x (k+1) x k Hypermatrices*, arXiv:2602.22129v1. Issue #12542
preregistered the exact assertion and its positive-`k`, characteristic-two
boundary. The repository's library note records the source's orbit, Bruhat,
triangular-invariance, algebraic-closure rank, and augmented-cell bridges.

## Gap

The source leaves the arbitrary two-mask weighted factorization as a
conjectural task. The bounded repository, pinned Mathlib, admissible third-party
Lean ecosystem, and the cited source search supplied no exact dominating
settlement. This is a bounded search statement and does not assert worldwide
absence or priority.

## Route

`MaskedFacesDefs` defines the literal faces, mask predicate, coefficient matrix
and integral coefficient polynomial. `LiteralMaskedCellCount` eliminates the
coefficient-one variables and counts the literal cell solutions. `PencilParameterFibers`
proves the algebraic-closure rank normalization and scalar-fiber classification.
`SoutheastFactorization` gives the constructive upper-pivot factorization and
uniqueness. `MaskedTensorWeightedReduction` builds the actual parameter
bijection and weighted scalar cancellation. `MaskedHypermatrixCount.result`
combines these with the finite-field count and the original prefactor.

The coefficient polynomial is the exact ordinary-monomial determinant
specification used by the source. The identification with the geometric
hyperdeterminant is cited literature evidence; it is not asserted as a new
Lean identity.

## Falsifier

A finite field, positive `k`, and admissible pair of masks for which the literal
matrix-pair subtype has a different cardinality would refute the result. A
purported counterexample must use the algebraic-closure rank condition, the
source zero regions, and the displayed q-bracket factors; testing only
rational combinations or changing the determinant defines a different claim.

## Evidence

The canonical Lean report is bound to source report SHA-256
`98056832a4299f7c57cf8c05b6dc275dd7428e3bf80cb9ea3c9e02e2c2349ccb`. It records
`D5.S3.Combinatorics.Hypermatrix.MaskedHypermatrixCount.result` with statement
ID `sha256:65685a267aa57019de4ca8ea460d33f767a76962c3219c4d02a45a2ddf7c2c28`
and axiom closure `Classical.choice`, `Quot.sound`, and `propext`; no `sorry`
or private axiom is part of the result. The six canonical frozen members are
the state pins under `Golden/Frozen/state/D5/S3/Combinatorics/Hypermatrix/`.

## Triage

Tier 1 external named open problem; `admission_basis: open-problem-resolution`
through preregistration #12542. The computational use is `none`.

| Declaration | proof_shape | admission_basis |
| --- | --- | --- |
| Definitions in `MaskedFacesDefs` | N/A | N/A |
| `literal_cell_count_original_masks` | content | escape-witness |
| `pencil_parameter_fibers` | content | escape-witness |
| `southeast_factorization` | content | escape-witness |
| `masked_tensor_weighted_reduction` | content | escape-witness |
| `MaskedHypermatrixCount.result` | content | open-problem-resolution |

The support results contain live constructive elimination, rank, factorization,
and parameter-cancellation steps. The public result is the complete universal
enumeration, including `k=1` and characteristic two; special boards are not
used as a substitute for the original quantifiers.

**Proved mechanism.** The weighted eligible-permutation sum admits a
first-column deletion and reconstruction with two finite digit coordinates.
For first-column bounds `L+1` and `B`, its weight splits into the tail weight
and the two digit weights. Summing the digits contributes
`[L+1]_q [B]_q`; induction gives the displayed product for arbitrary
admissible masks. Coefficient-one elimination counts the literal field
solutions, while the scalar fiber of size `q-1` cancels one triangular-group
factor. Together these give the original prefactor and the count of actual
matrix pairs, rather than only the permutation sum. The coefficient
determinant/rank bridge is proved internally, including `k=1` and
characteristic two; its geometric hyperdeterminant identification retains
the literature boundary stated in Route.

**Proved consequence and source boundary.** This factors the general weighted
sum left unresolved in the source's Section 5.1 and, through its Corollary
4.19 count bridge, supplies the arbitrary-two-mask formula of Conjecture 3.1.
The source's proved special families and unweighted hyperrook count remain
published results; this settlement does not replace their proofs or settle
other questions in the paper. No independently verified dependency of a
further source conjecture is asserted here.

**Unresolved extensions.** Dropping antitonicity or either mask bound,
replacing finite fields by rings, and counting degenerate tensors require
separate statements and proofs. The current count is an equality, so no
separate estimate-sharpness claim is needed. The digit recurrence is a
candidate method for other weighted board counts, but no such extension is
claimed. Any new candidate requires its own source search, admission and
formalization; it is not covered by this problem's resolution claim.

## ASSUMED-UNVERIFIED

The literature and priority assessment is limited to the cited source, its
linked version, the repository library note, and the bounded searches recorded
above. The geometric hyperdeterminant correspondence is not a kernel theorem
of this module. No claim is made about later unpublished work or an exhaustive
global search.
