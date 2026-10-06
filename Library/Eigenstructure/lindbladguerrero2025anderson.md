---
bibkey: lindbladguerrero2025anderson
authors: O. Lindblad and E. Guerrero
year: 2025
title: Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model
doi: null
url: https://arxiv.org/abs/2512.00278v1
claim: "Conversely, we also ask whether every bad potential shares a nontrivial symmetry with the laplacian."
strata_touched:
  - D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2512.00278v1

The version-one PDF, pages 2, 3, 7 and 8, supplies the definitions,
question and symmetry lemma quoted below.

## The model and badness

Section 1, page 2, writes

\[
(H_t\psi)(j)=\sum_{k\sim j}(\psi(j)-\psi(k))+t\omega_j\psi(j).
\]

Definition 1.1, page 2:

> We say that V is a good potential if H_t = Δ + tV has simple eigenvalues
> and non-vanishing eigenvectors for all but finitely many t values. We say
> that V is a bad potential if H_t fails to satisfy at least one of these
> conditions for any t ∈ ℝ.

Section 1, page 2, describes

> To explain the discrepancy, in section 3 we show shared symmetries —
> orthogonal matrices that commute with both Δ and V — lead to the failure
> of our conditions.

## The converse question

After Theorem 1.3, page 3:

> Conversely, we also ask whether every bad potential shares a nontrivial symmetry with the laplacian.

Section 4, page 8:

> In general, we do not know whether the converse of lemma 3.2 is true.

Lemma 3.2, page 7, assumes an orthogonal O ≠ I commuting with the two real
symmetric matrices. Its first branch assumes O² ≠ I; its second assumes
Oe_j = e_j for some vertex. Each branch excludes O = −I. Accordingly, the
converse question is encoded with O ≠ I and O ≠ −I. Merely allowing −I
would make the conclusion hold for every potential.

On the cycle, Mathlib's cycleGraph and lapMatrix give the displayed sum
of neighbour differences. Simple spectrum is expressed by algebraic
multiplicity one for each complex characteristic-polynomial root;
non-vanishing requires every complex nonzero eigenvector to be nonzero
at every vertex. The normalized values {−1,1} represent any two distinct
potential values: V ↦ αV + βI, α ≠ 0, reparametrizes t by αt and shifts
the eigenvalues by βt while preserving the eigenvectors and shared
commutants.

The eight-cycle potential (1,1,1,1,−1,1,−1,−1) has a persistent nodal
eigenvector branch and scalar shared commutant. These are conclusions of
the accompanying refutation, rather than results attributed to the paper.
