---
bibkey: mathlib2026recordcapacity
authors: Junyan Xu and the mathlib community
year: 2026
title: Wedderburn–Artin structure and trace of idempotent endomorphisms
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean
claim: Finite-dimensional semisimple complex algebras are products of full matrix algebras; the associated record-count bounds follow by applying the trace-rank identity to their faithful actions.
strata_touched:
  - D5/S3/Quantum/Matrix/RecordCapacity
license: Apache-2.0
triage: anchor
---

# Algebraic record capacity

## Verified locator

The exact upstream locator is:
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean

The pinned source was opened through GitHub's raw endpoint successfully.
`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` supplies the
matrix-block decomposition. In the same pinned tree,
`Mathlib/LinearAlgebra/Trace.lean`, also opened through the raw endpoint,
contains `LinearMap.IsProj.trace` and `IsIdempotentElem.trace_eq_zero_iff`.
The first identifies the trace of an idempotent with the dimension of its range;
the second detects a zero idempotent by its trace in characteristic zero.

The capacity argument combines these results with trace additivity and the faithful
block diagonal action. The source supplies structure and trace identities, rather than
the complete record-count statement. The D5 theorem keeps the common action and
equivariance explicit. It also supplies a dimension bound without semisimplicity.
The relation between a separately specified irrep decomposition and these block sizes
is outside the delivered formalization.

## The count is a standard corollary, not a new principle

The record-count inequality `card I ≤ Σ_b m_b` is the standard corollary of the
structure theorem above, by composition length of the regular module. Write

    A = ∏_b M_{m_b}(ℂ),

and let ℓ_A(M) denote the composition length of a finite-length left A-module.
The regular module decomposes into simple column modules, m_b of them for each
block, so ℓ_A(A) = Σ_b m_b. A family of nonzero idempotents summing to one gives
A = ⊕_i A p_i, and each A p_i is nonzero because it contains p_i = 1 · p_i, so its
composition length is at least one. Composition length is additive over finite
direct sums, hence

    |I| ≤ Σ_i ℓ_A(A p_i) = ℓ_A(A) = Σ_b m_b.

The budget spent here is the composition length of the regular module, not the
complex dimension Σ_b m_b², and the two must not be interchanged.

The textbook chain for the two inputs is Artin–Wedderburn together with
Jordan–Hölder. Both appear in Etingof, Golberg, Hensel, Liu, Schwendner,
Vaintrob and Yudovina, *Introduction to representation theory*, arXiv:0901.0827;
that record is bound in this repository as `D5/L/Quantum/etingof2009representation`.

The formalization in this repository proves a version with *fewer* hypotheses
than the classical statement: `matrix_blocks_card_le_sum` assumes only that the
idempotents are nonzero and sum to one, and does not assume pairwise
orthogonality. It reaches the bound through the faithful block diagonal action
and the trace-rank identity rather than through composition length. Dropping a
redundant hypothesis does not make the counting principle new.

## What this note does and does not attest

Attested by this repository's own retrieval: the arXiv record 0901.0827v5 in
primary class math.RT, with the title and the seven authors as given in
`D5/L/Quantum/etingof2009representation`, was fetched and checked.

Not attested here: the interior section and theorem numbering of that book, and
any page numbers in other textbooks. An oracle seat reported specific locations
for the two inputs; the orchestrator's attempt to confirm them from the arXiv
PDF failed, because its text streams use subset font encodings that the
extraction available here does not decode. The claim this note supports is
therefore the mathematical one — that the count is the standard corollary of
Artin–Wedderburn and Jordan–Hölder, with the derivation written out above — and
not a claim about where in any particular printing it is stated.

No priority claim is made, and no earliest appearance is asserted.

## The trace-rank step and the semisimple structure, in textbook form

Two textbook inputs carry the whole module, and they are named here so the
stance of every result in it rests on a chain a reader can follow.

**Trace equals rank for an idempotent.** Sheldon Axler, *Linear Algebra Done
Right*, fourth edition: section 8D gives linearity of the trace, and the
exercises for that section ask for exactly `P² = P ⟹ tr P = dim range P`. The
statement is not restricted to orthogonal projections.

Axler works over the reals or the complexes, while this repository's version is
stated over any field of characteristic zero. The remaining step is short and
is written out rather than attributed: over any field an idempotent `p` is
`diag(I_r, 0)` in a basis adapted to `range p ⊕ ker p`, so its trace is the
image of the natural number `r` in the field, and characteristic zero lets the
resulting equation between natural numbers be pulled back. The chain is

    |I| ≤ Σ_i dim range p_i = Σ_i tr p_i = tr 1 = dim V.

**The semisimple structure.** Etingof, Golberg, Hensel, Liu, Schwendner,
Vaintrob and Yudovina, *Introduction to representation theory*: the left
regular representation `a ↦ L_a` appears in section 1, and the correspondence
between finite-dimensional semisimple algebras and finite direct sums of matrix
algebras in section 2.5. Faithfulness of the left regular representation is
immediate from `L_a(1) = a`.

Every result in this module is one of these two inputs transported along an
interface: to an arbitrary finite-dimensional complex algebra, to the actual
commutant of a group action, to a product of matrix blocks acting faithfully on
the direct sum of their column spaces, or to a supplied algebra equivalence.
The transport is the repository's work; the counting is not new.

The verification boundary of the section above applies here too: the section
and page numbers of these books were reported by an oracle seat and were not
confirmed by this repository's own retrieval. What is confirmed here is the
mathematics, which is written out above.
