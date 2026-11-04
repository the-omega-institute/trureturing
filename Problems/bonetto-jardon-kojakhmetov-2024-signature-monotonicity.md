---
slug: bonetto-jardon-kojakhmetov-2024-signature-monotonicity
bibkey: bonetto2024mixed
doi: null
url: https://arxiv.org/html/2408.00487v1
triage: theorem
motivation_gids:
  - D5/S3/SpectralTopology/FiniteSpectralLocalizer.posIndex_neg_eq_negIndex
---

# Bonetto–Jardón Kojakhmetov Conjecture 1

## Problem

Bonetto and Jardón Kojakhmetov, *On the Eigenvalues of Graphs with Mixed
Algebraic Structure*, arXiv:2408.00487v1, Section 3, Conjecture 1 states:

> The signature of the matrix M(ε) is a monotonic decreasing function of ε.

For every universe-polymorphic finite vertex type V with Fintype and
DecidableEq instances, let F,G,H be simple undirected loopless graphs on
V with disjoint G,H and G union H = F. Set M(u)=L_G+u A_H over the reals,
using the ordinary combinatorial Laplacian and 0/1 adjacency matrix.
For every real 0<s≤t, the entire assertion is

    signature(M(t)) ≤ signature(M(s)).

Signature is the integer number of positive roots minus negative roots
of the actual characteristic polynomial, counted with algebraic
multiplicity; zero roots contribute zero. For these symmetric matrices,
the full root multiset equals the indexed spectral eigenvalue multiset.
Decreasing means nonincreasing, allowing equality and constant intervals.
Singular matrices, persistent kernels, disconnected graphs, empty edge
classes, the empty vertex type, s=t and the whole positive parameter
axis remain included. Transition counts, limiting signatures, strict
decrease and substitution of zero for a positive parameter are separate
assertions and are not claimed.

## Motivation

The existing positive-subspace characterization of spectral inertia and
the frozen negation identity for positive and negative indices provide
an exact route that retains kernels and multiplicities. The source uses
signature to compare stable and unstable directions in linear systems
with diffusive and saddle interactions.

## Gap

The source states the full signature assertion as Conjecture 1 and its
Outlook asks for a proof or further understanding. Its perturbative
results and numerical plots do not prove this assertion on the entire
positive axis. The bounded source and registration searches found no
other exact registration or posted complete settlement in their scope;
they do not certify worldwide absence, priority or a new method.

## Route

The sole public theorem
`D5/S3/Combinatorics/SpectralGraph/BonettoSignature.result` proves the
complete quantified assertion above. The partition is retained for the
original graph interpretation, although the proof uses only symmetry
and positive semidefiniteness of L_G. For 0<s≤t,

    M(s) = (s/t) M(t) + (1-s/t) L_G,
    -M(t) = (t/s) (-M(s)) + (t/s-1) L_G.

The first coefficient in each identity is strictly positive and the
second is nonnegative. Thus positive subspaces of M(t) remain positive
for M(s), while positive subspaces of -M(s) remain positive for -M(t).
The maximal-dimension characterization gives Nplus(M(t))≤Nplus(M(s))
and Nminus(M(s))≤Nminus(M(t)); subtracting in the integers gives the
signature inequality. No inverse, eigenvalue-continuity argument,
generic crossing, simple-spectrum assumption or kernel removal is used.

## Falsifier

A different original matrix or signature convention, an omitted original
case, an added hypothesis, failure of the algebraic-multiplicity bridge,
or failure of either positive-subspace transfer would invalidate this
resolution. An exact pre-existing settlement or another person's exact
registration excludes the open-problem admission claim. A counterexample
to a neighboring transition or limiting-signature assertion would not
refute the stated monotonicity theorem.

## Evidence

The source note binds Definitions 1–3 and Remark 1, Definitions 7–8 and
Remark 2, all of Section 3 including the conjecture and its transition
discussion, Section 4 Outlook, and the version record. The primary HTML
and record match the source hashes recorded in that note and the
preregistration evidence. The native Lean result uses actual SimpleGraph
matrices and strict-sign characteristic-root counts. Targeted Lean and
scoped inspector evidence cover the whole result, standard axiom closure,
empty dimension, singular repeated roots and equality. The corresponding
Scribe resolution binds this exact theorem, with no companion theorem
or replacement closed claim. Preregistration:
https://github.com/the-omega-institute/trureturing/issues/23242.

## Triage

`theorem`; Tier 1, a named external conjecture in an August 2024 paper
with a complete short route from existing inertia results.
Admission basis is `open-problem-resolution`, not a new spectral method.
The result is conservatively `proof_shape: bind-only`. The definitions
IsEdgePartition, mixedMatrix and signature are source-object bindings
consumed by result. The private helpers mixedMatrix_isHermitian,
signature_eq_indices and posIndex_le_of_form are bind-only and all
consumed on the live result proof path. There are no unused wrappers,
additional public theorems or new dependencies. Utility is `none`:
this is a symbolic theorem over arbitrary finite types and all positive
parameters, not a bounded enumeration or numerical certificate.

## ASSUMED-UNVERIFIED

The four-slot source-bound audit is unfinished:
https://github.com/the-omega-institute/trureturing/issues/23257.
The scoped registration inventory is empty and no Reg mirror is delivered.
Missing evidence comprises complete-telescope reconstruction and
sourceSelection binding of both composite matrix operands; a lawful
enrolled realization with the exact equivalence and actual-positive
bridge; whole-family variation and sensitivity with other observations
fixed; and actual observational dependence with current binding evidence.
No declared_validated, designated-refutation exemption or interface
incapability is claimed. The linked issue discloses this gap under
CLAUDE.md §3.9 and supplies no audit proof. Mathematical freeze and the
typed Proved resolution do not certify completion of this audit.

Worldwide prior-proof absence remains unverified beyond the bounded
searches described in the source note and preregistration. Standalone
scribe-content-checks exited 2 because its raw-v3-only reader rejects
the scoped-v1 report before evaluating the candidate; issue 20682 records
that contract boundary. This is not a passed-check claim. Full supported
required CI on the final head and final independent CLI architecture,
quality and tests reviews remain pending. Merge, the first dev push and
solve credit remain caller-owned lifecycle steps.
