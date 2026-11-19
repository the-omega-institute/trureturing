---
slug: cheon-riordan-bell-inertia-611
bibkey: cheon2018riordanspectral
doi: 10.1016/j.laa.2019.04.011
url: https://arxiv.org/abs/1801.07021v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.result
---

# The positive and negative inertia of Bell-type Riordan graphs

## Problem

Gi-Sang Cheon, Ji-Hwan Jung, Sergey Kitaev and Seyed Ahmad Mojallal,
*Riordan graphs II: Spectral properties*, arXiv:1801.07021v1,
Problem 6.11, printed/PDF page 25, asks:

> Is it true that $n^+\le n^-$ for any Riordan graph $G_n(g,zg)$?

### Complete statement

For every natural $n\ge1$ and every integer formal power series
$g\in\mathbb Z[[z]]$, put $f=zg$. On source labels $1,\ldots,n$, let
$A_{ii}=0$ and, for $1\le j<i\le n$, let $A_{ij}=A_{ji}$ be the unique
member of $\{0,1\}$ congruent to $[z^{i-2}]g(z)f(z)^{j-1}$ modulo two.
The question asserts $n^+(A)\le n^-(A)$, counting strictly positive and
strictly negative real eigenvalues with algebraic multiplicity. Zero
belongs to neither count. Properness, evenness, io-decomposability,
nonsingularity, degree bounds and finite-order cutoffs are not hypotheses.

The definition `RiordanBellInertiaRefutation.claim` is this entire
universal proposition; `RiordanBellInertiaRefutation.result` proves its
literal negation. A `Fin n` index $i$ represents source label $i+1$,
so the lower coefficient indices become $i-1$ and $j$ in the Lean rule.
Definition 2.2 and equation (2), page 3, fix the adjacency convention;
Section 2.4, page 6, fixes the inertia convention.

## Motivation

The existing frozen theorems
`D5/S3/Weil/Pick/InvertibleHermitianInertiaPullback.inertia_invariant_of_isUnit_det`
and `D5/S3/QuadraticForms/StructuredRankOneInertia.diagonal_counts`
transport inertia through an invertible congruence and count the strict
signs of a diagonal. The source coefficient rule connects their matrix
input to a Bell-type Riordan graph.

## Gap

The question was preregistered in
[issue #29551](https://github.com/the-omega-institute/trureturing/issues/29551),
with the complete event and predictions in its
[immutable registration](https://github.com/the-omega-institute/trureturing/issues/29551#issuecomment-6821785527).
The supplied bounded literature screen covered seven arXiv family records,
six other family full texts, arXiv:2009.02770 and eight distinct citing
works, six with screened full texts. No answer was located in those
retrieved texts. Tier 1 eligibility is provisional within that scope;
no exhaustive modern-open or priority claim follows.

## Route

Take $n=5$ and $g=1+z^3$. The source coefficient rule gives lower rows
$(1)$, $(0,1)$, $(0,0,1)$, $(1,0,0,1)$ and hence

$$
A=\begin{pmatrix}
0&1&0&0&1\\1&0&1&0&0\\0&1&0&1&0\\0&0&1&0&1\\1&0&0&1&0
\end{pmatrix}.
$$

The certificate is

$$
B=\begin{pmatrix}
1&1&-1&-1&1\\1&-1&0&0&-1\\0&0&1&1&-1\\0&0&1&-1&1\\0&0&0&0&1
\end{pmatrix},\qquad
\det B=4,\qquad B^TAB=\operatorname{diag}(2,-2,2,-2,2).
$$

Congruence invariance and diagonal sign counts give $n^+(A)=3$ and
$n^-(A)=2$. Applying the universal claim to this actual series would
give $3\le2$.

## Falsifier

A source mismatch in the coefficient indexing, parity reduction,
quantifiers or multiplicity convention would invalidate the proposed
identification with Problem 6.11. A conditional inertia assumption or a
matrix supplied without the coefficient equality would not refute the
source question. The delivered proof establishes that equality and both
strict sign counts before contradicting the universal claim.

## Evidence

The kernel-checked endpoint is
`D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.result`.
Its consumed private helpers `adjacency_witness`, `B_det`, `congruence`
and `witness_inertia` establish the coefficient matrix, determinant,
congruence and exact inertia. The Hermitian eigenvalue API identifies the
indexed spectrum with the characteristic-root multiset, retaining
algebraic multiplicities. The mathematical proof uses only the existing
inertia theorems and coefficient normalization; no escape witness is
claimed. The source is the hash-bound arXiv v1 PDF identified in
`Library/QuadraticForms/cheon2018riordanspectral.md`.

## Triage

The original universal question is refuted by the designated result.
The admission basis is `open-problem-resolution` for this external named
question; the result and its consumed theorem helpers are `bind-only`.

### What the settlement shows

- Proved in Lean by `RiordanBellInertiaRefutation.result`, using its
  internal exact certificate: the order-five Bell-type adjacency above
  has positive inertia three and negative inertia two. It has the
  five-cycle edge pattern; Bell type alone does not ensure the proposed
  sign inequality.
- Proved in the cited source, not newly formalized here: the paragraph
  immediately preceding Problem 6.11 on page 25 states that an even
  generating function gives a bipartite graph by Lemma 2.6, and hence
  equal positive and negative inertia. That restricted statement is a
  surviving source result. The witness $1+z^3$ is not even.
- Open: a characterization of the Bell-type graphs satisfying the
  inequality, or another useful sufficient hypothesis beyond the cited
  even-series case. Neither a family classification nor a modified
  conjecture is asserted by this one counterexample.
- Source scope: Theorems 6.7 and 6.12 and Corollary 6.9 on page 25 have
  their own decomposability or derivative-type hypotheses; this result
  concerns Problem 6.11. Their proofs and the paper's other questions
  have not been reverified here. No source theorem is withdrawn on the
  basis of this refutation.

## ASSUMED-UNVERIFIED

The version-of-record full text returned HTTP 403 in the supplied screen;
two citing full texts remain unverified. The DOI identifies the journal
publication, while the statement and definitions used here are explicitly
those of arXiv:1801.07021v1. The bounded screen does not establish worldwide
priority, exhaustive absence of a prior answer or final eligibility.
Final independent review and required CI are separate delivery obligations.
