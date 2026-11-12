---
bibkey: cheon2018riordanspectral
authors: Gi-Sang Cheon, Ji-Hwan Jung, Sergey Kitaev and Seyed Ahmad Mojallal
year: 2018
title: "Riordan graphs II: Spectral properties"
doi: 10.1016/j.laa.2019.04.011
url: https://arxiv.org/abs/1801.07021v1
claim: "Problem 6.11: Is it true that n+ <= n- for any Riordan graph G_n(g,zg)?"
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation
license: citation-only
triage: anchor
---

# Riordan graphs II: Spectral properties

## Verified locator

DOI: 10.1016/j.laa.2019.04.011

Source: https://arxiv.org/abs/1801.07021v1

The source used here is arXiv v1, submitted 22 January 2018. The PDF at
https://arxiv.org/pdf/1801.07021v1 has SHA-256
`418c2f3e14b50a93221eca6bee181212698db25987d54f9c509503bd6286caa8`.
The journal full text has not been read; its HTTP 403 response does not
establish the contents of that version.

## Source statements

Problem 6.11, printed/PDF page 25: “Is it true that n+ ≤ n− for any
Riordan graph G_n(g,zg)?”

Section 2, page 2, fixes vertex labels [n] = {1,2,...,n}.
Definition 2.2 and equation (2), page 3, specify a symmetric binary
adjacency matrix with zero diagonal and, for i > j ≥ 1,

\[
r_{ij}\equiv[z^{i-2}]g(z)f(z)^{j-1}\pmod 2.
\]

The generating series have integer coefficients. For the Bell type,
f(z)=zg(z), which has zero constant coefficient for every g in Z[[z]].
Properness is defined separately and is not imposed by Problem 6.11.
Section 2.2, page 6, counts strictly positive and strictly negative adjacency
eigenvalues with multiplicity; zero eigenvalues count in neither index.

## Encoding and counterexample

The Lean interface ranges over every positive natural order and every
`PowerSeries Int`. An element i of `Fin n` denotes source label i.val+1.
For a lower entry, the exponent i-2 becomes i.val-1 and j-1 becomes
j.val. Integer remainder modulo positive two selects the unique residue
in {0,1}; casting that integer to Real gives the real adjacency matrix.
The upper triangle is reflected from the lower triangle and the diagonal
is zero. No degree cutoff, properness, parity, io-decomposability or
nonsingularity condition restricts the universal claim.

For n=5 and g=1+z^3, the integer lower-triangle coefficient rows are
(1), (0,1), (0,0,1), (1,0,0,1). The resulting adjacency matrix is

\[
A=\begin{pmatrix}
0&1&0&0&1\\1&0&1&0&0\\0&1&0&1&0\\0&0&1&0&1\\1&0&0&1&0
\end{pmatrix}.
\]

The integer matrix

\[
B=\begin{pmatrix}
1&1&-1&-1&1\\1&-1&0&0&-1\\0&0&1&1&-1\\0&0&1&-1&1\\0&0&0&0&1
\end{pmatrix}
\]

has determinant 4 and satisfies
B^T A B = diag(2,-2,2,-2,2). The existing public congruence-invariance
and diagonal-count theorems therefore give n+=3 and n-=2. This is the
negation of the entire universal question, without requiring a
classification of Bell-type graphs.

## Literature boundary

The bounded source screen is supplied in issue #29551. It found no
answer in the retrieved texts. The journal full text and two citing
full texts remain unverified. This scope does not establish worldwide
priority or exhaustive absence of a published answer.
