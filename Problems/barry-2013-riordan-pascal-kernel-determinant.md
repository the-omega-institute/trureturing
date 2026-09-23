---
slug: barry-2013-riordan-pascal-kernel-determinant
bibkey: barry2013riordanpascal
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.pdf
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.result
---

# Barry's Riordan-Pascal kernel determinant

## Problem

Barry defines the generalized Pascal matrix on printed page 1:

> In this note, we investigate some properties of the two-parameter generalized
> Pascal triangle M^{(m)}(a, b) given by the Riordan array
> M^{(m)}(a, b) = ( 1/(1 − ax) , x(1 + bx)/(1 − ax)^m ).

The row polynomials are defined on printed page 19:

> We can regard the matrix M^{(m)}(a, b) as the coefficient array of a family of
> polynomials P_n(x; m, a, b). We have
> P_n(x; m, a, b) = Σ_{k=0}^{n} T^{(m)}_{n,k}(a, b) x^k.

The comparison that introduces the kernel appears later on printed page 19:

> It is interesting to compare the matrices defined by the quotient above with
> those defined by Σ_{j=0}^{n} P_j(x; m, a, b)P_j(y; m, a, b). In the case
> of monic orthogonal polynomials, such expressions lead to the same matrices.
> However, M^{(m)}(a, b) is not in general the coefficient array of a family of
> monic orthogonal polynomials, and hence the two family of matrices will in
> general differ. In the case m = 2, a = b = 1, we can conjecture the following.

Conjecture 32 is stated on printed page 20:

> **Conjecture 32.** The matrix D̃_n(2, 1, 1) with generating function
> Σ_{k=0}^{n} P_j(x; 2, 1, 1)P_j(y; 2, 1, 1) is given by
> M_n^{(2)}(a, b)^t M_n^{(2)}(a, b). We then have
> |D̃_n(2, 1, 1)| = 1 for n ≥ 0. In the above the notation M_n denotes the
> matrix formed from the first (n + 1) rows and columns of M.

The page-20 lower summation index is printed as `k=0`, while its summand uses
`P_j`. The unambiguous comparison display on page 19 uses `j=0,...,n`, so the
formal sum uses that index. The right side is read at `(a,b)=(1,1)`, as fixed
by the sentence immediately preceding the conjecture and by its left side.
The generic reading fails already at `n=1`: `Dtilde_1 = [[2,1],[1,1]]`, while
`M_1(a,b)^t M_1(a,b) = [[1+a^2,a],[a,1]]`.

The phrase "with generating function" uses the coefficient-array convention
from the same section: entry `(i,k)` is the coefficient of `x^i y^k`. Section
2 defines a Riordan array entry by `T_{n,k} = [x^n] g f^k`, with columns
indexed from zero. Thus the quantified claim is, for every natural `n`,
`Dtilde_n = M_n^t M_n` and `det Dtilde_n = 1`.

## Motivation

Conjecture 32 asks for both an exact matrix identity and its determinant
consequence for every truncation size. The frozen theorem settles both clauses
uniformly, including `n=0`, rather than checking a bounded collection of
matrices.

## Gap

Issue #9215 preregisters the named first-tier open problem and its bounded
literature check. OpenAlex lists five citing works. Three have arXiv full texts;
each contains zero `Christoffel` hits. The two citing works without arXiv full
text were checked only through available metadata and remain
`ASSUMED-UNVERIFIED`.

OEIS A114188 cites Barry's article but contains no settlement of the determinant
or Gram-matrix assertion. Four MathDB searches, for `Riordan`, `Barry`, `Pascal
matrix determinant`, and `Christoffel-Darboux determinant`, returned no entry.
Semantic Scholar returned HTTP 429 and remains `ASSUMED-UNVERIFIED`.

These checked surfaces do not establish exhaustive worldwide literature
coverage, publication priority, or the absence of an independent proof.

## Route

(A) Coefficient extraction from `Sum_{j=0}^{n} P_j(x)P_j(y)` gives
`Sum_j T_{j,i}T_{j,k}` in entry `(i,k)`, exactly the corresponding entry of
`M_n^t M_n`.

(B) The factor defining column `k` contains `X^k`; therefore entries strictly
above the diagonal vanish, and the remaining factor has constant coefficient
one. Hence `M_n` is lower unitriangular and `det M_n = 1`. Multiplicativity and
transpose invariance then give `det Dtilde_n = 1`.

Under CLAUDE.md section 3.2, `result` is bind-only. The strict-upper-zero and
diagonal-one facts are direct power-series coefficient normalizations, and the
determinant step directly instantiates pinned Mathlib's triangular determinant,
multiplicativity, and transpose lemmas. There is no escape witness. Admission
is `open-problem-resolution`: the settlement of the preregistered named
conjecture is the new content, not the proof steps.

## Falsifier

A natural `n` for which the coefficient matrix differs from `M_n^t M_n`, or
for which its determinant differs from one, would refute the theorem. A generic
`(a,b)` reading, the Christoffel-Darboux quotient matrix of Conjecture 31, or a
different interpretation of the misprinted summation index is a different
claim.

## Evidence

The source and printed-page locators are recorded in
`Library/Recurrence/barry2013riordanpascal.md`. Exact symbolic enumeration for
`n=0,...,8` gives `Dtilde_n = M_n^t M_n` and determinant one in every case.
The first six rows of `M` are `[1]`, `[1,1]`, `[1,4,1]`, `[1,9,7,1]`,
`[1,16,26,10,1]`, and `[1,25,70,52,13,1]`, matching the rows printed on page 2.

The frozen declaration is
`D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant.result`, with
statement ID
`sha256:47340acd13b0514d3a4d25748e921f2f60bbbf1dc42e97c472de5eedf1bf52c8`.
Its freeze event is
`sha256:c10c0b78783c62d4772cd2e78d54a6e83d83dcb83eada6bc668da20af50e0418`.
The axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`;
the freeze event has no prerequisite frozen project nodes.

## Triage

First tier: a conjecture printed in Barry, Journal of Integer Sequences 16
(2013), Article 13.5.4, preregistered in issue #9215. Resolution: `proved`.
Conjecture 31 is not asserted or settled by this module.

| Declaration | proof_shape | direct frozen dependencies | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| `result` | bind-only | none | none | open-problem-resolution |

The public surface is exactly `riordan`, `P`, `M`, `Dtilde`, `claim`, and
`result`. The module proves a symbolic theorem for every `n`; it is not bounded
enumeration, checker infrastructure, numeric reduction, or a certified finite
instance, so `utility: none` applies.

## ASSUMED-UNVERIFIED

The two OpenAlex citing works without arXiv full text are
`ASSUMED-UNVERIFIED` beyond their available metadata. Semantic Scholar is
`ASSUMED-UNVERIFIED` because the request returned HTTP 429. The bounded
literature checks do not establish exhaustive worldwide novelty, priority, or
the absence of an independent proof. The Lean kernel does not authenticate the
external PDF, its pagination, or its publication history.
