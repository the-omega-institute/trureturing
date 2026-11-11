---
slug: oeis-a188475-original-shifted-hankel
bibkey: barry2011a188475
doi: null
url: https://oeis.org/A188475/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CatalanPowerHankel/BarryA188475
---

# Barry's original all-index shifted Hankel determinant

## Problem

Paul Barry, OEIS A188475, revision 2:

> Hankel transform of A137398(n+1) (conjecture).

For the current one-based recurrence-defined q, q(1)=0, q(2)=1, q(3)=2,
and, for every r>=4,

$$q(r)=2q(r-1)+2q(r-2)+\sum_{k=1}^{r-3} C_k q(r-k-1).$$

The complete original assertion, for every natural n including zero, is

$$\det[q(i+j+2)]_{0\le i,j\le n}
=1+2\sum_{k=0}^n k^2
=\frac{2n^3+3n^2+n+3}{3}.$$

The conjecture used the old zero-based A137398. Its later offset correction
makes the original shift q(i+j+2). The literal recurrence determines q;
corrected tabulation errors are not an alternate definition. The Lean
auxiliary q(0)=0 is outside the matrix's source indices.

## Motivation

This is a first-tier externally named all-index conjecture. The question is
about the Hankel transform of the source recurrence, including n=0, with
no extra positivity, moment representation or nonsingularity assumption.
The preregistered target is issue 29029.

## Gap

The current entry still calls the assertion a conjecture. The bounded
prior-art screen in issue 29029 found no exact supplier in the inspected
papers, repository, pinned Mathlib or third-party Lean search.
The paper exclusions are Goy–Shattuck (2023), Theorem 3, p. 425 and the
recurrence argument p. 431 (https://doi.org/10.15330/cmp.15.2.420-436);
Chang–Hu–Zhang (2013), Linear Algebra and its Applications 438:2523–2541,
Theorem 3.5; and Liu–Wang–Zhang, arXiv:2607.18644v2, Theorems 1.5–1.8
(https://arxiv.org/html/2607.18644v2). These are bounded exclusions of exact
suppliers, not assertions that the methods are unrelated. A331474's
signed Gram adjugate proof is source specific. The Cigler Motzkin family
fixes the first descent weight at one, whereas this source requires two.
Neither supplies this result by direct specialization.

## Route

Let C be the formal Catalan series, T=C², F=sum(q(r)X^r) and M=1+2F.
The literal recurrence gives
F(1-2X-2X²-X²T)=X². The Catalan equation gives
T(1-2X-X²T)=1, and these imply M(1-2X²T)=1.

The monic polynomials are P(0)=1, P(1)=X and
P(j+2)=(X-2)P(j+1)-beta(j)P(j), with beta(0)=2 and beta(j+1)=1.
Reversed-polynomial errors vanish strictly below degree 2j and have
coefficient two at degree 2j for every j>=1. This proves exact
orthogonality for the moment functional of M, with norms 1,2,2,... .

The monic coefficient matrix A has determinant one. For the finite moment
Gram matrix G, AᵀGA=diag(1,2,...,2). Mathlib's adjugate product identity
then gives adj(G)=A adj(diag(1,2,...,2)) Aᵀ. The (0,0) entry is evaluated
using P(j+1)(0)=2(-1)^j j and its square 4j². The same entry is the
determinant of G with row and column zero removed. That minor is twice
the exact shifted source matrix entry by entry. Cancelling the nonzero
power of two yields the sum of squares. Induction evaluates that sum to
the displayed cubic over the rationals.

## Falsifier

A natural n for which the recurrence-defined shifted determinant differs
from the cubic refutes the original assertion. Matching finitely many
values cannot prove the quantified result. Replacing q by an assumed
moment sequence would not discharge the source correspondence.

## Evidence

The canonical mathematical source is
D5/S3/Combinatorics/CatalanPowerHankel/BarryA188475.lean, namespace
BarryA188475. Its public definitions q and hankel preserve the recurrence
and the exact shift. The intended public theorem result has the two
required equalities as a conjunction, quantifies over all natural n and
has no hypotheses. A cache-guarded scoped Lean build verifies the complete
theorem with axiom closure propext, Classical.choice and Quot.sound. Admission,
independent review and publication remain separate obligations.

## Triage

The all-index theorem is the sole resolution target. The auxiliary finite
Gram, cofactor and orthogonality claims are consumed on its proof path.
No theory volume or digestion atom corresponds to this target. The source-bound determinant registration has a compiled equivalence bridge,
whole-family variation, single-role sensitivity and actual observational
dependence on its rational matrix state. Its continuation is unknown; that
records a residual and does not assert undecidability. Independent prefreeze
review, canonical freezing and publication remain separate from implementation.

Source evidence: the original OEIS assertion, cubic name, source recurrence
and offset-change locators are retained in the associated library note.
No dependent theorem or later question relying on this conjecture was
identified in the inspected source entry.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish global novelty or
first-publication priority. The external conjecture's exact historical
index translation is supported by its original assertion and the source's
offset correction, not by matching a finite prefix.
