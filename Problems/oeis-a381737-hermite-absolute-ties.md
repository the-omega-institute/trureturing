---
slug: oeis-a381737-hermite-absolute-ties
bibkey: sheppard2025a381737
doi: null
url: https://oeis.org/A381737/internal?rev=28
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.result
---

# The complete A381737 Conjecture 1 enumeration

## Problem

OEIS A381737, revision 28, by Mike Sheppard (2025), names the sequence:

> Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice.

Its Formula field states:

> Conjecture 1: a(n) = 2*n*(n + 2) + (n + 1)*(-1)^(n+1).

The offset is 1,1. Let $H_k$ be the physicists Hermite polynomial, with the
original coefficients represented by `HermiteSignedMode.physicistsHermite`
over the rationals. For natural $k$ and $j$, write

$$
M(k,j)\iff j\le k\ \land\ \forall i\le k,\quad
|[x^i]H_k|\le |[x^j]H_k|.
$$

Exactly two maxima means that there exist $u<v$ such that, for every natural
$j$, $M(k,j)$ holds if and only if $j=u$ or $j=v$. The entire row from zero
through $k$ is compared, including zero coefficients of the other parity.
For every positive natural index, define the integer value

$$
a(n)=2n(n+2)+(n+1)(-1)^{n+1}.
$$

The complete assertion is that $a(n)>0$ for every $n\ge1$, that
$a(n)<a(m)$ whenever $1\le n<m$, and that for every natural order $k$,
including zero, exactly two maxima occur if and only if there is exactly one
$n\ge1$ with $(k:\mathbb Z)=a(n)$. The additions and products in the formula
are integer operations; $n+1$ in the exponent is natural. There is no finite
cutoff or asymptotic qualification.

## Motivation

This dossier concerns the whole external Conjecture 1, preregistered at
https://github.com/the-omega-institute/trureturing/issues/25855#issuecomment-6590328488.
The full-row meaning follows the source name and its physicists $H_8$
example. The neighboring absolute-mode result supplies coefficient
maximality, while the tie classification and enumeration identify every
qualifying order. Conjectures 2 and 3 are outside this resolution.

## Gap

The Library note identifies revision 28, the Name and Formula fields and
the one-based offset. Programs and finite examples do not supply the
universal enumeration. The needed relation is an exact tie criterion for
the original coefficient row, followed by an exhaustive solution of that
criterion and uniqueness of the positive index. The source locator does
not certify worldwide current openness or priority, and no such claim is
made here.

## Route

For $2r\le k$, let $w(k,r)$ be the absolute value of the original coefficient
at exponent $k-2r$. The existing absolute-mode results give positivity, the
adjacent coefficient identity, maximality at $\operatorname{mode}(k)$ and
strict decrease beyond that index. The strict threshold before the last
adjacent pair restricts a maximizing index to
$\operatorname{mode}(k)$ or $\operatorname{mode}(k)-1$. A tie occurs exactly
when, for some $r\ge1$ with $2r\le k$,

$$
(k-2r+1)(k-2r+2)=4r.
$$

Conversely this equality forces $r=\operatorname{mode}(k)$ and precisely two
maxima. The coefficient extraction theorem transfers this statement to
every exponent in the full polynomial row; parity zeros cannot maximize a
positive mode weight.

Put $j=k-2r$. The equality forces $j=4t+2$ or $j=4t+3$. These give,
respectively, $k=8t^2+18t+8=a(2t+1)$ and
$k=8t^2+22t+13=a(2t+2)$, and both families supply a valid $r$.
Every positive index is of exactly one of these forms. The adjacent integer
difference $a(n+1)-a(n)$ is $2n+3$ or $6n+9$, hence positive; $a(1)=8$.
Strict increase supplies uniqueness as well as positivity and exhaustion.

## Falsifier

A positive index with a nonpositive value, a pair $1\le n<m$ with
$a(n)\ge a(m)$, or a natural order at which exactly two full-row absolute
maxima disagree with the unique-positive-index condition would falsify the
complete event. A finite list, a different Hermite normalization or a
restriction to nonzero coefficients cannot replace this criterion.

## Evidence

`D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.result` proves the complete
`claim`, whose definitions retain the original row, exactly two distinct
maximizers, every positive index and every natural order. Its owning Scribe
binds one typed `OpenProblemResolutionClaim` of kind `Proved` to this slug.
The mathematical sources and their Reg evidence are reused unchanged.

Every child theorem is conservatively classified `proof_shape: bind-only`:
`max_iff_weight`, `strict_before`, `equal_mode_indices`, `adjacent_equal`,
`tie_is_mode`, `tie_characterization`, `a_odd`, `a_even`, `a_strictMono`,
`a_positive`, `tie_orders` and `result`. The admission basis is
`open-problem-resolution`; `escape_witness: none` and `utility: none`.
This classification grants no new abstract mathematical-content credit.
The helper proofs support the complete external resolution.

## Triage

The source classification is `theorem`. The resolution covers the complete
Conjecture 1 enumeration, including positivity, strict increase, exhaustive
classification and unique positive indexing. Conjectures 2 and 3, other
normalizations and new utility claims remain outside its scope.

## ASSUMED-UNVERIFIED

The interpretation of the source's name, offset and formula as the explicit
quantified statement above is a source-to-formal correspondence; the Lean
kernel checks the formal statement and does not interpret OEIS prose.
The Library locator is citation-only. No exhaustive literature search,
worldwide current-openness, originality or priority certification follows
from this dossier. Finite examples and source programs are not universal
proof evidence.
