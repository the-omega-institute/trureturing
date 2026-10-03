---
slug: thanatipanonda-2014-shifted-binomial-power-linearization
bibkey: thanatipanonda2014zudilin
doi: 10.1080/10236198.2014.917635
url: https://arxiv.org/abs/1403.4962v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BinomialBases/ShiftedBinomialPowerLinearization.result
---

# Thanatipanonda's shifted binomial power linearization

## Problem

T. Thanatipanonda, *Beyond Zudilin's Conjectured q-analog of Schmidt's
problem*, arXiv:1403.4962v1, Section 4, Conjecture 4.1, p. 6:

> For any integers d, k ≥ 0 and r ≥ 1, there exist integers $a^{(r)}_{d,k,j}$ such that $\binom{n+dk}{k}^r = \sum_j a^{(r)}_{d,k,j}\binom{n+dj}{j}$ for all n = 0, 1, 2, .... Moreover $a^{(r)}_{d,k,j}$ can be defined as following: $a^{(1)}_{d,k,k} = 1$, $a^{(1)}_{d,k,j} = 0$ for j ≠ k and $a^{(r+1)}_{d,k,j} = \sum_i S_d(k, j, i)a^{(r)}_{d,k,i}$, where, $S_d(k, j, i)$ are integers, independent of r, for all d, k, j, i.

The formal statement uses natural numbers for every nonnegative source
parameter and casts binomial values to integers before taking powers. It
includes both sentences and proves finite support, at j≤rk for the power
coefficients and at j≤i+k for the structure constants.

## Motivation

`D5/S3/Combinatorics/BinomialBases/ShiftedBinomialPowerLinearization.result`
proves the quantified `claim`. For every d,k it supplies one integer-valued
function T(j,i), chosen before the power index r, with the required initial
row, recursion, support and identity for every natural argument n.

## Gap

Issue #12307 preregisters this Tier 1 named external conjecture, its complete
quantified statement and the integral unitriangular route. Its literature
screen records arXiv v1 as the only source version, Crossref's citation count
of zero, and MathDB problem 327501 with zero solutions. The Semantic Scholar
and OpenAlex zero-citation readings in that issue are search-seat reports.
These bounded negative findings do not establish worldwide priority.

The checked statement is the arXiv text. The journal DOI identifies the
article; retention of Conjecture 4.1 in the unread journal version is
ASSUMED-UNVERIFIED.

## Route

Write $B_j(n)=\binom{n+dj}{j}$. Vandermonde gives

$$B_t(n)=\sum_{v=0}^t\binom{dt}{t-v}\binom nv.$$

Its diagonal coefficient is one. Recursively define integer coefficients
$W_{t,t}=1$ and, for $j\ne t$,

$$W_{t,j}=-\sum_{v<t}\binom{dt}{t-v}W_{v,j}.$$

Strong induction proves $W_{t,j}=0$ for j>t and
$\binom nt=\sum_{j=0}^t W_{t,j}B_j(n)$; this is the private content theorem
`integral_inverse`.

The binomial product identity is used locally:

$$\binom np\binom nq=\sum_{u=0}^p\binom{q+u}p\binom pu\binom n{q+u}.$$

Substitution of the inverse produces integer T(j,i), independent of n and r,
such that $B_k(n)B_i(n)=\sum_{j=0}^{i+k}T(j,i)B_j(n)$ and T(j,i)=0 for j>i+k.
The private content theorem `basis_product` establishes both clauses. Starting
from the Kronecker delta at k, induction on the positive power proves the
source recursion and the support j≤rk. Normalization identities are local
proof steps; the sole public theorem is `result`.

## Falsifier

An integer d,k,r with r≥1 for which no single integer recursion supports the
identity for all natural n would falsify the source statement. The universal
Lean theorem excludes such a witness in its formal domain. A different
interpretation allowing negative d, nonnatural n, or insisting on nonnegative
coefficients is outside the stated conjecture.

## Evidence

The kernel-checked `result : claim` has the standard axiom closure
`propext`, `Classical.choice`, `Quot.sound`. Its direct mathematical import is
`Mathlib.Data.Nat.Choose.Vandermonde`; there are no imported D5 prerequisites.
The supporting definitions are B, the integer coefficient recursion a and
claim; W, S, integral_inverse and basis_product are private.

## Triage

Tier 1; Proved; preregistration #12307. Admission basis:
`open-problem-resolution`. The result and the two private content theorems
have `proof_shape: content`. `utility: none` describes a universal identity
and existence proof; no bounded enumeration, checker, numerical reduction
or certified instance is delivered.

### What the settlement shows

- **Proved in this module:** the unitriangular Vandermonde expansion has an
  integral inverse with finite support (`integral_inverse`, used by `result`).
  Division by a diagonal coefficient is unnecessary because that coefficient
  is one. This mechanism works for every nonnegative d, including d=0, and
  every k, including k=0.
- **Proved in this module:** the constructed T(j,i) are integer structure
  constants for the pointwise product of the B-functions, with support
  j≤i+k (`basis_product`, used by `result`). This product identity is the
  evaluation form of multiplication in the shifted binomial basis of
  integer-valued polynomials. The Lean module proves the function identities;
  an abstract polynomial-ring identification and uniqueness theorem are
  **open** formalization candidates.
- **Proved in this module:** the same T works for every positive power, and
  the integer coefficients vanish beyond rk (`result`). Coefficient
  nonnegativity is not a conclusion or an assumption.
- **Open:** replacing dj by an arbitrary nonnegative shift f(j), with
  f:ℕ→ℕ, retains the candidate unitriangular diagonal
  $\binom{f(j)}0=1$. The inverse and product route suggest the same recursion
  theorem, but this module formalizes only f(j)=dj. Negative integer shifts
  would additionally require an integer-argument binomial definition and its
  Vandermonde bridge; natural-number subtraction is not that extension.
- **Open:** Conjecture 4.2 asks for holonomicity, and absence of a first-order
  closed form outside d=0,1, of S_d. Existence of integer structure constants
  does not establish these claims.
- **Proved scope:** Conjecture 4.1 supplies the all-d extension that Section 4
  formulates after the known d=0,1 cases. The Schmidt and q-analog identities
  of Sections 2–3 have their own proofs; this settlement changes no hypothesis
  or proof of those results. Conjecture 4.2 retains its separate mathematical
  obligations.

## ASSUMED-UNVERIFIED

The journal text has not been read. The worldwide absence of a prior proof
is not established by the bounded literature screen. The search-seat citation
readings and MathDB status are reported in #12307, rather than new kernel
facts. Arbitrary shift families, a polynomial-ring API and Conjecture 4.2
are outside the delivered formal theorem.
