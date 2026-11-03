---
slug: oeis-a381737-hermite-tie-generating-function
bibkey: sheppard2025a381737
doi: null
url: https://oeis.org/A381737/internal?rev=28
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.result
---

# The complete A381737 Conjecture 3 generating function

## Problem

OEIS A381737 revision 28, by Mike Sheppard, names the sequence:

> Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice.

Its Formula field states:

> Conjecture 3: G.f.: (8*x + 5*x^2 + 5*x^3 - x^4 - x^5) / ((1 - x)^3 * (1 + x)^2).

The offset is 1,1. Let $H_k$ denote the physicists Hermite polynomial over
$\mathbb Q$, represented by `HermiteSignedMode.physicistsHermite`. For natural
orders $k$ and exponents $j$, define

$$
M(k,j)\iff j\le k\ \land\ \forall i\le k,\quad
|[x^i]H_k|\le |[x^j]H_k|.
$$

Write $T(k)$ when there exist natural exponents $u<v$ such that, for every
natural $j$, $M(k,j)$ holds if and only if $j=u$ or $j=v$. This is precisely
`HermiteAbsoluteTieOrders.HasExactlyTwo k`: exactly two distinct positions
maximize the absolute coefficient over the full row $0,\ldots,k$, including
parity-zero coefficients.

The entire assertion is that there exists a total $a:\mathbb N\to\mathbb N$
satisfying all of the following:

- $a(n)>0$ for every natural $n\ge1$.
- $a(n)<a(m)$ whenever $1\le n<m$.
- For every natural order $k$, including zero,
  $T(k)\iff\exists! n\in\mathbb N,\ 1\le n\land a(n)=k$.
- There exists $S\in\mathbb Q[[X]]$ with $[X^0]S=0$ and
  $[X^n]S=(a(n):\mathbb Q)$ for every $n\ge1$, such that

$$
P=8X+5X^2+5X^3-X^4-X^5,\qquad
D=(1-X)^3(1+X)^2,\qquad [X^0]D=1,\qquad S=PD^{-1}.
$$

The inverse is the formal power-series unit inverse: the constant
coefficient of $D$ is one. The zero coefficient of $S$ is padding, not an
assertion about $a(0)$. This is a formal series identity at every positive
coefficient, with no analytic convergence assertion, finite prefix,
selected subfamily or recurrence-defined substitute.

## Motivation

The complete external C3 event is preregistered at
https://github.com/the-omega-institute/trureturing/issues/25978#issuecomment-6595713432.
Its clock remains
https://github.com/the-omega-institute/trureturing/issues/25978#issuecomment-6595846899.
The stronger frozen C1 enumeration supplies the actual sequence; its
separate dossier is `oeis-a381737-hermite-absolute-ties`. The C2 recurrence
has the separate fulfilled scope in `oeis-a381737-hermite-tie-recurrence`.
This C3 label grants no automatic independent discovery, priority or KPI.

## Gap

A rational identity for an arbitrary formula or a recurrence alone would
not identify the original sequence. The bridge must preserve the exhaustive
unique indexing of all qualifying natural orders, positivity and strict
increase, transport the integer formula to natural values and rational
coefficients, and prove the entire zero-padded formal series identity.
Finite source computations cannot replace those universal obligations.

## Route

`HermiteAbsoluteTieOrders.result` supplies the full-row predicate,
positivity, strict increase and exhaustive unique positive indexing for

$$
b(n)=2n(n+2)+(n+1)(-1)^{n+1}.
$$

Set $a(n)=\operatorname{toNat}(b(n))$. For every $n\ge1$, positivity gives
$(a(n):\mathbb Z)=b(n)$, hence the rational coefficient cast is exact.
This transfers the C1 enumeration without changing its predicate or its
positive natural indices.

In $\mathbb Q[[X]]$, use the standard binomial series

$$
T_0=\sum_{n\ge0}X^n,\qquad
T_1=\sum_{n\ge0}(n+1)X^n,\qquad
T_2=\sum_{n\ge0}\binom{n+2}{2}X^n,\qquad U=T_1(-X).
$$

The pinned Mathlib identities give $T_0(1-X)=1$,
$T_1(1-X)^2=1$ and $T_2(1-X)^3=1$. Rescaling the second identity by $-1$
gives $U(1+X)^2=1$. Define

$$
F=4T_2-2T_1-2T_0-U+1.
$$

Its constant coefficient is $4-2-2-1+1=0$. For every $n\ge1$,

$$
[X^n]F=4\binom{n+2}{2}-2(n+1)-2-(n+1)(-1)^n
=2n(n+2)+(n+1)(-1)^{n+1}=(a(n):\mathbb Q).
$$

Multiplying by $D$ and using the four displayed binomial identities gives
$FD=P$ by polynomial normalization. Since $[X^0]D=1$, the formal inverse
identity gives $F=PD^{-1}$. Taking $S=F$ proves all clauses together.
The private `quotient`, `coeff_zero` and `coeff_positive` helpers are each
consumed by `result` on this derivation.

## Falsifier

The event fails if the original full-row predicate has no positive,
strictly increasing, exhaustive enumeration with unique positive indexing,
or if the formal series of that enumeration, padded by zero at index zero,
fails the displayed quotient identity at any coefficient. A prefix match,
a different Hermite normalization or a proxy sequence cannot decide this
event. The absence of an analytic convergence claim is part of its scope.

## Evidence

`D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.result` proves the
entire `claim`. Its declaration statement ID is
`sha256:6a1ccf21b4de2af47244595dc5812447e03a12b8c6bd0ebae2956e6a4ce0e742`;
the canonical frozen module statement ID is
`sha256:291ef6a78631a6ca69455b361ab82399c2e4b97e5fc7b97c330a499351b0be74`.
The owning Scribe attaches one typed `OpenProblemResolutionClaim(Proved)`
to this dossier. No matching theory atom was identified in the inspected
theory/digestion scope, and the canonical route is `deposit-uncovered`.

The public `result` and consumed private helpers `quotient`, `coeff_zero`
and `coeff_positive` all have `proof_shape: bind-only`. The admission basis
is the complete named external `open-problem-resolution` under CLAUDE 3.2,
with no new escape witness. All declarations have `utility: none`: the
delivery is an unbounded symbolic assertion, with no bounded enumeration,
checker, numerical-premise reduction or isolated certified instance.
The C1 supplier is directly reused and attributed, with module statement ID
`sha256:9bd5f2909cc80c293978c0263d6749a8c673d97d54bca3431d800d04307ade51`
and result statement ID
`sha256:e509d64d2f77caffa4ca9c71fbc273aaee223094c27e684f9b60985c0bb0944a`.
No stronger supplier is re-proved. The accepted axiom closure is contained
in `Classical.choice`, `Quot.sound` and `propext`, with no `sorry` or new axiom.

The retained mirror is
`Reg/D5/S3/Analytic/Polynomial/HermiteTieGeneratingFunction.lean`.
Its faithful complete source-family law, equivalence, actual-positive,
variation, sensitivity and observational-dependence proofs compile.
The actual audit remains `declared_unresolved`, certificate null,
diagnostic `IE-C050 ClosedTruthReadout`, reason `unclassified_form`,
rule `source.observation_data`. The missing evidence is an accepted exact
source-observation reconstruction and binding certificate for the original
Prop-valued `HasExactlyTwo` occurrence. The CLAUDE 3.9 linked-issue exception is
https://github.com/the-omega-institute/trureturing/issues/26014.
Compiled equivalence is not a binding certificate; `declared_validated`
is not claimed.

## Triage

The source classification is `theorem`. The proved result covers exactly
the complete C3 formal generating-function event. It is a consequence of
the stronger C1 enumeration and standard binomial identities, with no
additional coefficient classification or general mathematical theorem.
C1 and C2 retain their separate fulfilled scopes. This dossier records no
new settlement clock or independent-result credit. Source finite checks
are computed agreement only; the universal formal assertion is proved.

## ASSUMED-UNVERIFIED

The mapping from the source name, offset and conjecture to the explicit
quantified event is a source-to-formal correspondence; Lean verifies the
formal event, not OEIS prose. The revision-28 official OEIS data mirror and
the bounded preregistered repository, pinned Mathlib and selected ecosystem
searches support the source and reuse attribution. They do not certify
worldwide openness, novelty or priority. Rooney's full text, the unidentified
Dudeja-Hsu citation and broad citation tails remain uninspected.

The Reg binding audit remains unfinished under #26014. The historical
C1/C2 audit issue #25957 and local raw/scoped reader boundaries #15595 and
#24733 remain unresolved by selected compilation or CI success. No full
project check or final independent three-seat approval is inferred from
a selected build. No analytic interpretation or new empirical consequence
is asserted.
