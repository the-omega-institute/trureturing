---
slug: oeis-a157100-five-term-recurrence
bibkey: mathar2015a157100
doi: null
url: https://oeis.org/A157100
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.result
---

# Mathar's five-term recurrence for OEIS A157100

## Problem

The FORMULA section of OEIS A157100, revision 14, states:

> G.f.: (1+x)*c(x*(1-x^2)), c(x) the g.f. of A000108;
> Conjecture: (n+1)*a(n) +(-5*n+1)*a(n-1) +2*(2*n-1)*a(n-2) +2*(2*n-7)*a(n-3) +2*(-2*n+7)*a(n-4) = 0. - _R. J. Mathar_, Feb 05 2015

The immutable source is
https://raw.githubusercontent.com/oeis/oeisdata/57bbd254e161585873f56950ff19ba6dc4aeb66c/seq/A157/A157100.seq.
Its locator and source identity are in `Library/Words/mathar2015a157100.md`.

Let $c(X)$ be the ordinary A000108 Catalan series, with its natural
coefficients mapped canonically to $\mathbb Q$, and define

$$A(X)=(1+X)c\bigl(X(1-X^2)\bigr),\qquad a_n=[X^n]A(X).$$

For every natural $n\ge4$, the assertion is

$$
(n+1)a_n+(-5n+1)a_{n-1}+2(2n-1)a_{n-2}
+2(2n-7)a_{n-3}+2(-2n+7)a_{n-4}=0.
$$

The source's OFFSET is `0,2`; the first coefficient has index zero.
The source does not specify an onset. The domain $n\ge4$ is the maximal
well-formed offset-zero interpretation of all five displayed arguments,
not a condition quoted from the source. Scalars are evaluated in
$\mathbb Q$; lagged arguments use natural subtraction, which agrees with
ordinary subtraction throughout this domain.

## Motivation

The conjecture asks whether a sequence specified by an algebraic Catalan
transform obeys this particular linear recurrence with polynomial
coefficients. The existing Catalan differential identity and Euler
coefficient identity in `D5/S1/Recurrence/A308815DFiniteRecurrence.lean`
provide the differential and coefficient interfaces needed for this
different transform.

## Gap

The immutable source explicitly labels the five-term identity a
conjecture. Tier-1 source qualification and the bounded literature and
duplicate screen are recorded in
https://github.com/the-omega-institute/trureturing/issues/29385.
That screen does not establish exhaustive absence of earlier proofs.
The mathematical assertion addressed here is exactly the universal
recurrence for the specified generating function, rather than finite
agreement or the other assertions in the OEIS entry.

## Route

The original Catalan differential identity is

$$X(1-4X)c'(X)+(1-2X)c(X)=1.$$

The existing `cat_ode` supplies this identity. Formal substitution at
$t=X(1-X^2)$ is valid because $t$ has zero constant coefficient.
The chain and product rules, followed by polynomial normalization, give

$$
(1-5X+4X^2+4X^3-4X^4)\,XA'(X)
+(1-4X+6X^2-2X^3-2X^4)\,A(X)=1-3X^2.
$$

This is the private `inhomogeneous` identity. Extract its coefficient of
degree $n$. The existing `euler_coeff` identifies
$[X^d](XA')=d[X^d]A$, and multiplication by each of the four powers of
$X$ shifts the coefficient index. The forcing coefficient is zero for
every $n\ge4$. The resulting five coefficients normalize to the exact
displayed recurrence. The argument uses no recurrence assumption and
does not divide by a coefficient that could vanish at the boundary.

## Falsifier

A natural index $n\ge4$ violating the displayed identity for the exact
coefficient sequence would refute the target. Changing the Catalan
series, its transform, a coefficient or lag, or replacing the universal
domain by an eventual or finite range would be a different assertion.
The omitted source onset remains an explicit interpretation boundary.

## Evidence

The formal source is
`D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.lean`.
Its `result : claim` proves every natural $n\ge4$. The canonical
exposition is the corresponding Blueprint Scribe and emitted Markdown.
The public result and its consumed private `inhomogeneous` helper have
proof shape `bind-only`; the result uses the external open-problem
resolution basis associated with #29385. No escape witness or separate
new general theorem is claimed. The source's definitions `A`, `a` and
`claim` all participate in this proof.

The original `cat_ode` is exposed at its existing definition with the
same mathematical statement and proof; both its original certificate and
the new transform use it. The existing `euler_coeff` is applied directly.
The reported axiom closures are contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The retained source-bound Reg mirror for `result` is unfinished under
https://github.com/the-omega-institute/trureturing/issues/29400.
Its compiled source-equivalence bridge, variation, sensitivity and
observational dependence do not supply a validated lawful readout
binding. The observation is `declared_unresolved`, with
`IE-C050 ClosedTruthReadout`, `forbidden_dependency`,
`source.unsafe_or_external` at `Nat.add`. The exposed original
`cat_ode` registration retains its validated source-equivalence evidence
and open continuation. The new result's registration is not reported as
validated.

## Triage

| Assertion | Evidence and boundary |
| --- | --- |
| Exact five-term recurrence | Proved by `result` for every natural $n\ge4$, including the first well-formed index |
| Decisive mechanism | Proved: the substituted Catalan differential identity gives `inhomogeneous`; coefficient extraction yields the five shifts |
| Finite computations | No finite experiment is used as evidence for the universal recurrence |
| Other polynomial Catalan transforms | Unresolved here: the substitution method suggests candidates, but each needs its own identity and source conditions |
| Hankel transform and Somos-4 assertion in the OEIS NAME | Unresolved in this formalization; the linear recurrence proof supplies no such implication |
| Other coefficient formulas in the OEIS entry | Unresolved in this formalization; they are not additional conclusions of `result` |

The recurrence can therefore be used for this exact coefficient sequence
without assuming the conjectured identity. The proof's structural scope
is the specified Catalan transform and all its well-formed indices.
It establishes neither a theorem about every Catalan transform nor a
Hankel-determinant relation. No source conclusion depending on those
separate assertions is promoted by this result.

## ASSUMED-UNVERIFIED

The source omits the onset; $n\ge4$ is the disclosed offset-zero
interpretation. The bounded literature screen does not certify global
priority or exhaustive absence of historical proofs. The new result's
four-slot audit remains unfinished under #29400. No additional
mathematical hypothesis is assumed in the recurrence proof.
