---
slug: calderon-2026-quadratic-order-reciprocal-moments
bibkey: calderon2026rectangular
doi: 10.48550/arXiv.2608.00347
url: https://arxiv.org/abs/2608.00347v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.result
---

# Calderon's reciprocal moments in imaginary quadratic orders

## Problem

Kevin Calderon, *Ljunggren–Jacobsthal and Bailey-Type Congruences for Rectangular
Gaussian Binomial Coefficients*, arXiv:2608.00347v1, Conjecture 6.3, PDF page 19:

> Let $\omega$ satisfy (6.1), and let $p$ satisfy (6.3). Then, for every $k\geq1$,
> $H_{1,\omega}(k)\in p^{2k}\mathcal O_{\omega,p}$,
> $H_{2,\omega}(k)\in p^k\mathcal O_{\omega,p}$.

Equation (6.1) is $\omega^2-T\omega+N=0$, with $T,N\in\mathbb Z$ and
$\Delta=T^2-4N<0$. Equation (6.3) requires a rational prime $p>5$,
$p\nmid\Delta$, and $(\Delta/p)=-1$. The local order is
$\mathcal O_{\omega,p}:=\mathbb Z_p[\omega]$. Its positive representatives are

$$
U_{\omega,k}:=\{x+y\omega:1\leq x,y\leq p^k,\ p\nmid(x,y)\},
\qquad H_{r,\omega}(k):=\sum_{z\in U_{\omega,k}}z^{-r}.
$$

The coordinate condition excludes simultaneous divisibility by $p$; both
intervals include $p^k$. The Lean ring `R` is the adjoin-root of $X^2-TX+N$
over `PadicInt p`, and `U` is the finite image of exactly this filtered
positive rectangle. All its elements are units in the admissible setting.
Consequently `Ring.inverse` in `H1` and `H2` is the underlying inverse unit
value, without adding an assumption or a term to the source's sums.

The fully quantified statement is: for every natural prime $p$, every pair
of integers $T,N$ satisfying all four admissibility clauses, and every
natural $k\geq1$, both displayed memberships hold. The public `claim`
encodes this statement; `result : claim` has no additional hypotheses.

## Motivation

Issue #13205 preregisters this external, first-tier named conjecture. It asks
whether the extra power of $p$ in the first moment is uniform in the
quadratic order and its chosen basis. The conclusion supplies the local
reciprocal-moment premise used in the source's proposed extension of
Gaussian rectangular congruences.

## Gap

The cited v1 states the assertion as Conjecture 6.3. The preregistration
records no proof in its searched Semantic Scholar, OpenAlex, MathDB and
formal-conjectures surfaces; those external search readings are producer
reported. They do not exclude every unpublished or unindexed proof.
The full target is not a named theorem in the searched pinned Mathlib
Padics, QuadraticAlgebra, finite-field and finite-sum scope. Existing
universal lifts, unit norms, residue maps and sum permutations are reused.
The settlement asserts the stated theorem, without claiming exhaustive
historical priority.

## Route

Write $q=p^k$. Positive coordinates identify the finite grid bijectively
with the units of the quadratic ring modulo $q$. Multiplication by $2$
permutes those units. The resulting relation $4H_2=H_2$ modulo $q$, and
cancellation of the unit $3$, give $H_2\in qR$. The same calculation puts
the scalar inverse-square sum $S$ in $q\mathbb Z_p$.

Reflect each coordinate $a<q$ to $q-a$, keeping $a=q$ fixed. The exact affine
identity is $\tau(z)=-z+qc_z$, where
$c_z=1+\omega+1_{x=q}+\omega1_{y=q}$. The inverse identity modulo $q^2$
gives $2H_1\equiv-qA$, with $A=(1+\omega)H_2+E_x+\omega E_y$.
The two boundary-strip sums satisfy $E_x\equiv\omega^{-2}S$ and
$E_y\equiv S$ modulo $q$. Thus $A\in qR$; cancellation of the unit $2$
gives $H_1\in q^2R$. Principal divisibility is exactly membership in the
singleton-generated ideals appearing in the public statement.

`proof_shape: result: bind-only`

`escape_witness: none`

`admission_basis: open-problem-resolution (#13205; Proved)`

The computational-content classification is `utility: none`: this is a
symbolic theorem for arbitrary admissible parameters, rather than bounded
enumeration, a checker, numerical reduction or a certified finite instance.
Information-escape registration is paused under CLAUDE.md §3.9.

## Falsifier

An admissible $(p,T,N,k)$ with either $H_1\notin p^{2k}R$ or
$H_2\notin p^kR$ falsifies the conjecture. A mismatch between the literal
finite image `U` and the unit grid, failure of the affine reflection at an
endpoint, or failure of either boundary congruence invalidates the stated
route. Finite agreement alone does not prove the universal claim.

## Evidence

The theorem is `CalderonReciprocalMoments.result` in
`D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.lean`.
Its public surface consists of `R`, `element`, `Admissible`, `U`, `H1`, `H2`,
`claim`, and this one theorem. The axiom closure is the standard
`propext`, `Classical.choice`, `Quot.sound`.

A compiled exact check inhabits the assumptions at $p=7,T=0,N=1$ and
inhabits `R` by zero. No `sorry`, private axiom or `native_decide` is used.
The Scribe result carries a `ResolutionKind.Proved` claim for this dossier.
The source formulas and the interpretation of their positive endpoints
are recorded in `Library/QuadraticForms/calderon2026rectangular.md`.

## Triage

`theorem`; resolution `Proved` for Conjecture 6.3, for all its parameters.

### What the settlement shows

- **Proved in this module:** the two moment bounds, simultaneously and
  uniformly in the chosen imaginary quadratic order and basis, by
  `D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.result`.
  The decisive mechanism is the combination of the doubling permutation
  with the affine reflection and its two endpoint strips.
- **Computed, probe-reported:** exact arithmetic checks cover 730 distinct
  admissible cases, with $5<p\leq31$, $|T|\leq3$, $1\leq N\leq10$, $k=1,2$,
  and $k=3$ for $p\leq19$. The generating commands are
  `/tmp/op-calderon/checks 2 31`, `/tmp/op-calderon/checks 3 13`, and
  `/tmp/op-calderon/checks 3 19 17 3`; the union removes repeated cases.
  These readings are not premises of the kernel proof.
- **Open:** weakening the admissibility conditions, changing the
  representative rectangle, higher reciprocal powers, and sharpness of
  the two valuations. The delivered theorem asserts no relaxed version.
- **Open:** Conjectures 6.4 and 6.5, the omega-Ljunggren and omega-Bailey
  conclusions. The source's reciprocal-moment premise is supplied by
  Conjecture 6.3 as proved here; the translated-block, Newton-identity and
  factorization arguments needed for those further conclusions are not
  additional conclusions of this module.

## ASSUMED-UNVERIFIED

The external literature-search counts and finite numerical checks above
are producer-reported. Exhaustive absence of an earlier proof and
historical priority are not verified. Sharpness, relaxed hypotheses and
the source's remaining conjectures are open; this settlement does not
prove them.
