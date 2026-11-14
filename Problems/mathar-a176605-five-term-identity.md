---
slug: mathar-a176605-five-term-identity
bibkey: mathar2016a176605
doi: null
url: https://oeis.org/A176605
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence.result
---

# Mathar's A176605 five-term identity

## Full source question

OEIS A176605 revision 19, NAME, defines a natural sequence by a(0)=a(1)=1
and, for every m ≥ 1,

$$
a(m+1)=\sum_{p=0}^{m}a(p)a(m-p)+1.
$$

Its FORMULA line, attributed to R. J. Mathar, states:

> Conjecture: (n+1)*a(n) +2*(-3*n+1)*a(n-1) +(9*n-13)*a(n-2) +8*(-n+3)*a(n-3) +4*(n-4)*a(n-4)=0.

The unchanged event is: for every a : Nat → Nat satisfying exactly those
initial values and convolution equations, and for every natural n ≥ 4,

$$
(n+1)a(n)+2(-3n+1)a(n-1)+(9n-13)a(n-2)
 +8(-n+3)a(n-3)+4(n-4)a(n-4)=0
$$

in the integers, with n and all a-values cast before signed arithmetic.
Lag indices are natural. The source omits the linear onset: n ≥ 4 is the
explicit nonnegative-backshift interpretation, not OFFSET 0,3. The nonlinear
recurrence is not imposed at m=0. The sum includes p=0 and p=m; +1 is
outside the sum.

## Mechanism and complete bridge

The original source conditions imply the formal-series equation

$$
X(1-X)A^2-(1-X)A+1-X+X^2=0,\qquad A=\sum_{n\ge0}a(n)X^n.
$$

Coefficient extensionality proves this bridge, treating the first two
coefficients separately. After differentiation, a polynomial certificate
and cancellation of the nonzero factor 2XA-1 yield

$$
(1-6X+9X^2-8X^3+4X^4)(XA')+(1-4X+5X^2)A
 =1-2X+4X^2-2X^3.
$$

The inhomogeneous equation is valid in every degree. The forcing polynomial
has no coefficient at n ≥ 4. Applying the existing frozen Euler coefficient
identity and four backshifts gives the entire homogeneous five-term formula.
The proof assumes neither the entry's generating function nor its alternate
finite-sum expression, and uses no analytic convergence or finite-prefix
surrogate. A well-founded natural recursion constructs an actual source;
the Reg mirror proves its full source conditions and uses it in variation.

## Evidence and boundaries

The Lean mathematical source and matching Blueprint share the subject
address `D5/S1/Recurrence/Algebraic/MatharA176605FiveTermRecurrence`.
Its sole public theorem `result` has exactly the universal proposition
`claim`. The private helpers are consumed on the convolution, differentiation,
elimination and coefficient-extraction path. The source construction is
consumed by the Reg nonvacuity and intervention proofs. This unit is ready
for independent pre-freeze fidelity and form review only after the current
scoped Lean and native binding consumers succeed; no frozen status or
publication is asserted here.

The original source locator, attribution, confirmed CC BY-SA 4.0 license
and bounded literature search are in
`Library/RecurrenceAlgebraic/mathar2016a176605.md`.
[Issue #30568](https://github.com/the-omega-institute/trureturing/issues/30568#issuecomment-6884652919)
is the unchanged preregistration. Worldwide openness, priority and reliable
general web coverage remain ASSUMED-UNVERIFIED.

## Triage and continuation

The exact named question is the sole proposed problem resolution, with
proof_shape: bind-only, admission_basis: open-problem-resolution and
utility: none. The essential mechanism is the faithful convolution-to-series
bridge and algebraic differential elimination; no new general extraction
result is claimed.

- **Proved by the scoped result when compiled:** all original source
  sequences satisfy the identity at every n ≥ 4. The forcing polynomial
  explains this complete legal-lag range; no minimal-order claim follows.
- **Internal consequence:** the inhomogeneous differential equation holds
  in every degree. It is a consumed proof step, not another exported resolution.
- **Open successor candidate:** for the source's broader family
  a(m+1)=Σ(a(p)a(m-p)+k)+l with arbitrary fixed natural k,l and the same
  initial values, determine a uniform polynomial differential equation and
  the full legal-lag recurrence, including degree drops in degenerate
  parameters. This is a research direction, not another proved named question.
- **Open here:** minimal homogeneous recurrence order, analytic asymptotics,
  and a verified equivalence to the entry's alternate finite sum.

A falsifier of the unchanged event would be an actual natural-valued source
satisfying all original conditions and a violating index n ≥ 4. A failed
attempt to derive the generating function would not itself be a refutation.
The Reg audit and pre-freeze review are separate from the mathematical
identity and must not be inferred from this narrative.
