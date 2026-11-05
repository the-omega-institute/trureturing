---
slug: oeis-a002620-forberg-exponential-floor
bibkey: forberg2013a002620
doi: null
url: https://oeis.org/A002620/internal
triage: theorem
motivation_gids:
  - D5/S3/Analytic/SeriesInequalities/ForbergExponentialFloor.result
---

# Forberg's exponential formula for the quarter-squares

## Problem

OEIS A002620, revision 880, contains the formula attributed to Richard R. Forberg:

> Empirical: a(n-1) = floor(n/(e^(4/n)-1)). - _Richard R. Forberg_, Jul 24 2013

The entry defines the quarter-squares by
$a(m)=\lfloor m/2\rfloor\lceil m/2\rceil=\lfloor m^2/4\rfloor$, with offset zero.
The complete assertion is

$$
\forall n\in\mathbb N,\quad 1\le n\ \Longrightarrow
\left\lfloor\frac{n}{\exp(4/n)-1}\right\rfloor
=\left\lfloor\frac{(n-1)^2}{4}\right\rfloor.
$$

All operations inside the floors are in $\mathbb R$, with $n$ coerced before
division and subtraction. The exponential is `Real.exp`; both floors are
`Int.floor` and the equality is in $\mathbb Z$. The index shift is $m=n-1$.
The assertion includes $n=1$, both parities, and arbitrarily large indices,
with no additional hypothesis.

## Motivation

The formula identifies a transcendental expression with an elementary integer
sequence at every positive index. The result explains the agreement through
uniform analytic bounds and the spacing of integer floor intervals.

## Gap

The source labels the formula empirical and supplies no proof of this line.
The mathematical obligation is the identity at all positive indices; agreement
on a finite prefix would leave that obligation open. The bounded literature
scope and its unverified surfaces are stated in
`Library/AnalyticClosure/forberg2013a002620.md`; they do not certify worldwide
openness or priority.

## Route

For every real $r\ge2$, the private lemma `bounds` establishes

$$
\frac{(r-1)^2}{4}
\le\frac{r}{\exp(4/r)-1}
<\frac{r^2}{4}-\frac r2+1.
$$

The denominator is positive. With $q=(1+1/r)/(1-1/r)$, the logarithmic series
bound gives $4/r\le2\log q$, hence
$\exp(4/r)\le((r+1)/(r-1))^2$ and the lower estimate. The quadratic bound
$\exp(4/r)\ge1+4/r+(4/r)^2/2$ gives the strict upper estimate.
The proof directly applies `Real.sum_range_le_log_div` at $x=1/r$, $N=1$,
and `Real.quadratic_le_exp_of_nonneg`.

For $n=2k\ge2$, both expressions have floor $k(k-1)$; for $n=2k+1\ge2$,
both have floor $k^2$. `Int.floor_eq_iff` verifies the corresponding unit
intervals. At $n=1$, the quadratic exponential bound places
$1/(\exp(4)-1)$ in $[0,1)$ and the shifted square is zero.

## Falsifier

A counterexample would be a natural number $n\ge1$ for which the two integer
floors differ. Fidelity would fail if the theorem replaced real subtraction by
natural subtraction, changed the exponent or shift, omitted $n=1$ or a parity,
or bounded the index range. The stated theorem retains every one of these
clauses.

## Evidence

The Lean source is
`D5/S3/Analytic/SeriesInequalities/ForbergExponentialFloor.lean`.
The public declaration is
`D5.S3.Analytic.SeriesInequalities.ForbergExponentialFloor.result` with type

```lean
∀ n : ℕ, 1 ≤ n →
  (⌊(n : ℝ) / (Real.exp (4 / (n : ℝ)) - 1)⌋ : ℤ) =
    ⌊(((n : ℝ) - 1)^2 / 4)⌋
```

The only other authored declaration is the private real-parameter lemma
`bounds`, used in both parity branches of `result`. Both declarations have
exactly the standard axioms `Classical.choice`, `Quot.sound`, and `propext`.
The Blueprint Scribe binds the public result to this dossier with
`OpenProblemResolutionClaim` and `ResolutionKind.Proved`.

## Triage

**Proved:** the whole positive-integer identity, including the endpoint and
both parity formulas, by the declared result. The mechanism is the real
analytic sandwich combined with integer spacing; the private bound itself
holds uniformly for real $r\ge2$.

The quarter-square definition is used with the substitution $m=n-1$; no new
sequence definition is introduced. The proof adds no arbitrary-real floor
identity, further conjecture, asymptotic theorem, or priority claim.

## ASSUMED-UNVERIFIED

The source identity is bound to revision 880 and the authenticated payload
recorded in the Library note. The accepted bounded searches do not establish
absence of every prior proof; failed reads, unread papers, historical indexing
corrections, and truncated benchmark coverage remain unverified.

The source-bound four-slot Reg audit remains unfinished under
[issue #23058](https://github.com/the-omega-institute/trureturing/issues/23058).
The client candidate failed to convert its actual and intervened readouts to
the explicit floor expressions. Compiled rejection/variation, role sensitivity,
actual observational dependence, complete registration axiom closures, and a
current source reconstruction/template/binding certificate are missing.
No Reg source is retained and no `declared_validated` status is asserted.
