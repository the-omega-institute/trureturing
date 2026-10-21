---
slug: amdeberhan-chen-moll-sagan-2014-reciprocal-tail-floor-conjecture-4-6
bibkey: amdeberhanchenmollsagan2014fibonomial
doi: 10.1007/s00026-014-0242-9
url: https://arxiv.org/abs/1306.6511v2
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.result
---

# Floors of reciprocal generalized Fibonacci tails

## Problem

Amdeberhan, Chen, Moll and Sagan, *Generalized Fibonacci polynomials and
Fibonomial coefficients*, Annals of Combinatorics 18 (2014), 541–562,
Conjecture 4.6, first clause:

> If $s>t\geq1$ with $(s,-t)\ne(2,-1)$ and $n,r\in\mathbb P$ then
> $\left\lfloor\left(\sum_{k=n}^{\infty}1/\{rk\}_{s,-t}\right)^{-1}\right\rfloor
> =\{rn\}_{s,-t}-\{r(n-1)\}_{s,-t}-1$.

The source defines $\mathbb P$ as the positive integers and
$\{0\}_{s,t}=0$, $\{1\}_{s,t}=1$,
$\{j+2\}_{s,t}=s\{j+1\}_{s,t}+t\{j\}_{s,t}$.
The squared-reciprocal clause is a separate question.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Integral coefficients and the three recurrence cases | `U` | Literal recursive definition over integers and natural indices. |
| $s>t\geq1$ | `claim`'s `t < s` and `1 ≤ t` | Same inequalities. |
| $(s,-t)\ne(2,-1)$ | The excluded-pair hypothesis | Same pair and signs. |
| $n,r\in\mathbb P$ | Natural indices with `1 ≤ n`, `1 ≤ r` | Exactly positive indices. |
| Tail starting at $n$ | Real reciprocal of `U s (-t) (r * (n + k))`, summed over natural $k$ | Reindexing, with the integer denominator cast to the reals. |
| Convergence presupposed by the source | Explicit `Summable` conjunct | Prevents a divergent `tsum` from satisfying the identity vacuously. |
| Reciprocal, integer floor and difference endpoint | Second conjunct of `claim` | Natural subtraction at $n-1$ is ordinary subtraction because $n\geq1$. |

## Motivation

This is the first-tier external named conjecture preregistered in
[#18768](https://github.com/the-omega-institute/trureturing/issues/18768).
The settling node is `D5/S1/Recurrence/LinearRows/ACMSReciprocalTailFloor.result`.
It proves the complete first clause, including convergence, with symbolic
parameters and stride. The source acknowledgement is
`D5/L/ArithUnits/amdeberhanchenmollsagan2014fibonomial`.

## Gap

The growing Cassini defect for a negative second coefficient requires a
uniform upper comparison. A result for a unit second coefficient alone does
not cover arbitrary integral $t\geq1$. Literature completeness remains
ASSUMED-UNVERIFIED; the preregistration distinguishes direct readings from
search-seat reports of partial results.

## Route

Write $a_k=U(s,-t,rk)$, $Q=t^r$, $c=U(s,-t,r)$ and let $P$ be the trace of
the $r$th power of the companion matrix. The frozen
`D5.S0.Observation.MatrixTracePowerSum.pow_add_two`, used in `stride_rec`,
gives the stride recurrence. Integer induction supplies
$P\geq Q+1$, $P\geq c+2$ and $c\geq1$ without a root formula.

For a real recurrence satisfying `RecData`, put $b_k=a_{k+1}-a_k$.
The private helpers prove $b_k\geq c(k+1)$,
$a_{k+1}^2-a_ka_{k+2}=c^2Q^k$, and
$c^2Q^k+1\leq a_{k+2}-a_k$. The positive denominators then give
$1/b_m<S_m$ and, when $b_m>1$, $S_m\leq1/(b_m-1)$, where
$S_m=\sum_{k\geq0}1/a_{m+k+1}$.
The reciprocal limits vanish by linear growth. With the integer endpoint
$B=b_m$, these bounds give $\lfloor S_m^{-1}\rfloor=B-1$.
The case $B=1$ uses positivity and the strict lower tail estimate.

## Falsifier

An admissible integral quadruple $(s,t,n,r)$ with a different floor, or a
failure of convergence, contradicts the settled proposition. The excluded
pair has $U(2,-1,j)=j$ and a harmonic tail. A finite numerical check cannot
establish the universally quantified result.

## Evidence

`D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor.result` proves `claim`.
The only public mathematical definitions are `U` and `claim`; the analytic
and integer-recurrence helpers are private. The axiom closure of every public
declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

Escape audit unfinished:
[#19868](https://github.com/the-omega-institute/trureturing/issues/19868),
covering `D5.S1.Recurrence.LinearRows.ACMSReciprocalTailFloor.result`.
No faithful enrolled infinite-family readout with the required reconstruction,
variation, sensitivity and observational-dependence proofs is supplied. No
`declared_validated` registration is asserted.

### Experiment

[Independent numerical checks at commit 281d694121129f1956238980908f2f72a8dae758](https://github.com/the-omega-institute/trureturing-experiments/tree/281d694121129f1956238980908f2f72a8dae758/docs/reports/amdeberhan-chen-moll-sagan-2014-conjecture-4-6-reciprocal-tail).
Command: `python3 check.py`, from that directory; exit 0.
Script SHA-256: `2c617d7bdee2463146b5e021bc12cd0711e409ee54c57ba781ad7011947fa86e`.
The 260-digit calculation with cutoff $10^{-240}$ reports 1,300 passing floor
and tail-bound cases for $2\leq s\leq12$, $1\leq t<s$, $(s,t)\ne(2,1)$,
$r\in\{1,2,3,5\}$ and $n\in\{1,2,3,4,7\}$.
Exact Cassini and domination checks have zero failures for $2\leq s\leq9$,
$1\leq t<s$, excluding $(2,1)$, $r\in\{1,2,3,4\}$ and
$1\leq k<\lfloor400/r\rfloor-1$. The check also verifies the first eleven
values $U(2,-1,j)=j$ for $0\leq j\leq10$; divergence is the harmonic-series
argument, not an experimental conclusion. These are computed finite checks.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Root-free companion bounds $P\geq t^r+1$ and $P\geq U(s,-t,r)+2$ | Proved, kernel-checked private `stride_parameters`, using `integer_growth` and `matrix_shape`; used by public `result`. The square-root/Binet route is unnecessary for this proof. |
| Real-coefficient recurrence theorem under `RecData` | Proved, kernel-checked private `recurrence_floor`. Its $a,P,Q,c$ are real; only the endpoint $B$ is an integer, with $(B:\mathbb R)=b_m$. For an integral sequence this endpoint is integral, so the general integral-recurrence conclusion in the preregistration follows by the same theorem. |
| Linear growth suffices for the telescope limits | Proved, kernel-checked private `growth`, `inv_b_limit`, `telescoping_has_sum`, `upper_has_sum` and `tail_lower`. No geometric-series estimate is a premise. |
| Conjecture 4.6, squared-reciprocal second clause | Open; no declaration in this module settles it. |
| Complete literature assertion that no prior proof settles the first clause, including the scope of partial results | Open, ASSUMED-UNVERIFIED; literature reading and attributed reports in #18768, not a kernel theorem. |

The decisive mechanism is uniform domination of the growing Cassini defect,
which supplies the shifted telescoping upper bound. The floor interval is
$B-1\leq S_m^{-1}<B$, with the endpoint $B=1$ included. The helpers extend the
analytic argument to real recurrence data satisfying their explicit
inequalities; no unrestricted real-parameter floor theorem is claimed.

The first-clause statement of Conjecture 4.6 is therefore available as a theorem.
The squared-reciprocal clause and claims about other source results depending
on it remain open here. No inventory of all downstream literature consequences
is asserted. Prior partial results are reported in #18768: Cui et al.,
arXiv:2212.02639v2, Theorem 1.7, Case 1 has a restricted negative coefficient
and a defect-domination hypothesis; Park, arXiv:1407.8086, Theorem 18 is
search-seat reported. Their complete scope and the completeness of this
comparison remain ASSUMED-UNVERIFIED.

## ASSUMED-UNVERIFIED

The literature screen is the one attributed in #18768. It includes direct
readings of the source and Cui et al.; the other partial-result claims are
attributed search-seat reports. It does not prove that all prior literature
has been found or that none contains a prior proof. Four-slot escape
registration remains unfinished under #19868. The second conjecture clause
and a complete analysis of downstream source dependencies remain open.
