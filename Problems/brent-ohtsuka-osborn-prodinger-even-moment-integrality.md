---
slug: brent-ohtsuka-osborn-prodinger-even-moment-integrality
bibkey: brent2016evenmoments
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/BrentEvenMomentPolynomial.result
---

# Ordinary integer coefficients of even double binomial moments

## Problem

Brent, Ohtsuka, Osborn and Prodinger, *Some Binomial Sums Involving
Absolute Values*, Journal of Integer Sequences 19 (2016), Article 16.3.7,
§3.3, printed page 10 immediately after Theorem 9, state:

> It follows from Theorem 9 that the coefficients of $2^{2r-4n}W_{2r}(n)$
> are in $\mathbb Z$, but it is not obvious how to prove the stronger result,
> suggested by the cases above, that the coefficients of $2^{r-4n}W_{2r}(n)$
> are in $\mathbb Z$. We leave this as a conjecture.

The corresponding locator in [arXiv:1411.1477v2](https://arxiv.org/abs/1411.1477v2)
is §3.3, printed page 11 after Theorem 5. This dossier anchors exactly
that stronger coefficient assertion. With the source's conventions,

$$
W_\beta(n)=\sum_{i,j=-n}^{n}
\binom{2n}{n+i}\binom{2n}{n+j}|i^2-j^2|^\beta,
$$

where $r,n,\beta$ are nonnegative integers, binomial coefficients vanish
outside their legal range and $0^0=1$. The exact assertion is

$$
\forall r\in\mathbb N\;\exists P_r\in\mathbb Z[X]\;\forall n\in\mathbb N,
\qquad 2^{4n}P_r(n)=2^rW_{2r}(n)
\quad\text{in }\mathbb Q.
$$

The polynomial is chosen before $n$. Its ordinary monomial coefficients
must be integers; integer-valued rational polynomials do not suffice.
Neither zero parameter is excluded, and no degree restriction or
additional moment-expansion hypothesis is imposed.

## Motivation

The source's even-moment theorem gives the weaker factor $2^{2r-4n}$.
The question asks for an additional uniform factor of $2^r$ in those
coefficients. The full assertion, rather than finitely many orders or
values, is the Tier 1 target preregistered in
[issue 30544](https://github.com/the-omega-institute/trureturing/issues/30544).

## Gap

`D5/S3/ArithSums/BrentEvenMomentPolynomial.result` proves the full
quantified equation above. Its `W` is defined independently by the original
integer-index double sum, and `claim` has no extra premises.
The separate source-bound escape registration remains unfinished under
[issue 30597](https://github.com/the-omega-institute/trureturing/issues/30597);
no `declared_validated` audit is asserted.

## Route

Pair two sign sequences of length $2n$ and count them by their positive
positions to recover the exact binomial multiplicities in $W$.
For paired signs $\epsilon,\eta$, put
$U=(\epsilon+\eta)/2$ and $V=(\epsilon-\eta)/2$.
The product of their coordinate sums is the difference of the two
squared centered indices. Expanding the $2r$ factors of each color and
grouping step labels by their equality partition gives a finite sum over
partitions of $4r$ positions.

Mixed blocks and odd blocks contribute zero. Each nonempty pure even
block contributes $1/2$. A surviving partition with $m$ blocks has
$m\le 2r$ and $(2n)_{\underline m}$ injective label assignments.
The recursively constructed integer polynomial $K_m$ satisfies

$$
2^{\lceil m/2\rceil}K_m(X)=(2X)_{\underline m}.
$$

Thus $H_{r,m}=2^{r-\lfloor m/2\rfloor}K_m$ has integer coefficients
and satisfies $2^mH_{r,m}(n)=2^r(2n)_{\underline m}$.
Summing these polynomials over all surviving partitions gives a single
polynomial for each $r$. The finite-average denominator is exactly
$2^{4n}$, yielding the stated cleared identity, including the empty cases.

The proof directly reuses the equality-kernel grouping and quotient-block
assignment results in
`D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion`,
and Mathlib's descending Pochhammer and embedding-cardinality theorems.
That existing partition module is an unfrozen source supplier; its results
are neither new mathematics of this dossier nor previously frozen inputs.

## Falsifier

A nonnegative order $r$ for which no ordinary integer-coefficient
polynomial agrees with $2^{r-4n}W_{2r}(n)$ at every nonnegative $n$
would refute the assertion. A failed finite interpolation or one
nonintegral value of an unrelated normalization would not establish this.

## Evidence

The exact source definitions and conclusion are represented by
`BrentEvenMomentPolynomial.binomial`, `.W`, `.claim` and `.result`.
The constructive proof includes `half_falling_eval`, `integral_basis_eval`
and `polynomial_mean`; the other theorem helpers are used in that proof.
The Blueprint states the same $\forall r\,\exists P_r\,\forall n$ equation
over the rationals and attributes the source question to the Library note
`D5/L/ArithSums/brent2016evenmoments`.

The bounded source qualification attached to issue 30544 compared
Krattenthaler–Schneider [1607.05314v3](https://arxiv.org/abs/1607.05314v3),
Brent–Krattenthaler–Warnaar [1601.06536v1](https://arxiv.org/abs/1601.06536v1),
Bostan–Lairez–Salvy [1510.07487v2](https://arxiv.org/abs/1510.07487v2),
and the single-moment formulas of Tuenter and Brent. Those checked results
do not supply this uniform ordinary-coefficient assertion. The final JIS
source retains the conjecture. The inherited repository, pinned Mathlib
and lexical public Lean searches found no exact settlement within their
stated scope; this is not an exhaustive literature or Lean-library census.

## Triage

The target is a Tier 1 explicitly published conjecture. The formal result
covers its full parameter range; it is an unbounded algebraic and
combinatorial theorem, rather than a bounded enumeration, checker,
numerical reduction or certified positive finite instance.

### What the settlement shows

- **Proved:** `BrentEvenMomentPolynomial.result` supplies the stronger
  ordinary-coefficient normalization for every even order, with both zero
  indices included. The decisive mechanism is the cancellation of powers
  of two in falling factorials for pure even equality partitions, as
  established by `half_falling_eval`, `integral_basis_eval` and
  `polynomial_mean` in the same module.
- **Proved:** the source's displayed low-order coefficient patterns extend
  to all nonnegative orders through this single quantified theorem.
  The source's weaker even-moment theorem remains a compatible prior
  formula; it is reused as source context, not reproved here.
- **Open:** sharp coefficient divisibility beyond this normalization,
  extensions to other weights, and the source's separate odd-moment
  questions are not resolved by this declaration. They require their own
  statements and evidence. No additional downstream source theorem or
  distinct open question is claimed as settled.

## ASSUMED-UNVERIFIED

The literature qualification is bounded and inherited from the source
qualification and independent source review; it gives no global priority
or universal still-open certificate. Opening a pull request is not a
complete delivery or a new-open-problem KPI settlement.
The Reg issue leaves source reconstruction, source-law equivalence,
whole-family variation and sensitivity, actual observational dependence
and current registration binding evidence unfinished. The linked issue
is an explicit audit exception, not a proof or registration status.
