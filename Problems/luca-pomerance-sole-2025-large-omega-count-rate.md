---
slug: luca-pomerance-sole-2025-large-omega-count-rate
bibkey: lucapomerancesole2025robin
doi: null
url: https://math.dartmouth.edu/~carlp/robin4.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Robin/Analytic/OmegaTail/Asymptotic.result
---

# The exponential rate of the large distinct-prime tail

## Problem

Section 3, “Conclusion and Open Problems,” printed page 3 of the
[correction](https://math.dartmouth.edu/~carlp/robin4.pdf), asks:

> It is interesting to consider the set S(x) of numbers n ≤ x with ω(n) > y.

Here $y=\log x/\log\log x$. The section then asks:

> How good is this estimate?

Write $L=\log x$, $\ell=\log L$, $y=L/\ell$, and

$$
N_\lambda(x)=\#\{1\le n\le x:\omega(n)>y+\lambda y/\ell\},
$$

where $\omega$ counts distinct prime divisors. The target attached to the
Section 3 question of Luca, Pomerance, and Sole is

$$
\frac{\log N_0(x)}y\longrightarrow C_0,
\qquad C_0=\inf_{s>1}s\left(1-\log\frac{s\sin(\pi/s)}\pi\right).
$$

This is a statement about distinct prime factors, not factors counted with
multiplicity. The real cutoff uses the natural floor, and the strict
inequality in the threshold is retained. The source locator is recorded in
`Library/Analytic/lucapomerancesole2025robin.md`.

## Motivation

The source correction bounds the count by $\exp(O(y))$ and uses a related
large-$\omega$ condition to control Robin exceptions. Matching upper and
lower exponents determine the constant in the large-$\omega$ count.
The target is preregistered in issue #31303. This dossier does not assert
that the Robin exceptional set itself has this asymptotic.

## Gap

The Rankin upper bound alone cannot give the matching exponent. A lower
bound must select actual primes, preserve the exact number of distinct
factors after rounding, fit every resulting integer below the original
cutoff, and count different selections injectively. In particular,
$K=y+o(y)$ alone does not justify the product budget: multiplication by
$\ell$ can magnify that error. The required cancellation is
$K\ell=L+\lambda y+O(\ell)$ with $\ell=o(y)$.

## Route

**Paper derivation:** Put $a(s)=s\sin(\pi/s)/\pi$,
$m(s)=\log a(s)-(\pi/s)\cot(\pi/s)$, and
$H(s)=s-\pi\cot(\pi/s)$. On $s>1$,

$$
m'(s)=\frac1s\left(1-\frac{(\pi/s)^2}{\sin^2(\pi/s)}\right)<0,
\qquad F_0'(s)=-m(s).
$$

The signs $m(4/3)>0>m(2)$ give a unique zero $s_0\in(1,2)$.
The derivative signs show that this is the global minimizer of $F_0$.
At that zero, $C_0=F_0(s_0)=H(s_0)>s_0>1$.

**Paper derivation:** The density

$$
q_s(u)=\frac{a(s)^s}{a(s)^s+u^s}\quad(u>0)
$$

has mass one, logarithmic moment $m(s)$, and binary entropy integral
$H(s)$. For $0<r<s$, substitution in the existing power normalizer gives

$$
\int_0^\infty u^{r-1}q_s(u)\,du
=\frac{\pi a(s)^r}{s\sin(\pi r/s)}.
$$

Differentiation at $r=1$, dominated by two neighboring powers, gives the
logarithmic moment. The pointwise entropy identity is

$$
h(q_s)=\log(1+a(s)^s/u^s)-s q_s\log a(s)+s q_s\log u.
$$

The derivative of $u\log(1+a(s)^s/u^s)$ and its vanishing endpoint
limits give the integral of the first term as $s$.

**Paper derivation:** Fix $s>s_0$, so that $m(s)<0$. Truncate $q_s$ to
$[\delta,R]$, let $M=\int_\delta^R q_s$, and use
$g(u)=q_s(Mu)$ on $[\delta/M,R/M]$. This has mass exactly one.
Its moment is $-\log M+M^{-1}\int_\delta^R q_s(v)\log v\,dv$;
its entropy is $M^{-1}\int_\delta^R h(q_s(v))\,dv$.
Thus the moment remains strictly negative and the entropy approaches
$H(s)$. A finite partition into sufficiently narrow positive intervals
$(a_j,b_j]$ gives masses $r_j$ of total one, with
$0<r_j<b_j-a_j$ and $\sum r_j\log b_j<0$. Jensen's inequality gives

$$
\sum_j(b_j-a_j)h\!\left(\frac{r_j}{b_j-a_j}\right)
\ge\int h(g).
$$

**Paper derivation:** PNT supplies $(b_j-a_j)y+o(y)$ actual primes in
each interval $(a_jL,b_jL]$. Take $\lfloor r_j y\rfloor$ primes per
bin and adjust the first bin so that the total is exactly
$K=\lfloor y\rfloor+1$. The adjustment is $o(y)$ and each limiting
occupancy is strictly interior. The exact cancellation above and the
negative moment give $\log n<L$ for every selected product. Distinct
subsets give different squarefree integers by unique factorization.
Their number is the product of the binomial coefficients.

Stirling's formula with moving interior proportions yields

$$
\frac1y\log\binom{P_j(x)}{k_j(x)}
\longrightarrow (b_j-a_j)h\!\left(\frac{r_j}{b_j-a_j}\right).
$$

This proves the lower exponent $H(s)$. Letting $s\downarrow s_0$ gives
$C_0$. The phase-one `OmegaTailUpper.upper_bound`, applied directly at
$s_0$, gives the opposite inequality.

## Falsifier

Replacing $\omega$ by $\Omega$, using separate unattainable bin optima,
losing exact cardinality in rounding, or checking only the first-order
product cost does not prove this statement. A conditional density or
prime-capacity hypothesis does not establish the unconditional count.
An upper bound on Robin exceptions does not determine their lower bound.

## Evidence

**Proved in Lean:** The designated target is
`D5.S3.Arith.Robin.Analytic.OmegaTail.Asymptotic.result`.
It establishes the displayed two-sided limit for $\lambda=0$ without
additional analytic hypotheses. The constant is the stated infimum;
`saddle_characterization` proves its attainment at the unique zero of
$m$ on $(1,\infty)$, the location $1<s_0<2$, and $C_0=H(s_0)$.
`constant_gt_one` proves $C_0>1$.
The source modules separate density integrals, compact truncation,
finite averaging, exact integer adjustment, injective counting, moving
binomial entropy, and final asymptotic composition.

**Literature check as of 2026-11-17:** The bounded comparison supplied
with preregistration #31303 records the following scope:

- Erdos-Nicolas (1981), Theoreme 2, fixes $c<1$ and does not imply $C_0$.
- Nicolas (1984) and Hwang (1998) concern $\Omega$, not $\omega$.
- Pomerance (1985), Theorem 6.1, gives an $\exp(O(y))$ upper bound.
- Hildebrand-Tenenbaum (1988) treats $k\ll L/\ell^2$.
- Norton (1994) gives only an upper bound on the $y\log\ell$ scale
  at the target point.
- Norton (1982), Theorem 1.11, supplies a lower-bound precedent with
  constant one.
- Only the first two pages of Balazard (1990), Progress in Mathematics 81,
  were available; its full text was not excluded as prior coverage.

This is a bounded literature comparison, not a certification of priority.

## Triage

**Proved in Lean (phase 1):** `OmegaTailUpper.upper_bound` gives the
Rankin upper bound $N_\lambda(x)\le\exp((F_\lambda(s)+\epsilon)y)$
eventually for each $\lambda\le1$, $s>1$, and $\epsilon>0$.
The phase-one result at $\lambda=1$ proves
$\log(1+N_1(x))/y\to0$, equivalently $\log(1+N_1(x))=o(y)$.

**Paper consequence:** Rankin's saddle and the density-selection entropy
construction are dual optimizations giving the same constant.
For every fixed $\lambda<1$, the analogous saddle solves
$m(s_\lambda)=-\lambda$ and gives
$C_\lambda=F_\lambda(s_\lambda)=H(s_\lambda)$.
The full family is not claimed as an additional Lean conclusion.

**Paper consequence:** The lower construction uses exactly
$K=\lfloor y\rfloor+1$ factors. The single layer
$\#\{n\le x:\omega(n)=K\}$ therefore has the same exponential rate.
This is not a separate formalized conclusion here.

**Paper interpretation:** When the source correction bounds Robin
exceptions using this large-$\omega$ count, the counting input can be
sharpened from an unspecified $O(y)$ to $(C_0+o(1))y$ in the exponent.
This is an upper-bound implication only; no asymptotic equality for the
Robin exceptional set follows.

**Computed, not certified:** A 65-digit mpmath computation of the zero of
$m$ and evaluation of $F_0$ gives
$s_0=1.62838624481198914552\ldots$ and
$C_0=2.80541038572427676832\ldots$.
The interval $2.8054<C_0<2.8055$ is not certified in Lean.

## ASSUMED-UNVERIFIED

Worldwide priority, completeness of later literature, full-text exclusion
of Balazard (1990), and rigorous certification of the displayed decimal
values are unverified.

The four-slot registration for `constant_gt_one` is incomplete:
`IE-C050 ClosedTruthReadout`, `incomplete_closure`,
`source.operand_identity`. The missing evidence is the accepted binding
of the source operands. See
[issue #31359](https://github.com/the-omega-institute/trureturing/issues/31359).
This information-escape audit is unfinished; the Lean proof of $C_0>1$
is separate from that audit.
