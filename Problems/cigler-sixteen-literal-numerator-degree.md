---
slug: cigler-sixteen-literal-numerator-degree
bibkey: cigler2023catalanpowers
doi: 10.48550/arXiv.2308.07642
url: https://arxiv.org/abs/2308.07642v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.result
---

# The literal numerator degree in Cigler's Conjecture 16

## Problem

Johann Cigler, *Some experimental observations about Hankel determinants of
convolution powers of Catalan numbers*, arXiv:2308.07642v2, Section 3,
Conjecture 16, equation (30), printed page 10, asserts the following whole
conjunction. For every integer $k\ge1$ and every integer $m\ge1-k$, there is
an actual polynomial $Q=Q_{2k-1,m}$ such that

$$
\left(1+(-1)^k x^{2k-1}\right)^{\binom{k+m}{2}+1}
\sum_{N\ge0}D_{2k-1,m}(N)x^N=Q(x),
\qquad \deg Q=\pi_{2k+1}(m+k-1)+k.
$$

Here $C(x)=\sum_{n\ge0}C_nx^n$, where $C_n=\binom{2n}{n}/(n+1)$ is the
Catalan number; $C_{r,t}=[x^t]C(x)^r$ for $t\ge0$, and $C_{r,t}=0$ for
$t<0$. The actual determinant is

$$
D_{r,m}(N)=\det(C_{r,i+j+m})_{0\le i,j<N},\qquad D_{r,m}(0)=1,
\qquad \pi_j(t)=\frac{t((j-2)t+(j-4))}{2}.
$$

Every $Q$ is either palindromic or skew palindromic: for its actual degree
$d$, $x^dQ(1/x)=Q(x)$ or $x^dQ(1/x)=-Q(x)$. Palindromicity is required
if $k\equiv1\pmod4$ and $m$ is even, if $k\equiv3\pmod4$ and $m$ is odd,
and if $k\equiv0,2\pmod4$ and $m\equiv0,1\pmod4$. These implications
include no converses. The generating identity is coefficientwise.

The source does not specify a coefficient ring. The formal claim uses complex
polynomials and series. Its exact-degree clause uses an actual natural degree
$d$ with $Q.\mathrm{degree}=d$, then equates $d$ to the source's expression
in exact rational arithmetic. It therefore excludes the zero polynomial and
does not assign a nominal or padded degree. The reciprocity equations are
stated directly at every nonzero complex argument with that actual degree.

## Motivation

The named conjecture combines rationality of every full determinant generating
series with exact numerator degree and reciprocity. Refuting its universally
quantified conjunction requires one allowed pair, while preserving every clause
in the statement being negated. The designated theorem is
`D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.result`.

## Gap

The bounded qualification of the source and the related texts of Fulmek
(2402.19127v2 and ECA 5:3, Article S2R17), Cigler (2403.11244v1 and
2404.05263v2), Liu–Wang–Zhang–Zhang (2503.17187v1), Chern–Shi
(2608.27208v1), and Han (2512.12603v1 and EJC 33(2), P2.42) identified no
whole literal Conjecture 16 answer. Inspected MathDB entries 392477, 340916,
340917, 340918 and 372040 concern different determinant assertions. This is
a bounded finding, not a claim of global absence or priority.

The reservation is [issue 23457](https://github.com/the-omega-institute/trureturing/issues/23457).
The all-state ownership screen distinguished the other owner's issue 12943 and
PR 13035, which concern Conjecture 11: a single determinant-size residue class
at odd convolution orders at least three. That target does not include the
whole generating series, numerator degree, reciprocity clauses or order one.

## Route

Take the permitted pair $k=1,m=0$. Its order is one, its exponent is
$\binom12+1=1$, and its multiplier is $1-x$. Since $\pi_3(0)=0$, the
demanded actual degree is one. The actual empty and singleton determinants
give $D_{1,0}(0)=D_{1,0}(1)=1$. Consequently

$$
[x](1-x)\sum_{N\ge0}D_{1,0}(N)x^N
=D_{1,0}(1)-D_{1,0}(0)=0.
$$

Equality to $Q$ transfers this coefficient to $Q$. An actual polynomial of
exact degree one has a nonzero coefficient at one, giving the contradiction.
Only these two determinants are needed; no all-order Hankel evaluation is
reproved. The constant coefficient of the product is one, so the source's
degree convention for zero cannot affect the obstruction.

The Catalan series is the coefficientwise image of Mathlib's actual natural
Catalan series. Its powers supply the convolution coefficients, and Fin N
matrices supply the determinants. Natural conversions affect only $k$,
$2k-1$ and $k+m$, all positive in the claimed range. Negative $m$ remains
an integer, and the polygonal expression uses ordinary signed arithmetic.

## Falsifier

A source exclusion of $k=1,m=0$, or a degree upper bound in place of exact
degree, would invalidate this literal refutation. The printed statement has
neither. Its following paragraph calls $k=1$ “not optimal” and prints
$Q_{1,m+1}(x)=(x-1)^{m+1}P_{2,m}(x)$. With $m\ge0$ from (29), that relation
does not address $Q_{1,0}$ and does not expressly retract exact degree. Its
printed sign is not corrected or used as a premise. V1 Conjecture 16 is a
different assertion, numbered Conjecture 18 in v2.

## Evidence

The theorem negates the closed definition `claim`, which contains the whole
universal conjunction. The proof applies the source claim at $k=1,m=0$ and
uses Mathlib's `Matrix.det_isEmpty`, `Matrix.det_fin_one`, Catalan series
coefficient identities, `PowerSeries.coeff_succ_X_mul`,
`Polynomial.coeff_coe`, and `Polynomial.coeff_ne_zero_of_eq_degree`.
The private coefficient obstruction is quantified over every commutative
ring. It therefore applies directly to integer, rational and real polynomials
as well as to the chosen complex realization; no rational-only restriction or
unproved coefficient-field transfer is involved.

## Triage

Tier 1: an externally named experimental conjecture with a short literal
boundary obstruction and bounded literature qualification. The mathematical
claim is the negation of the whole literal v2 assertion, not of a repaired
family. No worldwide priority or new determinant evaluation is claimed.

### What the refutation shows

- Proved (Lean, designated GID above): the full literal Conjecture 16 is false.
  Its exact-degree clause already fails at the allowed order-one boundary.
- Known (source equation (6)): all $D_{1,0}(N)$ are one, so the actual
  numerator at this pair is the constant polynomial one. This all-order
  evaluation is attributed to the source, rather than claimed as a new result.
- Open here: a corrected exact-degree formula, the version restricted to
  $k\ge2$, and the general rationality and reciprocity assertions considered
  separately. The zero linear coefficient does not refute a degree bound.
- Source dependency boundary: the source's subsequent examples for $k=2$ and
  its displayed boundary formulas with $k\ge2$ or $k\ge3$ do not use the
  excluded order-one exact-degree conclusion. The literal counterexample
  gives no counterexample to those formulas, to Conjecture 15, or to the
  distinct binomial-determinant Conjectures 17 and 18.

## ASSUMED-UNVERIFIED

Unindexed or private answers, uninspected literature and worldwide standing
are not established by the bounded source and ownership screens. Independent
assessment of the source-to-statement fidelity remains separate from Lean
verification of the stated negation. No assertion about a repaired conjecture
or the author's intended correction is made.
