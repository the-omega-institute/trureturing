---
bibkey: monagan2004reconstruction
authors: Michael Monagan
year: 2004
title: "Maximal Quotient Rational Reconstruction: An Almost Optimal Algorithm for Rational Reconstruction"
doi: 10.1145/1005285.1005321
url: https://www.cecm.sfu.ca/~mmonagan/papers/MQIRR.pdf
claim: "Algorithm RR reconstructs or excludes a reduced modular rational in an unequal height box with 2ND<m; the nonzero-numerator case of Lemma 2 identifies it by the unique largest Euclidean quotient when 9n^2d^2<m."
strata_touched: []
license: citation-only
triage: anchor
---

# Classical rational reconstruction and the fixed FIB reference

The inspected primary source is the author's seven-page
[ISSAC 2004 paper](https://www.cecm.sfu.ca/~mmonagan/papers/MQIRR.pdf),
printed pp.243–249, DOI [10.1145/1005285.1005321](https://doi.org/10.1145/1005285.1005321).
The locators below refer to its printed pagination. They record the statements
and algorithm contract; they do not report an independent audit of every proof
or a Lean verification.

## Unequal bounds and the necessary validation

Algorithm Rational Reconstruction (RR), p.245, takes integers
$m>x\ge0$, $P,Q>0$, and $2PQ<m$. It returns a reduced rational $a/b$ with

$$
|a|\le P,\qquad 1\le b\le Q,\qquad a\equiv xb\pmod m,
$$

or `FAIL`, meaning no rational with that contract exists. The numerator may
be negative. The modulus need not be prime, and the bounds need not be equal.
This is classical rational reconstruction, attributed in the paper to Wang
and Wang–Guy–Davenport; no new reconstruction theorem is proposed here.

Remark 2, p.245, records the Collins–Encarnación correction: an unchecked
Euclidean pair must not be accepted and then silently cancelled. Its example
$m=12$, $x=5$, $(a,b)=(-2,2)$ satisfies the integer congruence but reduces to
$-1$, which does not represent $5$ modulo $12$. The reducedness check in
Algorithm RR rejects it. In the reduced-congruence contract above,
$\gcd(b,m)=1$ follows; the application's original denominator-unit condition
must also be respected when producing a modular image.

## Deterministic maximal-quotient condition

Use the nonzero-numerator case of Lemma 2, p.247: a reduced $a/b$ with
$a\ne0$, $b>0$,
$\gcd(b,m)=1$, and $x=a/b\bmod m$. If

$$
|a|b<\sqrt m/3,
$$

the Euclidean algorithm on $(m,x)$ has a unique largest quotient, and its
associated remainder/coefficient row represents $a/b$. The proof uses
Lemma 1, p.246, to show that this quotient exceeds $\sqrt m$.
This is a deterministic recovery statement under the stronger height bound;
the paper's random-input experiments and heuristic stopping parameters are
not substitutes for that bound.
The zero residue has no Euclidean quotient in this convention; Algorithm
MQRR on the same page treats it separately. The FIB application below has
strictly positive $a=v$ and a unit residue, so it does not use that case.

## Parameter transport

For the [FIB theory](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
fix the same reference $n=n_y$ from equation (230.4) in §230.2 for the entire host window and write the whole
host ratio $N/n=u/v$ in lowest terms. Use

$$
(m,x,P,Q)=(V,\ n\bmod V,\ W,\ U),\qquad a/b=v/u.
$$

The height tests are $2UW<V$ for RR and $9U^2W^2<V$ for the deterministic
maximal-quotient identification. The latter forces a Euclidean quotient
larger than $\sqrt V$ in $(V,n\bmod V)$; the integer part of $n/V$ is not
such a signature. Both conditions require certified integer bounds on the
whole host, including its cofactor, rather than just on one divisor.

## Whole-host bounds and actual-source filters

The application directly reuses FIB §230.2 for the height input. If a low-loss
divisor satisfies $d/n=\alpha/\beta$ in lowest terms, write $h=N/d$ and
$q=\gcd(h,\beta)$. The whole-host ratio has

$$
u=h\alpha/q,\qquad v=\beta/q,\qquad v\mid\beta\mid n.
$$

Thus a certified bound $\log\beta\le L_0$ gives
$v\le e^{L_0}$ and $u\le Xv/n$ for the same $N\le X$. Choose a certified
integer $W\ge e^{L_0}$ and $U=\lfloor XW/n\rfloor$. If $U=0$, the positive
envelope is empty; otherwise check $\gcd(n,V)=1$ and $2UW<V$. The asymptotic
$L_0=O(y/\sqrt{\log y})$, $\log n=y+o(y)$ and
$\log V=y/2+O(1)$ provide an eventual short-height regime, not an effective
finite bound or a certified onset. The numerator of $d/n$ alone omits $h$.

Using [Abbott's exact-modulus specialization](abbott2015reconstruction.md),
take the last convergent $k/u$ of $n/V$ with denominator at most $U$ and
form $v=nu-kV$. A possible positive host requires

$$
1\le v\le W,\qquad \gcd(u,v)=1,\qquad v\mid n.
$$

Under the unit and reducedness checks, the final divisibility test is
equivalently $v\mid k$, or $\gcd(n,k)=v$. If it passes, recover

$$
g=k/v,\qquad N=(n/v)u=1+Vg,
$$

and check the original multiplier interval, size window and source restrictions.
Failure excludes all hosts covered by the certified box. Acceptance retrieves
one actual integer; the necessary height envelope does not itself certify
low-loss membership. This is a consumer of classical reconstruction, not a
new uniqueness, continued-fraction or divisor-weight theorem.

The reference factorization and $v\mid n$ give the denominator's factors.
Factor the small numerator $u$ and combine exponents before using an Euler
product:

$$
e_p=v_p(n)+v_p(u)-v_p(v),\qquad
Z(N)=\prod_{p:e_p>0}\frac{1-p^{-(e_p+1)}}{1-p^{-1}}.
$$

$u$ may share primes with $n/v$, so $Z(n/v)Z(u)$ is generally incorrect.
Only the additional factorization of $u$ is required; this does not assert
a polynomial-time factoring algorithm.

For the already recorded FIB source $V=F_{11}=89$, $g=10$, $N=891$ in
§207.3, use reference $n=594$, window $[802,1514]$, $W=2$ and $U=5$.
The last eligible convergent is $20/3$; its remainder is two, which divides
twenty. It recovers $(594/2)\cdot3=891=3^4\cdot11$ and $Z(891)=44/27$.
Splitting the shared power of three would instead give
$Z(297)Z(3)=640/297$. With reference $683$ and the same window and $W$,
$U=4$ and the convergent is $23/3$; its remainder is two but does not divide
twenty-three, so that box contains no integer host. These references are not
the prescribed $n_y$; the examples demonstrate filters, not an asymptotic
onset, low-loss membership or the $N>5040$ Robin range.

Unlike the per-core method of equation (207.11) in FIB §207.3, this application fixes $n_y$ once;
the recovered $n_y/v$ need not be the complete small-prime core and $u$ need
not be a rough coprime cofactor. Those per-core hypotheses cannot be inherited.
The pending analytic consumer remains FIB §233.5. A certified empty envelope
can be combined with an applicable complementary moment bound; a surviving
host still needs its own complete joint budget. Reconstruction alone supplies
no uniform exclusion or favorable signed Robin estimate for the specified
$n_y\bmod F_r$. No random-residue assumption is made for the specified
Fibonacci modulus.
