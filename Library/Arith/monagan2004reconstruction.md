---
bibkey: monagan2004reconstruction
authors: Michael Monagan
year: 2004
title: "Maximal Quotient Rational Reconstruction: An Almost Optimal Algorithm for Rational Reconstruction"
doi: 10.1145/1005285.1005321
url: https://www.cecm.sfu.ca/~mmonagan/papers/MQIRR.pdf
claim: "Algorithm RR reconstructs or excludes a reduced modular rational in an unequal height box with 2ND<m; Lemma 2 identifies it deterministically by the unique largest Euclidean quotient when 9n^2d^2<m."
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

Lemma 2, p.247, applies to a reduced $a/b$ with $b>0$,
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

## Parameter transport

For the [FIB theory](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
fix the same reference $n=n_y$ for the entire host window and write the whole
host ratio $N/n=u/v$ in lowest terms. Use

$$
(m,x,P,Q)=(V,\ n\bmod V,\ W,\ U),\qquad a/b=v/u.
$$

The height tests are $2UW<V$ for RR and $9U^2W^2<V$ for the deterministic
maximal-quotient identification. The latter forces a Euclidean quotient
larger than $\sqrt V$ in $(V,n\bmod V)$; the integer part of $n/V$ is not
such a signature. Both conditions require certified integer bounds on the
whole host, including its cofactor, rather than just on one divisor.

Successful reconstruction still needs the original divisibility and source
window filters. It neither proves low-loss membership nor bounds the
complete Robin weight of a surviving host. These are separate consumers of
the retrieved actual integer. No random-residue assumption is made for
the specified Fibonacci modulus.
