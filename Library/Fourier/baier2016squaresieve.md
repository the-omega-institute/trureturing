---
bibkey: baier2016squaresieve
authors: Stephan Baier
year: 2016
title: The square sieve and the large sieve with square moduli
doi: null
url: https://arxiv.org/abs/1506.06148v2
claim: "Lemma 2 recalls Heath-Brown's weighted square sieve, retaining the Jacobi correlations and the support restriction |d|<exp(L) for L sieve primes."
strata_touched: []
license: citation-only
triage: anchor
---

# The weighted square-sieve input

The inspected primary text is [arXiv:1506.06148v2](https://arxiv.org/pdf/1506.06148v2), updated 2016-06-07; the first version was submitted 2015-06-19. The locator used here is **Lemma 2, printed p.2**, rather than the paper's main large-sieve theorem. This is an existing theorem, not a new estimate or a statement of the latest large-sieve bound.

Baier credits D. R. Heath-Brown, *The square sieve and consecutive square-free numbers*, **Mathematische Annalen 266** (1984), 251–259, Theorem 1. The lemma below was checked in Baier's primary text; this note does not claim an independent full-text inspection of Heath-Brown's article.

Let $\mathcal S$ contain $L\ge1$ distinct primes. For a nonnegative weight $w$ supported on positive integers, impose the lemma's additional restriction

$$
w(d)=0\qquad\text{if }d=0\text{ or }|d|\ge\exp(L).
$$

The weighted number of positive squares then satisfies

$$
\sum_{t\ge1}w(t^2)
\ll\frac1L\sum_{d\in\mathbb Z}w(d)
+\frac1{L^2}
\sum_{\substack{p,q\in\mathcal S\\p\ne q}}
\left|\sum_{d\in\mathbb Z}w(d)
\left(\frac d{pq}\right)\right|.
\tag{B1}
$$

The pair sum is ordered. In applications below all sieve primes are odd, so the Jacobi symbol is unambiguous. Its value at a nonunit is zero; replacing that value by one changes the correlation term. The support cap is also part of the quoted lemma. A proposed use with larger discriminants needs another justified sieve formulation or a new choice of primes before (B1) can be applied.

No Lean verification or originality claim is supplied. The primary input alone does not bound the correlations of a population selected by its own prime divisibility conditions.

## Conditioning on the actual FIB prime support

For each actual positive integer $n$, let $h\in\{0,1\}$ be its canonical Zeckendorf unit bit and $(A,B)$ its complete remaining five-window composition. Use the same source throughout:

$$
n=h+2A+3B,\qquad Q=A^2+AB-B^2,\qquad
c=4A+7B,\qquad D=5h^2-4Q.
$$

The existing [FIB theory, §202.1](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md) gives

$$
c^2-D=5n(n-2h).
\tag{B2}
$$

Take a finite population $\mathcal N$ with $D(n)>0$, nonnegative weights $a_n$, and a **common** set $\mathcal S$ of $L$ odd primes dividing every $n\in\mathcal N$. Define

$$
w(d)=\sum_{n\in\mathcal N}a_n\mathbf1_{D(n)=d},
\qquad k(n)=\#\{p\in\mathcal S:p\nmid D(n)\}.
$$

For each $p\in\mathcal S$, (B2) forces $D(n)\equiv c(n)^2\pmod p$. Thus every nonzero symbol is one, while a zero remains zero. For distinct $p,q\in\mathcal S$,

$$
\sum_d w(d)\left(\frac d{pq}\right)
=\sum_{n\in\mathcal N}a_n\mathbf1_{\gcd(D(n),pq)=1}\ge0.
$$

Consequently the entire normalized correlation term is exactly

$$
\frac1{L^2}\sum_{\substack{p,q\in\mathcal S\\p\ne q}}
\left|\sum_d w(d)\left(\frac d{pq}\right)\right|
=\sum_{n\in\mathcal N}a_n\frac{k(n)(k(n)-1)}{L^2}.
\tag{B3}
$$

If every discriminant is coprime to $\prod_{p\in\mathcal S}p$, (B3) equals $(1-1/L)\sum_n a_n$. There is no cancellation saving from these support primes, even when the discriminants are nonsquares. As a concrete canonical example, $n=360$ has $h=1$, $(A,B)=(52,85)$, $c=803$, and $D=409$. Both $(409/3)$ and $(409/5)$ equal one. This example verifies the symbol mechanism; with just those two sieve primes, $409>\exp(2)$ prevents applying (B1).

The zero-sensitive formula (B3) holds without the coprimality assumption. Writing $z(n)=L-k(n)$ gives

$$
k(n)(k(n)-1)=L(L-1)-(2L-1)z(n)+z(n)^2.
\tag{B4}
$$

Any saving attributed to zeros must control the actual weighted incidence sufficiently to bound (B3); (B4) records the exact first- and second-moment combination. Dropping zeros, or assigning independent quadratic signs after imposing $p\mid n$, does not estimate this quantity. The common-prime assumption is essential; changing the sieve set separately for each candidate needs a separately justified argument.

### The two canonical unit branches have different zero loci

If $h=0$ and $g=\gcd(A,B)>0$, then for every odd $p\mid n$,

$$
p\mid D\quad\Longleftrightarrow\quad p\mid c
\quad\Longleftrightarrow\quad p\mid g.
\tag{B5}
$$

Indeed, (B2) gives the first equivalence, and the two rows $(2,3)$ and $(4,7)$ have determinant two. Over an odd prime, their simultaneous zero therefore forces both composition coordinates to vanish. Conversely $p\mid g$ makes $n,c,D$ vanish modulo $p$. Here $z(n)$ counts the selected support primes dividing this **same** composition gcd.

For $h=1$, $n=1+g(2a+3b)$ implies $\gcd(n,g)=1$ after writing $(A,B)=g(a,b)$. Nevertheless $p\mid n,D$ can occur when $4a+7b\equiv0\pmod p$. For example $n=30$ has $h=1$, $(A,B)=(4,7)$, $g=1$, and $D=25$: the support prime five divides $D$ while it does not divide $g$. The equivalence $p\mid D\iff p\mid c$ persists, but (B5)'s last equivalence does not transfer to this unit branch.

### The quoted sieve's size restriction

Suppose a candidate sequence additionally has $D(n)\asymp n$, $P^+(n)\asymp\log n$, and all selected sieve primes at most $P^+(n)$. The prime-counting bound then gives

$$
L\le\pi(P^+(n))=O\!\left(\frac{\log n}{\log\log n}\right),
\qquad \exp(L)=n^{o(1)}<D(n)
$$

eventually. Its positive-weight discriminants violate the support cap of (B1). The hypothesis $D(n)\asymp n$ has not been established for actual SA/CA candidates; the fixed-support density example in the [complementary-divisor note](../ArithSums/fibcomplement2026weightedresidues.md) cannot supply it there.

These are paper applications of the cited lemma and the existing finite identity. They diagnose this choice of support primes, preserving zeros and all source weights. They supply neither a square-discriminant exclusion nor the pointwise signed Euler deficit required for Robin; modified sieves and primes outside the candidate support remain separate possibilities.
