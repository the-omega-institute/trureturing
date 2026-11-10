---
bibkey: karp2012toeplitz
authors: D. Karp
year: 2012
title: Positivity of Toeplitz determinants formed by rising factorial series and properties of related polynomials
doi: 10.48550/arXiv.1203.1482
url: https://arxiv.org/abs/1203.1482v1
claim: Equation (3) defines the rising-factorial Toeplitz polynomial; Conjecture 2 asserts Hurwitz stability for positive shifts and strictly log-concave nonnegative nonzero inputs without internal zeros.
strata_touched:
  - D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Asymptotics/karp2012toeplitz -->
# General-shift rising-factorial Toeplitz stability

## Verified locator

DOI: 10.48550/arXiv.1203.1482

Source: https://arxiv.org/abs/1203.1482v1

The source is arXiv v1, Section 1, equation (3) and Conjecture 2, p. 2.
The journal edition is *Journal of Mathematical Sciences* 193(1),
106–114 (2013), DOI 10.1007/s10958-013-1438-y. Agreement of the
subscription full text with v1 is ASSUMED-UNVERIFIED.

## Source statement

Equation (3), p. 2:

\[
Q^{\alpha,\beta}_{n}(x):=\sum\limits_{k=0}^{n}f_{k}f_{n-k}\binom{n}{k}\left[(x+\alpha)_k(x+\beta)_{n-k}-(x+\alpha+\beta)_k(x)_{n-k}\right].
\]

Conjecture 2, p. 2:

> If $f_k^2>f_{k-1}f_{k+1}$, $k=1,2,\ldots,n-1$, $n\geq{3}$, then
> $Q^{\alpha,\beta}_n(x)$ is Hurwitz stable.

> Recall that a polynomial is called Hurwitz stable if all its zeros
> have negative real part.

The surrounding assumptions are $\alpha,\beta>0$, a nonnegative,
nonzero sequence, and the following zero condition, quoted from p. 1:

> and if $f_N=0$ for some $N>0$ then $f_k=0$ for all
> $k\geq{N}$.

The rising factorial is $(a)_0=1$ and
$(a)_n=a(a+1)\cdots(a+n-1)$. The Lean expression uses
`ascPochhammer ℂ n`, real-to-complex casts, and polynomial composition.
The function $f:\mathbb N\to\mathbb R$ is read only on $0,\ldots,n$.
The finite zero condition is imposed at $1\le N\le n$ and propagates
through $n$. Strict log-concavity is imposed at $1\le k<n$.

## Mathematical boundary

The repository refutation uses $n=20$, $\alpha=\beta=1/t$ and
$f_k=t^{(k-10)^2+(10-k)^2}$ for some $0<t<1$, with natural-number
subtraction in both exponents. It proves failure of negative-real-part
root location. It does not merely exhibit nonreal roots.
The scaled polynomial tends to
$184756((z+1)^{20}-(z(z+2))^{10})$ as $t\to0$.
At $z=1/50+(3/4)i$ the real part of its derivative times the conjugate
of its value is strictly negative. Continuity and the root-sum formula
for the logarithmic derivative yield a root with positive real part.
No explicit finite shift or all-degree family is Lean-established.

The exact experiment is in
[trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments),
commit `88f14279e22537534c13fde03538c32a7583841a`,
`docs/reports/rising-factorial-hurwitz/check.py`, SHA-256
`da6505d120dad430aa9f7b5b54d129fa373400a5e4ea1b654c4806760133fe23`.
The recorded command is
`python3 docs/reports/rising-factorial-hurwitz/check.py` from the experiment
repository root; its reported exit is 0 with `ALL_CHECKS_OK`. Its finite Routh counts are
computed evidence, not Lean proofs.

The literature screen recorded in issue #22349 includes
Zweiman, arXiv:2610.18895v1, Theorem 1.3 and Corollary 1.5:
the positive PF-infinity unit-shift case has a published proof.
That stronger input assumption and restricted shift are unaffected.
Conjecture 1's coefficient positivity is not refuted by this argument.
Global literature completeness and originality are ASSUMED-UNVERIFIED;
the screen has API rate limits and partial citation enumeration.
