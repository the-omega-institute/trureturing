---
bibkey: nicolas1971repartition
authors: Jean-Louis Nicolas
year: 1971
title: Répartition des nombres hautement composés de Ramanujan
doi: 10.4153/cjm-1971-012-6
url: https://doi.org/10.4153/cjm-1971-012-6
claim: The paper introduces a primewise benefit decomposition for the divisor-count objective and quadratic costs for crossing its prime-exponent thresholds; its highly-composite conclusions do not directly apply to arbitrary Robin candidates.
strata_touched: []
license: citation-only
triage: anchor
---

# Répartition des nombres hautement composés de Ramanujan

Primary source: *Canadian Journal of Mathematics* **23** (1971), 116–130,
[publisher full text](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00053037).
The benefit definition and the threshold-cost calculations on printed
pp.117–120 have been inspected, including the page images for pp.119–120.
This note records their statements and application limits, without verifying
the entire paper or supplying Lean evidence.

## Objective and arbitrary-integer decomposition

The paper's $d(n)$ is the number of divisors, conventionally $\tau(n)$;
it is neither $\sigma(n)/n$ nor the FIB increment $b_s(n)$.
For $0<\epsilon<1$, its reference $N=N_\epsilon$ maximizes
$\tau(m)m^{-\epsilon}$ over positive integers. Equations (6)–(8), printed
p.117, give its prime exponents and thresholds

$$
x=2^{1/\epsilon},\qquad
x_k=x^{\log(1+1/k)/\log2},\qquad
a_p=k\ \Longleftrightarrow\ x_{k+1}<p\le x_k.
$$

Proposition 1 and equations (11)–(12), printed p.118, apply to an arbitrary
positive integer $M=(r/t)N$, where $(r,t)=1$ and $t\mid N$. They decompose

$$
\operatorname{ben}_{N,\epsilon}(M)
=\epsilon\log(M/N)-\log\frac{\tau(M)}{\tau(N)}\ge0
$$

into primewise addition and deletion costs, including further nonnegative
terms for repeated changes at one prime. This is a classical benefit
decomposition, not a FIB-specific invariant.

## Quadratic threshold costs and their hypotheses

In “Calcul de bénéfices”, printed pp.119–120, $k$ is fixed and the primes
$Q_1,\ldots,Q_n$ immediately above $x_k$ are added to $N$, while primes
$q_1,\ldots,q_n$ immediately below $x_k$ are deleted. The displayed estimates
are for $n\to\infty$ with $n\le x_k^{5/8}/\log x_k$; their proof also uses
the short-interval prime input to keep each modification in the same
exponent layer. For $W_n=N\prod_iQ_i$, equation (14) reads

$$
\operatorname{ben}(W_n)\gtrsim
\frac{n^2\log2}{x_k\log x}.
$$

For $W'_n=N/\prod_iq_i$, equation (15) gives the corresponding lower scale
and the displayed upper bound

$$
\frac{n^2\log2}{x_k\log x}
\lesssim\operatorname{ben}(W'_n)
\le\frac{n\log2}{x_k^{1-5/8}\log x}.
$$

The symbols here preserve the paper's asymptotic comparison; they are not
finite certificates with specified constants. These calculations already
contain the mechanism “threshold displacement has quadratic benefit cost”.
Renaming it stability, transport, or boundary loss does not make it new.

Proposition 4, printed p.120, makes the stronger assumption that $A$ is
**highly composite** and $N$ is the preceding superior highly composite
integer. If $p_k$ is its largest prime with exponent exactly $k$, then

$$
\pi(p_k)-\pi(x_k)=O((x_k\log x)^{1/2}).
$$

The proof combines the quadratic calculation with Proposition 3's
$\operatorname{ben}(A)=O(1)$. The corollary gives
$p_k-x_k=O(x_k^{5/8})$ when $x_k\to\infty$. Neither that bounded-benefit
hypothesis nor the ordered prime profile follows for an arbitrary integer
in a prescribed residue class.

## Robin interface

[Erdős–Nicolas 1975](erdosnicolas1975repartition.md), §3, Proposition 5,
explicitly transfers the method to $Z(n)=\sigma(n)/n$ with a CA reference,
but its structural conclusion assumes a **superabundant** target between
$N$ and $NP$. The arbitrary-integer benefit definition survives that change
of objective; the highly-composite or superabundant consequences require
their own hypotheses.

For [FIB §§233.5–234](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
the actual host is an integer in a specified window and residue class.
Neither source identifies it as superabundant. A useful application must
therefore retain that host's complete prime exponents, derive any resource
lower bound for those exponents, and compare its benefit with the same
host's Robin support-line excess. The quadratic mechanism is already
classical; a source-preserving quantitative estimate and its required
strict budget are separate obligations.
