---
bibkey: diamondford2008generalizedeuler
authors: Harold G. Diamond; Kevin Ford
year: 2008
title: Generalized Euler constants
doi: 10.1017/S0305004108001187
url: https://arxiv.org/abs/math/0703508v2
claim: Proposition 1 and Theorem 1 supply the finite-prime-set formula and prime-prefix infimum reduction; Theorem 2 rules out monotone descent, and Corollary 1 makes the strict prefix floor equivalent to RH. The signed Robin source estimate remains unpaid.
strata_touched: []
license: citation-only
triage: anchor
---

# Sieved harmonic constants and the prime-prefix criterion

The inspected primary is [arXiv:math/0703508v2](https://arxiv.org/pdf/math/0703508v2),
whose title page identifies the version as 7 July 2007. The publisher DOI
and Crossref metadata identify *Mathematical Proceedings of the Cambridge
Philosophical Society* 145 (2008), no. 1, 27–41. The journal text was not
independently compared with this manuscript. All locators below refer to
the inspected version. The source results and proofs are reused; this
note supplies no new sieve theorem, originality claim or Lean certification.

## The finite-prime-set variational result is already known

For a finite set of primes $\mathcal Q$, put

$$
\delta_{\mathcal Q}=\prod_{p\in\mathcal Q}(1-1/p).
$$

The paper defines the constant $\gamma(\mathcal Q)$ by the sieved harmonic
asymptotic

$$
\sum_{\substack{n\le y\\p\nmid n\ (p\in\mathcal Q)}}\frac1n
=\delta_{\mathcal Q}\log y+\gamma(\mathcal Q)+o(1).
$$

Proposition 1, equation (1.2), gives

$$
\gamma(\mathcal Q)
=\delta_{\mathcal Q}
 \left(\gamma+\sum_{p\in\mathcal Q}\frac{\log p}{p-1}\right).
\tag{DF1}
$$

Here $\gamma$ is the ordinary Euler constant. Write $p_r$ for the $r$th
prime, $\mathcal Q_r=\{p_1,\ldots,p_r\}$ and
$\gamma_r=\gamma(\mathcal Q_r)$, including $\gamma_0=\gamma$.
Theorem 1 states that for every finite $\mathcal Q$ there is
$0\le r\le\#\mathcal Q$ with $\gamma(\mathcal Q)\ge\gamma_r$. In particular,

$$
\inf_{\mathcal Q\text{ finite}}\gamma(\mathcal Q)
=\inf_{r\ge0}\gamma_r.
\tag{DF2}
$$

This is an existing reduction from arbitrary finite prime sets to prime
prefixes, not a consequence newly obtained from FIB encoding. Equation
(1.3) gives $\gamma_r\to e^{-\gamma}$. Theorem 2 proves infinitely many
increases and infinitely many decreases. Convergence and prefix
minimization therefore supply no monotone-descent argument.

Theorem 3 proves $\gamma_r>e^{-\gamma}$ for every $r\ge0$ under RH.
Theorem 4 proves infinitely many $\gamma_r<e^{-\gamma}$ if RH fails.
Corollary 1 explicitly states

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\gamma_r>e^{-\gamma}\quad\text{for every }r\ge0.
\tag{DF3}
$$

Thus (DF2), which is unconditional, must be distinguished from the
unpaid floor in (DF3).

## The exact error decomposition retains opposing contributions

Keep inclusive prime-power endpoints and define, for $x\ge2$,

$$
\begin{aligned}
R_{\rm DF}(x)&=\sum_{n\le x}\frac{\Lambda(n)}n-\log x+\gamma,\\
K_{\rm DF}(x)&=\int_x^\infty\frac{R_{\rm DF}(t)}{t\log^2t}\,dt,\\
D(x)&=\sum_{\substack{p\le x,\ a\ge1\\p^a>x}}
                  \frac{\log p}{p^a},\\
\widetilde D(x)&=\sum_{\substack{p\le x,\ a\ge1\\p^a>x}}
                  \frac1{ap^a}.
\end{aligned}
$$

These are the source's $R,H,\Delta,\widetilde\Delta$ respectively;
$R_{\rm DF}$ is distinct from the CA pressure reserve.
Set $r=\pi(x)$, $L=\log x$ and $z=(R_{\rm DF}(x)+D(x))/L$.
Equations (4.2)–(4.4), with the same inclusive cut, give

$$
\log(e^\gamma\gamma_r)
=K_{\rm DF}(x)
 +\left(\frac{D(x)}L-\widetilde D(x)\right)
 +\log(1+z)-z.
\tag{DF4}
$$

The logarithm is defined: $L(1+z)=\gamma+
\sum_{p\le x}\log p/(p-1)>0$. Lemma 4.5 supplies the exact nonnegative
prime-power term

$$
\frac{D(x)}L-\widetilde D(x)
=\sum_{\substack{p\le x,\ a\ge1\\p^a>x}}
 \frac1{p^a}\left(\frac{\log p}L-\frac1a\right)\ge0,
$$

and its asymptotic $2/(\sqrt x\log^2x)+O(1/(\sqrt x\log^3x))$.
The other displayed defect satisfies $\log(1+z)-z\le0$.
Neither sign controls their sum with $K_{\rm DF}$. In particular, the
positive prime-power term alone cannot establish (DF3). The source's
Lemma 4.3 bounds $K_{\rm DF}$ at the required scale **under RH**;
that lemma is not an independent supplier for proving RH.

## Relation to the original Robin tail and its actual source

The original tail is

$$
I_\psi(x)=\int_x^\infty(\psi(t)-t)
              \frac{1+\log t}{t^2\log^2t}\,dt.
$$

Use the [existing full-tail summation identity](../Analytic/bhattacharyamartinsimpson2026weightedprimeerrors.md)
and the source's (4.2). Their parameter correspondence is

$$
I_\psi(x)
=\frac{(\psi(x)-x)/x-R_{\rm DF}(x)}{\log x}
 +K_{\rm DF}(x).
\tag{DF5}
$$

This is an application of the existing summation formulas, not a new
tail identity. No prime powers, endpoint terms or infinite tails are
removed. For the [same actual regular GA1 future-record source](../Arith/caveney2012sacaga.md#retain-the-original-oscillation-exponent-on-the-regular-ga1-source),
take $A=\log N$ and retain its existing endpoint asymptotic. Then (DF5)
reads

$$
\sqrt A\log A\,I_\psi(A)
=-(\sqrt2-1)-\sqrt A\,R_{\rm DF}(A)
 +\sqrt A\log A\,K_{\rm DF}(A)+o(1).
\tag{DF6}
$$

The prime cut matches this same source without a support-index
restriction. Reuse the
[proper-GA1 prime envelope](../Arith/caveney2012sacaga.md#directly-reusable-prime-and-stack-envelopes)
from CNS Theorem 9: every $p\mid N$ satisfies $p\le A$. Conversely,
the [existing GA2 support argument](../Analytic/polak2026finiterobinca.md#application-to-arbitrary-ga2-sources-including-extra-prime-support)
gives $p\mid N$ for every prime $p\le A$; its support argument only
requires $A>1$, as holds here. Therefore
$\operatorname{supp}N=\{p:p\le A\}$ and
$\gamma_{\pi(A)}=\gamma(\operatorname{supp}N)$, including the endpoint
if $A$ is prime. These two existing results identify the finite prime
cut; the DF constant still retains no prime-exponent data.

An eventual fixed lower bound on the right side is still an unpaid
joint estimate at that same source. Neither (DF2) nor the positive
term in (DF4) supplies it; invoking (DF3) or Lemma 4.3 assumes RH.
The full CA reserve remains in the existing relation
$I_\psi(A)=-h_N-R_{\rm CA}(A)$, with
$h_N=\log G(N)-\gamma$. It is not $R_{\rm DF}(A)$.

A FIB address may encode the finite prime set or the integer $N$.
The interval length and branch weights of that encoding have not been
identified with the weighted terms in (DF4)–(DF6). Such a representation
does not pay the missing signed estimate. The variational reduction,
oscillation theorem and RH criterion above remain attributed to
Diamond–Ford; the same-source comparison remains a research obligation.
