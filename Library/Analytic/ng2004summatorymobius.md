---
bibkey: ng2004summatorymobius
authors: Nathan Ng
year: 2004
title: The distribution of the summatory function of the Möbius function
doi: 10.1112/S0024611504014741
url: https://www.cs.uleth.ca/~nathanng/RESEARCH/mobius2b.pdf
claim: The source records the classical unconditional Mertens estimate used here to bound the complete odd-Möbius cutoff remainder; the corrected finite head still requires the signed Robin estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# The classical Mertens input and the complete odd-source cutoff

The published source is Nathan Ng, *Proceedings of the London Mathematical
Society* 89 (2004), issue 2, 361–389,
[DOI](https://doi.org/10.1112/S0024611504014741). The inspected
[author manuscript](https://www.cs.uleth.ca/~nathanng/RESEARCH/mobius2b.pdf)
has 39 pages, title-page date 17 January 2004 and SHA-256
`760cc3f77d657e3ceee8969f479c38c2ffcb9851eda72a220932d179fe4c2bb5`.
Printed p.5 records the unconditional estimate below and attributes it to
Ivić, pp.309–315. Ng's conditional limiting-distribution and negative-moment
results are not used. Neither those proofs nor the complete unconditional
source argument is independently audited or Lean-verified here.

## Reuse of the unconditional input

For the actual $M(t)=\sum_{n\le t}\mu(n)$, the source states

$$
M(t)=O\!\left(t\exp\left[-c\frac{(\log t)^{3/5}}
{(\log\log t)^{1/5}}\right]\right),\qquad c>0.
$$

This is the classical Vinogradov–Korobov scale already cited in
[FIB §390](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
No new Mertens theorem or numerical value of $c$ is supplied. Write
$V(u)=u^{3/5}/(\log u)^{1/5}$ for $u>1$.

The actual odd prefix in
[the companion volume, §453.3](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_PRIME_PREFIX.md)
is $O(t)=\sum_{n\le t,\ n\text{ odd}}\mu(n)$ and already satisfies
$O(t)=\sum_{2^a\le t}M(\lfloor t/2^a\rfloor)$.
Applying the source estimate to $2^a\le\sqrt t$ bounds this part by
$2Ct\exp[-c_1V(\log t)]$, for some fixed $c_1>0$ and sufficiently large
$t$. Indeed $\lfloor t/2^a\rfloor\ge\sqrt t/2$, and the ratio of its
$V$-argument to $V(\log t)$ is eventually bounded below by a fixed
positive constant. The remaining geometric sum is at most $2\sqrt t$,
which is absorbed into the same bound after decreasing $c_1$ if needed.
Consequently there are fixed $C,c_1,t_0>0$ such that

$$
|O(t)|\le Ct e^{-c_1V(\log t)}\qquad(t\ge t_0).
\tag{N1}
$$

This transports a known estimate to the existing dyadic inverse; it does
not assume square-root growth of the actual Möbius sequence.

## Pay the natural odd-atom remainder at a joint cutoff

Retain exactly the companion's actual factorial kernel and weight:

$$
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y,\quad
w(t)=\frac{1+\log t}{t^2\log^2t},\quad
P_x(s)=\int_x^\infty\eta(t/s)w(t)\,dt,\quad
\mathscr D_x(s)=P_x(s)-P_x(2s).
$$

For $x\ge e$, put $\ell=\log x$. FIB (429.2)–(429.3) already give
$-P'_x(s)=G_{\eta,x}(\log s)/s^2$ and
$|\ell G_{\eta,x}(\ell+v)|\le v^2/2+v+12$ for $s>x$, $v=\log(s/x)$.
Reusing that bound at both $s$ and $2s$ gives

$$
|\mathscr D'_x(s)|\le
\frac{36(1+\log(s/x))^2}{\ell s^2},\qquad
|\mathscr D_x(s)|\le
\frac{180(1+\log(s/x))^2}{\ell s}
\quad(s\ge x).
\tag{N2}
$$

The endpoint derivative uses the right extension. For the first inequality,
use $v^2/2+v+12\le12(1+v)^2$, $\log2<1$, and the factor $1/2$ in
$2|P'_x(2s)|$. The second integrates the first from $s$ to infinity,
using the existing $P_x(s)\to0$ and
$\int_s^\infty(1+\log(t/x))^2t^{-2}dt
=[(1+v)^2+2(1+v)+2]/s$.

For integer $N\ge\max(x,t_0)$, define the actual natural-cutoff tail by
the sum below. When $N\ge\lceil8x\rceil$, this is exactly the companion's
complement remainder (CC.29). Abel summation gives

$$
\begin{aligned}
\mathscr R_x(N)
&=\lim_{R\to\infty}
\sum_{\substack{N<m\le R\\m\text{ odd}}}\mu(m)\mathscr D_x(m)\\
&=-O(N)\mathscr D_x(N)
  -\int_N^\infty O(t)\mathscr D'_x(t)\,dt.
\end{aligned}
\tag{N3}
$$

The identity is ordinary Abel summation with the strict lower cutoff
retained. Equations (N1)–(N2) make the integral absolutely convergent and
the upper boundary zero, uniformly with the displayed parameters. They
bound $\ell|\mathscr R_x(N)|$ by a fixed constant times

$$
(1+q)^2e^{-c_1V(q)}
 +\int_q^\infty(1+u)^2e^{-c_1V(u)}\,du,
\qquad q=\log N.
$$

For any fixed $0<d<c_1$, $V$ is eventually increasing and the polynomial
factor is integrable against $e^{-(c_1-d)V(u)}$. Thus fixed $C_d,N_0$
exist, independent of $x,N$, such that

$$
\ell|\mathscr R_x(N)|\le C_d e^{-dV(\log N)}
\qquad(x\ge e,\ N\ge\max(x,N_0)).
\tag{N4}
$$

Choose a fixed $K>0$ with
$d(3/5)^{1/5}K^{3/5}>1/2$ and let, for sufficiently large $x$,

$$
N(x)=\left\lceil\exp\left[K\ell^{5/3}(\log\ell)^{1/3}\right]\right\rceil.
\tag{N5}
$$

The identity
$V(K\ell^{5/3}(\log\ell)^{1/3})
\sim K^{3/5}(3/5)^{1/5}\ell$, monotonicity and (N4) give
$\sqrt x\ell|\mathscr R_x(N(x))|\to0$. The cutoff eventually exceeds
$\lceil8x\rceil$. Companion (CC.30) therefore reads

$$
\sqrt x\ell\left[I_\psi(x)-\mathscr F_x(N(x))
-O(N(x))\mathscr D_x(N(x)+1)\right]\longrightarrow0,
\quad
\mathscr F_x(N)=\sum_{n=1}^NO(n)
 [\mathscr D_x(n)-\mathscr D_x(n+1)].
\tag{N6}
$$

All terms use the full actual odd prefix. The $O(N)$ boundary is not the
prime-panel count; (N6) does not replace it by that count or discard it.

## Remaining signed estimate and comparison with the existing cutoff

The [existing complete rough-row tail bound](alladi1982roughmobius.md#a-critical-scale-bound-for-the-complete-upper-row-tail)
already pays a different complete complement, using a growing primorial
filter and the explicit Lee–Leong input at
$\log H_z=1024(\log z)^2$. It is reused as precedent, not rederived here.
Equations (N3)–(N6) specify the natural odd-atom cutoff and its exact
full-prefix boundary instead. The Vinogradov–Korobov input yields a
smaller asymptotic logarithmic cutoff order, but its constants and starting
point are not numerically certified here. No effective improvement over
that existing bound is claimed.

This is an application of existing summatory and kernel estimates, not a
new analytic theorem or RH criterion. It pays the omitted natural-source
remainder at an expensive superpolynomial sufficient cutoff; necessity or
optimality of that cutoff is not asserted. It supplies no signed
lower bound for the corrected finite head in (N6), no inexpensive
evaluation of that head, no new Robin-safe integer range, and no RH proof.
The finite head's same-source critical lower estimate remains unproved.
The parameter application is a paper derivation, without Lean verification.
