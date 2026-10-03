# Uniform lower quantiles and dependent nonnegative series

## 1. Almost-sure accumulation

**Theorem 1.1 (uniform lower-quantile divergence).** Let $(\Omega,\mu)$
be a finite measure space. Let $X_j:\Omega\to[0,\infty]$ be measurable
and let $w_j\in[0,\infty]$ satisfy $\sum_j w_j=\infty$. Suppose that
for every real $\delta>0$ there is a finite real $c>0$ such that
$$
 \mu\{X_j<c w_j\}\le\delta\qquad\text{for every }j.
$$
Then $\sum_j X_j=\infty$ almost everywhere. No independence of the
variables is required.

*Proof.* Write $F=\sum_j X_j$. Fix a finite integer $T$ and suppose
$B=\{F\le T\}$ has measure $p>0$. Choose $\delta=p/2$ and its uniform
constant $c>0$. For each $j$, the intersection
$B\cap\{X_j\ge c w_j\}$ has measure at least $p/2$. Consequently
$$
 \int_B X_j\,d\mu\ge c w_j p/2.
$$
Tonelli's theorem gives
$$
 Tp\ge\int_B F\,d\mu
 =\sum_j\int_B X_j\,d\mu
 \ge (cp/2)\sum_j w_j=\infty,
$$
a contradiction. Thus each $\{F\le T\}$ is null. Their countable union
contains every point where $F$ is finite. $\square$

## 2. Absolute-discrepancy application

For a sequence of integer discrepancies $E_j$ put
$$
 f(x)=\frac{1}{\sqrt{2+|x|}\log(2+|x|)},\qquad
 w_j=\frac{1}{(j+1)\log(j+2)}.
$$
If the marginal bounds $\Pr(|E_j|>C_\delta(j+1)^2)\le\delta$ hold
uniformly over $j$, then
$$
 f(E_j)\ge
 \frac{w_j}{\sqrt{C_\delta+2}
 (2+\log(C_\delta+2)/\log 2)}
$$
off a set of measure at most $\delta$. The divergent deterministic
series $\sum_j w_j$ therefore gives $\sum_j f(E_j)=\infty$ almost
surely by Theorem 1.1.

In an endpoint exploration of actual separable permutations, let $N$
count low-value suffix removals and let $\chi=1$ denote a finite-valued
terminal block. With $t=\sqrt2-1$ and $a=1-1/\sqrt2$, the coupled
endpoint probabilities are
$$
\begin{aligned}
 u_0&=\Pr(N=0,\chi=1)=a,& v_0&=\Pr(N=0,\chi=0)=a(1+t),\\
 u_r&=a t(1+t)t^{2r-2},& v_r&=t u_r\quad(r\ge1).
\end{aligned}
$$
For the actual occupied-shape mass $O$, the predictable cycle hazard is
$$
 q(e)=\sum_{r\ge0}\frac{u_r}{a}
       \mathbb E\,O(e+R_1+\cdots+R_r)\ge O(e).
$$
Thus an occupied-mass bound $O(e)\ge c_0 f(e)$ and the indicated
uniform marginal discrepancy bounds supply almost-sure accumulated
hazard divergence. The probability theorem does not supply those
occupied-mass or marginal hypotheses. Terminal type and removal count
are not independent; their joint atom $u_0$, rather than a product of
marginals, is the term used in the lower bound.

The endpoint decomposition uses the minimum first direct or skew cut
of an actual permutation in $\operatorname{Av}(2413,3142)$; see
Ross G. Pinsky, *The Infinite Limit of Separable Permutations*,
arXiv:1911.05565v2, Section 3. The coupled expressions describe the
alternating endpoint transitions, not the independent primitive
specification printed in that article.
