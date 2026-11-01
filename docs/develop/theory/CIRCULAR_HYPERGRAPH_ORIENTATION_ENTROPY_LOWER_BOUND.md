## 1. Circular orientations and the entropy bound

**定义 1.1（圆周上的独立均匀随机定向）。** Let $r\ge 3$ and $n>r$ be integers. On $\mathbb Z_n$ let

$$
e_i=\{i,i+1,\ldots,i+r-1\},\qquad i\in\mathbb Z_n,
$$

with all vertex and edge indices interpreted modulo $n$. Independently for each $i$, choose a vertex $Y_i$ uniformly from $e_i$, and put

$$
X=\left|\{Y_i:i\in\mathbb Z_n\}\right|.
$$

For a finite integer-valued random variable, write

$$
H(X)=-\sum_k\Pr(X=k)\log_2\Pr(X=k),
$$

with $0\log_2 0=0$. Define constants depending only on $r$ by

$$
a_r=\left(1-\frac1r\right)^{r-1},\qquad
q_r=a_r(1-a_r),\qquad
b_r=\frac{r-1}{r^2},\qquad
c_r=q_r(1-e^{-2b_r}),
$$

and

$$
K_r=\max\left\{\frac12,\frac12\log_2\frac{\pi}{c_r}\right\}.
$$

Here $0<a_r<1$, so $c_r>0$ and $K_r$ is finite and nonnegative.

**定理 1.2（圆周超图的固定一致度熵下界）。** For every such $r$ and $n$,

$$
H(X)\ge\frac12\log_2\frac nr-K_r.
$$

**证明。**

### 1.2.1. Exposing separated edges

First assume $n\ge 2r$, and set

$$
m=\left\lfloor\frac{n}{2r}\right\rfloor,\qquad
s_j=2rj\quad(0\le j<m).
$$

The successive cyclic gaps between the $s_j$ are at least $2r$: the last gap is $n-2r(m-1)\ge2r$. Consequently the edges $e_{s_j}$ are pairwise disjoint. The sets of edge indices

$$
D_j=\{s_j-r+1,\ldots,s_j-1\}\cup
     \{s_j+1,\ldots,s_j+r-1\}
$$

are also pairwise disjoint, have $2r-2$ elements each, and contain none of the selected indices $s_\ell$. These assertions include the gap crossing zero, by the same cyclic-gap inequality.

Reveal all $Y_i$ with $i\notin\{s_0,\ldots,s_{m-1}\}$; denote this revealed information by $\mathcal F$. Let $O$ be the set of vertices chosen by those revealed edges, let $B=|O|$, and define

$$
k_j=|e_{s_j}\setminus O|,\qquad p_j=\frac{k_j}{r}.
$$

Given $\mathcal F$, the unrevealed choices remain independent and uniform. Since their edges are disjoint, the exact identity is

$$
X=B+\sum_{j=0}^{m-1} Z_j,\qquad
Z_j=\mathbf1_{\{Y_{s_j}\notin O\}},
$$

where, conditionally on $\mathcal F$, the $Z_j$ are independent Bernoulli variables with parameters $p_j$.

Write $u_j=s_j$ and $v_j=s_j+r-1$ for the endpoints of the selected edge. The edges containing $u_j$ have precisely the indices $s_j-r+1,\ldots,s_j$; those containing $v_j$ have precisely the indices $s_j,\ldots,s_j+r-1$. Thus define the $\mathcal F$-measurable event

$$
G_j=
\bigcap_{d=1}^{r-1}\{Y_{s_j-d}\ne u_j\}
\ \cap
\bigcup_{d=1}^{r-1}\{Y_{s_j+d}=v_j\}.
$$

On $G_j$, the vertex $u_j$ is absent from $O$ and the vertex $v_j$ belongs to $O$. In particular,

$$
1\le k_j\le r-1,\qquad p_j(1-p_j)\ge b_r.
$$

The left and right groups of $r-1$ edge choices in $G_j$ are disjoint. The probability that the left group avoids $u_j$ is $a_r$; the probability that the right group chooses $v_j$ at least once is $1-a_r$. Therefore

$$
\Pr(G_j)=q_r.
$$

Moreover, the events $G_0,\ldots,G_{m-1}$ are independent: they depend on the original independent edge choices in the pairwise disjoint sets $D_j$.

### 1.2.2. A point-probability estimate for the actual law

Let $\phi(t)=\mathbb E e^{itX}$ for real $t$. The conditional identity above gives

$$
\mathbb E(e^{itX}\mid\mathcal F)
=e^{itB}\prod_{j=0}^{m-1}(1-p_j+p_je^{it}).
$$

For $0\le p\le1$, putting $s=\sin^2(t/2)$ yields

$$
|1-p+pe^{it}|^2=1-4p(1-p)s,
\qquad
|1-p+pe^{it}|\le e^{-2p(1-p)s}.
$$

Taking absolute values before averaging over $\mathcal F$, and using the independent events $G_j$, gives

$$
\begin{aligned}
|\phi(t)|
&\le \mathbb E\prod_j |1-p_j+p_je^{it}|\\
&\le \mathbb E\exp\left(-2b_rs\sum_j\mathbf1_{G_j}\right)\\
&=(1-q_r+q_re^{-2b_rs})^m\\
&\le \exp\bigl(-mq_r(1-e^{-2b_rs})\bigr)\\
&\le \exp\bigl(-mc_r\sin^2(t/2)\bigr).
\end{aligned}
$$

The last inequality follows from concavity on $[0,1]$ of $s\mapsto1-e^{-2b_rs}$, whose value at zero is zero. No independence between $B$ and the events $G_j$ is needed; its phase has already disappeared in the absolute-value bound.

For an integer $k$, finite Fourier inversion gives

$$
\Pr(X=k)=\frac1{2\pi}\int_{-\pi}^{\pi}e^{-ikt}\phi(t)\,dt.
$$

Indeed, expand the finite sum defining $\phi$ and use that the integral of $e^{i\ell t}$ on this interval is zero for every nonzero integer $\ell$. For $|t|\le\pi$, concavity of sine gives $\sin(|t|/2)\ge |t|/\pi$. Consequently, the Gaussian integral implies

$$
\begin{aligned}
\Pr(X=k)
&\le\frac1{2\pi}\int_{-\pi}^{\pi}
       e^{-mc_rt^2/\pi^2}\,dt\\
&\le\frac1{2\pi}\int_{\mathbb R}
       e^{-mc_rt^2/\pi^2}\,dt
 =\frac{\sqrt\pi}{2\sqrt{mc_r}}.
\end{aligned}
$$

Because $n/(2r)\ge1$, we have $m\ge n/(4r)$. It follows that, for all $n\ge2r$,

$$
\sup_{k\in\mathbb Z}\Pr(X=k)
\le\sqrt{\frac{\pi r}{c_r n}}.
$$

### 1.2.3. Entropy and the finite prefix

For every finite law with largest atom $p_*$,

$$
H(X)=\sum_{k:\Pr(X=k)>0}\Pr(X=k)\log_2\frac1{\Pr(X=k)}
\ge\log_2\frac1{p_*}.
$$

Applying the point-probability estimate, for $n\ge2r$ we obtain

$$
H(X)\ge\frac12\log_2\frac nr-\frac12\log_2\frac\pi{c_r}
\ge\frac12\log_2\frac nr-K_r.
$$

For the remaining integers $r<n<2r$, nonnegativity of Shannon entropy and $K_r\ge1/2$ give

$$
H(X)\ge0\ge\frac12\log_2\frac nr-K_r.
$$

This proves the theorem for every integer $n>r$, with one finite constant for each fixed $r\ge3$.

### 1.2.4. Mathematical sources

The circular hypergraph, the independent uniform edge-choice law, the base-two entropy convention, and the target lower bound are those of Christos Pelekis, *On the Shannon entropy of the number of vertices with zero in-degree in randomly oriented hypergraphs*, arXiv:1808.04166v1, Section 4, Conjecture 4.1, and *Le Matematiche* 74(1), 119–130, DOI [10.4418/2019.74.1.8](https://doi.org/10.4418/2019.74.1.8), Conjecture 4.1 on p.129. The title's complementary count is $n-X$, which has the same entropy.

Finite Fourier inversion, the Gaussian integral, the Bernoulli characteristic-function identity, and the largest-atom entropy inequality are elementary classical inputs. The separated-edge exposure and the independent endpoint events above establish the quantitative estimate for this particular joint orientation law. The conclusion concerns every fixed $r$; it asserts neither a constant uniform in $r$ nor circular entropy maximality.

## 追加锚（本行以下为增补区）
