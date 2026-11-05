# CDSO capacity crossovers and rare phases

## 1. Common laws and the scalar family

**Definition 1.1 (The moving-mean problem).** Let $a\ge7$ be an integer and set

$$
r=a+1,\qquad s=a+2,\qquad
0\le\delta\le1,\qquad \theta=1-\delta,\qquad q=r-\delta=a+\theta.
$$

A law $x$ assigns masses $x_T\ge0$ of total one to the nonempty subsets of $[s]$. Write

$$
K=|T|,\qquad I_i=\mathbf1_{\{i\in T\}},\qquad
y_i=\mathbb E I_i>0,\qquad \mathbb E K=q.
$$

All moments, marginals and conditional laws refer to this one $x$. There is no restriction on the positive-mass cardinalities or on connectedness of the incidence support. In particular zero type masses and arbitrarily small positive marginals are allowed. Define

$$
\begin{aligned}
H(x)&=\mathbb E\left[K^2\sum_{i\in T}y_i^{-2}\right],\\
Z&=\delta a^3+\theta r^3,\\
B&=\frac{a^2r^2}{q}+\frac{(2a+1)\theta r^3}{q^2}
 =\frac{r^2Z}{q^2},\\
d(x)&=H(x)-B,\qquad D_a(\delta)=\inf_x d(x).
\end{aligned}\tag{1.1}
$$

These use the common-array model and the normalization $H=2J_s$, $B=2F_r(q)$ of [*CDSO incidence moments and capacity phases*, Definitions 1.1–1.2](CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md). In particular $Z$ is a reference adjacent-cardinality third moment, not the third moment of an arbitrary admissible law. The graph normalization underlying $J_s$ is the CDSO normalization in A. M. Albalahi, S. Das, A. Ali, J. Barman and A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*, Discrete Math. Lett. 16 (2025), 108–115, §1, p.109, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176).

For $0<t<q$ put

$$
\begin{aligned}
h_\theta(t)&=\frac1t+\frac{a^2r^2}{q-t}
 +\frac{(2a+1)[\theta+(a-1)t]r^3}{(q-t)^2},\\
g_\theta(t)&=h_\theta(t)-\frac1t,\\
\Xi_\theta(t)&=\frac3t-\frac{a(2a+1)tr^3}{(q-t)^2},\\
\Lambda_\theta(t)&=\frac{a(2a+1)tr^3}{(q-t)^2}.
\end{aligned}\tag{1.2}
$$

**Lemma 1.2 (Two actual upper families and one scalar root).** For every parameter of Definition 1.1 there is an admissible law with

$$
H_{\rm dense}=\frac{s^2Z}{q^2},\qquad
H_{\rm dense}-B=\frac{(2r+1)Z}{q^2}=2a^2+O(a),\tag{1.3}
$$

where the constant is absolute and uniform in $\delta$. If $\delta>0$, a second admissible family, indexed by a label $e$, $C=[s]\setminus\{e\}$ and $0<t\le\delta/a$, is

$$
x_{\{e\}}=t,\qquad x_C=\theta+(a-1)t,\qquad
x_{C\setminus\{j\}}=\frac{\delta-at}{r}\quad(j\in C),\qquad
x_T=0\ \text{for all other }T.\tag{1.4}
$$

It has $y_e=t$, $y_i=(q-t)/r$ on $C$, and $H=h_\theta(t)$. Uniformly for $0<t\le1/a$ and $0\le\theta\le1$,

$$
h_\theta(t)-B=\frac1t+2a^3t+O(a^2t).\tag{1.5}
$$

On the larger interval $(0,q)$, $h_\theta$ has a unique minimizer $t_*$, the unique positive root of

$$
(q-t)^3=t^2(M_0+N_0t),\tag{1.6}
$$

where

$$
\begin{aligned}
A_0&=a^2r^2,\qquad E_0=(2a+1)r^3,\\
M_0&=A_0q+E_0[(a-1)q+2\theta],\\
N_0&=E_0(a-1)-A_0=r^2(2a^3-2a-1)>0.
\end{aligned}
$$

Equivalently this root solves

$$
(1+N_0)t^3+(M_0-3q)t^2+3q^2t-q^3=0.\tag{1.7}
$$

**Proof.** For the first law, choose a uniformly distributed $a$-subset of $[s]$ with probability $\delta$, and a uniformly distributed $r$-subset with probability $\theta$. Its mean is $q$, every marginal is $q/s$, and its third moment is $Z$. Thus its energy is $s^2Z/q^2$. Subtraction gives (1.3), since $s^2-r^2=2r+1$, $Z=a^3+O(a^2)$ and $q=a+O(1)$ uniformly.

For (1.4), the masses add to $t+\theta+(a-1)t+\delta-at=1$, and their cardinality mean is

$$
t+r[\theta+(a-1)t]+a(\delta-at)=a+\theta.
$$

The masses are nonnegative in the stated range. A core marginal is $1-t-(\delta-at)/r=(q-t)/r$. Direct counting gives

$$
\mathbb E[K^2I_i]=a^2y_i+(2a+1)[\theta+(a-1)t]\quad(i\in C),
\qquad \mathbb E[K^2I_e]=t,
$$

which proves the energy formula. This extends, in the mean parameter, the actual family supplied by the parent volume's Theorem 10.1; its $\theta=0$ instance is that same family.

For (1.5), let

$$
G_\theta(t)=\frac{a^2r^2}{q-t}
 +\frac{(2a+1)(\theta-t)r^3}{(q-t)^2}.
\tag{1.8}
$$

Then $G_\theta(0)=B$ and
$h_\theta(t)=1/t+G_\theta(t)+\Lambda_\theta(t)$.
On $0\le t\le1/a$, direct differentiation gives $G_\theta'(t)=O(a^2)$, and
$a(2a+1)r^3/(q-t)^2=2a^3+O(a^2)$, with absolute constants. This proves (1.5).

Differentiation on $(0,q)$ gives

$$
\begin{aligned}
h_\theta'(t)&=-\frac1{t^2}+\frac{M_0+N_0t}{(q-t)^3},\\
h_\theta''(t)&=\frac2{t^3}+\frac{2A_0}{(q-t)^3}
 +E_0\left[\frac{4(a-1)}{(q-t)^3}
 +\frac{6[\theta+(a-1)t]}{(q-t)^4}\right]>0.
\end{aligned}\tag{1.9}
$$

The first derivative tends to $-\infty$ at zero and to $+\infty$ at $q$. Strict convexity proves uniqueness and (1.6). Both $M_0,N_0$ are positive, so (1.6) has no root $t\ge q$; this also proves uniqueness among all positive real roots. Expansion of (1.6) yields (1.7). ∎

## 2. Deletion, retained singletons and actual capacity

**Lemma 2.1 (Generalized core remainder with exact nonnegative gaps).** For an admissible law choose any least-marginal label $e$ and define

$$
\begin{gathered}
t=y_e=\min_i y_i,\qquad C=[s]\setminus\{e\},\qquad I=I_e,\qquad L=K-I,\\
m^2=\mathbb E[K^2\mid I=1],\qquad
\mu=\mathbb E[K\mid I=1],\\
\alpha=\mathbb P(T=\{e\}\mid I=1),\qquad \beta=1-\alpha,\qquad
v=m^2-1,\qquad u=v-3\beta.
\end{gathered}\tag{2.1}
$$

Thus $0<t\le q/s<1$, $1\le\mu\le m$, $u\ge0$, and

$$
v\ge3\beta,\qquad v\ge3(\mu-1),\qquad
\boxed{\ \delta\ge t(r-\mu)\ }.\tag{2.2}
$$

For $i\in C$ set

$$
\begin{aligned}
R_i&=\mathbb E[L^2I_i]-a^2y_i-(2a+1)(\theta-t),\\
\rho_i&=(1-I_i)(2a+1)(a-L)+I_i(r-L)(r-L-1),\\
S_i&=R_i-a(2a+1)\alpha t,\qquad
D_i=\mathbb E[I(2L+1)I_i].
\end{aligned}\tag{2.3}
$$

Then $R_i=\mathbb E\rho_i$, $S_i,D_i\ge0$, and

$$
\sum_{i\in C}R_i=\mathbb E Q_a(L),\qquad
Q_a(l)=(r-l)(a-l)(2a+1+l)\ge0\quad(l\in\{0,\ldots,r\}).\tag{2.4}
$$

Let

$$
c_\alpha=(2a+1)[\theta+(a\alpha-1)t],\qquad
f_\alpha(y)=\frac{a^2}{y}+\frac{c_\alpha}{y^2},\qquad
\bar y=\frac{q-t}{r},\qquad
\mathcal G_\alpha=\sum_{i\in C}f_\alpha(y_i)-r f_\alpha(\bar y).
$$

The function $f_\alpha$ is strictly convex on $[t,1]$, so $\mathcal G_\alpha\ge0$, with equality exactly when all core marginals equal $\bar y$. The following identity is exact:

$$
H-h_\theta(t)-\beta\Xi_\theta(t)
=\frac ut+\mathcal G_\alpha+
 \sum_{i\in C}\frac{S_i+D_i}{y_i^2}.\tag{2.5}
$$

In particular, without any lower bound on $\alpha$,

$$
\begin{aligned}
H&\ge h_\theta(t)+\beta\Xi_\theta(t),\\
H&\ge h_\theta(t)+\frac vt-\beta\Lambda_\theta(t)
 \ge h_\theta(t)+v\left(\frac1t-\frac{\Lambda_\theta(t)}3\right).
\end{aligned}\tag{2.6}
$$

**Proof.** The conditional inequalities follow from
$k^2-1\ge3\mathbf1_{\{k\ge2\}}$ and
$k^2-1\ge3(k-1)$ for integers $k\ge1$. On $I=0$ one has $K\le r$, hence
$q\le r(1-t)+t\mu$, proving the capacity inequality in (2.2).

Here $\mathbb E L=q-t=a+\theta-t$. Expanding the integrand of (2.3) gives

$$
\rho_i=L^2I_i-a^2I_i+(2a+1)(a-L),
$$

whose expectation is exactly $R_i$. If $I_i=0$, then $L\le a$; if $I_i=1$, the two consecutive integer factors $r-L,r-L-1$ have nonnegative product. Thus $\rho_i\ge0$, including when $L=0$. On the singleton event $T=\{e\}$ it equals $a(2a+1)$. Consequently

$$
S_i=\mathbb E[\rho_i\mathbf1_{\{T\ne\{e\}\}}]\ge0.
$$

Summing the integrands and using $\sum_{i\in C}I_i=L$ gives (2.4). The product there is nonnegative at every allowed integer, with zeros only at $l=a,r$.

The hub contribution is $m^2/t$. On core incidences $K^2=L^2+I(2L+1)$, so the exact energy decomposition is

$$
H=\frac{m^2}{t}+\sum_{i\in C}f_\alpha(y_i)
 +\sum_{i\in C}\frac{S_i+D_i}{y_i^2}.\tag{2.7}
$$

As $c_\alpha\ge-(2a+1)t$, for $y\ge t$ one has

$$
f_\alpha''(y)=\frac{2(a^2y+3c_\alpha)}{y^4}
\ge\frac{2(a^2-6a-3)t}{y^4}>0.\tag{2.8}
$$

The finite Jensen inequality therefore gives the asserted gap and its strict equality condition. This is the usual convex-combination inequality, as in S. Boyd and L. Vandenberghe, *Convex Optimization*, §3.1.8, pp.77–78 ([author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)); it is applied to the actual core marginals, without averaging laws or assuming convexity of $H$.

Substitute $m^2=1+3\beta+u$ and $\alpha=1-\beta$ in (2.7). The constant terms are $h_\theta(t)$, and the coefficient of $\beta$ is $\Xi_\theta(t)$. This proves (2.5). Alternatively retain $v=m^2-1$ before replacing $\beta\le v/3$; this proves both lines of (2.6). The parent volume's Lemma 12.3 supplies the endpoint residual pattern. The present calculation uses $\mathbb E L=a+\theta-t$ explicitly and proves the moving-mean identity, rather than assuming that endpoint hypothesis. ∎

**Lemma 2.2 (Uniform conditional-moment certificates).** There is an absolute constant $C_0$ such that, simultaneously for all parameters and all laws of Definition 1.1, the notation of Lemma 2.1 satisfies

$$
\begin{aligned}
d&\ge\frac{m^2}{t}
 +t\left(\mathbb E[P_a(K)\mid I=1]-\mathcal A_\theta(t)\right),\\
d&\ge\frac{m^2}{t}
 +t\left(C_a-E_a(m-1)-\mathcal A_\theta(t)\right),\\
m^2&\le td+C_0a^2t^2,
\end{aligned}\tag{2.9}
$$

where

$$
\begin{gathered}
P_a(k)=(a+2-k)(a+1-k)(2a+k),\\
C_a=a(a+1)(2a+1),\qquad E_a=3a^2+3a+1,\\
\mathcal A_\theta(t)=\frac{B-G_\theta(t)}t,\qquad
|\mathcal A_\theta(t)|\le C_0a^2.
\end{gathered}\tag{2.10}
$$

These bounds hold for every $0<t\le q/s$ occurring as a least marginal, not just in the feasible range of (1.4).

**Proof.** Before removing the singleton part from the residual, (2.7) reads

$$
H=\frac{m^2}{t}+\sum_{i\in C}
 \left[\frac{a^2}{y_i}+\frac{(2a+1)(\theta-t)}{y_i^2}
       +\frac{R_i+D_i}{y_i^2}\right].
$$

The scalar function in the first two terms is strictly convex for $y\ge t$, by the same calculation as (2.8). Since $0<y_i\le1$, $R_i/y_i^2\ge R_i$. Also $Q_a(L)=P_a(K)$ on $I=1$, and $Q_a(L)\ge0$ on the remaining events. Jensen and (2.4) give

$$
H\ge\frac{m^2}{t}+G_\theta(t)+t\mathbb E[P_a(K)\mid I=1].
$$

For $0\le v\le t<1$, $q-v\ge a-1$. Direct differentiation of (1.8) gives the three terms

$$
G_\theta'(v)=\frac{a^2r^2}{(q-v)^2}
 -\frac{(2a+1)r^3}{(q-v)^2}
 +\frac{2(2a+1)(\theta-v)r^3}{(q-v)^3}.
$$

Their absolute sum is at most $C_0a^2$ with an absolute constant. As $G_\theta(0)=B$, the bound on $\mathcal A_\theta$ follows. The integer polynomial $P_a$ is nonnegative for $1\le k\le s$, and

$$
P_a(k)=C_a-E_a(k-1)+(k-1)^3.
$$

Take its conditional expectation and use $\mu\le m$. This gives the second certificate. Discarding $P_a\ge0$ from the first one gives the last line of (2.9). ∎

## 3. An absolute uniform capacity envelope

**Lemma 3.1 (A full-label certificate for the dense branch).** Put $n=s$, $b=r$, and define, for every label,

$$
\begin{aligned}
\widehat R_i&=\mathbb E[K^2I_i]-b^2y_i+(2b+1)\delta,\\
\widehat\rho_i&=(1-I_i)(2b+1)(b-K)+I_i(n-K)(n-K-1),\\
t_{\rm conv}&=\frac{3(2b+1)\delta}{b^2}.
\end{aligned}\tag{3.1}
$$

Then $\widehat R_i=\mathbb E\widehat\rho_i\ge0$. If $t=\min_i y_i\ge t_{\rm conv}$, then

$$
H\ge H_{\rm dense}
 -6b\delta\left(\frac{n^2}{q^2}-1\right)
 =H_{\rm dense}-O(\delta),\tag{3.2}
$$

with an absolute constant. At $\delta=0$ the exact global minimum is $H_{\rm dense}=rs^2$, attained only by the uniform law on the $r$-subsets of $[s]$.

**Proof.** Expansion of the integrand gives
$\widehat\rho_i=K^2I_i-b^2I_i+(2b+1)(b-K)$.
Its expectation is $\widehat R_i$ since $\mathbb E K=b-\delta$. If $i$ is absent, $K\le b$, and if it is present the two consecutive integer factors have nonnegative product. Thus each integrand is nonnegative. Their sum is

$$
\sum_i\widehat\rho_i=Q_b(K),\qquad
Q_b(k)=(n-k)(b-k)(2b+1+k).
$$

For $z=b-k\in\{-1,0,\ldots,b-1\}$,

$$
Q_b(k)-6b(b-k)
=z(z+1)(3b+1-z)-6bz
=z(z-1)(3b-z-1)\ge0.\tag{3.3}
$$

Indeed at $z=-1$ the value is $6b$, at $z=0,1$ it is zero, and for $2\le z\le b-1$ all factors are positive. Hence $\sum_i\widehat R_i\ge6b\delta$.

Let $f(y)=b^2/y-(2b+1)\delta/y^2$. On $y\ge t_{\rm conv}$,

$$
f''(y)=\frac{2[b^2y-3(2b+1)\delta]}{y^4}\ge0.
$$

Thus the actual identity $H=\sum_i f(y_i)+\sum_i\widehat R_i/y_i^2$, Jensen, and $y_i\le1$ give

$$
H\ge\frac{b^2n^2}{q}-\frac{(2b+1)\delta n^3}{q^2}+6b\delta.
$$

Since $a=b-1$, one has
$Z=b^3-(3b^2-3b+1)\delta$ and
$b^2q-(2b+1)\delta n=Z-6b\delta$.
This proves (3.2). Moreover $n^2/q^2-1=O(1/a)$ uniformly, making the error $O(\delta)$.

At $\delta=0$, $f$ is strictly convex and the error is zero. Equality forces all marginals equal $b/n$ and $\mathbb E Q_b(K)=0$. The only allowed zeros of $Q_b$ are $K=b,n$; their mean $b$ forces $K=b$ almost surely. A $b$-subset omits a single label, and its omitted-label probabilities are then $1/n$. This is precisely the stated uniform law. ∎

**Definition 3.2 (Truncated scalar profile).** For $\delta>0$ set

$$
S_a(\delta)=\min_{0<t\le\delta/a}\left(\frac1t+2a^3t\right),
\qquad S_a(0)=+\infty,\qquad
W_a(\delta)=\min\{2a^2,S_a(\delta)\}.
\tag{3.4}
$$

Explicitly,

$$
S_a(\delta)=
\begin{cases}
a/\delta+2a^2\delta,&0<\delta\le1/\sqrt{2a},\\
2\sqrt2\,a^{3/2},&\delta\ge1/\sqrt{2a}.
\end{cases}\tag{3.5}
$$

**Lemma 3.3 (Uniform bounded conditional moment on the rare branch).** For each fixed $M>0$ there are constants $A_M,C_M$, depending only on $M$, such that for every $a\ge A_M$, $\delta\in[0,1]$, and actual law with

$$
t<t_{\rm conv},\qquad d\le M W_a(\delta),\tag{3.6}
$$

one has $m\le C_M$ and

$$
d\ge\frac{m^2}{t}+(2a^3-C_Ma^2)t,\qquad
\delta\ge a(1-C_M/a)t.\tag{3.7}
$$

The constants are independent of $\delta$, the support, all positive marginal sizes, and the choice of a least marginal.

**Proof.** The rare branch is empty when $\delta=0$. Otherwise (3.1) gives $t\le C\delta/a$ with an absolute constant. By Lemma 2.2,

$$
m^2\le td+C_0a^2t^2.\tag{3.8}
$$

If $0<\delta\le a^{-1/2}$, use
$W_a(\delta)\le a/\delta+2a^2\delta$, which follows either by (3.5) or by evaluating the scalar objective at $\delta/a$. Then

$$
m^2\le C_M(1+a\delta^2+\delta^2)=O_M(1).
$$

If $\delta\ge a^{-1/2}$, then $W_a(\delta)\le2\sqrt2\,a^{3/2}$ and (3.8) first gives

$$
m^2\le C_M(\delta\sqrt a+\delta^2)=O_M(\sqrt a),\qquad
m=O_M(a^{1/4}).
$$

The coefficient in the second certificate of (2.9) is therefore

$$
C_a-E_a(m-1)-\mathcal A_\theta(t)
=2a^3+O_M(a^{9/4})\ge a^3
$$

for all sufficiently large $a$ depending only on $M$. Thus
$d\ge m^2/t+a^3t$. Since $d=O_M(a^{3/2})$ in this case, it follows that $t=O_M(a^{-3/2})$ and $m^2\le dt=O_M(1)$. In both cases $m=O_M(1)$. Substitution back in the same certificate makes its coefficient $2a^3+O_M(a^2)$, proving the first inequality in (3.7). The actual capacity (2.2) and $\mu\le m$ give
$r-\mu=a+1-\mu\ge a-C_M$, proving the second. ∎

**Theorem 3.4 (Uniform relative error of order $1/a$).** There are absolute constants $A,C>0$ such that for every integer $a\ge A$ and every $\delta\in[0,1]$,

$$
\boxed{\quad
(1-C/a)W_a(\delta)\le D_a(\delta)\le(1+C/a)W_a(\delta).
\quad}\tag{3.9}
$$

In particular $D_a(\delta)/W_a(\delta)\to1$ uniformly on the entire closed interval of $\delta$.

**Proof.** The dense family gives
$d\le(1+C/a)2a^2$ by (1.3). For $\delta>0$, choose (1.4) with

$$
t=\min\left\{\frac\delta a,\frac1{\sqrt2\,a^{3/2}}\right\}.
$$

By (1.5), its gap is at most $(1+C/a)S_a(\delta)$: the error $Ca^2t$ is at most $C/(2a)$ times $2a^3t$. Taking the better of the two actual laws proves the upper bound, including $\delta=0$ via the first law.

For the lower bound consider any admissible law. If $d>2W_a(\delta)$, the desired lower bound already holds. Otherwise fix $M=2$ in Lemma 3.3. If $t\ge t_{\rm conv}$, (3.2) and (1.3) give

$$
d\ge2a^2-Ca\ge(1-C'/a)W_a(\delta).
$$

If $t<t_{\rm conv}$, Lemma 3.3 supplies a single absolute $C_1$ such that, for $\rho=1-C_1/a>0$,

$$
d\ge\frac1t+2\rho a^3t,\qquad
\delta\ge a\rho t.
$$

The same $\rho$ can be used by increasing $C_1$ to cover both inequalities. Set $u=\rho t$. Then $0<u\le\delta/a$ and

$$
d\ge\frac\rho u+2a^3u
\ge\rho\left(\frac1u+2a^3u\right)
\ge\rho S_a(\delta)\ge\rho W_a(\delta).
$$

This proves a pointwise lower bound for every law; taking its infimum proves (3.9). No independently optimized marginal or conditional law is combined with another realization. ∎

**Corollary 3.5 (Low-energy localization on the whole moving-mean domain).** For each fixed $M>0$, uniformly over every $\theta\in[0,1]$, every law with $d\le Ma^{3/2}$, and every choice of a least marginal, sufficiently large $a$ depending only on $M$ satisfies

$$
\frac1M\le\tau:=a^{3/2}t\le M,\qquad 1\le m\le M,
\qquad
\frac d{a^{3/2}}\ge\frac{m^2}{\tau}+2\tau-O_M(a^{-1}),
\tag{3.10}
$$

and

$$
\sqrt a\,\delta\ge\tau\left(1+\frac1a-\frac\mu a\right).
\tag{3.11}
$$

**Proof.** For large $a$, $W_a(\delta)\ge2\sqrt2\,a^{3/2}$, so this sublevel satisfies the energy restriction of Lemma 3.3 with a constant depending only on $M$. The dense branch would give $d\ge2a^2-Ca>Ma^{3/2}$ by Lemma 3.1, a contradiction. Thus Lemma 3.3 applies on the rare branch. Its coefficient is at least $a^3$ for large $a$, so
$d\ge m^2/t+a^3t$. Each term is nonnegative. Hence $1/t\le d$, $a^3t\le d$ and $m^2\le dt$, proving the first three bounds in (3.10). Substituting the sharper coefficient $2a^3-O_M(a^2)$ proves its last inequality. Multiplication of the exact capacity (2.2) by $\sqrt a$ gives (3.11). ∎

## 4. Eventual exact classification away from the upper endpoint

**Theorem 4.1 (Uniform interior minimum and all equality laws).** For every fixed $0<\delta_0\le1$ there is an integer $A(\delta_0)\ge7$ such that, simultaneously for all integers $a\ge A(\delta_0)$ and all $\theta\in[0,1-\delta_0]$, the minimizer $t_*$ of Lemma 1.2 satisfies

$$
0<t_*<\frac{1-\theta}{a},\qquad
\min_x H(x)=h_\theta(t_*).\tag{4.1}
$$

A law attains this minimum if and only if it is (1.4) at $t=t_*$, for some choice of $e$. Its least-marginal label is unique. Its positive-mass types are exactly $\{e\}$, $C$, and $C\setminus\{j\}$ for $j\in C$, and its incidence support has exactly the two components $\{e\}$ and $C$. There is no restriction to such supports in the minimization. The case $\theta=0$ is the endpoint classification of the parent volume's Theorem 12.5; (4.1) extends its mean range with one threshold uniform on each stated interval.

**Proof.** Put $t_0=1/(\sqrt2\,a^{3/2})$. For large $a$ depending only on $\delta_0$, $t_0\le\delta_0/a\le(1-\theta)/a$; this is the first use of the interior restriction. Thus (1.4) supplies an actual trial law of energy $h_\theta(t_0)$. By (1.5), uniformly in the whole interval of $\theta$,

$$
h_\theta(t_0)-B=2\sqrt2\,a^{3/2}+O(a^{1/2}).\tag{4.2}
$$

Consider the entire trial sublevel

$$
\mathcal U_{a,\theta}=\{x:H(x)\le h_\theta(t_0)+1\}.
$$

For every law in this sublevel, $d\le4a^{3/2}$ eventually, with a threshold independent of the law and of $\theta$. Corollary 3.5 with the fixed value $M=4$ gives $1/4\le\tau\le4$ and

$$
\frac{m^2-1}{\tau}
+\left(\frac1\tau+2\tau-2\sqrt2\right)\le O(a^{-1}).\tag{4.3}
$$

The two terms on the left are nonnegative, and

$$
\frac1\tau+2\tau-2\sqrt2
=\frac{2(\tau-1/\sqrt2)^2}{\tau}.
$$

Therefore, uniformly on this entire sublevel,

$$
m^2-1=O(a^{-1}),\qquad
\tau=\frac1{\sqrt2}+O(a^{-1/2}),\qquad
\beta=O(a^{-1}),\qquad
t\Xi_\theta(t)=2+O(a^{-1/2})>0.\tag{4.4}
$$

For the last assertion substitute $t=\tau a^{-3/2}$ in (1.2); the coefficient multiplying $\tau^2$ in $3-t\Xi_\theta(t)$ is $2+O(a^{-1})$. All thresholds here depend only on the fixed trial bound, apart from the feasibility threshold depending on $\delta_0$.

The scalar derivative also gives, for any fixed positive $w$,

$$
\frac{h_\theta'(w a^{-3/2})}{a^3}
=-\frac1{w^2}+2+O_w(a^{-1}),\tag{4.5}
$$

uniformly for $\theta\in[0,1]$. Strict convexity brackets $a^{3/2}t_*$ between any fixed values on opposite sides of $1/\sqrt2$, once $a$ is large. Hence $a^{3/2}t_*\to1/\sqrt2$ uniformly in $\theta$. In particular $t_*<(1-\theta)/a$ uniformly on the specified interior interval. This is the second use of $\delta_0$, and makes (1.4) at $t_*$ admissible.

For an arbitrary law outside $\mathcal U_{a,\theta}$, one has
$H>h_\theta(t_0)+1>h_\theta(t_*)$. For a law inside, (2.5) and (4.4) imply

$$
H\ge h_\theta(t)+\beta\Xi_\theta(t)\ge h_\theta(t_*).
$$

The feasible family at $t_*$ attains this bound. This proves the global minimum without assuming that a minimizing law has already been found.

If equality holds, all the terms in

$$
\begin{aligned}
H-h_\theta(t_*)={}&h_\theta(t)-h_\theta(t_*)
 +\beta\Xi_\theta(t)+\frac ut+\mathcal G_\alpha
 +\sum_{i\in C}\frac{S_i+D_i}{y_i^2}
\end{aligned}
$$

are nonnegative. Strict scalar convexity gives $t=t_*$; positivity of $\Xi_\theta(t)$ gives $\beta=0$. Thus $e$ occurs only as the singleton $\{e\}$. Equality in Jensen makes every core marginal $(q-t)/r$, and every $S_i$ is zero. Summing their residual representations gives

$$
0=\mathbb E\left[Q_a(L)\mathbf1_{\{T\ne\{e\}\}}\right].
$$

On this remaining event $I=0$ and $L=K\ge1$. The only integer zeros of $Q_a$ there are $a,r$. Thus the remaining positive masses lie at $C$ and $C\setminus\{j\}$. Write these masses as $z,b_j$. Normalization and the mean imply

$$
z+\sum_jb_j=1-t,\qquad rz+a\sum_jb_j=q-t,
$$

so $z=\theta+(a-1)t$ and $\sum_jb_j=\delta-at$. The marginal equality $1-t-b_j=(q-t)/r$ forces $b_j=(\delta-at)/r$ for each $j$. These are exactly (1.4). Conversely Lemma 1.2 proves their equality. Feasibility is strict at $t_*$, so every displayed mass is positive. Finally $t_*=O(a^{-3/2})$ while all core marginals tend uniformly to one. This proves uniqueness of the rare label and the claimed support components. ∎

**Theorem 4.2 (Interior second coefficient and root expansion).** For each fixed $0<\delta_0\le1$, uniformly for $\theta\in[0,1-\delta_0]$ as $a\to\infty$,

$$
\begin{aligned}
D_a(1-\theta)
&=2\sqrt2\,a^{3/2}+\sqrt2(3-2\theta)a^{1/2}
 +O_{\delta_0}(a^{-1/2}),\\
t_*&=\frac1{\sqrt2\,a^{3/2}}
 \left[1-\frac{3-2\theta}{2a}+O_{\delta_0}(a^{-2})\right].
\end{aligned}\tag{4.6}
$$

Consequently the minimum of $J_s-F_r(q)$ is

$$
\sqrt2\,a^{3/2}+\frac{3-2\theta}{\sqrt2}a^{1/2}
 +O_{\delta_0}(a^{-1/2}).\tag{4.7}
$$

At $\theta=0$ these coefficients are those of the stronger endpoint expansion in the parent volume's Theorem 12.6.

**Proof.** Let $c_1=g_\theta'(0)=M_0/q^3$. Expansion of its rational formula, uniformly on $0\le\theta\le1$, gives

$$
c_1=2a^3+(6-4\theta)a^2+O(a).\tag{4.8}
$$

For example, its exact numerator after placing it over $q^3$ is

$$
c_1=\frac{r^2}{(a+\theta)^3}
\left[2a^4+2a^3\theta+2a^3+6a^2\theta-2a^2+4a\theta-a+\theta\right].
$$

On $0\le t\le C a^{-3/2}$, differentiation of (1.2) gives $g_\theta''(t)=O_C(a^2)$ uniformly. Therefore

$$
\begin{aligned}
h_\theta(t)-B&=\frac1t+c_1t+O_C(a^2t^2),\\
h_\theta'(t)&=-\frac1{t^2}+c_1+O_C(a^2t).
\end{aligned}\tag{4.9}
$$

The function $g_\theta$ is convex, so its tangent at zero yields
$h_\theta(t)-B\ge1/t+c_1t\ge2\sqrt{c_1}$ for every $0<t<q$. At $t=c_1^{-1/2}$, (4.9) gives the reverse bound with error $O(a^{-1})$. Hence

$$
h_\theta(t_*)-B=2\sqrt{c_1}+O(a^{-1}).\tag{4.10}
$$

Also $t_*=\Theta(a^{-3/2})$ by (4.5). The stationary equation and the second line of (4.9) give

$$
t_*=c_1^{-1/2}[1+O(a^{-5/2})].
$$

Expanding the square root and inverse square root of (4.8) proves (4.6), using Theorem 4.1 to identify the global minimum. Division by two proves (4.7). The analytic error bounds above are uniform even on $\theta\in[0,1]$; the interior restriction is needed to identify the scalar minimum with an admissible law. ∎

## 5. The two principal crossover scales

**Theorem 5.1 (The primary crossover and its necessary rare structure).** Define

$$
F(c)=\min_{0<\tau\le c}\left(\frac1\tau+2\tau\right)
=\begin{cases}
1/c+2c,&0<c\le1/\sqrt2,\\
2\sqrt2,&c\ge1/\sqrt2.
\end{cases}\tag{5.1}
$$

If $\sqrt a\,\delta_a\to c\in(0,\infty)$, then

$$
\frac{D_a(\delta_a)}{a^{3/2}}\longrightarrow F(c).\tag{5.2}
$$

For every fixed $0<c_-\le c_+<\infty$, uniformly for $c_-\le\sqrt a\,\delta\le c_+$,

$$
D_a(\delta)=a^{3/2}F(\sqrt a\,\delta)+O_{c_-,c_+}(a^{1/2}).\tag{5.3}
$$

If actual laws $x_a$ in the regime of (5.2) satisfy
$d(x_a)/a^{3/2}\to F(c)$, then for every choice of a least-marginal label $e_a$,

$$
a^{3/2}y_{e_a}\longrightarrow\min\{c,1/\sqrt2\},\qquad
\mathbb E[K^2\mid e_a\in T]\longrightarrow1,\qquad
\mathbb P(T=\{e_a\}\mid e_a\in T)\longrightarrow1.
\tag{5.4}
$$

All other marginals tend uniformly to one, and $e_a$ is eventually unique.

**Proof.** The explicit scalar formula gives
$S_a(\delta)=a^{3/2}F(\sqrt a\,\delta)$. On any of the stated compact intervals this is $O(a^{3/2})$, and is less than $2a^2$ eventually. Thus $W_a=S_a$ there. The relative error $O(1/a)$ of Theorem 3.4 proves (5.3) and (5.2).

For the structure, Corollary 3.5 applies to $x_a$ with one fixed $M$. Thus $\tau=a^{3/2}t$ stays in a compact subinterval of $(0,\infty)$ and $m$ is bounded. Equation (3.11) implies that every limit point of $\tau$ is at most $c$. Along any subsequence where $\tau\to\tau_*$ and $m^2\to m_*^2$, (3.10) gives

$$
F(c)\ge\frac{m_*^2}{\tau_*}+2\tau_*
\ge\frac1{\tau_*}+2\tau_*\ge F(c).
$$

The constrained scalar minimum has the unique minimizing point $\min\{c,1/\sqrt2\}$. Thus $\tau_*$ is that point and $m_*^2=1$. Every subsequence has the same possible limits, proving the first two conclusions in (5.4); $3\beta\le m^2-1$ proves the third. Finally

$$
\sum_{i\ne e_a}(1-y_i)=r-(q-t)=\delta_a+t\longrightarrow0.
\tag{5.5}
$$

So all the other marginals tend uniformly to one, whereas $t\to0$. This proves eventual uniqueness. ∎

**Theorem 5.2 (The secondary crossover and the intermediate window).** With the convention $1/0=+\infty$, if $a\delta_a\to\lambda\in[0,\infty)$, then

$$
\frac{D_a(\delta_a)}{a^2}\longrightarrow\min\{2,1/\lambda\}.
\tag{5.6}
$$

If instead $a\delta_a\to\infty$ and $\sqrt a\,\delta_a\to0$, then

$$
D_a(\delta_a)\sim\frac a{\delta_a}.\tag{5.7}
$$

These limits are attained asymptotically by the actual laws of Lemma 1.2, choosing the better family when both are defined.

**Proof.** If $a\delta_a$ has a finite limit and $\delta_a>0$, eventually the first line of (3.5) applies, and

$$
\frac{S_a(\delta_a)}{a^2}=\frac1{a\delta_a}+2\delta_a.
$$

Taking the minimum with two and using Theorem 3.4 proves (5.6) for $\lambda>0$ and for positive $\delta_a$ with $a\delta_a\to0$. The terms with $\delta_a=0$ obey the same limit by the exact value in Lemma 3.1. In the intermediate window,
$2a^2\delta_a/(a/\delta_a)=2a\delta_a^2\to0$ and
$(a/\delta_a)/(2a^2)=1/(2a\delta_a)\to0$.
Thus $W_a(\delta_a)\sim a/\delta_a$, and (3.9) proves (5.7). The upper laws used to prove (3.9) were actual laws throughout. ∎

**Theorem 5.3 (Necessary near-optimal branches at the secondary scale).** Suppose $a\delta_a\to\lambda\in[0,\infty)$ and actual laws satisfy

$$
\frac{d(x_a)}{a^2}\longrightarrow\min\{2,1/\lambda\}.
\tag{5.8}
$$

Let $t_a=\min_i y_i$, and on every term choose any least-marginal label $e_a$.

If $0\le\lambda<1/2$, then $t_a\to1$.

If $\lambda>1/2$, then

$$
t_a\to0,\qquad a^2t_a\to\lambda,\qquad
\mathbb E[K^2\mid e_a\in T]\to1,\qquad
\mathbb P(T=\{e_a\}\mid e_a\in T)\to1.\tag{5.9}
$$

In this case the other marginals tend uniformly to one and $e_a$ is eventually unique.

If $\lambda=1/2$, then $\operatorname{dist}(t_a,\{0,1\})\to0$. Every subsequence has a further subsequence on which either $t_a\to1$, or $t_a\to0$ and (5.9) holds with $\lambda=1/2$. Both branches occur for actual asymptotically optimal families. A sequence need not choose the same branch at every index.

**Proof.** Throughout this proof $\delta_a=O(1/a)$, so direct expansion gives

$$
B-q^3=O(a),\qquad B=r^3+O(a),\qquad q^3=r^3+O(a).
\tag{5.10}
$$

The energy assumption implies $H\le B+Ma^2$ for one constant $M$. Write $\sigma^2=\operatorname{Var}(K)$. The exact identity

$$
\mathbb E K^3-q^3
=\mathbb E[(K-q)^2(K+2q)]\ge(2q+1)\sigma^2
\tag{5.11}
$$

and $H\ge\mathbb E K^3$ show that $\sigma^2=O(a)$ and $\mathbb E(K-a)^2=O(a)$.

Pass to an arbitrary subsequence along which $t_a\to t_0\in[0,1]$. First suppose $t_0>0$. Put $V_T=\sum_{i\in T}(y_i^{-2}-1)$. Since
$\sum_i(1-y_i)=s-q=1+\delta_a$, one has

$$
0\le V_T\le\frac{2(1+\delta_a)}{t_a^2}=O(1),
\qquad
\mathbb E V_T=2(1+\delta_a)+\sum_i\frac{(1-y_i)^2}{y_i}.
\tag{5.12}
$$

Also $\mathbb E|K^2-a^2|\le(2a+2)\sqrt{\mathbb E(K-a)^2}=O(a^{3/2})$. The exact energy decomposition then yields

$$
\begin{aligned}
H&=\mathbb E K^3+\mathbb E[K^2V_T]\\
&\ge q^3+a^2\mathbb E V_T-O(a^{3/2}),\\
\frac d{a^2}&\ge2+\sum_i\frac{(1-y_i)^2}{y_i}-o(1).
\end{aligned}\tag{5.13}
$$

Thus this branch costs at least two. If its limiting cost equals two, the nonnegative sum tends to zero; its term at a least marginal forces $t_a\to1$.

Now suppose $t_0=0$. Keeping the hub's excess over the unit core weights gives the pointwise-integrated estimate

$$
H\ge\mathbb E K^3+m^2(1/t_a-t_a)
\ge q^3+m^2(1/t_a-t_a).\tag{5.14}
$$

Indeed the hub contributes $\mathbb E[K^2I_e]/t_a^2=m^2/t_a$, whereas replacing that weight by one would give $t_am^2$. By the energy upper bound and (5.10),
$m^2/t_a=O(a^2)$ since $t_a\to0$. In particular $m/a=O(\sqrt{t_a})\to0$. The actual capacity (2.2) implies

$$
a^2t_a\le a\delta_a(1+o(1)).\tag{5.15}
$$

For $\lambda=0$ this contradicts $m^2/t_a=O(a^2)$ and $m^2\ge1$, so this branch is impossible. For $\lambda>0$, (5.14)–(5.15) imply its limiting cost is at least $1/\lambda$. If the limiting cost is exactly $1/\lambda$, the same inequalities force $a^2t_a\to\lambda$ and $m^2\to1$: the former has limsup at most $\lambda$, and $m^2/(a^2t_a)$ has limsup at most $1/\lambda$, while $m^2\ge1$. Then $\beta\to0$. Equation (5.5) proves the other-marginal statement and eventual uniqueness.

For $\lambda<1/2$ a branch $t_a\to0$ would cost strictly more than two; for $\lambda>1/2$ a positive-limit branch would cost strictly more than $1/\lambda$. This proves the first two cases. At $\lambda=1/2$, every positive-limit branch has cost two and hence limit $t_0=1$ by (5.13); a zero-limit branch has the structure just proved. Compactness of $[0,1]$ gives the stated distance and subsequence assertions. The dense family has $t_a=q/s\to1$, while (1.4) at $t_a=\delta_a/a$ has $a^2t_a\to1/2$; both have limiting cost two by their explicit energies. ∎

## 6. Global competition in the finite secondary window

**Theorem 6.1 (Two-family squeeze with additive error $O(1/a)$).** Fix $0<\lambda_-\le\lambda_+<\infty$. There are $A,C$, depending only on this interval, such that for all integers $a\ge A$ and $\delta=\lambda/a$ with $\lambda\in[\lambda_-,\lambda_+]$, put

$$
T=\frac\delta a=\frac\lambda{a^2},\qquad
H_{\rm rare}=\frac1T+\frac{r^3}{1-T}.
\tag{6.1}
$$

Then

$$
\boxed{\quad
\min\{H_{\rm dense},H_{\rm rare}\}-\frac Ca
\le\inf_x H(x)\le\min\{H_{\rm dense},H_{\rm rare}\}.
\quad}\tag{6.2}
$$

The rare value is the energy of the actual law $x_{\{e\}}=T$, $x_C=1-T$. Every law with $t<t_{\rm conv}$ satisfies the exact lower bound $H\ge H_{\rm rare}$ for all these parameters once $a\ge A$. The theorem does not identify the exact global dense minimizer or an exact finite-$a$ transition.

**Proof.** The upper bounds are the two laws of Lemma 1.2; at $t=T$, the missing-one masses in (1.4) vanish and the full-core mass is $1-T$, proving (6.1).

For the lower bound, a law with $H>H_{\rm dense}+1$ already exceeds the proposed minimum. On the remaining sublevel $H\le H_{\rm dense}+1$, a law with $t\ge t_{\rm conv}$ satisfies (3.2). Its error is at most $C\delta\le C\lambda_+/a$, proving the desired dense-branch lower bound.

Consider now $t<t_{\rm conv}$. Uniformly on the fixed interval of $\lambda$,

$$
t<t_{\rm conv}=O(a^{-2}),\qquad
\sum_{i\in C}(1-y_i)=\delta+t=O(a^{-1}),\qquad
\min_{i\in C}y_i\ge1-\delta-t.
\tag{6.3}
$$

On the energy sublevel just specified, (5.14) and
$H_{\rm dense}-q^3=O(a^2)$ give

$$
m^2(1/t-t)\le O(a^2),\qquad m^2=O(1).
$$

This conditional-moment estimate uses that sublevel; the scalar comparison that follows in fact needs no bound on $m$ or on $H$.

Choose a fixed $C_1$ large enough that both $t_{\rm conv}$ and $T$ are at most $C_1/a^2$ for all the parameters in question. By (1.2), $g_\theta'>0$ on $(0,q)$ and $g_\theta'(t)=O(a^3)$ uniformly on $0<t\le C_1/a^2$. Hence

$$
h_\theta'(t)=-1/t^2+g_\theta'(t)<0
\quad(0<t\le C_1/a^2)
\tag{6.4}
$$

for all sufficiently large $a$ depending only on $\lambda_+$. Also
$\Lambda_\theta(t)=O(a)$ on this interval, and $1/t\ge a^2/C_1$.

If $t\le T$, monotonicity (6.4) and (2.6) give

$$
H\ge h_\theta(T)+v\left[\frac1t-\frac{\Lambda_\theta(t)}3\right]
\ge h_\theta(T),
$$

because $v\ge0$ and the bracket is positive for all sufficiently large $a$. If $t\ge T$, the increase of $g_\theta$ gives

$$
h_\theta(t)\ge h_\theta(T)+\frac1t-\frac1T.
$$

The exact capacity and $r=a+1$ imply

$$
\frac1t-\frac1T\ge-\frac{\mu-1}{\delta}
\ge-\frac v{3\delta}.
\tag{6.5}
$$

Therefore the second line of (2.6) yields

$$
H\ge h_\theta(T)+v\left[
\frac1t-\frac1{3\delta}-\frac{\Lambda_\theta(t)}3\right]
\ge h_\theta(T).\tag{6.6}
$$

Indeed $1/(3\delta)\le a/(3\lambda_-)$ and $\Lambda_\theta(t)=O(a)$, whereas $1/t\ge a^2/C_1$. This positivity is uniform on the given compact interval. Since $h_\theta(T)=H_{\rm rare}$, both rare cases give the exact bound. They did not use the preliminary sublevel restriction, so it can be dropped for the last assertion of the theorem. Combining the dense and rare branches, together with the trivial high-energy case, proves (6.2). ∎

**Theorem 6.2 (Two finer competition limits).** For every fixed real $\nu$, if

$$
\delta_a=\frac1{2a}+\frac\nu{a^2},
$$

then, for all sufficiently large $a$ these are admissible parameters and

$$
\frac{D_a(\delta_a)-2a^2}{a}\longrightarrow\min\{5,1-4\nu\}.
\tag{6.7}
$$

For every fixed real $\omega$, if

$$
\delta_a=\frac1{2a}-\frac1{a^2}+\frac\omega{a^3},
$$

then

$$
D_a(\delta_a)-2a^2-5a\longrightarrow\min\{2,7-4\omega\}.
\tag{6.8}
$$

In fact the difference between the left side of (6.8) and its stated limit is $O_\omega(1/a)$. The competing coefficients agree at $\nu=-1$ in (6.7), and at $\omega=5/4$ in (6.8). These are asymptotic competition values, not claims about an exact finite-parameter transition.

**Proof.** Write $d_{\rm dense}=H_{\rm dense}-B$ and $d_{\rm rare}=H_{\rm rare}-B$. Uniformly for $\lambda$ in a fixed positive compact interval, their exact rational expressions give

$$
\begin{aligned}
d_{\rm dense}
 &=2a^2+5a+3-2\lambda+\frac{3\lambda}{a}+O(a^{-2}),\\
d_{\rm rare}
 &=\frac{a^2}{\lambda}+2\lambda a+2\lambda
   +\frac{4\lambda^2+2\lambda}{a}+O(a^{-2}).
\end{aligned}\tag{6.9}
$$

Here $\delta=\lambda/a$. To obtain controlled errors directly, put $z=1/a$ in the formulas

$$
\begin{aligned}
d_{\rm dense}&=\frac{(2r+1)[\delta a^3+(1-\delta)r^3]}{(r-\delta)^2},\\
d_{\rm rare}&=\frac a\delta+\frac{r^3}{1-\delta/a}
 -\frac{r^2[\delta a^3+(1-\delta)r^3]}{(r-\delta)^2}.
\end{aligned}
$$

After substitution $\delta=\lambda z$, multiply each expression by $z^2$. The resulting functions are analytic in $z$ near zero with denominators uniformly bounded away from zero for $\lambda$ in the fixed compact interval (and $\lambda$ itself bounded away from zero). Expanding the factors $(1+z-\lambda z^2)^{-2}$ and $(1-\lambda z^2)^{-1}$ with their uniformly bounded Taylor remainders yields (6.9), including the displayed $1/a$ coefficients.

For $\lambda=1/2+\nu/a$, expansion of $1/\lambda$ in (6.9) gives

$$
\begin{aligned}
d_{\rm dense}&=2a^2+5a+2+O_\nu(a^{-1}),\\
d_{\rm rare}&=2a^2+(1-4\nu)a+(1+2\nu+8\nu^2)
 +O_\nu(a^{-1}).
\end{aligned}\tag{6.10}
$$

The global squeeze (6.2), after subtracting $B$, places $D_a$ within $O(1/a)$ below the minimum of these two values and at or below that minimum. Subtracting $2a^2$ and dividing by $a$ proves (6.7).

For $\lambda=1/2-1/a+\omega/a^2$, the same rational expansions instead give

$$
\begin{aligned}
d_{\rm dense}&=2a^2+5a+2+O_\omega(a^{-1}),\\
d_{\rm rare}&=2a^2+5a+7-4\omega+O_\omega(a^{-1}).
\end{aligned}\tag{6.11}
$$

For instance
$\lambda^{-1}=2+4/a+(8-4\omega)/a^2+O_\omega(a^{-3})$,
while $2\lambda a=a-2+2\omega/a$ and $2\lambda=1-2/a+O_\omega(a^{-2})$; their constant contributions in (6.9) sum to $7-4\omega$. Applying (6.2) again proves (6.8) and its error estimate. ∎

The parent volume's Theorems 10.1 and 12.5–12.6 supply, respectively, the integer-endpoint upper family and its eventual exact classification and expansion. The moving-mean remainder, the uniform envelope (3.9), the interior extension, and the crossover and competition conclusions here are repo-derived deductions from the common law specified in Definition 1.1. Jensen and Cauchy–Schwarz are classical intermediate inequalities. These statements concern laws on nonempty subsets; they do not assert exact realization or optimality at a prescribed finite graph budget. Their full-text overlap with K. Zhao and X. Zhao, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), is not determined here, and no literature-priority claim is made. Exact global minimizers in the boundary window, the least interior threshold $A(\delta_0)$, and an exact finite-$a$ transition remain unspecified.

## 追加锚（本行以下为增补区）

## 7. Actual symmetry breaking in the adjacent-cardinality family

**Definition 7.1 (Secondary-window notation).** Retain the entire law domain of Definition 1.1. In §§7–10 suppose $0<\delta\le1$ and write

$$
\begin{aligned}
w_i&=\mathbb E[K^2I_i],\qquad \mu=\frac qs,\qquad
H_d=H_{\rm dense}=\frac Z{\mu^2},\\
T_0&=\frac\delta a,\qquad
H_r=\frac1{T_0}+\frac{r^3}{1-T_0},\\
b&=(2r+1)\delta,\qquad \tau=\frac{3b}{r^2},\\
\mathcal A&=3r^2-3r+1,\qquad
\mathcal C=r(r-1)(2r-1).
\end{aligned}\tag{7.1}
$$

Here $T_0$ is a real number, whereas $T$ remains the random nonempty subset. The letter $\mu$ in these sections denotes the common marginal average $q/s$. The quantities $H_d,H_r$ are the two actual trial energies already specified in Lemma 1.2 and (6.1); no assertion of exact dense optimality is part of this notation. Zero atom masses, disconnected support, every possible cardinality $1\le K\le s$, and arbitrarily small positive marginals remain admissible.

**Theorem 7.2 (A feasible descent from equal marginals).** For every $a\ge7$ and $0<\delta<1/r$, there is an actual law supported on cardinalities $a,r$ with $H<H_d$. Its marginals can be chosen arbitrarily close to $\mu$. More explicitly, let $P=\{1,2\}$ and define

$$
\begin{aligned}
x_{[s]\setminus P}&=\delta,\\
x_{[s]\setminus\{i\}}
 &=\frac{1+\delta}{s}-\delta-\varepsilon
 &&(i=1,2),\\
x_{[s]\setminus\{j\}}
 &=\frac{1+\delta}{s}+\frac{2\varepsilon}{a}
 &&(3\le j\le s),
\end{aligned}\tag{7.2}
$$

with all other masses zero. For

$$
0\le\varepsilon<\frac{1-r\delta}{s},\qquad
v:=\mu-\frac{2\varepsilon}{a}>0,\tag{7.3}
$$

this law has mean $q$, marginals $u=\mu+\varepsilon$ on $P$ and $v$ off $P$, and exact energy

$$
\mathcal H(\varepsilon)
=\frac{2r^2}{\mu+\varepsilon}
 +a\left[
 \frac{r^2}{\mu-2\varepsilon/a}
 -\frac{(2r-1)\delta}{(\mu-2\varepsilon/a)^2}
 \right].\tag{7.4}
$$

In particular,

$$
\mathcal H(0)=H_d,\qquad
\mathcal H'(0)=-\frac{4(2r-1)\delta}{\mu^3}<0.\tag{7.5}
$$

**Proof.** The two masses indexed by $P$ equal $(1-r\delta)/s-\varepsilon$, and all the other displayed masses are positive under (7.3). Their total at cardinality $r$ is

$$
2\left(\frac{1+\delta}{s}-\delta-\varepsilon\right)
 +a\left(\frac{1+\delta}{s}+\frac{2\varepsilon}{a}\right)
=1-\delta.
$$

Adding the cardinality-$a$ mass $\delta$ gives total mass one and mean $a\delta+r(1-\delta)=q$. A label in $P$ is missing from both the mass $\delta$ and its own missing-one type; hence its marginal is $u$. A label outside $P$ is missing only from its own missing-one type; hence its marginal is $v$. These are marginals of (7.2), rather than independent choices. Positive masses and total mass one also give $u,v\le1$.

For $i\in P$ the cardinality-$a$ atom avoids $i$, so $w_i=r^2u$. For $j\notin P$ it contains $j$, giving

$$
w_j=r^2v-(r^2-a^2)\delta
=r^2v-(2r-1)\delta.
$$

Summing $w_i/y_i^2$ gives precisely the sum in (7.4). At $\varepsilon=0$ all marginals equal $\mu$ and $\mathbb E K^3=Z$, proving its value in (7.5). Differentiating that rational sum proves its derivative. Both upper bounds on a sufficiently small positive $\varepsilon$ in (7.3) have positive length, so (7.5) supplies a strict descent with arbitrarily small marginal perturbations. ∎

**Proposition 7.3 (An explicit counterlaw for every $a\ge7$).** At

$$
\delta=\frac1{2a},\qquad
\varepsilon=\frac{(2r-1)\delta}{r^2},\tag{7.6}
$$

the law (7.2) is feasible and satisfies

$$
H_d-\mathcal H(\varepsilon)
\ge\frac{(2r-1)^2\delta^2}{r^2\mu^3}>0.\tag{7.7}
$$

**Proof.** The strict mass inequality in (7.3) is equivalent to

$$
(2a+1)(a+2)<(a-1)(a+1)^2.
$$

The difference is $a^3-a^2-6a-3$, positive for $a\ge7$ since it is at least $6a^2-6a-3$. Also $\varepsilon<1/(ar)$ and $\mu\ge7/9$. For every $0\le z\le\varepsilon$ these imply

$$
\mu-\frac{2z}{a}\ge\frac9{10}\mu>0,
$$

because $2/(a^2r)\le2/(7^2\cdot8)<7/90\le\mu/10$. Direct differentiation of (7.4) gives

$$
\mathcal H''(z)
=\frac{4r^2}{(\mu+z)^3}
 +\frac{8r^2}{a(\mu-2z/a)^3}
 -\frac{24(2r-1)\delta}{a(\mu-2z/a)^4}
\le\frac{6r^2}{\mu^3}.
$$

The last step uses $8/[a(9/10)^3]\le2$ for $a\ge7$. Taylor's theorem and (7.5) now yield

$$
\begin{aligned}
\mathcal H(\varepsilon)-H_d
&\le-\frac{4(2r-1)\delta\varepsilon}{\mu^3}
 +\frac{3r^2\varepsilon^2}{\mu^3}\\
&=-\frac{(2r-1)^2\delta^2}{r^2\mu^3}.
\end{aligned}
$$

This proves both feasibility and strict improvement. ∎

**Theorem 7.4 (Quadratic descent and failure of convex symmetrization).** If $\delta=\lambda/a$ with fixed $0<\lambda<1$, then for all sufficiently large $a$ the choice $\varepsilon=(2r-1)\delta/r^2$ in (7.2) is feasible and

$$
\mathcal H(\varepsilon)
=H_d-\frac{8\lambda^2}{a^2}+O_\lambda(a^{-3}).\tag{7.8}
$$

The remainder and feasibility threshold can be taken uniformly on each compact interval $0<\lambda_-\le\lambda\le\lambda_+<1$. The nonlinear functional $H$ on the full law domain is not convex for any $0<\delta<1/r$.

**Proof.** On each such compact interval the mass upper bound in (7.3) is $(1-\lambda)/a+O(a^{-2})$, whereas $\varepsilon=2\lambda/a^2+O(a^{-3})$ and $\mu=1+O(a^{-1})$. Thus (7.3) holds uniformly eventually. In addition to (7.5), the exact second derivative at zero is

$$
\mathcal H''(0)
=4r^2(1+2/a)\mu^{-3}
 -\frac{24(2r-1)\delta}{a\mu^4}.
$$

On $0\le z\le\varepsilon$, all denominators in the first three derivatives stay bounded away from zero. Differentiating (7.4) three times therefore gives $\mathcal H'''(z)=O(a^2)$ uniformly on the compact parameter interval. The linear Taylor term at $\varepsilon$ is
$-16\lambda^2/a^2+O(a^{-3})$, the quadratic term is
$8\lambda^2/a^2+O(a^{-3})$, and the third-order remainder is $O(a^2\varepsilon^3)=O(a^{-4})$. This proves (7.8).

For the convexity assertion choose any strict descent from Theorem 7.2 and average its law over every label permutation. This average is the fully symmetric mixture of $a$- and $r$-subsets from Lemma 1.2 and has energy $H_d$. Every law being averaged has the same smaller energy $\mathcal H(\varepsilon)$. A convex functional would give $H_d\le\mathcal H(\varepsilon)$, a contradiction. This argument uses actual feasible laws and does not treat the $w_i$ and $y_i$ as independent variables. ∎

## 8. A centered residual estimate on the full law domain

**Theorem 8.1 (Dense lower bound with quadratic error).** For any law of Definition 1.1 with $0<\delta\le1$, suppose

$$
t:=\min_i y_i\ge\tau,\qquad
\frac b{r^2\mu}\le\frac1{12}.
\tag{8.1}
$$

Then, without any restriction on the cardinalities in its support,

$$
H(x)\ge H_d-72\delta^2\mu^{-6}.\tag{8.2}
$$

**Proof.** Use the full-label residuals of Lemma 3.1, writing $R_i=\widehat R_i=w_i-r^2y_i+b$ and $\tau=t_{\rm conv}$. That lemma, on exactly the full law domain used here, gives

$$
R_i\ge0,\qquad S:=\sum_iR_i
=\mathbb E K^3-r^2q+sb\ge6r\delta=:S_0.
\tag{8.5}
$$

Put $f(y)=r^2/y-b/y^2$. The exact energy decomposition and the centered rational identity are

$$
H=\sum_i f(y_i)+\sum_i\frac{R_i}{y_i^2},\tag{8.6}
$$

$$
f(y)-f(\mu)-f'(\mu)(y-\mu)
=\frac{(y-\mu)^2}{\mu^2y^2}
 \left[r^2y-b\left(1+\frac{2y}{\mu}\right)\right].
\tag{8.7}
$$

This is an identity after bringing its two sides to a common denominator. If $y\ge\tau=3b/r^2$, then $b\le r^2y/3$, while the other condition in (8.1) gives $2by/\mu\le r^2y/6$. Thus the bracket in (8.7) is at least $r^2y/2$. Using $\mu,y_i\le1$ and $\sum_i(y_i-\mu)=0$, obtain

$$
\sum_i f(y_i)\ge sf(\mu)+\frac{r^2}{2}V,
\qquad V=\sum_i(y_i-\mu)^2.
\tag{8.8}
$$

To retain the residual's dependence on the marginals, let $M=\max_i y_i\ge\mu$. Nonnegativity of $R_i$, (8.5), and the elementary tangent inequality for the inverse square give

$$
\begin{aligned}
\sum_i\frac{R_i}{y_i^2}
&\ge\frac{S_0}{M^2}\\
&\ge\frac{S_0}{\mu^2}
 -\frac{2S_0}{\mu^3}(M-\mu)\\
&\ge\frac{S_0}{\mu^2}
 -\frac{2S_0}{\mu^3}\sqrt V.
\end{aligned}\tag{8.9}
$$

The middle inequality can also be read directly from

$$
\frac1{M^2}-\frac1{\mu^2}+\frac{2(M-\mu)}{\mu^3}
=\frac{(M-\mu)^2(2M+\mu)}{\mu^3M^2}\ge0.
$$

Finally, (8.5) gives $sf(\mu)+S_0/\mu^2=H_d$. Substitution of (8.8)–(8.9) into (8.6), followed by completion of the square in $\sqrt V$, yields

$$
\begin{aligned}
H-H_d
&\ge\frac{r^2}{2}V-\frac{2S_0}{\mu^3}\sqrt V\\
&\ge-\frac{2S_0^2}{r^2\mu^6}
=-72\delta^2\mu^{-6}.
\end{aligned}
$$

Only the auxiliary rational expression has been centered; no convexity of $H$ has been assumed. ∎

## 9. The exact rare bound from an actual deleted-label core

**Theorem 9.1 (Rare lower bound and all its equality laws).** Fix $L>0$ and suppose

$$
a\ge N(L):=\left\lceil10^4\max(1,L^2)\right\rceil,
\qquad 0<\delta\le\frac La.
\tag{9.1}
$$

Every law of Definition 1.1 with $t=\min_i y_i<\tau$ satisfies $H(x)\ge H_r$. Equality holds if and only if, for some label $e$,

$$
x_{\{e\}}=T_0,\qquad
x_{[s]\setminus\{e\}}=1-T_0,
\qquad x_T=0\text{ otherwise}.
\tag{9.2}
$$

In particular, the equality class consists of these laws under arbitrary relabeling.

**Proof.** First (9.1) gives $a\ge10000$, $L^2/a\le10^{-4}$ and $\delta\le10^{-4}$. The latter follows separately from $L\le1$ and $L\ge1$. Direct calculation gives

$$
1<\frac\tau{T_0}
=\frac{3a(2r+1)}{r^2}<6,
\qquad \delta+\tau<1.
\tag{9.3}
$$

The left strict inequality follows from $5a^2+7a-1>0$, the right from $3a(2a+3)<6(a+1)^2$, and $\delta+\tau<1$ from $\tau<6\delta/a$.

Choose a least-marginal label $e$ and define, from the original law,

$$
\begin{aligned}
t&=y_e,\qquad z=x_{\{e\}},\qquad \eta=t-z,\\
\xi&=\mathbb E[(K-1)I_e],\qquad m=q-t.
\end{aligned}
$$

On each nonsingleton atom containing $e$ there is at least one further label; hence $0\le\eta\le\xi$. Since an atom avoiding $e$ contains at most $r$ labels, its actual capacity gives

$$
q\le r(1-t)+t+\xi=r-at+\xi,
\qquad \xi\ge at-\delta.
\tag{9.4}
$$

For integer $k\ge1$, $k^2-1-3(k-1)=(k-1)(k-2)\ge0$. Thus the contribution at $e$ satisfies

$$
\frac{w_e}{t^2}\ge\frac1t+\frac{3\xi}{t^2}.
\tag{9.5}
$$

Delete $e$ from this same random set, obtaining $T'=T\setminus\{e\}$. The probability of $T'=\varnothing$ is exactly $z$ and $\mathbb E|T'|=m$. For each $j\ne e$ its marginal is still $y_j>0$, and $K^2\ge|T'|^2$. Since $t<\tau$ and $\delta+\tau<1$, one has $r-1<m=q-t\le r$. Conditional on $T'\ne\varnothing$, the actual core law therefore has mean

$$
r-1\le u:=\frac{m}{1-z}\le r.
\tag{9.6}
$$

The upper bound in (9.6) is its capacity $|T'|\le r$, not an independent constraint on moments. All its conditional marginals are positive. Apply [*CDSO incidence moments and capacity phases*, Theorem 3.1](CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md) directly to this conditional law: in the normalization $H=2J$, that existing result is $H_{\rm core}\ge r^2(\mathcal A u-\mathcal C)/u^2$. The probability scaling is

$$
\sum_{j\ne e}\frac{\mathbb E[|T'|^2I_j]}{y_j^2}
=\frac{H_{\rm core}}{1-z}.
$$

It follows that

$$
\begin{aligned}
\sum_{j\ne e}\frac{w_j}{y_j^2}
&\ge\frac{r^2[\mathcal A(q-t)-\mathcal C(1-z)]}{(q-t)^2}\\
&=G(t)-A(t)\eta,
\end{aligned}\tag{9.7}
$$

where

$$
G(t)=\frac{r^2[\mathcal A(q-t)-\mathcal C(1-t)]}{(q-t)^2},
\qquad A(t)=\frac{r^2\mathcal C}{(q-t)^2}.
$$

Combining (9.5), (9.7), $A(t)>0$ and $\eta\le\xi$ yields

$$
H\ge F(t)+C(t)\xi,
\qquad F(t)=\frac1t+G(t),\qquad
C(t)=\frac3{t^2}-A(t).
\tag{9.8}
$$

We next bound this scalar expression on the whole interval $0<t<\tau$. There $q-t\ge r-2\ge3r/4$, and

$$
A(t)\le4r^3,\qquad |G'(t)|\le10r^3.
\tag{9.9}
$$

For completeness put $N_t=\mathcal A(q-t)-\mathcal C(1-t)$. Since $q-t>r-1$ and $0<t<1$, $0<N_t\le3r^3$, in particular $|N_t|\le5r^3$. Moreover $0\le\mathcal C-\mathcal A\le2r^3$ for $r\ge8$. Differentiation gives

$$
G'(t)=r^2\left[
\frac{\mathcal C-\mathcal A}{(q-t)^2}
 +\frac{2N_t}{(q-t)^3}\right].
$$

The two terms are bounded in absolute value by $(32/9)r^3$ and $(640/27)r^2$. Their sum is less than $7r^3$ for $r\ge8$, proving the second inequality of (9.9). The first follows from
$A(t)\le(16/9)\mathcal C<4r^3$.

Using $r\le2a$, $T_0\le L/a^2$ and (9.3), the explicit threshold (9.1) also gives

$$
\begin{aligned}
4r^3\tau^2&\le\frac{1152L^2}{a}<1,\\
10r^3T_0^2&\le\frac{80L^2}{a}<1,\\
\frac a{18}&>1+10r^3T_0^2.
\end{aligned}\tag{9.10}
$$

Indeed the first two upper bounds are at most $0.1152$ and $0.008$, whereas $a/18\ge10000/18>1.008$. Equations (9.9)–(9.10) imply $C(t)\ge2/t^2>0$, so the capacity (9.4) makes (9.8) into

$$
H\ge F(t)+C(t)\max\{0,a(t-T_0)\}.
\tag{9.11}
$$

For $0<t\le T_0$,

$$
F'(t)\le-T_0^{-2}+10r^3<0.
$$

Thus $F(t)\ge F(T_0)$, strictly unless $t=T_0$. For $T_0\le t<\tau$, integrate the bound on $G'$ and use $1/t-1/T_0\ge-(t-T_0)/T_0^2$ to obtain

$$
F(t)-F(T_0)\ge-(T_0^{-2}+10r^3)(t-T_0).
$$

On the other hand,

$$
C(t)a(t-T_0)
\ge\frac{2a}{\tau^2}(t-T_0)
\ge\frac{a}{18T_0^2}(t-T_0).
$$

By the third inequality of (9.10), their sum is strictly positive when $t>T_0$. Finally $q-T_0=r(1-T_0)$ and $\mathcal A r-\mathcal C=r^3$, whence

$$
G(T_0)=\frac{r^3}{1-T_0},\qquad F(T_0)=H_r.
$$

This proves the lower bound for every law in the rare region, without an energy sublevel assumption.

If $H=H_r$, the strict scalar comparisons force $t=T_0$. Returning to (9.8), where $C(t)>0$, then forces $\xi=0$. Thus every occurrence of $e$ is its singleton, so $z=t=T_0$. On the complementary event the conditional core mean is
$(q-T_0)/(1-T_0)=r$, its maximal capacity. Therefore the core is the full set of the $r$ remaining labels with probability one. This proves the necessity of (9.2) from the same realized law. Conversely (9.2) has the prescribed mean, marginals $T_0$ and $1-T_0$, and energy $H_r$. Here $T_0<\tau$ and $T_0<1/2$, so its least marginal is indeed in the asserted rare region. ∎

## 10. A global quadratic squeeze and the fifth competition scale

**Theorem 10.1 (Global $O(a^{-2})$ squeeze without a lower window cutoff).** Under (9.1), the infimum over exactly the full domain of Definition 1.1 satisfies

$$
\boxed{\quad
\min\{H_d-72\delta^2\mu^{-6},H_r\}
\le\inf_xH(x)\le\min\{H_d,H_r\}.
\quad}\tag{10.1}
$$

In particular,

$$
0\le\min\{H_d,H_r\}-\inf_xH(x)
\le72\delta^2\mu^{-6}=O_L(a^{-2}).
\tag{10.2}
$$

No positive lower bound on $a\delta$ is required. The infimum is attained by an admissible law.

**Proof.** The threshold implies $\mu\ge1/2$ and

$$
\frac b{r^2\mu}\le\frac{6\delta}{r}
\le\frac{6L}{a^2}<\frac1{12}.
$$

For example $L/a\le10^{-4}$ and $a\ge10000$ already make the final strict inequality immediate. Every actual law either has $\min_i y_i\ge\tau$, when Theorem 8.1 applies, or has $\min_i y_i<\tau$, when Theorem 9.1 applies. This exhaustive partition proves the lower bound in (10.1). The upper bound consists of the actual symmetric law in Lemma 1.2 and the actual two-atom law (9.2). The difference between the two lower and upper minima is at most $72\delta^2\mu^{-6}$. Since $\mu\ge1/2$ and $\delta\le L/a$, this proves (10.2), including arbitrarily small positive $a\delta$.

For attainment choose a minimizing sequence with energy bounded by some finite $M$, possible because the symmetric trial law has finite energy. Since $K\ge1$, one has $w_i\ge y_i$ and hence $H\ge1/y_i$ for every label. Thus each marginal along this sequence is at least $1/M$. The probability simplex on the finite set of nonempty subsets of $[s]$ is compact. A convergent subsequence has a limit with total mass one, mean $q$ and all marginals at least $1/M$. Energy is continuous there, so the limit attains the infimum. The lower bound $1/M$ is a consequence for this sequence, not a restriction of the original domain. ∎

**Corollary 10.2 (The quadratic error order is necessary).** Fix $0<\lambda<1/2$ and put $\delta=\lambda/a$. Then $H_d<H_r$ eventually and

$$
H_d-\inf_xH(x)
\ge\frac{8\lambda^2}{a^2}+O_\lambda(a^{-3}).
\tag{10.3}
$$

Consequently the $O_L(a^{-2})$ gap in (10.2) cannot be replaced throughout this region by $o(a^{-2})$. This is a lower bound on the global improvement furnished by one actual family; it does not identify the optimal quadratic coefficient.

**Proof.** Substitution in the exact rational formulas gives

$$
\frac{H_r-H_d}{a^2}\longrightarrow\lambda^{-1}-2>0.
$$

The actual law of Theorem 7.4 has energy $H_d-8\lambda^2/a^2+O_\lambda(a^{-3})$, so the global infimum is at most this value. This proves (10.3) and the failure of an $o(a^{-2})$ bound even along any such fixed $\lambda$. ∎

**Theorem 10.3 (The fifth scale and exact noncritical rare minimizers).** For fixed $\zeta\in\mathbb R$, set

$$
\delta_a=\frac1{2a}-\frac1{a^2}
 +\frac5{4a^3}+\frac\zeta{a^4}.
\tag{10.4}
$$

These parameters are eventually positive and admissible, and

$$
\boxed{\quad
\lim_{a\to\infty}a\,[D_a(\delta_a)-2a^2-5a-2]
=\min\left\{\frac72,-\frac32-4\zeta\right\}.
\quad}\tag{10.5}
$$

The two fifth-scale coefficients meet at $\zeta=-5/4$. If $\zeta>-5/4$ is fixed, then for all sufficiently large $a$ the global minimum is exactly $H_r$, and all minimizing laws are (9.2), up to relabeling. If $\zeta<-5/4$ is fixed, every minimizing law has $\min_i y_i\ge\tau$ eventually, and $\inf H<H_d<H_r$; no exact dense minimizing law is asserted.

The optimal dense improvement coefficient at order $a^{-2}$, an exact finite-$a$ crossing, and the next scale at $\zeta=-5/4$ remain unspecified. The law (7.2) is an improvement family and is not asserted to attain the global minimum. The threshold $N(L)$ is sufficient and is not asserted to be least. These statements concern the subset-law problem and assert no prescribed finite-graph realization or graph-budget optimality.

**Proof.** For fixed $\zeta$, (10.4) eventually satisfies (9.1) with $L=1$. Subtracting the same parameter-dependent $B$ in (10.1) gives

$$
D_a(\delta_a)
=\min\{H_d-B,H_r-B\}+O_\zeta(a^{-2}).
\tag{10.6}
$$

Here is a direct expansion of the exact rational energies. Put $h=1/a$, write $\delta=\delta_a$, and set

$$
Q=1+h-h\delta,\qquad
P=(1+h)^3-\delta(3h+3h^2+h^3),\qquad
F=\frac P{Q^2}.
$$

Then $q=aQ$, $Z=a^3P$, and exactly

$$
\begin{aligned}
B&=h^{-3}(1+h)^2F,\\
H_d-B&=h^{-2}(2+3h)F,\\
H_r-B&=\frac1{h\delta}
 +h^{-3}\left[\frac{(1+h)^3}{1-h\delta}-(1+h)^2F\right].
\end{aligned}\tag{10.7}
$$

Substitute $\delta=h/2-h^2+5h^3/4+\zeta h^4$. Multiplication of the Taylor series for the displayed polynomial numerators and inverse denominators yields

$$
\begin{aligned}
F&=1+h-\frac12h^2+\frac52h^3-7h^4
 +O_\zeta(h^5),\\
\frac1{h\delta}
 &=\frac2{h^2}+\frac4h+3+(-4-4\zeta)h
 +O_\zeta(h^2),\\
\frac{(1+h)^3}{1-h\delta}-(1+h)^2F
 &=h^2-h^3+\frac52h^4+O_\zeta(h^5).
\end{aligned}\tag{10.8}
$$

All remainders here are ordinary Taylor remainders of analytic rational functions near $h=0$: $Q(0)=1$, $1-h\delta=1$ there, and $\delta/h$ tends to $1/2$. Thus the inverse factors are defined with bounded derivatives in a neighborhood depending only on the fixed $\zeta$. Equations (10.7)–(10.8) give

$$
\begin{aligned}
H_d-B&=2a^2+5a+2+\frac7{2a}+O_\zeta(a^{-2}),\\
H_r-B&=2a^2+5a+2
 +\frac{-3/2-4\zeta}{a}+O_\zeta(a^{-2}).
\end{aligned}\tag{10.9}
$$

Taking the smaller expansion in (10.6), multiplying by $a$, and letting $a\to\infty$ proves (10.5). Equality of the two limiting coefficients is $7/2=-3/2-4\zeta$, namely $\zeta=-5/4$.

If $\zeta>-5/4$, then (10.9) gives

$$
H_d-H_r=\frac{5+4\zeta}{a}+O_\zeta(a^{-2})
>72\delta_a^2\mu^{-6}
$$

eventually. Theorem 8.1 then puts every law with least marginal at least $\tau$ strictly above $H_r$. Theorem 9.1 bounds the complementary region by $H_r$ and classifies all equality laws, proving the exact global rare assertion. If $\zeta<-5/4$, (10.9) instead gives $H_d<H_r$ eventually. The symmetric trial law therefore excludes every rare-region law from global minimization. Also $\delta_a<1/r$ eventually, so Theorem 7.2 supplies $\inf H<H_d$. This proves precisely the stated dense-side conclusions. ∎

## 追加锚（本行以下为增补区）

## 11. The sharp dense improvement on the entire law domain

**Definition 11.1 (Dense infimum and centered incidence).** Retain Definition 1.1, with no restriction on the cardinalities of positive-mass types, and the notation of Definition 7.1. For $0<\delta\le1$ define

$$
\mathscr D_a(\delta)
=\inf\{H(x):x\text{ satisfies Definition 1.1 and }\min_i y_i\ge\tau\}.
\tag{11.1}
$$

The additional condition in (11.1) defines the dense part of the original domain; it imposes neither exchangeability nor a prescribed support. For a vector $v\in\mathbb R^s$ let

$$
\Pi v=v-\frac1s\Bigl(\sum_i v_i\Bigr)\mathbf1,
\qquad \|v\|^2=\sum_i v_i^2.
$$

For each actual law put

$$
\begin{aligned}
z&=r-K,\qquad
\Phi(z)=z(z-1)(3r-z-1),\\
\Delta&=\mathbb E K^3-Z,\qquad
d_i=y_i-\mu,\qquad V=\|d\|^2,\\
c_i&=\mathbb E[(K^2-r^2)I_i],\qquad c^\circ=\Pi c,\\
\kappa&=\sqrt{\frac{2a}{s}},\qquad
A=\kappa(2r-1)\delta,\\
Q_*&=\frac{A^2}{r^2\mu^3}
=\frac{2a}{s}\frac{(2r-1)^2\delta^2}{r^2\mu^3}.
\end{aligned}\tag{11.2}
$$

Every expectation in these definitions is taken under the same $x$. The reference moment $Z$ is still the adjacent-cardinality moment, rather than an imposed third moment. The polynomial deficit in Lemma 3.1, the centered identity (8.7), and the actual comparison laws (7.2) will be used below. The optimization of feasible joint moments and the distinction between tight bounds and attained bounds have the classical background of D. Bertsimas and I. Popescu, *Optimal inequalities in probability theory: A convex optimization approach*, SIAM J. Optim. 15(3), 780–804, DOI [10.1137/S1052623401399903](https://doi.org/10.1137/S1052623401399903), pp.780–781. The nonlinear dense estimate here is a repo-derived consequence of the actual incidence relation proved below; it is not an application of a theorem optimizing the moment coordinates independently.

**Proposition 11.2 (A centered incidence constraint from the actual law).** Every law of Definition 1.1 satisfies

$$
\Delta=\mathbb E\Phi(z)\ge0,
\qquad \boxed{\ \|c^\circ\|\le A+3\Delta.\ }
\tag{11.3}
$$

Neither density nor an energy sublevel is assumed.

**Proof.** The secant residual of $k^3$ at $k=a,r$ is

$$
(k-a)(k-r)(k+a+r)
=k^3-(a^2+ar+r^2)k+ar(a+r).
$$

Its expectation is $\mathbb E K^3-Z$, because the actual mean and the reference mean both equal $q$. Substitution $k=r-z$ gives $\Phi(z)$, the deficit already used in (3.3). Its value at $z=-1$ is $6r$, its values at $z=0,1$ vanish, and it is positive for integers $2\le z\le r-1$. This proves the first assertion on every allowed cardinality $1\le K\le s$.

Linearity of projection gives the same-law identity

$$
c^\circ=\mathbb E\left[(K^2-r^2)
 \left(I-\frac Ks\mathbf1\right)\right],
\qquad
\left\|\mathbf1_T-\frac{|T|}{s}\mathbf1\right\|^2
=\frac{|T|(s-|T|)}s.
\tag{11.4}
$$

Write $p_j=\mathbb P(z=j)$. At $z=-1$ the projected incidence vector is zero, and at $z=0$ the multiplier $K^2-r^2$ is zero. At $z=1$, the norm of each integrand in (11.4) is $(2r-1)\kappa$. For $2\le z\le r-1$, the ratio of its norm to $\Phi(z)$ is

$$
\frac{(2r-z)\sqrt{(r-z)(z+1)/s}}
 {(z-1)(3r-z-1)}
\le\frac{\sqrt{z+1}}{z-1}\le2.
\tag{11.5}
$$

Here $2r-z\le3r-z-1$ and $(r-z)/s\le1$; the last inequality follows from $z+1\le4(z-1)^2$ for integers $z\ge2$. The total contribution of these cardinalities therefore has norm at most $2\Delta$. Finally $\mathbb E z=\delta$ implies

$$
p_1=\delta+p_{-1}-\sum_{j\ge2}j p_j
\le\delta+\frac{\Delta}{6r}.
$$

The triangle inequality in (11.4) now gives

$$
\|c^\circ\|\le(2r-1)\kappa p_1+2\Delta
\le A+\left(2+\frac{\kappa(2r-1)}{6r}\right)\Delta
\le A+3\Delta.
$$

The last coefficient bound uses $\kappa\le\sqrt2$. Thus both the vector being bounded and the deficit paying for all other cardinalities come from the original law. ∎

**Lemma 11.3 (Dense sublevel localization retaining the moment deficit).** Fix $L>0$. For all sufficiently large $a$, uniformly over $0<\delta\le L/a$, every actual dense law with $H\le H_d$ satisfies

$$
\sqrt V\le\frac{24\delta}{r\mu^3},\qquad
0\le\Delta\le72\delta^2\mu^{-6},\qquad
\max_i|c_i|=O_L(r\delta).
\tag{11.6}
$$

In particular $y_i=\mu+O_L(\delta/r)$ for every label. These are consequences for this sublevel and are not extra assumptions on the law domain.

**Proof.** Set $R_i=c_i+b$, as in Lemma 3.1. Its pointwise nonnegative residual is

$$
(1-I_i)(2r+1)(r-K)+I_i(s-K)(s-K-1).
$$

Consequently

$$
R_i\ge0,\qquad
\sum_iR_i=S_0+\Delta,\qquad S_0=6r\delta.
\tag{11.7}
$$

The sum identity follows from $\sum_i c_i=\mathbb E K^3-r^2q$ and $Z-r^2q+sb=6r\delta$. With $f(y)=r^2/y-b/y^2$, (8.6)–(8.8) give, for all sufficiently large $a$ in the stated window,

$$
H=\sum_i f(y_i)+\sum_i\frac{R_i}{y_i^2},\qquad
\sum_i f(y_i)\ge sf(\mu)+\frac{r^2}{2}V,
\qquad sf(\mu)+\frac{S_0}{\mu^2}=H_d.
$$

Indeed $\mu\ge1/2$ and $b/(r^2\mu)\le1/12$ eventually, and density is exactly the other hypothesis needed in (8.7). Put $M=\max_i y_i$. Since $M\le1$, the inverse-square tangent inequality yields

$$
\begin{aligned}
\sum_i\frac{R_i}{y_i^2}
&\ge\frac{S_0+\Delta}{M^2}\\
&\ge\frac{S_0}{\mu^2}
 -\frac{2S_0}{\mu^3}(M-\mu)+\Delta\\
&\ge\frac{S_0}{\mu^2}
 -\frac{2S_0}{\mu^3}\sqrt V+\Delta.
\end{aligned}
$$

Thus

$$
H-H_d\ge\Delta+\frac{r^2}{2}V
 -12r\delta\mu^{-3}\sqrt V.
\tag{11.8}
$$

Under $H\le H_d$, nonnegativity of $\Delta$ first gives the bound for $\sqrt V$ in (11.6). Maximizing $12r\delta\mu^{-3}u-r^2u^2/2$ over $u\ge0$ gives the displayed bound for $\Delta$. Finally (11.7) implies
$|c_i|\le b+S_0+\Delta=O_L(r\delta)$, since $\delta/r$ is uniformly bounded and tends to zero. ∎

**Theorem 11.4 (Uniform sharp dense infimum with no lower window cutoff).** For every fixed $0<L<1$ there are constants $a_0(L),C_L$ such that, for all integers $a\ge a_0(L)$ and all $0<\delta\le L/a$,

$$
\boxed{\quad
\left|\mathscr D_a(\delta)-H_d+Q_*\right|
\le C_L\frac{\delta^3}{r}.
\quad}\tag{11.9}
$$

The dense infimum is attained. In particular, for every compact interval $J\subset(0,1)$, uniformly for $\lambda\in J$,

$$
\mathscr D_a(\lambda/a)
=H_d-\frac{8\lambda^2}{a^2}+O_J(a^{-4}).
\tag{11.10}
$$

The lower bound in (11.9) holds on the entire dense part of Definition 1.1, including laws with arbitrary positive cardinalities and disconnected support.

**Proof.** First consider a dense law with $H\le H_d$. Lemma 11.3 gives uniform lower bounds on all $y_i$ and $\mu$, as well as $\|d\|=O_L(\delta/r)$. Expand the exact identity

$$
H=\sum_i\left(\frac{r^2}{y_i}+\frac{c_i}{y_i^2}\right).
$$

The constant term is $(r^2q+\sum_i c_i)/\mu^2=H_d+\Delta/\mu^2$. The $r^2$ linear term vanishes because $\sum_i d_i=0$, and $\langle c,d\rangle=\langle c^\circ,d\rangle$. Thus

$$
H-H_d=\frac{\Delta}{\mu^2}
 +\mu^{-3}\left(r^2\|d\|^2-2\langle c^\circ,d\rangle\right)
 +E,\qquad |E|\le C_L\frac{\delta^3}{r}.
\tag{11.11}
$$

To justify the error without a factor depending on the number of labels, use the exact scalar identities

$$
\begin{aligned}
\frac1{\mu+d}-\frac1\mu+\frac d{\mu^2}-\frac{d^2}{\mu^3}
 &=-\frac{d^3}{\mu^3(\mu+d)},\\
\frac1{(\mu+d)^2}-\frac1{\mu^2}+\frac{2d}{\mu^3}
 &=\frac{d^2(3\mu+2d)}{\mu^3(\mu+d)^2}.
\end{aligned}
$$

They imply

$$
|E|\le C\left[r^2\sum_i|d_i|^3
 +(\max_i|c_i|)V\right]
\le C_L\left(r^2V^{3/2}+r\delta V\right)
\le C_L\frac{\delta^3}{r}.
$$

Complete the square in (11.11):

$$
H-H_d+Q_*
=\frac{r^2}{\mu^3}\left\|d-\frac{c^\circ}{r^2}\right\|^2
 +\frac{\Delta}{\mu^2}
 +\frac{A^2-\|c^\circ\|^2}{r^2\mu^3}+E.
$$

By Proposition 11.2 the possibly negative norm gap is at least
$-(6A\Delta+9\Delta^2)/(r^2\mu^3)$. Since
$A=O(r\delta)$ and $\Delta=O_L(\delta^2)$, uniformly on the stated window and for large $a$,

$$
\mu^{-2}-\frac{6A+9\Delta}{r^2\mu^3}\ge\frac12.
$$

We obtain the stronger sublevel stability estimate

$$
\boxed{\quad
H-H_d+Q_*\ge\frac\Delta2
 +\frac{r^2}{\mu^3}\left\|d-\frac{c^\circ}{r^2}\right\|^2
 -C_L\frac{\delta^3}{r}.
\quad}\tag{11.12}
$$

Dropping its nonnegative terms proves the required lower bound for $H\le H_d$; laws with $H>H_d$ satisfy that lower bound automatically.

For a matching actual upper law, fix a pair $P\subset[s]$ and use (7.2), with its labels relabeled to $P$, at

$$
\varepsilon_*=
\frac as\frac{(2r-1)\delta}{r^2}.
\tag{11.13}
$$

The two missing-one masses on $P$ are $(1-r\delta)/s-\varepsilon_*$, and each missing-one mass off $P$ is $(1+\delta)/s+2\varepsilon_*/a$. For large $a$, the former are positive uniformly over the whole window: $1-r\delta\ge(1-L)/2$, while $\varepsilon_*=O_L(\delta/r)=O_L(a^{-2})$. The masses of cardinality $r$ add to $1-\delta$, and the sole cardinality-$a$ mass is $\delta$ on $[s]\setminus P$. Hence this is an actual probability law of mean $q$. Its marginals are $\mu+\varepsilon_*$ on $P$ and $\mu-2\varepsilon_*/a$ off $P$, so it is dense for all sufficiently large $a$.

For this one law, directly,

$$
\begin{aligned}
\Delta&=0,\qquad
c_i=0\ (i\in P),\qquad
c_j=-(2r-1)\delta\ (j\notin P),\\
c^\circ&=(2r-1)\delta
 \left(\mathbf1_P-\frac2s\mathbf1\right),\qquad
\|c^\circ\|^2=A^2,\qquad d=\frac{c^\circ}{r^2}.
\end{aligned}\tag{11.14}
$$

Its explicit vectors satisfy $\|d\|=O_L(\delta/r)$ and $\max_i|c_i|=O(r\delta)$, so the scalar identities proving (11.11) apply to it directly, without assuming its energy lies in a sublevel. Equations (11.11) and (11.14) give $H=H_d-Q_*+O_L(\delta^3/r)$, proving the upper bound. No exact finite-$a$ minimizing property of this family is needed. The feasible dense laws form a nonempty compact subset of the finite probability simplex with $y_i\ge\tau>0$. Continuity of $H$ proves attainment.

Finally put $h=1/a$ and $\delta=\lambda h$. The exact expression (11.2) becomes

$$
Q_*=\frac{2\lambda^2h^2(2+h)^2(1+2h)^2}
 {(1+h)^2(1+h-\lambda h^2)^3}.
\tag{11.15}
$$

The rational factor multiplying $\lambda^2h^2$ has constant coefficient $8$ and linear coefficient zero: the relative linear coefficient of both its numerator and denominator is $5$. Taylor expansion with denominators bounded away from zero uniformly on $J$ gives
$Q_*=8\lambda^2h^2+O_J(h^4)$. Also $\delta^3/r=O_J(h^4)$. Substitution in (11.9) proves (11.10). ∎

## 12. Necessary concentration of an omitted pair

**Theorem 12.1 (Structure forced by asymptotically minimizing dense laws).** Let $J$ be a fixed compact interval in $(0,1)$. For each sufficiently large integer $a$, choose $\lambda_a\in J$, set $\delta_a=\lambda_a/a$, and let $x_a$ be any actual dense law satisfying

$$
H(x_a)-\mathscr D_a(\delta_a)=o(a^{-2}).
\tag{12.1}
$$

Then there exist pairs $P_a\subset[s]$ such that

$$
\begin{aligned}
\mathbb P_{x_a}(K=a)&=\delta_a+o(a^{-3}),\\
\mathbb P_{x_a}(K\notin\{a,r\})&=o(a^{-3}),\\
\mathbb P_{x_a}(T=[s]\setminus P_a\mid K=a)&=1-o(1),\\
\left\|y-\mu\mathbf1
 -\frac{(2r-1)\delta_a}{r^2}
 \left(\mathbf1_{P_a}-\frac2s\mathbf1\right)\right\|
 &=o(a^{-2}).
\end{aligned}\tag{12.2}
$$

All little-oh assertions are along the given sequence $a\to\infty$; $\lambda_a$ need not converge. The conditional law is defined eventually by the first line. This is a necessary asymptotic structure, not a finite-$a$ equality classification or a sufficiency assertion for arbitrary laws satisfying (12.2).

**Proof.** Since $\lambda_a$ stays bounded away from zero, $Q_*$ is bounded below by a positive constant times $a^{-2}$. Theorem 11.4 and (12.1) therefore put $x_a$ in $H<H_d$ eventually. The left side of (11.12) is $o(a^{-2})$, and its error is $O_J(a^{-4})$. Consequently

$$
\Delta=o(a^{-2}),\qquad
\left\|d-\frac{c^\circ}{r^2}\right\|=o(a^{-2}).
\tag{12.3}
$$

For $z\ge2$, $\Phi(z)\ge2rz(z-1)$, while $\Phi(-1)=6r$. Hence, with $p_j=\mathbb P(z=j)$,

$$
p_{-1}+\sum_{j\ge2}p_j=O(\Delta/r),\qquad
\left|p_1-\delta_a\right|
=\left|p_{-1}-\sum_{j\ge2}j p_j\right|
=O(\Delta/r).
$$

These estimates prove the first two lines of (12.2).

Let $e=d-c^\circ/r^2$. Rewriting (11.11) gives

$$
H-H_d=-\frac{\|c^\circ\|^2}{r^2\mu^3}
 +\frac\Delta{\mu^2}+\frac{r^2}{\mu^3}\|e\|^2+E.
$$

Equations (12.1), (12.3) and Theorem 11.4 imply

$$
\|c^\circ\|^2=A^2+o(1).
\tag{12.4}
$$

Write $p=\mathbb P(K=a)$ and

$$
v=\mathbb E\left[I-\frac as\mathbf1\ \middle|\ K=a\right].
$$

The other cardinalities in (11.4) have total projected contribution $O(\Delta)$ by (11.5), and therefore

$$
c^\circ=-(2r-1)p v+O_{\|\cdot\|}(\Delta).
\tag{12.5}
$$

Here $O_{\|\cdot\|}(\Delta)$ denotes a vector of Euclidean norm $O(\Delta)$. The scalar $(2r-1)p$ is bounded above and away from zero, and $p/\delta_a\to1$. Combining (12.4)–(12.5) yields
$\|v\|^2=\kappa^2-o(1)$, since each centered cardinality-$a$ incidence vector has squared norm $\kappa^2$.

Take independent conditional draws $U,U'$ given $K=a$. The Euclidean variance identity gives

$$
\mathbb E\|\mathbf1_U-\mathbf1_{U'}\|^2
=2(\kappa^2-\|v\|^2)=o(1).
$$

Two distinct $a$-subsets have squared incidence distance at least two. Thus their conditional coincidence probability tends to one. If $\pi_U=\mathbb P(T=U\mid K=a)$, then

$$
1-o(1)=\sum_U\pi_U^2\le\max_U\pi_U\le1.
$$

Choose a largest atom $U_a=[s]\setminus P_a$. This proves the third line of (12.2). Since all the centered incidence vectors have norm $\kappa\le\sqrt2$, their mean differs from the vector at this atom by norm at most $2\sqrt2(1-\pi_{U_a})=o(1)$. Hence

$$
v=\mathbf1_{[s]\setminus P_a}-\frac as\mathbf1+o_{\|\cdot\|}(1).
$$

Equation (12.5) and $p=\delta_a+o(a^{-3})$ now give

$$
c^\circ=(2r-1)\delta_a
 \left(\mathbf1_{P_a}-\frac2s\mathbf1\right)+o_{\|\cdot\|}(1).
$$

Together with (12.3) this proves the final line of (12.2). In particular the two enhanced marginals and the concentrated omitted pair are properties of the same actual law. ∎

## 13. The sixth competition scale and its fixed critical sequence

**Theorem 13.1 (Sixth-scale competition and eventual phases).** Fix $\eta\in\mathbb R$ and put

$$
\delta_a=\frac1{2a}-\frac1{a^2}+\frac5{4a^3}
 -\frac5{4a^4}+\frac\eta{a^5}.
\tag{13.1}
$$

These parameters are positive and admissible for all sufficiently large $a$, and

$$
\boxed{\quad
\lim_{a\to\infty}a^2
 \left[D_a(\delta_a)-2a^2-5a-2-\frac7{2a}\right]
=\min\left\{-\frac{17}{2},-1-4\eta\right\}.
\quad}\tag{13.2}
$$

If $\eta<15/8$, every globally minimizing law is eventually dense, and

$$
D_a(\delta_a)=2a^2+5a+2+\frac7{2a}
 -\frac{17}{2a^2}+\frac{41}{2a^3}+O_\eta(a^{-4}).
\tag{13.3}
$$

If $\eta\ge15/8$, including the fixed value $\eta=15/8$, the global minimum of $H$ is eventually exactly $H_r$. All globally minimizing laws are, up to relabeling,

$$
x_{\{e\}}=\frac{\delta_a}{a},\qquad
x_{[s]\setminus\{e\}}=1-\frac{\delta_a}{a},\qquad
x_T=0\text{ otherwise},
\tag{13.4}
$$

and on this side

$$
D_a(\delta_a)=2a^2+5a+2+\frac7{2a}
 +\frac{-1-4\eta}{a^2}
 +\frac{24-14\eta}{a^3}+O_\eta(a^{-4}).
\tag{13.5}
$$

The parameter $\eta$ in these assertions is fixed. Neither an exact finite-$a$ dense optimizer nor an exact crossing curve for parameters moving beyond the specified sequence is determined by this theorem. The conclusions concern precisely the subset-law domain of Definition 1.1 and do not assert realization or optimality at a prescribed finite graph budget.

**Proof.** The parameters (13.1) eventually satisfy $0<\delta_a\le(3/4)/a$, so both Theorem 11.4 and Theorem 9.1 apply. The latter gives the exact rare minimum $H_r$, attained only by (13.4). Dense and rare are an exhaustive partition of the original domain. Thus

$$
\inf_xH(x)=\min\{\mathscr D_a(\delta_a),H_r\}.
\tag{13.6}
$$

Attainment is also provided by Theorem 10.1.

For the required expansions put $h=1/a$, substitute
$\delta=h/2-h^2+5h^3/4-5h^4/4+\eta h^5$, and define

$$
\begin{aligned}
Q_0&=1+h-h\delta,\\
P_0&=(1+h)^3-\delta(3h+3h^2+h^3),\\
F&=P_0/Q_0^2,\\
R&=\frac{(1+h)^3}{1-h\delta}-(1+h)^2F.
\end{aligned}
$$

The exact rational identities (10.7) read

$$
H_d-B=h^{-2}(2+3h)F,\qquad
H_r-B=\frac1{h\delta}+h^{-3}R.
\tag{13.7}
$$

Multiplying the numerator polynomials and the inverse denominator series gives

$$
\begin{aligned}
F&=1+h-\frac12h^2+\frac52h^3-7h^4
 +\frac{67}{4}h^5+O_\eta(h^6),\\
\frac1{h\delta}
 &=2h^{-2}+4h^{-1}+3+h
 +\left(\frac92-4\eta\right)h^2
 +(14-16\eta)h^3+O_\eta(h^4),\\
R&=h^2-h^3+\frac52h^4-\frac{11}{2}h^5
 +(10+2\eta)h^6+O_\eta(h^7).
\end{aligned}\tag{13.8}
$$

For example the first series is characterized to the displayed order by
$Q_0^2F=P_0$; the second by $(h\delta)(h\delta)^{-1}=1$ after factoring $h^2$; and the third follows by substitution of the first into its defining difference. All inverse factors after these powers of $h$ are removed are analytic near zero: $Q_0\to1$, $1-h\delta\to1$, and $\delta/h\to1/2$. Thus the remainders in (13.8) are bounded Taylor remainders for each fixed $\eta$.

Equations (13.7)–(13.8) yield

$$
\begin{aligned}
H_d-B&=2a^2+5a+2+\frac7{2a}
 -\frac{13}{2a^2}+\frac{25}{2a^3}+O_\eta(a^{-4}),\\
H_r-B&=2a^2+5a+2+\frac7{2a}
 +\frac{-1-4\eta}{a^2}
 +\frac{24-14\eta}{a^3}+O_\eta(a^{-4}).
\end{aligned}\tag{13.9}
$$

In (11.15) the moving parameter is
$\lambda_a=a\delta_a=1/2-h+5h^2/4-5h^3/4+\eta h^4$. It stays in a fixed compact interval in $(0,1)$, so

$$
Q_*=8\lambda_a^2h^2+O_\eta(h^4)
=2h^2-8h^3+O_\eta(h^4),\qquad
\frac{\delta_a^3}{r}=O_\eta(h^4).
$$

Theorem 11.4 therefore sharpens the dense branch to

$$
\mathscr D_a(\delta_a)-B
=2a^2+5a+2+\frac7{2a}
 -\frac{17}{2a^2}+\frac{41}{2a^3}+O_\eta(a^{-4}).
\tag{13.10}
$$

Taking the smaller of (13.9) and (13.10) in (13.6) proves (13.2). More precisely,

$$
H_r-\mathscr D_a(\delta_a)
=\frac{15/2-4\eta}{a^2}
 +\frac{7/2-14\eta}{a^3}+O_\eta(a^{-4}).
\tag{13.11}
$$

For fixed $\eta<15/8$ the first coefficient is positive, so every rare law has energy strictly greater than the attained dense infimum. This proves (13.3) and the dense assertion. For fixed $\eta>15/8$ it is negative, so the dense region is strictly above $H_r$; Theorem 9.1 then proves (13.4)–(13.5). At the fixed value $\eta=15/8$, the first coefficient vanishes but the second equals $-91/4$. Hence

$$
H_r-\mathscr D_a(\delta_a)
=-\frac{91}{4a^3}+O(a^{-4})<0
$$

for all sufficiently large $a$, giving the same exact rare minimum and equality class. In this case the $a^{-3}$ coefficients of the rare and dense branches are $-9/4$ and $41/2$, respectively. This decides the stated fixed critical sequence without determining a general finite-$a$ transition curve. ∎

## 追加锚（本行以下为增补区）

## 14. Exact finite-parameter dense minimizers

**Definition 14.1 (Exact scalar parameters).** Retain the law of Definition 1.1, the notation of Definition 7.1 and the dense infimum $\mathscr D_a(\delta)$ of (11.1). In this section put

$$
\gamma=(2r-1)\delta,\qquad
\rho=\frac{\gamma}{r^2},\qquad
m=\frac{1-r\delta}{s},\qquad e_0=4\rho,
\tag{14.1}
$$

and, whenever both denominators are positive, write

$$
\begin{aligned}
u(\varepsilon)&=\mu+\varepsilon,
&v(\varepsilon)&=\mu-\frac{2\varepsilon}{a},\\
\mathcal H(\varepsilon)
&=\frac{2r^2}{u(\varepsilon)}
 +a\left[\frac{r^2}{v(\varepsilon)}
 -\frac{\gamma}{v(\varepsilon)^2}\right].
\end{aligned}
\tag{14.2}
$$

Thus $\mathcal H$ is precisely the energy (7.4) of the actual family (7.2). No restriction on the cardinalities of an arbitrary law is added to (11.1).

**Lemma 14.2 (A weighted certificate on every nonempty subset).** For any law of Definition 1.1 with $\delta>0$, define from its actual marginals

$$
\alpha_i=y_i^{-2},\qquad
W_T=\sum_{i\in T}\alpha_i,\qquad
W=\sum_{i=1}^s\alpha_i,\qquad
M=\max_{\substack{U\subseteq[s]\\|U|=a}}W_U.
\tag{14.3}
$$

For every nonempty $T\subseteq[s]$, put $k=|T|$ and

$$
G_y(T)=(r-k)\big[(2r-1)M-(r+k)W_T\big].
\tag{14.4}
$$

Then $G_y(T)\ge0$, and its complete zero set is

$$
G_y(T)=0
\quad\Longleftrightarrow\quad
k=r\ \text{ or }\ (k=a\ \text{ and }\ W_T=M).
\tag{14.5}
$$

For the same original law one has the exact decomposition

$$
\boxed{\quad
H(x)=r^2\sum_{i=1}^s\frac1{y_i}-\gamma M
       +\mathbb E_xG_y(T).
\quad}
\tag{14.6}
$$

In particular this certificate requires neither density nor localization of the marginals.

**Proof.** If $k\le a$, extend $T$ to an $a$-subset. The positive weights give $W_T\le M$. For $k<a$ it follows that

$$
(2r-1)M-(r+k)W_T
\ge(a-k)M>0,
$$

so $G_y(T)>0$. At $k=a$ it equals $(2r-1)(M-W_T)$, giving the second zero case of (14.5). At $k=r$ it vanishes. The only remaining cardinality is $k=s=r+1$, for which $T=[s]$ and

$$
G_y([s])=(2r+1)W-(2r-1)M\ge2M>0.
$$

This proves the inequality and every equality case on the whole allowed cardinality range. Expanding (14.4) gives

$$
G_y(T)=(k^2-r^2)W_T+(2r-1)(r-k)M.
$$

Since $\mathbb E_x(r-K)=\delta$ and

$$
\mathbb E_x W_T
=\sum_i\alpha_i\mathbb E_x I_i
=\sum_i\frac1{y_i},
$$

taking expectation proves (14.6). The passage from a pointwise inequality to an expectation bound is the classical weak-duality principle; see D. Bertsimas and I. Popescu, *Optimal inequalities in probability theory: A convex optimization approach*, SIAM J. Optim. 15(3), 780–804, DOI [10.1137/S1052623401399903](https://doi.org/10.1137/S1052623401399903), Theorem 2.1. The explicit expression (14.4) supplies its pointwise inequality here. All weights and expectations in (14.6) are computed from $x$. ∎

**Theorem 14.3 (Exact dense minimum and all labeled equality laws).** Fix $0<L<1$ and set

$$
A(L)=\left\lceil\frac{64}{1-L}\right\rceil.
\tag{14.7}
$$

For every integer $a\ge A(L)$ and every real $0<\delta\le L/a$, there is a unique $\varepsilon_*$ in $(0,e_0)$ satisfying

$$
r^2v(\varepsilon_*)
 \big[u(\varepsilon_*)^2-v(\varepsilon_*)^2\big]
=2\gamma u(\varepsilon_*)^2.
\tag{14.8}
$$

It obeys the strict bounds

$$
0<\varepsilon_*<\frac{\rho}{\mu^3}<e_0<m.
\tag{14.9}
$$

Write $u_*=u(\varepsilon_*)$ and $v_*=v(\varepsilon_*)$. The minimum over the entire dense domain (11.1) is exactly

$$
\boxed{\quad
\mathscr D_a(\delta)
=\frac{2r^2}{u_*}
 +a\left(\frac{r^2}{v_*}-\frac{\gamma}{v_*^2}\right)
=\mathcal H(\varepsilon_*)<H_d.
\quad}
\tag{14.10}
$$

An equivalent algebraic specification uses the unique real root $z_*$ in the isolating interval $(1-1/a,1)$ of

$$
r^2qz^3-(r^2q-2a\gamma)z+4\gamma=0.
\tag{14.11}
$$

In terms of this root,

$$
\begin{aligned}
u_*&=\frac q{2+az_*},
&v_*&=\frac{qz_*}{2+az_*},
&\varepsilon_*&=\frac q{2+az_*}-\mu,\\
\mathscr D_a(\delta)
&=\frac{r^2(2+az_*)}{q}
  \left[2+\frac a2\left(z_*+z_*^{-1}\right)\right].
\end{aligned}
\tag{14.12}
$$

All labeled minimizing laws, and only those laws, are indexed by a two-element set $P\subseteq[s]$ and have masses

$$
\begin{aligned}
x_{[s]\setminus P}&=\delta,\\
x_{[s]\setminus\{i\}}&=m-\varepsilon_*
&& (i\in P),\\
x_{[s]\setminus\{j\}}&=\frac{1+\delta}{s}
                       +\frac{2\varepsilon_*}{a}
&& (j\notin P),\\
x_T&=0&&\text{for every other }T.
\end{aligned}
\tag{14.13}
$$

Every displayed nonzero mass is strictly positive. The actual marginals are $u_*$ on $P$ and $v_*$ off $P$, with $u_*>v_*>\tau$. Consequently there are exactly $\binom{s}{2}$ labeled minimizers, and there is a unique minimizer up to relabeling. The minimum of $d(x)$ on this domain is $\mathcal H(\varepsilon_*)-B$.

The quantifiers include arbitrarily small positive $\delta$ in the stated interval. The least sufficient threshold, the remaining smaller values of $a$, an exact rare/dense crossing curve, and prescribed finite-graph realization remain undetermined.

**Proof.** First establish parameter bounds uniformly throughout the interval, without a lower bound on $\delta$. Put $w=1-L$. Since $aw\ge64$, $\delta\le L/a<1/a$, and $s\le2a$, one has

$$
\begin{gathered}
1-r\delta\ge1-L-\frac La>\frac w2,
\qquad m>\frac w{4a},\\
0<\rho<\frac2{a^2},\qquad
e_0<\frac8{a^2}\le\frac w{8a}<m,
\qquad \mu\ge\frac a{a+2}\ge\frac79,\\
0<\tau=\frac{3(2r+1)\delta}{r^2}
 <\frac9{a^2}<\frac12.
\end{gathered}
\tag{14.14}
$$

For every $0\le\varepsilon\le e_0$ these imply

$$
\tau<v(\varepsilon)
\ge\mu-\frac{2e_0}{a}
>\frac79-\frac{16}{a^3}>\frac12,
\qquad
\tau<u(\varepsilon)\le\mu+e_0
<\mu+m=1-\delta<1.
\tag{14.15}
$$

Consider the interval of grouped dense marginals

$$
\mathcal I=
\left[0,\min\left\{1-\mu,\frac a2(\mu-\tau)\right\}\right].
\tag{14.16}
$$

It contains $[0,e_0]$ by (14.15); on $\mathcal I$, both $u$ and $v$ belong to $[\tau,1]$. The auxiliary functions

$$
g_0(t)=\frac{r^2}t,\qquad
g_1(t)=\frac{r^2}t-\frac{\gamma}{t^2}
\tag{14.17}
$$

are strictly convex on $[\tau,1]$, since

$$
g_0''(t)=\frac{2r^2}{t^3}>0,\qquad
g_1''(t)=\frac{2(r^2t-3\gamma)}{t^4}>0,
\qquad r^2\tau-3\gamma=6\delta>0.
\tag{14.18}
$$

In particular direct differentiation of (14.2) gives, throughout $\mathcal I$,

$$
\begin{aligned}
\mathcal H'(\varepsilon)
&=2r^2(v^{-2}-u^{-2})-4\gamma v^{-3},\\
\mathcal H''(\varepsilon)
&=\frac{4r^2}{u^3}
 +\frac{8(r^2v-3\gamma)}{av^4}>4r^2.
\end{aligned}
\tag{14.19}
$$

Here $u=u(\varepsilon)$ and $v=v(\varepsilon)$. Thus $\mathcal H'$ is strictly increasing, and

$$
\mathcal H'(0)=-\frac{4r^2\rho}{\mu^3}<0,\qquad
\mathcal H'(e_0)
>4r^2\rho(4-\mu^{-3})>0,
\tag{14.20}
$$

because $\mu^{-3}\le(9/7)^3<4$. There is exactly one zero $\varepsilon_*\in(0,e_0)$; it is the unique minimizer of $\mathcal H$ on all of $\mathcal I$. Its derivative equation is (14.8). Integrating the strict second-derivative bound from zero to $\varepsilon_*$ yields $\varepsilon_*<\rho/\mu^3$, proving (14.9). Also $\mathcal H(\varepsilon_*)<\mathcal H(0)=H_d$, using the existing family identity (7.5).

Now let $x$ be any dense law in the original domain, with no assumption on its support or energy. Form its weights (14.3), and choose $P$ to consist of two largest marginals, breaking ties arbitrarily. Then $[s]\setminus P$ maximizes $W_U$ over $a$-subsets, so (14.6) reads

$$
\begin{aligned}
H(x)
&=F_P(y)+\mathbb E_xG_y(T),\\
F_P(y)
&=\sum_{i\in P}g_0(y_i)
  +\sum_{j\notin P}g_1(y_j).
\end{aligned}
\tag{14.21}
$$

Let $u=\frac12\sum_{i\in P}y_i$ and $v=\frac1a\sum_{j\notin P}y_j$. These are averages of the same actual marginals. The choice of $P$ gives $u\ge v$, and $2u+av=q$, hence $u=\mu+\varepsilon$, $v=\mu-2\varepsilon/a$ for some $\varepsilon\in\mathcal I$. Applying Jensen's inequality separately to the two strictly convex functions in (14.17) gives

$$
H(x)\ge F_P(y)
\ge2g_0(u)+ag_1(v)
=\mathcal H(\varepsilon)
\ge\mathcal H(\varepsilon_*).
\tag{14.22}
$$

The middle inequality is an equality exactly when the two marginals on $P$ both equal $u$ and all $a$ marginals off $P$ equal $v$. Jensen's inequality is used in its standard finite convex-combination form; see S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, §3.1.8, pp.77–78, [author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf). Strictness here follows from the positive second derivatives in (14.18). Convexity is asserted for $g_0,g_1$ and $\mathcal H$, without imposing convexity on $H$ as a function of the law.

To prove actual attainment, fix $P$ and use (14.13). Positivity follows from (14.9), including $\delta>0$. The masses on the $r$-subsets add to

$$
2(m-\varepsilon_*)
+a\left(\frac{1+\delta}{s}
        +\frac{2\varepsilon_*}{a}\right)=1-\delta.
\tag{14.23}
$$

Thus the total mass is one and its cardinality mean is $a\delta+r(1-\delta)=q$. A label in $P$ is absent from the sole $a$-atom and from its own missing-one type, giving marginal

$$
1-\delta-(m-\varepsilon_*)=u_*.
$$

A label off $P$ is absent only from its own missing-one type, giving marginal

$$
1-\left(\frac{1+\delta}{s}
       +\frac{2\varepsilon_*}{a}\right)=v_*.
$$

These actual marginals satisfy the density condition by (14.15). Moreover $w_i=r^2u_*$ on $P$ and $w_j=r^2v_*-\gamma$ off $P$. Therefore its energy is precisely $\mathcal H(\varepsilon_*)$, proving (14.10) together with the unrestricted-cardinality lower bound (14.22).

For completeness, suppose any actual dense law attains this value. Every inequality in (14.22) must then be an equality. Strict convexity gives $\varepsilon=\varepsilon_*$ and constant marginals within each group. Since $\varepsilon_*>0$, the two marginals on $P$ are strictly larger than all the others. Consequently $[s]\setminus P$ is the unique $a$-subset maximizing $W_U$. By (14.5) and $\mathbb E_xG_y(T)=0$, every positive-mass atom has cardinality $r$, except possibly this one $a$-subset. The mean constraint forces the mass of that $a$-subset to be $\delta$. Each $r$-subset is a missing-one type, and its mass is forced by the actual marginal to be

$$
x_{[s]\setminus\{i\}}
=1-y_i-\delta\,\mathbf1_{\{i\in P\}}.
\tag{14.24}
$$

These are exactly the masses in (14.13). The construction already proves the converse. The pair $P$ is recoverable as the two largest marginals, so different pairs give different labeled laws and all are related by label permutations.

Finally put $z_*=v_*/u_*$. The identity $2u_*+av_*=q$ gives the first line of (14.12), and (14.8) becomes

$$
\gamma=\frac{r^2qz_*(1-z_*^2)}{2(2+az_*)},
\tag{14.25}
$$

which is equivalent to (14.11). Also

$$
1-z_* =\frac{s\varepsilon_*}{au_*}
<\frac{se_0}{a\mu}<\frac1a,
\qquad se_0<\frac{16}a\le\frac14<\mu.
\tag{14.26}
$$

Thus $z_*\in(1-1/a,1)$. The derivative of the polynomial in (14.11) is

$$
r^2q(3z^2-1)+2a\gamma>0
\quad\text{for }1-1/a\le z\le1,
$$

since $a\ge64$. Its root in this interval is therefore unique. Substitute (14.25) into (14.2) to obtain

$$
\mathcal H(\varepsilon_*)
=\frac{r^2(2+az_*)}{q}
 \left[2+\frac a{z_*}
       -\frac{a(1-z_*^2)}{2z_*}\right],
$$

which simplifies to the second line of (14.12). This completes the exact algebraic specification and the equality classification. ∎

## 追加锚（本行以下为增补区）

## 15. The finite rare/dense crossing on the whole continuous window

**Definition 15.1 (Crossing threshold and branch values).** Fix

$$
\frac12<L<1,
\qquad
A_\times(L)=\left\lceil
\max\left\{10^4,\frac{64}{1-L},\frac{8L}{2L-1}\right\}
\right\rceil.
\tag{15.1}
$$

For an integer $a\ge A_\times(L)$ and $0<\delta\le L/a$, retain
$r=a+1$, $s=a+2$, $q=r-\delta$, $C=2r-1$, and
$
\gamma=C\delta,
\mu=q/s,
\tau=3(2r+1)\delta/r^2.
$
Define the scalar energy

$$
h(\varepsilon,\delta)
=\frac{2r^2}{\mu+\varepsilon}
 +a\left[\frac{r^2}{\mu-2\varepsilon/a}
 -\frac{C\delta}{(\mu-2\varepsilon/a)^2}\right].
$$
Let $\varepsilon_*(\delta)$ be the unique point supplied by Theorem 14.3, and put

$$
\begin{aligned}
 u_*(\delta)&=\mu+\varepsilon_*(\delta),
 &v_*(\delta)&=\mu-\frac{2\varepsilon_*(\delta)}a,\\
 M_a(\delta)&=\frac{2r^2}{u_*(\delta)}
 +a\left(\frac{r^2}{v_*(\delta)}-
 \frac{C\delta}{v_*(\delta)^2}\right),\\
 R_a(\delta)&=\frac a\delta+
 \frac{r^3}{1-\delta/a}.
\end{aligned}
\tag{15.2}
$$

Thus $M_a=\mathscr D_a$ is the exact dense value from Theorem 14.3, while
$R_a=H_r$ is the exact rare value from Theorem 9.1.

**Theorem 15.2 (Unique finite crossing and the complete phase diagram).** For every
$1/2<L<1$ and every integer $a\ge A_\times(L)$ there is a unique number

$$
\delta_c(a)\in\left(0,\frac1{2a}\right)\subset\left(0,\frac La\right)
\tag{15.3}
$$

such that

$$
M_a(\delta_c(a))=R_a(\delta_c(a)).
\tag{15.4}
$$

For every $0<\delta\le L/a$, on the full law domain of Definition 1.1,
including arbitrary cardinalities, zero type masses, disconnected support and
non-symmetric laws,

$$
\boxed{\quad
\inf_x H(x)=\min\{M_a(\delta),R_a(\delta)\},
\qquad
D_a(\delta)=\min\{M_a(\delta),R_a(\delta)\}-B(\delta).
\quad}
\tag{15.5}
$$

The infimum is attained. Its equality laws are exactly as follows.

* If $0<\delta<\delta_c(a)$, they are the $\binom{s}{2}$ laws $D_P$ indexed by
  $P\subset[s]$, $|P|=2$, with

  $$
  x_{[s]\setminus P}=\delta,
  \quad
  x_{[s]\setminus\{i\}}=\frac{1-r\delta}{s}-\varepsilon_*(\delta)\ (i\in P),
  \quad
  x_{[s]\setminus\{j\}}=\frac{1+\delta}{s}+\frac{2\varepsilon_*(\delta)}a\ (j\notin P),
  \tag{15.6}
  $$

  with all other masses zero.
* If $\delta_c(a)<\delta\le L/a$, they are the $s$ laws $R_e$ indexed by
  $e\in[s]$, with

  $$
  x_{\{e\}}=\frac\delta a,
  \qquad
  x_{[s]\setminus\{e\}}=1-\frac\delta a,
  \tag{15.7}
  $$

  and all other masses zero.
* At $\delta=\delta_c(a)$ the equality class is the disjoint union of the two
  displayed families. There is no additional mixed equality law.

Put $F_a=R_a-M_a$. Then $F_a$ is continuous on $(0,L/a]$, is $C^1$ on
$(0,L/a)$, and

$$
F_a'(\delta)<-a^3+44a^2<0.
\tag{15.8}
$$

Consequently $F_a>0$ before $\delta_c(a)$ and $F_a<0$ after it.

**Proof.** Write $m(\delta)=(1-r\delta)/s$. Since
$\delta\le L/a<1/a$ and $a\ge64/(1-L)$,

$$
 r\delta\le L+\frac1a
 \le L+\frac{1-L}{64}<1,
\tag{15.9}
$$

so $m>0$. On $0\le\varepsilon\le m$, the quantities in (14.2) obey

$$
 u=\mu+\varepsilon\le\mu+m=1-\delta<1,
 \qquad
 v=\mu-\frac{2\varepsilon}{a}
 \ge\frac{a+1-3/a}{a+2}>\frac12,
 \qquad \mu>\frac12.
\tag{15.10}
$$

Also $0<\gamma< C/a<3$. Direct differentiation of the scalar energy in
(14.2) gives

$$
\partial_\varepsilon h
 =2r^2(v^{-2}-u^{-2})-4\gamma v^{-3},
\qquad
\partial_{\varepsilon\varepsilon}h
 =\frac{4r^2}{u^3}
 +\frac{8(r^2v-3\gamma)}{av^4}.
\tag{15.11}
$$

The second expression is strictly positive, because
$r^2v-3\gamma>a^2/2-9>0$. The point $\varepsilon_*(\delta)$ is interior by
Theorem 14.3, so the implicit-function theorem and (15.11) make it $C^1$ in
$\delta$; uniqueness makes the local branches agree. It is continuous at the
right endpoint by the same interior bounds. Moreover
$u_*>v_*>1/2$, and hence $v_*/u_*\in(1/2,1)$.

The partial derivative with respect to $\delta$, at fixed $\varepsilon$, has
the exact identity

$$
\partial_\delta h
 =\frac{r^2}{u^2}-\frac{aC}{v^2}
 +\frac{a}{2s}\,\partial_\varepsilon h.
\tag{15.12}
$$

At the stationary point the last term vanishes. Therefore the envelope value
satisfies

$$
M_a'(\delta)=\frac{r^2}{u_*^2}-\frac{aC}{v_*^2}
 \ge-4aC\ge-12a^2,
\tag{15.13}
$$

where $C=2a+1\le3a$. On the other hand,

$$
R_a'(\delta)=-\frac a{\delta^2}
 +\frac{r^3}{a(1-\delta/a)^2}
 <-a^3+32a^2.
\tag{15.14}
$$

Indeed $\delta<1/a$ gives the first bound, while $r\le2a$ and
$1-\delta/a>1-1/a^2\ge3/4$ give the second. Equations (15.13)–(15.14)
prove (15.8), since $a\ge10^4$.

It remains to establish opposite endpoint signs. At $\varepsilon=0$,
$\partial_\varepsilon h=-4\gamma/\mu^3$. Using
$\partial_{\varepsilon\varepsilon}h\ge4r^2$ and the mean-value theorem at the
zero $\varepsilon_*$ gives

$$
0<\varepsilon_*(\delta)
 \le\frac{\gamma}{r^2\mu^3}.
\tag{15.15}
$$

Thus $\varepsilon_*(\delta)\to0$ as $\delta\downarrow0$ and
$M_a(\delta)\to h(0,0)=rs^2$, whereas $R_a(\delta)\to+\infty$. Hence
$F_a(\delta)\to+\infty$ at the left endpoint.

For a finite negative value, set $\delta_0=1/(2a)$. It lies in the prescribed
window because $L>1/2$. With

$$
 P_a=24a^6+56a^5-72a^3-38a^2+12a+9,
 \qquad
 Q_a=(2a^2-1)(2a^2+2a-1)^2,
\tag{15.16}
$$

substitution into the exact rational expressions for $R_a$ and $H_d$ gives

$$
R_a(\delta_0)-H_d(\delta_0)+a=-a\frac{P_a}{Q_a}.
\tag{15.17}
$$

Both $P_a$ and $Q_a$ are positive for $a\ge2$: group the first two negative
terms as
$24a^3(a^3-3)$ and $56a^5-38a^2$, with the remaining terms positive.
The dense minimizer is dense, and at $\delta_0$ the hypothesis of Theorem 8.1
holds because $b=(2r+1)\delta_0<2$ and $\mu>1/2$, so
$b/(r^2\mu)<4/a^2\le1/12$. Therefore

$$
M_a(\delta_0)\ge H_d(\delta_0)-72\delta_0^2\mu^{-6}
 >H_d(\delta_0)-\frac{1152}{a^2}.
\tag{15.18}
$$

Equations (15.17)–(15.18) imply
$F_a(\delta_0)<-a+1152/a^2<0$. Continuity and the intermediate value theorem
produce a zero in $(0,\delta_0)$, and (15.8) makes it unique and fixes the
signs on both sides.

For each fixed $\delta$, Theorem 14.3 gives the exact lower bound $M_a$ and
all dense equality laws, while Theorem 9.1 gives the exact lower bound $R_a$ and
all rare equality laws. The conditions $\min_i y_i\ge\tau$ and
$\min_i y_i<\tau$ partition the full original law domain, so the two attained
bounds give (15.5) and the three equality alternatives. In particular, a law
mixing distinct displayed minimizers cannot be an additional minimizer: it lies
in one of the two regions and would then have to belong to that region's
exhaustive equality class. The masses in (15.6) and (15.7) are actual laws of
mean $q$ by the constructions in Theorems 14.3 and 9.1, so no independent
marginal or cardinality optimization has been spliced into the comparison. ∎

**Proposition 15.3 (Exact algebraic prescription without spurious roots).**
For $a\ge A_\times(L)$, let $d$ and $z$ be real variables and define

$$
q_d=r-d,
\qquad
\varepsilon(d,z)=\frac{a q_d(1-z)}{s(2+az)}.
\tag{15.19}
$$

Let $\mathcal R_a$ be the legal region

$$
\mathcal R_a=\left\{(d,z):
0<d<\frac1{2a},\quad \frac12<z<1,\quad
0<\varepsilon(d,z)<\frac{1-rd}{s}\right\}.
\tag{15.20}
$$

There is exactly one pair $(d,z)\in\mathcal R_a$ satisfying the two
integer-coefficient equations

$$
\begin{aligned}
 r^2(r-d)z(1-z^2)-2C d(2+az)&=0,\\
 2a(r-d)z(a-d+r^3d)
 -r^2d(a-d)(2+az)(az^2+4z+a)&=0.
\end{aligned}
\tag{15.21}
$$

Its first coordinate is $d=\delta_c(a)$. The optimizer is recovered exactly by

$$
 u=\frac{r-d}{2+az},
 \qquad v=zu,
 \qquad \varepsilon_*=u-\frac{r-d}{s}
 =\varepsilon(d,z).
\tag{15.22}
$$

**Proof.** At the crossing put $z=v_*/u_*$. The bounds in (15.10) and the
strict positivity of $\varepsilon_*$ give $(\delta_c,z)\in\mathcal R_a$. Since
$2u_*+av_*=q$, (15.22) follows. The stationary equation (14.8), after division
by the positive factor $u_*^2$ and substitution of (15.22), is exactly the
first equation in (15.21).

Conversely, take any $(d,z)\in\mathcal R_a$ satisfying (15.21), and define
$u,v,\varepsilon$ by (15.22). The first equation is equivalent, after
multiplication only by the positive factor $2+az$, to

$$
 r^2v(u^2-v^2)=2Cd\,u^2,
\tag{15.23}
$$

which is the stationary equation for the scalar dense energy. Strict convexity
in (15.11) and the legal inequalities in (15.20) therefore force
$\varepsilon=\varepsilon_*(d)$.

Using the first equation to replace $Cd$ in the scalar energy gives

$$
M_a(d)=
\frac{r^2(2+az)(az^2+4z+a)}{2z(r-d)}.
\tag{15.24}
$$

All factors in $2z(r-d)d(a-d)$ are positive on $\mathcal R_a$, and direct
clearing of these denominators shows that the second equation in (15.21) is
exactly

$$
R_a(d)-M_a(d)=0.
\tag{15.25}
$$

Thus every legal solution gives $F_a(d)=0$, hence $d=\delta_c(a)$ by (15.8).
The crossing pair already constructed supplies existence, so the legal solution
is unique. The positivity restrictions in (15.20) are retained throughout the
clearing step; roots outside them are not admissible and are not counted. ∎

The finite crossing uses the exact full-law results of Theorems 9.1 and 14.3.
The envelope calculation is proved directly from the displayed scalar function;
Milgrom and Segal, *Envelope Theorems for Arbitrary Choice Sets*,
Econometrica 70 (2002), 583–601, provides the classical envelope background but
is not used to supply the moving-domain regularity or the slope bound here.
The endpoint identity (15.17) is a rational identity, and the dense estimate
(15.18) is Theorem 8.1; no asymptotic expansion, numerical grid or convexity of
$H$ as a function of the law is used.

## 追加锚（本行以下为增补区）


## 16. Exact dense support transitions through the terminal endpoint

**Definition 16.1 (Capacity-sensitive marginal functions).** Retain Definition 1.1 and the dense domain (11.1). Throughout this section assume

$$
a\ge4096,\qquad a\in\mathbb Z,\qquad 0<\delta\le\frac1a,
\qquad r=a+1,\quad s=a+2,\quad n=a-1,
\tag{16.1}
$$

and write

$$
q=r-\delta,\quad \mu=\frac qs,\quad \theta=1-\delta,
\quad c=2a+1,\quad \gamma=c\delta,
\quad \tau=\frac{3(2a+3)\delta}{r^2}.
\tag{16.2}
$$

In particular $\mathscr D_a(\delta)$ continues to mean the infimum over all laws on nonempty subsets of $[s]$ with this mean and with every actual marginal at least $\tau$. No restriction on cardinalities, symmetry or zero masses is imposed. For an omitted set $J\subsetneq[s]$ put $\bar x_J=x_{[s]\setminus J}$. Define

$$
g_0(z)=\frac{r^2}{z},\qquad
g_1(z)=\frac{r^2}{z}-\frac{\gamma}{z^2},\qquad
f(z)=\frac{a^2}{z}+\frac{c\theta}{z^2}.
\tag{16.3}
$$

For real variables $u,w$ set

$$
v=\frac{q-2u-w}{n},\qquad
\Omega=\{(u,w):\tau\le v\le w\le u\le1\},
\tag{16.4}
$$

and, on $\Omega$, define

$$
\begin{aligned}
F_0(u,w)&=2g_0(u)+g_1(w)+n g_1(v),\\
F_1(u,w)&=2f(u)+\frac{r^2}{w}
 +\frac{c(2u+\delta-2)}{w^2}+n g_1(v),\\
F(u,w)&=\max\{F_0(u,w),F_1(u,w)\}.
\end{aligned}
\tag{16.5}
$$

These are functions of grouped marginals, with $v$ determined by the same mean constraint. The graph normalization remains precisely the one in Definition 1.1 and its citation to Albalahi et al., DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176), p.109.

**Lemma 16.2 (A capacity certificate on the entire subset domain).** Let $x$ be any dense law in Definition 16.1, and relabel its actual marginals so that $y_1\ge\cdots\ge y_s$. Put

$$
\alpha_i=y_i^{-2},\quad W=\sum_i\alpha_i,\quad
\omega=\alpha_3,\quad b_i=c(\omega-\alpha_i)_+,
\quad W_T=\sum_{i\in T}\alpha_i.
\tag{16.6}
$$

For every nonempty $T\subseteq[s]$, with $k=|T|$ and $J=[s]\setminus T$, the expression

$$
\mathcal R_y(T)
=(r-k)\big[c(W-2\omega)-(r+k)W_T\big]
 +\sum_{i\in J}b_i
\tag{16.7}
$$

is nonnegative. Its entire zero set is

$$
\mathcal R_y(T)=0
\quad\Longleftrightarrow\quad
\begin{cases}
k=r,\ J=\{i\},\ y_i\le y_3,\quad\text{or}\\
k=a,\ J=\{i,j\},\ y_i,y_j\ge y_3.
\end{cases}
\tag{16.8}
$$

For the grouped point

$$
u=\frac{y_1+y_2}{2},\qquad w=y_3,\qquad
v=\frac1n\sum_{i=4}^s y_i
\tag{16.9}
$$

one has $(u,w)\in\Omega$ and $H(x)\ge F(u,w)$. In the inequality $H(x)\ge F_1(u,w)$, equality forces $y_1=y_2=u$ and $y_4=\cdots=y_s=v$ as well as $\mathcal R_y(T)=0$ on every positive-mass atom.

**Proof.** The actual mean and ordering give $q\le2+a y_3$. Thus, with $\ell=1-2/a$,

$$
y_3\ge\frac{a-1-\delta}{a}\ge\ell,\qquad
\omega\le\ell^{-2}\le(32/31)^2<16/15,
\qquad \alpha_i\ge1.
\tag{16.10}
$$

For $k=r$, the residual is $b_i$ on the atom omitting $i$, proving the first zero case. For $k=a$, direct substitution gives

$$
\mathcal R_y(T)
=c\sum_{i\in J}(\alpha_i-\omega)_+,
\tag{16.11}
$$

proving the second case. At $k=s$ it equals $2W+2c\omega>0$.

For the remaining cardinalities $k<a$, put $d=|J|$, so $3\le d\le s-1$. The bracket in (16.7) is

$$
(d-2)W+(2s-1-d)\sum_{i\in J}\alpha_i-2c\omega
\ge3sd-2s-d-d^2-2c\omega.
\tag{16.12}
$$

The quadratic in $d$ on the right is concave. Its minimum on $[3,s-1]$ is at least $7s-12$: the endpoint values before subtracting $2c\omega$ are $7s-12$ and $2s(s-2)$. Consequently the bracket is at least

$$
7s-12-\frac{32c}{15}
=\frac{41a-2}{15}>0.
\tag{16.13}
$$

Since $r-k>0$ and $b_i\ge0$, the residual is strictly positive there. This proves nonnegativity and exhausts the zero set over every allowed nonempty subset.

Expanding (16.7) and using $\mathbb E(r-K)=\delta$ and $\mathbb P(i\in J)=1-y_i$ gives the exact identity under the original law

$$
H(x)=r^2\sum_i\frac1{y_i}
 -c\delta(W-2\omega)-\sum_i(1-y_i)b_i
 +\mathbb E_x\mathcal R_y(T).
\tag{16.14}
$$

Only $b_1,b_2$ can be nonzero. Its non-residual part therefore equals

$$
f(y_1)+f(y_2)+\frac{r^2}{y_3}
 +\frac{c(y_1+y_2+\delta-2)}{y_3^2}
 +\sum_{i=4}^s g_1(y_i).
\tag{16.15}
$$

Here $f''>0$, and

$$
g_1''(z)=\frac{2(r^2z-3\gamma)}{z^4}>0
\quad(\tau\le z\le1),\qquad
r^2\tau-3\gamma=6\delta>0.
\tag{16.16}
$$

Apply finite Jensen separately to $f(y_1)+f(y_2)$ and to the last $n$ terms in (16.15). The coupling depends on $y_1,y_2$ only through their sum, and $y_3=w$ is fixed. This gives $H(x)\ge F_1(u,w)$, with exactly the asserted necessary equality conditions. Lemma 14.2, with the two largest marginals as its omitted pair, gives the other inequality $H(x)\ge F_0(u,w)$ by the same grouping, using $g_0$ instead of $f$.

The expectation step is the classical pointwise-certificate form of weak duality; see Bertsimas and Popescu, *Optimal inequalities in probability theory: A convex optimization approach*, DOI [10.1137/S1052623401399903](https://doi.org/10.1137/S1052623401399903), Theorem 2.1. Finite Jensen is used in the form of Boyd and Vandenberghe, *Convex Optimization*, §3.1.8, pp.77–78, [author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf). The explicitly proved residual supplies the first principle's hypothesis, and (16.16) supplies the second principle's convexity hypothesis. Both are applied to the same actual law; no convexity of $H$ as a function of $x$ is asserted. ∎

**Lemma 16.3 (Strict convexity and the ordered minimum of the second certificate).** The set $\Omega$ is nonempty, compact and convex. Both $F_0$ and $F_1$ are strictly convex there, as is $F$. In fact

$$
\nabla^2F_1\succeq a^2 I_2\quad\text{on }\Omega.
\tag{16.17}
$$

The unique minimum $(u_1,w_1)$ of $F_1$ on $\Omega$ satisfies

$$
\sqrt{(u_1-\mu)^2+(w_1-\mu)^2}<\frac{64}{a^2},
\qquad u_1>w_1,\qquad u_1,w_1<1.
\tag{16.18}
$$

**Proof.** The point $(\mu,\mu)$ belongs to $\Omega$. Every point of $\Omega$ satisfies

$$
1\ge u\ge w\ge v\ge\frac{q-3}{n}
=1-\frac{1+\delta}{a-1}\ge\ell=1-\frac2a>\tau,
\tag{16.19}
$$

which also proves compactness. On $[\ell,1]$, elementary bounds give

$$
a^2\le g_1''(z)<3a^2,\qquad f''(z)\ge2a^2,
\qquad c\le\frac{33a}{16},\qquad
\ell^{-3}<\frac{10}{9},\quad\ell^{-4}<\frac87.
\tag{16.20}
$$

For example, $g_1''(z)\ge2a^2-6\gamma\ell^{-4}>a^2$ and $g_1''(z)\le2r^2\ell^{-3}<3a^2$. These bounds already hold for $a\ge64$ in the parameter range at issue.

Put $D=2u+\delta-2$. Differentiating with $v=(q-2u-w)/n$ gives

$$
\begin{aligned}
(F_1)_{uu}&=2f''(u)+\frac4n g_1''(v),\\
(F_1)_{uw}&=-\frac{4c}{w^3}+\frac2n g_1''(v),\\
(F_1)_{ww}&=\frac{2r^2}{w^3}
 +\frac{6cD}{w^4}+\frac1n g_1''(v).
\end{aligned}
\tag{16.21}
$$

Since $D\ge-4/a$, (16.20) implies

$$
(F_1)_{uu}\ge4a^2,\qquad
|(F_1)_{uw}|<10a,\qquad
(F_1)_{ww}\ge2a^2-\frac{396}{7}.
\tag{16.22}
$$

For the middle bound, the two terms of opposite signs in $(F_1)_{uw}$ each have absolute value less than $10a$. Subtracting the off-diagonal row sums from the diagonal entries proves (16.17). The Hessian quadratic form of $F_0$ is

$$
\frac{4r^2}{u^3}(du)^2+g_1''(w)(dw)^2
 +\frac{g_1''(v)}n(2du+dw)^2,
\tag{16.23}
$$

so $F_0$ is strictly convex too. The maximum of two strictly convex functions is strictly convex, which proves the assertion for $F$.

At $p_0=(\mu,\mu)$ both functions equal the actual uniform-law value $H_d$. Direct differentiation gives

$$
\nabla F_1(p_0)
=-\frac{4c}{\mu^3}\big(1-\mu,\ \mu+\delta-1\big),
\qquad \|\nabla F_1(p_0)\|<32.
\tag{16.24}
$$

Indeed $1-\mu=(1+\delta)/s<1/a$ and $|\mu+\delta-1|=|r\delta-1|/s<1/a$. Strong convexity, together with $F_1(u_1,w_1)\le F_1(p_0)$, yields

$$
\frac{a^2}{2}\|(u_1,w_1)-p_0\|^2
\le\|\nabla F_1(p_0)\|\,\|(u_1,w_1)-p_0\|.
\tag{16.25}
$$

This proves the distance bound. Since $1-\mu\ge1/s>64/a^2$, both $u_1,w_1$ are less than one. The lower marginal boundary is already excluded by (16.19).

If $u_1=w_1=v$, the point is $p_0$, where increasing $u$ with $w$ fixed is feasible and has derivative $-4c(1-\mu)/\mu^3<0$. If $u_1=w_1=z>v$, the feasible direction $(du,dw)=(1,-2)$ keeps $v$ fixed and has derivative

$$
\frac{4c(3z+2\delta-3)}{z^3}<0.
\tag{16.26}
$$

For its sign, (16.18)'s distance bound gives

$$
3(1-z)-2\delta
\ge\frac{3-c\delta}{s}-\frac{192}{a^2}
\ge\frac1{2a}-\frac{192}{a^2}>0.
$$

Neither case can minimize $F_1$. Thus $u_1>w_1$. ∎

**Lemma 16.4 (The two exact support thresholds).** For $0<t<1/r$ put

$$
U(t)=1-t,\qquad V(t)=1-\frac{1-t}{a},\qquad
C_0=r^2,\quad C_1=r^2+c,
\tag{16.27}
$$

and define the polynomials

$$
P_j(t)=C_j V(t)\big[U(t)^2-V(t)^2\big]
 -2ct\,U(t)^2\qquad(j=0,1).
\tag{16.28}
$$

Each has exactly one real root in $(0,1/r)$. Denote the root of $P_0$ by $\delta_1$ and that of $P_1$ by $\delta_2$. They obey

$$
\frac{a-4}{a^2}<\delta_1<\delta_2<\frac{a-2}{a^2}
<\frac1r<\frac1a.
\tag{16.29}
$$

For each $0<\delta\le1/a$ there is also exactly one root $u_0\in(\mu,\mu+4/a^2)$ of

$$
r^2v_0(u_0^2-v_0^2)=2\gamma u_0^2,
\qquad v_0=\frac{q-2u_0}{a}.
\tag{16.30}
$$

It satisfies $u_0<\mu+3/a^2$. For $\delta<1/r$, it is less than, equal to, or greater than $\theta$ according as $\delta$ is less than, equal to, or greater than $\delta_1$.

**Proof.** On $(0,1/r)$ one has $U>V>0$. Dividing $P_j(t)=0$ by $tU(t)^2$ gives

$$
C_j\frac{V(t)}t\left[1-\left(\frac{V(t)}{U(t)}\right)^2\right]=2c.
\tag{16.31}
$$

The two positive factors on the left strictly decrease: $V(t)/t=(a-1)/(at)+1/a$, while $V(t)/U(t)$ strictly increases. Their product tends to infinity at zero and to zero at $1/r$. This proves existence and uniqueness in the stated region. At the first root, $P_1-P_0=cV(U^2-V^2)>0$, so $\delta_1<\delta_2$.

At $t=(a-4)/a^2$, one has $U-V>3/a^2$ and $U,V\ge31/32$. Hence the positive term in (16.28) exceeds $6(31/32)^2$, whereas $2ctU^2\le4+2/a$. Both polynomials are positive there. At $t=(a-2)/a^2$, one has $U-V\le33/(32a^2)$ and $C_j\le9a^2/8$. Their positive term is at most $297/128$, whereas $2ctU^2\ge4(31/32)^3$. Both polynomials are negative there. This proves (16.29).

For the scalar root consider

$$
\Phi(u)=2g_0(u)+a g_1\left(\frac{q-2u}{a}\right).
\tag{16.32}
$$

On the ordered interval $\mu\le u\le1$, the lower argument is at least $\ell$, and $\Phi''(u)>4r^2$. Also $\Phi'(\mu)=-4\gamma/\mu^3<0$. The point $\mu+4/a^2$ is less than one, and integration of this second-derivative bound gives $\Phi'(\mu+4/a^2)>0$. Thus the root is unique and

$$
0<u_0-\mu<\frac{\gamma}{r^2\mu^3}<\frac3{a^2}.
\tag{16.33}
$$

The derivative equation is exactly (16.30), with positive $u_0,v_0$. For $\delta<1/r$, the point $u=\theta$ belongs to this ordered interval and its lower argument is $V=V(\delta)$. Half its derivative is

$$
E_0=r^2(V^{-2}-\theta^{-2})-\frac{2\gamma}{V^3}
=\frac{P_0(\delta)}{\theta^2V^3}.
\tag{16.34}
$$

Strict increase of $\Phi'$ proves the final comparison. ∎

**Theorem 16.5 (The exact dense minimum and all labeled equality laws).** Under Definition 16.1, the dense infimum is attained and has precisely the following three branches. All unlisted atom masses in each displayed law are zero.

If $0<\delta<\delta_1$, use the unique $u_0,v_0$ of (16.30). Then

$$
\mathscr D_a(\delta)=2g_0(u_0)+a g_1(v_0).
\tag{16.35}
$$

All equality laws are indexed by unordered pairs $P\subseteq[s]$ and are

$$
\bar x_P=\delta,\qquad
\bar x_{\{i\}}=\theta-u_0\quad(i\in P),\qquad
\bar x_{\{j\}}=1-v_0\quad(j\notin P).
\tag{16.36}
$$

Every displayed mass is positive. Their actual marginals are $u_0$ on $P$ and $v_0$ elsewhere.

If $\delta_1\le\delta\le\delta_2$, put $V=V(\delta)$. Then

$$
\mathscr D_a(\delta)=2g_0(\theta)+a g_1(V).
\tag{16.37}
$$

All equality laws are indexed by unordered pairs $P$ and are

$$
\bar x_P=\delta,\qquad
\bar x_{\{j\}}=\frac\theta a\quad(j\notin P).
\tag{16.38}
$$

Their actual marginals are $\theta$ on $P$ and $V$ elsewhere. In particular the two singleton-omission masses on $P$ are zero throughout this closed interval, including both thresholds.

If $\delta_2<\delta\le1/a$, there is exactly one real triple $(u,w,v)$ in the legal region

$$
2u+w+n v=q,\qquad \tau<v<w<u<1,\qquad u>\theta
\tag{16.39}
$$

satisfying the polynomial equations

$$
\begin{aligned}
[a^2u+2c\theta]w^3
 &=[(r^2+c)w+2c(2u+\delta-2)]u^3,\\
[r^2w+2c(2u+\delta-2)]v^3
 &=[r^2v-2\gamma]w^3.
\end{aligned}
\tag{16.40}
$$

This triple also satisfies the isolating bound (16.18). With $\eta=u+\delta-1>0$, the exact value is

$$
\boxed{\quad
\mathscr D_a(\delta)
=2\left(\frac{a^2}{u}+\frac{c\theta}{u^2}\right)
 +\frac{r^2}{w}-\frac{c(\delta-2\eta)}{w^2}
 +n\left(\frac{r^2}{v}-\frac{\gamma}{v^2}\right).
\quad}
\tag{16.41}
$$

Every equality law is obtained by choosing an unordered pair $P=\{p_1,p_2\}$ and a label $h\notin P$. Its positive masses are exactly

$$
\begin{aligned}
\bar x_P&=\delta-2\eta,\\
\bar x_{\{p_1,h\}}=\bar x_{\{p_2,h\}}&=\eta,\\
\bar x_{\{h\}}&=1-w-2\eta,\\
\bar x_{\{j\}}&=1-v\qquad(j\notin P\cup\{h\}).
\end{aligned}
\tag{16.42}
$$

The actual marginals are $u$ on $P$, $w$ on $h$ and $v$ on the other labels. There are exactly $\binom{s}{2}$ labeled minimizers in each of the first two branches, and exactly $a\binom{s}{2}$ in the third. Each branch has one minimizer up to relabeling. The dense minimum of $d(x)$ is the displayed value of $\mathscr D_a(\delta)$ minus $B$.

**Proof.** Every grouped point in Lemma 16.2 lies in the same convex set $\Omega$, and that lemma bounds every actual dense law by $F$ there.

For the first branch, Jensen across all $a$ lower coordinates gives

$$
F_0(u,w)\ge\Phi(u)\ge\Phi(u_0).
\tag{16.43}
$$

The ordered mean implies $u\ge\mu$, so Lemma 16.4 applies on the entire possible interval. It also gives $u_0<\theta$, while $u_0>v_0$. Thus (16.36) has positive masses. Its pair mass is $\delta$ and its singleton-omission masses sum to $1-\delta$. Its omission probabilities are $1-u_0$ on $P$ and $1-v_0$ off $P$. It is therefore an actual law of total mass one, mean $a\delta+r(1-\delta)=q$, and exactly the claimed marginals, all greater than $\tau$. Labels on $P$ never belong to its sole cardinality-$a$ atom. Consequently their incidence second moments are $r^2u_0$, whereas the others have $r^2v_0-\gamma$. Its energy is exactly (16.35), attaining (16.43).

For the middle branch put $p_\theta=(\theta,V)$. This point belongs to $\Omega$ since $\delta_2<1/r$. At it,

$$
F_0(p_\theta)=F_1(p_\theta)
=2g_0(\theta)+a g_1(V),
\qquad
\nabla F_0(p_\theta)=(2E_0,0),\quad
\nabla F_1(p_\theta)=(2E_1,0),
\tag{16.44}
$$

where

$$
E_j=C_j(V^{-2}-\theta^{-2})-\frac{2\gamma}{V^3}
=\frac{P_j(\delta)}{\theta^2V^3}.
\tag{16.45}
$$

Lemma 16.4 gives $E_0\le0\le E_1$. The supporting-plane inequalities for these convex functions show that $F_0(u,w)$ is at least their common value when $u\le\theta$, and $F_1(u,w)$ is at least that value when $u\ge\theta$. Hence $F$ is minimized at $p_\theta$, uniquely by strict convexity. The law (16.38) has pair mass $\delta$ and singleton-omission mass $a(\theta/a)=1-\delta$. Its actual omissions are $\delta$ on $P$ and $\theta/a$ elsewhere; thus its marginals, mean and energy are as claimed. Its energy attains the bound, including at both endpoints.

For the third branch take the minimum $(u_1,w_1)$ of $F_1$ from Lemma 16.3. First it has $u_1>\theta$. If $\delta_2<\delta<1/r$, then $E_1<0$. The supporting plane at $p_\theta$ gives

$$
F_1(u,w)\ge F_1(p_\theta)+2E_1(u-\theta)
\ge F_1(p_\theta)\quad(u\le\theta).
\tag{16.46}
$$

Increasing $u$ slightly from $p_\theta$ with $w$ fixed is feasible and strictly decreases $F_1$, so its minimum cannot have $u_1\le\theta$. If $\delta\ge1/r$, the ordered mean and $u_1>w_1$ give $u_1>\mu\ge\theta$, proving the same conclusion.

Next $w_1>v_1$. Indeed, on the face $w=v$ with $u>\theta$, differentiation in the feasible direction increasing $w$ with $u$ fixed gives

$$
(F_1)_w=-\frac{4c(u+\delta-1)}{w^3}<0.
\tag{16.47}
$$

Lemma 16.3 already gives $u_1>w_1$ and excludes the cube boundary. Thus the minimizer is interior in $\Omega$ and its stationary equations are

$$
f'(u)+\frac{c}{w^2}
=-\frac{r^2}{w^2}-\frac{2c(2u+\delta-2)}{w^3}
=g_1'(v).
\tag{16.48}
$$

Clearing positive denominators gives exactly (16.40). Conversely, any triple satisfying (16.39) and (16.40) gives an interior stationary point of $F_1$ on $\Omega$. Strict convexity makes that point its unique minimum. This proves both existence and uniqueness in the specified legal region and excludes any further algebraic root there. Roots outside this region are not part of the specification.

Write this triple as $(u,w,v)$ and put $\eta=u+\delta-1$. The distance bound in Lemma 16.3 and $\mu+\delta-1\le1/[a(a+2)]$ give

$$
0<\eta<\frac{65}{a^2},\qquad
\delta-2\eta>\frac1{2a}-\frac{130}{a^2}>0,
\qquad
1-w-2\eta>\frac1{a+2}-\frac{194}{a^2}>0.
\tag{16.49}
$$

Here $\delta>\delta_2>1/(2a)$ by (16.29). Also $v<\mu<1$, so $1-v>0$. These prove the positivity of every mass in (16.42). Their pair total is $\delta$, and their singleton-omission total, using $2u+w+n v=q$, is

$$
1-w-2\eta+n(1-v)=1-\delta.
\tag{16.50}
$$

The omission probabilities on $P$ are $(\delta-2\eta)+\eta=1-u$; that on $h$ is $2\eta+(1-w-2\eta)=1-w$; and those on the other labels are $1-v$. This verifies total mass, the mean $q$, and every marginal from one law. Density follows from (16.19). Its actual incidence second moments are, respectively,

$$
r^2u-c\eta=a^2u+c\theta,\qquad
r^2w-c(\delta-2\eta),\qquad r^2v-\gamma.
\tag{16.51}
$$

They give (16.41), which is $F_1(u,w)$. Thus the law attains the lower bound $H(x)\ge\min_\Omega F_1$ on the full original dense domain.

It remains to exhaust equality laws. In the first branch, equality in (16.43) and the strict Jensen inequalities fixes the marginals as two copies of $u_0$ and $a$ copies of $v_0$. In the middle branch, the unique minimizing point of $F$ is $p_\theta$. Since $F_0=F_1$ there, equality also forces equality in the $F_0$ certificate and its strict Jensen inequalities. Thus the marginals are two copies of $\theta$ and $a$ copies of $V$. In both branches the two larger marginals recover a unique pair $P$. Lemma 14.2 forces every positive-mass atom to have cardinality $r$, except for the unique cardinality-$a$ atom omitting $P$. The mean forces its mass to be $\delta$, and the actual omission probabilities force all singleton-omission masses. These are precisely (16.36) and (16.38), with no additional equality laws at either threshold.

In the third branch, strict convexity of $F_1$ and equality in Lemma 16.2 force marginals $u,u,w,v,\ldots,v$. The zero set (16.8) allows only singleton omissions outside $P$ and pair omissions inside $P\cup\{h\}$; all other cardinalities have strictly positive residual. In particular the singleton-omission masses on $P$ vanish. The mean forces total pair mass $\delta$, and the two actual omission probabilities $1-u$ force the three pair masses to be $\delta-2\eta,\eta,\eta$. The remaining marginals force every singleton-omission mass in (16.42). Hence this is the complete equality class. The strict marginal groups recover $P$, and in the third branch also recover $h$. Their possible choices give the stated labeled counts, and permutations relate all laws in each branch. ∎

The capacity certificate and equality classification in Theorem 16.5 are repo-derived deductions for the actual subset-law model. The classical sources attached to Lemma 16.2 supply only weak duality and finite Jensen. The finite-graph extrema in A. M. Albalahi, *On Two Conjectures Concerning the Hyperbolic Sombor Index and Its Counterpart*, DOI [10.47443/dml.2026.217](https://doi.org/10.47443/dml.2026.217), Proposition 2.1 and Theorem 2.2, concern prescribed graph order and cyclomatic number; they are not input theorems for this law-domain classification. The full text of Zhao–Zhao, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), is not an input here. Its possible overlap remains unassessed, and no worldwide priority assertion is made.

**Corollary 16.6 (The exact endpoint and the uniform continuous terminal layer).** For every integer $a\ge4096$, set

$$
\kappa_j=a-a^2\delta_j\quad(j=1,2).
\tag{16.52}
$$

Then $2<\kappa_2<\kappa_1<4$. Throughout the entire continuous interval

$$
\delta=\frac{1-\kappa/a}{a},\qquad 0\le\kappa\le8,
\tag{16.53}
$$

the complete dense optimizer classification is (16.36) when $\kappa>\kappa_1$, (16.38) when $\kappa_2\le\kappa\le\kappa_1$, and (16.42) when $\kappa<\kappa_2$, with the exact energies and unique legal roots of Theorem 16.5. These are genuine support changes: two positive singleton-omission masses disappear at $\kappa_1$, and two additional pair-omission masses become positive below $\kappa_2$.

At the endpoint $\delta=1/a$, substitute

$$
\theta=\frac{a-1}{a},\qquad q=a+1-\frac1a,
\qquad \gamma=\frac{2a+1}{a}
\tag{16.54}
$$

in (16.39)–(16.41). This specifies the exact dense minimum by a unique real algebraic triple in the displayed legal region. All attaining laws are exactly (16.42), with strictly positive displayed masses and

$$
\eta>\frac1{a(a+2)}.
\tag{16.55}
$$

There are exactly $a\binom{a+2}{2}$ labeled endpoint minimizers, forming one class up to relabeling. These assertions make no claim for smaller $a$, for the least sufficient threshold, for $\delta>1/a$, or for realization by a finite graph with prescribed budgets.

**Proof.** The threshold bounds and all terminal branches follow directly from (16.29) and Theorem 16.5, including both threshold equality classes. The endpoint is strictly in the third branch because $\delta_2<1/r<1/a$. Its mean and strict marginal ordering imply $u>\mu$, and

$$
\mu+\frac1a-1=\frac1{a(a+2)},
$$

which proves (16.55). All masses, moments and the energy are those of the one law already verified in (16.49)–(16.51). In contrast, the parameter $m=(1-r\delta)/s$ in (14.13) equals $-1/[a(a+2)]$ at this endpoint, so its masses $m-\varepsilon$ cannot define a law for $\varepsilon\ge0$. The three-pair branch supplies the actual endpoint law. ∎

## 追加锚（本行以下为增补区）

## 17. An exact dense phase with a continuum of actual minimizers

**Definition 17.1 (The interior capacity window and its marginal functions).** Fix a real number $0<\eta<1/4$ and put

$$
A(\eta)=\left\lceil\frac{1024}{\eta}\right\rceil.
$$

Throughout this section let

$$
\begin{gathered}
a\in\mathbb Z,\quad a\ge A(\eta),\quad
\frac32+\eta\le\lambda\le2-\eta,\quad \delta=\frac\lambda a,\\
r=a+1,\quad s=a+2,\quad n=a-2,\quad C=2a+1,\\
q=r-\delta,\quad \mu=\frac qs,\quad
\tau=\frac{3(2a+3)\delta}{r^2},\quad
H_d=\frac{\delta a^3+(1-\delta)r^3}{\mu^2}.
\end{gathered}
\tag{17.1}
$$

The domain is exactly that of Definition 1.1 with the additional inequalities $y_i\ge\tau$. Thus the random nonempty subset $T\subseteq[s]$ has arbitrary nonnegative masses of total one, actual marginals $y_i=\mathbb P(i\in T)>0$, mean $\mathbb E|T|=q$, and energy

$$
H(x)=\mathbb E_x\left[|T|^2\sum_{i\in T}y_i^{-2}\right].
$$

The dense infimum is still $\mathscr D_a(\delta)$ from (11.1). No constraint on cardinalities, connectedness, symmetry or positive atom masses is added. Write $J=[s]\setminus T$ and $\bar x_J=x_{[s]\setminus J}$ for each proper subset $J\subsetneq[s]$. For $z>0$ define

$$
\varphi(z)=\frac{a^2}{z}+\frac{C(1-\delta)}{z^2},
\qquad g(z)=\frac{r^2}{z}-\frac{C\delta}{z^2}.
\tag{17.2}
$$

For a three-element label set $P$ and a label $j\notin P$, define on the box $\mathcal B=[9/10,1]^s$

$$
\begin{aligned}
F_{P,j}(y)
={}&\sum_{i\in P}\varphi(y_i)
 +\frac{r^2}{y_j}
 +\frac{C(\delta-3+\sum_{i\in P}y_i)}{y_j^2}
 +\sum_{k\notin P\cup\{j\}}g(y_k),\\
\mathcal B_q={}&\left\{y\in\mathcal B:\sum_i y_i=q\right\}.
\end{aligned}
\tag{17.3}
$$

These are auxiliary functions of a vector; an arbitrary vector in $\mathcal B_q$ is not assumed to be the marginal vector of a law. Attainment by one actual law will be established separately. The energy normalization is the one in Definition 1.1; its graph convention comes only from Albalahi et al., DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176), p.109, where the factor $1/\sqrt2$ is removed in defining CDSO. The results of §§14 and 16 have smaller parameter ranges and do not classify the window (17.1).

**Lemma 17.2 (Explicit localization of all relevant dense competitors).** Every actual dense law in Definition 17.1 with $H(x)\le H_d$ satisfies

$$
y_i>\frac9{10}\quad(1\le i\le s).
\tag{17.4}
$$

In particular this is a consequence on an energy sublevel, rather than an additional hypothesis on the original domain.

**Proof.** The uniform adjacent-cardinality law of Lemma 1.2 has all marginals $\mu$ and energy $H_d$. The parameter bounds give

$$
\begin{gathered}
a>4096,\quad 0<\delta<2/a<1,\quad
\frac1a-\frac2{a^2}<h_0:=1-\mu
 =\frac{1+\delta}{a+2}\le\frac1a,\\
\mu\ge\frac9{10},\qquad
C\delta\le5,\qquad \tau\le\frac{15}{a^2}<\frac9{10},\qquad
\mu^{-2}-1\le\frac3a.
\end{gathered}
\tag{17.5}
$$

The last inequality follows by substituting $\mu\ge1-1/a$ and multiplying by $(1-1/a)^2>0$. Thus the uniform law is dense.

Apply Lemma 14.2 to the actual weights $\alpha_i=y_i^{-2}$. If $\alpha_{(1)},\alpha_{(2)}$ are their two smallest values, then $M=\sum_i\alpha_i-\alpha_{(1)}-\alpha_{(2)}$. Its unrestricted-cardinality certificate gives

$$
H(x)\ge\sum_i g(y_i)+C\delta[\alpha_{(1)}+\alpha_{(2)}]
\ge\sum_i g(y_i)+2C\delta.
\tag{17.6}
$$

On the whole dense interval $[\tau,1]$,

$$
g''(z)=\frac{2r^2}{z^3}
 \left(1-\frac{3C\delta}{r^2z}\right)
\ge\frac{4r^2}{2a+3}\ge r.
\tag{17.7}
$$

Here $z\ge\tau=3(C+2)\delta/r^2$ bounds the fraction by $C/(C+2)$, and $z\le1$. Taylor's inequality with (17.7), summed using $\sum_i(y_i-\mu)=0$, proves

$$
\sum_i g(y_i)\ge s g(\mu)+\frac r2 V,
\qquad V=\sum_i(y_i-\mu)^2.
$$

The identity $H_d=sg(\mu)+2C\delta\mu^{-2}$ therefore yields

$$
\frac r2V\le2C\delta(\mu^{-2}-1)\le\frac{30}{a}.
\tag{17.8}
$$

Consequently $|y_i-\mu|\le\sqrt V<8/a$, whence $1-y_i<9/a<1/10$. This proves (17.4) for every sublevel competitor without assuming an adjacent-cardinality support. ∎

**Lemma 17.3 (The fourth-weight certificate and its complete zero set).** Let $x$ be any actual law whose marginals belong to $\mathcal B$, and order labels so that $P$ consists of three largest marginals and $j$ is a fourth largest marginal, breaking ties arbitrarily. Put

$$
\alpha_i=y_i^{-2},\quad \beta=\alpha_j,\quad
W=\sum_i\alpha_i,\quad W_T=\sum_{i\in T}\alpha_i,
\quad Q_T=\sum_{i\in P}(\alpha_i-\beta)\mathbf1_{\{i\in J\}}\le0.
\tag{17.9}
$$

For every nonempty subset $T\subseteq[s]$, with $k=|T|$, define

$$
R_y(T)=(k^2-r^2)W_T
 +C(r-k)(W-2\beta)-C Q_T.
\tag{17.10}
$$

Then $R_y(T)\ge0$. Its entire zero set is

$$
R_y(T)=0\quad\Longleftrightarrow\quad
\begin{cases}
k=r,\quad J=\{i\},\quad y_i\le y_j,\quad\text{or}\\
k=a,\quad J=\{i,l\},\quad y_i,y_l\ge y_j.
\end{cases}
\tag{17.11}
$$

If this law also has mean $q$, its exact same-law decomposition is

$$
\boxed{\ H(x)=F_{P,j}(y)+\mathbb E_x R_y(T)\ }.
\tag{17.12}
$$

**Proof.** The ordering gives $\alpha_i\le\beta$ on $P$ and $\alpha_i\ge\beta$ outside $P$. At $k=r$ the residual is $-C Q_T$ on a singleton omission, so it vanishes exactly as in the first case of (17.11). At $k=a$, $J$ is a pair and expansion gives

$$
R_y(T)=C\sum_{i\in J\setminus P}(\alpha_i-\beta)\ge0.
\tag{17.13}
$$

Its zeros are exactly the second case of (17.11), including all ties. At $k=s$ the residual is $2W+2C\beta>0$.

For every remaining cardinality $k<a$, put $z=r-k$, so $2\le z\le r-1$ and $|J|=z+1$. With $A_J=\sum_{i\in J}\alpha_i$, (17.10) becomes

$$
R_y(T)=z\big[(z-1)W+(2r-z)A_J-2C\beta\big]-C Q_T.
\tag{17.14}
$$

Since $\alpha_i\ge1$ and $\beta\le100/81<5/4$, the bracket is strictly greater than

$$
\begin{aligned}
(z-1)(r+1)+(2r-z)(z+1)-\frac52C
 &=-z^2+3rz+r-1-\frac52C\\
 &\ge7r-5-\frac52C
 =2r-\frac52>0.
\end{aligned}
\tag{17.15}
$$

For the middle inequality the quadratic is concave on $[2,r-1]$; its endpoint values before subtracting $5C/2$ are $7r-5$ and $2r^2-2$, and the latter is no smaller for $r\ge3$. Thus (17.14) is strictly positive. This accounts for every allowed cardinality and proves the complete zero set.

Taking expectations in (17.10), use only the identities of this actual law,

$$
\mathbb E(r-K)=\delta,\qquad
\mathbb E W_T=\sum_i y_i^{-1},\qquad
\mathbb E Q_T=\sum_{i\in P}(\alpha_i-\beta)(1-y_i).
$$

It follows that

$$
H(x)=r^2\sum_i y_i^{-1}-C\delta(W-2\beta)
 +C\sum_{i\in P}(\alpha_i-\beta)(1-y_i)
 +\mathbb E R_y(T).
\tag{17.16}
$$

The non-residual part is exactly (17.3), because $r^2-C=a^2$. This proves (17.12). Integrating a pointwise bound is the weak-duality principle in Bertsimas and Popescu, *Optimal inequalities in probability theory: A convex optimization approach*, DOI [10.1137/S1052623401399903](https://doi.org/10.1137/S1052623401399903), Theorem 2.1, p.785. Here (17.10) supplies the pointwise certificate itself. No strong duality, independent attainment of moment coordinates, or convexity of $H$ in the law is used. ∎

**Lemma 17.4 (A unique legal root for the marginal lower problem).** For every fixed $P,j$ of Definition 17.1, $F_{P,j}$ has exactly one minimizer on $\mathcal B_q$. Its coordinates are $u$ on $P$, $v$ at $j$ and $w$ elsewhere, where $(u,v,w)$ is the unique real triple in the region

$$
\begin{gathered}
3u+v+n w=q,\qquad \frac9{10}<w<v<u<1,\\
\max\{|u-\mu|,|v-\mu|,|w-\mu|\}<\frac{48}{a^2},\\
h=1-u,\qquad \zeta=2\delta-3h,\qquad 0<\zeta<h,
\end{gathered}
\tag{17.17}
$$

satisfying

$$
\boxed{\quad
\varphi'(u)+\frac C{v^2}
=g'(v)-\frac{2C\zeta}{v^3}
=g'(w).
\quad}
\tag{17.18}
$$

In fact (17.18) and the sum constraint have at most one root anywhere in $(9/10,1)^3$. Moreover $\min_{\mathcal B_q}F_{P,j}<H_d$.

**Proof.** The compact convex slice $\mathcal B_q$ contains $\mu\mathbf1$. On the whole box $\mathcal B$, the only nonzero off-diagonal Hessian entries connect $j$ with a label in $P$ and equal $-2C/y_j^3$. Their absolute values are less than $12a$. For the diagonal entries, writing $D=\delta-3+\sum_{i\in P}y_i\ge-3/10$, one has

$$
\begin{aligned}
(F_{P,j})_{ii}
 &=\frac{2a^2}{y_i^3}+\frac{6C(1-\delta)}{y_i^4}
 \ge2a^2 &&(i\in P),\\
(F_{P,j})_{jj}
 &=\frac{2r^2}{y_j^3}+\frac{6CD}{y_j^4}
 \ge2a^2-11a,\\
(F_{P,j})_{kk}
 &=\frac{2r^2}{y_k^3}-\frac{6C\delta}{y_k^4}
 \ge2a^2-72 &&(k\notin P\cup\{j\}).
\end{aligned}
\tag{17.19}
$$

For these bounds, $C\le3a$, $C\delta\le5$, $y_i^{-4}\le(10/9)^4<2$, and $a\ge100$ suffice: in particular $6CD/y_j^4\ge-(18/10)\cdot3a\cdot2>-11a$. Subtracting absolute off-diagonal row sums gives respectively $2a^2-12a$, $2a^2-47a$ and $2a^2-72$. Each is at least $a^2$ for $a\ge100$. Thus

$$
\nabla^2F_{P,j}\succeq a^2 I_s\quad\text{throughout }\mathcal B.
\tag{17.20}
$$

The minimizer $y^*$ on $\mathcal B_q$ exists and is unique.

Subtract the scalar $g'(\mu)$ from each entry of $\nabla F_{P,j}(\mu\mathbf1)$. The remaining vector has three entries $-2Ch_0/\mu^3$, one entry $-2Cd_0/\mu^3$, and all other entries zero, where

$$
h_0=1-\mu,\qquad
 d_0=2\delta-3h_0
 =\frac{2\lambda-3+\lambda/a}{a+2}.
\tag{17.21}
$$

Here $0<h_0\le1/a$ by (17.5), and $0<d_0\le1/a$: the lower bound follows from $\lambda\ge3/2+\eta$, and the upper bound follows by substituting $\lambda\le2$. Using $C\le3a$ and $\mu\ge9/10$, the norm of this residual vector is less than $24$. Since $F_{P,j}(\mu\mathbf1)=H_d$, strong convexity and minimality give

$$
\frac{a^2}{2}\|y^*-\mu\mathbf1\|^2
\le-\nabla F_{P,j}(\mu\mathbf1)\cdot(y^*-\mu\mathbf1)
<24\|y^*-\mu\mathbf1\|
\tag{17.22}
$$

when $y^*\ne\mu\mathbf1$. In fact this inequality is strict in the nonzero case because of the strict residual norm bound, and yields

$$
\|y^*-\mu\mathbf1\|<48/a^2.
\tag{17.23}
$$

The same bound holds if the difference is zero. This places every coordinate strictly between $9/10$ and one: use $\mu\ge1-1/a$, $h_0>1/a-2/a^2$, and $a\ge100$. Hence $y^*$ is interior relative to its sum hyperplane.

Permuting $P$, or permuting the other $n$ labels, leaves both the function and slice unchanged. Finite Jensen applied to the average over these permutations, with convexity on $\mathcal B_q$ supplied by (17.20), and uniqueness therefore give three equal coordinates $u$, one coordinate $v$, and $n$ equal coordinates $w$. This is the finite convex-combination inequality of Boyd and Vandenberghe, *Convex Optimization*, §3.1.8, pp.77–78, [author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf), used on an explicitly convex domain. The Lagrange equations for the interior minimum are (17.18).

It remains to establish strict ordering and the capacity inequalities, rather than impose them on this minimization. From (17.5) and (17.23),

$$
\zeta=2\delta-3(1-u)
\ge\frac{2\eta}{a}-\frac{144}{a^2}>0,
\qquad
h-\zeta=4h-2\delta
>\frac{2\eta}{a}-\frac{200}{a^2}>0.
\tag{17.24}
$$

Both signs follow from $a\eta\ge1024$.

Hold $w$ fixed, and let $t=(3u+v)/4$. The point with all four of these coordinates equal to $t$ lies in the same slice and within $48/a^2$ of $\mu$ in each coordinate. At this point the difference of a top partial derivative and the fourth partial derivative is

$$
\frac{4C[\delta-2(1-t)]}{t^3}<0,
\qquad
\delta-2(1-t)\le-\frac\eta a+\frac{100}{a^2}<0.
\tag{17.25}
$$

Along the line fixing $3u+v$ and $w$, the derivative in the direction increasing $u$ and decreasing $v$ is three times this difference at $u=v=t$. Strict convexity makes this one-variable derivative strictly increasing, while it vanishes at the interior minimizer. Therefore $u>t>v$.

Next hold $u$ fixed and set $t=(v+n w)/(n+1)$. At $v=w=t$, the fourth partial derivative minus a lower partial derivative is

$$
-\frac{2C\zeta}{t^3}<0.
\tag{17.26}
$$

Strict convexity along the line fixing $v+n w$ now gives $v>t>w$. This proves all of (17.17). Any triple in $(9/10,1)^3$ with the stated sum and (17.18) gives a stationary point of the same strictly convex function on $\mathcal B_q$, and hence must give its unique minimizer. This proves the stronger uniqueness assertion as well.

Finally $\mu\mathbf1$ is not a minimum: increasing one coordinate in $P$ and decreasing one lower coordinate has derivative $-2Ch_0/\mu^3<0$ there, and is feasible for a sufficiently small displacement. Consequently the minimum is strictly below $H_d$. ∎

**Theorem 17.5 (Exact dense infimum and every actual labeled minimizing law).** For every parameter in (17.1), let $(u,v,w)$ be the unique triple of Lemma 17.4 and put $h=1-u$, $\zeta=2\delta-3h$. Then

$$
\boxed{\quad
\mathscr D_a(\delta)
=3\varphi(u)+g(v)+\frac{C\zeta}{v^2}+n g(w)
<H_d.
\quad}
\tag{17.27}
$$

Equivalently the middle two terms are $r^2/v+C(\delta-3+3u)/v^2$. The dense infimum of $d(x)$ from Definition 1.1 is (17.27) minus $B$.

A finite polynomial specification of this value consists of (17.17), the sum constraint, and

$$
\begin{aligned}
[a^2u+2C(1-\delta)]v^3
 &=[(r^2+C)v+2C(\zeta-\delta)]u^3,\\
[r^2v+2C(\zeta-\delta)]w^3
 &=[r^2w-2C\delta]v^3,\qquad
\zeta=2\delta-3+3u.
\end{aligned}
\tag{17.28}
$$

There exists exactly one legal root. All denominators in (17.18) are strictly positive in (17.17), so (17.28) is equivalent there; roots outside that region are not part of the specification.

All labeled minimizing laws, and only those laws, are the following. Choose an unordered triple $P\subseteq[s]$, a label $j\notin P$, and real parameters

$$
b_i\ge0\quad(i\in P),\qquad \sum_{i\in P}b_i=\zeta.
\tag{17.29}
$$

Their masses are

$$
\begin{aligned}
\bar x_{\{i,j\}}&=b_i &&(i\in P),\\
\bar x_{\{i,k\}}&=\frac{h-\zeta}{2}+b_l
 &&(\{i,k,l\}=P),\\
\bar x_{\{j\}}&=1-v-\zeta,\\
\bar x_{\{k\}}&=1-w &&(k\notin P\cup\{j\}),\\
\bar x_J&=0 &&\text{for every other proper subset }J.
\end{aligned}
\tag{17.30}
$$

The actual marginals are $u,u,u,v,w,\ldots,w$, with the strict ordering in (17.17). The three pair masses inside $P$ and all displayed singleton masses are strictly positive. Each of the three masses $b_i$ may be zero, including two simultaneously.

For each of exactly $\binom{s}{3}(s-3)$ distinct labeled marginal patterns, (17.30) is an affine bijection from the nondegenerate closed two-dimensional simplex (17.29) onto the entire actual minimizing-law fibre over that pattern. Its inverse is $b_i=\bar x_{\{i,j\}}$. Thus uniqueness of the marginal pattern up to labels coexists with a continuum of actual minimizing laws.

**Proof.** First construct each law in (17.30) and verify every condition using its own masses. Since $0<\zeta<h$, all pair masses are nonnegative and the three pairs inside $P$ have positive masses. Moreover

$$
1-v-\zeta>h-\zeta>0,\qquad 1-w>0.
\tag{17.31}
$$

The pair-omission degrees at the four labels $P\cup\{j\}$ are $(h,h,h,\zeta)$. Indeed, at $i\in P$ the two internal pairs have total $h-\zeta+\sum_{k\in P\setminus\{i\}}b_k=h-b_i$, and the pair $\{i,j\}$ adds $b_i$. The degree at $j$ is $\sum_i b_i=\zeta$. The total pair mass is therefore

$$
\frac{3h+\zeta}{2}=\delta.
\tag{17.32}
$$

The sum constraint gives

$$
3h+(1-v)+n(1-w)=s-q=1+\delta.
$$

Consequently the singleton-omission masses sum to

$$
1-v-\zeta+n(1-w)=1-\delta.
\tag{17.33}
$$

Total mass is one and all atoms are nonempty, since omissions have size one or two and $s>2$. The mean is $a\delta+r(1-\delta)=q$. The omission probabilities are $h$ on $P$, $\zeta+(1-v-\zeta)=1-v$ at $j$, and $1-w$ elsewhere. Thus these same masses induce precisely the claimed marginals. They are dense, since $w>9/10>\tau$.

For a direct energy computation, the incidence second moments of this law are

$$
\begin{aligned}
\mathbb E[K^2 I_i]&=r^2u-C(\delta-h)
 =a^2u+C(1-\delta) &&(i\in P),\\
\mathbb E[K^2 I_j]&=r^2v-C(\delta-\zeta),\\
\mathbb E[K^2 I_k]&=r^2w-C\delta
 &&(k\notin P\cup\{j\}).
\end{aligned}
\tag{17.34}
$$

Dividing by the squares of the actual marginals gives exactly (17.27). Equivalently every supported atom has residual zero in Lemma 17.3, and its energy is $\min_{\mathcal B_q}F_{P,j}$.

Now take any dense law from the full original domain. If $H>H_d$, it is strictly worse than (17.27) by Lemma 17.4. Otherwise Lemma 17.2 places its marginals in $\mathcal B$. Choose its top triple and fourth label and apply Lemma 17.3. The same-law identity gives

$$
H(x)\ge F_{P,j}(y)\ge\min_{\mathcal B_q}F_{P,j}.
\tag{17.35}
$$

Relabeling coordinates does not change this last minimum. Lemma 17.4 therefore identifies it with (17.27), already attained by the constructed actual laws. This proves the minimum over all cardinalities, including nonsymmetric and disconnected incidence laws.

Conversely, any law attaining this value has $H<H_d$, is localized, and has equality in both inequalities (17.35). Strict convexity forces its marginal vector to be exactly the unique minimizer of $F_{P,j}$. Its strict three-level pattern recovers $P$ as the three largest coordinates and $j$ as the sole intermediate coordinate. Equality in (17.12) forces all positive-mass atoms into (17.11). At these strict marginals, the allowed omissions are exactly singleton omissions outside $P$ and pair omissions within $P\cup\{j\}$. Every other atom has strictly positive residual, whatever its cardinality.

The mean now forces pair mass $\delta$. Since no singleton omission at a label of $P$ is allowed, each such label has pair degree $h$. The remaining pair degree at $j$ is $2\delta-3h=\zeta$. Set $b_i=\bar x_{\{i,j\}}$. Its degree equation gives $\sum_i b_i=\zeta$. For $\{i,k,l\}=P$, the remaining three degree equations have the unique solution

$$
\bar x_{\{i,k\}}
=\frac{(h-b_i)+(h-b_k)-(h-b_l)}2
=\frac{h-\zeta}{2}+b_l.
\tag{17.36}
$$

The actual marginals then force all singleton masses to be those in (17.30). This proves necessity as well as sufficiency, with no positivity assumption on $b_i$ and no omitted boundary laws.

Because the marginal groups are strict, different choices of $P,j$ give different recoverable labeled patterns. There are $\binom{s}{3}(s-3)$ choices. The displayed affine inverse and $\zeta>0$ prove that every fibre is exactly the stated closed two-dimensional simplex.

The pair-degree part is the classical fractional perfect $b$-matching polytope $\mathcal P(K_4,(h,h,h,\zeta))$ in the notation of Roger E. Behrend, *Fractional Perfect b-Matching Polytopes. I: General Theory*, [arXiv:1301.7356v1](https://arxiv.org/abs/1301.7356v1), (2), DOI [10.1016/j.laa.2013.10.001](https://doi.org/10.1016/j.laa.2013.10.001). Taking all $b_i=\zeta/3$ makes all six pair masses strictly positive. Thus its Corollary 19 applies: $K_4$ is connected and nonbipartite, so the dimension is $6-4=2$. This dimension formula is a classical intermediate fact. Equations (17.32)–(17.36) supply the particular simplex shape and the exhaustive bridge to the actual nonlinear energy minimizers. Finally clearing the positive denominators in (17.18) gives exactly (17.28), and Lemma 17.4 proves existence and uniqueness in the specified region. ∎

**Corollary 17.6 (Boundary strata and the continuum after relabeling).** Under (17.1), each labeled marginal pattern has exactly three vertex laws. A simplex vertex has four positive pair-omission masses, a relative interior point of an edge has five, and a relative interior point of the simplex has six. All these laws also have the same $n+1=a-1$ positive singleton-omission masses. Two minimizing laws are related by a label permutation if and only if, after mapping their recovered $P,j$ to one another, their parameter triples $(b_i)_{i\in P}$ differ by a permutation. Consequently a full set of representatives for all minimizing laws modulo relabeling is

$$
0\le b_1\le b_2\le b_3,\qquad b_1+b_2+b_3=\zeta.
\tag{17.37}
$$

It is the nondegenerate closed triangle with vertices

$$
(0,0,\zeta),\qquad (0,\zeta/2,\zeta/2),
\qquad (\zeta/3,\zeta/3,\zeta/3).
\tag{17.38}
$$

In particular the continuum survives relabeling.

**Proof.** The three internal pair masses in (17.30) always exceed zero. Of the other three pair masses, respectively one, two or three are positive at a vertex, in an edge interior, or in the simplex interior. Equation (17.31) supplies all singleton positivities. A permutation relating two laws must map their actual marginal vectors to one another, hence must map their recovered top triples and intermediate labels. The only remaining action on (17.29) is the permutation of the three top labels; permutations of lower labels do not affect $b$. Conversely every permutation of $b$ is induced by such a label permutation. Sorting the triple therefore gives a unique representative. To verify the triangle description directly, any sorted triple in (17.37) is the convex combination of the three vectors in (17.38) with coefficients

$$
\frac{b_3-b_2}{\zeta},\qquad
\frac{2(b_2-b_1)}{\zeta},\qquad
\frac{3b_1}{\zeta},
$$

which are nonnegative and sum to one. The vertices are not collinear because $\zeta>0$. ∎

The nonlinear all-law optimum and the complete actual-law fibre correspondence in Theorem 17.5 are deductions for the common law of Definition 1.1; the attributed weak-duality, finite-Jensen and matching-polytope statements supply only the indicated intermediate steps. No conclusion here extends to $\lambda=3/2$ or $\lambda=2$, their adjoining boundary layers, smaller $a$, a least sufficient $A(\eta)$, unrestricted rare/dense competition, or realization by a finite graph with prescribed budgets. The full text of Zhao–Zhao, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), is not an input; its possible overlap remains unassessed. No worldwide priority assertion is made.

## 追加锚（本行以下为增补区）

## 18. Fixed higher dense phases and their complete degree fibres

**Definition 18.1 (Fixed-phase parameters and auxiliary marginal functions).** Fix an integer $k\ge4$ and a real number $0<\eta<1/4$, and put

$$
\begin{gathered}
L=k+1,\qquad A(k,\eta)=\left\lceil\frac{2^{16}L^2}{\eta}\right\rceil,\\
a\in\mathbb Z,\quad a\ge A(k,\eta),\qquad
\frac k2+\eta\le\lambda\le\frac{k+1}{2}-\eta,\qquad
\delta=\frac\lambda a,\\
r=a+1,\quad s=a+2,\quad n=a+1-k,\quad c=2a+1,\\
q=r-\delta,\quad \theta=1-\delta,\quad \gamma=c\delta,\quad
\mu=\frac qs,\quad \tau=\frac{3(2a+3)\delta}{r^2}.
\end{gathered}
\tag{18.1}
$$

The actual-law domain is exactly Definition 11.1: nonnegative masses $x_T$ on all nonempty $T\subseteq[s]$, of total one, with $\mathbb E_x|T|=q$ and actual marginals $y_i=\mathbb P_x(i\in T)\ge\tau$. Its energy is the $H(x)$ of Definition 1.1. All expectations and marginals belong to this same law. In particular no support, symmetry, connectedness, or strictly positive atom-mass condition is imposed. Write $J=[s]\setminus T$ and $\bar x_J=x_{[s]\setminus J}$ for proper subsets $J\subsetneq[s]$.

For $z>0$ set

$$
f(z)=\frac{a^2}{z}+\frac{c\theta}{z^2},\qquad
g(z)=\frac{r^2}{z}-\frac\gamma{z^2}.
\tag{18.2}
$$

Given $P\subseteq[s]$ with $|P|=k$ and $h\notin P$, put $N=[s]\setminus(P\cup\{h\})$ and define

$$
\begin{aligned}
\mathcal G_{P,h}(y)
&=\sum_{i\in P}f(y_i)+\frac{r^2}{y_h}
 +\frac{c(\sum_{i\in P}y_i+\delta-k)}{y_h^2}
 +\sum_{j\in N}g(y_j),\\
\mathcal B&=[9/10,1]^s,\qquad
\mathcal B_q=\{y\in\mathcal B:\sum_i y_i=q\},\\
v(u,w)&=\frac{q-ku-w}{n},\qquad D(u)=ku+\delta-k,\\
F_k(u,w)&=k f(u)+\frac{r^2}{w}+\frac{cD(u)}{w^2}+n g(v(u,w)).
\end{aligned}
\tag{18.3}
$$

These are auxiliary functions; membership in $\mathcal B_q$ does not assert realizability by an actual law. The normalization $H$ and the subtractand $B$ remain (1.1). The graph normalization cited there uses the convention of Albalahi et al., DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176), §1, p.109, which drops $1/\sqrt2$ in defining CDSO; no finite-graph extremal theorem is assumed here. The parameter range (18.1) is disjoint from §17.

**Lemma 18.2 (A full-cardinality certificate and a grouped lower bound).** Sort the actual marginals of any law in Definition 18.1 as $y_1\ge\cdots\ge y_s$, and choose $P=\{1,\ldots,k\}$ and $h=k+1$. Set

$$
\alpha_i=y_i^{-2},\quad \omega=\alpha_h,\quad
W=\sum_i\alpha_i,\quad W_T=\sum_{i\in T}\alpha_i,\quad
b_i=c(\omega-\alpha_i)_+.
\tag{18.4}
$$

Here $(z)_+=\max\{z,0\}$. For every allowed nonempty $T$, let $j=|T|$ and define

$$
R_y(T)=(r-j)\{c(W-2\omega)-(r+j)W_T\}
       +\sum_{i\notin T}b_i.
\tag{18.5}
$$

Then $R_y(T)\ge0$, with its entire zero set given by

$$
R_y(T)=0\quad\Longleftrightarrow\quad
\begin{cases}
J=\{i\},\quad y_i\le y_h,\quad\text{or}\\
J=\{i,l\},\quad y_i,y_l\ge y_h.
\end{cases}
\tag{18.6}
$$

Ties are included in these conditions. There is the exact same-law identity

$$
H(x)=\mathcal G_{P,h}(y)+\mathbb E_xR_y(T).
\tag{18.7}
$$

If $u=k^{-1}\sum_{i\in P}y_i$, $w=y_h$ and $v=n^{-1}\sum_{j\in N}y_j$, then

$$
H(x)\ge F_k(u,w),\qquad
\tau\le v\le w\le u\le1,\qquad
ku+w+nv=q,\qquad v\ge1-\frac3a>\frac9{10}.
\tag{18.8}
$$

Equality in the first inequality holds exactly when $R_y(T)=0$ on every positive-mass atom, all $k$ top marginals equal $u$, and all $n$ lower marginals equal $v$.

**Proof.** The threshold in (18.1) implies

$$
a\ge1024L^2,\quad n\ge a/2,\quad
0<\delta\le\frac{L}{2a}<\frac12,\quad
\tau\le\frac{9L}{2a^2}<\frac9{10}.
\tag{18.9}
$$

The mean and ordering give $q\le k+(s-k)y_h$, hence

$$
y_h\ge1-\frac{1+\delta}{s-k}\ge1-\frac3a
       \ge\ell:=1-\frac4a,\qquad
1\le\omega\le\ell^{-2}<\frac{16}{15}.
\tag{18.10}
$$

The last strict bound follows already for $a\ge128$. All $\alpha_i\ge1$. At $j=r$, (18.5) is $b_i$ for the sole omitted label; it vanishes exactly when $y_i\le y_h$. At $j=a$ it is

$$
c\left(\sum_{i\in J}\alpha_i-2\omega\right)
 +c\sum_{i\in J}(\omega-\alpha_i)_+
 =c\sum_{i\in J}(\alpha_i-\omega)_+.
\tag{18.11}
$$

This proves precisely the pair case in (18.6). At $j=s$, the residual is $2W+2c\omega>0$.

For every remaining nonempty cardinality $j<a$, put $e=|J|=s-j$, so $3\le e\le s-1$ and $r-j=e-1>0$. Writing $A_J=\sum_{i\in J}\alpha_i$, the bracket in (18.5) equals

$$
\begin{aligned}
(e-2)W+(2s-1-e)A_J-2c\omega
&\ge 3se-2s-e-e^2-2c\omega\\
&>7s-12-\frac{32c}{15}
 =\frac{41a-2}{15}>0.
\end{aligned}
\tag{18.12}
$$

Indeed the quadratic $3se-2s-e-e^2$ is concave in $e$; at the two endpoints it is $7s-12$ and $2s(s-2)$, and the latter is no smaller for $s\ge5$. Also $2s-1-e>0$ throughout this interval, justifying both substitutions $W\ge s$ and $A_J\ge e$. The omitted $b_i$ are nonnegative. This proves positivity for every other cardinality and exhausts the zero set.

Taking expectation of (18.5) under the actual $x$, use $\mathbb E(r-|T|)=\delta$, $\mathbb EW_T=\sum_i y_i^{-1}$, and $\mathbb E\mathbf1_{\{i\notin T\}}=1-y_i$. It follows that

$$
H(x)=r^2\sum_i\frac1{y_i}-c\delta(W-2\omega)
      -\sum_i(1-y_i)b_i+\mathbb E R_y(T).
\tag{18.13}
$$

Only indices in $P$ can have $b_i\ne0$. Expanding their terms and using $r^2-c=a^2$ turns the non-residual part exactly into $\mathcal G_{P,h}(y)$, proving (18.7). This is the pointwise-to-expectation weak-duality argument of Bertsimas and Popescu, DOI [10.1137/S1052623401399903](https://doi.org/10.1137/S1052623401399903), Theorem 2.1, p.785, with the present residual established directly. No strong-duality or independent moment-attainment assertion is needed.

On the entire original dense interval $[\tau,1]$,

$$
f''(z)=\frac{2a^2}{z^3}+\frac{6c\theta}{z^4}>0,\qquad
g''(z)=\frac{2(r^2z-3\gamma)}{z^4}>0,
\qquad r^2\tau-3\gamma=6\delta>0.
\tag{18.14}
$$

Finite Jensen applied separately on $P$ and $N$ gives (18.8), with equality precisely as stated, since the remaining dependence on the top coordinates in (18.3) is linear. The finite convex-combination inequality used here is Boyd and Vandenberghe, *Convex Optimization*, §3.1.8, pp.77–78, [author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf); its strictness follows from (18.14). Finally $ku+w\le k+1$ implies

$$
v\ge\frac{q-k-1}{n}=1-\frac{1+\delta}{n}\ge1-\frac3a.
\tag{18.15}
$$

Thus the grouped vector belongs to $\mathcal B_q$ even when some individual lower marginals of the original law do not belong to $\mathcal B$. No energy sublevel or stronger density condition was imposed. ∎

**Lemma 18.3 (Unique exact root and strict capacity slack).** For each fixed $P,h$, the function $\mathcal G_{P,h}$ has exactly one minimum on $\mathcal B_q$. Its coordinates are $u$ on $P$, $w$ at $h$, and $v$ on $N$, independent of the labels. They satisfy

$$
\begin{gathered}
ku+w+nv=q,\qquad \tau<v<w<u<1,\\
\max\{|u-\mu|,|w-\mu|,|v-\mu|\}\le\frac{48L}{a^2},\\
t=1-u,\qquad d=2\delta-kt,\qquad
0<d<t,\qquad d>\frac\eta a,\quad
 t-d>\frac\eta a,\quad 1-w-d>\frac\eta a.
\end{gathered}
\tag{18.16}
$$

Equivalently $(u,w,v)$ is the unique real triple in the legal region

$$
ku+w+nv=q,\qquad \tau<v<w<u<1
\tag{18.17}
$$

solving

$$
\begin{aligned}
[a^2u+2c\theta]w^3
 &=\big[(r^2+c)w+2c(ku+\delta-k)\big]u^3,\\
[r^2w+2c(ku+\delta-k)]v^3
 &=[r^2v-2\gamma]w^3.
\end{aligned}
\tag{18.18}
$$

Its value $F_k(u,w)$ is strictly less than $H_d=Z/\mu^2$, where $Z=\delta a^3+\theta r^3$ as in (1.1).

**Proof.** On $\mathcal B$, put $D_y=\sum_{i\in P}y_i+\delta-k\ge-k/10$. The only off-diagonal Hessian entries of $\mathcal G_{P,h}$ are the $P$--$h$ entries $-2c/y_h^3$, each of absolute value at most $9a$. Its diagonal entries have the respective lower bounds

$$
\begin{aligned}
(\mathcal G_{P,h})_{ii}
 &=2a^2/y_i^3+6c\theta/y_i^4\ge2a^2 &&(i\in P),\\
(\mathcal G_{P,h})_{hh}
 &=2r^2/y_h^3+6cD_y/y_h^4\ge2a^2-4ka,\\
(\mathcal G_{P,h})_{jj}
 &=2r^2/y_j^3-6\gamma/y_j^4\ge2a^2-18L &&(j\in N).
\end{aligned}
\tag{18.19}
$$

Here $c\le3a$, $\gamma\le3L/2$, $z^{-3}<3/2$ and $z^{-4}<2$ on $[9/10,1]$. Subtracting the absolute off-diagonal row sums gives lower bounds $2a^2-9a$, $2a^2-13ka$ and $2a^2-18L$. Each is at least $a^2$ under (18.9). Consequently

$$
\nabla^2\mathcal G_{P,h}\succeq a^2 I_s\quad\text{on }\mathcal B.
\tag{18.20}
$$

For completeness the row estimate follows by applying $2|z_i z_j|\le z_i^2+z_j^2$ to each off-diagonal term of the Hessian quadratic form. The compact convex slice $\mathcal B_q$ contains $\mu\mathbf1$, so it has a unique minimizer $y^*$.

Let $\beta=2\lambda-k\in[2\eta,1-2\eta]$ and $h_0=1-\mu$. The exact identities and bounds

$$
\begin{gathered}
h_0=\frac1a+\frac{\lambda-2}{a(a+2)},\qquad
\frac1a\le h_0\le\frac1a+\frac{L}{2a^2}\le\frac2a,\\
d_0=2\delta-kh_0=\frac\beta a-k\left(h_0-\frac1a\right),
\qquad |d_0|\le\frac2a,\qquad \mu^{-3}<2
\end{gathered}
\tag{18.21}
$$

follow from $k\ge4$, $\lambda>2$ and $a\ge1024L^2$. Subtract $g'(\mu)$ from every entry of $\nabla\mathcal G_{P,h}(\mu\mathbf1)$. The resulting vector has entries $-2ch_0/\mu^3$ on $P$, $-2cd_0/\mu^3$ at $h$, and zero on $N$. Each nonzero entry has absolute value at most $24$, so its Euclidean norm is at most $24\sqrt L\le24L$. The sum constraint annihilates the subtracted constant vector. Strong convexity and $\mathcal G_{P,h}(y^*)\le\mathcal G_{P,h}(\mu\mathbf1)$ therefore give

$$
\frac{a^2}{2}\|y^*-\mu\mathbf1\|^2
 \le24L\|y^*-\mu\mathbf1\|,
\qquad \|y^*-\mu\mathbf1\|\le\frac{48L}{a^2}.
\tag{18.22}
$$

In particular every coordinate is strictly below one, since $h_0\ge1/a>48L/a^2$, and strictly above $9/10$, since it is at least $1-2/a-48L/a^2>9/10$. Thus the minimum is interior relative to its sum hyperplane. Invariance under permutations of $P$ and of $N$, together with uniqueness, forces coordinates $u,w,v$ of the stated multiplicities. Its Lagrange equations are

$$
f'(u)+\frac c{w^2}
 =-\frac{r^2}{w^2}-\frac{2c(ku+\delta-k)}{w^3}
 =g'(v).
\tag{18.23}
$$

We next prove ordering and legal masses. From (18.21)–(18.22),

$$
\left|t-\frac1a\right|\le\frac{49L}{a^2},\qquad
\left|d-\frac\beta a\right|\le\frac{49L^2}{a^2},\qquad
\left|(t-d)-\frac{1-\beta}{a}\right|\le\frac{49L^2}{a^2}.
\tag{18.24}
$$

Since $a\eta\ge2^{16}L^2>49L^2$, this implies $d>\eta/a$ and $t-d>\eta/a$.

To compare $u$ and $w$, hold the lower coordinates $v$ fixed and set $z=(ku+w)/L$. The line with high coordinates $z+\varepsilon$ and intermediate coordinate $z-k\varepsilon$ preserves the sum. At $\varepsilon=0$, its derivative is $k$ times the difference of a top partial derivative and the intermediate partial derivative, namely

$$
\frac{2kc[2\delta-L(1-z)]}{z^3}<0.
\tag{18.25}
$$

Indeed $|1-z-1/a|\le49L/a^2$ by the same coordinate bound, and
$2\delta-L(1-z)\le-(1-\beta)/a+49L^2/a^2<-\eta/a$.
The line segment from this equalized point to $y^*$ lies inside $\mathcal B_q$. Its one-variable derivative is strictly increasing by (18.20), and vanishes at $y^*$. Its parameter there must therefore be positive. Thus $u>z>w$.

Next hold all high coordinates $u$ fixed, and set $z=(w+nv)/(n+1)$. Along the line increasing the intermediate coordinate and decreasing each lower coordinate by $1/n$ times that increase, the derivative at the equalized point is

$$
-\frac{2cd}{z^3}<0.
\tag{18.26}
$$

The same strict-convexity argument gives $w>z>v$. Also $1-w-d>1-u-d=t-d>\eta/a$. Together with (18.9), (18.22) and $v>9/10$, these prove (18.16).

Clearing the positive denominators in (18.23) gives exactly (18.18). Conversely any real triple satisfying (18.17) has
$v\ge1-(1+\delta)/n\ge1-3/a>9/10$ by its mean and $u,w\le1$. Its repeated-coordinate vector is therefore interior to $\mathcal B_q$. Equations (18.18), with positive denominators, are equivalent to (18.23); they make this vector a stationary point of $\mathcal G_{P,h}$ on that slice. Strong convexity identifies it with $y^*$. This proves existence, uniqueness, and absence of additional roots in the whole legal region, without interpreting roots outside that region as solutions of the original optimization.

Finally direct substitution gives $\mathcal G_{P,h}(\mu\mathbf1)=Z/\mu^2$. At this point, increasing one coordinate of $P$ and decreasing one coordinate of $N$ has derivative $-2ch_0/\mu^3<0$. Such a sufficiently small displacement is feasible, since $\mu\mathbf1$ is interior and $n>0$. The unique minimum is thus strictly below $H_d$. ∎

**Theorem 18.4 (Exact full-law dense minimum and all labeled closed fibres).** For all parameters (18.1), let $(u,w,v)$ be the unique legal root (18.17)–(18.18), and put $t=1-u$ and $d=2\delta-kt$. Then the exact infimum in Definition 11.1 is an attained minimum, equal to

$$
\boxed{\quad
\mathscr D_a(\delta)
 =k\left(\frac{a^2}{u}+\frac{c\theta}{u^2}\right)
  +\frac{r^2}{w}+\frac{c(d-\delta)}{w^2}
  +n\left(\frac{r^2}{v}-\frac\gamma{v^2}\right)
 =F_k(u,w)<\frac Z{\mu^2}.
\quad}
\tag{18.27}
$$

The exact dense minimum of $d(x)$ from Definition 1.1 is (18.27) minus $B$.

All labeled minimizing actual laws are given as follows. Choose $P\subseteq[s]$ with $|P|=k$ and $h\notin P$, and set $S=P\cup\{h\}$ and $N=[s]\setminus S$. On the unordered edges of the complete graph $K_S$, choose any array in the closed polytope

$$
\begin{aligned}
\mathcal Q_{P,h}(t,d)=\bigg\{(z_{ij})_{\{i,j\}\in\binom S2}:\;&z_{ij}\ge0,\\
&\sum_{j\in S\setminus\{i\}}z_{ij}=t\quad(i\in P),\qquad
\sum_{i\in P}z_{ih}=d\bigg\}.
\end{aligned}
\tag{18.28}
$$

Here $z_{ij}=z_{ji}$ denotes one unordered-edge coordinate. The masses of the law are

$$
\begin{aligned}
\bar x_{\{i,j\}}&=z_{ij} &&(\{i,j\}\in\tbinom S2),\\
\bar x_{\{h\}}&=1-w-d,\\
\bar x_{\{j\}}&=1-v &&(j\in N),\\
\bar x_J&=0 &&\text{for every other proper subset }J\subsetneq[s].
\end{aligned}
\tag{18.29}
$$

Every edge coordinate in (18.28) is allowed to be zero, subject only to its displayed degree equations. There are exactly

$$
\binom sk(s-k)
\tag{18.30}
$$

distinct labeled marginal patterns, recovered from each actual minimizing law as its $k$ largest-marginal labels $P$ and sole intermediate-marginal label $h$. For each such pattern, (18.29) is an affine bijection from the entire compact polytope (18.28) onto the full minimizing-law fibre, with inverse $z_{ij}=\bar x_{\{i,j\}}$. Its affine dimension is

$$
\binom{k+1}{2}-(k+1)=\frac{(k+1)(k-2)}2.
\tag{18.31}
$$

More precisely the following describes every support stratum and boundary of each law fibre. For $E\subseteq\binom S2$, let $\mathcal Q_E$ be the subset of (18.28) with $z_e=0$ for $e\notin E$, and let $\mathcal Q_E^+$ additionally require $z_e>0$ for all $e\in E$. When $\mathcal Q_E^+$ is nonempty, it is the relative interior of $\mathcal Q_E$, its closure is $\mathcal Q_E$, and

$$
\dim\mathcal Q_E=|E|-|S|+B(E),
\tag{18.32}
$$

where $B(E)$ is the number of bipartite components of the spanning graph $(S,E)$. These $\mathcal Q_E$ are exactly all nonempty faces when $E$ is taken to be the positive support of a relative interior point of that face. Under (18.29), the relative interior of the full law fibre consists exactly of the laws with every $z_e>0$, and its relative boundary consists exactly of the laws with at least one $z_e=0$. The singleton masses in (18.29) stay strictly positive throughout. The vertex laws are exactly those whose positive pair-support components are trees or contain exactly one cycle, of odd length.

Two minimizing laws are related by a label permutation exactly when, after identifying their recovered $P,h$, their edge arrays are related by a permutation of $P$ fixing $h$. Permutations of $N$ act trivially on the array. Thus every labeled fibre and also the set of minimizing laws modulo all label permutations contain uncountably many laws.

**Proof.** The inequalities $0<d<t$ in (18.16) give a strictly positive member of (18.28):

$$
z_{ih}^{\circ}=\frac dk\quad(i\in P),\qquad
z_{ij}^{\circ}=\frac{t-d/k}{k-1}\quad(i,j\in P,\ i\ne j).
\tag{18.33}
$$

Its degrees at $P$ are $(k-1)(t-d/k)/(k-1)+d/k=t$, and its degree at $h$ is $d$. Thus the polytope is nonempty; it is closed and bounded, since every coordinate is between zero and the positive degree at either endpoint.

For any member of this whole polytope, double counting degrees gives total pair mass

$$
\sum_{\{i,j\}\in\binom S2}z_{ij}=\frac{kt+d}{2}=\delta.
\tag{18.34}
$$

The mean constraint of the root gives $kt+(1-w)+n(1-v)=s-q=1+\delta$, hence

$$
(1-w-d)+n(1-v)=1-\delta.
\tag{18.35}
$$

All masses in (18.29) are nonnegative, and its displayed singleton masses are strictly positive by (18.16). Equations (18.34)–(18.35) prove total mass one. All its atoms are nonempty, since their omission sizes are one or two. Its actual mean is $a\delta+r(1-\delta)=q$. Its omission probabilities are exactly $t$ on $P$, $d+(1-w-d)=1-w$ at $h$, and $1-v$ on $N$. Consequently its actual marginals are $u$ on $P$, $w$ at $h$ and $v$ on $N$, and these exceed $\tau$.

The same masses give the actual incidence second moments

$$
\begin{aligned}
\mathbb E_x[|T|^2I_i]
 &=r^2u-c(\delta-t)=a^2u+c\theta &&(i\in P),\\
\mathbb E_x[|T|^2I_h]
 &=r^2w-c(\delta-d),\\
\mathbb E_x[|T|^2I_j]
 &=r^2v-c\delta &&(j\in N).
\end{aligned}
\tag{18.36}
$$

For example the probability of a cardinality-$a$ atom containing a high label is $\delta-t$; subtracting $c=r^2-a^2$ times this probability from $r^2u$ gives its first expression. The other two follow from probabilities $\delta-d$ and $\delta$. Dividing (18.36) by the squares of these actual marginals proves energy (18.27), since $d-\delta=ku+\delta-k$. These computations hold at every boundary point of the polytope as well as at its positive member.

Now take an arbitrary dense actual law with every cardinality still allowed. Sort its marginals and apply Lemma 18.2. Its grouped vector lies in $\mathcal B_q$, and therefore

$$
H(x)\ge F_k(u',w')
       \ge\min_{\mathcal B_q}\mathcal G_{P,h}
       =F_k(u,w).
\tag{18.37}
$$

The minimum of the auxiliary function is independent of the chosen labels. Lemma 18.3 identifies it exactly, and (18.29) attains it using an actual law. This proves the full-domain minimum, without assuming realizability of arbitrary auxiliary vectors.

If an actual law attains this value, equality must hold in both inequalities (18.37). Strict convexity fixes the grouped vector to the root. The strict Jensen conditions of Lemma 18.2 then fix all its individual marginals to $u$ on $P$, $w$ at $h$ and $v$ on $N$. The strict inequalities $u>w>v$ uniquely recover these label groups, irrespective of any initial tie-breaking in sorting. Equality in (18.7) forces residual zero on each positive-mass atom. At these strict marginal groups, (18.6) permits exactly singleton omissions outside $P$ and pair omissions within $S$. Every other cardinality and support atom has strictly positive residual.

The mean, with only these two cardinalities remaining, forces total pair mass $\delta$. A label in $P$ has no singleton omission, so its pair degree equals its omission probability $t$. The remaining pair degree at $h$ is $2\delta-kt=d$. Its singleton omission is therefore $1-w-d$, and the singleton omission at each lower label is $1-v$. All remaining freedom is exactly the nonnegative array (18.28). This proves exhaustive necessity, including every zero pair-mass boundary, as well as the asserted affine inverse. The strict marginal groups also prove disjointness and the count (18.30).

The geometry used at this point is classical intermediate geometry. In the notation of Roger E. Behrend, *Fractional Perfect b-Matching Polytopes. I: General Theory*, [arXiv:1301.7356v1](https://arxiv.org/html/1301.7356v1), definition (2), DOI [10.1016/j.laa.2013.10.001](https://doi.org/10.1016/j.laa.2013.10.001), (18.28) is $\mathcal P(K_S,b)$ with $b_i=t$ for $i\in P$ and $b_h=d$. The graph is finite, loopless and undirected, and its prescribed degrees are positive. Equation (18.33) supplies a strictly positive feasible element, the required hypothesis of Behrend's Corollary 19. The complete graph $K_{k+1}$ is connected and nonbipartite, so that corollary gives dimension $|E|-|S|$, exactly (18.31). The affine bijection transfers that dimension to the actual-law fibre.

For precision about all boundaries, in the affine space of the degree equations a point with every edge positive has a neighborhood with every edge positive; it is a relative interior point. A feasible point with $z_e=0$ lies in a supporting coordinate hyperplane. This is a proper supporting hyperplane because (18.33) has $z_e>0$. Thus the relative boundary is exactly the union of these coordinate-zero sets, with any empty sets contributing nothing. The same argument applied to the coordinates $E$ shows that if $\mathcal Q_E^+$ is nonempty, it is exactly $\operatorname{relint}\mathcal Q_E$. Blending any point of $\mathcal Q_E$ with a point of $\mathcal Q_E^+$ gives a positive point on $E$ and converges back to the former point, proving the closure assertion. For the graph $(S,E)$, the positive element of $\mathcal Q_E^+$ permits the same Corollary 19 and yields (18.32). Its hypotheses hold separately for every claimed support stratum; no dimension is assigned by this formula to an empty stratum.

Every nonempty face is of this form. Indeed take a relative interior point $z$ of a face and let $E$ be its positive support. Every other point of the face has support in $E$: otherwise extending the segment slightly past $z$ inside the face would make a zero coordinate of $z$ negative. Conversely, for any $y\in\mathcal Q_E$, all coordinates of $z$ in $E$ are positive, so for sufficiently small $\varepsilon>0$ the point $z+\varepsilon(z-y)$ is feasible. The point $z$ lies in the open segment between this point and $y$. The defining face property implies $y$ belongs to the face. Hence that face is exactly $\mathcal Q_E$.

Behrend's Theorem 22 applies to any element of this same $\mathcal P(K_S,b)$: it is a vertex if and only if each component of its positive-support graph is acyclic or has just one odd cycle. Since $b_i>0$, there are no isolated vertices in a feasible positive-support graph, so acyclic components here are trees with at least one edge. This proves the stated vertex-law characterization. It is also a finite exact description: enumerate such spanning subgraphs of $K_S$ and retain precisely their strictly positive solutions to the degree equations. Each candidate has at most one solution. On a tree, remove a leaf, assign its sole edge the remaining required degree at that leaf, and subtract it at the neighbor; the last residual must vanish. On an odd unicyclic component, remove its attached leaves in this way. The remaining odd cycle equations $z_{i-1}+z_i=b_i'$ have a unique solution, obtained by alternating substitution around the cycle and division by two. Retaining only positive edge weights and vanishing final residuals gives exactly all vertex laws. A solution with some zero edge weights is represented by its smaller positive support. Arbitrary feasible arrays, not merely these vertices, are included in (18.28)–(18.29).

Finally a label permutation relating two minimizing laws must carry their actual marginal vectors to one another. It must therefore carry $P$ to $P$, $h$ to $h$, and $N$ to $N$ after the two recovered patterns have been identified. Its only nontrivial effect on the edge array is the indicated permutation of $P$. Conversely each such permutation, extended arbitrarily on $N$, gives the corresponding relabeling of (18.29). The dimension (18.31) is positive for $k\ge4$, and the positive member has an open neighborhood in that affine space, so each fibre is uncountable. Quotienting finitely many such fibres by the finite label-permutation group still leaves uncountably many laws.

The new all-law optimization and inverse reconstruction in (18.27)–(18.37) use weak duality, finite Jensen, and Behrend's geometry only in the attributed intermediate roles above. Their scope is the fixed-$k$, fixed-$\eta$ interval (18.1); they assert no endpoint or transition-layer classification, growing-$k$ asymptotic regime, small-$a$ classification, least sufficient threshold, global rare/dense comparison, or prescribed finite-graph realization. The full text of Zhao–Zhao, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), is not an input, and its possible overlap remains unassessed. No worldwide priority claim is made. ∎

## 追加锚（第18节之后为增补区）

## 19. Exact saturated-block intervals and their two collision boundaries

**Definition 19.1 (Saturated-block parameters).** Fix an integer $m\ge4$ and assume

$$
\begin{gathered}
a\in\mathbb Z,\qquad a\ge A(m):=2^{16}m^2,\qquad
r=a+1,\quad s=a+2,\quad n=s-m,\quad c=2a+1,\\
0<\delta\le1,\qquad \theta=1-\delta,\quad q=r-\delta,\quad
\gamma=c\delta,\quad \tau=\frac{3(2a+3)\delta}{r^2},\\
t=\frac{2\delta}{m},\qquad U=1-t,\qquad
V=1-\frac{1-\delta}{n},\qquad \xi=1-\frac2m,\qquad
\delta_{\rm eq}=\frac{m}{2a+4-m}.
\end{gathered}
\tag{19.1}
$$

The actual-law domain, energy $H$, infimum $\mathscr D_a(\delta)$ and subtractand $B$ are precisely Definitions 1.1 and 11.1. In particular every nonempty subset remains allowed. The functions $f,g$ are (18.2), with the parameters (19.1); the fixed-$\eta$ restrictions in (18.1) are not imposed here. The bound $A(m)$ is sufficient, with no least-threshold assertion. The relations

$$
mU+nV=q,\qquad
U>V\ \Longleftrightarrow\ 0<\delta<\delta_{\rm eq}
\tag{19.2}
$$

hold. For an $m$-element label set $C\subseteq[s]$, write $N=[s]\setminus C$ and define

$$
\mathcal Z_C(t)=\left\{z\in\mathbb R_{\ge0}^{\binom C2}:
\sum_{j\in C\setminus\{i\}}z_{ij}=t\quad(i\in C)\right\}.
\tag{19.3}
$$

Here $z_{ij}=z_{ji}$ denotes an unordered edge coordinate. A saturated $C$-law is the actual omission law

$$
\bar x_{\{i,j\}}=z_{ij}\quad(\{i,j\}\subseteq C),\qquad
\bar x_{\{h\}}=\frac{\theta}{n}\quad(h\in N),\qquad
\bar x_J=0\quad\text{for all other proper }J\subsetneq[s],
\quad z\in\mathcal Z_C(t).
\tag{19.4}
$$

This definition allows zero pair masses. It makes sense on all $0<\delta\le1$; $C$ is the high-marginal block only in the strict coalescence range in (19.2).

**Lemma 19.2 (Two unique ordered thresholds).** Put

$$
\begin{aligned}
E_0(\delta)&=f'(U)+\frac c{U^2}-g'(V),\\
E_1(\delta)&=f'(U)+\frac c{V^2}-g'(V),\\
P_j(\delta)&=(r^2+jc)UV(U^2-V^2)
 -2c\delta(U^3-\xi V^3),\qquad j=0,1.
\end{aligned}
\tag{19.5}
$$

There is exactly one zero $\delta_j$ of $E_j$ on $[0,1]$, and

$$
0<\delta_-:=\delta_0<\delta_+:=\delta_1<\delta_{\rm eq}.
\tag{19.6}
$$

Each threshold is equivalently the unique root of $P_j=0$ in $0<\delta<\delta_{\rm eq}$, with $U,V$ given by (19.1). On the entire interval $[0,1]$,

$$
E_j=\frac{P_j}{U^3V^3},\qquad
E_j'(\delta)\le-\frac{2a^2}{m}<0.
\tag{19.7}
$$

Consequently $E_0\le0\le E_1$ holds exactly on $[\delta_-,\delta_+]$.

**Proof.** The definitions extend continuously to $\delta=0$. Throughout $[0,1]$ one has $n\ge a/2$, $c\le3a$, $U\ge1/2$ and $V\ge1-2/a$. Define

$$
A_*=V^{-2}-U^{-2},\qquad B_*=V^{-3}-\xi U^{-3},\qquad
R_j=r^2+jc.
$$

Using $a^2=r^2-c$ and $U-\theta=\xi\delta$ gives

$$
E_j=R_j A_*-2c\delta B_*.
\tag{19.8}
$$

Multiplication by the positive $U^3V^3$ proves the polynomial identity in (19.7). Since $U'=-2/m$ and $V'=1/n$,

$$
\begin{aligned}
A_*'&=-\frac{2}{nV^3}-\frac{4}{mU^3}\le-\frac4m,\\
B_*'&=-\frac{3}{nV^4}-\frac{6\xi}{mU^4},\\
E_j'&=R_jA_*'-2cB_*-2c\delta B_*'\\
&\le-\frac{4a^2}{m}+16c+\frac{12c}{n}+\frac{192c}{m}\\
&\le-\frac{4a^2}{m}+192a+72
\le-\frac{4a^2}{m}+200a
\le-\frac{2a^2}{m}.
\end{aligned}
\tag{19.9}
$$

Here $V^{-3},V^{-4}<2$, $U^{-3}\le8$, $U^{-4}\le16$, $0\le\xi\le1$, $m\ge4$, $a\ge9$ and $a\ge100m$ justify the successive estimates. In particular the estimate does not require $U>V$.

At zero, $U=1$ and $V=1-1/n$, so $E_j(0)=R_j(V^{-2}-1)>0$. At $\delta_{\rm eq}$, $U=V$ and

$$
E_j(\delta_{\rm eq})
=-\frac{2c\delta_{\rm eq}(1-\xi)}{U^3}<0.
$$

Continuity and (19.9) prove existence and uniqueness, including absence of further roots on $[0,1]$. In the open coalescence range,

$$
E_1-E_0=c(V^{-2}-U^{-2})>0.
\tag{19.10}
$$

Thus $E_1(\delta_-)>0$, giving the strict root order. Monotonicity now proves the last assertion. ∎

**Lemma 19.3 (Two supporting bounds over every cardinality).** Assume $0<\delta<\delta_{\rm eq}$ and set

$$
S=m f(U)+n g(V).
$$

For any original dense actual law, order its marginals decreasingly, let $C$ be its first $m$ labels and put

$$
D=\sum_{i\in C}y_i-mU.
$$

Then both bounds

$$
H(x)\ge S+E_0D,\qquad H(x)\ge S+E_1D
\tag{19.11}
$$

hold. Equality in either bound forces every individual marginal to be $U$ on $C$ and $V$ on $N$. For the first bound, equality further requires that every supported atom omit either one label or two labels of $C$. For the second, equality further requires that every supported atom omit either one label of $N$ or two arbitrary labels. These are necessary equality conditions; the mass constraints will further restrict them in Theorem 19.4.

**Proof.** The parameter inequalities needed for the certificates and convexity are

$$
\delta_{\rm eq}<\frac ma<\frac12,\quad
n-1\ge\frac a2,\quad
\gamma\le3m,\quad \tau\le\frac{9m}{a^2}<\frac9{10}.
\tag{19.12}
$$

Two adjacent pivots are used: $(P_0,h_0)=(\{1,\ldots,m-1\},m)$ and $(P_1,h_1)=(C,m+1)$, with $k_j=|P_j|$. The function $\mathcal G_{P_j,h_j}$ is the algebraic function (18.3), with its lower index set of size $s-k_j-1$ and with the present parameters. Thus no existence or strict-interior assertion of Lemma 18.3 is being invoked.

For either pivot, put $\omega=y_{h_j}^{-2}$, $\alpha_i=y_i^{-2}$, $W=\sum_i\alpha_i$ and $b_i=c(\omega-\alpha_i)_+$. The ordered mean gives

$$
y_{h_j}\ge1-\frac{1+\delta}{s-k_j}\ge1-\frac3a,
\qquad \omega<(16/15),\qquad \alpha_i\ge1.
\tag{19.13}
$$

Define $R_y(T)$ by exactly (18.5). Its all-cardinality argument can be checked with (19.13), independently of the narrower parameters (18.1). At $|T|=r$ it is $b_i$ for the omitted label. At $|T|=a$ it is $c\sum_{i\notin T}(\alpha_i-\omega)_+$. At $|T|=s$ it is $2W+2c\omega>0$. For every remaining nonempty cardinality, put $e=s-|T|\in[3,s-1]$. The bracket multiplying $r-|T|$ in (18.5) is at least

$$
3se-2s-e-e^2-2c\omega
\ge7s-12-2c\omega
>\frac{41a-2}{15}>0.
\tag{19.14}
$$

The middle inequality follows from concavity in $e$ and the endpoint values $7s-12$ and $2s(s-2)$. The omitted $b_i$ are nonnegative. Hence the complete zero set is still (18.6), with the present pivot, and expectation gives the same-law identity

$$
H(x)=\mathcal G_{P_j,h_j}(y)+\mathbb E_xR_y(T).
\tag{19.15}
$$

This identity is just expansion using $\mathbb E(r-K)=\delta$ and $\mathbb EW_T=\sum_i1/y_i$, as in (18.13); no restriction of the original support has been made.

Both $f$ and $g$ are strictly convex on $[\tau,1]$, because their second derivatives are (18.14), with $r^2\tau-3\gamma=6\delta>0$. Average the coordinates of $P_j$, leave $h_j$ fixed, and average the remaining coordinates. Denote the resulting repeated-coordinate vector by $z^{(j)}$. Finite Jensen and the linear dependence of the cross term on the coordinates in $P_j$ give

$$
H(x)\ge\mathcal G_{P_j,h_j}(z^{(j)}).
\tag{19.16}
$$

Equality requires residual zero on every positive-mass atom and equal coordinates within each of the two averaged groups. The lower averaged coordinate is at least

$$
1-\frac{1+\delta}{s-k_j-1}\ge1-\frac3a>\frac9{10},
\tag{19.17}
$$

since the other $k_j+1$ coordinates are at most one. Ordering bounds the other coordinates below by that average. Thus $z^{(j)}$ belongs to the compact slice $\mathcal B_q$ of (18.3), even when some original individual marginals lie outside $\mathcal B$.

For clarity, strong convexity on this box also holds with the present parameters. For a pivot with $k\le m$, the only off-diagonal Hessian entries are the $P$--$h$ entries, of absolute value at most $9a$. Its diagonal entries on $[9/10,1]^s$ are bounded below by $2a^2$ on $P$, $2a^2-4ka$ at $h$, and $2a^2-36m$ elsewhere. Indeed $\sum_{i\in P}y_i+\delta-k\ge-k/10$, $\gamma\le3m$, and $z^{-3}<3/2$, $z^{-4}<2$ on that interval. Subtracting the absolute off-diagonal row sums leaves at least $a^2$ in every row under (19.1). Applying $2|v_iv_h|\le v_i^2+v_h^2$ to its quadratic form proves

$$
\nabla^2\mathcal G_{P_j,h_j}\succeq a^2 I_s
\quad\text{on }\mathcal B.
\tag{19.18}
$$

Let $y^C$ have coordinates $U$ on $C$ and $V$ on $N$. It is in the relative interior of $\mathcal B_q$, by (19.1), (19.2), (19.12). With $D_C(y)=\sum_{i\in C}y_i+2\delta-m$, the two algebraic identities are

$$
\begin{aligned}
\mathcal G_{P_0,h_0}(y)
 &=\sum_{i\in C}f(y_i)+\sum_{i\in N}g(y_i)
   +\frac{cD_C(y)}{y_{h_0}^2},\\
\mathcal G_{P_1,h_1}(y)
 &=\sum_{i\in C}f(y_i)+\sum_{i\in N}g(y_i)
   +\frac{cD_C(y)}{y_{h_1}^2}.
\end{aligned}
\tag{19.19}
$$

Since $D_C(y^C)=0$, both functions have value $S$ at $y^C$. Their respective gradients there are $f'(U)+c/U^2$ and $f'(U)+c/V^2$ on every label of $C$, and $g'(V)$ on every label of $N$. Grouping preserves the total on $C$ as well as the total on $N$. The supporting inequality obtained by integrating (19.18) on the line segment from $y^C$ to $z^{(j)}$ therefore gives

$$
\mathcal G_{P_j,h_j}(z^{(j)})
\ge S+E_jD+\frac{a^2}{2}\|z^{(j)}-y^C\|^2.
\tag{19.20}
$$

Equations (19.16) and (19.20) prove (19.11). If equality holds, (19.20) fixes the grouped vector to $y^C$, and strict Jensen fixes every individual coordinate. At this two-level vector, the pivot in the first bound has marginal $U$, so (18.6) allows all singleton omissions but only pair omissions within $C$. The pivot in the second bound has marginal $V$, so it allows only singleton omissions in $N$ but every pair omission. This proves all stated necessities.

The convex-combination inequality and first-order supporting inequality used here are classical: Stephen Boyd and Lieven Vandenberghe, *Convex Optimization*, §§3.1.8 and 3.1.3, respectively, pp.77–78 and 69–70, [author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf). Their hypotheses are supplied by (18.14), (19.17) and (19.18); the strengthened term in (19.20) follows directly by integration. Convexity is asserted for these auxiliary marginal functions, not for $H$ as a function of law masses. ∎

**Theorem 19.4 (Exact closed saturated interval and every minimizing actual law).** Under (19.1), the saturated laws (19.4) are globally minimizing in Definition 11.1 if and only if

$$
\delta\in[\delta_-,\delta_+].
\tag{19.21}
$$

On that closed interval the exact value is

$$
\boxed{\quad \mathscr D_a(\delta)=m f(U)+n g(V).\quad}
\tag{19.22}
$$

The corresponding dense infimum of $d(x)$ is (19.22) minus $B$. Every minimizing actual law is exactly (19.4), for one $m$-element $C$ and an arbitrary array (19.3). This includes both endpoints and every feasible zero pair-mass boundary. There are exactly $\binom{s}{m}$ distinct labeled marginal patterns. For each pattern, (19.4) is an affine bijection from the full compact polytope $\mathcal Z_C(t)$ onto the entire minimizing-law fibre, with inverse $z_{ij}=\bar x_{\{i,j\}}$ and affine dimension

$$
\binom m2-m=\frac{m(m-3)}2.
\tag{19.23}
$$

Its relative interior consists of the arrays with every edge positive; its relative boundary consists of the arrays with at least one zero edge. Its vertices have positive-support components that partition $C$ into single edges and odd cycles: single edges have mass $t$, and cycle edges have mass $t/2$. No further endpoint equality laws occur.

For every $0<\delta<\delta_-$ and every $\delta_+<\delta\le1$, each saturated actual law admits an actual dense-law perturbation of the same mean with strictly smaller energy. Thus (19.21) concerns exact global minimization in the original domain, not merely validity of an auxiliary stationary condition.

**Proof.** The constant edge array $z_{ij}=t/(m-1)$ is strictly positive and feasible. Every feasible array has total pair mass $mt/2=\delta$; the singleton mass in (19.4) is $\theta$. Hence these are nonnegative laws of total mass one, with only omission sizes two and one. Their atoms are nonempty, their mean is $a\delta+r\theta=q$, and their actual marginals are exactly $U$ on $C$ and $V$ on $N$. On all $0<\delta\le1$ these are at least $1/2$ and $1-2/a$, respectively, whereas $\tau\le9/a<1/2$. Thus (19.4) is an original dense actual law throughout that range, without requiring $U>V$ for its feasibility.

For any such law its incidence second moments are

$$
\begin{aligned}
M_C&=r^2U-c(\delta-t)=a^2U+c\theta
 &&\text{at each label of }C,\\
M_N&=r^2V-c\delta
 &&\text{at each label of }N.
\end{aligned}
\tag{19.24}
$$

Dividing by the squared actual marginals gives energy $S=m f(U)+n g(V)$, independently of the chosen edge array.

Now let $\delta\in[\delta_-,\delta_+]$. Lemma 19.2 gives $E_0\le0\le E_1$, and $E_1-E_0>0$. Choose

$$
\rho=\frac{E_1}{E_1-E_0}\in[0,1],\qquad
\rho E_0+(1-\rho)E_1=0.
\tag{19.25}
$$

For any original dense actual law, combine its two bounds (19.11) with these nonnegative coefficients. This gives $H(x)\ge S$, with the same $S$ independently of the ordering labels. Equation (19.24) attains it and proves (19.22).

If a law attains $S$, its nonnegative gaps in this convex combination vanish for each positively weighted bound. At least one weight is positive. Lemma 19.3 then fixes all individual marginals to $y^C$. The strict inequality $U>V$ recovers $C$ uniquely as its high-marginal labels.

For $\delta\in[\delta_-,\delta_+)$, one has $\rho>0$, including $\rho=1$ at $\delta_-$. Equality in the first certificate permits only singleton omissions and pair omissions within $C$. Their total masses must be $\theta$ and $\delta$, since the mean is $q$. The sum of omission probabilities on $C$ is $m(1-U)=2\delta$. The internal pairs already account for all $2\delta$, so every singleton omission in $C$ has mass zero. Consequently the pair degree at every label of $C$ is $t$, and each singleton omission in $N$ has mass $1-V=\theta/n$. These are exactly (19.3)–(19.4).

At $\delta=\delta_+$ the available weight is $1-\rho=1$. The second certificate permits only singleton omissions in $N$ and arbitrary pair omissions. Again their total masses are $\theta$ and $\delta$. The total omission probability on $N$ is $n(1-V)=\theta$, already exhausted by its singleton masses. Thus every pair incident to $N$ has mass zero. The remaining pair degrees and singleton masses are precisely (19.3)–(19.4). This explicitly removes the additional zero-residual atoms at the second endpoint. At the first endpoint the preceding high-omission count removes its additional singleton atoms. No positivity of individual edge masses was used.

The strict marginal gap proves the count $\binom{s}{m}$ and disjointness of the recovered patterns. The displayed coordinate inverse proves the affine bijection and compactness. The classical intermediate polytope here is Roger E. Behrend's $\mathcal P(K_C,b)$ with $b_i=t>0$, in *Fractional Perfect b-Matching Polytopes. I: General Theory*, definition (2), [arXiv:1301.7356v1](https://arxiv.org/html/1301.7356v1), DOI [10.1016/j.laa.2013.10.001](https://doi.org/10.1016/j.laa.2013.10.001). Its Corollary 19 applies because $K_C$ is finite, connected and nonbipartite and the constant edge array above is strictly positive. It gives dimension $|E|-|C|$, proving (19.23). Strict positive feasibility also identifies the relative interior and boundary as stated: a positive array has a small relative neighborhood remaining positive, while each zero coordinate lies on a proper supporting coordinate hyperplane.

Behrend's Theorem 22 says that a feasible array is a vertex exactly when each positive-support component is acyclic or has exactly one cycle, of odd length. Here no label is isolated because $t>0$. A leaf in a tree component forces its incident edge to have mass $t$, exhausting the degree of its neighbor; positivity then forces that component to be just that edge. The same argument rules out attached trees at a unicyclic component. Thus the remaining components are bare odd cycles, whose degree equations uniquely give edge mass $t/2$. Conversely any partition into single edges and odd cycles with these masses is feasible and satisfies Behrend's criterion. These attributed facts describe the fibre geometry, rather than supply the all-law nonlinear minimum proved above.

It remains to prove necessity of the interval by actual-law descents. Fix any saturated law, including one with zero internal edges. If $0<\delta<\delta_-$, choose $i\in C$ and $h\in N$ and move mass $\varepsilon>0$ from the singleton omission $\{h\}$ to the singleton omission $\{i\}$. All pairs stay fixed. For sufficiently small $\varepsilon$, this is a dense actual law of the same mean, since $\theta/n>0$, and its changed marginals are $U-\varepsilon$ at $i$ and $V+\varepsilon$ at $h$. Using (19.24), its energy derivative at zero is

$$
\left(-\frac{r^2}{U^2}+\frac{2M_C}{U^3}\right)
 +\left(\frac{r^2}{V^2}-\frac{2M_N}{V^3}\right)
=-\left(f'(U)+\frac c{U^2}\right)+g'(V)
=-E_0<0.
\tag{19.26}
$$

If $\delta_+<\delta\le1$, choose $h\in N$. Replace every old internal edge mass by $(1-\varepsilon/\delta)z_{ij}$ and add pair-omission mass $\varepsilon/m$ at each $\{i,h\}$, $i\in C$. Leave all singleton masses fixed. For sufficiently small $0<\varepsilon<\delta$ this is a nonnegative actual law, still with pair mass $\delta$, singleton mass $\theta$ and mean $q$. Its high pair degrees decrease by $\varepsilon/m$ each, and the pair degree at $h$ increases by $\varepsilon$. Thus the changed marginals are $U+\varepsilon/m$ on $C$ and $V-\varepsilon$ at $h$; they remain dense. The moment derivatives are $a^2/m$ at each high label and $-a^2$ at $h$. Its energy derivative is therefore

$$
\left(\frac{a^2}{U^2}-\frac{2M_C}{U^3}\right)
 -\left(\frac{a^2}{V^2}-\frac{2M_N}{V^3}\right)
=f'(U)-g'(V)+\frac c{V^2}
=E_1<0.
\tag{19.27}
$$

The sign follows from Lemma 19.2 even beyond $\delta_{\rm eq}$. The construction still works at $\delta=1$, when the singleton masses vanish. These two directions preserve all actual mass and mean constraints and apply to every feasible edge array. Differentiability and the strict negative derivatives yield smaller energies for sufficiently small positive $\varepsilon$. This proves necessity throughout $0<\delta\le1$. ∎

**Proposition 19.5 (Threshold widths, collision equations and scope).** For fixed $m$, as $a\to\infty$, the thresholds in Lemma 19.2 satisfy

$$
\begin{aligned}
\delta_j&=\frac{m}{2a}+\frac{m(m-8)}{4a^2}
 +\frac{m(m^2-8m+60+16j)}{8a^3}+O_m(a^{-4}),
 \qquad j=0,1,\\
\delta_+-\delta_-&=\frac{2m}{a^3}+O_m(a^{-4}).
\end{aligned}
\tag{19.28}
$$

The lower endpoint is the high/intermediate collision of the algebraic stationarity equations (18.23) for $k=m-1$:

$$
u=w=U,\quad v=V,\quad
2\delta-k(1-u)=t,\quad 1-w-t=0,\quad E_0=0.
\tag{19.29}
$$

The upper endpoint is their intermediate/low collision for $k=m$:

$$
u=U,\quad w=v=V,\quad
2\delta-k(1-u)=0,\quad E_1=0.
\tag{19.30}
$$

In (19.29) the lower multiplicity is $n$; in (19.30) it is $n-1$, in addition to the displayed intermediate label. These are collision relations and exact endpoint laws, without a classification of the adjacent open branches.

**Proof.** Put $h=1/a$. After cancellation, $hP_j$ under each substitution below is a rational function of $h$ with denominator nonzero near $h=0$ for fixed $m$. In particular

$$
V=1-\frac{h(1-\delta)}{1+(2-m)h}.
$$

First substitute $\delta=(m/2)h+b h^2$ into $hP_j$. Taylor expansion gives

$$
hP_j=\left(m-8-\frac{4b}{m}\right)h+O_{m,b}(h^2).
\tag{19.31}
$$

With $b=m(m-8)/4$, substitute $\delta=(m/2)h+b h^2+d h^3$ instead. The next coefficient is

$$
hP_j=\left(\frac{m^2-8m+60+16j}{2}
             -\frac{4d}{m}\right)h^2+O_{m,d}(h^3).
\tag{19.32}
$$

These expansions follow by inserting (19.1) into (19.5) and collecting powers; their remainders are Taylor remainders of the indicated rational functions, bounded on a fixed sufficiently small $h$-interval for each fixed $m,b,d$. Choose $d=m(m^2-8m+60+16j)/8$ and denote the resulting trial value by $\widehat\delta_j$. Equations (19.31)–(19.32) give $P_j(\widehat\delta_j)=O_m(h^2)$ and hence $E_j(\widehat\delta_j)=O_m(h^2)$, since $U,V\to1$. For all sufficiently small positive $h$ the trial value lies in the coalescence range: indeed

$$
\delta_{\rm eq}=\frac m2h+\frac{m(m-4)}4h^2+O_m(h^3),
\qquad \delta_{\rm eq}-\widehat\delta_j=m h^2+O_m(h^3)>0.
$$

The derivative estimate (19.7) and the mean value theorem now give

$$
|\widehat\delta_j-\delta_j|
\le\frac{m}{2a^2}|E_j(\widehat\delta_j)|=O_m(h^4).
\tag{19.33}
$$

This proves the remainder and both expansions in (19.28), rather than only their formal coefficients.

For (19.29), take $k=m-1$ in the algebraic formula (18.3). At $u=w=U$ its intermediate pair degree is $2\delta-(m-1)t=t$, and its intermediate singleton mass is $1-U-t=0$. The high and intermediate derivatives both equal $f'(U)+c/U^2$, so their equality with the lower derivative is exactly $E_0=0$. For (19.30), take $k=m$. At $u=U$, the intermediate degree is zero, and at $w=v=V$ the intermediate derivative already equals $g'(V)$; the remaining stationarity equation is $E_1=0$. Every denominator is positive. At the lower collision the choice of which of the $m$ high labels is called intermediate is redundant; at the upper collision the choice among the $n$ low labels is redundant. Neither choice adds a labeled pattern to the $\binom{s}{m}$ in Theorem 19.4.

The new conclusions here are the two finite thresholds, their strict order and width, the all-cardinality supporting bounds across the collision, and the exhaustive actual-law minimum on their closed interval, with genuine descents outside it. The finite Jensen, supporting-plane and fractional perfect matching geometry are used only in the attributed intermediate roles in Lemma 19.3 and Theorem 19.4. The result asserts no classification of all neighboring open phases, no growing-$m$ asymptotic regime, no least sufficient $A(m)$, no small-$a$ classification, no comparison with the unrestricted rare minimum and no realization by a finite graph with prescribed budgets. The full technical overlap with Zhao–Zhao, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), remains unassessed; that full text is not an input to these deductions. No worldwide priority claim is made. ∎

## 追加锚（第18节之后为增补区）

## 20. Complete neighboring inter-saturation phases

**Definition 20.1 (Neighboring blocks and the original domain).** Fix an integer $m\ge4$ and an integer $a\ge2^{16}m^2$. Put $M=m+1$, $r=a+1$, $s=a+2$, $c=2a+1$, and retain $q=r-\delta$, $\theta=1-\delta$, $\gamma=c\delta$ and $\tau=3(2a+3)\delta/r^2$. The domain is exactly Definition 11.1: one actual probability law on every nonempty $T\subseteq[s]$, with actual mean $q$ and actual marginals at least $\tau$. The energy, dense infimum and subtractand are $H$, $\mathscr D_a(\delta)$ and $B$ from Definitions 1.1 and 11.1. No restriction of cardinality or positive support is imposed. Write $\bar x_J=x_{[s]\setminus J}$ for proper omission sets.

For $p\in\{m-1,m,m+1\}$ define

$$
\begin{gathered}
n_p=s-p,\quad U_p=1-2\delta/p,\quad
V_p=1-(1-\delta)/n_p,\quad \xi_p=1-2/p,\quad
\Delta_p=\frac{p}{2a+4-p},\\
f(z)=a^2/z+c\theta/z^2,\qquad g(z)=r^2/z-c\delta/z^2,\\
E_{0,p}=f'(U_p)+c/U_p^2-g'(V_p),\qquad
E_{1,p}=f'(U_p)+c/V_p^2-g'(V_p),\\
P_{j,p}=(r^2+jc)U_pV_p(U_p^2-V_p^2)
 -2c\delta(U_p^3-\xi_pV_p^3)\quad(j=0,1).
\end{gathered}
\tag{20.1}
$$

The primes on $f,g$ denote differentiation in their argument. The roots specified below define $\delta_{-,p}$ and $\delta_{+,p}$. In particular $\delta_{\pm,m}$ are exactly the thresholds of §19. For $k\in\{m-1,m\}$ set

$$
\alpha_k=\delta_{+,k},\qquad \beta_k=\delta_{-,k+1},\qquad
n=s-k-1,
\tag{20.2}
$$

and use the algebraic functions $\mathcal G_{P,h}$ and $F_k(u,w)$ of (18.3), with $|P|=k$, $h\notin P$ and $N=[s]\setminus(P\cup\{h\})$. Here these functions are defined without the fixed-$\eta$ assumptions of (18.1).

**Lemma 20.2 (The three exact neighboring threshold pairs).** For each $p$ in Definition 20.1, $E_{j,p}$ has exactly one zero on $[0,1]$, and

$$
0<\delta_{-,p}<\delta_{+,p}<\Delta_p<p/a\le M/a.
\tag{20.3}
$$

The respective roots are equivalently the unique roots of $P_{0,p}$ and $P_{1,p}$ in $(0,\Delta_p)$. Moreover $E_{0,p}\le0\le E_{1,p}$ holds exactly on $[\delta_{-,p},\delta_{+,p}]$.

**Proof.** This includes $p=3$ when $m=4$. The original bound on $a$ implies $a\ge600p$, $n_p\ge a/2$, $c\le3a$, $U_p\ge1/3$ and $V_p\ge1-2/a$ on $[0,1]$. Write

$$
A=V_p^{-2}-U_p^{-2},\quad C=V_p^{-3}-\xi_pU_p^{-3},\quad R_j=r^2+jc.
$$

The identity $U_p-\theta=\xi_p\delta$ gives $E_{j,p}=R_jA-2c\delta C=P_{j,p}/(U_p^3V_p^3)$. Its derivative satisfies

$$
\begin{aligned}
A'&=-2/(n_pV_p^3)-4/(pU_p^3)\le-4/p,\\
C'&=-3/(n_pV_p^4)-6\xi_p/(pU_p^4),\\
E_{j,p}'&\le-4a^2/p+54c+12c/n_p+972c/p\\
&\le-4a^2/p+1134a+72
 \le-4a^2/p+1200a\le-2a^2/p<0.
\end{aligned}
\tag{20.4}
$$

Here $V_p^{-3},V_p^{-4}<2$, $U_p^{-3}\le27$, $U_p^{-4}\le81$ and $0\le\xi_p\le1$ justify the bounds. At zero $E_{j,p}=R_j(V_p^{-2}-1)>0$. At $\Delta_p$, $U_p=V_p$ and $E_{j,p}=-2c\Delta_p(1-\xi_p)/U_p^3<0$. In $(0,\Delta_p)$ one has $U_p>V_p$ and $E_{1,p}-E_{0,p}=c(V_p^{-2}-U_p^{-2})>0$. Strict decrease proves every assertion. Thus neither $p=3$ nor $p=m+1$ requires an enlarged bound on $a$. ∎

**Lemma 20.3 (A legal branch on the whole gap).** For each $k\in\{m-1,m\}$ one has $\alpha_k<\beta_k$. On the entire interval $\alpha_k<\delta<\beta_k$, there is exactly one triple satisfying

$$
ku+w+nv=q,\qquad \tau<v<w<u<1
\tag{20.5}
$$

and the two algebraic equations (18.18). It is the unique minimum of $\mathcal G_{P,h}$ on $\mathcal B_q=\{y\in[9/10,1]^s:\sum_i y_i=q\}$, with coordinates $u$ on $P$, $w$ at $h$ and $v$ on $N$. Put

$$
t=1-u,\qquad d=2\delta-kt,\qquad e=t-d.
\tag{20.6}
$$

Throughout that open interval,

$$
0<d<t,\qquad 1-w-d=e+u-w>0.
\tag{20.7}
$$

The triple extends continuously to both endpoints, with exact values

$$
\begin{array}{c|ccc|cc}
\delta&u&w&v&d&e\\ \hline
\alpha_k&U_k&V_k&V_k&0&1-U_k\\
\beta_k&U_{k+1}&U_{k+1}&V_{k+1}&1-U_{k+1}&0
\end{array}
\tag{20.8}
$$

where each entry on a row is evaluated at that row's $\delta$.

**Proof.** Work first on the larger auxiliary parameter interval $I=[0,M/a]$, without assuming marginal ordering or actual-law realizability. For either $k$, $n\ge a/2$, $0\le\delta<1/2$ and $\gamma\le3M$. The only off-diagonal Hessian entries of $\mathcal G=\mathcal G_{P,h}$ are $\mathcal G_{ih}=-2c/y_h^3$ for $i\in P$; these are nonpositive, of absolute value at most $9a$. As in the direct differentiation in (18.19), the diagonal lower bounds on the whole box are

$$
2a^2\quad(i\in P),\qquad
2a^2-4ka\quad(i=h),\qquad
2a^2-36M\quad(i\in N).
\tag{20.9}
$$

Indeed $D_y=\sum_{i\in P}y_i+\delta-k\ge-k/10$, $z^{-3}<3/2$ and $z^{-4}<2$ on $[9/10,1]$. Subtracting the absolute off-diagonal row sums leaves at least $a^2$. The inequality $2|z_iz_h|\le z_i^2+z_h^2$ therefore proves $\nabla^2\mathcal G\succeq a^2I_s$. These estimates also hold for $k=p-1,p$ for any of the three $p$ in Definition 20.1: then $k\le M$ and the same original bound on $a$ still dominates every displayed error term. This observation will supply the saturated endpoint certificates.

For the present $k\in\{m-1,m\}$ the compact convex slice contains $\mu\mathbf1$, $\mu=q/s$, so it has a unique minimizer $y^*$. Set $h_0=1-\mu=(1+\delta)/s$ and $d_0=2\delta-kh_0$. On $I$,

$$
\frac1{a+2}\le h_0\le\frac2a,\qquad |d_0|\le\frac{4M}{a},\qquad \mu^{-3}<2.
\tag{20.10}
$$

Subtracting $g'(\mu)$ from each entry of $\nabla\mathcal G(\mu\mathbf1)$ gives entries $-2ch_0/\mu^3$ on $P$, $-2cd_0/\mu^3$ at $h$, and zero on $N$. Their Euclidean norm is at most $24\sqrt k+48M\le72M$. Strong convexity and the minimizing inequality yield

$$
\frac{a^2}{2}\|y^*-\mu\mathbf1\|^2
 \le72M\|y^*-\mu\mathbf1\|,
\qquad \|y^*-\mu\mathbf1\|\le\frac{144M}{a^2}.
\tag{20.11}
$$

Since $a>576M$, this places every coordinate strictly between $9/10$ and $1$. Uniqueness and invariance under permutations of $P$ and of $N$ give coordinates $u,w,v$, with no ordering asserted yet. The stationarity equations are exactly

$$
f'(u)+c/w^2=-r^2/w^2-2c(ku+\delta-k)/w^3=g'(v).
\tag{20.12}
$$

We need a uniform variation bound, including the transition layers. Write $Q=\nabla^2\mathcal G(y^*)$. Besides (20.9), every diagonal entry is at most $4a^2$: the top entries are at most $3a^2+36a$, the middle one at most $3r^2+36M$ since $D_y\le\delta$, and the lower ones at most $3r^2$. Consequently

$$
Q_{ij}\le0\ (i\ne j),\qquad
 a^2\mathbf1\le Q\mathbf1\le5a^2\mathbf1.
\tag{20.13}
$$

The bordered stationary system is nonsingular. Indeed $Qz=\ell\mathbf1$, $\mathbf1^Tz=0$ implies $z^TQz=0$, hence $z=0$ and $\ell=0$. The implicit function theorem and uniqueness make $y^*(\delta)$ continuously differentiable on $I$, with one-sided derivatives at its ends.

For clarity the inverse estimate used next follows directly from (20.13). If $Qz\ge0$ and a smallest coordinate $z_i$ were negative, then

$$
(Qz)_i=(Q\mathbf1)_iz_i+
 \sum_{j\ne i}Q_{ij}(z_j-z_i)<0,
$$

a contradiction. Thus $Q^{-1}$ is entrywise nonnegative, and

$$
(5a^2)^{-1}\mathbf1\le Q^{-1}\mathbf1\le a^{-2}\mathbf1.
\tag{20.14}
$$

At fixed $y$, the $\delta$ derivative $b=\partial_\delta\nabla\mathcal G$ has entries $2c/y_i^3$ on $P\cup N$ and $-2c/y_h^3$ at $h$. Hence $\|b\|_\infty\le12a$. Differentiating stationarity and the mean gives

$$
Q(y^*)'+b=\ell'\mathbf1,\quad \mathbf1^T(y^*)'=-1,\quad
\ell'=\frac{\mathbf1^TQ^{-1}b-1}{\mathbf1^TQ^{-1}\mathbf1}.
\tag{20.15}
$$

Nonnegativity of $Q^{-1}$ bounds the weighted average of $b$ in this quotient by $12a$ in absolute value. Its remaining term is at most $5a^2/s<5a$. Equations (20.14)–(20.15) imply

$$
\|(y^*)'\|_\infty\le29/a,\qquad
 d'=2+ku'>1,\qquad e'=-(k+1)u'-2<-1.
\tag{20.16}
$$

All three estimates hold on the whole $I$, not just near an endpoint.

At $\delta=\alpha_k$, the vector $(u,w,v)=(U_k,V_k,V_k)$ is inside the box and satisfies the mean and (20.12): its middle derivative equals $g'(V_k)$ because $d=0$, and the remaining equation is $E_{1,k}=0$. At $\delta=\beta_k$, $(u,w,v)=(U_{k+1},U_{k+1},V_{k+1})$ is similarly stationary; now $d=t$ and the remaining equation is $E_{0,k+1}=0$. Strong convexity identifies both with $y^*$, proving (20.8) independently of their order. Since $d(\alpha_k)=0$, $d(\beta_k)=1-U_{k+1}>0$ and $d'>1$ on $I$, it follows that $\alpha_k<\beta_k$. Strict monotonicity then gives $d>0$ and $e>0$ throughout their open gap.

To convert these capacity signs into strict marginal ordering, (20.12) gives the exact identities

$$
\begin{aligned}
g'(w)-g'(v)&=2cd/w^3,\\
f'(u)-f'(w)-2c(u-w)/w^3&=2ce/w^3.
\end{aligned}
\tag{20.17}
$$

On the box, $g''>0$ by (20.9). Also $f''\ge2a^2$ and $2c/w^3\le9a<2a^2$. Writing $f'(u)-f'(w)=(u-w)\int_0^1f''(w+t(u-w))\,dt$ shows that $u-w$ has the sign of $e$. The first identity shows that $w-v$ has the sign of $d$. Thus $u>w>v$, $d<t$ and $1-w-d=e+u-w>0$. Furthermore $\tau\le9M/a^2<9/10<v$.

Clearing the positive denominators in (20.12) gives precisely (18.18). Conversely any triple satisfying (20.5) and those equations has $v\ge1-(1+\delta)/n\ge1-3/a>9/10$. It is therefore an interior stationary vector on the same slice, and strict convexity makes it $y^*$. This proves uniqueness in the entire legal region. The convex supporting and finite averaging inequalities used here and below are the classical results in Boyd and Vandenberghe, *Convex Optimization*, §§3.1.3 and 3.1.8, pp.69–70 and 77–78, [author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf); the quantitative variation estimate (20.16) follows from the displayed Hessian computation. ∎

**Theorem 20.4 (The two full open phases and every actual minimizing law).** Under Definition 20.1, both intervals

$$
(\delta_{+,m-1},\delta_{-,m}),\qquad
(\delta_{+,m},\delta_{-,m+1})
\tag{20.18}
$$

are nonempty. On either, use its corresponding $k=m-1$ or $k=m$, the unique triple of Lemma 20.3, and $t,d$ from (20.6). The exact original-domain global minimum is

$$
\boxed{\ \mathscr D_a(\delta)=F_k(u,w)
 =k f(u)+\frac{r^2}{w}+\frac{c(d-\delta)}{w^2}+n g(v).\ }
\tag{20.19}
$$

The dense minimum of $d(x)$ is this value minus $B$. Precisely all attaining actual laws are (18.28)–(18.29), for every choice of $P,h$ and every nonnegative edge array in that closed degree polytope. Every feasible zero edge is included. The $\binom sk(s-k)$ marginal patterns are distinct. For each pattern the array-to-law map is an affine bijection, with inverse $z_{ij}=\bar x_{\{i,j\}}$, and dimension $(k+1)(k-2)/2$.

For each support $E\subseteq\binom{P\cup\{h\}}2$ admitting a feasible array positive exactly on $E$, the corresponding closed face has dimension $|E|-(k+1)+B(E)$, with $B(E)$ the number of bipartite components of the spanning support graph. Its relative interior consists of the arrays positive exactly on $E$. These are all faces. In particular the full fibre's relative boundary consists exactly of its arrays with at least one zero edge. The vertex laws have positive pair-support components that are trees or have just one cycle of odd length. Label equivalence is exactly permutation of $P$ fixing $h$, after identifying the recovered marginal groups, as in §18.

**Proof.** First reestablish the all-cardinality bound without invoking a fixed-$\eta$ hypothesis. Sort the marginals of an arbitrary original dense law, take its first $k$ labels as $P$ and its next as $h$, and put $\omega=y_h^{-2}$, $\alpha_i=y_i^{-2}$ and $b_i=c(\omega-\alpha_i)_+$. The ordered mean implies

$$
y_h\ge1-(1+\delta)/(s-k)\ge1-3/a,\qquad
1\le\omega<16/15,\qquad \alpha_i\ge1.
\tag{20.20}
$$

For $R_y(T)$ defined by (18.5), the singleton- and pair-omission residuals are respectively $b_i$ and $c\sum_{i\notin T}(\alpha_i-\omega)_+$. The full-set residual is $2\sum_i\alpha_i+2c\omega>0$. For every other nonempty cardinality, put $e_J=s-|T|\in[3,s-1]$. The bracket multiplying $r-|T|$ in (18.5) is bounded below by

$$
3se_J-2s-e_J-e_J^2-2c\omega
 \ge7s-12-2c\omega>(41a-2)/15>0.
\tag{20.21}
$$

The quadratic is concave and has endpoint values $7s-12$ and $2s(s-2)$. Thus the residual is nonnegative over every allowed cardinality and has exactly the zero set (18.6). Taking expectation gives the algebraic same-law identity (18.7) with the present $k,\delta$.

Both $f$ and $g$ are strictly convex on the entire original dense interval $[\tau,1]$: their second derivatives are (18.14), and $r^2\tau-3c\delta=6\delta>0$. Average on $P$ and on $N$, leaving $h$ fixed. Finite Jensen gives $H(x)\ge\mathcal G_{P,h}(z)$ for the grouped vector $z$. Its lower coordinate is at least $1-(1+\delta)/n\ge1-3/a$; ordering bounds every other grouped coordinate below by this one. Hence $z\in\mathcal B_q$, even if an original individual marginal lies outside the box. Lemma 20.3 now gives $H(x)\ge F_k(u,w)$.

For attainment and exhaustive reconstruction, (20.7) supplies a strictly positive array of the degree polytope:

$$
z_{ih}^{\circ}=d/k\quad(i\in P),\qquad
z_{ij}^{\circ}=(t-d/k)/(k-1)\quad(i,j\in P,\ i\ne j).
\tag{20.22}
$$

Every nonnegative array with those same degrees has total pair mass $(kt+d)/2=\delta$. Its singleton masses in (18.29) sum to $1-\delta$, since the mean equation gives

$$
kt+(1-w)+n(1-v)=1+\delta.
\tag{20.23}
$$

They are strictly positive by (20.7) and $v<1$. Thus (18.29) is an actual probability law of mean $a\delta+r(1-\delta)=q$, whose actual marginals are exactly $u,w,v>\tau$. For every such array, including its entire boundary, direct incidence counting gives (18.36); division by the squared actual marginals gives (20.19).

If an actual law attains this bound, strict convexity fixes its grouped vector to $y^*$, and strict Jensen fixes every individual marginal in each group. The strict inequalities $u>w>v$ recover $P,h,N$ uniquely. The zero residuals permit only singleton omissions outside $P$ and pair omissions within $S=P\cup\{h\}$. Their total pair mass is forced to be $\delta$ by the mean. Each $i\in P$ has pair degree $1-u=t$, the degree at $h$ is consequently $2\delta-kt=d$, and its singleton mass must be $1-w-d$. Every $j\in N$ has singleton mass $1-v$. This is exactly the entire closed fibre (18.28)–(18.29), with no exclusion of any zero coordinates.

For the geometric assertions use the classical intermediate results of Behrend, *Fractional Perfect b-Matching Polytopes. I: General Theory*, [arXiv:1301.7356v1](https://arxiv.org/html/1301.7356v1), definition (2), Corollary 19 and Theorem 22, DOI [10.1016/j.laa.2013.10.001](https://doi.org/10.1016/j.laa.2013.10.001). The fibre is $\mathcal P(K_S,b)$ with degrees $t$ on $P$ and $d$ at $h$. These are positive, and (20.22) is strictly positive, so Corollary 19 applies on the connected nonbipartite $K_{k+1}$, including $k=3$. The same corollary applies to each stated support graph because its strictly positive element is part of the support hypothesis. It gives exactly the dimensions above. Coordinate nonnegativity makes positive arrays the relative interior; blending with a positive array shows that each stated closed support face is the closure of its relative interior. Every face is obtained by setting its relative interior point's zero coordinates to zero, by the segment argument in the proof of Theorem 18.4. Theorem 22 gives exactly the vertex criterion. These are attributed matching-polytope facts used to describe the reconstructed actual-law fibres. Finally the recovered strict groups give both the pattern count and the label equivalence. ∎

**Theorem 20.5 (All endpoint fibres and their limits).** For every $p\in\{m-1,m,m+1\}$, on the entire closed saturated interval $[\delta_{-,p},\delta_{+,p}]$ one has

$$
\mathscr D_a(\delta)=p f(U_p)+(s-p)g(V_p).
\tag{20.24}
$$

Every minimizing actual law is exactly (19.3)–(19.4) with $m$ replaced by $p$: choose a $p$-element block $C$, all nonnegative internal edge arrays of degree $t_p=2\delta/p$, singleton mass $(1-\delta)/(s-p)$ at every label outside $C$, and zero on every other omission set. This includes both thresholds and all zero-edge arrays. The high block is uniquely recovered, giving $\binom sp$ marginal patterns. Each fibre has dimension $p(p-3)/2$, relative interior given by positive internal edges, and relative boundary given by at least one zero internal edge. Its vertices partition $C$ into single edges of mass $t_p$ and odd cycles of edge mass $t_p/2$. For $p=3$ the fibre is a single triangle with edge mass $t_p/2$, dimension zero and empty relative boundary.

Consequently each closed interval $[\alpha_k,\beta_k]$ consists of the open phase of Theorem 20.4 and precisely the saturated endpoint classes just stated. At $\alpha_k$, $h$ is any one of the $s-k$ low labels and adds no marginal pattern. At $\beta_k$, $h$ is any one of the $k+1$ high labels, again adding no marginal pattern. The minimum (20.19) tends to (20.24) at both ends. Every endpoint minimizing actual law is a limit, in its full vector of atom masses, of interior minimizing laws. Conversely every convergent sequence of interior minimizers approaching an endpoint has one of exactly these saturated endpoint limits.

**Proof.** The threshold argument of Lemma 20.2 applies under the original bound on $a$. On $0<\delta<\Delta_p$, the bounds needed for the two saturated certificates are

$$
n_p-1\ge a/2,\quad \gamma<3p,\quad \tau<9p/a^2<9/10,
\quad U_p,V_p>1-2/a>9/10.
\tag{20.25}
$$

For the pivots with $k=p-1$ and $k=p$, the ordered-mean and grouped-mean bounds (20.20) and the all-cardinality residual calculation (20.21) hold unchanged. The Hessian estimate (20.9) applies to these pivots, as explicitly checked there for $k\le M$. Thus the algebraic identities (19.19), followed by strict Jensen and the supporting inequality, give for every original dense actual law both bounds

$$
H(x)\ge S_p+E_{0,p}D_C,\qquad
H(x)\ge S_p+E_{1,p}D_C,\quad
S_p=p f(U_p)+n_p g(V_p),\quad
D_C=\sum_{i\in C}y_i-pU_p,
\tag{20.26}
$$

where $C$ is its first $p$ labels. Equality in either fixes all individual marginals to $U_p$ on $C$ and $V_p$ outside. This uses exactly the strict Hessian supporting term and strict Jensen, not a hypothesis $p\ge4$ or $a\ge2^{16}p^2$.

On $[\delta_{-,p},\delta_{+,p}]$, combine the bounds with weights $\rho=E_{1,p}/(E_{1,p}-E_{0,p})$ and $1-\rho$. They are nonnegative, sum to one, and cancel the $D_C$ term. Every saturated law in the statement is feasible and has energy $S_p$: its pair mass is $pt_p/2=\delta$, singleton mass is $\theta$, and its actual marginals and second moments are the algebraic formulas (19.24) with $p$ in place of $m$. This proves (20.24).

For equality, at least one supporting weight is positive, fixing all individual marginals; $U_p>V_p$ recovers $C$. When $\rho>0$, the first residual permits singleton omissions anywhere and pair omissions only inside $C$. The pair mass is $\delta$, already accounting for the entire omission probability $p(1-U_p)=2\delta$ on $C$. Thus singleton omissions on $C$ have zero mass. When $\rho=0$, namely at $\delta_{+,p}$, the second residual permits singleton omissions only outside $C$ and arbitrary pairs. Their total singleton mass $\theta$ already exhausts the omission probability $n_p(1-V_p)=\theta$ outside $C$, so every pair incident outside $C$ has zero mass. Both cases give exactly the displayed saturated fibres, without a positivity assumption on any edge.

The constant internal edge array $t_p/(p-1)$ is strictly positive. Behrend's Corollary 19 therefore gives dimension $\binom p2-p$, and the coordinate argument gives its relative interior and boundary. By Theorem 22 each positive-support component at a vertex is a tree or is odd unicyclic. A leaf forces its incident edge to have mass $t_p$, exhausting the neighbor's degree, so a tree component must be a single edge and an odd unicyclic component has no attached trees. Its cycle edges have mass $t_p/2$. This proves the geometry, including the triangle case and all closed boundary arrays.

At $\alpha_k$, (20.8) has $d=0$, so nonnegativity forces all edges incident to $h$ to vanish; its singleton mass is $1-V_k$, like every other low label. The fibre is exactly the saturated $k$-block on $P$. At $\beta_k$, $d=t$ and $u=w$, so $1-w-d=0$ and the degree array is precisely the regular array on the $(k+1)$-block $S$. Thus choosing an intermediate label at either tied level is redundant in exactly the ways stated. Substitution in $F_k$ proves the endpoint values, since its algebraic expression agrees with $S_p$ at the two collision vectors.

To verify that every boundary law actually occurs as a limit, fix any nonnegative endpoint array $z^0$, and let $t_0$ be its positive common degree. At the left endpoint extend its array on $P$ to $S=P\cup\{h\}$ by

$$
z_{ij}(\delta)=\frac{t-d/k}{t_0}z^0_{ij}\quad(i,j\in P),\qquad
z_{ih}(\delta)=d/k\quad(i\in P).
\tag{20.27}
$$

This is nonnegative, has degrees $t$ on $P$ and $d$ at $h$, and tends to the prescribed array with zero hub edges. At the right endpoint, for any choice $h\in S$ and $P=S\setminus\{h\}$, put

$$
z_{ih}(\delta)=\frac d{t_0}z^0_{ih},\qquad
z_{ij}(\delta)=\frac d{t_0}z^0_{ij}+\frac{t-d}{k-1}
 \quad(i,j\in P).
\tag{20.28}
$$

Its degrees on $P$ are $d+(t-d)=t$ and its degree at $h$ is $d$. It is nonnegative and tends to $z^0$. The singleton formulas (18.29) converge to the stated endpoint masses as well. Thus both constructions give interior minimizing actual laws tending to every endpoint law, including every zero-edge law. Conversely there are finitely many choices of $P,h$; on any fixed-pattern subsequence, nonnegative arrays and their degree equations pass to the limit. Formula (20.8) then forces exactly the saturated class above. Every convergent sequence has such a subsequence with the same limit, proving the converse.

The full-gap legality, all-cardinality optimum and exhaustive continuation of the actual-law fibres in Lemma 20.3 and Theorems 20.4–20.5 are repo-derived conclusions. The convex inequalities and matching-polytope geometry are used only in the attributed intermediate roles above. The scope remains the original sufficient bound $a\ge2^{16}m^2$ and these two neighboring gaps and saturated endpoints; no least sufficient bound, small-$a$ classification, unrestricted rare/dense competition, growing-$m$ asymptotic theorem or prescribed finite-graph realization follows. The full text of Zhao–Zhao, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), is not a premise; technical overlap with it remains undetermined, and no worldwide priority is asserted. ∎

## 追加锚（第18节之后为增补区）
