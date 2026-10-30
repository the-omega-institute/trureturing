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
