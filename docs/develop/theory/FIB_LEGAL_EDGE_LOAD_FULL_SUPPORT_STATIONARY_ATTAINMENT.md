# Fibonacci harmonic-edge load: full-support stationary attainment

## 1. Domain, objective, and inherited facts

For $n\geq 1$, let

$$
B_n=\{b\in\{0,1\}^n:b_jb_{j+1}=0\ (1\leq j<n)\}.
$$

For $w\in B_n$, write $k(w)=\sum_{j=1}^nw_j$, and let
$\mathcal P(B_n)$ denote the probability simplex on $B_n$.

Let $\Gamma_n$ have vertex set $B_n$ and every legal Hamming-one edge. Write
$b+e_i$ for an upward edge, with the convention $b_0=b_{n+1}=0$. Thus the
endpoints, the all-zero word, and every legal open-path edge are included. Put

$$
h(s,t)=
\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}
\qquad
\Phi_n(\mu)=\sum_{\{b,c\}\in E(\Gamma_n)}h(\mu_b,\mu_c).
$$

Let $\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu)$. The following are
inherited source facts, with their original domains and hypotheses unchanged:

$$
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad
c_\star=\lim_{n\to\infty}{\kappa_n\over n},\qquad
c_\star n\leq\kappa_n\leq c_\star(n+1).
\tag{1.1}
$$

These are [Growth, Theorems 3.2 and 5.2]. For every $N$, [Positive Unique
Optimizer, Theorem 3.1] supplies a unique maximizer $\pi^{(N)}$ with

$$
{1\over3}\,\pi^{(N)}_b\leq\pi^{(N)}_{b+e_i}\leq\pi^{(N)}_b
\tag{1.2}
$$

on every legal upward edge. The lower constant $1/3$ is the weakest of the
endpoint and interior constants in that theorem. [Nonattainment, Theorem 1.5]
states that every normalized stationary law with positive legal cylinders and
finite visible Markov order has density strictly below $c_\star$.

## 2. Finite exterior risk

Let

$$
X=\{x\in\{0,1\}^{\mathbb Z}:x_jx_{j+1}=0\text{ for all }j\},
$$

and write $[w]$ for a cylinder. For a probability law $P$ on $X$ and $r\geq1$, set

$$
\mathcal F_r=\sigma(X_{-r},\ldots,X_{-1},X_1,\ldots,X_r),
\qquad
D_r(P)=\mathbb E_P\!\left[(X_0-\mathbb E_P[X_0\mid\mathcal F_r])^2\right].
$$

The two-point fiber identity gives the explicit formula

$$
D_r(P)=\sum_{\substack{a,v\in B_r\\a_r=v_1=0}}
h\bigl(P([a0v]),P([a1v])\bigr).
\tag{2.1}
$$

Indeed, after the exterior word $av$ is fixed, the center is either forced to
zero or has the two masses $s=P([a0v])$ and $t=P([a1v])$. Its conditional
squared risk is $st/(s+t)$, including the cases $s=0$, $t=0$, and $s=t=0$ by
the displayed definition of $h$. Consequently $D_r$ is continuous and
concave in $P$, because $h$ is continuous and concave ([Growth, Lemma 3.1]).

The fields $\mathcal F_r$ increase to $\mathcal F_\infty=\sigma(X_j:j\neq0)$.
The bounded martingale convergence theorem therefore gives

$$
D_r(P)\downarrow D_\infty(P):=
\mathbb E_P\!\left[(X_0-\mathbb E_P[X_0\mid\mathcal F_\infty])^2\right].
\tag{2.2}
$$

In particular, $D_\infty=\inf_rD_r$ is upper semicontinuous for weak
convergence, since each $D_r$ is continuous.

For a probability vector $\mu$ on $B_n$, let $\Phi_{n,i}(\mu)$ be the sum of
$h(\mu_b,\mu_{b+e_i})$ over the legal fibers at coordinate $i$. The same fiber
calculation gives

$$
\Phi_n(\mu)=\sum_{i=1}^n\Phi_{n,i}(\mu),\qquad
0\leq\Phi_{n,i}(\mu)\leq\frac14.
\tag{2.3}
$$

The bound follows from $h(s,t)\leq(s+t)/4$ and the fact that the coordinate
fibers form a matching. If $P$ is stationary and $P_n$ is its actual marginal
on an interval of length $n$, conditioning on all other coordinates in that
interval is a finite exterior conditioning. Conditional variance decreases
under refinement, so for $n\geq2r+1$,

$$
D_\infty(P)\leq {\Phi_n(P_n)\over n}
\leq { (n-2r)D_r(P)+r/2\over n}.
\tag{2.4}
$$

The left inequality holds at every coordinate. For the right inequality, the
$n-2r$ coordinates at distance at least $r$ from both endpoints have risk at
most $D_r(P)$, and the remaining $2r$ terms satisfy (2.3). First let
$n\to\infty$ in (2.4), then let $r\to\infty$. Thus every stationary $P$ has

$$
d(P):=\lim_{n\to\infty}{\Phi_n(P_n)\over n}=D_\infty(P).
\tag{2.5}
$$

Since $\Phi_n(P_n)\leq\kappa_n$, (1.1) and (2.5) imply

$$
d(P)\leq c_\star
\tag{2.6}
$$

for every stationary $P$, without a support or memory assumption.

## 3. One coherent stationary law at the optimum

**Theorem 3.1 (full-support stationary attainment).** There is one normalized,
two-sided, stationary probability law $Q_\star$ on $X$ such that, for every
$n\geq1$ and every $w\in B_n$,

$$
Q_\star([w])\geq2^{-(n+2)}3^{-k(w)}>0,
$$

and

$$
n c_\star\leq\Phi_n((Q_\star)_n)\leq\kappa_n\leq(n+1)c_\star.
$$

Consequently $d(Q_\star)=c_\star$, including along $n=3N$.

Embed $b\in B_N$ into $X$ by putting $b$ at coordinates $1,\ldots,N$ and
zeros elsewhere, and let $P_N$ be the pushforward of $\pi^{(N)}$. With
$(Tx)_j=x_{j+1}$ define

$$
A_N={1\over N}\sum_{i=1}^N(T^i)_*P_N.
\tag{3.1}
$$

Each $A_N$ is a probability law on the original shift $X$. The compactness of
$X$ and the weak compactness of its probability measures give a subsequence,
still denoted $A_N$, converging weakly to a probability law $Q_\star$ on $X$.
For every cylinder $C$,

$$
\left|(T_*A_N)(C)-A_N(C)\right|\leq {1\over N},
\tag{3.2}
$$

because the two spatial sums telescope to their two endpoint terms. Hence
$T_*Q_\star=Q_\star$; the limiting law is two-sided and stationary.

Fix $r$. Under $(T^i)_*P_N$, the center coordinate is the original bit $b_i$.
The radius-$r$ exterior reveals a subset of the other original word bits and
some deterministic padding. Its conditional risk is therefore at least the
risk after revealing all other original bits, namely $\Phi_{N,i}(\pi^{(N)})$.
Using the concavity of $D_r$ and (2.1),

$$
D_r(A_N)\geq {1\over N}\sum_{i=1}^ND_r((T^i)_*P_N)
\geq {1\over N}\sum_{i=1}^N\Phi_{N,i}(\pi^{(N)})
= {\kappa_N\over N}.
\tag{3.3}
$$

The first inequality is Jensen's inequality for the concave finite-cylinder
functional $D_r$. Passing to the selected limit and using (1.1) gives
$D_r(Q_\star)\geq c_\star$ for every $r$. Equations (2.2) and (2.6) now give

$$
d(Q_\star)=D_\infty(Q_\star)=c_\star.
\tag{3.4}
$$

Moreover, the coordinatewise conditional-variance comparison used for the
left side of (2.4) holds for every finite word, including $n<2r+1$. Summing it
over coordinates and combining it with (1.1) yields

$$
n\,c_\star\leq\Phi_n((Q_\star)_n)\leq\kappa_n\leq(n+1)c_\star
\qquad(n\geq1).
\tag{3.5}
$$

## 4. Support of the same law

Let $C$ be a finite exterior event, not involving coordinate $0$, and assume
$C\subseteq\{X_{-1}=X_1=0\}$. Every component $(T^i)_*P_N$ in (3.1) has
$1\leq i\leq N$, so its center is the original bit $b_i$.
Pair each center-zero word satisfying $C$ with its center-one insertion.
This is a legal bijection onto the center-one words satisfying $C$: both
neighbors are zero, and changing the center preserves every exterior
coordinate, including padding. Summing (1.2) over these pairs gives

$$
\frac13(T^i)_*P_N(C,X_0=0)
\leq(T^i)_*P_N(C,X_0=1)
\leq(T^i)_*P_N(C,X_0=0).
\tag{4.1}
$$

The inequalities survive averaging and cylinder limits. A monotone-class
argument extends them to every $C$ in the exterior sigma-field contained in
$\{X_{-1}=X_1=0\}$. Let
$p_\star=\mathbb E_{Q_\star}[X_0\mid\mathcal F_\infty]$. The Radon--Nikodym
form of (4.1) gives

$$
p_\star=0\quad\text{if }X_{-1}=1\text{ or }X_1=1,
\qquad
\frac14\leq p_\star\leq\frac12\quad\text{if }X_{-1}=X_1=0,
\tag{4.2}
$$

almost surely.

For any exterior event $A$ (with no condition on the neighbors), split it
according to whether both neighbors are zero. On the free part, (4.1) says
$Q_\star(A\cap\{X_{-1}=X_1=0\},X_0=0)\geq
Q_\star(A\cap\{X_{-1}=X_1=0\})/2$; on the complementary part legality
forces $X_0=0$. Hence, for every event $A$ not involving coordinate $i$,

$$
Q_\star(A,X_i=0)\geq\frac12Q_\star(A).
\tag{4.3}
$$

Applying (4.3) successively to the coordinates of an all-zero word gives

$$
Q_\star([0^m])\geq2^{-m}\qquad(m\geq1).
\tag{4.4}
$$

Let $w\in B_n$. Start with the cylinder $[0^{n+2}]$ and insert the $k(w)$
ones of $w$ one at a time in its middle $n$ coordinates. Every intermediate
word is legal and the inserted coordinate has two zero neighbors, even when
$w$ begins or ends with $1$. Applying (4.1) at each insertion gives

$$
Q_\star([w])\geq Q_\star([0w0])
\geq3^{-k(w)}Q_\star([0^{n+2}])
\geq2^{-(n+2)}3^{-k(w)}>0.
\tag{4.5}
$$

Thus every legal finite cylinder is positive. Every legal finite next-extension
$wz$ is another legal cylinder, so

$$
Q_\star([wz])/Q_\star([w])>0.
\tag{4.6}
$$

When the last bit of $w$ is $1$, legality makes the sole extension $z=0$ have
conditional probability one.

## 5. Memory consequence and source ownership

The law $Q_\star$ is normalized, two-sided, stationary, positive on every
legal cylinder, and has density $c_\star$ by (3.4). If it had finite visible
Markov order, all hypotheses of [Nonattainment, Theorem 1.5] would hold, and
that theorem would give $d(Q_\star)<c_\star$, contradicting (3.4). Therefore
$Q_\star$ has no finite visible Markov order. No ergodicity, uniqueness, hidden
state, Gibbs, or effective-construction assertion follows.

The only external probability facts used above are the bounded martingale
convergence theorem for the increasing finite exterior sigma-fields and weak
compactness of probability measures on a compact metrizable space. Their
hypotheses are exactly the bounded coordinate variable $X_0\in\{0,1\}$ and
the compact shift space $X$. All Fibonacci objective identities and all
insertion inequalities are owned by [Growth, Lemma 3.1 and Theorems 3.2, 5.2]
and [Positive Unique Optimizer, Theorem 3.1]; the finite-order contradiction is
owned by [Nonattainment, Theorem 1.5].

[Growth]: FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[Positive Unique Optimizer]: FIB_LEGAL_EDGE_LOAD_POSITIVE_UNIQUE_OPTIMIZER.md
[Nonattainment]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_NONATTAINMENT.md

## 追加锚（本行以下为增补区）
