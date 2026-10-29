# CDSO incidence moments and capacity phases

## 1. Joint arrays and graph costs

**Definition 1.1 (One joint incidence array).** For a positive integer $s$, let $[s]=\{1,\ldots,s\}$. A profile is one array

$$
x=(x_T)_{\varnothing\ne T\subseteq[s]},\qquad
x_T\ge0,\qquad \sum_Tx_T=1.
$$

All expectations below refer to the random nonempty subset $T$ with this law. Put

$$
K=|T|,\qquad q=\mathbb E K,\qquad
y_i=\mathbb P(i\in T)>0,\qquad
w_i=\mathbb E[K^2\mathbf1_{\{i\in T\}}],
$$

$$
U_T=\sum_{i\in T}y_i^{-1},\qquad
2J_s(x)=\sum_{i=1}^s\frac{w_i}{y_i^2}
=\mathbb E\left[K^2\sum_{i\in T}y_i^{-2}\right].
$$

Thus $0<y_i\le1$, $\sum_i y_i=q$, $1\le q\le s$ and $U_T\ge K$. No independent choice of the marginals is permitted: the same $x$ determines $K,U,y,w$ and $J_s$.

**Definition 1.2 (Adjacent-cardinality candidate).** Fix an integer $r\ge5$ and write

$$
a=r-1,\qquad D=3a^2+3a+1=3r^2-3r+1,\qquad
C=a(a+1)(2a+1)=r(r-1)(2r-1),
$$

$$
f_r(q)=Dq-C,\qquad F_r(q)=\frac{r^2f_r(q)}{2q^2},\qquad
\kappa_r=2+\sqrt{8a(a^2-1)}.
$$

For $q\in[a,r]$, put $\theta=q-a$ and define a profile on $[r]$ by

$$
x^*_{[r]}(q)=\theta,\qquad
x^*_{[r]\setminus\{i\}}(q)=\frac{r-q}{r}\quad(1\le i\le r),
\qquad x^*_T(q)=0\text{ otherwise}.
$$

Its marginals are $q/r$, its mean cardinality is $q$, and

$$
\mathbb E_{x^*}K^3=(1-\theta)a^3+\theta r^3=f_r(q),
\qquad J_r(x^*(q))=F_r(q).
$$

Both endpoints are included: the full type has mass zero at $q=a$, and all missing-one types have mass zero at $q=r$.

**Definition 1.3 (Actual graphs and excess).** Graphs are finite, simple and connected. For integers $n\ge2$ and $\ell\ge0$, let $\mathcal G(n,\ell)$ consist of the graphs of order $n$ and size $m=n-1+\ell$. Set

$$
\Phi(G)=\sum_{uv\in E(G)}\frac{\sqrt{d_u^2+d_v^2}}{\max(d_u,d_v)},
\qquad g(t)=\sqrt{1+t^2}-1,
$$

$$
E(G)=\Phi(G)-m
=\sum_{uv\in E(G)}g\!\left(\frac{\min(d_u,d_v)}{\max(d_u,d_v)}\right).
$$

Each unordered edge is counted once. This is the complementary diminished Sombor index with the normalization of A. M. Albalahi, S. Das, A. Ali, J. Barman and A. E. Hamza, *On the hyperbolic Sombor index and its counterpart*, Discrete Math. Lett. 16 (2025), 108–115, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176), §1, p.109. Their Conjecture 4.1 is a historical motivation, not an open premise here: its CDSO universal-vertex assertion is refuted by the unicyclic comparison in A. Ali, K. C. Das and A. A. Attiya, *Bond incident degree indices of fixed-order unicyclic graphs*, DOI [10.47443/dml.2025.192](https://doi.org/10.47443/dml.2025.192), Remark 2.3, and for every positive cyclomatic number by A. M. Albalahi, *On Two Conjectures Concerning the Hyperbolic Sombor Index and Its Counterpart*, DOI [10.47443/dml.2026.217](https://doi.org/10.47443/dml.2026.217), Proposition 2.1. The latter paper's Theorem 2.2 concerns maxima.

When adjacent degrees differ, orient each edge toward its endpoint of larger degree. A sink has no outgoing edge, a source has no incoming edge, and a two-layer graph has every edge joining a source to a sink. We use these notions and the fixed-cost reduction of [*CDSO sink incidences and density limits*, Definitions 1.1–1.2 and Theorem 3.1](CDSO_SINK_INCIDENCE_AND_DENSITY_LIMITS.md). In a two-layer graph, label the actual sinks by $[s]$, put $N_s=n-s$, and let $a_T$ count sources with neighborhood exactly $T$. Its actual profile is $x_T=a_T/N_s$. Then

$$
\sum_Ta_T=N_s,\qquad \sum_T|T|a_T=m,\qquad
\sum_T(|T|-1)a_T=\ell+s-1,
$$

$$
D_i=\sum_{T\ni i}a_T=N_sy_i,\qquad q_s=\frac m{N_s}.
$$

These identities use the vertices and degrees of one graph.

## 2. An incidence certificate for arbitrary finite hub number

**Theorem 2.1 (Integer support with incidence remainders).** For every integer $r\ge5$, every finite $s\ge1$, every profile of Definition 1.1, and every $2\le\beta\le\kappa_r$, one has

$$
2J_s(x)=f_r(q)+\beta(s-q)+R_{\mathrm{inc}}+R_{\mathrm{sc}}
\ge f_r(q)+\beta(s-q),
$$

where

$$
R_{\mathrm{inc}}
=\mathbb E\left[K\sum_{\substack{i<j\\i,j\in T}}
 (y_i^{-1}-y_j^{-1})^2\right]\ge0,
$$

$$
R_{\mathrm{sc}}
=\mathbb E\left[KU_T^2-(D-\beta)K-\beta U_T+C\right]\ge0.
$$

There is no restriction $q\in[r-1,r]$ in this theorem.

**Proof.** The incidence identity

$$
\mathbb E U_T=\sum_{i=1}^s\frac{\mathbb P(i\in T)}{y_i}=s
$$

uses precisely the marginals of $x$. For a fixed nonempty $T$ of cardinality $k$, the elementary identity

$$
k\sum_{i\in T}z_i^2-\left(\sum_{i\in T}z_i\right)^2
=\sum_{\substack{i<j\\i,j\in T}}(z_i-z_j)^2
$$

with $z_i=y_i^{-1}$ gives

$$
K^2\sum_{i\in T}y_i^{-2}=KU_T^2+
K\sum_{\substack{i<j\\i,j\in T}}(y_i^{-1}-y_j^{-1})^2.
$$

It remains to prove the pointwise support inequality

$$
ku^2\ge(D-\beta)k+\beta u-C
\quad\text{for every integer }k\ge1\text{ and every real }u\ge k.\tag{2.1}
$$

First, $\kappa_r\le2a^2$. Indeed $2a\le a^2-1$ for $a\ge4$, so

$$
\sqrt{2a(a^2-1)}\le a^2-1,
\qquad 2+\sqrt{8a(a^2-1)}\le2a^2.
$$

Consequently $D-\beta\ge a^2+3a+1>0$. Let $h=\sqrt{\beta/2}$; then $1\le h\le a$.

If the integer $k\ge h$, the derivative with respect to $u$ of the difference in (2.1) is $2ku-\beta\ge2k^2-\beta\ge0$. Its minimum on $u\ge k$ occurs at $u=k$ and equals

$$
k^3-Dk+C=(k-a)(k-a-1)(k+2a+1)\ge0.
$$

For an integer $k$, the first two factors are both nonpositive when $k\le a$, and both nonnegative when $k\ge a+1$; there is no integer strictly between $a$ and $a+1$.

If instead $1\le k\le h$, the unconstrained minimizer $u=\beta/(2k)$ is feasible. Its value, multiplied by $4k>0$, is

$$
Q(k)=4Ck-4(D-\beta)k^2-\beta^2.
$$

This is a concave quadratic on the real interval $[1,h]$. Its endpoint values satisfy

$$
Q(1)=8a(a^2-1)-(\beta-2)^2\ge0,
$$

$$
Q(h)=4h\bigl(h^3-Dh+C\bigr)
=4h(h-a)(h-a-1)(h+2a+1)\ge0.
$$

The latter sign follows from $h\le a$. Concavity bounds $Q$ below by its endpoint chord, hence $Q(k)\ge0$ throughout $[1,h]$. If $h=1$ the interval is a singleton and the same endpoint computation applies. These two cases exhaust all positive integers $k$, including their common boundary. This proves (2.1).

Apply (2.1) to each actual pair $(K,U_T)$, integrate, and use $\mathbb E K=q$, $\mathbb E U_T=s$. Combining with the incidence identity gives the stated exact decomposition. Types of mass zero contribute zero, with no division by $x_T$. ∎

**Theorem 2.2 (Shared-budget certificate on the nine-hub interval).** Let $s$ be finite and let $x$ be one profile of Definition 1.1. For each positive integer $k$ put

$$
m_k=\mathbb E\min(k,K).
$$

For every nonempty fixed $T\subseteq[s]$, writing $k=|T|$ and $b_T=\sum_{i\in T}y_i$, one has

$$
0<b_T\le m_k\le\min(k,q),\qquad
U_T\ge\frac{k^2}{b_T}\ge\frac{k^2}{m_k}
\ge\max\{k,k^2/q\}.\tag{2.2}
$$

In particular the following necessary overlap bound holds for this actual array:

$$
2J_s(x)\ge\mathbb E\frac{K^5}{m_K^2}.\tag{2.3}
$$

If $8\le q\le9$, then

$$
2J_s(x)\ge105q+84s-1000,\tag{2.4}
$$

with equality if and only if $s=8$, $q=8$ and $x_{[8]}=1$.

**Proof.** Take an independent copy $T'$ drawn from this same array. For a fixed $T$,

$$
b_T=\sum_{i\in T}\mathbb P(i\in T')=\mathbb E|T\cap T'|
\le\mathbb E\min(k,|T'|)=m_k\le\min(k,q).
$$

The inequalities $b_T>0$ and $m_k>0$ follow from the positive marginals and nonempty types. Cauchy–Schwarz applied within this one $T$ gives

$$
k^2=\left(\sum_{i\in T}\sqrt{y_i}\,y_i^{-1/2}\right)^2
\le b_TU_T.
$$

This proves (2.2). A second application gives

$$
U_T^2\le k\sum_{i\in T}y_i^{-2},\qquad
k^2\sum_{i\in T}y_i^{-2}\ge kU_T^2\ge\frac{k^5}{m_k^2}.
$$

Taking expectation proves (2.3) and also

$$
2J_s(x)\ge\mathbb E(KU_T^2).
$$

The bound $U_T\ge k^2/q$ retains the shared marginal budget $\sum_i y_i=q$ for every realized type; the two moment identities alone do not impose it. All copies, marginals and expectations above come from $x$.

To prove (2.4), the needed integer-support certificate is

$$
G_q(k,u):=ku^2-230k-84u+125q+1000\ge0
\quad\left(\begin{array}{l}8\le q\le9,\ k\in\mathbb Z_{\ge1},\\
u\ge\max\{k,k^2/q\}\end{array}\right).\tag{2.5}
$$

Its equality class is exactly $q=8$, $k=8$, $u=8$. Here is a proof covering every positive integer $k$. Write $t=q-8\in[0,1]$.

For $1\le k\le6$, complete the square:

$$
G_q(k,u)=k(u-42/k)^2+2000-230k-1764/k+125t.
$$

The constants after the square, before $125t$, for $k=1,\ldots,6$ are respectively

$$
6,\quad658,\quad722,\quad639,\quad2486/5,\quad326.
$$

They are all strictly positive, even without a restriction on $u$.

For $k=7,8$, use $u\ge k$ and

$$
G_q(k,u)-G_q(k,k)=(u-k)\bigl[k(u+k)-84\bigr]\ge0.
$$

The bracket is positive because $2k^2-84>0$. The two endpoint values are

$$
G_q(7,7)=145+125t,\qquad G_q(8,8)=125t.
$$

Thus equality in these two cases requires exactly $t=0$, $k=8$, $u=8$.

For $k=9$, put $v=81/q\ge9$. Since $u\ge v$,

$$
G_q(9,u)-G_q(9,v)=(u-v)\bigl[9(u+v)-84\bigr]\ge0.
$$

The bracket is positive. Direct expansion gives

$$
\begin{aligned}
q^2G_q(9,v)
&=125q^3-1070q^2-6804q+59049\\
&=137+76t+1930t^2+125t^3>0.
\end{aligned}\tag{2.6}
$$

For every integer $k\ge10$, set $v=k^2/q$. Again $u\ge v$ and

$$
G_q(k,u)-G_q(k,v)=(u-v)\bigl[k(u+v)-84\bigr]\ge0,
$$

since the bracket is at least $2k^3/q-84\ge2000/9-84>0$. Put $z=1/q\ge1/9$. Then

$$
\begin{aligned}
&k^5z^2-84k^2z-\bigl[k^5/81-(28/3)k^2\bigr]\\
&\hspace{1em}=(z-1/9)k^2\bigl[k^3(z+1/9)-84\bigr]\ge0,
\end{aligned}
$$

because the last bracket is at least $2000/9-84>0$. Also $125q+1000\ge2000$. Therefore

$$
G_q(k,u)\ge\frac{k^5-756k^2-18630k+162000}{81}.
$$

Writing $v_0=k-10\ge0$, the numerator equals

$$
100+16250v_0+9244v_0^2+1000v_0^3+50v_0^4+v_0^5>0.\tag{2.7}
$$

This proves (2.5) and its full equality classification, without an upper bound on $k$.

Apply (2.5) to the actual pairs $(K,U_T)$ using (2.2). Since $\mathbb E K=q$ and $\mathbb E U_T=s$,

$$
2J_s(x)\ge\mathbb E(KU_T^2)
\ge230q+84s-125q-1000=105q+84s-1000.
$$

If the final bound is an equality, the two nonnegative gaps in this chain have expectation zero. In particular $G_q(K,U_T)=0$ for every positive-mass type. The equality classification forces $q=8$ and $K=U_T=8$ on every such type. Since every $y_i\le1$, the eight summands $y_i^{-1}$ in any such type must all equal one. These eight marginals use the entire budget $\sum_i y_i=8$. The strict positivity of every marginal excludes any further hub. Thus $s=8$ and the only possible type is $[8]$. Conversely the profile $x_{[8]}=1$ gives $2J_8=512=105\cdot8+84\cdot8-1000$.

In particular (2.4) is strict for every $s\ge10$. The coefficient $84$ belongs to the new constrained certificate (2.5), whose domain includes $u\ge k^2/q$. It is not a choice of $\beta$ in (2.1), which has the different domain $u\ge k$ and requires $\beta\le\kappa_r$. No sufficiency of (2.2)–(2.3) for joint realizability is asserted. Zero type masses and positive marginals with no uniform lower bound are allowed throughout. Indeed $K\ge1$ implies $w_i\ge y_i$, hence

$$
2J_s(x)\ge\sum_i y_i^{-1}.
$$

For fixed finite $s$, an individual marginal tending to zero therefore forces the energy to infinity. Neither a limiting zero type mass nor a rare type alters the pointwise inequalities used above. ∎

**Theorem 2.3 (Strict nine-hub comparison and quantitative compensation).** Let $s\ge10$ be finite and $8\le q\le9$. For every actual profile of mean $q$, with $t=q-8\in[0,1]$,

$$
\begin{aligned}
2J_s(x)-2F_9(q)
&>\frac{2048+23t+2360t^2+105t^3}{q^2}+84(s-10)\\
&\ge\frac{2048}{81}+84(s-10)>0.
\end{aligned}\tag{2.8}
$$

At $q=8$ this gives $2J_s(x)>680+84(s-10)$. In particular no actual profile on $[10]$ has $2J_{10}=648$ at that mean. For $s=10$, $q=8$, and the remainders of Theorem 2.1 with $r=9$, $\beta=\kappa_9=2+8\sqrt{63}$,

$$
R_{\mathrm{inc}}+R_{\mathrm{sc}}
>164-16\sqrt{63}=32+(132-16\sqrt{63}).\tag{2.9}
$$

**Proof.** Here $2F_9(q)=81(217q-1224)/q^2$. The strict case of (2.4) gives

$$
2J_s(x)>105q-160+84(s-10).
$$

The exact difference is

$$
\begin{aligned}
q^2\bigl[105q-160-2F_9(q)\bigr]
&=105q^3-160q^2-17577q+99144\\
&=2048+23t+2360t^2+105t^3.
\end{aligned}
$$

All coefficients are positive and $q^2\le81$, proving (2.8) at both endpoints and throughout the interval. At $q=8$, (2.4) gives the claimed $680+84(s-10)$ bound directly. For the remainder assertion, the incidence identity in Theorem 2.1 gives exactly

$$
\begin{aligned}
R_{\mathrm{inc}}+R_{\mathrm{sc}}
&=2J_{10}-\bigl[(217-\kappa_9)8+10\kappa_9-1224\bigr]\\
&=2J_{10}-516-16\sqrt{63}.
\end{aligned}
$$

Subtract this constant from $2J_{10}>680$ to obtain (2.9). These bounds do not identify the true minimum at $q=8$, $s=10$, or an attaining array; in particular $680$ is not asserted to be optimal. ∎

## 3. Fixed hub count, strict equality and stability

**Theorem 3.1 (The fixed-$r$ remainder as a stability estimate).** For every integer $r\ge5$, every profile on $[r]$ with $q\in[r-1,r]$ satisfies $J_r(x)\ge F_r(q)$. Write

$$
\Delta=J_r(x)-F_r(q),\qquad
p_{\mathrm{low}}=\sum_{|T|\le r-2}x_T.
$$

Then

$$
\Delta\ge3(r-1)p_{\mathrm{low}}
+\frac{(r-1)^2}{2}\sum_{i=1}^r\left(y_i-\frac qr\right)^2,\tag{3.1}
$$

$$
\|x-x^*(q)\|_1
\le\frac{\sqrt{2r}}{r-1}\sqrt\Delta+\frac23\Delta.\tag{3.2}
$$

Equality $J_r(x)=F_r(q)$ holds exactly for $x=x^*(q)$, including $q=r-1$ and $q=r$.

**Proof.** The following type identity is the intermediate structure needed for the estimates, rather than an assumption of equal marginals. For $\theta=q-a$ define

$$
R_i=w_i-a^2y_i-(2r-1)\theta.
$$

Expansion separately over types containing and avoiding $i$ gives

$$
R_i=\sum_{T\not\ni i}(2r-1)(r-|T|-1)x_T
+\sum_{T\ni i}(r-|T|)(r-|T|-1)x_T.\tag{3.3}
$$

All occurring coefficients are nonnegative: a type avoiding $i$ has $|T|\le r-1$, and the other product vanishes at $|T|=r-1,r$. For a type of cardinality $k\le r-2$, its coefficient in $\sum_iR_i$ is

$$
(r-k)(r-k-1)(2r-1+k)\ge6(r-1).
$$

To verify the last inequality for all such integers, set $z=r-k\in\{2,\ldots,r-1\}$. The expression is $z(z-1)(3r-z-1)$; its increment from $z$ to $z+1$ is $3z(2r-z-1)>0$, and its value at $z=2$ is $6(r-1)$. Since $y_i\le1$,

$$
J_r(x)=\sum_{i=1}^rh_\theta(y_i)+\frac12\sum_i\frac{R_i}{y_i^2}
\ge\sum_i h_\theta(y_i)+3a p_{\mathrm{low}},
$$

$$
h_\theta(y)=\frac{a^2}{2y}+\frac{(2r-1)\theta}{2y^2},\qquad
h_\theta''(y)=\frac{a^2}{y^3}+\frac{3(2r-1)\theta}{y^4}\ge a^2
\quad(0<y\le1).
$$

The ordinary strong-convexity inequality, summed at $y=q/r$ using $\sum_i(y_i-q/r)=0$, yields

$$
\sum_i h_\theta(y_i)\ge r h_\theta(q/r)
+\frac{a^2}{2}\sum_i(y_i-q/r)^2.
$$

The first term is $F_r(q)$, as is also seen by substituting $x^*$. This proves (3.1). The convexity inequality and Cauchy–Schwarz used here are standard; their consumers are the quantitative remainder and the cross-hub and finite-graph conclusions below.

For the distributional estimate, put

$$
p=p_{\mathrm{low}},\qquad
\varepsilon=\sum_{|T|\le a-1}(a-|T|)x_T,\qquad
l_i=\sum_{\substack{|T|\le a-1\\i\notin T}}x_T.
$$

The mean identity implies $x_{[r]}=\theta+\varepsilon$, and the marginal identity implies

$$
x_{[r]\setminus\{i\}}-\frac{r-q}{r}
=-(y_i-q/r)-l_i.
$$

Here $0\le\varepsilon\le(a-1)p$ and $\sum_i l_i=\varepsilon+p$. Thus

$$
\begin{aligned}
\|x-x^*(q)\|_1
&\le\sum_i|y_i-q/r|+2\varepsilon+2p\\
&\le\sqrt r\left(\sum_i(y_i-q/r)^2\right)^{1/2}+2ap.
\end{aligned}\tag{3.4}
$$

Combining (3.4) with (3.1) gives (3.2). Finally $\Delta=0$ forces $p=0$ and every $y_i=q/r$. The displayed identities then give exactly $x^*(q)$. Conversely that candidate attains $F_r(q)$ by Definition 1.2. The proof did not require either $\theta$ or $1-\theta$ to be positive. ∎

**Theorem 3.2 (Unrestricted profiles for $r=5,6,7,8,9$).** Let $r\in\{5,6,7,8,9\}$, $q\in[r-1,r]$, and let $x$ be any profile on any finite $[s]$ with $s\ge r$. Then

$$
J_s(x)\ge F_r(q),
$$

with equality exactly when $s=r$ and $x=x^*(q)$, up to relabeling. For $s\ge r+1$ the stronger bound is

$$
J_s(x)-F_r(q)\ge\frac12+\frac{\beta_r}{2}(s-r-1),\qquad
(\beta_5,\beta_6,\beta_7,\beta_8,\beta_9)=(23,32,42,53,\kappa_9).\tag{3.5}
$$

For these same five values of $r$, every profile with $s\ge r+1$ and $q\ge r$ satisfies

$$
2J_s(x)\ge r^3+\beta_r(s-r)+(D-\beta_r)(q-r)
\ge r^3+\beta_r.\tag{3.6}
$$

**Proof.** For $r=5,6,7,8$, the four choices of $\beta$ lie in $[2,\kappa_r]$: the comparisons $(\beta-2)^2\le8a(a^2-1)$ are respectively

$$
441\le480,\quad900\le960,\quad1600\le1680,\quad2601\le2688.
$$

For these four values, put $t=q-a\in[0,1]$ and $L_r(q)=f_r(q)+\beta_r(r+1-q)$. The following are exact polynomial identities:

$$
\begin{array}{c|l}
r&q^2\bigl[L_r(q)-2F_r(q)-1\bigr]\\ \hline
5&144-45t+413t^2+38t^3\\
6&200+79t+778t^2+59t^3\\
7&180+425t+1319t^2+85t^3\\
8&1140t+2072t^2+116t^3.
\end{array}\tag{3.7}
$$

The first polynomial is at least $144-45=99$; the remaining three have nonnegative coefficients. Therefore $L_r(q)\ge2F_r(q)+1$ on the entire closed interval. Theorem 2.1 now gives

$$
2J_s(x)\ge L_r(q)+\beta_r(s-r-1),
$$

proving (3.5) for $r=5,6,7,8$. For $r=9$, Theorem 2.3 gives the stronger strict bound (2.8). Since

$$
\kappa_9=2+8\sqrt{63}<66<84,\qquad 2048/81>1,
$$

that bound implies (3.5) with $\beta_9=\kappa_9$ for every finite $s\ge10$ and $q\in[8,9]$. It uses no restriction on source cardinalities or positive type masses. For $s=r$, Theorem 3.1 gives the inequality and the complete equality class. Thus no assumption on the cardinalities in the support is needed.

For (3.6), use Theorem 2.1 outside the candidate interval as allowed there. Since $f_r(r)=r^3$,

$$
f_r(q)+\beta_r(s-q)
=r^3+\beta_r(s-r)+(D-\beta_r)(q-r).
$$

Both $D-\beta_r>0$ and $q-r\ge0$, proving (3.6). This gives a fixed positive separation even if an actual extra-hub graph has mean cardinality above $r$. ∎

## 4. All parameters under a cardinality hypothesis

**Theorem 4.1 (All-$r$ conditional comparison and Bernstein certificate).** Let $r\ge5$, let $s\ge r$ be finite, and let $x$ be a profile supported on $K\ge r-2$. If $q\in[r-1,r]$, then $J_s(x)\ge F_r(q)$, with equality exactly when $s=r$ and $x=x^*(q)$, up to relabeling. Set

$$
d=r-2,\qquad
\gamma_r=\frac{6r^4-39r^3+52r^2-8r-8}{6r^2}\ge\frac{127}{150}.
$$

For every $s\ge r+1$ one has

$$
J_s(x)-F_r(q)\ge\gamma_r+
\frac{(r-2)^2}{2q}\bigl[s^2-(r+1)^2\bigr].\tag{4.1}
$$

For the same support condition, every $s\ge r+1$ and every feasible $q\ge r$ satisfy

$$
J_s(x)\ge\frac{r^3}{2}+\gamma_r.\tag{4.2}
$$

**Proof.** For every integer $k$,

$$
k^2\ge d^2+(2d+1)(k-d),
\qquad k^2-d^2-(2d+1)(k-d)=(k-d)(k-d-1)\ge0.
$$

For types in the support $K-d\ge0$. Consequently

$$
\begin{aligned}
2J_s(x)
&\ge d^2\mathbb E\sum_{i\in T}y_i^{-2}
 +(2d+1)\mathbb E\left[(K-d)\sum_{i\in T}y_i^{-2}\right]\\
&\ge d^2\sum_i y_i^{-1}+(2d+1)\mathbb E[K(K-d)]\\
&\ge\frac{d^2s^2}{q}+(2d+1)\bigl(\mathbb E K^2-dq\bigr).
\end{aligned}\tag{4.3}
$$

The second step uses $y_i^{-2}\ge1$ only with nonnegative coefficients, and the third uses $(\sum_i y_i)(\sum_i y_i^{-1})\ge s^2$.

For integer $K$, $(K-r+1)(K-r)\ge0$, so

$$
\mathbb E K^2\ge(2r-1)q-r(r-1).
$$

On $[r-1,r]$, (4.3) therefore gives

$$
2J_s(x)\ge B_{r,s}(q):=
\frac{(r-2)^2s^2}{q}+(2r-3)\bigl[(r+1)q-r(r-1)\bigr].\tag{4.4}
$$

Here is a coefficient proof valid for every $r\ge5$, including the whole $q$ interval. Put $u=r-5\ge0$, $t=q-r+1\in[0,1]$ and

$$
P_r(q)=q^2\bigl[B_{r,r+1}(q)-2F_r(q)\bigr].
$$

After expansion it has the cubic Bernstein representation

$$
P_r(r-1+t)=\sum_{j=0}^3b_j\binom3j t^j(1-t)^{3-j},
$$

where

$$
\begin{aligned}
b_0&=2u^4+27u^3+128u^2+244u+144,\\
b_1&=2u^4+27u^3+\tfrac{367}{3}u^2+\tfrac{587}{3}u+\tfrac{127}{3},\\
b_2&=2u^4+\tfrac{85}{3}u^3+\tfrac{406}{3}u^2+231u+62,\\
b_3&=2u^4+31u^3+169u^2+369u+245.
\end{aligned}\tag{4.5}
$$

In particular $b_1>0$. The exact differences are

$$
\begin{aligned}
b_0-b_1&=\tfrac13(17u^2+145u+305),\\
b_2-b_1&=\tfrac13(4u^3+39u^2+106u+59),\\
b_3-b_1&=\tfrac13(12u^3+140u^2+520u+608).
\end{aligned}
$$

All are nonnegative. The Bernstein weights are nonnegative and sum to one, so $P_r(q)\ge b_1$. Since $q\le r$,

$$
B_{r,r+1}(q)-2F_r(q)\ge\frac{b_1}{r^2}=2\gamma_r.
$$

Replacing $r+1$ by $s$ in (4.4) adds exactly $d^2[s^2-(r+1)^2]/q$, proving (4.1). Also

$$
\gamma_r=r^2-\frac{13r}{2}+\frac{26}{3}-\frac4{3r}-\frac4{3r^2}.
$$

Its derivative as a real function on $[5,\infty)$ is $2r-13/2+4/(3r^2)+8/(3r^3)>0$, and $\gamma_5=127/150$.

For $q\ge r$, use $\mathbb E K^2\ge q^2$ in (4.3) instead. The lower bound obtained by replacing $s$ with $r+1$ is

$$
G_r(q)=\frac{d^2(r+1)^2}{q}+(2r-3)(q^2-dq).
$$

It is strictly increasing for $q\ge r$: its second derivative is positive and

$$
G_r'(r)=\frac{r^4+3r^3-3r^2-4r-4}{r^2}>0.
$$

For example $r^4-3r^2-4r-4>0$ for $r\ge5$, since it is at least $22r^2-4r-4>0$. At $q=r$ one has $G_r(r)=B_{r,r+1}(r)\ge r^3+2\gamma_r$. This proves (4.2). Finally Theorem 3.1 handles $s=r$, while the positive gap excludes $s>r$, proving the equality statement. ∎

**Theorem 4.2 (Weighted low-cardinality defect without the hypothesis).** For any profile, define

$$
\Delta_d(x)=\sum_{1\le|T|<d}x_T(d-|T|)
\sum_{i\in T}(y_i^{-2}-1),\qquad d=r-2.
$$

For $q\in[r-1,r]$ and $s\ge r+1$, without any restriction on the support,

$$
J_s(x)-F_r(q)\ge\gamma_r+
\frac{d^2[s^2-(r+1)^2]}{2q}-\frac{2r-3}{2}\Delta_d(x).\tag{4.6}
$$

Thus $J_s(x)\le F_r(q)$ requires

$$
\Delta_d(x)\ge
\frac{2\gamma_r+d^2[s^2-(r+1)^2]/q}{2r-3};\tag{4.7}
$$

a strict counterexample requires a strict inequality in (4.7).

**Proof.** Retain the integer quadratic inequality at the start of (4.3), but now keep track of its signed coefficient:

$$
\begin{aligned}
\mathbb E\left[(K-d)\sum_{i\in T}y_i^{-2}\right]
&=\mathbb E[K(K-d)]\\
&\quad+\sum_Tx_T(K-d)\sum_{i\in T}(y_i^{-2}-1)\\
&\ge\mathbb E[K(K-d)]-\Delta_d(x).
\end{aligned}
$$

The terms with $K\ge d$ are nonnegative, while the others are exactly the negative of the displayed defect. Hence $2J_s\ge B_{r,s}(q)-(2r-3)\Delta_d(x)$. Apply (4.5). The remaining implications follow by rearranging. All the favorable terms and all the defect terms belong to the same array. This is a necessary condition on a possible counterexample, not such a counterexample. ∎

## 5. Capacity, integer candidates and their exact cost

**Definition 5.1 (Full capacity interval and balanced construction).** For $r\ge5$, define

$$
L_r(n)=(r-2)n-r^2+2r+1,\qquad
U_r(n)=(r-1)n-r^2+1.
$$

For integers $n\ge2r$ and $L_r(n)\le\ell\le U_r(n)$ put

$$
N=n-r,\qquad c=\ell-(r-2)n+r(r-1)-1,\qquad
b=U_r(n)-\ell.
$$

Choose nonnegative integers $b_1,\ldots,b_r$ summing to $b$ and differing pairwise by at most one. The graph $H_r(n,\ell)$ has $r$ independent hubs, $c$ distinct sources adjacent to all hubs, and $b_i$ distinct sources adjacent to all hubs except hub $i$. All sources are independent. Put

$$
M_c(z)=z g((r-1)/z)+c\bigl[g(r/z)-g((r-1)/z)\bigr]\quad(z>0).
$$

**Theorem 5.2 (Capacity exclusion and quantitative rounding).** For $n\ge2r$, the complete integer interval in which $r$ independent hubs can accommodate the edge budget and every smaller hub number is excluded by that capacity is precisely $[L_r(n),U_r(n)]$. On this interval,

$$
b+c=N,\qquad (r-1)b+rc=m=n-1+\ell,\qquad c\ge r,\quad b\ge0.
$$

The graph $H_r(n,\ell)$ is simple and connected with exactly the prescribed $n,m,\ell$. Its hub degrees are $D_i=N-b_i$. For $n\ge3r$, these are larger than the source degrees, so they are its degree-oriented sinks. Its exact excess is

$$
E(H_r(n,\ell))=\sum_{i=1}^rM_c(N-b_i).\tag{5.1}
$$

Set

$$
q_r=\frac mN=r-1+\frac cN,\qquad
B=r\bigl[4(r-1)^2+24(2r-1)\bigr],\qquad C_0=4r^3.
$$

The actual normalized profile $x^H$ satisfies

$$
0\le J_r(x^H)-F_r(q_r)\le\frac B{N^2},\tag{5.2}
$$

and

$$
E(H_r(n,\ell))\le\frac{F_r(q_r)}N+\frac B{N^3},\qquad
E(H_r(n,\ell))\le\frac{C_0}{n}.\tag{5.3}
$$

**Proof.** With $t$ independent hubs and $n-t$ sources, simplicity gives $m\le t(n-t)$. For integers $t\le r-1$ and $n\ge2r$, this capacity increases with $t$. Thus the condition excluding all $t\le r-1$ is

$$
m>(r-1)(n-r+1),
$$

which, for integer $\ell$, is exactly $\ell\ge L_r(n)$. Feasibility of $r$ hubs is $m\le r(n-r)$, or $\ell\le U_r(n)$. Conversely all integer edge counts in this interval are supplied by the construction. Solving its two count equations gives the displayed $b,c$. At the lower endpoint $c=r$ and at the upper endpoint $b=0$; hence $r\le c\le N$ throughout. The full sources connect every hub, and every other source has a nonempty neighborhood. All memberships are simple edges between distinct vertices. Thus connectedness, simplicity, order and size hold together in this one graph, even if a missing-one count is zero.

At hub $i$, precisely $c$ incident sources have degree $r$ and $b-b_i=D_i-c$ have degree $r-1$. Every $D_i\ge c\ge r$, so the hub is a larger-degree endpoint and (5.1) holds even when the endpoint degrees are equal. For a balanced choice, $b_i\le b/r+1$ and $b\le N-r$, so $D_i\ge(r-1)N/r$. If $n\ge3r$, this is greater than $r$. This also proves the claimed orientation.

For the quantitative estimate, write $\theta=c/N$ and $y_i=1-b_i/N$. Balance gives

$$
|y_i-q_r/r|<1/N,\qquad \sum_i(y_i-q_r/r)=0,
\qquad y_i\ge\tfrac12.
$$

Only cardinalities $r-1,r$ occur. Hence (3.3) is an equality with $R_i=0$ and $J_r(x^H)=\sum_i h_\theta(y_i)$. On the segment between $y_i$ and $q_r/r$, both arguments are at least $1/2$, and

$$
h_\theta''(y)\le8(r-1)^2+48(2r-1).
$$

Taylor's formula, summed with the zero linear term, proves the upper bound in (5.2); its lower bound is Theorem 3.1. On every actual edge $g(t)\le t^2/2$, so $E(H_r)\le J_r(x^H)/N$, proving the first part of (5.3). Finally $D_i\ge N/2$, there are $m\le rN$ edges, and each source degree is at most $r$. Therefore

$$
E(H_r)\le\frac{mr^2}{2(N/2)^2}\le\frac{2r^3}{N}\le\frac{4r^3}{n}.
$$

Here $N\ge n/2$. All the cost estimates hold for $n\ge2r$; the stronger $n\ge3r$ condition was needed only for strict degree orientation. ∎

## 6. Exact finite minimizers throughout the capacity interval

**Theorem 6.1 (Uniform sufficient threshold and unique finite minimum).** Fix $r\ge5$. Let the admissible class $\mathcal A_r(n,\ell)$ be either of the following:

1. for $r\in\{5,6,7,8,9\}$, all of $\mathcal G(n,\ell)$;
2. for any $r\ge5$, the members of $\mathcal G(n,\ell)$ whose minimum degree is at least $r-2$.

Define

$$
C_0=4r^3,\quad A=2C_0+1,\quad K_0=\lceil\sqrt A\rceil,
\quad R=\frac{(3C_0)^4K_0^5}{8},
$$

$$
B=r\bigl[4(r-1)^2+24(2r-1)\bigr],\qquad
H=R+8B,\qquad
\widehat\gamma=\min\{1/2,\gamma_r\}=1/2.
$$

Take any integer $n_0(r)$ strictly greater than

$$
\max\left\{
1,2r,C_0^2,3C_0,A^3,4AK_0^2,36C_0^2A,
\sqrt{H/\widehat\gamma},\frac{H}{3(r-1)}
\right\}.\tag{6.1}
$$

For every integer $n\ge n_0(r)$ and every integer

$$
L_r(n)\le\ell\le U_r(n),
$$

$H_r(n,\ell)$ is the unique minimizing isomorphism class in $\mathcal A_r(n,\ell)$. In particular the exact minimum excess is

$$
E_r^{\min}(n,\ell):=\min_{G\in\mathcal A_r(n,\ell)}E(G)
=\sum_{i=1}^rM_c(N-b_i),\tag{6.2}
$$

with $N,c,b_i$ as in Definition 5.1; the minimum of $\Phi$ is $m$ plus (6.2). The threshold is sufficient; it is not asserted to be least. For $r\ge10$, the second class here is a material minimum-degree restriction; for $r=9$ the unrestricted conclusion holds throughout the interval $[L_9(n),U_9(n)]=[7n-62,8n-80]$.

**Proof.** The candidate belongs to either stated class, has source degrees $r-1,r$, and its hub degrees exceed $r$ at this threshold. It has $E(H_r)\le C_0/n$ by Theorem 5.2. A graph with larger excess is already strictly worse than the candidate. It suffices to consider actual graphs $G$ with $E(G)\le C_0/n$.

Apply [*CDSO sink incidences and density limits*, Theorem 3.1](CDSO_SINK_INCIDENCE_AND_DENSITY_LIMITS.md) with exactly $C=C_0$, $A=2C_0+1$, $K=K_0$. The six reduction inequalities there are included in (6.1). Thus $G$ is two-layer, its actual sink number obeys $s\le K_0$, and each sink degree satisfies

$$
D_i\ge\frac n{3C_0}.
$$

This uses the existing reduction, rather than asserting an additional reduction theorem. Capacity from Theorem 5.2 forces $s\ge r$. In the second admissible class, each source also satisfies $K\ge r-2$. Let $N_s=n-s$ and use the actual array of Definition 1.3. In particular $q_s=m/N_s\ge q_r=m/(n-r)>r-1$, but $q_s$ need not be at most $r$.

The uniform error on these actual edges follows from the elementary identity, also used in [*CDSO minimizers without a universal vertex for every cyclomatic number*, §11](CDSO_UNIVERSAL_VERTEX_ALL_CYCLOMATIC.md),

$$
0\le\frac{t^2}{2}-g(t)
=\frac{t^4}{2(\sqrt{1+t^2}+1)^2}\le\frac{t^4}{8}\quad(t\ge0).
$$

The quadratic edge sum is exactly $J_s(x)/N_s$. Counting at most $s$ incidences at each source, each source degree at most $s$, gives

$$
\begin{aligned}
0\le\frac{J_s(x)}{N_s}-E(G)
&\le\frac18\sum_Ta_T|T|^4\sum_{i\in T}D_i^{-4}\\
&\le\frac{N_ss^5}{8(\min_iD_i)^4}\le\frac R{n^3}.
\end{aligned}\tag{6.3}
$$

The candidate bound is

$$
E(H_r)\le\frac{F_r(q_r)}{n-r}+\frac{8B}{n^3},\tag{6.4}
$$

since $n-r\ge n/2$.

Suppose first that $s\ge r+1$. If $q_s\le r$, use (3.5) in the unrestricted class and (4.1) in the restricted class. In either case

$$
J_s(x)\ge F_r(q_s)+\widehat\gamma\ge F_r(q_r)+\widehat\gamma.
$$

For completeness, $F_r$ is strictly increasing on $[r-1,r]$, because

$$
F_r'(q)=\frac{r^2}{2q^3}(2C-Dq)>0,
\qquad 2C-Dr=r(r^2-3r+1)>0.
$$

If $q_s\ge r$, (3.6) in the unrestricted class gives

$$
J_s(x)\ge r^3/2+\beta_r/2\ge F_r(q_r)+\widehat\gamma,
$$

whereas (4.2) gives the same conclusion in the restricted class. In particular, for $r=9$ and an actual $s\ge10$, (3.6) is precisely

$$
2J_s(x)\ge729+\kappa_9(s-9)+(217-\kappa_9)(q_s-9)\qquad(q_s\ge9).
$$

Here $217-\kappa_9>0$, so the gap is at least $\kappa_9/2>1/2$, even when $q_s>9$. If instead $q_s\le9$, the same graph has $8<q_s\le9$, and (2.8) gives $J_s-F_9(q_s)>1024/81+42(s-10)>1/2$. These two cases cover the actual budget $q_s=m/(n-s)$ without substituting $q_r$ for it. Thus $\widehat\gamma=1/2$ is a common gap in both cases, with $C_0,A,K_0,R,B,H$ as defined in the statement. This is the upper-capacity bridge: a graph with more hubs and $q_s>r$ is still separated by a fixed positive amount. Both cases therefore imply, using $F_r(q_r)>0$, $N_s\le n-r$ and (6.3)–(6.4),

$$
E(G)-E(H_r)\ge\frac{\widehat\gamma}{n}-\frac H{n^3}>0.\tag{6.5}
$$

The last inequality is exactly the square-root condition in (6.1). Thus a minimizing or tying graph must have $s=r$ throughout the closed integer capacity interval.

Let $A_{\mathrm{low}}$ count its sources of degree at most $r-2$. If $A_{\mathrm{low}}\ge1$, (3.1) gives

$$
J_r(x)\ge F_r(q_r)+\frac{3(r-1)A_{\mathrm{low}}}{N}.
$$

Hence (6.3)–(6.4) yield

$$
E(G)-E(H_r)\ge\frac{3(r-1)}{N^2}-\frac H{n^3}
\ge\frac{3(r-1)}{n^2}-\frac H{n^3}>0,\tag{6.6}
$$

by the last condition in (6.1). Every source of a minimizer consequently has degree $r-1$ or $r$. The vertex and edge budgets now force the full count $c$ and the total missing-one count $b$ in Definition 5.1. In particular $c\ge r$, independent of how these missing-one counts are distributed.

It remains to minimize the exact cost, not just its quadratic approximation. For every distribution of missing-one counts,

$$
D_i=N-b_i\ge c\ge r,\quad \sum_iD_i=m,\quad
E(G)=\sum_iM_c(D_i).
$$

The function $M_c$ is strictly convex on $(0,\infty)$. The analytic pattern in [the preceding universal-vertex volume, Theorem 8.2](CDSO_UNIVERSAL_VERTEX_ALL_CYCLOMATIC.md), extends here with adjacent source degrees $a,r$: let $f_k(z)=g(k/z)$, so

$$
M_c(z)=\sqrt{z^2+a^2}-z+c(f_r(z)-f_a(z)),
$$

$$
f_k''(z)=\frac{k^2(3z^2+2k^2)}{z^3(z^2+k^2)^{3/2}}.
$$

For fixed $z>0$, the derivative with respect to $v>0$ of

$$
Q_z(v)=\frac{v(3z^2+2v)}{(z^2+v)^{3/2}}
$$

is

$$
Q_z'(v)=\frac{6z^4+5z^2v+2v^2}{2(z^2+v)^{5/2}}>0.
$$

Thus $f_r''(z)>f_a''(z)$ and

$$
M_c''(z)=\frac{a^2}{(z^2+a^2)^{3/2}}+c(f_r''(z)-f_a''(z))>0.\tag{6.7}
$$

Suppose $D_j\ge D_i+2$, equivalently $b_i\ge b_j+2$. At least one actual source misses hub $i$. Delete its edge to $j$ and add its missing edge to $i$. This changes that source's neighborhood from $[r]\setminus\{i\}$ to $[r]\setminus\{j\}$, raises $D_i$ by one and lowers $D_j$ by one. The operation preserves simplicity, source degree, $n,m,\ell$ and the untouched $c$ full sources, so it preserves connectedness. Hub degrees remain at least $c$, preserving the minimum-degree restriction as well. Strict convexity gives

$$
M_c(D_i+1)+M_c(D_j-1)<M_c(D_i)+M_c(D_j),
$$

for example by integrating the strictly increasing derivative over the two unit intervals. The reverse imbalance is handled by exchanging $i,j$. Repeated legal moves terminate at degrees differing pairwise by at most one, since their integer sum is fixed and each move decreases the sum of their squares. Therefore all minimizing $b_i$ are balanced. Their multiset is unique. Permuting hubs and sources identifies all graphs with that multiset, while any unbalanced graph admits a strictly improving actual move. Combined with (6.5)–(6.6), this proves the exact value and the unique graph isomorphism class. ∎

## 7. Exact prescribed budgets and high-density stability

**Theorem 7.1 (Single-array realization at a prescribed high-density budget).** Fix $r\ge5$, finite $s\ge r$, and $\alpha\in[r-2,r-1]$. Let $x$ be one profile on $[s]$ with $q=1+\alpha$ and all $y_i>0$. Suppose integer budgets $\ell_n$ satisfy $\ell_n/n\to\alpha$ and eventually

$$
0\le\ell_n\le s(n-s)-n+1.
$$

There are simple connected graphs with exactly $n$ vertices, $n-1+\ell_n$ edges and $s$ actual degree-oriented sinks whose type proportions converge to this same $x$, and whose energies satisfy

$$
nE(G_n)\longrightarrow J_s(x).
$$

If $x$ is supported on $K\ge d$ for some fixed $1\le d\le s$, the construction can preserve source degree at least $d$ provided additionally

$$
(d-1)(n-s-1)\le\ell_n
$$

eventually. In particular this lower inequality is automatic here for $d=r-2$. No positivity of all type masses is assumed.

**Proof.** Reserve $s$ hubs and one source adjacent to all of them. Put $M=n-s-1$ for the remaining sources. Round the finitely many numbers $Mx_T$ to nonnegative integer counts summing to $M$, with bounded error in each type; floors followed by distributing the bounded deficit suffice. If a support restriction is imposed, do this entirely within that support. The initial additional-membership count of these sources is

$$
B_0=\sum_T(|T|-1)a_T=M\alpha+O_s(1),
\qquad B_0-\ell_n=o(n).
$$

The exact possible interval for their additional memberships is $[0,(s-1)M]$, and

$$
(s-1)M=s(n-s)-n+1.
$$

If $B_0<\ell_n$, some source lacks a hub membership until the upper endpoint is reached; add one such membership. If $B_0>\ell_n$, some source has at least two neighbors until the lower endpoint is reached; remove one membership while leaving that source nonempty. Stop exactly at $B=\ell_n$. These are $|B_0-\ell_n|=o(n)$ edits. With a degree bound $d$, delete only from sources of degree greater than $d$, and stop at the lower endpoint $(d-1)M$; addition is unchanged. The assumed target lies within these two exact endpoints. For $d=r-2$, $\ell_n/M\to\alpha\ge r-2>d-1$, so the lower endpoint is eventually below the target.

The reserved full source is unchanged, so it connects every hub at every finite order. Other sources retain nonempty neighborhoods. All memberships are subsets of $[s]$, hence the graph is simple, and its edge count is exactly

$$
s+M+B=n-1+\ell_n.
$$

The reserved source and the $o(n)$ edits change each limiting type mass by zero, even for a type whose limiting mass is zero. Thus $a_T/(n-s)\to x_T$, and $D_i/(n-s)\to y_i>0$. For sufficiently large $n$ the hub degrees exceed $s$, whereas source degrees are at most $s$; these are consequently the actual degree-oriented sinks. Applying the actual-edge expansion from (6.3), now with fixed $s$ and positive limiting marginals, gives

$$
E(G_n)=\frac{J_s(x^{(n)})}{n-s}+O(n^{-3}).
$$

Continuity in a neighborhood of the positive limiting marginals proves the energy limit. ∎

**Theorem 7.2 (Capacity-constrained density limit and necessary and sufficient near-minimum structure).** Fix either admissible class of Theorem 6.1 and a prescribed integer sequence $\ell_n$ with

$$
L_r(n)\le\ell_n\le U_r(n)\text{ eventually},\qquad
\frac{\ell_n}{n}\longrightarrow\alpha\in[r-2,r-1].
$$

Then

$$
nE_r^{\min}(n,\ell_n)\longrightarrow F_r(1+\alpha).\tag{7.1}
$$

For any sequence $G_n\in\mathcal A_r(n,\ell_n)$, the following are equivalent:

1. $E(G_n)-E_r^{\min}(n,\ell_n)=o(1/n)$;
2. $nE(G_n)\to F_r(1+\alpha)$;
3. eventually $G_n$ is an actual two-layer graph with exactly $r$ degree-oriented sinks, and, for its source counts and hub degrees with $N=n-r$,

$$
\frac1N\sum_{|T|\le r-2}a_T\longrightarrow0,\qquad
\frac{D_i}{N}-\frac{q_r}{r}\longrightarrow0\quad(1\le i\le r),
\qquad q_r=\frac{n-1+\ell_n}{n-r};\tag{7.2}
$$

4. eventually $G_n$ has exactly those $r$ actual sinks and source–sink structure, and its single profile satisfies

$$
\|x^{(n)}-x^*(q_r)\|_1\longrightarrow0.\tag{7.3}
$$

In the unrestricted class this includes $r=9$ and every $\alpha\in[7,8]$; for general $r\ge5$ the second class retains its minimum-degree hypothesis. Labels of the $r$ sinks may be chosen separately at each order; the limiting candidate is permutation invariant. In particular every hub degree divided by $n$ tends to $(1+\alpha)/r$. These conclusions allow $o(n)$ low-cardinality sources and unbounded sublinear hub imbalances. They do not assert finite disappearance of exceptional sources or a bounded difference of hub degrees.

**Proof.** Theorem 6.1 gives the exact minimum at every sufficiently large order. For its balanced graph, $q_r\to1+\alpha$, $y_i=q_r/r+O(1/N)$, and the actual-edge error (6.3) together with (5.2) gives

$$
E_r^{\min}(n,\ell_n)=\frac{F_r(q_r)}N+O_r(n^{-3}).\tag{7.4}
$$

Since $n/N\to1$, this proves (7.1) and the equivalence of 1 and 2.

Assume 1. The limit is bounded by $r^3/2$, because $F_r$ increases to $F_r(r)=r^3/2$. Thus $E(G_n)\le C_0/n$ eventually. The fixed-cost reduction of the sink-incidence volume, Theorem 3.1, applies to these actual graphs. It supplies their two-layer structure, a bounded number of sinks and the positive bound $D_i/n\ge1/(3C_0)$ for every actual sink. Capacity supplies $s\ge r$; no hub with a vanishing normalized degree has been suppressed. If $s>r$ along any infinite subsequence, (6.5) gives

$$
\liminf n\bigl(E(G_n)-E_r^{\min}(n,\ell_n)\bigr)\ge\widehat\gamma>0
$$

on that subsequence, contradicting 1. This exclusion uses (3.6) or (4.2) when $q_s>r$, so it remains valid at $\alpha=r-1$. Eventually $s=r$.

For the actual $r$-sink array let $\Delta_n=J_r(x^{(n)})-F_r(q_r)\ge0$. Equations (6.3) and (7.4) imply

$$
\Delta_n=N\bigl(E(G_n)-E_r^{\min}(n,\ell_n)\bigr)+O_r(n^{-2})\longrightarrow0.
$$

Theorem 3.1 yields (7.2) and (7.3), including the explicit estimate (3.2). This proves 3 and 4. Conversely 3 implies 4 directly from (3.4), independently of a presumed small energy gap.

Finally assume 4. Then every marginal tends to $(1+\alpha)/r>0$, so the bounded source degrees and positive linear hub degrees allow the actual-edge expansion. The functional $J_r$ is continuous there, and $x^*(q_r)\to x^*(1+\alpha)$, hence

$$
nE(G_n)=\frac nN J_r(x^{(n)})+O_r(n^{-2})\longrightarrow F_r(1+\alpha).
$$

This proves 2 and completes all equivalences.

The endpoint capacity hypotheses cannot be replaced by their density limits: $\alpha$ alone does not specify the least feasible integer hub count. At $\alpha=r-2$ the candidate full mass tends to zero, but its exact count is still $c\ge r$ at every finite order, connecting the entire construction. At $\alpha=r-1$ the missing-one masses may vanish, and $b=0$ gives an actual complete bipartite graph. All proofs above allow these zero-mass limits. ∎

## 8. An unconditional upper interval and the boundary of moment relaxation

**Theorem 8.1 (An explicit unconditional upper-density interval for all $r$).** For every integer $r\ge5$, put

$$
\delta_r=\min\left\{1,\frac{\kappa_r}{2r^2-\kappa_r}\right\}.
$$

For $q=r-\delta$ with $0\le\delta\le\delta_r$, every finite $s\ge r$ and every profile of mean $q$ satisfy $J_s(x)\ge F_r(q)$, with equality exactly for $s=r$, $x=x^*(q)$. For $s\ge r+1$ the following strict bound holds throughout this closed interval:

$$
2\bigl(J_s(x)-F_r(q)\bigr)
\ge\kappa_r-(2r^2-\kappa_r)\delta+r\delta^2
+\kappa_r(s-r-1)>0.\tag{8.1}
$$

More generally, for every $q\in[r-1,r]$ and $s\ge r+1$,

$$
2\bigl(J_s(x)-F_r(q)\bigr)
\ge\Gamma_r(q)+\kappa_r(s-r-1),
$$

$$
\Gamma_r(q)=\kappa_r(r+1-q)
-\left(\frac{r^2}{q^2}-1\right)f_r(q).\tag{8.2}
$$

In particular every hub count

$$
s>q+\frac{(r^2/q^2-1)f_r(q)}{\kappa_r}
$$

is strictly excluded from equality or improvement over the candidate.

**Proof.** Theorem 2.1 at $\beta=\kappa_r$ gives (8.2). The positivity $2r^2-\kappa_r>0$ follows from $\kappa_r\le2(r-1)^2<2r^2$. Monotonicity of $F_r$ on $[r-1,r]$ gives

$$
\frac{f_r(q)}{q^2}=\frac{2F_r(q)}{r^2}\le r.
$$

Therefore, when $q=r-\delta$,

$$
\left(\frac{r^2}{q^2}-1\right)f_r(q)
\le r(r^2-q^2)=2r^2\delta-r\delta^2.
$$

Substitute this in (8.2) to obtain (8.1). At $\delta=0$ its first three terms equal $\kappa_r>0$. For $0<\delta\le\kappa_r/(2r^2-\kappa_r)$ the first two terms have nonnegative sum and $r\delta^2>0$. Thus the stated endpoints are strict as well. Theorem 3.1 supplies the equality class for $s=r$. The last exclusion follows by rearranging Theorem 2.1 directly. ∎

**Theorem 8.2 (Exact two-moment relaxation at $r=9$).** Consider probability laws on pairs $(K,U)$ with integer $1\le K\le10$, real $U\ge K$, and

$$
\mathbb E K=8,\qquad \mathbb E U=10.
$$

The exact infimum, attained by such a law, is

$$
\min\mathbb E(KU^2)=516+16\sqrt{63}<648=2F_9(8).\tag{8.3}
$$

An attaining law, with $h=4\sqrt{63}$, is

$$
\begin{array}{c|ccc}
(K,U)&(1,1+h)&(8,8)&(9,9)\\ \hline
\mathbb P&2/h&1-16/h&14/h.
\end{array}\tag{8.4}
$$

There is also a wholly rational feasible law

$$
\begin{array}{c|ccc}
(K,U)&(1,33)&(8,8)&(9,9)\\ \hline
\mathbb P&1/16&1/2&7/16
\end{array}
$$

with objective $643<648$. Neither law is induced by a genuine profile on $[10]$ through Definition 1.1.

**Proof.** Here $a=8$, $D=217$, $C=1224$, $f_9(8)=512$ and $\kappa_9=2+8\sqrt{63}=2+2h$. The pointwise scalar inequality (2.1), which was proved for all integer $k\ge1$ and all $u\ge k$, integrates over any law in this relaxed problem to give

$$
\mathbb E(KU^2)\ge(217-\kappa_9)8+\kappa_9\,10-1224
=516+16\sqrt{63}.
$$

This is weak duality proved simply by integrating a pointwise inequality; it invokes no strong-duality or joint-realizability theorem.

Since $h>16$, all three probabilities in (8.4) are positive and sum to one. Direct summation gives $\mathbb E K=8$ and $\mathbb E U=10$. Equality holds in the scalar support inequality at each atom: at $K=1$, $U=\kappa_9/2=1+h$, while $K=8,9$ are the two integer zeros with $U=K$. Its objective is therefore the lower bound, proving attainment. It is strictly less than $648$ because $16\sqrt{63}<132$, equivalently $63<(33/4)^2$. The rational law has means

$$
\frac{1+64+63}{16}=8,\qquad
\frac{33+64+63}{16}=10,
$$

and objective

$$
\frac{1089}{16}+\frac{512}{2}+\frac{7\cdot729}{16}=643.
$$

For nonrealizability, either law assigns positive mass to $(K,U)=(8,8)$. If induced by a genuine finite array, some positive-mass eight-element type $T$ would satisfy

$$
8=U_T=\sum_{i\in T}y_i^{-1},\qquad y_i^{-1}\ge1.
$$

Every one of these eight marginals would equal one. Every positive-mass type would then contain all these eight elements, forcing $K\ge8$ almost surely. This contradicts the positive mass at $K=1$. The positive mass at $(K,U)=(9,9)$ also violates (2.2), since $q=8$ requires $U\ge81/8>9$ on every nine-element type of any actual array. Thus both laws exhibit the insufficiency of the relaxed moment constraints. They provide no genuine-array counterexample, and the exact relaxed optimum (8.3) coexists with the strictly larger actual-array bound of Theorem 2.3. ∎

**Definition 8.3 (Remaining comparison and its method boundary).** For $r\ge10$ outside the unconditional region of Theorem 8.1, and without the support hypothesis of Theorem 4.1, the remaining comparison asks whether every genuine profile of mean $q\in[r-1,r]$ and finite $s\ge r$ satisfies

$$
J_s(x)\ge F_r(q).
$$

Theorem 4.2 specifies a necessary weighted low-cardinality defect for any counterexample, and (8.2) already excludes sufficiently large $s$. This unrestricted comparison for $r\ge10$ remains open in that range; the conditional graph minimum of Theorem 6.1 does not settle it.

For $r=9$, the full interval $q\in[8,9]$ is covered by Theorem 3.2. At $q=8$, $s=10$, (2.9) supplies the quantitative compensation above the moment-relaxation optimum $516+16\sqrt{63}$, with a strict margin greater than $32$ beyond the $132-16\sqrt{63}$ needed to reach $2F_9(8)=648$. The exact actual-array minimum and all minimizing arrays at that point are not determined here. The overlap constraints (2.2)–(2.3) are necessary, with no claim that they characterize every realizable joint law; the certificate (2.5) is asserted only for $q\in[8,9]$.

The shared-budget certificate and its nine-hub graph consequences are repo-derived for the array and graph classes defined here. The fixed-cost reduction, the actual-edge expansion and the two-hub convexity argument are supplied by the two cited repository volumes with the scope specified above; the original CDSO papers supply the definition and historical comparisons, not these higher-capacity minima. No new literature priority claim is made. The full text of the Zhao–Zhao work has not been obtained here, so its hypotheses, conclusions and possible overlap are not assessed and it is not used as an input theorem.

## 追加锚（本行以下为增补区）
