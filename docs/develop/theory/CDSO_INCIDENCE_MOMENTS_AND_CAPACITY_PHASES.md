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

**Theorem 2.4 (Ten-hub comparison from a shared-budget certificate).** Let $s\ge11$ be finite, let $x$ be one profile of Definition 1.1, and suppose $9\le q\le10$. With $t=q-9\in[0,1]$, define

$$
G_q(k,u)=ku^2-292k-100u+151q+1440.
$$

For every positive integer $k$ and every real $u\ge\max\{k,k^2/q\}$,

$$
G_q(k,u)\ge0,\qquad
G_q(k,u)=0\ \Longleftrightarrow\ (q,k,u)=(9,9,9).\tag{2.10}
$$

For the actual array, with $R_{\mathrm{inc}}$ as in Theorem 2.1, the exact remainder formula is

$$
\begin{aligned}
2\bigl(J_s(x)-F_{10}(q)\bigr)
&=29+100(s-11)+\frac{521t+3438t^2+141t^3}{q^2}\\
&\quad+R_{\mathrm{inc}}+\mathbb E G_q(K,U_T),
\end{aligned}\tag{2.11}
$$

where $\mathbb E G_q(K,U_T)>0$. Consequently

$$
J_s(x)-F_{10}(q)>\frac{29}{2}+50(s-11),\qquad
F_{10}(q)=\frac{50(271q-1710)}{q^2}.\tag{2.12}
$$

**Proof.** First prove (2.10) for every positive integer $k$, without any upper cutoff. For $1\le k\le7$, completing the square gives

$$
G_q(k,u)=k(u-50/k)^2+c_k+151t,
$$

where, in order of increasing $k$,

$$
(c_1,\ldots,c_7)=
(7,965,3269/3,1006,839,1891/3,2785/7).
$$

Each constant is strictly positive, so these cases hold strictly for every real $u$.

For $k=8,9$, the derivative $2ku-100$ is strictly positive on $u\ge k$, since $2k^2-100>0$. Thus

$$
G_q(8,u)\ge G_q(8,8)=175+151t>0,\qquad
G_q(9,u)\ge G_q(9,9)=151t\ge0.
$$

Equality in these cases requires exactly $q=9$, $k=9$, $u=9$.

For $k=10$, the permitted range has $u\ge100/q$. The derivative is at least $2000/q-100\ge100>0$, so it suffices to evaluate at $u=100/q$. Expansion gives

$$
q^2G_q(10,100/q)=199+53t+2597t^2+151t^3>0.\tag{2.13}
$$

For every integer $k\ge11$, the same monotonicity reduces to $u=k^2/q$, because $2k^3/q-100>0$. Set

$$
h_k(q)=G_q(k,k^2/q)
=\frac{k^5}{q^2}-\frac{100k^2}{q}-292k+151q+1440.
$$

Its derivative is

$$
h_k'(q)=\frac{-2k^5+100k^2q+151q^3}{q^3}<0\quad(9\le q\le10).
$$

Indeed its numerator is at most $-2k^5+1000k^2+151000$, whereas

$$
2k^5-1000k^2=2k^2(k^3-500)
\ge2\cdot121\cdot831=201102>151000.
$$

Hence $h_k(q)\ge h_k(10)$. With $v=k-11\ge0$, the exact expansion

$$
100h_k(10)=v^5+55v^4+1210v^3+12310v^2+22005v+13851>0\tag{2.14}
$$

finishes the unbounded tail. This proves (2.10), including its equality class and both endpoints of the $q$ interval.

For the actual pairs $(K,U_T)$, (2.2) supplies the permitted domain of (2.10). The incidence identity of Theorem 2.1 and the two means give exactly

$$
2J_s(x)=141q+100s-1440+R_{\mathrm{inc}}+\mathbb E G_q(K,U_T).\tag{2.15}
$$

If the last expectation were zero, nonnegativity and the unique zero in (2.10) would force $q=9$ and $K=U_T=9$ almost surely. Then $\mathbb E U_T=9$, contradicting $\mathbb E U_T=s\ge11$. Thus that expectation is strictly positive; no strictness assumption on $R_{\mathrm{inc}}$ is needed.

Finally the benchmark subtraction is the polynomial identity

$$
q^2(141q-340)-100(271q-1710)
=2349+1043t+3467t^2+141t^3.
$$

Subtracting $29q^2$ from this identity leaves $521t+3438t^2+141t^3$. Substitute into (2.15) to obtain (2.11). Every additional term there is nonnegative, and the expectation is strictly positive, proving (2.12). Zero type masses, arbitrarily small positive marginals, rare types and disconnected incidence supports are all permitted. The common budget (2.2) and both means are taken from this one array. The coefficient $100$ is part of (2.10), whose domain includes $u\ge k^2/q$; it is not a substitution for $\beta$ in the different certificate (2.1). ∎

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

**Theorem 3.2 (Unrestricted profiles for $r=5,6,7,8,9,10$).** Let $r\in\{5,6,7,8,9,10\}$, $q\in[r-1,r]$, and let $x$ be any profile on any finite $[s]$ with $s\ge r$. Then

$$
J_s(x)\ge F_r(q),
$$

with equality exactly when $s=r$ and $x=x^*(q)$, up to relabeling. For $s\ge r+1$ the stronger bound is

$$
J_s(x)-F_r(q)\ge\frac12+\frac{\beta_r}{2}(s-r-1),\qquad
(\beta_5,\beta_6,\beta_7,\beta_8,\beta_9,\beta_{10})=(23,32,42,53,\kappa_9,\kappa_{10}).\tag{3.5}
$$

For these same six values of $r$, every profile with $s\ge r+1$ and $q\ge r$ satisfies

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

that bound implies (3.5) with $\beta_9=\kappa_9$ for every finite $s\ge10$ and $q\in[8,9]$. For $r=10$, Theorem 2.4 gives

$$
2\bigl(J_s(x)-F_{10}(q)\bigr)>29+100(s-11)
\quad(s\ge11,\ 9\le q\le10).
$$

Since $\kappa_{10}=2+24\sqrt{10}<78<100$ and $29>1$, this implies (3.5) with $\beta_{10}=\kappa_{10}$. Neither application restricts source cardinalities, requires positive mass for every type, or discards any hub with positive marginal. For $s=r$, Theorem 3.1 gives the inequality and the complete equality class. Thus no assumption on the cardinalities in the support is needed.

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

1. for $r\in\{5,6,7,8,9,10\}$, all of $\mathcal G(n,\ell)$;
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

with $N,c,b_i$ as in Definition 5.1; the minimum of $\Phi$ is $m$ plus (6.2). The threshold is sufficient; it is not asserted to be least. For $r\ge11$, the second class here is a material minimum-degree restriction. The unrestricted conclusion includes the full intervals $[L_9(n),U_9(n)]=[7n-62,8n-80]$ and $[L_{10}(n),U_{10}(n)]=[8n-79,9n-99]$.

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

Here $217-\kappa_9>0$, so the gap is at least $\kappa_9/2>1/2$, even when $q_s>9$. If instead $q_s\le9$, the same graph has $8<q_s\le9$, and (2.8) gives $J_s-F_9(q_s)>1024/81+42(s-10)>1/2$. For $r=10$, (3.6) likewise gives the unrestricted estimate

$$
2J_s(x)\ge1000+\kappa_{10}(s-10)+(271-\kappa_{10})(q_s-10)
\qquad(s\ge11,\ q_s\ge10).
$$

Here $271-\kappa_{10}>0$, so the gap above $1000/2$ is at least $\kappa_{10}/2>1/2$. In the other case the same actual graph has $9<q_s\le10$, and (2.12) gives $J_s(x)-F_{10}(q_s)>29/2+50(s-11)>1/2$. Thus the interval certificate is used only in its domain; the unrestricted certificate supplies every value $q_s>10$. For both $r=9$ and $r=10$, these two cases cover the actual budget $q_s=m/(n-s)$ without substituting $q_r$ for it. Thus $\widehat\gamma=1/2$ is a common gap in both cases, with $C_0,A,K_0,R,B,H$ as defined in the statement. This is the upper-capacity bridge: a graph with more hubs and $q_s>r$ is still separated by a fixed positive amount. Both cases therefore imply, using $F_r(q_r)>0$, $N_s\le n-r$ and (6.3)–(6.4),

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

In the unrestricted class this includes $r=9$ with every $\alpha\in[7,8]$, and $r=10$ with every $\alpha\in[8,9]$; for general $r\ge5$ the second class retains its minimum-degree hypothesis. Labels of the $r$ sinks may be chosen separately at each order; the limiting candidate is permutation invariant. In particular every hub degree divided by $n$ tends to $(1+\alpha)/r$. These conclusions allow $o(n)$ low-cardinality sources and unbounded sublinear hub imbalances. They do not assert finite disappearance of exceptional sources or a bounded difference of hub degrees.

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

**Definition 8.3 (Remaining comparison and its method boundary).** For $r\ge11$ outside the unconditional region of Theorem 8.1, and without the support hypothesis of Theorem 4.1, the remaining comparison asks whether every genuine profile of mean $q\in[r-1,r]$ and finite $s\ge r$ satisfies

$$
J_s(x)\ge F_r(q).
$$

Theorem 4.2 specifies a necessary weighted low-cardinality defect for any counterexample, and (8.2) already excludes sufficiently large $s$. This unrestricted comparison for $r\ge11$ remains open in that range; the conditional graph minimum of Theorem 6.1 does not settle it.

For $r=9$, the full interval $q\in[8,9]$ is covered by Theorem 3.2. At $q=8$, $s=10$, (2.9) supplies the quantitative compensation above the moment-relaxation optimum $516+16\sqrt{63}$, with a strict margin greater than $32$ beyond the $132-16\sqrt{63}$ needed to reach $2F_9(8)=648$. The exact actual-array minimum and all minimizing arrays at that point are not determined here. For $r=10$, Theorem 2.4 settles the comparison for the full interval $q\in[9,10]$ and every finite $s\ge11$; optimality of its numerical gap is not determined here. The overlap constraints (2.2)–(2.3) are necessary, with no claim that they characterize every realizable joint law. The certificate (2.5) is asserted only for $q\in[8,9]$, and (2.10) only for $q\in[9,10]$. Theorem 9.2 shows that even the self-consistent distribution-dependent $m_k$ constraints are insufficient by themselves to prove the all-$r$ comparison. Theorem 10.1 gives a genuine-array restriction on the scale of a possible uniform all-$r$ gap.

The shared-budget certificates, their nine- and ten-hub graph consequences, the rational relaxation obstruction of Theorem 9.2 and the genuine-array gap family of Theorem 10.1 are repo-derived for the classes defined here. The fixed-cost reduction, the actual-edge expansion and the two-hub convexity argument are supplied by the two cited repository volumes with the scope specified above; the original CDSO papers supply the definition and historical comparisons, not these higher-capacity minima. No new literature priority claim is made. The full text of the Zhao–Zhao work has not been obtained here, so its hypotheses, conclusions and possible overlap are not assessed and it is not used as an input theorem.

## 9. A self-consistent overlap relaxation that fails for every $r\ge17$

**Definition 9.1 (Distribution-dependent scalar relaxation).** For a positive integer $s$ and a real $q$, consider finite probability laws on pairs $(K,U)$ such that

$$
K\in\{1,\ldots,s\},\qquad
\mathbb E K=q,\qquad \mathbb E U=s,\qquad
m_k=\mathbb E\min(k,K)\quad(k\in\mathbb Z_{\ge1}),
$$

$$
U\ge\max\{K,K^2/m_K\}\quad\text{almost surely}.
$$

The surrogate objective is $V=\mathbb E(KU^2)$. The same $K$ law is used to compute every $m_k$; these values are not independent variables. By (2.2) and the incidence identity, every actual array supplies a feasible law with $V\le2J_s(x)$. Sufficiency of these scalar constraints for an actual array is not part of this definition.

**Theorem 9.2 (A rational obstruction throughout $r\ge17$).** For every integer $a\ge16$, put $r=a+1$, $q=a$, $s=a+2$, and $M=5a^2-a+1$. The following law is feasible in Definition 9.1:

$$
\begin{array}{c|ccc}
K&1&a&a+1\\ \hline
\mathbb P&1/(5a)&4/5&(a-1)/(5a)\\
U&(41a^4+13a^2+1)/(aM)&5a^3/M&(a+1)^2/a.
\end{array}\tag{9.1}
$$

Its objective satisfies

$$
V-a(a+1)^2=-\frac{P(a)}{5a^2M^2}<0,\tag{9.2}
$$

where

$$
P(a)=110a^8-1697a^7+58a^6-949a^5+56a^4-211a^3+24a^2-18a+2.
$$

No actual array on $[s]$ with all marginals positive induces this law. In particular minimizing the scalar surrogate under Definition 9.1 cannot alone give the lower bound $2F_r(a)=a(a+1)^2$ for all $r$.

**Proof.** All three probabilities are positive and sum to one. Their means are

$$
\frac1{5a}+\frac{4a}{5}+\frac{(a+1)(a-1)}{5a}=a,
$$

$$
\begin{aligned}
\mathbb E U
&=\frac{41a^4+13a^2+1}{5a^2M}
 +\frac{4a^3}{M}+\frac{(a-1)(a+1)^2}{5a^2}\\
&=a+2=s.
\end{aligned}
$$

The same $K$ law gives, at all cardinalities that carry mass,

$$
m_1=1,\qquad
m_a=\frac1{5a}+a\left(\frac45+\frac{a-1}{5a}\right)
=a-\frac{a-1}{5a}=\frac{M}{5a},\qquad
m_{a+1}=a.
$$

Writing $U_k$ for the value of $U$ at cardinality $k$ in (9.1), one has $U_a=a^2/m_a$ and $U_{a+1}=(a+1)^2/m_{a+1}$. Since $m_a\le a$ and $m_{a+1}\le a+1$, these two values also satisfy $U\ge K$. For the singleton atom,

$$
U_1-1=\frac{41a^4-5a^3+14a^2-a+1}{aM}>0.
$$

Its numerator is $a^3(41a-5)+a(14a-1)+1>0$ for $a\ge1$, so both constraints hold there as well. Also $1\le K\le a+1<s$. This proves all of the relaxed feasibility conditions simultaneously.

Direct substitution into $V$ gives

$$
V=\frac{(41a^4+13a^2+1)^2}{5a^3M^2}
+\frac{20a^7}{M^2}+\frac{(a-1)(a+1)^5}{5a^3}.
$$

Subtracting $a(a+1)^2$ and collecting terms gives (9.2). To prove its strict sign for every $a\ge16$, group the polynomial as

$$
\begin{aligned}
P(a)&=a^7(110a-1697)+a^5(58a-949)\\
&\quad+a^3(56a-211)+(24a^2-18a+2).
\end{aligned}
$$

The first two terms together are at least

$$
63a^7-21a^5=21a^5(3a^2-1)>0,
$$

and the other two grouped terms are positive. Thus $P(a)>0$ for the entire unbounded range.

For nonrealizability, suppose an actual array with $s=a+2$ and positive marginals induced (9.1). Every positive-mass type of size $a+1$ would then have $U_T=(a+1)^2/a$. Such types have positive total mass. Each omits one of the $s$ hubs, whose marginal is positive; consequently

$$
b_T=\sum_{i\in T}y_i<\sum_{i=1}^s y_i=q=a.
$$

The within-type inequality in (2.2) forces

$$
U_T\ge\frac{(a+1)^2}{b_T}>\frac{(a+1)^2}{a},
$$

a contradiction. The obstruction is a failure of common-array realization, even though $m_k$ is self-consistent with the one displayed $K$ law. It is a counterexample to the sufficiency of this relaxation for the desired bound, not to the original array or graph comparison.

For example, at $a=16$ the probabilities in (9.1) are $1/80,4/5,3/16$, its $U$ values are $538061/4048,4096/253,289/16$, and its corresponding $m_K$ values are $1,253/16,16$. Formula (9.2) gives

$$
V=\frac{37817565947}{8193152},\qquad
2F_{17}(16)=4624,\qquad
V-2F_{17}(16)=-\frac{67568901}{8193152}.
$$

These follow by substituting $a=16$ in the proved formulas. ∎

## 10. Genuine rare extra hubs and the scale of a uniform gap

**Theorem 10.1 (A genuine family with gap of order $r^{3/2}$).** For every integer $a\ge4$, put $r=a+1$, $s=a+2$, $H=[a+1]$ and $e=a+2$. For each real $0<\varepsilon\le1/a$, define the one array

$$
x_{\{e\}}=\varepsilon,\qquad x_H=(a-1)\varepsilon,\qquad
x_{H\setminus\{j\}}=\frac{1-a\varepsilon}{a+1}\quad(j\in H),
$$

with every other type mass zero. This is an actual profile of mean $q=a$ with positive marginals. Its support hypergraph, with vertices $[s]$ and hyperedges the positive-mass types, has two connected components. Define

$$
E_a=2a^3-2a-1,\qquad A_a=2a^3+2a^2-2a-1.
$$

Its energy and gap are exactly

$$
2J_s(x)=\frac{(a+1)^2[a^3+\varepsilon E_a]}{(a-\varepsilon)^2}
+\frac1\varepsilon,\tag{10.1}
$$

$$
2\bigl(J_s(x)-F_r(a)\bigr)
=\frac1\varepsilon+
\frac{(a+1)^2\varepsilon(A_a-a\varepsilon)}{(a-\varepsilon)^2}>0.\tag{10.2}
$$

For $\varepsilon_a=1/(\sqrt2\,a^{3/2})$ the limit is

$$
\frac{J_s(x(\varepsilon_a))-F_{a+1}(a)}{a^{3/2}}
\longrightarrow\sqrt2,
\qquad
\frac{J_s(x(\varepsilon_a))-F_{a+1}(a)}{(a+1)^{3/2}}
\longrightarrow\sqrt2.\tag{10.3}
$$

Thus no constant $c>0$ can satisfy $J_s(x)-F_r(q)\ge cr^2$ uniformly for all integers $r\ge5$, all finite $s\ge r+1$ and all actual profiles with $q\in[r-1,r]$.

**Proof.** The displayed masses are nonnegative and sum to

$$
\varepsilon+(a-1)\varepsilon+1-a\varepsilon=1.
$$

Their cardinality mean is

$$
\varepsilon+(a+1)(a-1)\varepsilon+a(1-a\varepsilon)=a.
$$

Counting the types containing each hub gives

$$
y_i=\frac{a-\varepsilon}{a+1}>0\quad(i\in H),\qquad
y_e=\varepsilon>0,
$$

$$
\begin{aligned}
w_i&=\frac{a^3(1-a\varepsilon)}{a+1}
 +(a+1)^2(a-1)\varepsilon
 =\frac{a^3+\varepsilon E_a}{a+1}\quad(i\in H),\\
w_e&=\varepsilon.
\end{aligned}
$$

In particular the extra marginal is retained. The only positive-mass type containing $e$ is $\{e\}$, while $H$ itself has positive mass. No positive-mass type meets both $H$ and $\{e\}$, so the incidence support has these two components. This remains true at $\varepsilon=1/a$, where all missing-one masses are zero; the core marginals remain positive there.

Summing $w_i/y_i^2$ gives (10.1). Since $2F_r(a)=a(a+1)^2$, subtraction gives (10.2). Its denominator is positive. Moreover $a\varepsilon\le1$ and $A_a>1$ for $a\ge4$, so both summands are strictly positive. Hence these arrays do not improve or tie the candidate.

The choice $\varepsilon_a$ lies in $(0,1/a]$. Dividing (10.2) by $2a^{3/2}$ gives

$$
\frac{J_s(x(\varepsilon_a))-F_r(a)}{a^{3/2}}
=\frac1{\sqrt2}
+\frac{(1+1/a)^2\bigl(A_a/a^3-\varepsilon_a/a^2\bigr)}
 {2\sqrt2(1-\varepsilon_a/a)^2}.
$$

As $a\to\infty$, the second term tends to $1/\sqrt2$, proving the first limit in (10.3). The second follows from $a/(a+1)\to1$. A wholly rational infinite subfamily is

$$
a=2b^2,\qquad \varepsilon=\frac1{4b^3},\qquad b\in\mathbb Z,\ b\ge2;
$$

it has exactly the same limit. Thus the gap divided by $r^2$ tends to zero through actual positive-marginal arrays. For any proposed $c>0$, a sufficiently large member violates the asserted uniform lower bound. ∎

The formulas (10.1)–(10.3) do not assert that these arrays minimize $J_s$, or determine the largest positive gap for any fixed $r$. They restrict the possible scale of a uniform all-$r$ gap. The exact array family has disconnected support; it is not itself a connected finite graph construction at every prescribed budget. Theorem 7.1 can realize a fixed profile asymptotically under its stated budget hypotheses, but does not identify the finite optimum or transfer (10.2) to every integer graph budget.

## 追加锚（本行以下为增补区）

## 11. Common-incidence truncation and unrestricted capacity phases

**Definition 11.1 (Common size-column data).** Let $s$ be a positive integer. A common incidence datum consists of real numbers $p_k,z_{ik}$, for $1\le k\le s$ and $1\le i\le s$, satisfying

$$
p_k\ge0,\qquad \sum_{k=1}^sp_k=1,\qquad
0\le z_{ik}\le p_k,\qquad \sum_{i=1}^sz_{ik}=kp_k.
$$

Put

$$
y_i=\sum_kz_{ik}>0,\qquad
q=\sum_kkp_k=\sum_i y_i,\qquad
w_i=\sum_kk^2z_{ik},\qquad
2\mathcal J_s(p,z)=\sum_i\frac{w_i}{y_i^2}.
$$

Every profile of Definition 1.1 supplies one such datum by

$$
p_k=\sum_{|T|=k}x_T,\qquad
z_{ik}=\sum_{\substack{|T|=k\\i\in T}}x_T.
$$

The resulting $y_i,w_i,q$ agree with Definition 1.1 and $\mathcal J_s(p,z)=J_s(x)$. In particular the column caps and all the denominators come from the same profile. No converse representation is needed below. For integers $r\ge2$, extend the notation of Definition 1.2 by

$$
a=r-1,\qquad D=3a^2+3a+1,\qquad C=ar(2a+1),
\qquad F_r(q)=\frac{r^2(Dq-C)}{2q^2}\quad(q>0).
$$

For $r\ge5$ these are precisely the earlier quantities.

**Theorem 11.2 (Common-incidence truncation and an integer-moment gap).** Let $r\ge2$ and $s\ge r+1$ be integers. Suppose the datum of Definition 11.1 has $a\le q\le r$, where $a=r-1$. Relabel its marginals so that $y_1\ge\cdots\ge y_s>0$, and put

$$
A=\{1,\ldots,r\},\qquad h=s-r,\qquad
u=\sum_{i\in A}y_i,\qquad v=\sum_{i\notin A}y_i=q-u,
$$

Define

$$
M_2=\sum_kk^2p_k,\qquad B_{\mathrm{inc}}=M_2-a^2,\qquad
\Delta_{\mathrm{int}}=\sum_k(k-a)(k-r)p_k.
$$

Then $u,v>0$, $B_{\mathrm{inc}}\ge0$, $\Delta_{\mathrm{int}}\ge0$, and

$$
\begin{aligned}
2\mathcal J_s(p,z)
&\ge\sum_{i\in A}\left(\frac{a^2}{y_i}
                    +\frac{B_{\mathrm{inc}}}{y_i^2}\right)
       +\sum_{i\notin A}\frac1{y_i}\\
&\ge\frac{a^2r^2}{u}+\frac{B_{\mathrm{inc}}r^3}{u^2}
       +\frac{h^2}{v}.\tag{11.1}
\end{aligned}
$$

Consequently

$$
2\bigl(\mathcal J_s(p,z)-F_r(q)\bigr)
\ge\frac{h(2ar+h)}q+\frac{r^3\Delta_{\mathrm{int}}}{q^2}>0.\tag{11.2}
$$

In particular

$$
\mathcal J_s(p,z)-F_r(q)
\ge\frac{2ar+1}{2q}\ge a+\frac1{2r}.
$$

The assertions allow zero columns, zero entries, ties between marginals, arbitrarily small positive marginals, and all sizes $1\le k\le s$. No assertion of optimality of these gap constants is made.

**Proof.** Write $t=q-a\in[0,1]$. Consecutive integrality gives $(k-a)(k-r)\ge0$ for every integer $k$, so

$$
B_{\mathrm{inc}}=(2a+1)t+\Delta_{\mathrm{int}}\ge0.\tag{11.3}
$$

Order the reciprocal weights $\omega_i=y_i^{-2}$, so that $\omega_i\le\omega_r$ on $A$ and $\omega_i\ge\omega_r$ on its complement. For every $k\ge r$, use the cap $z_{ik}\le p_k$ on $A$ and nonnegativity on its complement to obtain

$$
\begin{aligned}
\sum_i\omega_i z_{ik}-p_k\sum_{i\in A}\omega_i
&=\sum_{i\in A}\omega_i(z_{ik}-p_k)
  +\sum_{i\notin A}\omega_i z_{ik}\\
&\ge\omega_r\left(\sum_i z_{ik}-rp_k\right)
 =\omega_r(k-r)p_k\ge0.\tag{11.4}
\end{aligned}
$$

This calculation also covers $p_k=0$. It uses the same ordered marginals for every column.

For the low and high columns set

$$
L_{\mathrm{col}}=\sum_{k<a}(a^2-k^2)p_k,\qquad
P_{\mathrm{col}}=\sum_{k\ge r}(k^2-a^2)p_k,\qquad
\tau_i=\sum_k\min\{k^2,a^2\}z_{ik}.
$$

Since there is no integer strictly between $a$ and $r$, one has the exact identities

$$
w_i=\tau_i+\sum_{k\ge r}(k^2-a^2)z_{ik},\qquad
P_{\mathrm{col}}-L_{\mathrm{col}}=B_{\mathrm{inc}}.
$$

For $i\in A$, the very same column caps give

$$
\tau_i=a^2y_i-\sum_{k<a}(a^2-k^2)z_{ik}
\ge a^2y_i-L_{\mathrm{col}}.
$$

For $i\notin A$, the inequalities $k\ge1$ and $a\ge1$ give $\tau_i\ge y_i$. Multiply these inequalities by $\omega_i$ and sum. In the high-column part use (11.4), whose coefficients $k^2-a^2$ are nonnegative. The result is

$$
\begin{aligned}
\sum_i\frac{w_i}{y_i^2}
&\ge a^2\sum_{i\in A}\frac1{y_i}
  -L_{\mathrm{col}}\sum_{i\in A}\frac1{y_i^2}
  +\sum_{i\notin A}\frac1{y_i}
  +P_{\mathrm{col}}\sum_{i\in A}\frac1{y_i^2}\\
&=a^2\sum_{i\in A}\frac1{y_i}
  +B_{\mathrm{inc}}\sum_{i\in A}\frac1{y_i^2}
  +\sum_{i\notin A}\frac1{y_i}.
\end{aligned}
$$

Thus the high-column gain cancels the entire low-column loss on this one core. No separate choice or optimization of their marginals has occurred. The elementary Cauchy–Schwarz inequalities

$$
\sum_{i\in A}\frac1{y_i}\ge\frac{r^2}{u},\qquad
\sum_{i\in A}\frac1{y_i^2}
\ge\frac1r\left(\sum_{i\in A}\frac1{y_i}\right)^2
\ge\frac{r^3}{u^2},\qquad
\sum_{i\notin A}\frac1{y_i}\ge\frac{h^2}{v}
$$

prove (11.1), since $B_{\mathrm{inc}}\ge0$.

Because $u+v=q$ and $u,v>0$,

$$
\frac{a^2r^2}{u}+\frac{h^2}{v}-\frac{(ar+h)^2}{q}
=\frac{(arv-hu)^2}{uvq}\ge0,
\qquad \frac{B_{\mathrm{inc}}r^3}{u^2}
\ge\frac{B_{\mathrm{inc}}r^3}{q^2}.
$$

The target has the exact identity

$$
2F_r(q)=\frac{a^2r^2}{q}
       +\frac{(2a+1)t r^3}{q^2},\tag{11.5}
$$

because $D=a^2+(2a+1)r$ and $C=a(2a+1)r$. Substitute (11.3) in (11.1), apply the preceding two inequalities and subtract (11.5). Expanding $(ar+h)^2-a^2r^2=h(2ar+h)$ proves (11.2). Finally $h\ge1$ and $q\le r$ imply the stated uniform positive bound. All divisions used only $u,v,q,y_i>0$, not positivity of any individual type or column mass. ∎

**Theorem 11.3 (Unrestricted profile comparison at every capacity phase).** For every integer $r\ge5$, every finite $s\ge r$ and every profile of Definition 1.1 with $q\in[r-1,r]$,

$$
J_s(x)\ge F_r(q).
$$

Equality holds exactly for $s=r$ and $x=x^*(q)$, up to relabeling. If $s>r$, its common datum satisfies the stronger bound (11.2), in particular

$$
J_s(x)\ge F_r(q)+(r-1)+\frac1{2r}.\tag{11.6}
$$

For arbitrary $q\ge r$, every profile with finite $s\ge r+1$ also satisfies, for each $2\le\beta\le\kappa_r$,

$$
2J_s(x)\ge r^3+\beta(s-r)+(D-\beta)(q-r).
\tag{11.7}
$$

Here $D-\beta>0$; in particular $\beta=2$ gives $J_s(x)\ge r^3/2+1$. The bound (11.7) does not require $q\le r$.

The interval comparison includes every $r\ge11$ and every mean in Definition 8.3, without the support hypothesis of Theorem 4.1 or the upper-density restriction of Theorem 8.1. It extends the comparison and equality statement of Theorem 3.2 to all $r\ge5$. Its domain is $s\ge r$; at $q=r-1$ it does not exclude the separate class $s=r-1$.

**Proof.** If $s>r$, Definition 11.1 transfers the profile to one common datum, and Theorem 11.2 applies. If $s=r$, Theorem 3.1 supplies the inequality and its complete equality class, including both endpoints. This uses the existing fixed-$r$ equality theorem without any hypothesis on low cardinalities.

For (11.7), apply Theorem 2.1 on its unrestricted mean domain. Since $f_r(r)=r^3$,

$$
f_r(q)+\beta(s-q)
=r^3+\beta(s-r)+(D-\beta)(q-r).
$$

The admissible range of $\beta$ is nonempty, since $\kappa_r\ge2$. As proved in Theorem 2.1, $\kappa_r\le2a^2<D$, so the last coefficient is positive. For $s\ge r+1$ and $q\ge r$, taking $\beta=2$ gives the asserted gap above $r^3/2$. ∎

**Theorem 11.4 (Unrestricted finite minimizers on the full capacity interval).** Fix any integer $r\ge5$. Use exactly the constants $C_0,A,K_0,R,B,H$ of Theorem 6.1 and an integer $n_0(r)$ satisfying (6.1), with $\widehat\gamma=1/2$. For every integer $n\ge n_0(r)$ and every integer

$$
L_r(n)\le\ell\le U_r(n),
$$

the graph $H_r(n,\ell)$ is the unique minimizing isomorphism class among all of $\mathcal G(n,\ell)$. With the actual counts $N,c,b_i$ of Definition 5.1, put

$$
\mathfrak E_r(n,\ell)=\min_{G\in\mathcal G(n,\ell)}E(G).
$$

Then

$$
\mathfrak E_r(n,\ell)=\sum_{i=1}^rM_c(N-b_i),\tag{11.8}
$$

and the exact minimum of $\Phi$ is $m+\mathfrak E_r(n,\ell)$. Thus the unrestricted part of Theorem 6.1 extends to every fixed $r\ge5$, with the same sufficient threshold and no minimum-degree assumption.

**Proof.** Theorem 5.2 supplies a simple connected candidate at every integer budget in this closed interval, with $c\ge r$, $b+c=N=n-r$, and $E(H_r)\le C_0/n$. The conditions $n>2r$ and $n>3C_0\ge3r$ ensure its capacity and strict sink orientation. A graph with $E(G)>E(H_r)$ is already worse, so it is enough to consider graphs with $E(G)\le C_0/n$.

The six conditions

$$
n>\max\{1,C_0^2,3C_0,A^3,4AK_0^2,36C_0^2A\}
$$

in (6.1) are precisely the sufficient fixed-cost reduction conditions of [*CDSO sink incidences and density limits*, Theorem 3.1](CDSO_SINK_INCIDENCE_AND_DENSITY_LIMITS.md), at $C=C_0$. Hence every such actual graph is two-layer, has $s\le K_0$ actual sinks, and has $D_i\ge n/(3C_0)$ for every one of them. In particular no actual sink has been discarded. Also $n>4AK_0^2>2K_0$ ensures $N_s=n-s>0$. Capacity from Theorem 5.2, using $n>2r$, forces $s\ge r$. For its actual profile,

$$
q_s=\frac{m}{N_s}\ge q_r=\frac{m}{n-r}
=a+\frac cN>a,\qquad q_r\le r.
$$

These conclusions require no minimum-degree restriction on the sources.

The estimate (6.3) applies to precisely these actual edges: each source has degree at most $s\le K_0$, each actual sink has the stated linear degree bound, and

$$
0\le\frac{J_s(x)}{N_s}-E(G)
\le\frac{N_ss^5}{8(\min_iD_i)^4}
\le\frac R{n^3}.\tag{11.9}
$$

The quadratic edge sum here is exactly $J_s(x)/N_s$ for this graph. The candidate estimate (5.3), with $N\ge n/2$, gives

$$
E(H_r)\le\frac{F_r(q_r)}N+\frac{8B}{n^3}.\tag{11.10}
$$

Suppose $s\ge r+1$. If $q_s\le r$, Theorem 11.3 gives

$$
J_s(x)\ge F_r(q_s)+a+\frac1{2r}
\ge F_r(q_r)+\frac12.
$$

The last comparison uses the monotonicity already established in Theorem 6.1: $F_r'(q)>0$ on $[a,r]$, since $2C-Dr=r(r^2-3r+1)>0$. If instead $q_s\ge r$, apply (11.7) with the legal value $\beta=2$. Since $D-2>0$,

$$
J_s(x)\ge\frac{r^3}{2}+(s-r)+\frac{D-2}{2}(q_s-r)
\ge F_r(q_r)+1.
$$

This second case covers every actual value above $r$, including those arising at the upper capacity endpoint. Neither case substitutes $q_r$ for the graph's own $q_s$ in an interval hypothesis. They supply a common gap $1/2$ for every $r\ge5$, replacing exactly the uses of (3.5)–(3.6) or (4.1)–(4.2) in the restricted-class proof of Theorem 6.1.

Since $F_r(q_r)>0$ and $N_s\le N$, (11.9)–(11.10) now imply

$$
E(G)-E(H_r)
\ge\frac1{2n}-\frac{R+8B}{n^3}
=\frac1{2n}-\frac H{n^3}>0.\tag{11.11}
$$

The last sign is exactly the condition $n>\sqrt{H/\widehat\gamma}=\sqrt{2H}$ in (6.1). Thus every minimizer or tying graph has $s=r$.

For this $r$-sink graph let $A_{\mathrm{low}}$ count sources of degree at most $r-2$. Its mean $q_r$ belongs to $[a,r]$. Theorem 3.1 is valid for all $r\ge5$, and gives

$$
J_r(x)-F_r(q_r)\ge\frac{3aA_{\mathrm{low}}}{N}.
$$

If $A_{\mathrm{low}}\ge1$, the same actual-edge and candidate estimates give

$$
E(G)-E(H_r)\ge\frac{3a}{N^2}-\frac H{n^3}
\ge\frac{3a}{n^2}-\frac H{n^3}>0.\tag{11.12}
$$

The last threshold in (6.1), $n>H/(3a)$, supplies this sign. Thus all sources of any minimizer have degree $a$ or $r$. The vertex and edge budgets force exactly $c$ full sources and a total of $b$ missing-one sources, with $c,b$ as in Definition 5.1. In particular the capacity interval supplies $c\ge r$ without any balance assumption.

For arbitrary missing-one counts $b_i$ in this remaining class,

$$
D_i=N-b_i\ge c\ge r,\qquad
E(G)=\sum_i M_c(D_i).
$$

The exact formula remains valid even if an endpoint degree equals $r$, since the hub degree is at least every incident source degree. The strict convexity (6.7) holds for every $r\ge5$, $c\ge0$ and $z>0$; its proof contains no source minimum-degree assumption. If $D_j\ge D_i+2$, then $b_i\ge b_j+2$, so there is an actual source missing $i$ and adjacent to $j$. Delete its edge to $j$ and add its missing edge to $i$. The resulting counts are $b_i-1,b_j+1$, and the resulting degrees are $D_i+1,D_j-1$. This preserves simplicity, the source's degree, all vertex and edge budgets, and all $c$ full sources. Those unchanged full sources preserve connectedness. Also $D_j-1\ge c$, so the same exact cost formula applies after the move. Strict convexity gives a strict decrease of the sum of the two hub costs.

Iteration terminates with balanced counts: each move decreases the integer sum of the squared hub degrees, and any pair differing by at least two admits such a move. Conversely all balanced count vectors have the same multiset, hence the same cost; permuting hubs and sources identifies their graphs. Every unbalanced vector has a strictly improving legal move. This proves (11.8) and uniqueness up to graph isomorphism. All conditions of (6.1) have thus been used in their original domains: reduction and capacity, the multi-sink gap, or the low-source penalty; no larger threshold is needed. ∎

**Theorem 11.5 (Unrestricted near-minimum structure at every fixed phase).** Fix any integer $r\ge5$ and a prescribed integer sequence $\ell_n$ satisfying

$$
L_r(n)\le\ell_n\le U_r(n)\ \text{eventually},\qquad
\frac{\ell_n}{n}\longrightarrow\alpha\in[r-2,r-1].
$$

Then the unrestricted minima in Theorem 11.4 satisfy

$$
n\mathfrak E_r(n,\ell_n)\longrightarrow F_r(1+\alpha).
\tag{11.13}
$$

For every sequence of simple connected graphs $G_n\in\mathcal G(n,\ell_n)$, the following four conditions are equivalent:

1. $E(G_n)-\mathfrak E_r(n,\ell_n)=o(1/n)$;
2. $nE(G_n)\to F_r(1+\alpha)$;
3. eventually $G_n$ is two-layer with exactly $r$ actual degree-oriented sinks, and, for its actual counts with $N=n-r$ and $q_r=(n-1+\ell_n)/N$,

$$
p_{\mathrm{low}}^{(n)}=\frac1N\sum_{|T|\le r-2}a_T\longrightarrow0,
\qquad
\max_{1\le i\le r}\left|\frac{D_i}{N}-\frac{q_r}{r}\right|
\longrightarrow0;\tag{11.14}
$$

4. eventually $G_n$ has this same $r$-sink two-layer structure and its actual profile obeys

$$
\|x^{(n)}-x^*(q_r)\|_1\longrightarrow0.\tag{11.15}
$$

Labels may be chosen separately at each order. In particular all $r$ hub degrees divided by $n$ tend to $(1+\alpha)/r$. This extends Theorem 7.2 to unrestricted graphs at every fixed $r\ge5$. It allows $o(n)$ low-degree sources and sublinear hub imbalances; it does not assert their finite disappearance or bounded imbalance. The capacity inequalities remain hypotheses at each prescribed integer budget, including both density endpoints.

**Proof.** Theorem 11.4 identifies the exact minimizer at every sufficiently large order of this prescribed sequence. For that balanced candidate, (5.2), the positive linear hub degrees and the actual-edge expansion give

$$
\mathfrak E_r(n,\ell_n)=\frac{F_r(q_r)}{n-r}+O_r(n^{-3}).
\tag{11.16}
$$

Indeed its quadratic error above $F_r(q_r)$ is $O_r(N^{-2})$, and its actual-edge error is $O_r(n^{-3})$. Now $q_r\to1+\alpha$ and $n/(n-r)\to1$, proving (11.13) and the equivalence of 1 and 2.

Assume 1. Then $nE(G_n)\to F_r(1+\alpha)\le r^3/2<C_0$, so $E(G_n)\le C_0/n$ eventually. Apply the actual-graph fixed-cost reduction before making any profile comparison. It gives two-layer structure, a bounded number $s_n\le K_0$ of actual sinks, and $D_i/n\ge1/(3C_0)$ for every actual sink. Capacity gives $s_n\ge r$. These statements include every sink, rather than a selected collection of positive limiting marginals.

If $s_n>r$ along an infinite subsequence, (11.11) applies on that subsequence, and Theorem 11.4 gives

$$
\liminf n\bigl(E(G_n)-\mathfrak E_r(n,\ell_n)\bigr)\ge\frac12,
$$

contradicting 1. The exclusion uses (11.6) when $q_{s_n}\le r$ and the unrestricted certificate (11.7) with $\beta=2$ when $q_{s_n}>r$. Thus it is valid also when $\alpha=r-1$ and the actual means approach $r$ from above. This replaces the only cardinality- or $r$-restricted exclusion step in the necessity proof of Theorem 7.2. Eventually $s_n=r$.

For this actual $r$-sink array put $\delta_n=J_r(x^{(n)})-F_r(q_r)\ge0$. Equations (11.9) and (11.16) imply

$$
\delta_n=N\bigl(E(G_n)-\mathfrak E_r(n,\ell_n)\bigr)
+O_r(n^{-2})\longrightarrow0.
$$

The all-$r$ fixed-sink estimate (3.1) yields (11.14), and (3.2) yields (11.15). Independently of an energy assumption, condition 3 also implies condition 4 by the type identity (3.4). Thus both the low-source mass and marginal balance have their original fixed-$r$ suppliers.

Finally suppose 4. The reference marginals tend to $(1+\alpha)/r>0$, and convergence in $\ell^1$ forces the same limit for every actual marginal. With $r$ fixed, source degrees are bounded by $r$ and hub degrees are bounded below by a positive multiple of $n$. Consequently the actual-edge expansion is valid for this sequence without assuming an energy bound in advance:

$$
nE(G_n)=\frac nN J_r(x^{(n)})+O_r(n^{-2}).
$$

The functional $J_r$ is continuous where every marginal is positive. Since $x^*(q_r)\to x^*(1+\alpha)$, (11.15) implies $J_r(x^{(n)})\to F_r(1+\alpha)$, and hence condition 2. This completes the equivalences in both directions.

For every specified budget sequence in the theorem, Theorem 7.1 applies directly with $s=r$ and the fixed limiting profile $x=x^*(1+\alpha)$. Its marginals are $(1+\alpha)/r>0$, and its required upper bound is exactly

$$
\ell_n\le r(n-r)-n+1=U_r(n).
$$

It therefore realizes the profile with the prescribed integer order and edge budget at every sufficiently large order. Continuity of $x^*(q)$ makes convergence to that fixed limiting profile equivalent to (11.15) for these realized sequences, so they satisfy all four conditions. The exact balanced minimizers themselves already supply such sequences by Theorem 11.4. At $\alpha=r-2$ their full mass tends to zero while their exact full count remains $c\ge r$; at $\alpha=r-1$ missing-one masses may vanish, with $b=0$ giving a complete bipartite graph. Neither necessity, sufficiency nor the prescribed-budget realization requires positive limiting mass for all types. All limits hold for fixed $r$; no estimate uniform in a varying $r$ is asserted. ∎

## 追加锚（本行以下为增补区）

## 12. Eventual exact minimum with one rare hub at the integer endpoint

**Definition 12.1 (The full endpoint array problem).** For each integer $a\ge4$, put $r=a+1$ and $s=a+2$. Let $\mathcal X_a$ consist of all the profiles of Definition 1.1 on $[s]$ with $\mathbb E K=a$. Explicitly, the variables are one mass $x_T\ge0$ for every nonempty $T\subseteq[s]$, subject to

$$
\sum_Tx_T=1,\qquad \sum_T|T|x_T=a,\qquad
y_i=\sum_{T\ni i}x_T>0\quad(i\in[s]).
$$

No support or connectedness restriction is imposed. Define

$$
H(x)=2J_{a+2}(x)
=\mathbb E\left[K^2\sum_{i\in T}y_i^{-2}\right],\qquad
B_0=a(a+1)^2,\qquad d(x)=H(x)-B_0,\qquad
g_a=\frac12\inf_{x\in\mathcal X_a}d(x).
$$

Write

$$
M_a=2a^3+2a^2-2a-1,\qquad N_a=2a^3-2a-1.
$$

Thus $M_a,N_a$ are, respectively, $A_a,E_a$ of Theorem 10.1. On the larger scalar interval $0<t<a$, set

$$
\begin{aligned}
h_a(t)
&=\frac1t+\frac{a^2r^2}{a-t}
 +\frac{(2a+1)(a-1)r^3t}{(a-t)^2},\\
\lambda_a(t)
&=\frac3t-\frac{a(2a+1)r^3t}{(a-t)^2}.
\end{aligned}\tag{12.1}
$$

The quantities $K$, all conditional laws and all marginals below always refer to the same $x\in\mathcal X_a$.

**Lemma 12.2 (The scalar candidate and its unique positive root).** For every integer $a\ge4$, the function $h_a$ is strictly convex on $(0,a)$. Its unique minimizer $\epsilon_a$ belongs to $(0,1/a)$ and is the unique positive real solution of

$$
(a-\epsilon_a)^3
=r^2\epsilon_a^2\bigl[aM_a+N_a\epsilon_a\bigr].
\tag{12.2}
$$

The family of Theorem 10.1, with its parameter set to any $0<t\le1/a$, has energy $h_a(t)$. In particular $h_a(\epsilon_a)$ is an attained upper bound for $\inf_{\mathcal X_a}H$, without presupposing global optimality.

**Proof.** Reuse the array of Theorem 10.1, with its core denoted by $C$ and its remaining label by $e$:

$$
x_{\{e\}}=t,\qquad x_C=(a-1)t,\qquad
x_{C\setminus\{j\}}=\frac{1-at}{r}\quad(j\in C),
\qquad x_T=0\text{ otherwise}.
\tag{12.3}
$$

Its admissibility and energy were computed there. Formula (10.2) gives

$$
h_a(t)-B_0
=\frac1t+\frac{r^2t(M_a-at)}{(a-t)^2}.
\tag{12.4}
$$

The right side agrees with (12.1) by expansion. Thus no new construction is required.

For $U=a^2r^2>0$ and $V=(2a+1)(a-1)r^3>0$, differentiation gives

$$
h_a''(t)
=\frac2{t^3}+\frac{2U}{(a-t)^3}
 +\frac{V(4a+2t)}{(a-t)^4}>0.
$$

Also

$$
h_a'(t)=-\frac1{t^2}
 +\frac{r^2(aM_a+N_at)}{(a-t)^3},\qquad
h_a'(1/a)=\frac{a^3(2a^2+a+4)}{(a-1)^2}>0.
\tag{12.5}
$$

Since $h_a'(t)\to-\infty$ as $t\downarrow0$, strict convexity gives one stationary point in $(0,1/a)$ and makes it the unique minimum on $(0,a)$. Equation (12.5) proves (12.2). Since $M_a,N_a>0$, (12.2) has no positive solution with $\epsilon_a\ge a$; hence this is its unique positive root. The array (12.3) at $\epsilon_a$ supplies the asserted upper bound. ∎

**Lemma 12.3 (Weighted singleton residual and joint certificates).** Let $a\ge7$, $x\in\mathcal X_a$, and choose any label $e$ whose marginal is smallest. Put

$$
\begin{gathered}
t=y_e=\min_i y_i,\qquad C=[s]\setminus\{e\},\qquad
I=\mathbf1_{\{e\in T\}},\qquad
I_i=\mathbf1_{\{i\in T\}}\ (i\in C),\\
L=|T\cap C|=K-I,\qquad
m^2=\mathbb E[K^2\mid I=1],\qquad
\alpha=\mathbb P(T=\{e\}\mid I=1),\qquad \beta=1-\alpha.
\end{gathered}
$$

Here $m\ge1$, $0<t\le a/(a+2)<1$, $y_i\in[t,1]$ on $C$, and $\mathbb E L=a-t$. Define, for $i\in C$,

$$
\begin{aligned}
R_i&=\mathbb E[L^2I_i]-a^2y_i+(2a+1)t,\\
S_i&=R_i-a(2a+1)\alpha t,\\
D_i&=\mathbb E[I(2L+1)I_i],\\
u&=m^2-1-3\beta,\qquad
c=(2a+1)t(a\alpha-1),\qquad
f_c(y)=\frac{a^2}{y}+\frac c{y^2}.
\end{aligned}
$$

Let $\bar y=(a-t)/r$ and let the Jensen difference be

$$
\mathcal G=\sum_{i\in C}f_c(y_i)-r f_c(\bar y).
$$

Then $S_i,D_i,u,\mathcal G\ge0$, and there is the exact identity

$$
H(x)-h_a(t)-\beta\lambda_a(t)
=\frac ut+\mathcal G
 +\sum_{i\in C}\frac{S_i+D_i}{y_i^2}.
\tag{12.6}
$$

Moreover, writing

$$
\begin{gathered}
P_a(k)=(a+2-k)(a+1-k)(2a+k),\\
C_a=a(a+1)(2a+1),\qquad D_a=3a^2+3a+1,\\
\mathcal A_a(t)=\frac{r^2(a^2+3a+1+at)}{(a-t)^2},
\end{gathered}
$$

one has

$$
\begin{aligned}
d(x)
&\ge\frac{m^2}{t}
 +t\bigl(\mathbb E[P_a(K)\mid I=1]-\mathcal A_a(t)\bigr)\\
&\ge\frac{m^2}{t}
 +t\bigl(C_a-D_a(m-1)-\mathcal A_a(t)\bigr).
\end{aligned}\tag{12.7}
$$

For all allowed integer values of $K$, $P_a(K)\ge0$, and $\mathcal A_a(t)=O(a^2)$ uniformly over $a\ge7$, $0<t<1$.

**Proof.** The equality $\mathbb E(a-L)=t$ gives the pointwise residual representation

$$
\begin{aligned}
R_i&=\mathbb E\rho_i,\\
\rho_i
&=(1-I_i)(2a+1)(a-L)
  +I_i(r-L)(r-L-1).
\end{aligned}\tag{12.8}
$$

Indeed the integrand expands as
$L^2I_i-a^2I_i+(2a+1)(a-L)$.
When $I_i=0$, one has $L\le r-1=a$; when $I_i=1$, $r-L$ is a nonnegative integer. Thus $\rho_i\ge0$ in both cases, including $L=0$. On $T=\{e\}$, every $\rho_i$ equals $a(2a+1)$. Since that event has mass $\alpha t$, it follows that

$$
S_i=\mathbb E\bigl[\rho_i\mathbf1_{\{T\ne\{e\}\}}\bigr]\ge0.
\tag{12.9}
$$

Also $D_i\ge0$. Conditionally on $I=1$, the integer $K$ is at least one; on $K\ge2$ its square is at least four. Consequently $m^2\ge1+3\beta$ and $u\ge0$.

The contribution of $e$ to $H$ is $m^2/t$. Using $K^2=L^2+I(2L+1)$ on every core incidence yields the exact equality

$$
H=\frac{m^2}{t}
 +\sum_{i\in C}\left(\frac{a^2}{y_i}+\frac c{y_i^2}\right)
 +\sum_{i\in C}\frac{S_i+D_i}{y_i^2}.
\tag{12.10}
$$

No core type has been removed in this equality. Although $c$ can be negative, on the actual interval $y\ge t$ one has

$$
f_c''(y)
=\frac{2(a^2y+3c)}{y^4}
\ge\frac{2[a^2y-3(2a+1)t]}{y^4}>0.
\tag{12.11}
$$

The last sign follows from $a^2-6a-3>0$ for $a\ge7$. Jensen's inequality applied to the actual $r$ numbers $y_i$ therefore gives $\mathcal G\ge0$, with equality exactly when every $y_i=\bar y$. Here only the scalar function is convex; no convexity or averaging of the array functional $H$ is assumed. Substitute $\alpha=1-\beta$ and $m^2=1+3\beta+u$ into (12.10). The terms with $\beta=0=u$ and $y_i=\bar y$ equal $h_a(t)$, and the coefficient of $\beta$ equals $\lambda_a(t)$. This proves (12.6).

For (12.7), sum (12.8) over $C$. Since $\sum_{i\in C}I_i=L$, the exact sum is

$$
\sum_{i\in C}R_i=\mathbb E Q_a(L),\qquad
Q_a(l)=(r-l)(a-l)(2a+1+l).
\tag{12.12}
$$

For every integer $0\le l\le r$, $Q_a(l)\ge0$. On $I=1$ one has $L=K-1$ and $Q_a(L)=P_a(K)$, so

$$
\sum_{i\in C}R_i
\ge t\,\mathbb E[P_a(K)\mid I=1].
$$

Before removing the singleton contribution, the core contribution in (12.10) can instead be written as

$$
\sum_{i\in C}
 \left(\frac{a^2}{y_i}-\frac{(2a+1)t}{y_i^2}
                  +\frac{R_i+D_i}{y_i^2}\right).
$$

Drop $D_i\ge0$ and use $R_i/y_i^2\ge R_i$, since $0<y_i\le1$. The function
$f_-(y)=a^2/y-(2a+1)t/y^2$
is strictly convex for $y\ge t$ by (12.11) with $c=-(2a+1)t$. Hence

$$
\begin{aligned}
\sum_{i\in C}f_-(y_i)
&\ge\frac{a^2r^2}{a-t}
  -\frac{(2a+1)tr^3}{(a-t)^2}\\
&=B_0-t\mathcal A_a(t).
\end{aligned}
$$

This proves the first inequality of (12.7). The polynomial identity

$$
P_a(k)=C_a-D_a(k-1)+(k-1)^3
\tag{12.13}
$$

and $\mathbb E[K\mid I=1]\le m$ imply the second one, because $K-1\ge0$ under that conditional law. The two consecutive factors $a+2-k,a+1-k$ have nonnegative product for every integer $1\le k\le a+2$, proving $P_a(K)\ge0$. Finally,

$$
0<\mathcal A_a(t)
\le\left(\frac{a+1}{a-1}\right)^2(a^2+4a+1)=O(a^2)
$$

for $0<t<1$ and $a\ge7$. This bound is independent of the array.

The use of Jensen here is the finite convex-combination inequality of S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, §3.1.8, pp. 77–78 ([author-hosted text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf)). Its strict equality condition follows from (12.11). The residuals in (12.8)–(12.10), rather than a symmetrization assumption, supply the link to the common array. ∎

**Lemma 12.4 (Uniform localization of the entire candidate sublevel).** Fix $M>0$. Uniformly over all $x\in\mathcal X_a$ with $d(x)\le Ma^{3/2}$ and every choice of a smallest-marginal label $e$, the notation of Lemma 12.3 satisfies, for all sufficiently large $a$ depending only on $M$,

$$
\frac1M\le\tau:=a^{3/2}t\le M,\qquad
1\le m\le M,\qquad
\frac{d(x)}{a^{3/2}}
\ge\frac{m^2}{\tau}+2\tau-O_M(a^{-1}).
\tag{12.14}
$$

Define the sublevel using the scalar candidate already specified in Lemma 12.2:

$$
\mathcal U_a
=\{x\in\mathcal X_a:H(x)\le h_a(\epsilon_a)+1\}.
\tag{12.15}
$$

There are absolute constants and an integer $a_1\ge7$ such that, for every integer $a\ge a_1$, every $x\in\mathcal U_a$ and every smallest-marginal label $e$,

$$
m^2-1=O(a^{-1}),\qquad
\beta=O(a^{-1}),\qquad
\tau=\frac1{\sqrt2}+O(a^{-1/2}),\qquad
t\lambda_a(t)=2+O(a^{-1/2})>0.
\tag{12.16}
$$

All constants and thresholds are independent of $x$, its support, the sizes of its positive marginals, and the choice among tied smallest marginals.

**Proof.** Put $\Delta=\operatorname{Var}(K)$. As $\mathbb E K=a$,

$$
\mathbb E[(K-a)(K-a-1)]=\Delta.
$$

The integer identity

$$
k^3-D_ak+C_a=(k-a)(k-a-1)(k+2a+1)
$$

implies

$$
\mathbb E K^3-a^3\ge(2a+2)\Delta.
\tag{12.17}
$$

To see the sign without a real-variable support relaxation, subtract
$(2a+2)(k-a)(k-a-1)$
from the identity's right side. The remainder is
$(k-a)(k-a-1)(k-1)\ge0$
for each integer $k\ge1$. Also $aD_a-C_a=a^3$. Since $y_i\le1$, $H\ge\mathbb E K^3$. Thus the assumed sublevel gives

$$
\Delta\le\frac{2a^2+a+Ma^{3/2}}{2a+2}=O_M(a).
\tag{12.18}
$$

We first control $t$ without any rarity assumption. On this same array define

$$
V_T=\sum_{i\in T}(y_i^{-2}-1).
$$

The exact marginal budget is $\sum_i(1-y_i)=s-a=2$. It gives

$$
\begin{aligned}
0\le V_T
&\le\sum_i(y_i^{-2}-1)
 =\sum_i\frac{(1-y_i)(1+y_i)}{y_i^2}
 \le\frac4{t^2},\\
\mathbb E V_T
&=\sum_i\frac1{y_i}-a
 \ge\frac{(a+2)^2}{a}-a=4+\frac4a.
\end{aligned}\tag{12.19}
$$

The last inequality is Cauchy–Schwarz with $\sum_i y_i=a$. As $K\le a+2$,

$$
\mathbb E|K^2-a^2|
\le(2a+2)\mathbb E|K-a|
\le(2a+2)\sqrt\Delta.
$$

Consequently the exact equality $H=\mathbb E K^3+\mathbb E[K^2V_T]$ and (12.17)–(12.19) yield

$$
H\ge a^3+4a^2+4a
 -\frac{8(a+1)\sqrt\Delta}{t^2}.
$$

Compare with $H\le a^3+2a^2+a+Ma^{3/2}$. The denominator below is positive for all sufficiently large $a$ depending only on $M$, and then

$$
t^2\le
\frac{8(a+1)\sqrt\Delta}{2a^2+3a-Ma^{3/2}}
=O_M(a^{-1/2}).
\tag{12.20}
$$

This first gives $t=O_M(a^{-1/4})$ uniformly.

By $P_a(K)\ge0$ and the first inequality in (12.7),

$$
m^2\le t\bigl[d+t\mathcal A_a(t)\bigr]
\le Ma^{3/2}t+O(a^2t^2)=O_M(a^{3/2}).
$$

In particular $m/a=O_M(a^{-1/4})$. Therefore

$$
\kappa=C_a-D_a(m-1)-\mathcal A_a(t)
=2a^3+O_M(a^{11/4})\ge a^3
$$

eventually, uniformly over the entire sublevel. The second inequality in (12.7) improves the estimates to

$$
d\ge\frac{m^2}{t}+a^3t.
\tag{12.21}
$$

Each summand is positive. Since $m\ge1$ and $d\le Ma^{3/2}$, (12.21) gives

$$
\frac1M\le a^{3/2}t\le M,\qquad m^2\le M(a^{3/2}t)\le M^2.
$$

Now return to $\kappa$: the improved bound $m=O_M(1)$ gives
$\kappa=2a^3+O_M(a^2)$.
Substituting this in (12.7), and using $\tau\le M$, proves (12.14).

For (12.16), put $t_0=1/(\sqrt2\,a^{3/2})$. It lies in $(0,1/a]$, and the exact formula (12.4) gives

$$
h_a(\epsilon_a)-B_0
\le h_a(t_0)-B_0
=2\sqrt2\,a^{3/2}+O(a^{1/2}).
\tag{12.22}
$$

For example, this follows directly from
$r^2M_a/a^2=2a^3+O(a^2)$ and
$t_0/a=O(a^{-5/2})$
in that formula. Thus every $x\in\mathcal U_a$ satisfies $d\le4a^{3/2}$ for all sufficiently large $a$, with a threshold independent of $x$. Apply (12.14) with the fixed constant $M=4$. After comparison with (12.22), it gives

$$
\frac{m^2-1}{\tau}
+\left(\frac1\tau+2\tau-2\sqrt2\right)
\le O(a^{-1}),\qquad \frac14\le\tau\le4.
\tag{12.23}
$$

Both terms on the left are nonnegative, and

$$
\frac1\tau+2\tau-2\sqrt2
=\frac{2(\tau-1/\sqrt2)^2}{\tau}.
$$

It follows uniformly that $m^2-1=O(a^{-1})$ and
$\tau=1/\sqrt2+O(a^{-1/2})$.
Since $3\beta\le m^2-1$, the asserted estimate for $\beta$ follows as well. Finally (12.1) gives

$$
t\lambda_a(t)
=3-\frac{(2a+1)r^3}{a^2(a-t)^2}\tau^2
=2+O(a^{-1/2}),
$$

because the coefficient of $\tau^2$ is $2+O(a^{-1})$. This is strictly positive eventually.

All bounds were obtained with constants depending only on the initially fixed $M$, followed by the single choice $M=4$. Hence one integer $a_1$ works simultaneously for every array in (12.15) and every least marginal. The sublevel's definition used only the feasible scalar candidate, not an assumed global minimum. ∎

**Theorem 12.5 (Eventual exact global minimum and all equality arrays).** There exists an integer $a_0\ge7$ such that, for every integer $a\ge a_0$ and every $x\in\mathcal X_a$,

$$
H(x)\ge h_a(\epsilon_a).
\tag{12.24}
$$

Equality holds if and only if, for some label $e$ and $C=[a+2]\setminus\{e\}$,

$$
x_{\{e\}}=\epsilon_a,\qquad
x_C=(a-1)\epsilon_a,\qquad
x_{C\setminus\{j\}}=\frac{1-a\epsilon_a}{a+1}\quad(j\in C),
\qquad x_T=0\text{ otherwise}.
\tag{12.25}
$$

Here $\epsilon_a$ is the unique positive root in Lemma 12.2. In each equality array, $e$ is the unique label of smallest marginal. Thus there is precisely one minimizing array up to relabeling, and

$$
g_a=\frac1{2\epsilon_a}
 +\frac{r^2\epsilon_a(M_a-a\epsilon_a)}
        {2(a-\epsilon_a)^2}.
\tag{12.26}
$$

This determines the eventual minimum within the unrestricted array class $q=a$, $s=a+2$. It strengthens the upper-bound and scale statements of Theorem 10.1 on precisely this scope. No explicit or smallest $a_0$ is specified, and no classification for $4\le a<a_0$, other values of $q,s$, or exact finite graph budgets is asserted.

**Proof.** Choose $a_0$ large enough for all the uniform conclusions of Lemma 12.4 on $\mathcal U_a$ to hold, in particular $\lambda_a(t)>0$ for every least-marginal choice. If $x\notin\mathcal U_a$, then $H(x)>h_a(\epsilon_a)+1$, so (12.24) holds strictly. If $x\in\mathcal U_a$, choose any least-marginal label and apply (12.6):

$$
H(x)\ge h_a(t)+\beta\lambda_a(t)\ge h_a(\epsilon_a).
$$

The last step uses $\beta\ge0$, $\lambda_a(t)>0$, and the scalar minimum on the whole interval $(0,a)$. Thus the bound holds for all arrays, with the single threshold $a_0$ independent of the array. The feasible family in Lemma 12.2 attains it.

Suppose equality holds. The exact nonnegative difference (12.6) gives

$$
\begin{aligned}
0={}&h_a(t)-h_a(\epsilon_a)+\beta\lambda_a(t)
 +\frac ut+\mathcal G
 +\sum_{i\in C}\frac{S_i+D_i}{y_i^2}.
\end{aligned}
$$

Every summand is nonnegative. Strict scalar convexity forces $t=\epsilon_a$, and the strictly positive coefficient of $\beta$ forces $\beta=0$. The latter statement is exact: $e$ occurs only in the type $\{e\}$. Equality $\mathcal G=0$ forces $y_i=(a-t)/r$ for every core label; also every $S_i=D_i=0$.

Sum (12.9) over $i\in C$. On the remaining events $I=0$, one has $L=K\ge1$, so (12.12) gives

$$
0=\mathbb E\bigl[Q_a(L)\mathbf1_{\{T\ne\{e\}\}}\bigr].
$$

For integer $1\le l\le r$, $Q_a(l)>0$ when $1\le l\le a-1$, and its only zeros are $l=a,r$. Therefore the remaining positive masses are confined to $C$ and the types $C\setminus\{j\}$. This finite support conclusion follows from zero nonnegative residuals, rather than from a limit of $\beta$.

Let $z=x_C$ and $b_j=x_{C\setminus\{j\}}$. Normalization and the mean condition give

$$
z+\sum_jb_j=1-t,\qquad rz+a\sum_jb_j=a-t,
$$

hence $z=(a-1)t$ and $\sum_jb_j=1-at$. Each core marginal satisfies
$y_i=1-t-b_i=(a-t)/r$,
which forces $b_i=(1-at)/r$ for every $i$. This is exactly (12.25). Conversely, Lemma 12.2 shows that (12.25) attains equality.

Finally $\epsilon_a<1/a<a/(a+2)$ implies
$\epsilon_a<(a-\epsilon_a)/r$,
so $e$ is the unique smallest-marginal label. Formula (12.26) follows from (12.4). All types, including zero masses, were admitted throughout the argument; no positive marginal was discarded. In particular the disconnected support of (12.25) is allowed by Definition 12.1. ∎

**Theorem 12.6 (Subleading value and controlled expansion).** As $a\to\infty$ through integers, the exact minimum of Theorem 12.5 satisfies

$$
g_a=\sqrt2\,a^{3/2}+\frac3{\sqrt2}a^{1/2}
 -\frac1{4\sqrt2}a^{-1/2}
 +\frac1a+O(a^{-3/2}),
\tag{12.27}
$$

and its parameter satisfies

$$
\epsilon_a
=\frac1{\sqrt2\,a^{3/2}}
 \left(1-\frac3{2a}+O(a^{-2})\right).
\tag{12.28}
$$

**Proof.** Define

$$
\begin{aligned}
b_a&=\frac{r^2M_a}{a^2}
 =2a^3+6a^2+4a-3-\frac4a-\frac1{a^2},\\
t_b&=b_a^{-1/2},\\
W_a(t)&=
\frac{r^2t^2(2aM_a-a^3-M_at)}{a^2(a-t)^2}.
\end{aligned}
$$

An exact rearrangement of (12.4) is

$$
h_a(t)-B_0=\frac1t+b_at+W_a(t).
\tag{12.29}
$$

The stationary equation (12.2) is equivalently the clean positive-factor identity

$$
\epsilon_a^{-2}
=b_a\left(1+\frac{N_a}{M_a}\frac{\epsilon_a}{a}\right)
       \left(1-\frac{\epsilon_a}{a}\right)^{-3}.
\tag{12.30}
$$

Since both factors on the right after $b_a$ are at least one, $\epsilon_a\le t_b$. In particular $\epsilon_a/a=O(a^{-5/2})$, while $0<N_a/M_a<1$. For $0\le z\le1/2$, the derivative of $(1-z)^{-3}$ is bounded by an absolute constant. Applying this to (12.30) gives

$$
\epsilon_a^{-2}=b_a\bigl(1+O(a^{-5/2})\bigr),\qquad
\epsilon_a=t_b+O(a^{-4}).
\tag{12.31}
$$

These bounds also show $\epsilon_a\asymp t_b\asymp a^{-3/2}$.

For completeness, an explicit uniform remainder for $W_a$ follows from its rational expression. Put

$$
c_{2,a}=r^2\left(\frac{2M_a}{a^3}-\frac1a\right)
=4a^2+11a+6-\frac7a-\frac8{a^2}-\frac2{a^3}.
$$

Writing $A=2aM_a-a^3$, one has

$$
W_a(t)=\frac{r^2t^2}{a^4}(A-M_at)(1-t/a)^{-2}.
$$

On any interval $0<t\le Ca^{-3/2}$ with $C$ fixed, the bound
$|(1-z)^{-2}-1|\le C' z$ for $0\le z\le1/2$ gives

$$
W_a(t)=c_{2,a}t^2+O_C(at^3).
\tag{12.32}
$$

Indeed $r^2/a^4=O(a^{-2})$, $A=O(a^4)$ and $M_a=O(a^3)$, so both remaining terms are bounded by a constant times $at^3$. Thus this error estimate is uniform on an interval containing both $\epsilon_a$ and $t_b$ for all sufficiently large $a$.

There is also the exact scalar identity

$$
\frac1{\epsilon_a}+b_a\epsilon_a-2\sqrt{b_a}
=\frac{b_a(\epsilon_a-t_b)^2}{\epsilon_a}.
$$

By (12.31) its right side is $O(a^{-7/2})$. Since
$c_{2,a}=O(a^2)$, (12.31)–(12.32) similarly imply

$$
\begin{aligned}
W_a(\epsilon_a)
&=\frac{c_{2,a}}{b_a}+O(a^{-7/2}),\\
g_a
&=\sqrt{b_a}+\frac{c_{2,a}}{2b_a}+O(a^{-7/2})
 =\sqrt{b_a}+\frac1a+O(a^{-2}).
\end{aligned}\tag{12.33}
$$

For the first line, the replacement of $\epsilon_a^2$ by $t_b^2$ costs
$O(a^2\cdot a^{-3/2}\cdot a^{-4})=O(a^{-7/2})$;
the remainder $a\epsilon_a^3$ has the same order. For the last line,
$c_{2,a}=4a^2+O(a)$ and $b_a=2a^3+O(a^2)$ give
$c_{2,a}/(2b_a)=1/a+O(a^{-2})$.

Finally

$$
\frac{b_a}{2a^3}
=1+\frac3a+\frac2{a^2}+O(a^{-3}).
$$

The Taylor formulas for $(1+z)^{1/2}$ through degree two and for $(1+z)^{-1/2}$ through degree one have uniformly bounded next derivatives on $|z|\le1/2$. They therefore give, with controlled remainders,

$$
\begin{aligned}
\sqrt{b_a}
&=\sqrt2\,a^{3/2}
 \left(1+\frac3{2a}-\frac1{8a^2}+O(a^{-3})\right),\\
t_b
&=\frac1{\sqrt2\,a^{3/2}}
 \left(1-\frac3{2a}+O(a^{-2})\right).
\end{aligned}
$$

Substitution into (12.31) and (12.33) proves (12.27)–(12.28). In (12.28) the additional $O(a^{-4})$ is smaller than the displayed absolute remainder $O(a^{-7/2})$. ∎

Theorem 10.1 is the source of the upper family and its exact energy; Jensen and Cauchy–Schwarz are classical intermediate inequalities. The weighted residual, uniform sublevel comparison, equality classification and expansion above are repo-derived mathematical deductions in the domain of Definition 12.1. Their relation to K. Zhao and X. Zhao, DOI [10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26), is undetermined without that paper's full text; no literature-priority assertion is made. The threshold's least value and the minimum for the remaining finite range $4\le a<a_0$ are not determined here. The array theorem supplies no exact realization or optimality assertion at a prescribed finite graph budget.

## 追加锚（本行以下为增补区）
