# CDSO mesoscopic exact common laws

## 1. The mesoscopic sublevel and a moving contact

**Definition 1.1 (Original laws and mesoscopic sequences).** Retain
exactly the domain $\mathcal X(a,h)$, actual marginals $y_i$, energy
$H$, and infimum $M(a,h)$ of [*CDSO growing surplus hubs*,
Definition 1.1](CDSO_GROWING_SURPLUS_HUBS.md), abbreviated Growing.
Thus $a\ge4$ and $h\ge1$ are integers, $s=a+1+h$, and one probability
law on all nonempty subsets of $[s]$ satisfies

$$
\mathbb E|T|=a,\qquad y_i=\mathbb P(i\in T)>0,\qquad
H=\mathbb E\left[|T|^2\sum_{i\in T}y_i^{-2}\right].
\tag{1.1}
$$

No restriction is placed on cardinalities, vanishing type masses,
the size of positive marginals, or connectedness of the incidence
support. Put

$$
S_j=\frac{(a+j)^3(a+j-1)}{a-1}
       +\frac{(h+1-j)^2(a+j-1)}j,\qquad
U(a,h)=\min_{1\le j\le h}S_j.
\tag{1.2}
$$

The actual cap laws in Growing, Theorem 3.1, show $M\le U$.
A mesoscopic sequence means any sequence of these integer pairs with

$$
a\longrightarrow\infty,\qquad h/\sqrt a\longrightarrow\infty,
\qquad h/a^{3/2}\longrightarrow0.
\tag{1.3}
$$

All sequential estimates below hold for every sequence (1.3).
When laws are also chosen, they hold for every choice of actual laws
with $H\le U$. In particular, no minimizing law is presumed to exist.
Constants in $O(\cdot)$ are absolute; the index after which an estimate
applies may depend on the sequence. Little-oh estimates are uniform
over the chosen laws, in the sequential sense just specified.

**Lemma 1.2 (An $o(a^2)$ contact gap).** On any sequence (1.3), choose
any index $j_0$ attaining the finite minimum in (1.2), and put

$$
m_0=a+j_0,\quad r_0=m_0-1,\quad n_0=h+1-j_0,\quad
p_0^{\mathrm{ref}}=j_0/r_0,\quad
q_0^{\mathrm{ref}}=(a-1)/r_0.
\tag{1.4}
$$

Then

$$
j_0\sim\frac{h}{2\sqrt a},\qquad j_0\longrightarrow\infty,
\qquad j_0/a\longrightarrow0,\qquad
U=a^3+(8+o(1))a^2j_0.
\tag{1.5}
$$

Use the moving-contact polynomial of Growing, (8.8), namely

$$
\begin{gathered}
b(c)=4c(c-1)\sqrt{c+1}-2c^2+4c,\\
L_c=5c^4-2b(c)c,\quad N_c=4c^5-b(c)c^2,\\
W_c(k,v)=kv^2-L_ck-b(c)v+N_c,\\
G_c(a,s)=\{aL_c+ab(c)s-N_c\}/a^2.
\end{gathered}
\tag{1.6}
$$

For the real contact $c=m_0$, set $R=U-G_{m_0}(a,s)$. One has

$$
0\le R\le C\left(aj_0+\frac{a^2}{j_0}\right)=o(a^2).
\tag{1.7}
$$

Every original law with $H\le U$ therefore satisfies

$$
0\le \mathcal D(x)+a^{-2}\mathbb E W_{m_0}(K,aU_T)\le R,
\tag{1.8}
$$

where $K=|T|$, $U_T=\sum_{i\in T}y_i^{-1}$, and
$\mathcal D=\mathbb E[K\sum_{i<l,\ i,l\in T}
(y_i^{-1}-y_l^{-1})^2]\ge0$.

**Proof.** The construction and expansion in Growing, Theorem 8.2,
give the comparison
$U\le a^3+(4+o(1))a^{3/2}h$. The polynomial remainder displayed in
Growing, (8.4), has positive coefficients for every $j\ge1$ and
$a\ge4$, so its identity implies $S_j\ge a^3+4a^2j$ for all these
indices; its restricted asymptotic remainder estimate is not needed
for this step. Hence
$j_0=O(h/\sqrt a)=o(a)$ and $n_0/h\to1$.
The tail term, which is at least $an_0^2/j_0$, also implies
$j_0\ge c h/\sqrt a$. These two bounds give, uniformly for the
surviving indices, with $z=j_0\sqrt a/h$,

$$
\frac{S_{j_0}-a^3}{a^{3/2}h}=4z+z^{-1}+o(1).
\tag{1.9}
$$

Here $z$ stays in a fixed compact subset of $(0,\infty)$.
The function $4z+z^{-1}$ has its unique minimum $4$ at $z=1/2$.
The comparison forces $z\to1/2$, proving (1.5).
In particular, $1<j_0<h$ eventually.

Continue the formula $S_j$ to a real variable $z>0$, writing
$t=h+1$ and $m=a+z$. Its tail term equals

$$
\frac{(t-z)^2(a+z-1)}z
=\frac{(a-1)t^2}z-2(a-1)t+(a-1)z+t^2-2tz+z^2.
\tag{1.10}
$$

On $[j_0-1,j_0+1]$ this gives

$$
S''(z)=\frac{12(a+z)^2-6(a+z)}{a-1}
       +\frac{2(a-1)t^2}{z^3}+2
=O(a^2/j_0).
\tag{1.11}
$$

Since $S(j_0)\le S(j_0\pm1)$, Taylor's theorem gives
$|S'(j_0)|\le C a^2/j_0$. With $w=n_0/j_0$ the exact derivative is

$$
S'(j_0)=\frac{4m_0^3-3m_0^2}{a-1}
               -(a-1)w^2-2r_0w.
\tag{1.12}
$$

Since $w\sim2\sqrt a$, subtraction and factorization of two squares
in (1.12) give

$$
\left|w-\frac{2m_0^{3/2}}{a-1}\right|
\le C\left(1+\frac{\sqrt a}{j_0}\right).
\tag{1.13}
$$

Indeed the difference of the squares, before division by their sum,
is $O(\sqrt a+a/j_0)$, and that sum is bounded below by $c\sqrt a$.
Moreover $ar_0/(a-1)-m_0=j_0/(a-1)$ and
$b(m_0)/2=2m_0^{5/2}+O(a^2)$. Thus

$$
\left|ar_0w-b(m_0)/2\right|
\le C\left(a^2+\frac{a^{5/2}}{j_0}\right).
\tag{1.14}
$$

Evaluate the exact residual identity Growing, (8.11), on its cap
law of index $j_0$. Its $\mathcal D$ is zero. On the core event
$K=m_0$ and

$$
aU_T=m_0^2+v_0,\qquad v_0=\frac{m_0j_0}{a-1}=O(j_0).
$$

Since $W_{m_0}(m_0,m_0^2)=0$, the core residual is

$$
a^{-2}q_0^{\mathrm{ref}}
 \{(2m_0^3-b(m_0))v_0+m_0v_0^2\}=O(aj_0).
\tag{1.15}
$$

At a tail singleton the reciprocal is $r_0n_0/j_0=r_0w$.
Growing, (10.6), and (1.14) bound its total residual by

$$
\frac{p_0^{\mathrm{ref}}}{a^2}
       (ar_0w-b(m_0)/2)^2
\le C\left(aj_0+\frac{a^2}{j_0}\right).
\tag{1.16}
$$

The contact inequality in Growing, (8.10), proves nonnegativity.
Equations (1.15)--(1.16) prove (1.7), and its exact residual identity
for an arbitrary law proves (1.8). No uniformity assertion from
Growing, Theorem 8.4, at a positive fixed transition ratio is used. ∎

## 2. Localization on the entire original sublevel

**Lemma 2.1 (Growing core index and a bounded reciprocal-square
defect).** For every sequence (1.3) and every choice of laws with
$H\le U$, define the partition from their actual marginals by

$$
C=\{i:y_i>1/4\},\qquad D=[s]\setminus C.
\tag{2.1}
$$

Eventually there are integers $j\ge1$, $m=a+j$, $r=m-1$ and
$n=h+1-j$ with $|C|=m$, $|D|=n>0$. Write

$$
\begin{gathered}
u=\sum_{k\in D}y_k,\quad \delta=\max_{k\in D}y_k,
\quad c=\min_{i\in C}y_i,\quad q=(a-1)/r,\\
A=\{T\cap D\ne\varnothing\},\quad p=\mathbb P(A),
\quad e=\mathbb E[K;A].
\end{gathered}
\tag{2.2}
$$

Then, with $j_0$ as in Lemma 1.2,

$$
\begin{gathered}
c\longrightarrow1,\quad a\delta\longrightarrow0,\quad
u\longrightarrow0,\quad e\longrightarrow0,\\
j/j_0\longrightarrow1,\quad ap/j_0\longrightarrow1,\quad
\frac{n}{j\sqrt a}\longrightarrow2,\\
\sum_{i\in C}(y_i-(a-u)/m)^2=o(1),\qquad
\sum_{i\in C}y_i^{-2}=\frac m{q^2}+o(1).
\end{gathered}
\tag{2.3}
$$

**Proof.** Set $d_0=j_0/a+1/j_0=o(1)$ and use $R$ from Lemma 1.2.
Thus $R\le C a^2d_0$. Let

$$
\mathcal B=\{a/2\le K\le2a\},\qquad
\mathcal E=\{K\ge2\}\setminus\mathcal B.
$$

The pointwise estimate Growing, (10.5), applies at $m_0\sim a$.
Together with (1.8) it gives

$$
\mathbb E[(K-m_0)^2;K\ge2]\le C R/a,\quad
\mathbb P(\mathcal E)\le C R/a^3=o(a^{-1}),\quad
\mathbb E[K;\mathcal E]\le C R/a^2=O(d_0).
\tag{2.4}
$$

For the last bound, on $2\le K<a/2$ use
$K\le a/2$ and the probability bound; on $K>2a$ use
$K\le C(K-m_0)^2/a$. At singletons the exact square in Growing,
(10.6), yields, with $\eta_0=b(m_0)/(2a)\sim2a^{3/2}$,

$$
\sum_i x_{\{i\}}(y_i^{-1}-\eta_0)^2\le R.
\tag{2.5}
$$

Writing $P_1=\mathbb P(K=1)$, the mean identity and Cauchy give

$$
(m_0-1)P_1
=j_0+\mathbb E[K-m_0;K\ge2]
\le j_0+C\sqrt{R/a}.
\tag{2.6}
$$

Consequently $P_1\to0$, and (2.4) implies
$\mathbb P(\mathcal B)\to1$.

There is a second, distinct consequence of the same contact residual.
On $\mathcal B$, the derivative of $W_{m_0}(k,v)$ at $v=k^2$ is
$2k^3-b(m_0)\ge c_1 a^3$ eventually. Since $aU_T\ge K^2$,
nonnegativity of the boundary value gives

$$
\mathbb E[U_T-K^2/a;\mathcal B]\le C R/a^2\le C d_0.
\tag{2.7}
$$

Use the exact shared-budget identity, with $I_i=\mathbf1_{i\in T}$,

$$
U_T-K^2/a=\sum_{i=1}^s
              y_i(I_i/y_i-K/a)^2.
\tag{2.8}
$$

It follows by expansion from $\sum_i y_i=a$ and $\sum_iI_i=K$.
Put $z_i=\mathbb P(i\in T,\mathcal B)$.
For $y_i\le1/4$, an inclusion on $\mathcal B$ contributes at least
$1/(4y_i)$ to (2.8). Hence

$$
\sum_{i:y_i\le1/4}z_i/y_i\le C d_0.
\tag{2.9}
$$

For $y_i>1/4$, an omission on $\mathcal B$ contributes at least
$y_i/4\ge1/16$. Thus, uniformly for these labels,

$$
\mathbb P(\mathcal B,i\notin T)\le C d_0,
\qquad y_i\ge\mathbb P(\mathcal B)-C d_0=1-o(1).
\tag{2.10}
$$

Every small marginal is $o(a^{-1})$, uniformly over its labels.
To see this, if along a subsequence a small marginal $y_i$ were at
least $b/a$ for some fixed $b>0$, then (2.4) and (2.9) would imply

$$
x_{\{i\}}\ge(1-Cd_0)y_i-\mathbb P(\mathcal E)
\ge y_i/2.
$$

But $y_i^{-1}\le a/b=o(\eta_0)$, so its summand in (2.5) would be
at least $c_2 y_i a^3\ge c_2 b a^2$, contradicting $R=o(a^2)$.
This proves $a\delta\to0$ whenever small labels exist.

Their total marginal mass satisfies

$$
u\le P_1+\mathbb E[K;\mathcal E]+\sum_{i\in D}z_i
\le P_1+O(d_0)+C\delta d_0=o(1).
\tag{2.11}
$$

The inequality also holds when $D$ is empty. Thus $C$ is nonempty
eventually, and $c\to1$ by (2.10). If $m=|C|$, then
$a=m-\sum_{i\in C}(1-y_i)+u$, so $m-a$ is an integer greater than
$-1$ eventually.

For an upper bound on this integer, first note
$H\ge\mathbb E K^3\ge a^3$ and

$$
H-\mathbb E K^3
=\sum_i\mathbb E[K^2I_i](y_i^{-2}-1)
\le U-a^3=O(a^2j_0).
\tag{2.12}
$$

On $\mathcal B$, $K^2\ge a^2/4$, and (2.10) gives $z_i\ge1/2$
for every core label eventually. Since $y^{-2}-1\ge2(1-y)$,
(2.12) implies

$$
\sum_{i\in C}(1-y_i)=O(j_0),\qquad
0\le j:=m-a\le Cj_0.
\tag{2.13}
$$

In particular $j=o(a)$, $n=s-m=h+1-j\sim h>0$, so the maxima
and event in (2.2) are now defined. Every marginal on $D$ is positive,
hence $p>0$. On $\mathcal B$,

$$
\mathbb E[K;A,\mathcal B]
\le2a\,\mathbb P(A,\mathcal B)
\le2a\sum_{i\in D}z_i\le C a\delta d_0=o(1).
$$

Equations (2.4), (2.6) therefore give $e=o(1)$.
Let $H_D$ be the part of $H$ summed over labels in $D$.
Equation (2.12) gives

$$
H_D\le\frac{U-a^3}{1-\delta^2}\le C a^2j_0.
\tag{2.14}
$$

The actual identity
$\mathbb E[\sum_{i\in T\cap D}y_i^{-1}]=n$ and Cauchy, exactly
as in Growing, (7.15), give $H_D\ge n^2/p$. Thus
$p\ge c_3j_0/a$. Since $K\le m$ on $A^c$, the original mean gives
$mp\le j+e$. Consequently

$$
c_4j_0\le j\le Cj_0,\qquad
c_3j_0/a\le p\le Cj_0/a.
\tag{2.15}
$$

These bounds in particular exclude $j=0$.

To identify these quantities sharply, condition the same law on
$A^c$. Put $\pi=1-p$, $r_i=\mathbb P(i\in T,A)$ and
$y_i^0=(y_i-r_i)/\pi$. This conditional core law has mean
$q^0=(a-e)/\pi$ and deficit

$$
d^0=m-q^0=(j+e-mp)/\pi\ge0,\qquad d^0=O(j_0).
$$

Its marginals are at least $1/2$ eventually. Apply the elementary
conditional-core bound Growing, (7.16), with this deficit:
$H^0\ge m^2q^0-O(aj_0^2)$. Comparing the actual and conditional
denominators as in Growing, (7.19), uses
$\sum_{i\in C}r_i\le e$ and the bounded derivative of $y^{-2}$
on $[1/2,1]$. It gives for $H_C=H-H_D$

$$
\begin{aligned}
H_C&\ge\frac{m^2(a-e)}{(1-p)^2}
                   -O(aj_0^2+a^2e)\\
&\ge a^3+2a^2j+2a^3p-o(a^2j_0).
\end{aligned}
\tag{2.16}
$$

The error is small because $j_0=o(a)$, $j_0\to\infty$, and $e=o(1)$.
For $z=j/j_0$ and $v=ap/j_0$, (2.15), the capacity inequality and
$n\sim h\sim2j_0\sqrt a$ imply

$$
v\le z+o(1),\qquad
2z+2v+4/v\le8+o(1).
\tag{2.17}
$$

Both variables stay bounded above and away from zero.
Since $4v+4/v\ge8$, with equality only at $v=1$, (2.17) forces
$v\to1$ and $z\to1$. This proves the index, probability and tail-count
limits in (2.3).

It remains to control the reciprocal-square sum, rather than only
the smallest core marginal. On every core inclusion, use
$(x+y)^2\le2x^2+2y^2$ with $x=y_i^{-1}-K/a$ and
$y=(K-m_0)/a$. Summing its expectations over $\mathcal B$, (2.4),
(2.7), (2.8), and $\sum_{i\in C}y_i\le a$ yield

$$
\sum_{i\in C}z_i y_i(y_i^{-1}-m_0/a)^2\le C d_0.
\tag{2.18}
$$

Here every $z_i\ge1/2$, every $y_i\ge1/2$, and $m_0/a\to1$.
It follows that $\sum_{i\in C}(y_i-a/m_0)^2\le C d_0$.
The arithmetic mean minimizes the sum of squared deviations, so
$\sum_{i\in C}(y_i-\bar y)^2=o(1)$ for $\bar y=(a-u)/m$.
Taylor's theorem for $y^{-2}$ on $[1/2,1]$ then gives

$$
\sum_{i\in C}y_i^{-2}=m/\bar y^2+o(1).
$$

Finally, $\bar y-q=(j/r-u)/m$; both $j/r$ and $u$ tend to zero.
The bounded derivative gives $m/\bar y^2-m/q^2=o(1)$.
This proves the final assertion and all of (2.3). ∎

## 3. A strict certificate with a growing core

**Lemma 3.1 (Reciprocal-square payment to the cap).** Consider any
sequence of original laws with a partition $C\dot\cup D=[s]$ and
notation as in (2.2). Suppose

$$
\begin{gathered}
|C|=m=a+j,\quad |D|=n>0,\quad j\to\infty,\quad j/a\to0,
\quad n/(j\sqrt a)\to2,\\
c\to1,\quad a\delta\to0,\quad u\to0,\quad
Z_C:=\sum_{i\in C}y_i^{-2}=m/q^2+o(1),\qquad q=(a-1)/(m-1).
\end{gathered}
\tag{3.1}
$$

Eventually every one of these laws satisfies $H\ge S_j$.
Equality holds exactly for the full-core cap law on this partition:

$$
x_C=\frac{a-1}{a+j-1},\qquad
x_{\{k\}}=\frac{j}{(a+j-1)n}\quad(k\in D),
\qquad x_T=0\ \text{otherwise}.
\tag{3.2}
$$

More precisely, the proof gives a nonnegative singleton square and
a lower bound $a^3/8$ for every other realized type meeting $D$.

**Proof.** Put $r=m-1$, $d=2m-1$, $p_0=j/r$, and
$\eta=rn/j=n/p_0$. Write $L=|T\cap C|$, $B=|T\cap D|$, and
$K=L+B$. The adjacent-core incidence identity in Growing,
(15.12), is valid with this growing integer $j$: for $i\in C$ let

$$
\rho_i=(1-I_i)d(r-L)+I_i(m-L)(m-L-1)\ge0.
$$

The nonnegativity uses consecutive integrality when $I_i=1$ and
$L\le r$ when $I_i=0$. Expansion and $\mathbb EL=a-u$ give

$$
\mathbb E\rho_i=\mathbb E[L^2I_i]-r^2y_i+d(j-1+u).
\tag{3.3}
$$

Set

$$
\begin{gathered}
b_j(w)=d((m-2)w-(j-1)),\\
J(w)=\frac{r^2m^2}{a-w}+\frac{m^3b_j(w)}{(a-w)^2},\\
\theta=rd Z_C,\qquad \psi=d Z_C+r^2/c^2.
\end{gathered}
\tag{3.4}
$$

For $i\in C$, subtract $rdB$ from $\rho_i$. Summing with the actual
weights gives the exact identity on $A=\{B>0\}$

$$
\sum_{i\in C}\frac{rdB-\rho_i}{y_i^2}
=\{rd(B-1)+dL\}Z_C
       +(r^2-L^2)\sum_{i\in T\cap C}y_i^{-2}.
\tag{3.5}
$$

Whether or not $r^2-L^2$ is positive, its last term is at most
$r^2L/c^2$. Thus (3.5) is at most $\theta(B-1)+\psi L$.
Off $A$ every $\rho_i$ is nonnegative. Also $K^2\ge L^2$.
Using (3.3) in the original core energy consequently gives

$$
H\ge H_D+\sum_{i\in C}
       \{r^2/y_i+b_j(u)/y_i^2\}
       -\mathbb E[\theta(B-1)+\psi L;A].
\tag{3.6}
$$

The scalar function $f_u(y)=r^2/y+b_j(u)/y^2$ has

$$
f_u''(y)=2\{r^2y+3b_j(u)\}/y^4>0
\qquad(c\le y\le1)
\tag{3.7}
$$

eventually: $c\to1$ and $b_j(u)\ge-d(j-1)=-o(a^2)$.
Finite Jensen with the actual mean $(a-u)/m$ bounds the sum in
(3.6) below by $J(u)$.

The function $J$ is strictly convex on the interval joining $u$
and $p_0$ eventually. Direct differentiation gives

$$
J''(w)=\frac{2r^2m^2}{(a-w)^3}
 +\frac{4m^3d(m-2)}{(a-w)^3}
 +\frac{6m^3b_j(w)}{(a-w)^4}
=(8+o(1))a^2>0
\tag{3.8}
$$

uniformly there, since $u,p_0=o(1)$ and $j=o(a)$.
At its contact,

$$
J(p_0)=\frac{m^3r}{a-1},\qquad
J'(p_0)=\frac{2mr^2+d}{q^2}=(2+o(1))a^3.
\tag{3.9}
$$

Meanwhile $\eta^2=(4+o(1))a^3$. Put $P=\eta^2-J'(p_0)>0$.
For a type meeting $D$ define

$$
\begin{gathered}
V_T=\sum_{k\in T\cap D}y_k^{-1},\qquad
Z_T=K^2\sum_{k\in T\cap D}y_k^{-2},\\
\mathcal G_T=Z_T-2\eta V_T+\eta^2B
 -(\theta+mP/r)(B-1)-(\psi+P/r)L.
\end{gathered}
\tag{3.10}
$$

The actual identities $\mathbb EV_T=n$ and $\mathbb EB=u$ imply

$$
H_D=2\eta n-\eta^2u
       +\mathbb E[Z_T-2\eta V_T+\eta^2B;A].
\tag{3.11}
$$

The original mean and $K\le m$ off $A$ give

$$
ru-j\le\mathbb E[m(B-1)+L;A].
\tag{3.12}
$$

Combine (3.6), Jensen, the supporting tangent of $J$ at $p_0$,
(3.11), and (3.12). Since $P>0$ and $\eta p_0=n$, this gives

$$
H\ge J(p_0)+n^2/p_0+\mathbb E[\mathcal G_T;A]
=S_j+\mathbb E[\mathcal G_T;A].
\tag{3.13}
$$

Here finite Jensen and the supporting-tangent inequality are used
only after (3.7)--(3.8) verify their hypotheses; these elementary
convexity facts are as in S. Boyd and L. Vandenberghe,
*Convex Optimization*, §§3.1.3 and 3.1.8,
[author text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).

The cancellation needed for all cardinalities is stronger than a
bound using just $\min_{i\in C}y_i$. In fact, (3.1) gives
$\theta=mrd/q^2+o(a^2)$, and the exact identity (3.9) gives

$$
\begin{aligned}
\Xi&:=\eta^2-\theta-mP/r\\
&=\frac{mJ'(p_0)}r-\theta-\frac{\eta^2}r\\
&=\frac{mr+md/r}{q^2}-\frac{\eta^2}r+o(a^2)=O(a^2).
\end{aligned}
\tag{3.14}
$$

Also $\psi+P/r=O(a^2)$. Both constants are absolute eventually.
For a singleton in $D$, (3.10) is exactly

$$
\mathcal G_{\{k\}}=(y_k^{-1}-\eta)^2\ge0.
\tag{3.15}
$$

For $K\ge2$, completing each reciprocal square yields

$$
\begin{aligned}
\mathcal G_T
&\ge\eta^2(1-B/K^2)+\Xi(B-1)-(\psi+P/r)L\\
&\ge\eta^2/2-Ca^2K.
\end{aligned}
\tag{3.16}
$$

If $2\le K\le\sqrt a$, this is at least $a^3$ eventually.
For $K>\sqrt a$, use $y_k\le\delta=o(a^{-1})$ on $D$.
Then $K^2y_k^{-1}\ge4\eta$ eventually, and hence
$Z_T-2\eta V_T\ge Z_T/2$. Equations (3.10) and (3.14) give

$$
\mathcal G_T\ge\frac{BK^2}{2\delta^2}+\eta^2
                    +\Xi(B-1)-(\psi+P/r)L
\ge\frac{a^2K^2}{2}-Ca^2K\ge a^3/8
\tag{3.17}
$$

eventually. This includes $K>m$ and all cardinalities up to $s$;
there is no fixed bound on $B$, $L$, $j$ or $h/\sqrt a$.
Thus every summand in (3.13) is nonnegative and every nonsingleton
type meeting $D$ has the asserted strict price.

If $H=S_j$, (3.13)--(3.17) force every type meeting $D$ to be a
singleton. Every $y_k$ on $D$ then equals $x_{\{k\}}>0$;
(3.15) forces $y_k=1/\eta=p_0/n$. Thus $u=p=p_0$.
The remaining events lie in $C$, have total mass $1-p_0$, and have
total mean $a-p_0=m(1-p_0)$. Since their cardinalities are at most
$m$, every such event must be the whole set $C$. This is (3.2).
Conversely, Growing, Theorem 3.1, evaluates that law as $S_j$.
All equality implications concern the original joint law. ∎

## 4. The uniform exact classification

**Theorem 4.1 (Absolute mesoscopic envelope and all equality laws).**
There exist absolute constants $A>4$, $K_*>4$, and $\varepsilon>0$
such that, for every pair of integers

$$
a\ge A,\qquad K_*\sqrt a\le h\le\varepsilon a^{3/2},
\tag{4.1}
$$

the full original common-law problem satisfies

$$
M(a,h)=\min_{1\le j\le h}
\left\{\frac{(a+j)^3(a+j-1)}{a-1}
       +\frac{(h+1-j)^2(a+j-1)}j\right\}.
\tag{4.2}
$$

The infimum is attained. For each winning index $j$, every partition
$C\dot\cup D=[s]$ with $|C|=a+j$ gives an attaining law

$$
x_C=\frac{a-1}{a+j-1},\qquad
x_{\{k\}}=\frac{j}{(a+j-1)(h+1-j)}\ (k\in D),
\qquad x_T=0\ \text{otherwise}.
\tag{4.3}
$$

These, including arbitrary label permutations and every winning
index at a tie, are all equality laws. There are either one or two
winning indices; in the latter case they are adjacent. Their exact
comparison and all ties are the cap comparisons in Growing,
Proposition 15.6. No nontrivial convex combination of distinct
attaining laws is attaining.

**Proof.** First take an arbitrary mesoscopic sequence (1.3) and
arbitrary original laws with $H\le U$. Lemma 2.1 supplies the
partition and every hypothesis of Lemma 3.1. Eventually,

$$
U\ge H\ge S_j\ge U.
\tag{4.4}
$$

Thus the laws are precisely (4.3), with winning indices, for all
sufficiently large indices of this arbitrary sequence.

This sequential conclusion implies the absolute rectangular
parameter range (4.1). To verify the quantifiers, call a pair
$(a,h)$ bad if some original law with $H\le U$ is not a winning cap
law. If no constants in (4.1) excluded bad pairs, for every integer
$N\ge5$ one could choose a bad pair satisfying

$$
a_N\ge N,\qquad h_N/\sqrt{a_N}\ge N,
\qquad h_N/a_N^{3/2}\le1/N,
\tag{4.5}
$$

and one of its witnessing laws. This is a sequence (1.3), contradicting
(4.4) and Lemma 3.1. Therefore some absolute $A,K_*,\varepsilon$
exclude all bad pairs. Enlarging $A,K_*$ if necessary gives both
strictly greater than $4$. This argument proves simultaneous
uniformity on (4.1); it does not merely choose a slowly growing
upper bound for $h/\sqrt a$.

For such a pair, a law of energy strictly less than $U$ would itself
be bad. Therefore every original law has $H\ge U$. The cap suppliers
attain $U$, and the absence of bad pairs gives exactly (4.3) for
every equality. This proves both the value and attainment without
an a priori existence assumption for arbitrary optimizers.

Growing, Proposition 15.6, proves strict discrete convexity of the
entire cap sequence, not just a bounded-index restriction. It gives
the claimed adjacent ties and rules out triple ties. Finally, an
attaining law has exactly one nonsingleton type of positive mass,
its core $C$. If a convex combination of attaining laws were attaining,
positivity would force every component of positive weight to have
this same core. Its size fixes $j$, and (4.3) fixes all its masses.
All components are therefore identical, proving the mixture assertion.

The new estimates (1.7), (2.3), and the reciprocal-square cancellation
(3.14) are repo-derived. Growing, Theorems 3.1 and 8.2, supply the
cap comparisons and their leading scale; its identities (8.8)--(8.11),
(10.5)--(10.6), and (15.12) supply the reused contact and incidence
relations. Growing, Theorems 15.5--15.6, already classify every fixed
finite square-root window. Their fixed-window threshold is not used
to obtain uniformity in (4.1).

The other CDSO volumes have distinct conclusions: [*Capacity
crossovers and rare phases*](CDSO_CAPACITY_CROSSOVERS_AND_RARE_PHASES.md)
concerns moving means and dense phases; [*Incidence moments and
capacity phases*](CDSO_INCIDENCE_MOMENTS_AND_CAPACITY_PHASES.md) supplies
the common-incidence model and capacity results;
[*Higher-capacity profiles*](CDSO_HIGHER_CAPACITY_PROFILES.md),
[*Sink incidence and density limits*](CDSO_SINK_INCIDENCE_AND_DENSITY_LIMITS.md),
and [*Universal vertex, all cyclomatic numbers*](CDSO_UNIVERSAL_VERTEX_ALL_CYCLOMATIC.md)
also concern finite-graph reductions and realizations.
The fixed-parameter expansion of [*Periodic connection
cost*](CDSO_PERIODIC_CONNECTION_COST.md), Theorem 1.3, and the fixed
positive square-root-window transfer of [*Uniform dilution
limit*](CDSO_UNIFORM_DILUTION_LIMIT.md), Theorem 1.2, supply no
joint-growth graph conclusion here. Formula (4.2) is a theorem for
the original law domain, with all cardinalities, zero type masses,
arbitrarily small positive actual marginals, and disconnected
support retained.

The graph motivation uses the maximum-degree normalization in
Albalahi--Das--Ali--Barman--Hamza, *On the hyperbolic Sombor index
and its counterpart*, DOI
[10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176),
as recorded in Growing, Definition 1.1. No finite-graph extremal
statement from that article is a premise of the classification.
The possible full-text overlap with Zhao--Zhao, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
is unassessed; no priority assertion is attached to this theorem. ∎

## 追加锚（本行以下为增补区）
