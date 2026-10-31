# CDSO periodic connection cost

## 1. Prescribed graph budgets and the first connection term

**Definition 1.1 (Inherited domains and winning caps).** Fix a finite
$R\ge4$. Integers $a,h$ satisfy

$$
a\ge A_R,\qquad \frac72\sqrt a\le h\le R\sqrt a,\qquad
s=a+1+h.
\tag{1.1}
$$

Here $A_R$ may be increased in the statements below. The law domain
$\mathcal X(a,h)$, its energy $H$, and its minimum $M=M(a,h)$ are
exactly those of [*CDSO growing surplus hubs*, Definition
1.1](CDSO_GROWING_SURPLUS_HUBS.md): one probability law on every
nonempty subset of $[s]$, mean cardinality $a$, and strictly positive
actual marginals $y_i$. In particular,

$$
H(x)=\sum_{\varnothing\ne T\subseteq[s]}
x_T|T|^2\sum_{i\in T}y_i^{-2},\qquad
y_i=\sum_{T\ni i}x_T.
\tag{1.2}
$$

The graph class $\mathfrak G_N(a,h)$ and $V_N$ are exactly those of
Growing Definition 9.1. A graph is finite, simple, connected and
bipartite with independent parts $S,[s]$, with $N$ sources, $s$ sinks,
$aN$ edges, and

$$
d_G(u)<d_G(i)\quad(ui\in E,\ u\in S,\ i\in[s]).
\tag{1.3}
$$

Its cyclomatic number is $(a-1)N-s+1$. Its objective is

$$
\begin{aligned}
W(G)&=2NE(G),\\
E(G)&=\sum_{ui\in E}
\left(\sqrt{1+(d_G(u)/d_G(i))^2}-1\right),\\
V_N&=\min_{G\in\mathfrak G_N(a,h)}W(G)
\end{aligned}
\tag{1.4}
$$

whenever the class is nonempty. The maximum-endpoint-degree
normalization in (1.4) has no factor $1/\sqrt2$; it is the CDSO
normalization of Albalahi--Das--Ali--Barman--Hamza, *On the hyperbolic
Sombor index and its counterpart*, Discrete Math. Lett. 16 (2025),
108--115, §1, p.109, DOI
[10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176),
also [arXiv:2510.24809v1](https://arxiv.org/html/2510.24809v1).

Growing Theorem 15.5 supplies, in (1.1), the finite nonempty set

$$
J_* =\{j:1\le j\le h,\ S_j=M\},\qquad
S_j=\frac{(a+j)^3(a+j-1)}{a-1}
       +\frac{(h+1-j)^2(a+j-1)}j.
\tag{1.5}
$$

For $j\in J_*$ put

$$
m=a+j,\quad r=m-1,\quad n=h+1-j,\quad
\alpha=\frac{a-1}{r},\quad
\beta=\frac{j}{rn},\quad \eta=\beta^{-1}.
\tag{1.6}
$$

For each partition $C\dot\cup D=[s]$ with sizes $m,n$, its cap law is

$$
x_C^*=\alpha,\qquad x_{\{k\}}^*=\beta\ (k\in D),
\qquad x_T^*=0\text{ otherwise}.
\tag{1.7}
$$

Every minimum law is one of (1.7), by the cited theorem. The core
marginals are $\alpha$, the tail marginals are $\beta$, and
$\alpha+n\beta=1$, $m\alpha+n\beta=a$. All symbols in (1.6)
refer to this same actual law.

**Definition 1.2 (Connection and repair prices).** For each winning
$j$, with notation (1.6), define

$$
\begin{aligned}
\lambda_j&=\frac{\eta^2-m^3/\alpha^2}{r},\\
b_j&=\frac{4-2m^2}{\alpha^2}+3\eta^2-\lambda_j,\\
c_j&=\frac{\eta^2-(r^3+r^2m+m^2)/\alpha^2}{r},\\
d_{j,N}&=\bigl[n-(a-1)N\bigr]_r,\\
\chi_{j,N}&=nb_j+d_{j,N}c_j,\qquad
\chi_N=\min_{j\in J_*}\chi_{j,N}.
\end{aligned}
\tag{1.8}
$$

Here $[z]_r$ is the unique integer in $\{0,\ldots,r-1\}$ congruent
to $z$ modulo $r$. The symbols $b_j,c_j$ are respectively the
connection and repair prices; they are unrelated to the function
called $b_j(p)$ in Growing Definition 15.1. In its notation,

$$
c_j=-\frac{F_j'(j/r)}r>0.
\tag{1.9}
$$

The equality in (1.9) follows from Growing (15.23) and
$r^3+r^2m+m^2=2mr^2+2m-1$; its positivity also follows in Lemma
2.2 below.

**Theorem 1.3 (Periodic first connection cost and eventual source
types).** For every fixed finite $R\ge4$, one can choose $A_R$ so
that the following holds for every integer pair in (1.1). There
exist finite constants $C(a,h)>0$ and $N_0(a,h)$ such that, for
every integer $N\ge N_0(a,h)$, the class $\mathfrak G_N(a,h)$ is
nonempty and

$$
\left|V_N-M-\frac{\chi_N}{N}\right|
\le\frac{C(a,h)}{N^2}.
\tag{1.10}
$$

After increasing $N_0$, every exact minimizer has a partition
$C\dot\cup D=[s]$ associated to some
$j\in J_*$ with $\chi_{j,N}=\chi_N$, and has precisely these
source neighborhoods:

1. exactly $n$ two-element sets $\{i,k\}$, with $i\in C$, $k\in D$,
   one for each $k\in D$;
2. exactly $d_{j,N}$ sets $C\setminus\{i\}$, with $i\in C$;
3. full cores $C$ and singleton tails $\{k\}$ for every remaining
   source.

In particular there are no other source types. The statement does
not prescribe the core endpoints of the $n$ connectors, the omitted
core labels, the singleton allocations, or a graph isomorphism
class. The constants in (1.10), including $N_0$, may depend on the
fixed integers $a,h$; uniformity as $a,h,N$ grow jointly is not
asserted.

The proof is given in Section 5. Its lower bound ranges over the
whole class in Definition 1.1, with no restriction on source
cardinalities or marginal sizes.

## 2. A price for every nonempty neighborhood

**Definition 2.1 (Reduced type price).** Fix a winning cap and its
partition. For a nonempty $T\subseteq[s]$, write
$L=|T\cap C|$, $B=|T\cap D|$, and $K=L+B$. Define

$$
\rho_j(L,B)=\frac{L(K^2-2m^2)}{\alpha^2}
              +B(K^2-2)\eta^2+\eta^2-\lambda_j(K-1).
\tag{2.1}
$$

A type is ordinary when it is $C$ or a singleton in $D$; all other
types are exceptional. Thus
$\rho_j(m,0)=\rho_j(0,1)=0$,
$\rho_j(1,1)=b_j$, and $\rho_j(r,0)=c_j$.

**Lemma 2.2 (Strict all-cardinality price inequalities).** After
increasing $A_R$, every winning cap in (1.1) satisfies

$$
0<rc_j<\eta^2<b_j,\qquad
\eta^2>\frac{2m^2+4}{\alpha^2}.
\tag{2.2}
$$

For core-only types, $1\le L\le m$,

$$
\rho_j(L,0)=(m-L)c_j
 +\frac{(m-L)(r-L)(m+r+L)}{\alpha^2}.
\tag{2.3}
$$

For types meeting both parts, except $(L,B)=(1,1)$,

$$
\rho_j(L,B)>B b_j+\eta^2
                    >B b_j+rc_j.
\tag{2.4}
$$

For tail-only types with $B\ge2$,

$$
\rho_j(0,B)>(B-1)b_j+rc_j.
\tag{2.5}
$$

Every exceptional type consequently has strictly positive price.
These statements include every $1\le K\le s$.

**Proof.** Growing Lemma 15.2 bounds every winning $j$ by a
constant depending on $R$, with $j\ge2$. Put $q=h/\sqrt a$ and
$z=n^2/(j^2a)$. That lemma gives
$z>5/2-O_R(a^{-1/2})$, while $z=O_R(1)$. Uniformly over these
indices,

$$
\begin{gathered}
m=a+O_R(1),\quad r=a+O_R(1),\quad
\alpha=1+O_R(a^{-1}),\\
\eta^2=za^3+O_R(a^2),\qquad
\frac{r^3+r^2m+m^2}{\alpha^2}=2a^3+O_R(a^2),\\
rc_j=(z-2)a^3+O_R(a^2),\qquad
b_j=3za^3+O_R(a^2).
\end{gathered}
\tag{2.6}
$$

These imply (2.2). The strict upper bound $rc_j<\eta^2$ also
follows directly from (1.8). Substitution in (2.1) proves the
polynomial identity (2.3).

If $L,B\ge1$ and $K\ge3$, subtraction of $Bb_j$ gives exactly

$$
\begin{aligned}
\rho_j(L,B)-Bb_j
={}&\eta^2\left\{B(K^2-5)+1-\frac{L-1}{r}\right\}\\
 &+\frac{LK^2-4B-2m^2(L-B)+(m^3/r)(L-1)}{\alpha^2}.
\end{aligned}
\tag{2.7}
$$

Since $1\le L\le m$, the last two terms in braces after
$B(K^2-5)$ have nonnegative sum. The second line is bounded below
by $-(2m^2+4)K/\alpha^2$. For integers $K\ge3$,
$B(K^2-5)\ge K+1$. Thus (2.2) makes (2.7) strictly greater than
$\eta^2$, proving (2.4). The only mixed type of size two is
$(1,1)$, already listed in Definition 2.1.

For $L=0$, $B\ge2$, the exact subtraction is

$$
\rho_j(0,B)-(B-1)b_j
=(B^3-5B+4)\eta^2
  +\frac{(B-1)(2m^2-4)}{\alpha^2}.
\tag{2.8}
$$

Here $B^3-5B+4\ge2$, proving (2.5) by (2.2). Finally (2.3)
is positive for every core-only exceptional type: $m-L\ge1$,
$r-L\ge0$, and $c_j>0$. No support assumption has entered. ∎

**Lemma 2.3 (The prices are the constrained first variation).**
Extend the rational expression (1.2) to real arrays whose
marginals are positive. Its partial derivative at (1.7), for a
type with counts $L,B$, is

$$
g_j(L,B)=\frac{L(K^2-2m^2)}{\alpha^2}
              +B(K^2-2)\eta^2.
\tag{2.9}
$$

For every $x\in\mathcal X(a,h)$,

$$
DH(x^*)[x-x^*]=\sum_T\rho_j(|T\cap C|,|T\cap D|)x_T.
\tag{2.10}
$$

**Proof.** For a sink $i$, the numerator of its summand in $H$ is
$A_i(x)=\sum_{T\ni i}|T|^2x_T$. Differentiation gives

$$
\frac{\partial H}{\partial x_T}
=\sum_{i\in T}\left(\frac{K^2}{y_i^2}
                           -\frac{2A_i(x)}{y_i^3}\right).
$$

At the cap, $A_i=\alpha m^2$ for $i\in C$ and
$A_k=\beta$ for $k\in D$, proving (2.9). In particular
$g_j(m,0)=-m^3/\alpha^2$ and $g_j(0,1)=-\eta^2$.
The affine function of cardinality agreeing with these two values
is $\kappa_j+\lambda_j K$, where
$\kappa_j=-\eta^2-\lambda_j$. Subtracting it gives exactly
(2.1). Both the total mass and the mean of $x-x^*$ vanish.
The affine subtraction therefore changes no first variation.
The price vanishes on the support of $x^*$, proving (2.10). ∎

## 3. Local control without assuming convexity of the law energy

**Lemma 3.1 (A local lower expansion with a quadratic error in
exceptional mass).** Fix $a,h$ and a winning cap partition. There
are a neighborhood $\mathcal U$ of $x^*$ in the probability
simplex and constants $A,c,p_0>0$, depending on $a,h$, such that
every $x\in\mathcal U\cap\mathcal X(a,h)$ satisfies the following.
Write

$$
\varepsilon=\sum_{T\text{ exceptional}}x_T,\qquad
\nu_k=y_k-\beta\quad(k\in D),\qquad
P(x)=\sum_T\rho_j(|T\cap C|,|T\cap D|)x_T.
\tag{3.1}
$$

Then

$$
\begin{aligned}
H(x)&\ge S_j+P(x)+c\sum_{k\in D}\nu_k^2-A\varepsilon^2,\\
P(x)&\ge p_0\varepsilon,\\
H(x)&\ge S_j+\frac{p_0}{2}\varepsilon
                         +c\sum_{k\in D}\nu_k^2.
\end{aligned}
\tag{3.2}
$$

There is also an ordinary Taylor expansion

$$
H(x)=S_j+P(x)+O_{a,h}(\|x-x^*\|^2)
\tag{3.3}
$$

in this neighborhood, where the norm is Euclidean. No global
convexity of $H$ is asserted.

**Proof.** Set $z=x_C$, $w_k=x_{\{k\}}$ for $k\in D$, and regard
the exceptional masses as variables. The original normalization
and mean give the exact identity

$$
rz+\sum_{T\text{ exceptional}}(|T|-1)x_T=a-1.
\tag{3.4}
$$

Consequently $z-\alpha=O_{a,h}(\varepsilon)$. For a core label let

$$
e_i=\sum_{\substack{T\text{ exceptional}\\i\in T}}x_T,
\qquad
f_i=\sum_{\substack{T\text{ exceptional}\\i\in T}}|T|^2x_T.
$$

Its marginal and numerator are $z+e_i$ and $m^2z+f_i$. The core
contribution is therefore the smooth function

$$
H_C=\sum_{i\in C}\frac{m^2z+f_i}{(z+e_i)^2}.
\tag{3.5}
$$

All its arguments differ from their cap values by
$O_{a,h}(\varepsilon)$, so its Taylor remainder is bounded in
absolute value by a constant times $\varepsilon^2$.

For a tail label put

$$
q_k=\sum_{\substack{T\text{ exceptional}\\k\in T}}
(|T|^2-1)x_T\ge0.
$$

Then $q_k=O_{a,h}(\varepsilon)$ and the tail contribution is
exactly

$$
H_D=\sum_{k\in D}\left(\frac1{y_k}+\frac{q_k}{y_k^2}\right).
\tag{3.6}
$$

Shrink the neighborhood so that
$\beta/2<y_k<3\beta/2$. The positive second derivative of $1/t$
on this interval gives constants $c_1,A_1>0$ with

$$
\begin{aligned}
\sum_{k\in D}\frac1{y_k}
 &\ge \frac n\beta-\eta^2\sum_k\nu_k+c_1\sum_k\nu_k^2,\\
\sum_{k\in D}\frac{q_k}{y_k^2}
 &\ge\eta^2\sum_k q_k-A_1\varepsilon
                           \left(\sum_k\nu_k^2\right)^{1/2}.
\end{aligned}
\tag{3.7}
$$

The elementary inequality
$uv\le c_1v^2/2+u^2/(2c_1)$ absorbs the last product into half
the positive quadratic term, with another $O_{a,h}(\varepsilon^2)$
error. The sum of the linear terms from (3.5)--(3.7) is precisely
$DH(x^*)[x-x^*]=P(x)$ by Lemma 2.3. This proves the first line
of (3.2). There are finitely many exceptional types and their
prices are positive by Lemma 2.2. Their least price $p_0>0$ proves
the second line. Shrink $\mathcal U$ again so that
$A\varepsilon\le p_0/2$, obtaining the third line.

All marginal denominators are positive in a real open
neighborhood of the cap. The full rational function has bounded
second derivatives on a smaller neighborhood, giving (3.3).
The first inequality in (3.7) is the scalar supporting-tangent
inequality applied to $1/t$ after subtracting a positive
quadratic; see Boyd--Vandenberghe, *Convex Optimization*, §3.1.3,
[author text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf);
the positive second derivative above verifies the needed
convexity. No such hypothesis is imposed on $H$. ∎

**Lemma 3.2 (Compact localization for actual graphs).** Fix $a,h$.
For any finite $L_0>0$, graphs in Definition 1.1 satisfying
$W(G)\le L_0$ have actual sink marginals bounded below by a
positive constant depending only on $L_0$. Uniformly on this
sublevel,

$$
0\le H(x_G)-W(G)\le\frac{A(a,h,L_0)}{N^2}.
\tag{3.8}
$$

If $N\to\infty$ and $W(G_N)\le M+O_{a,h}(N^{-1})$, the law of
each graph belongs, eventually, to the union of the neighborhoods
in Lemma 3.1 over every winning cap and partition. In whichever
such neighborhood it lies, its number of exceptional sources is
$O_{a,h}(1)$ and

$$
W(G_N)\ge M+\frac{\mathcal P_j(G_N)}N
                         -\frac{A(a,h)}{N^2},
\qquad
\mathcal P_j(G)=\sum_{u\in S}\rho_j(L_u,B_u).
\tag{3.9}
$$

The constants can be chosen uniformly over the finitely many
winning partitions and over any fixed upper constant in the
$O(N^{-1})$ hypothesis.

**Proof.** Set $\vartheta=2/(1+\sqrt2)>0$. For $0\le t<1$,

$$
\vartheta t^2\le2(\sqrt{1+t^2}-1)\le t^2.
$$

The actual graph identity in Growing Lemma 9.2 therefore gives
$\vartheta H(x_G)\le W(G)\le H(x_G)$. Since every source has
positive degree,

$$
H(x_G)\ge\sum_{i=1}^s\frac1{y_i}.
\tag{3.10}
$$

Indeed the numerator $A_i=\mathbb E[K^2\mathbf1_{i\in T}]$ is
at least $y_i$. Thus $y_i\ge\vartheta/L_0$ on the sublevel.
Put $\delta=\vartheta/L_0$. Each source degree is at most $s$,
so Growing (9.5), with exactly $aN$ actual edges, implies

$$
0\le H(x_G)-W(G)
\le\frac N4(aN)\left(\frac{s}{\delta N}\right)^4
=\frac{as^4}{4\delta^4N^2}.
\tag{3.11}
$$

This proves (3.8) without an imposed marginal floor.

For the sequence in the assertion, $H(x_{G_N})\to M$ by (3.8)
and the definition of $M$. Its laws belong to a compact subset
of the finite-dimensional probability simplex: their means are
$a$ and every marginal is at least some fixed $\delta>0$.
$H$ is continuous on this compact set. Every subsequential limit
therefore minimizes $H$, hence is one of the finitely many laws
(1.7) by Growing Theorem 15.5. The laws eventually lie in any
prescribed open union of their neighborhoods. This argument is
uniform on the stated $M+O(N^{-1})$ sublevel; otherwise a
contradicting sequence outside that union would have such a limit.

Within each neighborhood (3.2) gives
$\varepsilon=O_{a,h}(N^{-1})$. The number of exceptional sources
is $N\varepsilon$, an integer bounded independently of $N$.
The first line of (3.2), with (3.8), now gives (3.9), since
$P(x_G)=\mathcal P_j(G)/N$. Finitely many caps and partitions
allow common constants. This uses the existing exhaustive
equality theorem only for localization; the finite-graph prices
and the error estimate are additional relations. ∎

## 4. Connected integer neighborhoods and exact edge repair

**Lemma 4.1 (The integer price minimum over all connected
competitors).** Fix a winning cap and its partition, and let
$G\in\mathfrak G_N(a,h)$ be any graph, without a neighborhood
restriction. Then

$$
\mathcal P_j(G)\ge nb_j+d_{j,N}c_j.
\tag{4.1}
$$

Equality holds if and only if the source types are precisely
those in Theorem 1.3 for this partition. In particular each tail
has its own single core--tail connector. This assertion concerns
the price sum, not an exact finite formula for $W$.

**Proof.** For a source with counts $L,B$ set

$$
q(L,B)=
\begin{cases}
B,&L>0,\ B>0,\\
B-1,&L=0,\ B>0,\\
0,&B=0.
\end{cases}
\tag{4.2}
$$

Connectedness implies

$$
\sum_{u\in S}q(L_u,B_u)\ge n.
\tag{4.3}
$$

To verify this, identify all core sinks as one vertex. For each
source replace its distinct adjacent sink vertices after the
identification by any tree spanning them, and remove the source.
A single adjacent sink needs no tree edge. The resulting
multigraph on the $n$ tail vertices and the core vertex is
connected, because each replacement preserves connectivity
between that source's adjacent sinks. Its number of edges is
exactly the left side of (4.3), so it is at least $n$. This
argument permits arbitrary original neighborhoods, including
tail-only sources and sources meeting all sinks.

Call a type meeting the tail bad if it is neither a tail singleton
nor a two-element core--tail connector. By Lemma 2.2 every type
has price at least $q(L,B)b_j$, and any bad type has price
strictly greater than $q(L,B)b_j+rc_j$. If a bad source exists,
(4.3) yields

$$
\mathcal P_j(G)>nb_j+rc_j
                  >nb_j+d_{j,N}c_j.
\tag{4.4}
$$

There can be no equality in this case, and (4.1) holds.

Otherwise let $b$ be the number of core--tail connectors and put

$$
D_0=\sum_{u:B_u=0}(m-L_u).
\tag{4.5}
$$

Now (4.3) is $b\ge n$. Using (2.3) gives

$$
\mathcal P_j(G)=bb_j+D_0c_j
 +\sum_{u:B_u=0}
   \frac{(m-L_u)(r-L_u)(m+r+L_u)}{\alpha^2}.
\tag{4.6}
$$

Every term in the last sum is nonnegative. If $b\ge n+1$,
$b_j>rc_j$ in (2.2) makes (4.6) strictly greater than the right
side of (4.1). It remains to consider $b=n$.

The original edge budget, after subtracting one from every source
degree, is

$$
(a-1)N=\sum_{u\in S}(K_u-1)
\equiv b-D_0\pmod r.
\tag{4.7}
$$

Here a core-only source contributes
$L_u-1=r-(m-L_u)$, a connector contributes one, and a tail
singleton contributes zero. Hence for $b=n$,
$D_0\equiv d_{j,N}\pmod r$, so $D_0\ge d_{j,N}$. Formula
(4.6) proves (4.1). Equality requires $D_0=d_{j,N}$ and
vanishing of every term in the last sum. For a nonempty core-only
type those zeros are exactly $L=m$ and $L=r$. Thus there are
exactly $d_{j,N}$ missing-one-core sources, and every other
core-only source is full-core. Only $n$ connectors and tail
singletons remain. Each tail must occur in at least one connector,
since otherwise it and its singleton sources form a separate
component. There are $n$ tails and $n$ connectors, so each tail
occurs exactly once. Conversely these source types give equality
by (2.1) and (1.8). ∎

**Lemma 4.2 (Every large integer budget realizes the minimum
price).** Fix $a,h$, a winning $j$, and any core--tail partition.
For every sufficiently large integer $N$ there is
$G_{j,N}\in\mathfrak G_N(a,h)$ with the source types in Theorem
1.3 and

$$
W(G_{j,N})=M+\frac{nb_j+d_{j,N}c_j}{N}
                         +O_{a,h}(N^{-2}).
\tag{4.8}
$$

No congruence condition on $N$ is needed.

**Proof.** Write $d=d_{j,N}$ and take $n$ degree-two connectors,
one from each tail to any core label. Take $d$ missing-one-core
sources, omitting arbitrary core labels. Set the full-core and
tail-singleton counts to be

$$
F=\frac{(a-1)N-n-(r-1)d}{r},\qquad
T=N-F-n-d.
\tag{4.9}
$$

The residue defining $d$ makes both counts integers. Since
$0\le d<r$ and $a,h$ are fixed,

$$
F=\alpha N+O_{a,h}(1)>0,\qquad
T=n\beta N+O_{a,h}(1)>0
\tag{4.10}
$$

for all sufficiently large $N$. Give $F$ sources the full-core
neighborhood and distribute the $T$ singleton sources among the
$n$ tails with counts differing by at most one. The source count
is exactly $N$, and the edge count is exactly

$$
mF+rd+2n+T
=N+rF+(r-1)d+n=aN.
\tag{4.11}
$$

Repeated neighborhoods belong to different source vertices, so
the graph is simple. A full-core source joins all core sinks,
and each tail has a connector to the core, so the graph is
connected. Its actual sink degrees satisfy

$$
d_i=\alpha N+O_{a,h}(1)\ (i\in C),\qquad
d_k=\beta N+O_{a,h}(1)\ (k\in D).
\tag{4.12}
$$

For example, if $o_i$ missing-one sources omit $i$ and $e_i$
connectors use it, then $d_i=F+d-o_i+e_i$; at a tail its degree
is its singleton count plus one. All these degrees eventually
exceed $s$, whereas every source degree is at most $s$. Thus
the strict orientation (1.3) holds for the same actual graph.
All the budgets and the cyclomatic number are consequently the
ones in Definition 1.1.

Its law has $x_C=F/N$, $x_{\{k\}}=\beta+O_{a,h}(N^{-1})$,
and at most $n+d$ exceptional sources. Hence
$\|x_G-x^*\|=O_{a,h}(N^{-1})$. Lemma 2.3 and (3.3) give

$$
H(x_G)=M+\frac{nb_j+dc_j}{N}+O_{a,h}(N^{-2}).
$$

The actual degrees (4.12), or Lemma 3.2, replace $H$ by $W$
with an $O_{a,h}(N^{-2})$ error. This proves (4.8). Finitely
many $j$, partitions and residues allow one threshold and error
constant for all of them. ∎

## 5. Global value, exact exclusion and periodic phase selection

**Proof of Theorem 1.3.** Choose $A_R$ large enough for Growing
Theorem 15.5, its high-ratio localization, and Lemma 2.2.
Thereafter fix $a,h$. Lemma 4.2 proves nonemptiness at every
large integer $N$. Choosing a winning $j$ with
$\chi_{j,N}=\chi_N$ gives a graph with

$$
W(G_{j,N})\le M+\frac{\chi_N}{N}+\frac{C_1(a,h)}{N^2}.
\tag{5.1}
$$

The quantities $\chi_N$ are bounded independently of $N$, because
$J_*$ is finite and every $d_{j,N}$ lies in $\{0,\ldots,r-1\}$.
Consider any graph in the full original class whose objective
is no greater than the right side of (5.1). All such graphs
belong to the sublevel of Lemma 3.2, uniformly, so each has a
winning cap partition for which

$$
\begin{aligned}
W(G)&\ge M+\frac{\mathcal P_j(G)}N
                             -\frac{C_2(a,h)}{N^2}\\
&\ge M+\frac{\chi_{j,N}}N-\frac{C_2(a,h)}{N^2}
 \ge M+\frac{\chi_N}N-\frac{C_2(a,h)}{N^2}.
\end{aligned}
\tag{5.2}
$$

The middle inequality is Lemma 4.1, which covered every
neighborhood type. A graph above the sublevel (5.1) already
exceeds the last lower bound in (5.2). Thus this lower bound
holds over every graph of Definition 1.1. Combining it with
(5.1) proves (1.10).

It remains to turn an asymptotic price minimum into exact
exclusion of source types. Every number in (1.6), (1.8) and
(2.1) is rational. There are finitely many winning indices and
possible integer pairs $0\le L\le m$, $0\le B\le n$,
$L+B\ge1$. Choose a positive integer $D_*$ clearing the
denominators of all their prices. Since $b_j,c_j$ are among
these prices, for every integer $N$ both
$\mathcal P_j(G)$ and $\chi_N$ belong to
$D_*^{-1}\mathbb Z$. In particular,

$$
\mathcal P_j(G)>\chi_N
\quad\Longrightarrow\quad
\mathcal P_j(G)-\chi_N\ge D_*^{-1}.
\tag{5.3}
$$

Let $G$ be any exact minimizer. It satisfies (5.1), so its
winning cap partition in (5.2) satisfies

$$
0\le\mathcal P_j(G)-\chi_N
\le\frac{C_1(a,h)+C_2(a,h)}N.
\tag{5.4}
$$

For $N>D_*(C_1+C_2)$ this forces equality. Since
$\mathcal P_j(G)\ge\chi_{j,N}\ge\chi_N$, both inequalities
are equalities. Thus $j$ attains $\chi_N$ and Lemma 4.1 gives
exactly the source types stated in Theorem 1.3. In particular
the missing-one count is the least residue $d_{j,N}$, rather
than that residue plus a multiple of $r$. The full-core count
then equals (4.9) and is positive for large $N$. The proof
does not compare the possible second-order costs of different
connector endpoints, omitted core labels or singleton
allocations, and makes no uniqueness assertion about them. ∎

**Corollary 5.1 (Periodic selection at a common-law tie).** Set

$$
P_* =\operatorname{lcm}_{j\in J_*}
\frac{a+j-1}{\gcd(a+j-1,a-1)}.
\tag{5.5}
$$

Then $\chi_N$ and the set
$\{j\in J_*:\chi_{j,N}=\chi_N\}$ depend only on $N$ modulo
$P_*$. On any residue class for which exactly one index attains
$\chi_N$, all sufficiently large exact graph minimizers belong
to that cap's source-type class in Theorem 1.3. If several indices
attain $\chi_N$, every large exact minimizer belongs to one of
their classes; the first-order formula alone does not assert
that all of these classes contain an exact minimizer.

**Proof.** The residue of $(a-1)N$ modulo $a+j-1$ has period
$(a+j-1)/\gcd(a+j-1,a-1)$. Formula (1.8) proves the first
assertion, and Theorem 1.3 proves the others. Growing Proposition
15.6 shows that in the stated domain $J_*$ has one member or
two adjacent members, including all actual scalar ties. No
choice of independent marginal optimizers is involved in this
periodic comparison: each coefficient belongs to its own
actual equality law (1.7). ∎

**Proposition 5.2 (Relation to the prescribed-budget realization
problem).** In the domain (1.1), the optimizing laws in Growing
Open problem 7.3 are realized as limits of connected graphs with
every sufficiently large integer source budget $N$, and their
unavoidable first connection cost is (1.8). The common-law
equality law itself is disconnected as an incidence support,
and no finite connected graph has that exact law. The graph
conclusion concerns precisely the prescribed sink count and
orientation in Growing Definition 9.1.

**Proof.** In (1.7) the core and the $n\ge1$ individual tail
labels are different incidence components. A graph with exactly
that law has no source meeting two such components, hence is
disconnected. Nevertheless Lemma 4.2 gives convergent connected
realizations at every large $N$. Lemma 4.1 proves that at least
$n$ connections, and then the residue repair, are paid in the
first variation; Lemmas 3.1--3.2 prove that these local prices
govern the global actual graph problem, with the controlled
error in Theorem 1.3. Existing Growing Sections 9 and 11 give
connected integer-budget suppliers and other bounds; the
all-type price exclusion and periodic coefficient proved here
are the additional relations. The finite-capacity graph results
in *CDSO incidence moments and capacity phases*, Sections 5--7
and 11, and in the sink-incidence and higher-capacity volumes
have different budget domains and do not determine this
connection cost for the cap's singleton components.

These are repo-derived deductions from the cited common-law
theorem and actual graph interface. The original graph-index
paper cited in Definition 1.1, §4, supplies the fixed-order,
fixed-cyclomatic motivation, rather than a theorem identifying
this restricted class's minimum. The possible full-text
overlap with Zhao--Zhao, *Extremal values with respect to
vertex-degree-based topological indices in unicyclic and
bicyclic graphs*, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
remains unassessed; that text is not a premise for any proof
above. No worldwide priority assertion is made.

The constants here depend on fixed $a,h$. The theorem therefore
does not settle growing $R(a)$, a least joint-growth source
budget, transition-scale costs, an exact finite formula for
$V_N$, or an extremum with a variable number of sinks. None
of these follows by exchanging the quantifiers in (1.10). ∎

## 追加锚（本行以下为增补区）

## 6. Exact finite allocation and all graph preimages

**Definition 6.1 (Integer allocation data).** All parameters, the
orientation, the graph class and the normalization remain exactly
those of Definition 1.1. Fix a winning $j\in J_*$ and an integer
$N$, and use its $m,r,n,\alpha,\beta$. Write

$$
\begin{gathered}
d=d_{j,N},\qquad
F=\frac{(a-1)N-n-(r-1)d}{r},\qquad
Q=N-F-d,\\
b=\left\lfloor\frac Qn\right\rfloor,\qquad
t=Q-nb\in\{0,\ldots,n-1\},\qquad
\mathcal J_N=\{j\in J_*:\chi_{j,N}=\chi_N\}.
\end{gathered}
\tag{6.1}
$$

Thus $Q$ is the sum of the actual tail degrees, and the number of
tail-singleton sources is $Q-n$. All assertions using graphs below
are for sufficiently large integer $N$, with $a,h$ fixed. In
particular $F>0$ and $b> s$. The letters $b,t$ in this section
are integer quotient and remainder, not the price $b_j$.

For a labelled partition $C\dot\cup D=[s]$ of sizes $m,n$, let
$e_i$ count connectors ending at $i\in C$, and let $o_i$ count
missing-one sources omitting $i$. Their constraints and the actual
sink degrees are

$$
\begin{gathered}
e_i,o_i\in\mathbb Z_{\ge0},\qquad
\sum_{i\in C}e_i=n,\qquad \sum_{i\in C}o_i=d,\\
D_i=F+d-o_i+e_i\quad(i\in C),\qquad
q_k=1+\#\{\text{singleton sources at }k\}\quad(k\in D),\\
q_k\in\mathbb Z_{\ge1},\qquad \sum_{k\in D}q_k=Q.
\end{gathered}
\tag{6.2}
$$

For $k>0$ and $x>0$ put

$$
f_k(x)=\sqrt{1+k^2/x^2}-1,\qquad
g(x)=(x-1)f_1(x)+f_2(x).
\tag{6.3}
$$

Define the finite set, indexed by the core labels,

$$
\mathcal Z_{m,n,d}=\left\{z\in\mathbb Z^C:
 \sum_i z_i=n-d,\quad
 \sum_i z_i^+\le n,\quad \sum_i z_i^-\le d\right\},
\qquad z_i^+=\max(z_i,0),\quad z_i^-=\max(-z_i,0).
\tag{6.4}
$$

Every coordinate lies in $[-d,n]$. For $z$ in this set put

$$
\begin{gathered}
L(z)=n-\sum_i z_i^+=d-\sum_i z_i^-\ge0,\qquad
z_0=\min_i z_i,\qquad I_0(z)=\{i:z_i=z_0\},\\
D_i(z)=F+d+z_i,\qquad D_0(z)=F+d+z_0,\\
\mathcal C_{j,N}(z)=
 \sum_{i\in C}\left\{
 Ff_m(D_i(z))+(d-z_i^-)f_r(D_i(z))
                      +z_i^+f_2(D_i(z))\right\}\\
\hspace{35mm}
 +L(z)\bigl(f_2(D_0(z))-f_r(D_0(z))\bigr),\\
\mathcal T_{j,N}=(n-t)g(b)+t g(b+1),\qquad
\mathcal A_{j,N}(z)=2N\bigl(\mathcal C_{j,N}(z)
                                      +\mathcal T_{j,N}\bigr).
\end{gathered}
\tag{6.5}
$$

When $L=0$ the last term is zero. When $d=0$, (6.4) forces
$z_i\ge0$, $\sum_i z_i=n$ and $L=0$. When $t=0$ the $g(b+1)$
term is absent. These conventions include all zero multiplicities.

**Lemma 6.2 (Exact tail balancing in actual graphs).** For all
sufficiently large $N$, every minimizer of the original class
$\mathfrak G_N(a,h)$ has tail degrees consisting of $n-t$ copies
of $b$ and $t$ copies of $b+1$, for its partition in Theorem 1.3.
All assignments of these degrees to the tail labels are feasible
with any feasible endpoint and omission counts in (6.2).

**Proof.** Theorem 1.3 supplies the source types and (4.9) fixes
$F$, independently of the allocations. At a tail of degree $q$,
there are $q-1$ degree-one sources and one degree-two connector.
Its exact contribution to $E(G)$ is $g(q)$. The objective of a
source-type graph is therefore exactly

$$
W(G)=2N\left[
 \sum_{i\in C}\{Ff_m(D_i)+(d-o_i)f_r(D_i)+e_i f_2(D_i)\}
                    +\sum_{k\in D}g(q_k)\right].
\tag{6.6}
$$

These are the actual degrees in that same graph. No marginal
relaxation has been made.

A minimizer has bounded $W$ by Theorem 1.3, so Lemma 3.2 bounds
all its sink degrees below by a positive multiple of $N$. In
particular its tail degrees exceed $4$ eventually. Direct
scalar differentiation gives

$$
g''(x)=
 \frac{x^3-3x^2-2}{x^3(x^2+1)^{3/2}}
 +\frac{4(3x^2+8)}{x^3(x^2+4)^{3/2}}>0\qquad(x\ge4).
\tag{6.7}
$$

For the displayed sign, $x^3-3x^2-2$ is positive at $4$ and
increasing thereafter. The scalar second-derivative criterion
is the standard one in Boyd--Vandenberghe, *Convex Optimization*,
§3.1.4, [author text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
Only this one-variable function is being asserted strictly convex.

If $q_k\ge q_l+2$, move one singleton source from $k$ to $l$.
This preserves its degree, both original budgets and simplicity.
The connector at each tail remains, and a full-core source remains,
so connectedness is preserved. The decreased tail degree is still
at least $4$, every connector still has degree two, and all core
degrees are unchanged; hence the strict orientation is preserved.
Integrating the strictly increasing derivative of $g$ over the
unit intervals gives

$$
g(q_k)+g(q_l)>g(q_k-1)+g(q_l+1).
\tag{6.8}
$$

This contradicts minimality. Thus the degrees differ by at most
one, and their sum $Q$ gives exactly (6.1). For $n=1$ this
conclusion follows from the sum alone.

Conversely, choose any endpoint assignment of the $n$ connectors,
one for each tail, with histogram $e$, and choose the $d$ omissions
with histogram $o$. Give tail $k$ exactly $q_k-1$ singletons,
where its $q_k$ is either $b$ or $b+1$ and exactly $t$ are the
latter. Together with $F$ full cores these are actual source
neighborhoods. Lemma 4.2's counting and connectivity argument
applies unchanged. All sink degrees are a positive multiple of
$N$ plus a bounded constant, uniformly over these finitely many
choices; they exceed $s$ for large $N$. This verifies the original
orientation for every assignment, including any choice of the
$t$ tail labels. ∎

**Lemma 6.3 (Coupled core allocation and its exact equality
conditions).** Fix $j,N$ and a partition as above. Among the
allocations in (6.2) with prescribed $z_i=e_i-o_i$, the least
core contribution to $E$ is exactly $\mathcal C_{j,N}(z)$.
All allocations attaining it are precisely

$$
e_i=z_i^++\ell_i,\qquad o_i=z_i^-+\ell_i,\qquad
\ell_i\in\mathbb Z_{\ge0},\quad
\sum_i\ell_i=L(z),\quad
\ell_i=0\text{ for }i\notin I_0(z).
\tag{6.9}
$$

Every $z\in\mathcal Z_{m,n,d}$ has such an allocation, and every
feasible pair $(e,o)$ has a unique expression of the first two
forms with $\ell_i=\min(e_i,o_i)$, before imposing the last
condition in (6.9).

**Proof.** Subtracting $e_i-o_i=z_i$ gives the claimed unique
expression. Summing it gives exactly $\sum_i\ell_i=L(z)$ and
(6.4). Conversely any nonnegative allocation of this integer $L$
gives a feasible pair, so (6.4) is also sufficient.

For fixed $z$ the actual core degrees $D_i=F+d+z_i$ do not
change when $\ell$ changes. Substitution in (6.6) leaves a base
sum, the sum in (6.5), plus

$$
\sum_i\ell_i\Delta(D_i),\qquad
\Delta(x)=f_2(x)-f_r(x).
\tag{6.10}
$$

Here $r>2$ in the inherited domain. For $x>0$,

$$
\Delta'(x)=\frac1{x^2}
 \left(\frac{r^2}{\sqrt{x^2+r^2}}
              -\frac4{\sqrt{x^2+4}}\right)>0,
\tag{6.11}
$$

because $k^2/\sqrt{x^2+k^2}$ is strictly increasing in $k>0$.
Consequently the least coefficient in (6.10) occurs exactly at
$I_0(z)$.

The corresponding strict improvement is a legal graph change.
If $\ell_i>0$, select a connector ending at $i$ and a missing-one
source omitting $i$. To move one unit of $\ell$ from $i$ to $l$,
move that connector's core endpoint to $l$ and make that
missing-one source omit $l$ instead. All source degrees, all
sink degrees, and both budgets stay fixed. Simplicity is retained:
the connector's other endpoint is a tail, and the modified
missing-one neighborhood is exactly $C\setminus\{l\}$. Full-core
sources and the tail connectors still ensure connectedness. The
orientation is unchanged since every degree is unchanged. The
change in $E$ is exactly $\Delta(D_l)-\Delta(D_i)$.
Thus every unit outside $I_0$ is strictly improvable, and all
placements inside $I_0$ have the same exact value. This proves
both the minimum and every equality condition, including $L=0$
and all ties among the minimum-degree core labels. ∎

**Theorem 6.4 (Full-domain exact value and exhaustive
reconstruction).** Under exactly Definition 1.1, for every fixed
admissible $a,h$ and every sufficiently large integer $N$,

$$
V_N=\min_{j\in\mathcal J_N}\
          \min_{z\in\mathcal Z_{m,n,d_{j,N}}}
                                      \mathcal A_{j,N}(z).
\tag{6.12}
$$

This is a finite relation with explicit radical summands (6.3)--(6.5).
For fixed parameters and a residue determining $d$, its allocation
set does not grow with $N$. It contains no residual optimization
over graphs.

Every minimizer, with arbitrary source labels, is obtained by the
following reconstruction, and every graph so obtained is a minimizer:
choose a pair $(j,z)$ attaining (6.12), a core--tail partition of
sizes $m,n$, and a choice (6.9); assign the $n$ labelled tails to
core endpoints with histogram $e$; take $d$ missing-one sources
with omission histogram $o$ and $F$ full-core sources; choose any
$t$ tails to have $b$ singleton sources each, and give each other
tail $b-1$ singleton sources. Permute the source labels arbitrarily.
All assignments with these data are included. Repeated descriptions
of one graph are allowed; uniqueness of the description is not
asserted.

**Proof.** The number of choices of $j$ and partitions is finite.
For each $j$, $0\le d<r$ and $-d\le z_i\le n$, so the sets in
(6.12) are finite uniformly in $N$. Equations (6.1) give
$F=\alpha N+O_{a,h}(1)$ and
$b=\beta N+O_{a,h}(1)$. Thus every proposed reconstruction is
legal for one common sufficiently large threshold. Its source
count and edge count are, respectively,

$$
F+d+n+(Q-n)=N,\qquad
mF+rd+2n+(Q-n)=N+rF+(r-1)d+n=aN.
\tag{6.13}
$$

It is simple and connected, and all sink degrees eventually
exceed $s$, by the proofs of Lemmas 6.2--6.3. Hence it belongs
to the full original class, with the prescribed orientation and
cyclomatic number. Formulas (6.6) and (6.9) show that its value
is exactly $\mathcal A_{j,N}(z)$. This gives the upper bound in
(6.12), with every proposed equality graph genuinely realized.

For the reverse bound, the finite nonempty original graph class
has a minimizer. Theorem 1.3, whose lower bound was over that
whole class, places this minimizer at some $j\in\mathcal J_N$
with precisely its source types. Lemma 6.2 forces the displayed
tail allocation. Lemma 6.3 forces (6.9), since otherwise a legal
strict improvement would contradict global minimality. The
minimizer's value is therefore one of the entries of (6.12),
which proves the reverse inequality. In particular this reasoning
is a lower bound for the full class, not an assumption that other
graphs were excluded from the domain.

The same argument sends every original minimizer into the
reconstruction. Conversely, each minimizing entry is realized
by every assignment specified above, and (6.6) shows that its
value is independent of the particular endpoint map with that
histogram, the ordering of omissions, the choice of high-degree
tails, and the source labels. This proves the exhaustive preimage
assertion, including all price ties, law ties, zero counts and
quotient--remainder endpoints. ∎

## 7. The complete second coefficient and a joint-allocation obstruction

**Definition 7.1 (Secondary allocation energy).** For the data of
Definition 6.1 put

$$
\begin{gathered}
\varphi=F-\alpha N=-\frac{n+(r-1)d}{r},\qquad
\sigma=\varphi+d=\frac{d-n}{r},\qquad
\gamma=-\frac{\sigma}{n}=\frac{n-d}{rn},\\
\delta_i=\sigma+z_i,\qquad \delta_0=\sigma+z_0,\qquad
B_i^0=m^2\varphi+r^2(d-z_i^-)+4z_i^+,\\
U_{j,N}=n\gamma^2+\frac{t(n-t)}n-6n\gamma.
\end{gathered}
\tag{7.1}
$$

Define the rational number

$$
\begin{aligned}
\Psi_{j,N}(z)={}&\frac1{\alpha^3}
 \left[\sum_i\{3m^2\delta_i^2-2B_i^0\delta_i\}
                +2(r^2-4)L(z)\delta_0\right]\\
 &+\frac{U_{j,N}}{\beta^3}
       -\frac14\left(\frac{m^5}{\alpha^3}
                                      +\frac n{\beta^3}\right),\\
\Psi_N={}&\min_{j\in\mathcal J_N}\
            \min_{z\in\mathcal Z_{m,n,d_{j,N}}}\Psi_{j,N}(z).
\end{aligned}
\tag{7.2}
$$

The last term in the first formula is the fourth-power correction
from the original graph objective. All quantities use the same
actual cap and allocation; no independent optimization of
numerators or marginal degrees is implicit.

**Theorem 7.2 (Uniform fixed-parameter second-order relation).**
For fixed admissible $a,h$, uniformly over all the allocation
entries in (6.12),

$$
\begin{aligned}
\mathcal A_{j,N}(z)
 &=M+\frac{\chi_{j,N}}N+\frac{\Psi_{j,N}(z)}{N^2}
                                      +O_{a,h}(N^{-3}),\\
V_N&=M+\frac{\chi_N}N+\frac{\Psi_N}{N^2}
                                      +O_{a,h}(N^{-3}).
\end{aligned}
\tag{7.3}
$$

Every sufficiently large exact minimizer has, in addition,
$\Psi_{j,N}(z)=\Psi_N$. Equality of these second coefficients
alone is not asserted to suffice for exact minimality.

**Proof.** First allow arbitrary $e,o$ in (6.2), keeping balanced
tails. Put $z=e-o$ and $\delta_i=\sigma+z_i$ as before, but use

$$
B_i=m^2\varphi+r^2(d-o_i)+4e_i.
\tag{7.4}
$$

The squared-source-degree numerator at core $i$ is exactly
$\alpha m^2N+B_i$, and its degree is exactly
$\alpha N+\delta_i$. At a tail write
$q_k=\beta N+\nu_k$. Its squared-degree numerator is $q_k+3$.
Thus the law energy in (1.2) is exactly

$$
H(x_G)=N\sum_i
 \frac{\alpha m^2N+B_i}{(\alpha N+\delta_i)^2}
                   +N\sum_k\frac{\beta N+\nu_k+3}
                                          {(\beta N+\nu_k)^2}.
\tag{7.5}
$$

The offsets $\varphi,\delta_i,B_i,\nu_k$ are bounded in terms
of fixed $a,h$ alone. Expanding each positive denominator gives

$$
\begin{aligned}
N\frac{\alpha m^2N+B_i}{(\alpha N+\delta_i)^2}
={}&\frac{m^2}{\alpha}
 +\frac{B_i-2m^2\delta_i}{\alpha^2N}
 +\frac{3m^2\delta_i^2-2B_i\delta_i}{\alpha^3N^2}
 +O_{a,h}(N^{-3}),\\
N\frac{\beta N+\nu_k+3}{(\beta N+\nu_k)^2}
={}&\frac1\beta+\frac{3-\nu_k}{\beta^2N}
 +\frac{\nu_k^2-6\nu_k}{\beta^3N^2}
 +O_{a,h}(N^{-3}).
\end{aligned}
\tag{7.6}
$$

The constant sum is $m^3/\alpha+n/\beta=S_j=M$. The coefficient
of $N^{-1}$ is $nb_j+dc_j$: this follows either by summing (7.6)
and using $\sum e_i=n$, $\sum o_i=d$, $\sum\nu_k=-\sigma$,
or from the exact first variation in Lemma 2.3. In the latter
calculation the exceptional counts are $n$ connectors and $d$
missing-one sources and all ordinary prices vanish.

For balanced tails, their offsets consist of $n-t$ copies of
$\gamma-t/n$ and $t$ copies of $\gamma+1-t/n$. Consequently

$$
\sum_k\nu_k=n\gamma,\qquad
\sum_k\nu_k^2=n\gamma^2+\frac{t(n-t)}n,
\tag{7.7}
$$

including $t=0$. This proves the tail term $U_{j,N}/\beta^3$.

It is essential to expand the actual square root as well.
For the actual edge ratios, all of which are $O_{a,h}(N^{-1})$,
Taylor's theorem gives, uniformly,

$$
W(G)=H(x_G)-\frac N4
       \sum_{ui\in E}\frac{d_G(u)^4}{d_G(i)^4}
                                      +O_{a,h}(N^{-4}).
\tag{7.8}
$$

Indeed the remainder per edge after the fourth power is
$O(N^{-6})$, there are $aN$ edges, and the exterior factor is
$N$. At core $i$ the fourth-power numerator is
$Fm^4+(d-o_i)r^4+16e_i=\alpha m^4N+O_{a,h}(1)$.
At tail $k$ it is $q_k+15=\beta N+O_{a,h}(1)$. Hence

$$
\frac N4\sum_{ui\in E}\frac{d_G(u)^4}{d_G(i)^4}
 =\frac1{4N^2}\left(\frac{m^5}{\alpha^3}
                               +\frac n{\beta^3}\right)
                                      +O_{a,h}(N^{-3}).
\tag{7.9}
$$

For a core-optimal allocation (6.9),
$B_i=B_i^0+(4-r^2)\ell_i$ and
$\sum_i\ell_i\delta_i=L(z)\delta_0$. Substitution in (7.6)
and (7.8)--(7.9) gives exactly (7.2), proving the first line of
(7.3).

There are finitely many $j$, values of $d$, and $z$. The tail
remainders $t$ also lie in a fixed finite set. All denominators
stay bounded below by a positive multiple of $N$ for one common
threshold. Taylor's remainders can therefore be bounded by one
constant on all these entries, including all actual minimizing
allocations and all their label assignments. Taking the finite
minimum in the exact identity (6.12) proves the second line of
(7.3).

The rational numbers in (7.2) range over a finite set as $N$
varies: $d$ and $t$ each range over a finite set, and the rest
of the formula is fixed on that data. A positive difference
$\Psi_{j,N}(z)-\Psi_N$ therefore has a positive lower bound
independent of $N$. In (7.3) this strict $N^{-2}$ difference
exceeds the uniform $O(N^{-3})$ error eventually. Thus no such
entry is an exact minimizer. This proves the necessary secondary
selection, without replacing the exact comparison (6.12) by its
second-order truncation. ∎

**Proposition 7.3 (Reachable nonconvex core allocation).** Suppose
$r\ge8$, $n\ge2$, and put $g_0=\gcd(a-1,r)=\gcd(a-1,j)$.
Choose the largest $d<r$ congruent to $n$ modulo $g_0$ and suppose
$d\ge4$. There are infinitely many integer budgets with
$d_{j,N}=d$. At every sufficiently large such budget there are
three actual graphs $G_-,G_0,G_+$ in the original class, with
this same cap, balanced tails and source types, whose endpoint
and omission arrays have the midpoint relation

$$
(e^{(0)},o^{(0)})=
 \tfrac12\bigl((e^{(-)},o^{(-)})+(e^{(+)},o^{(+)})\bigr)
\tag{7.10}
$$

but whose original objectives satisfy

$$
W(G_-)+W(G_+)-2W(G_0)
 =\frac{4(-r^2+6r+11)}{\alpha^3N^2}
                                      +O_{a,h}(N^{-3})<0.
\tag{7.11}
$$

Thus joint convexity in endpoint and omission allocations fails
even on reachable original graph budgets. The stated conditions
hold for every winning cap after a sufficient choice of the
threshold $A_R$ permitted in Definition 1.1. No assertion that
these three graphs are minimizers is needed.

**Proof.** The congruence
$(a-1)N\equiv n-d\pmod r$ is solvable because $g_0$ divides
$n-d$; its solutions form a cofinal residue class modulo $r/g_0$.
On that class take three distinct core labels $1,2,3$ and set

$$
\begin{gathered}
e^{(0)}_1=e^{(0)}_2=1,\quad e^{(0)}_3=n-2,\qquad
o^{(0)}_1=o^{(0)}_2=2,\quad o^{(0)}_3=d-4,\\
e^{(\pm)}=e^{(0)}\pm(1,-1,0,\ldots,0),\qquad
o^{(\pm)}=o^{(0)}\pm(2,-2,0,\ldots,0),
\end{gathered}
\tag{7.12}
$$

with all other entries zero. These are nonnegative integer arrays
of sums $n,d$. Realize each by the construction in Lemma 6.2,
with the same balanced tails. This preserves $N,aN,s$, simplicity,
connectedness and the strict orientation for all sufficiently
large $N$ in that residue.

The calculation (7.4)--(7.9) applies before imposing core
optimality. The part of its second coefficient homogeneous
quadratic in $e_i,o_i$ is

$$
\frac1{\alpha^3}\sum_i
 \left[(3m^2-8)e_i^2
 -2(3m^2-r^2-4)e_io_i+(3m^2-2r^2)o_i^2\right].
\tag{7.13}
$$

For the two changing coordinates in (7.12), evaluating the
midpoint second difference cancels every constant and linear
term. It leaves $4/\alpha^3$ times

$$
(3m^2-8)-4(3m^2-r^2-4)+4(3m^2-2r^2)
 =3m^2-4r^2+8=-r^2+6r+11<0.
\tag{7.14}
$$

All three have the same first coefficient and fourth-power
correction. The uniform remainder therefore proves (7.11).
Equivalently the matrix of the bracketed quadratic in (7.13) has
negative determinant $-(r^2-4)^2$, but (7.12) additionally
verifies an admissible integer direction and an actual-graph
realization; the determinant alone would not establish those.

Finally $g_0\le j$, so this largest reachable $d$ satisfies
$d\ge r-g_0\ge a-1$. The bounds on winning indices used in
Lemma 2.2 give $j=O_R(1)$, whereas $h\ge(7/2)\sqrt a$.
Thus $r\ge8$, $n=h+1-j\ge2$, and $d\ge4$ all hold after a
sufficient inherited threshold. The obstruction concerns the
coupled allocation problem; it neither invalidates the scalar
tail convexity nor presupposes global convexity of $H$. ∎

## 8. Refined periodic templates and exact ties

**Definition 8.1 (A sufficient refined period and analytic
allocation functions).** Set

$$
P=\operatorname{lcm}_{j\in J_*}(r_j n_j),
\qquad r_j=a+j-1,\quad n_j=h+1-j.
\tag{8.1}
$$

This is a sufficient period, with no claim of leastness. It is a
multiple of $P_*$ in (5.5), and $\alpha_jP,\beta_jP$ are
integers. Fix $\rho\in\{0,\ldots,P-1\}$. For each
$j\in\mathcal J_\rho$, the integers $d=d_{j,N}$ and $t$ in
(6.1) are constant on $N\equiv\rho\pmod P$. Here
$\mathcal J_\rho$ denotes the common set $\mathcal J_N$ on that
residue, not a graph assertion at a small budget $N=\rho$.
Define the rational offsets

$$
v_- =\gamma-\frac tn,\qquad v_+=\gamma+1-\frac tn,
\quad
a_k(u)=\alpha+\delta_k u,\quad a_0(u)=\alpha+\delta_0u,
\quad c_\pm(u)=\beta+v_\pm u.
\tag{8.2}
$$

For $p>0$ and $a(0)>0$ use the analytic germ

$$
R_p(a,u)=\frac{\sqrt{a(u)^2+p^2u^2}}{a(u)}-1,
\tag{8.3}
$$

where the square root is the positive one near $u=0$. For
$z\in\mathcal Z_{m,n,d}$ define

$$
\begin{aligned}
\mathscr A_{\rho,j,z}(u)=\frac2{u^2}\Bigg[&
 \sum_{i\in C}\left\{
 (\alpha+\varphi u)R_m(a_i,u)
   +u(d-z_i^-)R_r(a_i,u)+u z_i^+R_2(a_i,u)\right\}\\
 &+u L(z)\{R_2(a_0,u)-R_r(a_0,u)\}\\
 &+(n-t)\{(\beta+(v_--1)u)R_1(c_-,u)
                                         +uR_2(c_-,u)\}\\
 &+t\{(\beta+(v_+-1)u)R_1(c_+,u)
                                         +uR_2(c_+,u)\}\Bigg].
\end{aligned}
\tag{8.4}
$$

The apparent singularity at $u=0$ is removable because every
$R_p$ vanishes to order at least two. This is a real analytic
algebraic function near zero, with rational Taylor coefficients.
For the integers in this residue and sufficiently large $N$,

$$
\mathscr A_{\rho,j,z}(1/N)=\mathcal A_{j,N}(z).
\tag{8.5}
$$

Define $B_s=(6s+5)2^{6s+4}$ and the finite Taylor vector

$$
\mathbf c_{\rho,j,z}
 =\left([u^k]\mathscr A_{\rho,j,z}(u)\right)_{k=0}^{B_s}.
\tag{8.6}
$$

Order these rational vectors lexicographically from the constant
coefficient upward. Let $\mathcal W_\rho$ be all pairs $(j,z)$
whose vector is least among the finite set for that residue.
The first three entries are $M,\chi_\rho,\Psi_{j,\rho}(z)$
by Theorem 7.2. Formula (8.6) also retains every later coefficient
needed for exact selection, rather than declaring all secondary
ties to be exact ties.

**Theorem 8.2 (Eventual refined-periodic exact optimizer
templates).** For every fixed admissible $a,h$ there is a finite
threshold such that, on each integer residue $\rho$ modulo $P$
and above that threshold, the pairs attaining (6.12) are exactly
$\mathcal W_\rho$. Consequently every exact optimizer is given
by Theorem 6.4's reconstruction using these pairs, and every
such reconstruction is an exact optimizer.

All members of $\mathcal W_\rho$ have identical exact value
functions near $u=0$. They remain tied at every sufficiently
large budget in that residue. The finite data consisting of the
partition, $z$, the choices (6.9), endpoint assignments and the
$t$ high-degree tail labels give all optimizer templates; only
$F$ and the tail-singleton multiplicities grow with $N$, affinely
on that residue. Source-label permutations give all labelled
preimages. No least threshold, least period, or uniform
joint-growth estimate is asserted.

**Proof.** A shift of $N$ by $P$ leaves $d$ fixed. It increases
$F$ by $\alpha P$, $Q$ by $n\beta P$, and $b$ by $\beta P$,
so it leaves $t$ fixed as well. This proves all the residue
statements in Definition 8.1. Substituting $u=1/N$ in (8.3)
and (8.4) proves (8.5) directly from (6.5). Analyticity follows
since $\alpha,\beta>0$, and the expansion of the positive square
root about a positive rational square has rational coefficients.

For completeness, a finite algebraic bound justifies detecting
exact ties by (8.6). For any pair of the functions (8.4), expand
their last core term into its two summands and omit every
zero-coefficient term. Each function has at most
$3m+2n+2\le3s+2$ radical terms. If their difference is $D(u)$,
it has the form

$$
D(u)=\frac2{u^2}\sum_{l=1}^{K}w_l(u)
 \left(\frac{\sqrt{p_l(u)}}{a_l(u)}-1\right),
\quad K\le6s+4,
\tag{8.7}
$$

where $w_l,a_l$ are polynomials of degree at most one with
rational coefficients, $a_l(0)>0$, and
$p_l=a_l^2+k_l^2u^2$ has degree at most two. Negative coefficients
of $w_l$ are allowed. If $K=0$ the difference is identically
zero. Otherwise put

$$
\begin{aligned}
Z(u)&=\frac{u^2D(u)}2\prod_{l=1}^K a_l(u)
       =A_0(u)+\sum_{l=1}^K A_l(u)\sqrt{p_l(u)},\\
\deg A_0&\le K+1,\qquad \deg A_l\le K.
\end{aligned}
\tag{8.8}
$$

Form the monic polynomial in $Y$

$$
\Pi(u,Y)=\prod_{\epsilon\in\{-1,1\}^K}
 \left(Y-A_0(u)-\sum_{l=1}^K
                          \epsilon_lA_l(u)\sqrt{p_l(u)}\right).
\tag{8.9}
$$

This belongs to $\mathbb Q[u,Y]$: before substitution, changing
the sign of any formal radical permutes the factors, so only
even powers of each radical occur, and their squares are the
polynomials $p_l$. This argument does not require the radicals
to be algebraically independent. A coefficient of (8.9) is a
sum of products of at most $2^K$ expressions of polynomial
radical degree at most $K+1$, where a radical of a quadratic has
degree weight one. Substitution of even radical powers therefore
gives degree in $u$ at most

$$
(K+1)2^K\le (6s+5)2^{6s+4}=B_s.
\tag{8.10}
$$

Delete the largest power of $Y$ dividing $\Pi$, obtaining
$\Pi_0$ with nonzero constant coefficient $\Pi_0(u,0)$.
This polynomial is still nonzero, since (8.9) is monic.
If the analytic function $Z$ is not identically zero,
$\Pi(u,Z(u))=0$ and cancellation in the ring of analytic germs
gives $\Pi_0(u,Z(u))=0$. It follows that

$$
\operatorname{ord}_0 Z
 \le \operatorname{ord}_0\Pi_0(u,0)
 \le \deg_u\Pi_0(u,0)\le B_s.
\tag{8.11}
$$

For the first inequality, write the polynomial equation as its
constant coefficient plus terms each divisible by $Z$; their
vanishing orders are at least that of $Z$. If $\Pi_0$ has
no positive $Y$ powers, the nonzero-$Z$ case cannot occur at
all. Since every $a_l(0)>0$, (8.8) gives
$\operatorname{ord}_0Z=\operatorname{ord}_0D+2$ when $D$ is
nonzero. Thus a nonzero difference cannot have all coefficients
through order $B_s$ zero. This proves that equal vectors in
(8.6) are equivalent to identical analytic value functions near
zero. It supplies a finite equality test even when formal sign
choices in (8.9) create spurious zero conjugates; deleting the
$Y$ factors handles precisely that possibility. The large bound
is sufficient, with no claim of efficiency or optimality.

For two unequal vectors, let $k$ be their first different
coordinate. The exact difference is $c u^k+O(u^{k+1})$ with
$c\ne0$, so for sufficiently small positive $u$ its sign is the
sign of $c$. Hence the lexicographic comparison is the exact
comparison at every sufficiently large $N$ in the residue.
There are finitely many pairs of functions and finitely many
residues. One threshold suffices for every strict comparison;
identical functions remain exactly tied. Therefore the exact
minimum in (6.12) selects precisely $\mathcal W_\rho$.

For each selected $z$, all the choices of $\ell$ in (6.9) have
the same exact value, not only the same Taylor coefficients:
their degrees at $I_0$ are equal and (6.10) depends only on the
sum $L$. The same is true for the tail-label and endpoint-map
choices in Theorem 6.4 by (6.6). Each of these sets is finite
independently of $N$ on the residue. Counts $F$ and $b$ change
affinely by the increments already computed. The exhaustive
reconstruction now proves every template and preimage claim.

The new graph-specific deductions are the exact allocation
relation (6.12), its coupled equality conditions, the full
secondary energy (7.2), the reachable obstruction (7.11), and
the exact eventual selection just proved. They reuse Theorem
1.3's all-domain source exclusion and the common-law equality
theorem cited there, rather than reproving either as new content.
Scalar convexity, Taylor expansion and polynomial sign
symmetrization are mature intermediate tools; the graph budgets,
allocation formulas and reconstruction are the additional
relations. The original CDSO normalization and fixed-cyclomatic
motivation are from Albalahi--Das--Ali--Barman--Hamza,
[arXiv:2510.24809v1](https://arxiv.org/html/2510.24809v1), §1
and §4, also DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176).
Possible technical overlap with the full text of Zhao--Zhao,
*Extremal values with respect to vertex-degree-based topological
indices in unicyclic and bicyclic graphs*, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
remains unassessed. Its abstract does not resolve that question
and is not a premise of these proofs; no worldwide-priority
claim is attached to these repo-derived deductions. ∎

**Open problem 8.3 (Thresholds and changing budgets).** Determine
least sufficient source thresholds or least refined periods for
the exact allocation relation, and uniform estimates when $a,h,N$
grow together. Determine the extremum when the sink count is
also allowed to vary. Theorems 6.4--8.2 keep $a,h$ fixed in
Definition 1.1; their finite allocation sizes, comparison bounds
and thresholds can depend on these integers. They do not exchange
that quantifier order, and they make no extremal assertion for
graphs outside the prescribed bipartite orientation and budgets.

## 追加锚（本行以下为增补区）


## 9. A polynomially uniform first-connection window

The fixed-parameter estimates above leave one quantifier gap in Open
problem 8.3. This section closes a deliberately deep part of that gap.
The sink number remains the prescribed value \(s=a+1+h\), and every graph
below is still finite, simple, connected, bipartite with independent source
and sink parts, has exactly \(N\) sources and \(aN\) edges, and satisfies the
strict edge inequality (1.3). No support condition, marginal floor, or phase
separation is added.

### 9.1 Uniform bookkeeping for the high-ratio window

Fix a finite \(R\ge4\), and put

$$
J_R=\left\lceil4(R^2+10)\right\rceil,\qquad
K_R=2^{40}(R+J_R+10)^{40}.
\tag{9.1}
$$

Let \(A_R^{\mathrm{cap}}\) be a threshold for the already proved uniform
cap localization in Growing Lemmas 15.2--15.3, with every \(O_R(\cdot)\)
there replaced by the displayed rational bounds in those lemmas. Thus
\(A_R^{\mathrm{cap}}\) depends on \(R\) alone and does not depend on a fixed
pair \((a,h)\). Define

$$
A_R=\max\{A_R^{\mathrm{cap}},(8K_R)^2,8K_R\},\qquad
C_R=K_R^9,\qquad D_R=2K_R^{20}.
\tag{9.2}
$$

The following estimates are the uniform numerical ledger used below.

**Lemma 9.1 (Polynomial cap and price bounds).** If

$$
a\ge A_R,\qquad \frac72\sqrt a\le h\le R\sqrt a,
\tag{9.3}
$$

then every winning index \(j\in J_*\) satisfies \(2\le j\le J_R\), and,
with \(m,r,n,\alpha,\beta\) as in (1.6),

$$
\begin{gathered}
a\le m\le2a,\qquad a\le r\le2a,\qquad
\frac12\le\alpha\le1,\\
2\sqrt a\le n\le(R+2)\sqrt a,\qquad
\frac1{K_Ra^{3/2}}\le\beta\le\frac{K_R}{a^{3/2}},\qquad
\frac1{K_R}a^{3/2}\le\eta\le K_Ra^{3/2},\\
M(a,h)\le K_Ra^3,\qquad |\chi_{j,N}|\le K_Ra^{7/2},
\end{gathered}
\tag{9.4}
$$

and every exceptional type price in (2.1) is either zero on the cap
support or at least \(a^2/K_R\). If \(D_*(a,h)\) is a common positive
integer denominator for all the rational prices \(\rho_j(L,B)\), all
\(\chi_{j,N}\), and \(\chi_N\), it may be chosen with

$$
D_*(a,h)\le K_Ra^6.
\tag{9.5}
$$

**Proof.** Growing Lemma 15.2 gives the finite index range and the strict
margin \(n^2/(j^2a)>5/2\) after increasing \(A_R^{\mathrm{cap}}\). The
bounds on \(m,r,n,\alpha,\beta,\eta\) then follow directly from (1.6),
\(h\le R\sqrt a\), and \(a\ge(8K_R)^2\). Substitution in (1.8) and
(2.1), using \(n^2/(j^2a)>5/2\), gives

$$
rc_j\ge a^3/K_R,\qquad b_j\ge a^3/K_R,
\tag{9.6}
$$

after the same threshold increase; (2.3)--(2.5) then give the stated
lower bound for every nonzero price. The formula (1.5) gives
\(M=S_j\le K_Ra^3\), while (1.8) gives the bound for \(\chi_{j,N}\)
because \(n=O_R(\sqrt a)\), \(b_j=O_R(a^3)\), \(d_{j,N}<r=O(a)\),
and \(c_j=O_R(a^2)\). Finally, clear the denominators in (1.6),
(1.8), and (2.1). Their factors are among \(j\), \(r\), \(n\), and
\(a-1\), each bounded by \(K_Ra\); multiplying the displayed factors
gives the safe bound (9.5). No enumeration of labelled subsets is used.
\(\square\)

**Lemma 9.2 (Uniform realization and full-class lower estimate).** Under
(9.3), for every integer \(N\ge K_R^{20}a^{20}\) there is an actual graph in
\(\mathfrak G_N(a,h)\) with a winning \(j\) satisfying
\(\chi_{j,N}=\chi_N\) and

$$
W(G)\le M+\frac{\chi_N}{N}+\frac{K_R^9a^{17}}{N^2}.
\tag{9.7}
$$

For every graph \(G\in\mathfrak G_N(a,h)\),

$$
W(G)\ge M+\frac{\chi_N}{N}-\frac{K_R^9a^{17}}{N^2}.
\tag{9.8}
$$

The lower estimate is over the full original graph class.

**Proof.** Choose \(j\) with \(\chi_{j,N}=\chi_N\), set \(d=d_{j,N}\), and
use the construction of Lemma 4.2: \(n\) distinct degree-two
core--tail connectors, \(d\) missing-one core sources, full-core sources
and balanced tail singletons. The residue definition of \(d\) makes

$$
F=\frac{(a-1)N-n-(r-1)d}{r},\qquad
T=N-F-n-d
\tag{9.9}
$$

integers. From (9.4) and \(N\ge K_Ra^{20}\), \(F>\alpha N/2\) and
every tail degree is \(>\beta N/2\); since \(s\le K_Ra\), all source
degrees are strictly smaller than their adjacent sink degrees. The
construction therefore lies in the original class for every integer
residue, with no congruence restriction on \(N\).

For this graph the degree-ratio expansion (9.4)--(9.5) and (9.9) give
the fixed formulas (4.8) with an error bounded by \(K_R^3a^{12}/N^2\).
For example, the fourth-order remainder is bounded by

$$
N(aN)\left(\frac{2K_Ra}{\beta N}\right)^6
\le K_R^9a^{17}N^{-4}
\le K_R^9a^{17}N^{-2},
\tag{9.10}
$$

and the rational denominator expansions in (7.6) are smaller than the
same \(K_R^9a^{17}N^{-2}\) envelope. This proves (9.7).

For the lower bound, first consider a graph with value no larger than the
right side of (9.7). By (9.4), this is a sublevel \(W\le2K_Ra^3\).
The bridge (3.10) therefore gives \(y_i\ge K_R^{-1}a^{-3}\). Inserting
this bound and \(s\le K_Ra\) into (3.11) yields

$$
0\le H(x_G)-W(G)\le K_R^9a^{17}N^{-2}.
\tag{9.11}
$$

Growing Lemma 15.3, with the same explicit denominator bounds, places
the law in one of the cap neighborhoods; Growing Theorem 15.5 identifies
the corresponding sublevel minimum with \(M(a,h)\). On that neighborhood,
the quantitative form of (3.2), together with the price bound
\(P(x)\ge(a^2/K_R)\varepsilon\) from Lemma 9.1, gives
\(\varepsilon\le K_R^3a^{3/2}/N\): indeed the upper construction gives
\(H(x_G)-M\le K_R^3a^{7/2}/N+K_R^9a^{17}/N^2\), and the second term is
absorbed by \(N\ge K_R^{20}a^{20}\). The Taylor estimate (3.2), whose second
derivatives are bounded by \(K_Ra^{9/2}\) on these neighborhoods, then
gives

$$
W(G)\ge M+\frac{\mathcal P_j(G)}N-\frac{K_R^9a^{17}}{N^2}.
\tag{9.12}
$$

Here \(j\) is the actual winning cap of that neighborhood. Lemma 4.1
applies to every source type, without a support restriction, and gives
\(\mathcal P_j(G)\ge\chi_{j,N}\ge\chi_N\). A graph above the sublevel
already exceeds (9.8), while a graph in it satisfies (9.12), proving
(9.8) over the whole class. The powers in (9.10)--(9.12) are enlarged
to \(17\) only to use one envelope for all core and tail denominators.
\(\square\)

### 9.2 The uniform theorem and source exclusion

**Theorem 9.3 (Polynomially uniform first connection correction).** Let
\(R\ge4\) be finite and use (9.1)--(9.2). Put

$$
p=50,\qquad q=40.
\tag{9.13}
$$

For every pair in (9.3) and every integer

$$
N\ge\left\lceil D_Ra^p\right\rceil,
\tag{9.14}
$$

the original class is nonempty and

$$
\left|V_N(a,h)-M(a,h)-\frac{\chi_N(a,h)}N\right|
\le\frac{C_Ra^q}{N^2}.
\tag{9.15}
$$

Moreover every exact minimizer \(G\) has a cap partition and a law-winning
index \(j\in J_*\) with \(\chi_{j,N}=\chi_N\), and its source
neighborhoods are exactly the three types in Theorem 1.3:

1. one two-element core--tail connector for each of the \(n=h+1-j\)
   labelled tails;
2. exactly \(d_{j,N}\) missing-one core sources \(C\setminus\{i\}\);
3. full-core sources \(C\) and singleton tail sources for every remaining
   source.

All ties between winning laws, all price ties, every integer residue of
\(d_{j,N}\), and every feasible endpoint, omission, and balanced-tail
allocation remain in the statement. The theorem does not choose a least
threshold or least period and does not optimize over a variable sink count.

**Proof.** Since \(a\ge1\), (9.7)--(9.8) imply (9.15) with \(q=40\)
whenever (9.14) holds, after the harmless enlargement in (9.2). In
particular the explicit construction in Lemma 9.2 proves nonemptiness.

It remains to prove the source assertion. Let \(G\) be an exact minimizer
and use the cap \(j\) supplied by (9.12). Combining (9.7), (9.12), and
\(\mathcal P_j(G)\ge\chi_{j,N}\ge\chi_N\) gives

$$
0\le\mathcal P_j(G)-\chi_N
\le\frac{2K_R^9a^{17}}N.
\tag{9.16}
$$

By (9.5), a strict inequality on the left is at least
\(D_*^{-1}\ge K_R^{-1}a^{-6}\). The threshold (9.14), with
\(D_R=2K_R^{20}\), makes the right side of (9.16) smaller than this gap.
Therefore \(\mathcal P_j(G)=\chi_N\), and both inequalities
\(\mathcal P_j(G)\ge\chi_{j,N}\ge\chi_N\) are equalities. Lemma 4.1
now gives exactly the three source types listed above. Its equality proof
also gives one connector for each tail and the residue count
\(d_{j,N}\), so no source support or phase assumption has entered. The
argument treats the finite set of law ties and every residue separately
inside one common bound; it never replaces a joint realization by
independent marginal optima. \(\square\)

The explicit exponents \(p=50\) and \(q=40\) are intentionally wasteful.
They are chosen so that the polynomial denominator, localization, and
degree-ratio estimates are all dominated by one threshold. The result is
therefore a genuine common-growth theorem in the original graph domain,
but it does not assert that \(50\) is least, that the threshold in (9.14)
is least, or that the bound remains valid near \(N\asymp a^2\). Open
problem 8.3 still contains the least-threshold and least-period questions,
the smaller transition scales, the exact later analytic template choice,
and the extremum when the number of sinks varies.

The cap formulas and all graph constructions used here come from Growing
Definition 9.1, Lemma 9.2, Lemmas 15.2--15.3 and Theorem 15.5. The
nonlinear normalization is the maximum-endpoint normalization in (1.4),
with no \(1/\sqrt2\) factor. The original index source is
Albalahi--Das--Ali--Barman--Hamza, *On the hyperbolic Sombor index and its
counterpart*, Discrete Math. Lett. 16 (2025), 108--115,
[DOI 10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176),
§1 and §4. The proof above is a repository derivation from those
definitions and the cited Growing results; it makes no worldwide novelty
claim. Possible full-text overlap with Zhao--Zhao, *Extremal values with
respect to vertex-degree-based topological indices in unicyclic and
bicyclic graphs*, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
remains unassessed.
