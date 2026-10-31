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


## 9. Polynomial uniformity on a positive-excess sublevel

All laws and graphs in this section have exactly the domains of
Definition 1.1. In particular every nonempty source neighborhood remains
allowed. Fix a finite $R\ge4$, put

$$
C_0=R^2+10,\qquad J=\lceil4C_0\rceil,\qquad
\kappa=h/\sqrt a\in[7/2,R],
\tag{9.1}
$$

and increase an $R$-only lower threshold for $a$ when specified below.
All constants with subscript $R$ are positive and finite and depend only
on this fixed $R$. Every $O_R$ estimate is uniform in $h$, the law, its
labels and the bounded indices under discussion. We may assume
$s\le2a$ and $h\ge J$. A branch index selected from an approximate law
is not assumed to belong to $J_*$.

**Lemma 9.1 (The relaxed-sublevel bootstrap).** For every sufficiently
large $a$ depending only on $R$, every law with $H(x)\le M+1$ has a
partition $C\dot\cup D=[s]$ with the following properties. Write

$$
\begin{gathered}
|C|=m=a+j,\quad r=m-1,\quad |D|=n=h+1-j,\\
u_c=j/r,\quad \alpha=(a-1)/r,\quad
\beta=j/(rn),\quad \eta=\beta^{-1},\\
t_k=y_k\ (k\in D),\quad u=\sum_{k\in D}t_k,\quad
c=\min_{i\in C}y_i,\quad \delta=\max_{k\in D}t_k.
\end{gathered}
\tag{9.2}
$$

Then $2\le j\le J$, $\kappa^2/j^2>5/2$,
$u>\ell_j=(j-1)/(m-2)$, and

$$
u=O_R(a^{-1/2}),\qquad
c\ge1-O_R(a^{-1/2}),\qquad
\delta\le\beta(1+O_R(a^{-1/4})).
\tag{9.3}
$$

The partition is the threshold partition determined by the actual
marginals. There is no hypothesis on the positive support of $x$.

**Proof.** Growing Lemma 7.1 applies on the enlarged sublevel: the
comparison $S_1$ gives
$M+1\le S_1+1\le a^3+C_0a^2$ eventually, uniformly in (9.1).
Its threshold is $b/a$, with $b=4C_0$, and its core floor is
$c_0=(8C_0+1)^{-1}$. In particular it gives $1\le j\le J$,
$t_k<b/a$, $y_i\ge c_0$ on $C$, $u=O_R(a^{-1/2})$, and, for
$v=a\mathbb P(T\cap D\ne\varnothing)$,

$$
\begin{gathered}
v\ge c_R>0,\qquad v\le j+O_R(a^{-1/2}),\\
\frac{H-B_0(a)}{a^2}
\ge\kappa^2/v+2v+2j-2-O_R(a^{-1/2}).
\end{gathered}
\tag{9.4}
$$

This invocation uses the stated $a^3+C_0a^2$ sublevel of Growing
Lemma 7.1, rather than the exact-minimum sublevel of Growing Lemma 15.2.
For $1\le k\le J$, direct expansion of $S_k$ gives

$$
\frac{S_k-B_0(a)}{a^2}=g_k(\kappa)+O_R(a^{-1/2}),\qquad
g_k(\kappa)=\kappa^2/k+4k-2.
\tag{9.5}
$$

Let $\mathcal U(\kappa)=\min_{k\le J}g_k(\kappa)$ and
$\phi_j(\kappa)=\min_{0<w\le j}
(\kappa^2/w+2w+2j-2)$. Growing Theorem 7.2's scalar evaluation
identifies $\min_j\phi_j=\mathcal U$ on this interval. Clipping
$v$ to $w=\min(v,j)$ in (9.4), and using
$H\le M+1\le\min_{k\le J}S_k+1$, gives

$$
0\le\phi_j(\kappa)-\mathcal U(\kappa)
\le O_R(a^{-1/2})+a^{-2}.
\tag{9.6}
$$

At a zero of this difference in $[7/2,R]$, the scalar phase formula
excludes $j=1$. For $j=2$ it gives $\kappa^2/j^2\ge49/16$;
for $j\ge3$ it gives $\kappa^2/j^2\ge4(j-1)/j\ge8/3$.
Consequently the minimum of $\phi_j-\mathcal U$ on the finite union

$$
\{(\kappa,1):7/2\le\kappa\le R\}
\ \cup\!
\bigcup_{j=2}^J
\{(\kappa,j):7/2\le\kappa\le R,\ \kappa^2/j^2\le5/2\}
\tag{9.7}
$$

is a positive $R$-only number. The functions are explicit continuous
functions on these compact sets; empty sets are omitted. Choosing $a$
so that the right side of (9.6) is smaller than this number proves the
index and margin assertions. This compactness concerns a fixed ratio
interval and a bounded finite index set, not laws at fixed $a,h$.

For this same actual $j$, use $H\le S_j+1$ in (9.4)--(9.5).
On $0<w\le j$, the derivative of $\kappa^2/w+2w$ is at most
$-1/2$. Hence $j-w=O_R(a^{-1/2})$, and
$v=j+O_R(a^{-1/2})$. Since $au\ge v$ and
$a\ell_j=j-1+O_R(a^{-1})$, this proves $u>\ell_j$.

We give the residual bootstrap on this enlarged sublevel explicitly.
For the same law set

$$
\begin{gathered}
B=|T\cap D|,\quad L=|T\cap C|,\quad K=L+B,\quad A=\{B>0\},\\
\mathfrak a=mr(2m-1),\quad \mathfrak b=3m^2-3m+1,\quad d=2m-1,\\
Q(l)=(m-l)(r-l)(2m-1+l)=\mathfrak a-\mathfrak b l+l^3,\\
f_u(y)=r^2/y-d(j-1+u)/y^2,\quad \bar y=(a-u)/m,\\
\mathcal S_f=\sum_{i\in C}f_u(y_i)-m f_u(\bar y),\\
\mathcal B(w)=\frac{r^2m^2}{a-w}
             -\frac{dm^3(j-1+w)}{(a-w)^2},\qquad
\mathcal A(u)=\frac{\mathcal B(0)-\mathcal B(u)}u,\\
\gamma=\eta^2-\mathfrak a+\mathcal A(u).
\end{gathered}
\tag{9.8}
$$

On $c_0\le y\le1$, differentiation gives $f_u''(y)\ge a^2$
eventually. Also, uniformly on $0\le w\le u$,

$$
\begin{gathered}
\mathcal B'(w)=-a^2+O_R(a),\qquad
\mathcal A(u)=a^2+O_R(a),\\
z_*:=\frac{n^2}{j^2a}=\frac{\kappa^2}{j^2}+O_R(a^{-1/2}),\qquad
\eta^2/a^3=z_*+O_R(a^{-1}),\\
(\mathfrak a-\mathcal A(u))/a^3=2+O_R(a^{-1}),\qquad
\gamma\ge a^3/4,\quad \gamma=O_R(a^3).
\end{gathered}
\tag{9.9}
$$

The incidence identities (Growing (15.12)--(15.14)) are algebraic
identities and inequalities for this actual law. With
$I_i=\mathbf1_{i\in T}$ and

$$
\rho_i=(1-I_i)d(r-L)+I_i(m-L)(m-L-1)\ge0,
\tag{9.10}
$$

they read

$$
\begin{gathered}
\sum_{i\in C}\rho_i=Q(L),\qquad
\mathbb E\rho_i=\mathbb E[L^2I_i]-r^2y_i+d(j-1+u),\\
H\ge H_D+\mathcal B(u)+\mathbb E Q(L)+\mathcal S_f,\\
ru-j\le m\mathbb E[B-1;A]+\mathbb E[L;A].
\end{gathered}
\tag{9.11}
$$

Here $H_D=\mathbb E[K^2\sum_{k\in T\cap D}t_k^{-2};A]$.
Nonnegativity in (9.10) follows from the consecutive integer factors,
including $L=m$. For $K\ge L$, dropping the nonnegative difference
$K^2-L^2$ and using $y_i^{-2}\ge1$ proves the middle line of
(9.11). Strong Jensen gives
$\mathcal S_f\ge(a^2/2)\sum_{i\in C}(y_i-\bar y)^2$.

For $B>0$ define

$$
\begin{aligned}
V_T&=\sum_{k\in T\cap D}t_k^{-1},\\
\mathcal G_T
&=K^2\sum_{k\in T\cap D}t_k^{-2}+Q(L)-\mathcal A(u)B
  -2\eta V_T+\gamma B-\frac\gamma r\{m(B-1)+L\}.
\end{aligned}
\tag{9.12}
$$

The actual marginal identity gives $\mathbb E[V_T;A]=n$.
Substitution in (9.11), using $\gamma\ge0$, yields

$$
\begin{gathered}
H\ge E_j+\mathbb E[\mathcal G_T;A]
              +\mathbb E[Q(L);A^c]+\mathcal S_f,\\
E_j=\mathcal B(0)+2\eta n-j\gamma/r=S_j+O_R(a).
\end{gathered}
\tag{9.13}
$$

The last equality follows from
$\mathcal B(0)=a^3+2ja^2+O_R(a)$,
$j(\mathfrak a-\mathcal A(u))/r=2ja^2+O_R(a)$ and
$m^3r/(a-1)=a^3+4ja^2+O_R(a)$.
For a tail singleton, $\mathcal G_{\{k\}}=(t_k^{-1}-\eta)^2$.
For every other type with $B>0$, completing reciprocal squares gives

$$
\mathcal G_T\ge
\eta^2(1-B/K^2)-\mathcal A(u)(B-1)
-\mathfrak b L+L^3-\frac\gamma r(K-1).
\tag{9.14}
$$

If $2\le K\le\sqrt a$, then $B/K^2\le1/2$ and all negative
terms after the first are $O_R(a^{5/2})$. Thus (9.14) is at least
$a^3/4$ eventually. If $K>\sqrt a$, the actual threshold
$t_k<b/a$ gives $K^2t_k^{-1}>4\eta$ eventually. Using $Q(L)\ge0$
in (9.12) instead gives

$$
\mathcal G_T\ge\frac{BK^2a^2}{2b^2}-\mathcal A(u)B
            +\gamma\left(1-\frac{K-1}r\right).
\tag{9.15}
$$

For $K\le m$ the last term is nonnegative; for $K>m$ its negative
part is at most $\gamma n/r=O_R(a^{5/2})$, whereas the first
term then has order at least $a^4$. In both cases (9.15) is at
least $a^3/(4b^2)$ eventually. This covers every $K\le s$.

All three residuals in (9.13) are therefore nonnegative. Since
$H\le M+1\le S_j+1$, their sum is $O_R(a)$; the added constant
one has been retained in this comparison. It follows that

$$
p_2:=\mathbb P(A,K\ge2)=O_R(a^{-2}),\qquad
\sum_{i\in C}(y_i-\bar y)^2=O_R(a^{-1}).
\tag{9.16}
$$

As $\bar y=1-O_R(a^{-1})$, this gives the core bound in (9.3).
Put $x_k=x_{\{k\}}$. Then $0\le t_k-x_k\le p_2$.
If $w=\eta t_k\ge1$, we have $x_k\ge t_k/2$ eventually,
since $\eta p_2=O_R(a^{-1/2})$. Its singleton square implies

$$
\frac\eta2\frac{(w-1)^2}{w}
\le x_k(t_k^{-1}-\eta)^2\le O_R(a).
\tag{9.17}
$$

Thus $(w-1)^2/w=O_R(a^{-1/2})$, so $w-1=O_R(a^{-1/4})$.
Labels with $t_k<\beta$ already obey the asserted upper bound.
This proves (9.3) for the positive-excess sublevel. ∎

**Theorem 9.2 (Full-law polynomial cap stability, including near
branches).** There are $A_R,B_R$ such that for every integer pair in
(9.1) with $a\ge A_R$ and every original law with

$$
0\le\tau:=H(x)-M\le1,
\tag{9.18}
$$

the actual partition of Lemma 9.1 has an index $2\le j\le J$ and
satisfies $0\le S_j-M\le\tau$. For its notation (9.2), let
$\varepsilon=\sum_{T\text{ exceptional}}x_T$, with exceptional
meaning every type except $C$ and the singletons in $D$. Then

$$
\begin{gathered}
e:=\mathbb E[K-1;A]\le\tau/a^3,\qquad
|u-u_c|\le4\tau/a^3,\qquad
\varepsilon\le16\tau/a^2,\\
|y_i-\alpha|\le3\varepsilon\quad(i\in C),\\
\sum_{k\in D}(t_k-u/n)^2\le8\beta^3\tau,\qquad
\max_{k\in D}|t_k-\beta|
\le\sqrt{8\beta^3\tau}+\frac{4\tau}{na^3},\\
\|x-x^{j,*}\|_1\le B_R a^{-2}\sqrt\tau.
\end{gathered}
\tag{9.19}
$$

Here $x^{j,*}$ is the actual cap law on this partition, even when
$j$ is a nonwinning index. In particular every tail marginal is
between $\beta/2$ and $3\beta/2$ after increasing $A_R$.
There is a quantitative winning-index implication:

$$
\tau\le\frac1{2J^2a}\quad\Longrightarrow\quad j\in J_*.
\tag{9.20}
$$

**Proof.** We retain the Jensen losses in the strict-payment argument.
Use $\mathfrak a,\mathfrak b,d,\rho_i$ from (9.8)--(9.10), and put

$$
\begin{gathered}
\mathfrak c=rd,\qquad
b(u)=d((m-2)u-(j-1))>0,\\
F_j(u)=\frac{n^2}{u}+\frac{r^2m^2}{a-u}
                    +\frac{m^3b(u)}{(a-u)^2},\\
P_j=-F_j'(u_c),\qquad
\Lambda=3/\delta^2-\max\{\mathfrak a,\mathfrak b\}/c^2.
\end{gathered}
\tag{9.21}
$$

On $A$, each $\mathfrak c B-\rho_i\ge0$, and

$$
\sum_{i\in C}(\mathfrak c B-\rho_i)
=\mathfrak a(B-1)+\mathfrak b L-L^3
\le\max\{\mathfrak a,\mathfrak b\}(K-1).
\tag{9.22}
$$

Indeed for $I_i=0$ the left summand is
$d\{r(B-1)+L\}$; for $I_i=1$ it is
$\mathfrak c(B-1)+r^2+dL-L^2\ge0$ for $1\le L\le m$.
Off $A$ every $\rho_i\ge0$. Weight these signed inequalities
by $y_i^{-2}\le c^{-2}$, and use
$B(K^2-1)\ge3(K-1)$ on $A$. The exact incidence identity for
$H$ then gives

$$
H\ge\sum_{k\in D}t_k^{-1}
       +\sum_{i\in C}\{r^2/y_i+b(u)/y_i^2\}+\Lambda e.
\tag{9.23}
$$

For example this identity follows directly by substituting
$\mathbb E\rho_i=\mathbb E[L^2I_i]-r^2y_i+d(j-1+u)$,
and keeping the nonnegative core term from $K^2-L^2$.

Let $\bar t=u/n$. The two Jensen losses in (9.23) can be
retained as

$$
\begin{gathered}
H\ge F_j(u)+\Lambda e+\mathcal J_D
                   +a^2\sum_{i\in C}(y_i-\bar y)^2,\\
\mathcal J_D=\sum_{k\in D}t_k^{-1}-n^2/u
=\sum_{k\in D}\frac{(t_k-\bar t)^2}{\bar t^2t_k}
\ge\frac1{8\beta^3}\sum_{k\in D}(t_k-\bar t)^2.
\end{gathered}
\tag{9.24}
$$

The last bound uses $\bar t\le\delta\le2\beta$ from Lemma 9.1.
For the core loss, the second derivative of
$r^2/y+b(u)/y^2$ is at least $2a^2$ on $0<y\le1$.

The scalar function in (9.21) is strictly convex on
$\ell_j<u<a$: differentiation gives Growing (15.22), with all
four displayed terms positive. At $u_c$ its exact derivative is

$$
F_j'(u_c)=-\frac{n^2r^2}{j^2}
 +\frac{r^2(2mr^2+2m-1)}{(a-1)^2}.
\tag{9.25}
$$

By (9.9), $P_j/a^3=z_*-2+O_R(a^{-1})$.
The bounds (9.3) therefore give, uniformly over all surviving indices,

$$
P_j\ge a^3/4,\qquad
\frac{\Lambda-(m/r)P_j}{a^3}
\ge2z_*-O_R(a^{-1/4})\ge1.
\tag{9.26}
$$

The original mean also gives $(u-u_c)_+\le(m/r)e$ by
(9.11), since $m(B-1)+L\le m(K-1)$ on $A$.
Apply the supporting tangent of $F_j$ at $u_c$, where $F_j(u_c)=S_j$.
If $u\le u_c$, keep $P_j(u_c-u)$; if $u>u_c$, pay this
negative tangent term using $(m/r)P_je$. Equations (9.24)--(9.26)
prove the quantitative inequality

$$
H-S_j\ge a^3 e+\frac{a^3}{4}(u_c-u)_+
       +\mathcal J_D+a^2\sum_{i\in C}(y_i-\bar y)^2.
\tag{9.27}
$$

In particular $S_j\le H$ and $S_j\ge M$, because its cap is an
admissible law. Thus every term on the right is at most $\tau$.
This proves the assertions about $e,u$ and the tail variance.
The supporting-tangent inequality used here has precisely the
one-dimensional convexity hypotheses verified in (9.25)--(9.26);
see Boyd--Vandenberghe, *Convex Optimization*, §3.1.3, printed p.69.

To obtain exceptional mass, retain the exact common-mean identity

$$
\zeta:=\mathbb E[m-L;A^c]
=j-ru+r\mathbb E[B-1;A]+e
\le r(u_c-u)_++me.
\tag{9.28}
$$

On $A^c$ every type other than $C$ has $m-L\ge1$; on $A$ every
exceptional type has $K-1\ge1$. Hence
$\varepsilon\le\zeta+e\le(4r+m+1)\tau/a^3
\le16\tau/a^2$, using $m,r\le2a$.
Normalization and the original mean give (3.4), so

$$
x_C-\alpha=-\frac1r\sum_{T\text{ exceptional}}(K-1)x_T,
\qquad |x_C-\alpha|\le2\varepsilon.
\tag{9.29}
$$

Every core marginal is $x_C$ plus at most $\varepsilon$, proving
its bound. The tail bound in (9.19) follows from (9.24) and
$|\bar t-\beta|=|u-u_c|/n$.
Here $n\asymp_R\sqrt a$ and $\beta\asymp_R a^{-3/2}$.
Consequently that tail bound divided by $\beta$ tends uniformly
to zero for $\tau\le1$; this proves its asserted neighborhood.
Also

$$
\sum_{k\in D}(t_k-x_{\{k\}})
=\mathbb E[B;A,K\ge2]\le2e.
\tag{9.30}
$$

Combining (9.29)--(9.30) with Cauchy for the tail deviations gives

$$
\|x-x^{j,*}\|_1
\le3\varepsilon+2e+\sqrt{8n\beta^3\tau}
                          +4\tau/a^3
\le B_R a^{-2}\sqrt\tau.
\tag{9.31}
$$

Finally $S_j$ has denominator dividing $j(a-1)$. If $k\in J_*$,
a positive $S_j-S_k$ is at least $1/(jk(a-1))\ge1/(J^2(a-1))$.
The bound $S_j-M\le\tau$ therefore proves (9.20).
No separation assumption on the real phase parameter has been imposed;
nonwinning branches remain in (9.19) until this rational test excludes
them. All exact ties remain. ∎

**Lemma 9.3 (All-cardinality local remainder bounds).** There are
$A_R,L_R$ such that, for every winning cap and original law satisfying

$$
\varepsilon\le1/16,\qquad
|y_k-\beta|\le\beta/2\quad(k\in D),
\tag{9.32}
$$

one has, with $P(x)$ as in (3.1) and $\nu_k=y_k-\beta$,

$$
H(x)\ge S_j+P(x)+\frac1{3\beta^3}\sum_{k\in D}\nu_k^2
                         -L_Ra^{11}\varepsilon^2.
\tag{9.33}
$$

In addition, along any probability-law segment with marginals at least
$\delta_0>0$, a direction $v$ satisfies

$$
|D^2H(x)[v,v]|\le10s^3\delta_0^{-3}\|v\|_1^2.
\tag{9.34}
$$

The constants cover every source cardinality up to $s$.

**Proof.** Put $z=x_C$ and use (9.29). For each core label set
$e_i=\sum_{T\text{ exceptional},\,i\in T}x_T$ and
$f_i=\sum_{T\text{ exceptional},\,i\in T}K^2x_T$.
Then $0\le e_i\le\varepsilon$, $0\le f_i\le s^2\varepsilon$,
and its energy is $(m^2z+f_i)/(z+e_i)^2$. The marginal displacement
has magnitude at most $3\varepsilon$ and the numerator displacement
at most $2m^2\varepsilon+s^2\varepsilon$.
Since $\alpha\ge1/2$, the segment joining these arguments to their
cap arguments has marginal at least $1/4$. Direct differentiation of
$A/y^2$ bounds the sum of the core Taylor remainders by
$O_R(a^3\varepsilon^2)$.

For each tail label set

$$
q_k=\sum_{T\text{ exceptional},\,k\in T}(K^2-1)x_T\ge0.
\tag{9.35}
$$

The exact tail energy is $\sum_k(1/y_k+q_k/y_k^2)$, and
$\|q\|_2\le\sum_kq_k\le s^3\varepsilon$.
On (9.32), the exact reciprocal identity and the derivative of $y^{-2}$
give

$$
\begin{aligned}
\sum_k\frac1{y_k}
&\ge\frac n\beta-\beta^{-2}\sum_k\nu_k
                           +\frac2{3\beta^3}\|\nu\|_2^2,\\
\sum_k\frac{q_k}{y_k^2}
&\ge\beta^{-2}\sum_kq_k
                      -16\beta^{-3}\|q\|_2\|\nu\|_2.
\end{aligned}
\tag{9.36}
$$

The first line uses
$1/y=1/\beta-(y-\beta)/\beta^2+(y-\beta)^2/(\beta^2y)$.
The inequality $16QV\le V^2/3+192Q^2$ retains
$\|\nu\|_2^2/(3\beta^3)$ and pays at most
$192\beta^{-3}s^6\varepsilon^2$.
Since $\beta^{-3}=O_R(a^{9/2})$ and $s\le2a$, this payment is
$O_R(a^{21/2}\varepsilon^2)\le O_R(a^{11}\varepsilon^2)$.
The core and tail linear terms, including $\beta^{-2}\sum q_k$,
are exactly $DH(x^{j,*})[x-x^{j,*}]=P(x)$ by Lemma 2.3.
This proves (9.33).

For (9.34), write $A_i(x)=\sum_{T\ni i}K^2x_T$.
On a probability-law segment, $0\le A_i\le s^2y_i$, while
$|D A_i[v]|\le s^2\|v\|_1$ and $|D y_i[v]|\le\|v\|_1$.
The exact second derivative is

$$
D^2(A_i/y_i^2)[v,v]
=6A_i(Dy_i[v])^2/y_i^4-4DA_i[v]Dy_i[v]/y_i^3.
\tag{9.37}
$$

Its absolute value is at most $10s^2\delta_0^{-3}\|v\|_1^2$.
Summing over $s$ labels proves (9.34), without counting or
restricting the exceptional types. ∎

**Lemma 9.4 (Uniform graph realization and near-minimum comparison).**
There are $A_R,U_R,E_R,T_R$ such that, whenever (9.1) holds,
$a\ge A_R$ and $N\ge a^{24}$, the original graph class is
nonempty and contains a graph with

$$
W(G)\le M+\chi_N/N+U_Ra^{10}/N^2.
\tag{9.38}
$$

Every original graph with value at most the right side of (9.38)
satisfies the same-law bounds

$$
0\le H(x_G)-W(G)\le T_Ra^{17}/N^2,\qquad
0\le H(x_G)-M\le E_Ra^{7/2}/N.
\tag{9.39}
$$

**Proof.** Uniformly for the bounded winning indices,
$m,r\in[a,2a]$, $n\asymp_R\sqrt a$, $\alpha\ge1/2$ and
$\beta\asymp_R a^{-3/2}$. The displayed price formulas give
$b_j=O_R(a^3)$, $c_j=O_R(a^2)$, hence
$0<\chi_{j,N}=O_R(a^{7/2})$ and $M=O_R(a^3)$.

Choose a winning $j$ with $\chi_{j,N}=\chi_N$. Reuse Lemma 4.2's
single joint construction: $n$ connectors, $d=d_{j,N}<r$
missing-one core sources, and

$$
F=\frac{(a-1)N-n-(r-1)d}{r},\qquad T=N-F-n-d.
\tag{9.40}
$$

The residue makes $F,T$ integers. The exact shared budgets are
$F+T+n+d=N$ and $mF+rd+2n+T=aN$. Write
$f_0=(n+(r-1)d)/r=O_R(a)$, so $F=\alpha N-f_0$ and
$T=n\beta N-n+(n-d)/r$. Give the $T$ singleton sources to
the $n$ tails with counts differing by at most one. Each tail degree
then differs from $\beta N+1/r-d/(rn)$ by less than one.
A core degree is $F+d-o_i+e_i$, where $o_i$ and $e_i$ count its
omissions and connector endpoints. Thus the law satisfies

$$
\|x_G-x^{j,*}\|_1=O_R(a/N),\qquad
\min_i y_i\ge\beta/2
\tag{9.41}
$$

for the stated threshold, after increasing $A_R$.
Here $F,T>0$. A full-core source connects all core sinks, and the
one connector per tail connects every tail. Repeated neighborhoods
belong to different sources, so the graph is simple and bipartite.
All sink degrees exceed $s$ once $N\ge a^{24}$ and $a\ge A_R$;
indeed $\beta N/2\gg_R s$. This proves strict orientation for
the same graph, including every integer residue.

On the segment to its cap the least marginal is at least $\beta/2$.
Equation (9.34) and (9.41) bound the absolute Taylor remainder by
$O_R(a^{15/2}(a/N)^2)=O_R(a^{19/2}/N^2)$.
Its linear term is exactly $(nb_j+dc_j)/N=\chi_N/N$.
As $W\le H$, this proves (9.38) with the stated $a^{10}$ envelope.

For every competitor on this upper sublevel, $W\le L_Ra^3$ for
an $R$-only $L_R$: use $M=O_R(a^3)$, the price bound and (9.38).
The edge inequality in the original domain gives
$\vartheta H\le W\le H$, with $\vartheta=2/(1+\sqrt2)$, and
$H\ge\sum_i y_i^{-1}$ as in (3.10). Therefore the actual
marginals obey $y_i\ge\vartheta/(L_Ra^3)$.
Applying (3.11) with $s\le2a$ gives the first bound of (9.39),
with, for example, $T_R=4(L_R/\vartheta)^4$.
Together with (9.38) and $\chi_N=O_R(a^{7/2})$ it gives

$$
H-M\le O_R(a^{7/2}/N)+U_Ra^{10}/N^2+T_Ra^{17}/N^2
\le E_Ra^{7/2}/N,
\tag{9.42}
$$

since $N\ge a^{24}$. Nonnegativity is the definition of $M$.
All these bounds concern the same actual law and graph; no independent
choice of marginal data has entered. ∎

**Theorem 9.5 (A common-growth first-connection theorem in the
original graph class).** There are absolute integers

$$
p=24,\qquad q=17
\tag{9.43}
$$

with $q\ge1$ and $p>q+2$ such that the following holds. For each
fixed finite $R\ge4$ there are positive finite $R$-only constants
$A_R,C_R,D_R$ such that every integer $a\ge A_R$,
$(7/2)\sqrt a\le h\le R\sqrt a$, and
$N\ge\lceil D_Ra^p\rceil$ has a nonempty original class and

$$
\left|V_N-M-\frac{\chi_N}{N}\right|
\le\frac{C_Ra^q}{N^2}.
\tag{9.44}
$$

Every exact minimizer has exactly the source types of Theorem 1.3
for a law-winning $j\in J_*$ with $\chi_{j,N}=\chi_N$.
All law ties, price ties and integer residues are included.

**Proof.** Choose one threshold for Lemmas 9.1--9.4. By Growing
Proposition 15.6, there are at most two winning indices, adjacent
when distinct. Each price in (2.1), and each $b_j,c_j$, has denominator
dividing $j^2(a-1)^2$. This follows by substituting
$\eta=rn/j$ and $\alpha^{-1}=r/(a-1)$ in (1.8) and (2.1);
the division by $r$ in $\lambda_j$ and $c_j$ cancels one numerator
factor $r$. Thus a common positive integer denominator for every
winning price, $\chi_{j,N}$ and $\chi_N$ can be chosen as

$$
D_*=(a-1)^2\prod_{j\in J_*}j^2\le J^4a^2.
\tag{9.45}
$$

Take $L_R$ from (9.33), $U_R,E_R,T_R$ from Lemma 9.4, and put

$$
\begin{gathered}
F_R=T_R+256L_RE_R^2,\qquad
C_R=1+U_R+F_R,\\
D_R=1+2J^2E_R+2J^4C_R.
\end{gathered}
\tag{9.46}
$$

These are explicit choices in terms of the proved $R$-only estimates;
none depends on a fixed pair $a,h$ or on $N$.

Consider any graph whose value is at most the upper comparison
(9.38). Its actual excess $\tau$ is at most $E_Ra^{7/2}/N$ by
(9.39), and the threshold makes this at most $1/(2J^2a)$.
Theorem 9.2 therefore supplies a genuinely winning cap partition,
with $\varepsilon\le16E_Ra^{3/2}/N$ and the tail neighborhood
in (9.32). Its core neighborhood follows from (9.29).
After the fixed threshold increase $\varepsilon\le1/16$ as well.
Equations (9.33) and (9.39) give

$$
\begin{aligned}
W(G)
&\ge M+\frac{\mathcal P_j(G)}N
        -\frac{256L_RE_R^2a^{14}+T_Ra^{17}}{N^2}\\
&\ge M+\frac{\mathcal P_j(G)}N-\frac{F_Ra^{17}}{N^2}\\
&\ge M+\frac{\chi_N}N-\frac{F_Ra^{17}}{N^2}.
\end{aligned}
\tag{9.47}
$$

The last line is Lemma 4.1, which applies to every connected
source neighborhood type once this winning partition is supplied.
A graph above (9.38) already exceeds the last line of (9.47).
Consequently this is a lower bound over the entire original class.
Combining it with its one actual upper graph proves (9.44).

The finite labelled graph class has an exact minimizer. For any
such minimizer, (9.38) and (9.47) imply

$$
0\le\mathcal P_j(G)-\chi_N
\le\frac{U_Ra^{10}+F_Ra^{17}}N
\le\frac{C_Ra^{17}}N
<\frac1{J^4a^2}\le\frac1{D_*}.
\tag{9.48}
$$

Both prices have denominator dividing $D_*$. Hence their difference
is zero. The inequalities
$\mathcal P_j(G)\ge\chi_{j,N}\ge\chi_N$ are both equalities.
Lemma 4.1's equality characterization now gives one two-element
core--tail connector per tail, exactly $d_{j,N}$ missing-one core
sources, and only full cores and singleton tails for the rest.
It also gives $\chi_{j,N}=\chi_N$. No source restriction was
assumed to obtain this conclusion. ∎

The stability and graph deductions in this section are repo-derived.
They reuse Growing Lemma 7.1's coarse sublevel certificate, Theorem
7.2's scalar phase evaluation, Theorem 15.5's exact law value and
Proposition 15.6's finite branch competition. Equations (9.8)--(9.17)
retain the incidence residuals of Growing (15.7)--(15.18) on the stated
positive-excess sublevel. The price and exact-budget consumers are
Lemmas 2.3, 4.1 and 4.2 of this volume. The later allocation, secondary
energy and refined-periodic selection of Sections 6--8 retain their
fixed-parameter quantifiers. [*CDSO uniform dilution limit*, Corollary
40.3](CDSO_UNIFORM_DILUTION_LIMIT.md) treats the finite positive limit
$N/a^{3/2}\to D$ and its dilution variational value. The window here
has $N/a^{3/2}\to\infty$ and controls the finer $\chi_N/N$ term
and exact source exclusion; it makes no new finite-positive-$D$ claim.

The scalar supporting-tangent principle is the intermediate
literature-attested input of Boyd--Vandenberghe,
[*Convex Optimization*](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf),
§3.1.3, printed p.69; the second derivatives above verify its hypotheses.
The original CDSO definition is Albalahi--Das--Ali--Barman--Hamza,
[*On the hyperbolic Sombor index and its counterpart*](https://arxiv.org/html/2510.24809v1),
§1, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176):
maximum endpoint degree in the denominator, with the factor
$1/\sqrt2$ dropped. Its general connected-graph conjecture is not
a premise of this prescribed bipartite-budget theorem. Full-text
technical overlap with Zhao--Zhao, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
is not determined here; no worldwide-priority claim is made.

Theorem 9.5 supplies a sufficient deep polynomial window for the
common-growth part of Open problem 8.3. It does not determine least
thresholds or least refined periods, uniform later template selection,
the scale $N\asymp a^2$, varying $R$, or the extremum when the sink
number is allowed to vary. The sink budget throughout is exactly
$s=a+1+h$, with the original nonlinear objective and all the graph
conditions of Definition 1.1.

## 追加锚（本行以下为增补区）
