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

## 10. Effective uniform exact selection and canonical allocation data

The graph domain and normalization remain those of Definition 1.1.
Throughout this section $R\ge4$ is fixed and finite. Constants with
subscript $R$ depend only on $R$, and may be enlarged. Assume
$a\ge A_R$ and $(7/2)\sqrt a\le h\le R\sqrt a$. Use $J$ from
(9.1); in particular $2\le j\le J$ for every $j\in J_*$,
$m,r\le2a$, $\alpha\ge1/2$, $s\le2a$, and
$n\asymp_R\sqrt a$, $\beta\asymp_R a^{-3/2}$. Theorems and
proofs here are ordinary mathematical deductions, not claims of
Lean verification.

**Theorem 10.1 (Uniform exact allocation and reconstruction).**
After increasing $A_R,D_R$ in Theorem 9.5, for every integer
$N\ge\lceil D_Ra^{24}\rceil$, the exact relation (6.12) and every
reconstruction and equality condition in Theorem 6.4 hold. Thus
Sections 6.1--6.4 have uniform quantifiers on this window, including
all law ties, price ties and remainders.

**Proof.** For every winning branch and every $0\le d<r$,

$$
\begin{gathered}
F=\alpha N+\varphi,\qquad F+d=\alpha N+\sigma,
\qquad Q=n\beta N-\sigma,\\
|\varphi|\le C_Ra,\quad |\sigma|\le C_R,
\quad |z_i|\le C_Ra,\quad
b=\beta N+\gamma-t/n=\beta N+O_R(1).
\end{gathered}
\tag{10.1}
$$

These follow directly from (6.1), (6.4) and (7.1), since
$d<r=O_R(a)$ and $n=O_R(\sqrt a)$. They hold uniformly over
all allocation entries, rather than only minimizing ones. In this
window $F>0$, every possible core degree
$F+d+z_i=\alpha N+O_R(a)$ exceeds $s$, and both balanced tail
degrees exceed $s$. Every reconstruction in Theorem 6.4 is therefore
legal: (6.13) gives exactly $N$ sources and $aN$ edges; different
sources may have identical neighborhoods in a simple bipartite graph;
a full-core source connects all core sinks, and the one connector at
each tail connects every tail. All source degrees are at most $s$,
so the required strict orientation holds on every edge.

Conversely Theorem 9.5 gives every original minimizer exactly the
source types used in (6.2), for $j\in\mathcal J_N$. Its actual law
also satisfies the bounds used in the proof of that theorem, in
particular every tail marginal is at least $\beta/2$ by (9.19).
Thus every tail degree exceeds $4$ uniformly here. The singleton
transfer in Lemma 6.2 is legal on this same graph and forces exact
balancing. Lemma 6.3 then applies verbatim: its coupled move fixes
all degrees and budgets, and its strict equality condition is (6.9).
All inequalities needed for feasibility have just been made uniform;
no compactness over fixed integer parameters is being used. This proves
both directions of (6.12) and the exhaustive preimage assertion. ∎

**Proposition 10.2 (Least period of the complete allocation state).**
For fixed $a,h,j$, the integer state $(d_{j,N},t_{j,N})$ in (6.1),
viewed as a sequence for integer $N$, has least positive period

$$
P_j=\frac{r_jn_j}{\gcd(j,r_jn_j)}.
\qquad
P_{\rm data}=\operatorname{lcm}_{j\in J_*}P_j
\tag{10.2}
$$

is the least period of the full vector of these states and a sufficient
period for the graph selection data. This asserts no leastness for the
optimizer sequence.

**Proof.** Since $a-1=r-j$, direct substitution gives

$$
d_N=[n+jN]_r,\qquad Q_N=\frac{jN+n-d_N}{r}.
\tag{10.3}
$$

A shift $T>0$ preserves $d$ if and only if $r\mid jT$.
Under that condition $Q_{N+T}-Q_N=jT/r$, so it also preserves
$t=[Q]_n$ if and only if $n\mid jT/r$. Both conditions together
are exactly $rn\mid jT$, with least positive solution (10.2).
The argument is independent of $N$, and also proves leastness on any
cofinal sequence of consecutive integer budgets. Taking all branches
gives the least common multiple. For such a shift,
$\alpha T=T-jT/r$ and $\beta T=jT/(rn)$ are integers;
$F$ and $b$ increase by these amounts, while $d,t,\varphi,\sigma$
and $v_\pm$ stay fixed. The prices depend on $d$ alone.
Consequently the germs (8.4) can equally be defined on residues modulo
$P_{\rm data}$, using the same formulas and the common state of that
residue. This does not evaluate a graph at a possibly small residue
representative. Since $P_{\rm data}\mid P$, the original period $P$
is retained below without any change of notation. Distinct states can
have coincident selected values or templates; their period need not
be the least optimizer period. ∎

**Lemma 10.3 (Exact normalized-radical identity).** For a difference
$D$ of two functions (8.4), write its terms as in (8.7), and set

$$
b_l=\frac{a_l'(0)}{a_l(0)},\qquad
c_l=\frac{k_l}{a_l(0)}>0,\qquad
q_l(u)=(1+b_lu)^2+c_l^2u^2.
\tag{10.4}
$$

Group equal signatures $(b_l,c_l)$, and for each signature let
$W_q(u)$ be the sum of its affine weights $w_l(u)$, with signs.
Then $D$ is identically zero if and only if every $W_q$ is the zero
polynomial. This includes repeated terms, zero weights and negative
weights.

**Proof.** The discriminant of $q_l$ is $-4c_l^2<0$. Thus it is
an irreducible quadratic over $\mathbb Q$, with constant term one.
Two such normalized quadratics agree exactly when $b_l$ and $c_l$
agree. Distinct ones are nonassociate irreducibles; valuation at each
of these factors proves independence of their classes in
$\mathbb Q(u)^*/\mathbb Q(u)^{*2}$. The multiquadratic construction
then gives independent sign changes of their square roots. To check
the field step explicitly, induct on the number adjoined. Suppose the
earlier subset products form a basis, with all sign changes acting
independently. If the next $q$ were a square $z^2$ in that field, each
sign automorphism would send $z$ to $z$ or $-z$. Thus $z$ would be a
simultaneous eigenvector. The subset-product basis has distinct
characters, so each such eigenspace is one-dimensional over
$\mathbb Q(u)$, and $z$ would be a base-field multiple of one subset
product. Squaring contradicts the independent square classes. The next
quadratic extension therefore has degree two; its basis and all sign
changes extend the previous ones. This proves the assertion by induction.
It is the elementary quadratic Kummer construction;
[Stacks, Section 9.24](https://stacks.math.columbia.edu/tag/09I6)
gives the standard root-adjoining and sign-automorphism background.

The positive branches in (8.3) satisfy

$$
R_{k_l}(a_l,u)=\frac{\sqrt{q_l(u)}}{1+b_lu}-1,
\qquad
\frac{u^2D(u)}2
=\sum_q\frac{W_q(u)}{1+b_qu}\sqrt{q(u)}-\sum_qW_q(u).
\tag{10.5}
$$

These square roots, as formal series with constant term one, give an
embedding of the same field into the field of Laurent series. In that
field $1$ and the individual square roots are linearly independent over
$\mathbb Q(u)$, by the sign automorphisms. Thus (10.5) vanishes
exactly when all $W_q/(1+b_qu)$ vanish; then its rational part
vanishes too. All denominators are units at zero. This also proves
that normalization is essential: $a_1=1,k_1=1$ and $a_2=2,k_2=2$
give the same radical quotient, so their opposite weights cancel. ∎

**Proposition 10.4 (Graph-specific classification of exact ties).**
After increasing the $R$-only threshold $A_R$, on any fixed residue
$\rho$ modulo $P$, two allocation germs from (8.4) satisfy

$$
\mathscr A_{\rho,j,z}\equiv\mathscr A_{\rho,j',z'}
\quad\Longleftrightarrow\quad
j=j'\ \text{and}\ \{z_i:i\in C\}=\{z_i':i\in C'\}
\text{ as multisets}.
\tag{10.6}
$$

This is a branch-and-histogram classification, not uniqueness of a
labelled graph or of an isomorphism class.

**Proof.** The normalized frequencies $c$ of core terms are
$m_j/\alpha_j$, $r_j/\alpha_j$ and $2/\alpha_j$;
tail terms have frequencies $\eta_j,2\eta_j$. Enlarge $A_R$ so
that, for every winning index,

$$
\eta_j\ge13a,\qquad
m_j/\alpha_j\le4a,\qquad 2/\alpha_j\le4.
\tag{10.7}
$$

Indeed $n_j\ge3\sqrt a$ eventually, $r_j\ge a$ and $j\le J$,
so $\eta_j\ge3a^{3/2}/J$. A full-core frequency is at least
$a$, hence cannot equal a connector frequency. Nor can it equal a tail
frequency by (10.7). Full-core frequencies at distinct branches are
distinct, since $m_jr_j/(a-1)$ strictly increases in $j$. Finally a
full-core frequency cannot equal any missing-one frequency: such an
equality would require $m_j(m_j-1)=r_{j'}^2$, whereas the left side
lies strictly between $(m_j-1)^2$ and $m_j^2$.

Consequently each full-core signature occurs only among full-core terms
of its own branch. Its grouped coefficient in one germ is its positive
integer multiplicity times $\alpha_j+\varphi_ju$, whose constant
term is positive. Lemma 10.3 excludes identity for distinct branches.
Within one branch, the first signature coordinate is
$(\sigma_j+z_i)/\alpha_j$. Equality of all its full-core grouped
coefficients therefore recovers exactly the multiplicity of every value
of $z_i$. Conversely (8.4) is symmetric in the coordinates of $z$;
$L,z_0$ and all remaining sums are determined by this multiset. Equal
histograms on the fixed state hence give identical functions. No
separation of the other frequency classes from each other is needed. ∎

**Lemma 10.5 (A sufficient quadratic Taylor cutoff).** Put

$$
T_s=3(6s+5)^2.
\tag{10.8}
$$

Two germs (8.4) are identical if and only if their coefficients through
order $T_s$ agree. This assertion already holds for fixed admissible
parameters without the extra frequency separation in Proposition 10.4.
It handles repeated radicals and zero summands.

**Proof.** Use (8.7)--(8.8), with $K\le6s+4$. The case $K=0$ is
zero. Otherwise write each nonzero summand of $Z$ as $A\sqrt p$,
including its rational summand by taking $p=1$; here
$\deg A\le K+1$, $\deg p\le2$, and $p(0)>0$. Choose a maximal
constant-linearly-independent subset of these analytic summands,
of size $\ell\le K+1$. Their Wronskian $\mathcal W$ is nonzero.
The criterion being used is Bostan--Dumas, *Wronskians and linear
independence*, Theorem 2, American Mathematical Monthly 117 (2010),
722--727, DOI [10.4169/000298910X515785](https://doi.org/10.4169/000298910X515785),
[arXiv:1301.6598v1](https://arxiv.org/html/1301.6598v1): over
characteristic zero, linearly independent formal series have nonzero
Wronskian. Taking a basis first avoids any independence assumption on
repeated or cancelling original terms.

For each selected column let $B_0=A$. Differentiation gives

$$
(A\sqrt p)^{(v)}=p^{1/2-v}B_v,\qquad
B_{v+1}=pB_v'+(1/2-v)p'B_v,\qquad
\deg B_v\le K+1+v.
\tag{10.9}
$$

For $p=1$ the same formula just differentiates $A$. Factor
$p^{1/2-(\ell-1)}$ out of its Wronskian column. The entry in row
$v=0,\ldots,\ell-1$ that remains is
$p^{\ell-1-v}B_v$, of degree at most
$K+1+2(\ell-1)-v$. Thus the remaining determinant is a nonzero
polynomial of degree at most

$$
\ell(K+1)+\frac32\ell(\ell-1).
\tag{10.10}
$$

All the factored functions are units at zero, so this degree bounds
$\operatorname{ord}_0\mathcal W$. This low-degree determinant
factorization is the mature method also used by Koiran--Portier--Tavenas,
*A Wronskian Approach to the Real $\tau$-Conjecture*, §3 and the
proof of Theorem 13, [arXiv:1205.1015v3](https://arxiv.org/html/1205.1015v3),
DOI [10.1016/j.jsc.2014.09.036](https://doi.org/10.1016/j.jsc.2014.09.036).
Their distinct-real-zero bound is not being substituted for a local
multiplicity bound; (10.9)--(10.10) establish the needed degree here.

Suppose $Z\ne0$. Express $Z$ in the chosen basis and replace a column
with nonzero coefficient by $Z$. The new determinant is a nonzero
constant times $\mathcal W$. Expanding on that column, whose $v$th
entry has order at least $\operatorname{ord}_0Z-v$, gives

$$
\operatorname{ord}_0Z\le\operatorname{ord}_0\mathcal W+\ell-1.
\tag{10.11}
$$

If $\operatorname{ord}_0Z<\ell-1$ this is immediate; otherwise all
these lower orders are nonnegative and the determinant expansion proves
it directly. Since $\prod a_l$ is a unit,
$\operatorname{ord}_0D=\operatorname{ord}_0Z-2$. Equations
(10.10)--(10.11), with $\ell\le K+1$, imply

$$
\operatorname{ord}_0D
\le\ell(K+1)+\tfrac32\ell(\ell-1)+\ell-3
<3(K+1)^2\le T_s.
\tag{10.12}
$$

This proves the sufficient cutoff. The basis argument also covers a
zero rational part, constant affine denominators, and $\ell=1$.
No nonvanishing claim was made for an unreduced Wronskian. ∎

**Lemma 10.6 (Uniform rational separation and analytic control).**
For all winning branches, all residues and all allocations in Section 8,
set the positive even integer

$$
Q_0=2(a-1)\prod_{j\in J_*}(j r_j n_j)\le C_Ra^4.
\tag{10.13}
$$

For any pair difference $D$ of the corresponding germs,

$$
(2Q_0)^{k+3}[u^k]D\in\mathbb Z\quad(k\ge0).
\tag{10.14}
$$

There are $R$-only positive $c_R,C_R$ such that all these differences
are holomorphic on a neighborhood of the closed disk
$|u|\le r_0=c_Ra^{-3/2}$ and satisfy $|D(u)|\le M_0=C_Ra^6$
on that disk. In particular a first nonzero coefficient of order $k$
has absolute value at least $(2Q_0)^{-(k+3)}$.

**Proof.** Growing Proposition 15.6 supplies at most two winning
indices, both bounded by $J$. Each factor $jr_jn_j$ is
$O_R(a^{3/2})$, proving (10.13). The coefficients of every affine
weight $w_l$ in (8.7), and the numbers $b_l,c_l$ in (10.4), have
denominators dividing $Q_0$. For the core this follows from

$$
\alpha=\frac{a-1}{r},\quad
\varphi=-\frac{n+(r-1)d}{r},\quad
\frac{\delta_i}{\alpha}=\frac{d-n+rz_i}{a-1},\quad
\frac{k}{\alpha}=\frac{kr}{a-1}.
\tag{10.15}
$$

For a tail the corresponding quantities are

$$
\beta=\frac{j}{rn},\quad
v_-=\frac{n-d-rt}{rn},\quad v_+=v_-+1,\quad
\frac{v_-}{\beta}=\frac{n-d-rt}{j},\quad
\frac{k}{\beta}=\frac{krn}{j}.
\tag{10.16}
$$

Multiplicities in (8.4) are integers, so do not add denominators.
These formulas apply also to $a_0$ and to absent terms.

For one normalized term, expand directly as

$$
R=\sqrt{1+\frac{c^2u^2}{(1+bu)^2}}-1
 =\sum_{v\ge1}\binom{1/2}{v}c^{2v}u^{2v}(1+bu)^{-2v}.
\tag{10.17}
$$

For $q\ge2$ its coefficient of $u^q$ is the sum over
$1\le v\le q/2$ of

$$
\binom{1/2}{v}(-1)^{q-2v}
 \binom{q-1}{q-2v}c^{2v}b^{q-2v}.
\tag{10.18}
$$

The denominator of $\binom{1/2}{v}$ divides $2^{2v}$:
explicitly it is $(-1)^{v-1}C_{v-1}/2^{2v-1}$ with integral
Catalan number $C_{v-1}$. The remaining monomial has denominator
dividing $Q_0^q$, so $[u^q]R\in(2Q_0)^{-q}\mathbb Z$.
The coefficients of orders zero and one vanish. Multiplication by an
affine weight with denominator dividing $Q_0$, and then by $2/u^2$,
proves (10.14). This estimate uses the normalized quotients before
clearing their product; no exponential denominator from a norm
polynomial is needed.

Uniformly in (10.15)--(10.16),
$|b_l|+c_l\le C_Ra^{3/2}$. Core offsets have size $O_R(a)$;
tail offsets $v_\pm$ have size $O_R(1)$, while
$\beta^{-1}=O_R(a^{3/2})$. Choose $c_R$ small enough that on
a neighborhood of the closed disk, $|b_lu|,|c_lu|\le1/8$.
The square root in (10.17) is then its single holomorphic branch
with value one at zero, and $|R|\le Cc_l^2|u|^2$.
Every weight coefficient has size at most $C_Ra$ and there are
$O_R(a)$ terms; hence $\sum_l|w_l(u)|\le C_Ra^2$ on this
disk. Dividing their vanishing factors $u^2$ in (8.7) gives
$|D(u)|\le C_Ra^5\le C_Ra^6$, including $u=0$ by continuity.
This proves the disk and size assertions for one common radius and
bound. All estimates are uniform in the integer states and allocations. ∎

**Theorem 10.7 (Effective common-growth exact graph selector).**
For each fixed finite $R\ge4$ there are $R$-only positive constants
$A_R,D_R,E_R$ such that, for every pair in Definition 1.1 and every
integer

$$
N\ge\max\left\{\lceil D_Ra^{24}\rceil,
                 \left\lceil\exp(E_Ra^2\log a)\right\rceil\right\},
\tag{10.19}
$$

the following is an exact selection rule in the original graph class.
On the residue $\rho=N\bmod P$, replace $B_s$ in (8.6) by $T_s$
from (10.8). The lexicographically least vectors select precisely all
pairs attaining (6.12), and Theorem 6.4 reconstructs precisely all exact
minimizers. All selected pairs have one common branch and one common
$z$-histogram. Every source-label, endpoint, omission, minimum-offset
allocation and high-tail-label freedom allowed by that reconstruction
is retained. One may instead use $P_{\rm data}$ with the coherent
residue germs described in Proposition 10.2. Neither period is asserted
to be the least optimizer period, and (10.19) is only a sufficient
threshold.

**Proof.** Theorem 10.1 first identifies the exact original graph
minimum with the finite allocation relation. Lemma 10.5 says that
matching finite vectors means identity of the value germs. Otherwise
let $k\le T_s$ be the first nonzero coefficient of a pair difference,
called $c_k$. Cauchy's estimate on the disk of Lemma 10.6 gives, for
$0<u\le r_0/2$,

$$
\left|D(u)-c_ku^k\right|
 \le 2M_0r_0^{-(k+1)}u^{k+1}.
\tag{10.20}
$$

Thus its sign is the sign of $c_k$ whenever

$$
N\ge\max\{2/r_0,
       4M_0(2Q_0)^{k+3}r_0^{-(k+1)}\},\qquad u=1/N.
\tag{10.21}
$$

Indeed the error is then at most half the nonzero leading term by
(10.14). Since $s\le2a$, $k\le3(12a+5)^2$, $Q_0\le C_Ra^4$,
$M_0=C_Ra^6$, and $r_0^{-1}=C_Ra^{3/2}$, the logarithm of the
right side of (10.21) is at most $E_Ra^2\log a$, after choosing
one $R$-only $E_R$. This bound holds for each pair and residue with
the same constants. There is no multiplication by the number of
allocations or residues. Every strict comparison therefore has its
Taylor sign simultaneously in (10.19); all identities stay exact.
This proves the selector and all tie claims. Proposition 10.4 then
identifies the selected equivalence class with one branch and one
histogram. Exhaustive reconstruction follows from Theorem 10.1. ∎

The coefficient-separation step is logically necessary: even the linear
function $\varepsilon-u$, for a positive rational $\varepsilon$,
has a bounded vanishing order but requires $N>1/\varepsilon$ for
its positive eventual sign. Lemma 10.6 supplies the extra arithmetic
information for the actual graph functions. Theorem 10.7 therefore
strengthens the uniformity of the later selector, without inferring a
uniform sign threshold from finite order alone.

## 11. A necessary source-threshold scale from finite connection costs

This section compares different branches before restricting to a law
winner. It keeps every graph budget and the strict orientation in
Definition 1.1. A template-class comparison is not a lower bound for
all graphs outside those classes.

**Definition 11.1 (Templates on a possibly nonwinning branch).**
Fix finite $R\ge4$, an integer $J_0\ge2$ and $c>0$. Let
$(7/2)\sqrt a\le h\le R\sqrt a$, $2\le j\le J_0$, and take
$a$ sufficiently large in terms of $R,J_0,c$. Define $m,r,n,\alpha,
\beta,d,F,Q$ by (1.6), (6.1), without requiring $j\in J_*$.
Let $\widehat{\mathfrak C}_{j,N}$ be the class of original graphs
having a partition of sizes $m,n$ and exactly $n$ core--tail connectors,
one per tail, $d$ missing-one core sources, $F$ full-core sources and
$Q-n$ tail-singleton sources. All endpoint, omission and singleton
allocations satisfying the original graph conditions are allowed.
Write

$$
\widehat V_{j,N}=\min_{G\in\widehat{\mathfrak C}_{j,N}}W(G),
\qquad \bar\chi_{j,N}=nb_j+dc_j,
\tag{11.1}
$$

where the rational formulas (1.8) define $b_j,c_j$ also on this
branch. The bar distinguishes this algebraic extension from the
winning-branch price $\chi_N$; positivity of the extended prices
is not assumed.

**Lemma 11.2 (Uniform full-template comparison).** There are
$A_{R,J_0,c},C_{R,J_0,c}$ such that for all the above pairs with
$a\ge A_{R,J_0,c}$ and every integer $N\ge ca^2$, each
$\widehat{\mathfrak C}_{j,N}$ is nonempty and

$$
\left|\widehat V_{j,N}-S_j-\frac{\bar\chi_{j,N}}N\right|
 \le \frac{C_{R,J_0,c}a^5}{N^2}.
\tag{11.2}
$$

The estimate is uniform in every integer remainder. In particular its
lower bound applies to the minimum over every old winning-branch
template, including unbalanced tail allocations.

**Proof.** Bounded $j$ gives $r,m\asymp a$, $n\asymp_R\sqrt a$,
$\alpha\ge1/2$ and $\beta\asymp_{R,J_0}a^{-3/2}$.
The identities (10.1) still hold, uniformly over these branches, except
that no assertion of law optimality is used. Thus $F>0$ for
$N\ge ca^2$. For arbitrary $e,o$ in (6.2), all core degrees
are $\alpha N+O_{R,J_0}(a)$ and exceed $m$. Balanced tail degrees
are $\beta N+O_{R,J_0}(1)$, hence tend uniformly to infinity even
at $N=ca^2$. They exceed $2$, the maximum source degree incident
to a tail. Together with (6.13), this proves the precise source and
edge counts, simplicity, connectedness and strict orientation of every
balanced construction. It proves nonemptiness without the unnecessary
requirement that tail degrees exceed $s$ at this smaller scale.

We first reduce every graph in the template class to such balanced
tails. Strict orientation at its connector forces each integer tail
degree $q_k\ge3$, even if it is far from its balanced degree. In
fact (6.7) is strictly positive for every real $x\ge3$. To check the
extra interval, the numerator $x^3-3x^2-2$ is increasing on this
range and at least $-2$, whereas
$x^2+4\le2(x^2+1)$ and $3x^2+8\ge35$. Thus the second term
of (6.7) exceeds
$140/[3x^3(x^2+1)^{3/2}]$, which exceeds the possible negative
part $2/[x^3(x^2+1)^{3/2}]$ of its first term.

If $q_k\ge q_l+2$, transfer a singleton from $k$ to $l$.
The donor degree after the transfer is at least $4$ and both
connector degrees are still strictly less than their tail degrees.
Core degrees and all source degrees remain fixed. The connector at
each tail and the full cores preserve connectedness, and changing one
singleton neighborhood preserves simplicity and both budgets. Strict
convexity decreases $g(q_k)+g(q_l)$ as in (6.8). Repetition terminates,
for example by the strictly decreasing integer sum of squared tail
degrees, at the balanced degrees $b,b+1$. Hence minimizing over the
whole template class is equivalent to minimizing over balanced tails
and arbitrary feasible $e,o$. This supplies a full-template lower
bound, rather than a comparison of two chosen constructions.

We estimate the value on every such balanced graph using its same actual
empirical law. Put $z_i=e_i-o_i$, $\delta_i=\sigma+z_i$ and use
$B_i$ from (7.4), before any coupled core minimization. Uniformly,

$$
\begin{gathered}
|\sigma|\le C,\quad |\varphi|\le Ca,\quad
\sum_i|\delta_i|\le Ca,\quad \sum_i\delta_i^2\le Ca^2,
\quad \max_i|B_i|\le Ca^3,\\
q_k=\beta N+\nu_k,\quad |\nu_k|\le C,\quad
\sum_i\delta_i=\sigma,\quad \sum_k\nu_k=-\sigma.
\end{gathered}
\tag{11.3}
$$

Here and within this proof $C$ depends only on $R,J_0,c$.
For example $\sum|z_i|\le n+d=O(a)$ proves the offset bounds,
and
$B_i=m^2\sigma+(r^2-m^2)d-r^2o_i+4e_i$ proves the numerator
bound. The balanced tail offsets are exactly those of (7.7), with
$\gamma=O(1)$, proving their uniform boundedness. For large $a$,
$|\delta_i|\le\alpha N/2$ and $|\nu_k|\le\beta N/2$.
Taylor expansion of the exact law identity (7.5), with these bounds,
gives the first two terms in (7.6). Its summed core error is bounded by

$$
\frac C{N^2}\sum_i
       (m^2\delta_i^2+|B_i\delta_i|)
 \le\frac{Ca^4}{N^2};
\tag{11.4}
$$

the summed tail error is at most
$Cn\beta^{-3}/N^2\le Ca^5/N^2$. These estimates follow from the
Taylor remainder for $(1+x)^{-2}$ on $|x|\le1/2$; in the term
with $B_i/N$ its remainder after the constant term is bounded by
$C|B_i\delta_i|/N^2$. No fixed-parameter error is being reused
as a joint-growth error.

The constant term is $m^3/\alpha+n/\beta=S_j$.
For clarity the linear coefficient is exactly

$$
\frac{m^3\varphi+r^3d+4n-2m^2\sigma}{\alpha^2}
       +(3n+\sigma)\eta^2
 =nb_j+dc_j.
\tag{11.5}
$$

Indeed $\sum_iB_i=m^3\varphi+r^3d+4n$,
$\sum_i\delta_i=\sigma$, $\sum_k\nu_k=-\sigma$;
substitution of $\varphi=\sigma-d$, $r\sigma=d-n$ and $m=r+1$
into (1.8) proves the equality. This is rational algebra and does not
use any winning-branch inequality.

It remains to pass from this law energy to the original graph objective.
The scalar inequality
$0\le x-2(\sqrt{1+x}-1)\le x^2/4$ for $x\ge0$ yields

$$
0\le H(x_G)-W(G)
 \le\frac N4\sum_{ui\in E}\frac{d_G(u)^4}{d_G(i)^4}.
\tag{11.6}
$$

At a core the fourth-power numerator is
$Fm^4+(d-o_i)r^4+16e_i\le CNa^4$ and its degree is at least
$\alpha N/2$. Summing over $m=O(a)$ cores bounds their part
by $Ca^5/N^2$. At a balanced tail the numerator is $q_k+15$,
so its part is at most $CN/q_k^3\le C/(\beta^3N^2)$;
summing over $n$ tails again gives $Ca^5/N^2$.
Equations (11.3)--(11.6) bound the absolute error on every balanced
graph, uniformly over its endpoints, omissions, all $d,t$ and labels.
Their minimum has the same bound. The balancing reduction proves that
this minimum is $\widehat V_{j,N}$, completing (11.2). ∎

**Theorem 11.3 (An integer-family obstruction and a necessary
$a^{5/2}$ source threshold).** Set

$$
a=6t^2,\qquad h=12t-1,\qquad s=a+12t,
\qquad t\in\mathbb Z_{>0},\quad t\longrightarrow\infty.
\tag{11.7}
$$

These parameters lie in the $R=5$ domain for large $t$ and have
$J_* =\{2\}$. At the exact integer budget $N=a^2t$,

$$
\widehat V_{3,N}-\widehat V_{2,N}
      =-84a+O(\sqrt a)<0.
\tag{11.8}
$$

Thus the original graph class is nonempty and has exact minimizers,
but none has any of the law-winning source templates permitted by
Theorem 9.5 at this smaller budget. No global optimality of branch
$j=3$ is asserted.

More precisely, for a fixed admissible pair define $T_{\rm src}(a,h)$
to be the least positive integer $K$ such that, for every integer
$N\ge K$, the original class is nonempty and every exact minimizer
has the source-type conclusion of Theorem 1.3, including a law-winning,
price-winning branch. Theorem 9.5 ensures
$T_{\rm src}(a,h)\le\lceil D_5a^{24}\rceil$ on this family for
large $t$. Nevertheless

$$
\liminf_{t\to\infty}
 \frac{T_{\rm src}(6t^2,12t-1)}{(6t^2)^{5/2}}
 \ge\frac{5\sqrt6}{9}.
\tag{11.9}
$$

In particular no uniform fixed multiple of $a^2$ suffices for that
source-type conclusion in the $R=5$ domain.

**Proof.** Here $h/\sqrt a=2\sqrt6-1/(\sqrt6t)$ lies between
$7/2$ and $5$ for large $t$. Apply Growing Proposition 15.6, retaining
its exact adjacent-difference formula rather than a limiting phase
comparison. At $h+1=12t$ and $a=6t^2$ it gives

$$
\begin{aligned}
S_3-S_2&=36a-24t+96+\frac{138}{a-1}>0,\\
S_2-S_1&=-8a^2+32a+40-24t+\frac{46}{a-1}<0
                     \quad\text{for large }t.
\end{aligned}
\tag{11.10}
$$

For example the polynomial divisions in that formula give
$D_2(a)=4a^2+32a+96+138/(a-1)$ and
$D_1(a)=4a^2+20a+40+46/(a-1)$; subtracting
$24t+(a-1)(12t)^2/(j(j+1))$ gives (11.10).
Strict discrete convexity makes $j=2$ the unique winner among all
$1\le j\le h$, and Growing Theorem 15.5 identifies this as the full
law winner. This proves $J_* =\{2\}$, without asserting that only
these two adjacent branches need be considered for finite-graph
optimality.

We next compute the connection-price difference, retaining the remainder
$d=d_{j,N}$ for each branch. Substituting (1.8) gives the exact rational
identity, valid on either possibly nonwinning branch,

$$
\begin{aligned}
\bar\chi_{j,N}={}&\frac{(3r^2-r)n^3}{j^2}
 +\frac{nr^2}{(a-1)^2}
                  \left(\frac{m^3}{r}+4-2m^2\right)\\
 &+\frac{drn^2}{j^2}
 -\frac{dr(r^3+r^2m+m^2)}{(a-1)^2}.
\end{aligned}
\tag{11.11}
$$

On (11.7), put $\kappa=2\sqrt6$; then
$n=\kappa\sqrt a-j$ exactly. For fixed $j=2,3$,
$r=a+O(1)$, $m=a+O(1)$ and $0\le d<r$ imply, uniformly over
all integer $N$,

$$
\bar\chi_{j,N}=\frac{3\kappa^3}{j^2}a^{7/2}+O(a^3),
\qquad
\bar\chi_{3,N}-\bar\chi_{2,N}
     =-20\sqrt6\,a^{7/2}+O(a^3).
\tag{11.12}
$$

To see the uniform remainder directly, the first term in (11.11) is
$3\kappa^3a^{7/2}/j^2+O(a^3)$, its second is $O(a^{5/2})$,
and each $d$-term is $O(a^3)$. The leading difference is
$3(2\sqrt6)^3(1/9-1/4)=-20\sqrt6$. Thus no choice of a
residue or a repair count has been hidden in (11.12).

Fix any real $D>0$ and take the integer budget
$N=\lfloor Da^{5/2}\rfloor$. Lemma 11.2 applies to $j=2,3$
with $R=5,J_0=3$ and, for example, $c=1$ once $a$ is large.
Equations (11.2), (11.10)--(11.12) give

$$
\widehat V_{3,N}-\widehat V_{2,N}
 =\left(36-\frac{20\sqrt6}{D}\right)a+O_D(\sqrt a).
\tag{11.13}
$$

Indeed its two error terms $a^5/N^2$ are $O_D(1)$, while the
price remainder divided by $N$ is $O_D(\sqrt a)$; rounding $N$
changes the leading quotient by $O_D(a^{-3/2})$. Formula (11.8)
is the special case $D=1/\sqrt6$, for which
$N=a^{5/2}/\sqrt6=a^2t$ is already an integer and the coefficient
is $36-120=-84$.

If $0<D<5\sqrt6/9$, the leading coefficient in (11.13) is strictly
negative. Both template classes are nonempty by Lemma 11.2, so the
finite original class has a minimum and

$$
V_N\le\widehat V_{3,N}<\widehat V_{2,N}.
\tag{11.14}
$$

By definition $\widehat V_{2,N}$ is the minimum over all original
graphs with any $j=2$ source template, including every partition,
endpoint array, omission array, and unbalanced tail array. The lawful
balancing argument in Lemma 11.2 is what makes this the required lower
bound for all of them. Since the only law winner is $j=2$, no exact
original minimizer at this $N$ can have the asserted old source types.
This excludes every law-winning template, rather than just a preferred
construction at that branch.

Consequently $T_{\rm src}(a,h)>\lfloor Da^{5/2}\rfloor$ for every
fixed $D<5\sqrt6/9$ and all sufficiently large $t$. Its finiteness
and upper bound follow from Theorem 9.5, independently of any behavior
at smaller budgets. Divide by $a^{5/2}$, take the lower limit and then
let $D$ increase to $5\sqrt6/9$, proving (11.9). ∎

The obstruction concerns retaining the law-winning source restriction,
not the existence of a different uniform finite-$N$ variational rule.
It neither proves $j=3$ globally optimal nor decides the critical value
$D=5\sqrt6/9$, nor proves that $a^{5/2}$ is sufficient. A theorem
at $N\asymp a^2$ would have to retain competing near-law branches
and obtain new full-domain stability and exclusion estimates. The
$\tau\le1$ premise of Theorem 9.2 cannot simply be reused at a
larger excess. No moving-$R$ result or variable-sink-budget extremum
is implied.

## 12. Sources and remaining scope of the effective selection results

The graph-specific deductions in Sections 10--11 use the existing exact
law envelope and cap competition in Growing Theorem 15.5 and Proposition
15.6, the actual-graph allocation in Sections 6--8, and Theorem 9.5's
uniform source exclusion. They do not reprove those results as new
content. The uniform legality bridge, normalized frequency separation,
coefficient separation for these particular graph functions, and the
finite-connection reversal in (11.14) are the additional relations.
The positive finite-dilution regime in
[*CDSO uniform dilution limit*, Corollary 40.3](CDSO_UNIFORM_DILUTION_LIMIT.md)
has $N/a^{3/2}\to D\in(0,\infty)$; the budgets in (10.19) and
(11.13) instead have that ratio tending to infinity, so that corollary
is not substituted for either uniform estimate here.

The analytic Wronskian criterion is the characteristic-zero statement
of Bostan--Dumas cited in Lemma 10.5. The determinant factorization
method is also present in Koiran--Portier--Tavenas, §3 and Theorem 13,
with its stated distinct-zero scope. The derivative recurrence and local
order estimate needed here are explicitly (10.9)--(10.12). The
multiquadratic sign argument is standard field theory; independence
here follows from the actual irreducible factors in (10.4), not merely
from naming square classes. Binomial series, Cauchy's coefficient
estimate and scalar convexity are intermediate tools, not separate
claims of new general results.

The maximum-endpoint-degree definition and removal of $1/\sqrt2$ are
Albalahi--Das--Ali--Barman--Hamza,
[*On the hyperbolic Sombor index and its counterpart*](https://arxiv.org/html/2510.24809v1),
§1, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176).
The general fixed-order, fixed-cyclomatic connected-graph question in
its §4 remains broader than this prescribed bipartite domain. Full-text
technical overlap with Zhao--Zhao, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
remains unassessed; it is not a premise and no worldwide-priority claim
is made. These are prose results, with no assertion of new Lean
verification or of a digestion or frozen-ledger state.

The least optimizer period and least sufficient selector threshold
remain undetermined. Proposition 10.2 identifies only the least full
allocation-state period. Theorem 10.7 gives a sufficient effective
exponential selector threshold; it does not assert a polynomial one.
Theorem 11.3 supplies a necessary lower scale for the distinct
law-winning source restriction. It leaves the exact minimizers and
phase transitions at the intermediate scale, the critical constant's
behavior, changing $R$, and varying sink budgets open.

## 追加锚（本行以下为增补区）

## 13. Original-graph localization at the finite connection scale

**Definition 13.1 (Actual threshold partition and comparison sublevel).**
Fix finite $R\ge4$, $c>0$ and $B>0$. Throughout Sections 13--14,
$a,h,N$ are integers, $a$ is sufficiently large in terms of these
fixed constants, and

$$
\frac72\sqrt a\le h\le R\sqrt a,\qquad
s=a+1+h,\qquad N\ge ca^{5/2}.
\tag{13.1}
$$

The graphs, objective and empirical law are exactly those of Definition
1.1. In particular no nonempty neighborhood is removed. Set

$$
C_*=4(R^2+20),\qquad b_R=4C_*,\qquad J_R=\lceil4C_*\rceil,
\qquad T_N=\frac{a^{7/2}}N.
\tag{13.2}
$$

For an actual graph define

$$
C=\{i:y_i\ge b_R/a\},\qquad D=[s]\setminus C.
\tag{13.3}
$$

Here $y_i=d_G(i)/N$ always denotes that graph's actual marginal. The
comparison sublevel is $W(G)\le M+BT_N$. Constants below may depend
on $R,c,B$; they are uniform in all three integers, labels, residues
and graphs on this sublevel. A fixed increase of $B$ is permitted
before fixing the constants. Eventually $h>J_R$ and $s\le2a$.

**Lemma 13.2 (A nonlinear bootstrap with no imposed marginal floor).**
Every graph on the sublevel in Definition 13.1 has, for its partition
(13.3), the following properties. Put

$$
\begin{gathered}
m=|C|=a+j,\quad r=m-1,\quad n=|D|=h+1-j,\\
u_c=j/r,\quad \alpha=(a-1)/r,\quad
\beta=j/(rn),\quad \eta=1/\beta,\\
L=|T\cap C|,\quad B_T=|T\cap D|,\quad K=|T|,\quad
A=\{B_T>0\},\quad t_k=y_k\ (k\in D),\quad
u=\sum_{k\in D}t_k.
\end{gathered}
\tag{13.4}
$$

Then

$$
\begin{gathered}
2\le j\le J_R,\qquad h^2/(aj^2)>5/2,\qquad
u>\ell_j=(j-1)/(m-2),\\
\min_{i\in C}y_i\ge1-O_{R,c,B}(a^{-1/2}),\qquad
t_k=\beta(1+O_{R,c,B}(a^{-1/4}))\quad(k\in D),\\
\mathbb P(A,K\ge2)=O_{R,c,B}(a^{-2}),\qquad
Z:=\mathbb E\left[K^2\sum_{k\in T\cap D}t_k^{-2};A,K\ge2\right]
=O_{R,c,B}(a).
\end{gathered}
\tag{13.5}
$$

These conclusions precede any bound on $H-M$ smaller than order
$a^2$. The index $j$ is not assumed to minimize the law energy.

**Proof.** All probabilities and expectations in this proof are under
$x_G$. The winning-branch formula gives
$M\le S_1\le a^3+(R^2+6)a^2$ eventually. Since $BT_N\le(B/c)a$,
Uniform Dilution Lemma 2.1 places the actual law in
$H\le a^3+C_*a^2$. Apply Growing Lemma 7.1 with $C=C_*$.
Its actual threshold is precisely (13.3). It supplies a core floor
$c_0=(8C_*+1)^{-1}$, $1\le j\le J_R$, $n\asymp_R\sqrt a$,
$u=O_R(a^{-1/2})$, and, for $v=a\mathbb P(A)$,

$$
v_*\le v\le j+O_R(a^{-1/2}).
\tag{13.6}
$$

The core estimate in the proof of that lemma and the nonlinear
common-event estimate of Uniform Dilution Lemma 2.2 give

$$
\frac{W-B_0(a)}{a^2}
\ge \frac{(h+1-j)^2}{av}+2v+2j-2
       -O_R(a^{-1/2})-O_R(a^3/N^2).
\tag{13.7}
$$

This is the inequality before scalar minimization in Uniform Dilution
Proposition 3.1, using the enlarged fixed coarse-sublevel constant.
Its core error is $O_R(a^5/N^2)$: $y_i\ge c_0$, $K\le s$, and
$H\le2a^3$ suffice. Its tail error is the common-event error
$n^4/(4N^2\mathbb P(A)^3)$, also $O_R(a^5/N^2)$ by (13.6).
Thus no individual tail floor is used in (13.7).

For completeness, write $q=h/\sqrt a$ and

$$
g_k(q)=q^2/k+4k-2,\qquad
\phi_j(q)=\min_{0<w\le j}(q^2/w+2w+2j-2),\qquad
\mathcal U(q)=\min_{1\le k\le J_R}g_k(q).
\tag{13.8}
$$

Growing Theorem 7.2 evaluates $\min_j\phi_j=\mathcal U$ on this
fixed interval. Clip $v$ to $\min(v,j)$ in (13.7). Compare with
$W\le M+BT_N\le\min_k S_k+BT_N$ and
$(S_k-B_0)/a^2=g_k(q)+O_R(a^{-1/2})$. This gives
$0\le\phi_j(q)-\mathcal U(q)=O_{R,c,B}(a^{-1/2})$.
The compact positive gap used in (9.7) applies unchanged: at a zero
of this difference $j\ne1$, and $q^2/j^2$ is at least $49/16$
for $j=2$, and at least $4(j-1)/j\ge8/3$ for $j\ge3$.
There are finitely many $j$ and $q\in[7/2,R]$. Hence $j\ge2$
and $q^2/j^2>5/2$ eventually. On $0<w\le j$ the derivative of
$q^2/w+2w$ is then at most $-1/2$. Comparing (13.7) with $S_j$
also gives $v=j+O_{R,c,B}(a^{-1/2})$. Since $au\ge v$ and
$a\ell_j=j-1+O_R(a^{-1})$, this proves $u>\ell_j$.
This scalar argument uses the nonlinear value, not a premise
$H\le M+1$.

We next retain residuals to control the individual marginals. Use the
quantities $\mathfrak a,\mathfrak b,d,Q,f_u,\mathcal S_f,
\mathcal B,\mathcal A(u),\gamma$ defined in (9.8), for the same
actual partition. In particular

$$
\begin{gathered}
Q(l)=(m-l)(r-l)(2m-1+l)\ge0\quad(0\le l\le m),\\
\mathcal A(u)=a^2+O_R(a),\qquad
\gamma=\eta^2-\mathfrak a+\mathcal A(u)\ge a^3/4,\\
\eta\asymp_R a^{3/2},\qquad
\mathcal S_f\ge\frac{a^2}{2}
           \sum_{i\in C}(y_i-(a-u)/m)^2.
\end{gathered}
\tag{13.9}
$$

The estimates in (9.9) require only bounded $j$, $q^2/j^2>5/2$,
$u=O_R(a^{-1/2})$ and the coarse core floor. Their differentiated
rational expressions, and the incidence identities (9.10)--(9.11),
therefore apply here without a small-excess hypothesis.

Put $g(z)=2(\sqrt{1+z^2}-1)$ and
$\mathcal F_N(z)=N^2g(z/N)$. On every actual incidence $K/t_k<N$
by strict orientation. Two scalar estimates needed below are

$$
\begin{aligned}
\mathcal F_N(z)-2wz
&\ge-2N^2\left(1-\sqrt{1-w^2/N^2}\right)
 \ge-w^2-Cw^4/N^2\quad(0\le w\le N/2),\\
\mathcal F_N(z)-2\eta z+\eta^2
&\ge\tfrac18(z-\eta)^2-C\eta^4/N^2
                      \quad(0\le z\le N).
\end{aligned}
\tag{13.10}
$$

The first line follows by minimizing the strictly convex scalar
function: its stationary point is
$z=w/\sqrt{1-w^2/N^2}$. The second follows from
$\mathcal F_N''(z)=2(1+z^2/N^2)^{-3/2}\ge1/\sqrt2$ on $[0,N]$,
$\mathcal F_N(\eta)\ge\eta^2-\eta^4/(4N^2)$, and
$|\mathcal F_N'(\eta)-2\eta|\le\eta^3/N^2$; Young's inequality
absorbs the last linear error. Here $\eta/N=O_{R,c}(a^{-1})$,
so the displayed restrictions on $w$ hold in every use. These are
scalar convexity statements, with their derivatives verified, rather
than convexity claims about $H$.

For $T\in A$ define $V_T=\sum_{k\in T\cap D}t_k^{-1}$ and

$$
\begin{aligned}
\widetilde{\mathcal G}_T={}&
\sum_{k\in T\cap D}\mathcal F_N(K/t_k)+Q(L)-\mathcal A(u)B_T
-2\eta V_T\\
&+\gamma B_T-\frac\gamma r\{m(B_T-1)+L\}.
\end{aligned}
\tag{13.11}
$$

Replacing just the tail quadratic energy by its exact nonlinear
energy in the algebra of (9.11)--(9.13) gives

$$
\begin{gathered}
W\ge E_j+\mathbb E[\widetilde{\mathcal G}_T;A]
 +\mathbb E[Q(L);A^c]+\mathcal S_f-C_Ra^5/N^2,\\
E_j=\mathcal B(0)+2\eta n-j\gamma/r=S_j+O_R(a).
\end{gathered}
\tag{13.12}
$$

Indeed $\mathbb E V_T=n$, $\mathbb E B_T=u$ and
$ru-j\le\mathbb E[m(B_T-1)+L;A]$ are identities or
inequalities for this actual law. The core replacement loses only
the core Taylor error already bounded after (13.7).

For a tail singleton the residual (13.11) is exactly
$\mathcal F_N(1/t_k)-2\eta/t_k+\eta^2$, so (13.10) applies.
For every other type in $A$ there is a fixed $\epsilon_R>0$ such that

$$
\widetilde{\mathcal G}_T
\ge\frac1{16}\sum_{k\in T\cap D}\mathcal F_N(K/t_k)
       +\epsilon_Ra^3-C_RB_T\eta^4/N^2.
\tag{13.13}
$$

Here is an all-cardinality verification. If $2\le K\le\sqrt a$,
apply the first line of (13.10) to $15\mathcal F_N/16$ with
$w=16\eta/(15K)$. The part after the retained $\mathcal F_N/16$
is bounded below by

$$
\eta^2\left(1-\frac{16B_T}{15K^2}\right)
-\mathcal A(u)(B_T-1)-\mathfrak bL+L^3
-\frac\gamma r(K-1)-C_RB_T\eta^4/N^2.
\tag{13.14}
$$

Since $B_T/K^2\le1/2$, the leading coefficient is at least $7/15$;
all the other negative terms before the error are $O_R(a^{5/2})$.
This proves (13.13) in this range. If $K>\sqrt a$, use
$\mathcal F_N(K/t_k)\ge\vartheta K^2/t_k^2$ with
$\vartheta=2/(1+\sqrt2)$. The actual threshold $t_k<b_R/a$
gives $2\eta/(K^2/t_k)=O_R(a^{-1/2})$. After retaining $1/16$
of the nonlinear cost, the cost minus $2\eta V_T$ is therefore
at least $(\vartheta/2)K^2\sum t_k^{-2}$ eventually. Keep
$Q(L)\ge0$ in (13.11). For $K\le m$ the remaining $\gamma$ term
$\gamma(1-(K-1)/r)$ is nonnegative; for $K>m$ its negative
part is at most $\gamma n/r=O_R(a^{5/2})$. The positive term
is at least a fixed multiple of $B_TK^2a^2$, whereas
$\mathcal A(u)B_T=O_R(a^2B_T)$. This proves (13.13) also
for every $\sqrt a<K\le s$.

Upon taking expectations, the errors in (13.10), (13.13) total at
most $C_R\eta^4u/N^2\le C_Ra^{11/2}/N^2=O_{R,c}(\sqrt a)$.
Since $W\le M+BT_N\le S_j+O_{R,c,B}(a)$, (13.12) implies

$$
\begin{gathered}
\mathbb P(A,K\ge2)\le C_{R,c,B}a^{-2},\qquad
Z\le C_{R,c,B}a,\\
\sum_{k\in D}x_{\{k\}}(t_k^{-1}-\eta)^2\le C_{R,c,B}a,\qquad
\sum_{i\in C}(y_i-(a-u)/m)^2\le C_{R,c,B}a^{-1}.
\end{gathered}
\tag{13.15}
$$

For $Z$ use $\mathcal F_N(K/t_k)\ge\vartheta K^2/t_k^2$ again.
Since $(a-u)/m=1-O_R(a^{-1})$, the last bound proves the core
assertion in (13.5).

Write $x_k=x_{\{k\}}$. If $t_k<\beta/2$, then
$(t_k^{-1}-\eta)^2\ge1/(4t_k^2)$, while the portion of $Z$ at
this label is at least $(t_k-x_k)/t_k^2$. The first three bounds
of (13.15) would imply $1/(4t_k)\le C_{R,c,B}a$. This contradicts
$1/t_k>2\eta\asymp_R a^{3/2}$. Hence every $t_k\ge\beta/2$.
Also $t_k-x_k\le\mathbb P(A,K\ge2)=O(a^{-2})=o(\beta)$, so
$x_k\ge t_k/2$ eventually. With $w=\eta t_k\ge1/2$, the singleton
bound now gives

$$
\frac\eta2\frac{(w-1)^2}{w}\le C_{R,c,B}a.
\tag{13.16}
$$

It first bounds $w$, and then gives $w=1+O_{R,c,B}(a^{-1/4})$.
This derives both sides of the tail control from the original graph.
It completes the proof of (13.5). ∎

**Lemma 13.3 (Retained energy, integer degree control and transfer).**
On the same actual-graph sublevel, use (13.4), put
$c_C=\min_{i\in C}y_i$, $\delta=\max_{k\in D}t_k$, and set

$$
\begin{gathered}
e=\mathbb E[K-1;A],\qquad
\zeta=\mathbb E[m-L;A^c],\\
\mathcal J_D=\sum_{k\in D}t_k^{-1}-n^2/u,\qquad
\bar y=(a-u)/m.
\end{gathered}
\tag{13.17}
$$

There is a uniform constant $C_{R,c,B}$ such that

$$
\begin{aligned}
W-S_j+C_{R,c,B}a^5/N^2\ \ge{}&
a^3e+\frac{a^3}{4}(u_c-u)_++\mathcal J_D\\
&+a^2\sum_{i\in C}(y_i-\bar y)^2+Z/32.
\end{aligned}
\tag{13.18}
$$

Consequently

$$
\begin{gathered}
e+|u-u_c|\le C_{R,c,B}T_N/a^3,\qquad
\zeta\le C_{R,c,B}T_N/a^2,\qquad Z\le C_{R,c,B}T_N,\\
K_u^2\le C_{R,c,B}\sqrt a
\quad\text{for every source touching }D,\\
0\le H(x_G)-W(G)\le C_{R,c,B}a^{11/2}/N^2.
\end{gathered}
\tag{13.19}
$$

**Proof.** The tail floor was derived in Lemma 13.2. It now licenses
expanding the singleton baseline, but still not expanding every
individual tail incidence with a small-ratio premise. For $K\ge2$,
strict orientation and differentiation in $K^2$ give

$$
\mathcal F_N(K/t)-\mathcal F_N(1/t)
\ge\frac{K^2-1}{\sqrt2\,t^2}.
\tag{13.20}
$$

Because $K^2\le4(K^2-1)/3$ and $2/3<1/\sqrt2$,

$$
\frac1{\sqrt2}\frac{K^2-1}{t^2}
\ge\frac58\frac{K^2-1}{t^2}+\frac1{32}\frac{K^2}{t^2}.
\tag{13.21}
$$

Summing the exact singleton baseline gives
$\sum_k t_k\mathcal F_N(1/t_k)\ge
\sum_k1/t_k-C_Rn\beta^{-3}/N^2$; its error is $O_R(a^5/N^2)$.
Apply (13.21) to the remaining tail terms and keep $Z/32$.
The signed core incidence calculation (9.22)--(9.23), which uses
only this actual law, then yields

$$
W\ge F_j(u)+\Lambda_N e+\mathcal J_D
+a^2\sum_{i\in C}(y_i-\bar y)^2+Z/32-C_{R,c,B}a^5/N^2,
\tag{13.22}
$$

where

$$
\begin{gathered}
F_j(u)=\frac{n^2}{u}+\frac{r^2m^2}{a-u}
 +\frac{m^3d((m-2)u-(j-1))}{(a-u)^2},\qquad d=2m-1,\\
\Lambda_N=\frac{15}{8\delta^2}
       -\frac{\max\{\mathfrak a,\mathfrak b\}}{c_C^2}.
\end{gathered}
\tag{13.23}
$$

In detail, the retained tail surplus is at least
$(5/8)\mathbb E[B_T(K^2-1);A]/\delta^2\ge15e/(8\delta^2)$.
The negative core incidence correction is at most
$\max\{\mathfrak a,\mathfrak b\}e/c_C^2$ by (9.22); the omitted
core term from $K^2-L^2$ is nonnegative. The scalar core function
$r^2/y+d((m-2)u-(j-1))/y^2$ has second derivative at least
$2a^2$, since $u>\ell_j$. Jensen gives exactly its stated core
variance term. The core nonlinear replacement again costs only
$O_R(a^5/N^2)$. This proves (13.22).

On $\ell_j<u<a$, the four positive terms in Growing (15.22)
prove $F_j''(u)>0$. At $u_c$ one has $F_j(u_c)=S_j$ and, by
(9.25),

$$
P_j:=-F_j'(u_c),\qquad
P_j/a^3=z_*-2+O_R(a^{-1}),\qquad
z_*:=n^2/(j^2a)>5/2-O_R(a^{-1/2}).
\tag{13.24}
$$

The already established core and tail estimates give

$$
P_j\ge a^3/4,\qquad
\frac{\Lambda_N-(m/r)P_j}{a^3}
\ge\frac78z_*-O_{R,c,B}(a^{-1/4})\ge1.
\tag{13.25}
$$

Use the supporting tangent of this scalar convex function at $u_c$.
The actual mean identity gives $(u-u_c)_+\le(m/r)e$ as in
(9.11). Paying the negative tangent with this inequality proves
(13.18), while retaining its positive side when $u<u_c$.
No law-winning-index or $H-M\le1$ premise has been used.

The cap with this bounded index is an admissible law, so $S_j\ge M$.
Also $a^5/N^2\le C_cT_N$. Thus the left side of (13.18) is at most
$C_{R,c,B}T_N$. The exact common-mean identity (9.28) gives

$$
\zeta=j-ru+r\mathbb E[B_T-1;A]+e
       \le r(u_c-u)_++me.
\tag{13.26}
$$

This proves the first line of (13.19).

For a source of degree $K\ge2$ touching at least one tail, its
single contribution to $Z$ is at least $K^2/(N\delta^2)$. Its
empirical mass is at least $1/N$; repeated identical neighborhoods
only increase that mass. Hence

$$
K^2\le N\delta^2Z\le C_{R,c,B}N\beta^2T_N
                      \le C_{R,c,B}\sqrt a.
\tag{13.27}
$$

A tail singleton already has $K=1$. This proves the degree conclusion
for actual graph sources, rather than for a selected template.

Finally the edge inequality (11.6) applies to the entire actual graph.
For cores, $K\le s$, $y_i\ge1/2$ and $H\le2a^3$ bound its error
by $C_Ra^5/N^2$. For tails, (13.27), $t_k\ge\beta/2$ and

$$
H_D=\sum_k t_k^{-1}
 +\mathbb E\left[(K^2-1)\sum_{k\in T\cap D}t_k^{-2};A,K\ge2\right]
\le C_Ra^2+Z\le C_{R,c,B}a^2
\tag{13.28}
$$

bound the error by

$$
\frac1{4N^2}\mathbb E\left[K^4\sum_{k\in T\cap D}t_k^{-4}\right]
\le\frac{C_{R,c,B}\sqrt a}{N^2\beta^2}H_D
\le C_{R,c,B}\frac{a^{11/2}}{N^2}.
\tag{13.29}
$$

The core and tail errors prove the last line of (13.19). Every
denominator, source cardinality and energy in this transfer belongs
to $x_G$; no marginal from a cap has replaced an actual marginal. ∎

## 14. A defect expansion and the full-class finite-connection envelope

**Lemma 14.1 (First variation controlled by actual incidence defects).**
For every graph on the sublevel of Definition 13.1, let $j$ and its
actual partition be as above. Define $\rho_j$ algebraically by (2.1),
without requiring $j\in J_*$. Then

$$
W(G)\ge S_j+\sum_T\rho_j(L,B_T)x_{G,T}
                   -C_{R,c,B}a^{11/2}/N^2.
\tag{14.1}
$$

Moreover the integer price sum of every connected graph, with this
partition, satisfies

$$
N\sum_T\rho_j(L,B_T)x_{G,T}
             \ge nb_j+d_{j,N}c_j=\bar\chi_{j,N}.
\tag{14.2}
$$

**Proof.** Write $p=\mathbb P(A)$ and, for $i\in C$, set

$$
\begin{gathered}
v_i=y_i-\alpha,\qquad
D_i=\mathbb P(i\notin T,A^c),\qquad
l_i=\mathbb P(i\in T,A),\\
q_i^C=\mathbb E[(K^2-m^2)\mathbf1_{i\in T}].
\end{gathered}
\tag{14.3}
$$

The identity $y_i=1-p-D_i+l_i$ gives
$v_i=u_c-p-D_i+l_i$. Here
$\sum D_i=\zeta$, $\sum l_i=\mathbb E[L;A]\le2e$,
and $|p-u_c|\le|u-u_c|+\mathbb E[B_T-1;A]\le C T_N/a^3$.
Consequently Lemma 13.3 gives the stronger summed displacement bound

$$
\sum_{i\in C}|v_i|\le C T_N/a^2.
\tag{14.4}
$$

For a core-only type,
$|K^2-m^2|L=(m-L)(m+L)L\le2m^2(m-L)$.
For a type meeting the tail, $|K^2-m^2|\le C_Ra^2$ and
$\mathbb E[L;A]\le2e$. Thus

$$
\sum_{i\in C}|q_i^C|\le C_Ra^2(\zeta+e)\le C T_N.
\tag{14.5}
$$

In this proof $C$ may depend on $R,c,B$. The exact core energy is

$$
H_C=m^2\sum_{i\in C}\frac1{y_i}
                 +\sum_{i\in C}\frac{q_i^C}{y_i^2}.
\tag{14.6}
$$

Taylor expansion at $y_i=\alpha$, using $y_i,\alpha\ge1/2$,
has constant and linear terms
$m^3/\alpha-m^2\alpha^{-2}\sum v_i+\alpha^{-2}\sum q_i^C$.
Its absolute remainder is bounded by

$$
C\left(a^2\sum_i v_i^2+\sum_i|q_i^Cv_i|\right)
\le C T_N^2/a^2.
\tag{14.7}
$$

This uses summed actual defects, rather than the much larger bound
obtained by multiplying total exceptional mass by $m$.

For tails set

$$
q_k^D=\mathbb E[(K^2-1)\mathbf1_{k\in T};A,K\ge2],\qquad
Q_D=\sum_{k\in D}q_k^D,\qquad \omega_k=t_k-\beta.
\tag{14.8}
$$

All $q_k^D$ are nonnegative. Since $t_k\le\delta$,

$$
Q_D\le\delta^2Z\le C\beta^2T_N,\qquad
\sum_k(q_k^D)^2\le Q_D^2.
\tag{14.9}
$$

The exact tail energy is $\sum_k(1/t_k+q_k^D/t_k^2)$.
On $\beta/2\le t_k\le3\beta/2$ the reciprocal identity and
the derivative bound for $t^{-2}$ give

$$
\begin{aligned}
H_D\ge{}&\frac n\beta-\beta^{-2}\sum_k\omega_k
          +\beta^{-2}Q_D+\frac2{3\beta^3}\|\omega\|_2^2
          -16\beta^{-3}Q_D\|\omega\|_2\\
\ge{}&\frac n\beta-\beta^{-2}\sum_k\omega_k
          +\beta^{-2}Q_D+\frac1{3\beta^3}\|\omega\|_2^2
          -192\beta^{-3}Q_D^2.
\end{aligned}
\tag{14.10}
$$

The final negative term is at most $C\beta T_N^2$, by (14.9).
Together with (14.7), its magnitude is at most

$$
C(a^{-2}+\beta)T_N^2\le C a^{11/2}/N^2.
\tag{14.11}
$$

The constant term of the combined core and tail expansions is $S_j$.
Their linear term is exactly
$DH(x^{j,*})[x_G-x^{j,*}]=\sum_T\rho_j(L,B_T)x_{G,T}$.
Lemma 2.3 is a differentiation and affine-subtraction identity; its
proof uses only normalization and mean $a$, so it remains valid for
this possibly nonwinning cap. The transfer in Lemma 13.3 now proves
(14.1).

To license (14.2), positivity cannot be inferred merely from having
a bounded index. Here it follows from the additional derived margin
$z_*>5/2-O_R(a^{-1/2})$. In fact (2.6) gives, uniformly at this
actual index,

$$
rc_j=(z_*-2)a^3+O_R(a^2)>0,\quad
b_j=3z_*a^3+O_R(a^2),\quad
0<rc_j<\eta^2<b_j.
\tag{14.12}
$$

Also $\eta^2>(2m^2+4)/\alpha^2$ eventually. The exact identities
(2.3), (2.7), (2.8) therefore prove all the price comparisons in
Lemma 2.2 for this index, without using law optimality. Its proof
covers every $1\le K\le s$. The connected contraction count (4.3)
and the congruence $(a-1)N\equiv b-D_0\pmod r$ in (4.7)
are likewise independent of law optimality. Applying the proof of
Lemma 4.1 with these now verified price hypotheses gives (14.2),
for all residues $0\le d_{j,N}<r$. This is a lower bound over
original connected graphs and all their neighborhoods. It makes no
claim that equality in the energy requires price equality. ∎

**Theorem 14.2 (Uniform finite-connection value over the prescribed
full graph class).** For each fixed finite $R\ge4$ and $c>0$,
there are finite positive $A_{R,c},C_{R,c}$ such that, for every
integer $a\ge A_{R,c}$, every integer
$(7/2)\sqrt a\le h\le R\sqrt a$, and every integer
$N\ge ca^{5/2}$, the graph class in Definition 1.1 is nonempty.
Use the fixed $J_R$ in (13.2) and the algebraically extended prices
of Definition 11.1 to define

$$
L_N=\min_{2\le j\le J_R}
             \left(S_j+\frac{\bar\chi_{j,N}}N\right).
\tag{14.13}
$$

Then its full-class minimum satisfies

$$
|V_N-L_N|\le C_{R,c}\frac{a^{11/2}}{N^2}.
\tag{14.14}
$$

The assertion includes every integer remainder in every branch.
In particular, on any fixed window
$c\le N/a^{5/2}\le C'<\infty$, it gives
$V_N=L_N+O_{R,c}(\sqrt a)$. For every exact minimizer the
partition (13.3) has a derived index $2\le j\le J_R$ and

$$
S_j+\bar\chi_{j,N}/N\le L_N+C_{R,c}a^{11/2}/N^2.
\tag{14.15}
$$

**Proof.** For large $a$ every $2\le j\le J_R$ has $n>0$.
Lemma 11.2 applies to every such branch, at all our integer budgets.
It proves nonemptiness, the graph conditions including strict
orientation, and

$$
V_N\le L_N+C_{R,c}a^5/N^2.
\tag{14.16}
$$

The minimum exists because the labeled graph domain is finite.
Every winning law index belongs to this bounded interval, by Growing
Theorem 15.5 and Lemma 15.2. For such an index
$|\bar\chi_{j,N}|\le C_Ra^{7/2}$, uniformly in its residue.
Thus (14.16), or that single winning template, puts every exact
minimizer in $W\le M+B_RT_N$ after fixing a sufficiently large
$B_R$; $a^5/N^2=o(T_N)$ uniformly here. Lemmas 13.2--14.1
apply to that actual minimizer. They give

$$
V_N\ge S_j+\bar\chi_{j,N}/N-C_{R,c}a^{11/2}/N^2
       \ge L_N-C_{R,c}a^{11/2}/N^2.
\tag{14.17}
$$

Together with (14.16) this proves (14.14) and (14.15).
The lower argument ranges over the entire original graph class:
the comparison sublevel is justified by an available original-graph
upper bound, and localization within it is proved from its actual
nonlinear value. In particular it assumes neither template membership,
a tail floor, a tail-touching degree cutoff, a winning law branch,
nor an excess at most one. ∎

## 15. Global leading competition on the integer transition family

**Theorem 15.1 (Actual core switch and leading global value).** Let

$$
a=6t^2,\qquad h=12t-1,\qquad N=\lfloor Da^{5/2}\rfloor,
\qquad D>0\text{ fixed},\qquad t\in\mathbb Z_{>0},\quad t\to\infty.
\tag{15.1}
$$

Use $R=5$ and the actual marginal threshold (13.3), with its fixed
$b_5$. Then

$$
\frac{V_N-M}{a}\longrightarrow
 \min\left\{\frac{36\sqrt6}{D},\ 36+\frac{16\sqrt6}{D}\right\}.
\tag{15.2}
$$

Set $D_c=5\sqrt6/9$. For every sufficiently large $t$, every exact
minimizer has

$$
|C|=
\begin{cases}
a+3,&0<D<D_c,\\
a+2,&D>D_c.
\end{cases}
\tag{15.3}
$$

These are actual threshold core sizes; no exact source-template
membership is asserted. At the exact integer budget $N=a^2t$,

$$
V_N=M+132a+O(\sqrt a),\qquad |C|=a+3
\quad\text{for every exact minimizer eventually}.
\tag{15.4}
$$

**Proof.** Reuse the exact computations (11.10)--(11.12). They give
$M=S_2$, $S_3-S_2=36a+O(\sqrt a)$, and, uniformly over all
residues,

$$
\bar\chi_{2,N}=36\sqrt6\,a^{7/2}+O(a^3),\qquad
\bar\chi_{3,N}=16\sqrt6\,a^{7/2}+O(a^3).
\tag{15.5}
$$

One must also exclude the other bounded branches in the global
finite envelope. For each $2\le j\le J_5$,

$$
\frac{S_j-B_0(a)}{a^2}\longrightarrow 24/j+4j-2.
\tag{15.6}
$$

This scalar sequence has its only minima at $j=2,3$, both with
value $18$: its adjacent difference is $4-24/(j(j+1))$.
The finite remaining index set therefore has a fixed positive gap.
Its $S_j-S_2$ is bounded below by a positive multiple of $a^2$.
For all these fixed indices, including the nonwinning ones,
$|\bar\chi_{j,N}|=O(a^{7/2})$ by the rational formula (11.11).
Dividing by $N$ gives only $O_D(a)$ and cannot close that gap.
Thus the minimum defining $L_N$ is attained among $j=2,3$ eventually.

Theorem 14.2 has error $O_D(\sqrt a)$ at (15.1). Combining it
with (15.5), and retaining the harmless floor in $N$, yields

$$
V_N=M+a\min\left\{\frac{36\sqrt6}{D},\
                              36+\frac{16\sqrt6}{D}\right\}
           +O_D(\sqrt a).
\tag{15.7}
$$

Indeed the $O(a^3)$ price remainders divided by $N$ are
$O_D(\sqrt a)$, and rounding $N$ changes the displayed leading
quotients by $O_D(a^{-3/2})$. This proves (15.2), also at $D=D_c$.

For an exact minimizer, (14.15) first excludes every actual threshold
index except $2,3$, by the same order-$a^2$ gap. The signed difference
between their finite comparison values is

$$
\left(36-\frac{20\sqrt6}{D}\right)a+O_D(\sqrt a).
\tag{15.8}
$$

Away from $D_c$ its order-$a$ gap exceeds the $O_D(\sqrt a)$
allowance in (14.15). It forces $j=3$ below $D_c$ and $j=2$
above $D_c$, proving (15.3) for every exact minimizer. Lemma 13.2
also gives $y_i\ge1-O_D(a^{-1/2})$ on this actual core and
$y_k\asymp a^{-3/2}$ on its complement, so the fixed threshold
in (13.3) identifies the branch unambiguously.

Finally $N=a^2t=a^{5/2}/\sqrt6$ is an integer. Take
$D=1/\sqrt6<D_c$ in (15.7). The competing coefficients are $216$
and $36+96=132$, proving both assertions in (15.4). ∎

## 16. Sources and unresolved finite structure

The new relations in Sections 13--15 are deductions for the prescribed
graph class: the nonlinear residual with retained exceptional-tail
energy, its actual marginal floor, the integer incidence degree bound,
the defect-controlled first variation, and their full-class value and
threshold-core consequences. The law envelopes, scalar phase gaps,
price contraction argument and template constructions are reused from
Growing Lemma 7.1, Theorem 7.2, Theorem 15.5 and Proposition 15.6,
Uniform Dilution Lemmas 2.1--2.2 and Proposition 3.1, and Sections
2, 4, 9 and 11 of this volume. Each use beyond an old small-excess or
winning-index hypothesis is accompanied above by its required
inequalities; it is not an extension by assertion.

Scalar supporting tangents and Jensen are used only after the displayed
second derivatives or positive coefficients verify their hypotheses;
see Boyd--Vandenberghe, *Convex Optimization*, §3.1.3, printed pp.69--70,
[author text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
The conjugate in (13.10) is obtained by the displayed stationary-point
calculation. These scalar tools are standard intermediate facts;
no new general convexity theorem or convexity of the law energy is
claimed.

The primary CDSO definition and broader extremal question are
Albalahi--Das--Ali--Barman--Hamza,
[*On the hyperbolic Sombor index and its counterpart*](https://arxiv.org/html/2510.24809v1),
§§1,4, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176).
There the denominator is the maximum endpoint degree; subtracting the
edge count gives the excess in (1.4). Smirnov,
[*Bicyclic graphs with maximum complementary diminished Sombor index*](https://www.dmlett.com/archive/v18/DML26_v18_pp100-106.pdf),
Discrete Math. Lett. 18, 100--106, DOI
[10.47443/dml.2026.164](https://doi.org/10.47443/dml.2026.164),
Theorem 2.1, determines the bicyclic maxima and disproves the stated
minimum-degree prediction for those maxima. It is not a minimum theorem
in the present growing-cyclomatic prescribed bipartite domain.
Zhao--Zhao, *Extremal values with respect to vertex-degree-based
topological indices in unicyclic and bicyclic graphs*, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
has an abstract describing sufficient conditions for almost regular
extremizers and maximum VDB indices in those two fixed-cyclomatic
classes. Its detailed full-text overlap remains unassessed. Neither
its abstract nor inaccessible technical content is a premise here.
These distinctions preclude treating every part of the broader question
as unresolved, and make no worldwide-priority claim for the deductions.

Theorem 14.2 determines a uniform value envelope, and Theorem 15.1
identifies an actual threshold partition away from its critical
constant. They leave the critical constant's finite branch behavior,
exact source support, global optimality of a particular $j=3$ template,
and sufficiency of $a^{5/2}$ for eventual exact source restriction
undetermined. The threshold-core conclusion is weaker than such a
source restriction. Moving $R$, changing the prescribed sink budget,
and the unrestricted original connected-graph extremal problem are
outside these theorems.

## 追加锚（本行以下为增补区）

## 17. Connected incidence floors and the sharper full-class envelope

**Definition 17.1 (Tail incidence excess and price slack).** Fix finite
$R\ge4$, $c>0$ and $B>0$, and use exactly the integer domain,
original graphs, nonlinear objective and actual threshold partition of
Definition 13.1. Thus $a$ is sufficiently large in terms of these
constants, $(7/2)\sqrt a\le h\le R\sqrt a$,
$N\ge ca^{5/2}$ and $W(G)\le M+BT_N$. All notation
$m,r,n,j,\alpha,\beta,\eta,T_N$ belongs to this actual partition.
For each tail let $q_k=q_k^D$ be (14.8), and put

$$
\begin{gathered}
Q=\sum_{k\in D}q_k,\qquad
I=NQ-3n,\\
\mathcal P=\sum_{u\in S}\rho_j(L_u,B_u),\qquad
\Pi=\mathcal P-\bar\chi_{j,N}.
\end{gathered}
\tag{17.1}
$$

Here $\mathcal P$ is the unnormalized price sum over actual source
vertices, including repeated neighborhoods with their multiplicities.
The algebraic prices are those of (1.8) and (2.1), even when this
actual $j$ is not a law winner. No source neighborhood is excluded.

**Lemma 17.2 (A connected floor and coercivity of the price slack).**
On the domain of Definition 17.1, uniformly over every integer residue,

$$
\begin{gathered}
q_k\ge3/N\quad(k\in D),\qquad I\in\mathbb Z_{\ge0},\\
\Pi\ge\tfrac14\eta^2 I,\\
\sum_{k\in D}q_k^2\le\frac{9n}{N^2}+\frac{3QI}{N}.
\end{gathered}
\tag{17.2}
$$

**Proof.** Lemma 13.2 gives $2\le j\le J_R$, $n\asymp_R\sqrt a$,
$\alpha\ge1/2$, $\beta\asymp_R a^{-3/2}$ and the strict margin
$n^2/(j^2a)>5/2-O_R(a^{-1/2})$. Thus (14.12) verifies the price
hypotheses at this actual index. In addition, its uniform expansions
and $\eta^2\asymp_R a^3$ imply, after increasing $a$,

$$
0<rc_j<\eta^2,\qquad b_j\ge2\eta^2,\qquad
\eta^2\ge2A_c,\qquad A_c=\frac{2m^2+4}{\alpha^2}.
\tag{17.3}
$$

These uses require only bounded $j$ and the displayed strict margin,
not $S_j=M$. All identities (2.3), (2.7), (2.8) remain algebraic
identities at this index.

Every tail has an incident source of degree at least two. Otherwise
that tail and all its incident singleton sources would be a component
separate from the nonempty core. Such a source contributes at least
$3/N$ to $q_k=N^{-1}\sum_{u:k\in T_u}(K_u^2-1)$.
This proves the first assertion and integrality of $I$.

For a source write $\tau_u=q(L_u,B_u)$ as in (4.2), and set

$$
D_u=B_u(K_u^2-1)-3\tau_u,\qquad
\tau=\sum_u\tau_u.
\tag{17.4}
$$

These are nonnegative integers. A tail singleton and a core--tail
connector have $D_u=0$. A mixed source of size $K\ge3$ has
$D_u=B(K^2-4)\ge5$. A tail-only source with $B\ge2$ has
$D_u=B^3-4B+3\ge3$. A core-only source has $D_u=0$.
Connectedness gives $\tau\ge n$ by precisely the contraction of
(4.3), for the same actual graph, so

$$
I=3(\tau-n)+\sum_uD_u.
\tag{17.5}
$$

Call a tail-touching source bad if it is neither a singleton nor a
core--tail connector. Its price satisfies the quantitative strengthening

$$
\rho_j(L,B)-\tau_u b_j
\ge rc_j+\tfrac14\eta^2D_u.
\tag{17.6}
$$

To check every mixed bad type, the second line of (2.7) is at least
$-A_cK$, and $1-(L-1)/r\ge0$. Subtracting the right side of
(17.6) from (2.7), and using $rc_j<\eta^2$, leaves at least

$$
\eta^2\{B(3K^2/4-4)-1\}-A_cK\ge0.
\tag{17.7}
$$

Indeed $B\ge1$, $K\ge3$ imply the expression in braces is at
least $K/2$: the polynomial $3K^2/4-K/2-5$ is positive at
$K=3$ and increasing thereafter. Equation (17.3) proves the last
inequality. This argument covers all $3\le K\le s$.
For a tail-only bad type, (2.8), $2m^2-4>0$ and $rc_j<\eta^2$
leave at least

$$
\eta^2\{3B^3/4-4B+9/4\}>0
\tag{17.8}
$$

after subtracting (17.6). The polynomial in braces is $1/4$ at
$B=2$ and has positive derivative on $[2,\infty)$. This checks
all tail-only types as well. Core-only prices are nonnegative by
(2.3) and $c_j>0$.

Write $d=d_{j,N}$, so $0\le d<r$. If there are $b_{\rm bad}\ge1$
bad sources, summing (17.6) and the connector prices gives

$$
\begin{aligned}
\Pi&\ge(\tau-n)b_j+(b_{\rm bad}r-d)c_j
                   +\tfrac14\eta^2\sum_uD_u\\
&\ge\tfrac14\eta^2\{3(\tau-n)+\sum_uD_u\}
 =\tfrac14\eta^2I.
\end{aligned}
\tag{17.9}
$$

If there are none and $\tau\ge n+1$, the same conclusion follows
from

$$
\Pi\ge(\tau-n)b_j-dc_j
\ge(\tau-n)(b_j-rc_j)\ge(\tau-n)\eta^2,
\tag{17.10}
$$

because now $I=3(\tau-n)$. If there are none and $\tau=n$,
then $I=0$. The actual edge budget gives
$D_0\equiv n-(a-1)N\pmod r$ by (4.7), where $D_0$ is the
nonnegative total core-only omission count (4.5). Hence $D_0\ge d$,
and (4.6) gives $\Pi\ge0$. This completes the price inequality
without imposing any congruence restriction on $N$.

Finally set $z_k=q_k-3/N\ge0$. Their sum is $I/N$, and
$Q\ge3n/N\ge3/N$. Therefore

$$
\begin{aligned}
\sum_kq_k^2
&=9n/N^2+(6/N)\sum_kz_k+\sum_kz_k^2\\
&\le9n/N^2+(6/N+\sum_kz_k)I/N
 \le9n/N^2+3QI/N.
\end{aligned}
\tag{17.11}
$$

The last step uses $6/N\le2Q$ and $\sum z_k\le Q$.
This is a coordinate incidence bound; it does not replace the vector
$(q_k)$ by independently chosen marginal optimizers. ∎

**Lemma 17.3 (Sharp nonlinear transfer and an absorbed remainder).**
There is a constant $C_{R,c,B}$ such that every graph of Definition
17.1 satisfies the following bounds, uniformly in its labels and all
three integers:

$$
\begin{gathered}
0\le H(x_G)-W(G)\le C_{R,c,B}a^5/N^2,\\
W(G)\ge S_j+\bar\chi_{j,N}/N+\Pi/(2N)
                           -C_{R,c,B}a^5/N^2.
\end{gathered}
\tag{17.12}
$$

**Proof.** All expectations are under the actual law $x_G$. Lemmas
13.2--13.3 apply with the fixed $R,c,B$ in Definition 17.1. They
give $y_i\ge1/2$ on the actual core, $\beta/2\le t_k\le3\beta/2$
on its tail, $Z\le CT_N$, and $K^2\le C\sqrt a$ for every
actual source touching the tail. These are conclusions of localization,
not extra domain restrictions.

Use the exact nonlinear inequality (11.6), equivalently

$$
0\le H-W\le\frac1{4N^2}
\mathbb E\left[K^4\sum_{i\in T}y_i^{-4}\right].
\tag{17.13}
$$

The core part of the expectation is at most
$s^4\sum_{i\in C}y_i^{-3}\le Ca^5$. The tail singleton part
is at most $\sum_kt_k^{-3}\le Cn\beta^{-3}\le Ca^5$.
For the remaining tail incidences, retain their exceptional energy
rather than charging the singleton baseline with their degree bound:

$$
\mathbb E\left[K^4\sum_{k\in T\cap D}t_k^{-4};A,K\ge2\right]
\le C\sqrt a\,\beta^{-2}Z
\le C\sqrt a\,\beta^{-2}T_N.
\tag{17.14}
$$

Dividing this by $N^2$ gives $Ca^7/N^3\le C_{R,c,B}a^5/N^2$,
since $a^2/N\le c^{-1}a^{-1/2}$. This proves the first line of
(17.12) directly for the original nonlinear $W$.

For the law expansion, the actual summed core defects (14.4)--(14.5)
give the Taylor remainder (14.7) at $\alpha$, of absolute value
at most $CT_N^2/a^2=Ca^5/N^2$. These estimates hold on the
present sublevel with its actual bounded index; no winning-index
hypothesis entered their proof. At a tail write $\omega_k=t_k-\beta$.
The reciprocal identity and the derivative bound
$|(t^{-2})'|\le16\beta^{-3}$ on $[\beta/2,3\beta/2]$ give,
coordinate by coordinate,

$$
\begin{aligned}
\frac1{t_k}+\frac{q_k}{t_k^2}
\ge{}&\frac1\beta-\frac{\omega_k}{\beta^2}
 +\frac{q_k}{\beta^2}
 +\frac{2\omega_k^2}{3\beta^3}
 -\frac{16q_k|\omega_k|}{\beta^3}\\
\ge{}&\frac1\beta-\frac{\omega_k}{\beta^2}
 +\frac{q_k}{\beta^2}
 +\frac{\omega_k^2}{3\beta^3}
 -\frac{192q_k^2}{\beta^3}.
\end{aligned}
\tag{17.15}
$$

For the first line use
$1/t=1/\beta-\omega/\beta^2+\omega^2/(\beta^2t)$;
the second is completion of a square. In particular the negative
remainder is the sum of the coordinate squares $q_k^2$, rather
than the square of their total.

The constant and linear terms of this tail expansion and the core
expansion are exactly $S_j+\mathcal P/N$. This follows from
(2.9)--(2.10) because this same empirical law has total mass one and
mean $a$, and the cap with these parameters has marginals
$\alpha,\beta$. Differentiation and affine subtraction in that
identity do not require the cap to minimize $H$. Thus

$$
H\ge S_j+\mathcal P/N-Ca^5/N^2
                         -192\beta^{-3}\sum_kq_k^2.
\tag{17.16}
$$

Here $Q\le\delta^2Z\le C\beta^2T_N$ by (14.9), with
$\delta=\max t_k$. Apply both inequalities of Lemma 17.2:

$$
\begin{aligned}
\beta^{-3}\sum_kq_k^2
&\le9n\beta^{-3}/N^2+3\beta^{-3}QI/N\\
&\le Ca^5/N^2+C\beta^{-1}T_NI/N\\
&\le Ca^5/N^2+C\beta T_N\Pi/N\\
&\le Ca^5/N^2+C(a^2/N)\Pi/N.
\end{aligned}
\tag{17.17}
$$

The first term is of the desired order because
$n\asymp_R\sqrt a$ and $\beta\asymp_R a^{-3/2}$. The second
term is paid by actual price slack. Since $a^2/N\le c^{-1}a^{-1/2}$,
its coefficient is at most $1/2$ after increasing the uniform threshold
for $a$. Substitute $\mathcal P=\bar\chi_{j,N}+\Pi$ into
(17.16), and then use the first line of (17.12), already proved.
The result is the second line of (17.12). No assertion of convexity
of the full law energy or of exact source support is needed. ∎

**Theorem 17.4 (The $a^5/N^2$ envelope over all prescribed graphs).**
For every fixed finite $R\ge4$ and $c>0$ there are finite positive
$A_{R,c},C_{R,c}$ such that, for every integer $a\ge A_{R,c}$,
every integer $(7/2)\sqrt a\le h\le R\sqrt a$, and every integer
$N\ge ca^{5/2}$, the original graph class of Definition 1.1 is
nonempty and its minimum satisfies

$$
|V_N-L_N|\le C_{R,c}a^5/N^2.
\tag{17.18}
$$

Here $L_N$ is exactly (14.13), with the same fixed $J_R$ and every
actual residue $d_{j,N}$. Every exact minimizer, with its actual
threshold core $C=\{i:y_i\ge b_R/a\}$, has $|C|=a+j$ for
$2\le j\le J_R$ and satisfies

$$
S_j+\bar\chi_{j,N}/N\le L_N+C_{R,c}a^5/N^2.
\tag{17.19}
$$

The domain retains simplicity, connectedness, bipartition, $N$ sources,
$s=a+1+h$ sinks, exactly $aN$ edges and strict orientation (1.3).
There is no restriction on its nonempty source neighborhoods or on
integer remainders.

**Proof.** Apply Lemma 11.2 with $J_0=J_R$, the fixed $R,c$ above,
and $N\ge ca^{5/2}\ge ca^2$. Every branch in (14.13) has $n>0$
for large $a$, and that lemma provides legal balanced suppliers for
all its residues, including all graph conditions and strict orientation.
It gives nonemptiness and

$$
V_N\le L_N+C_{R,c}a^5/N^2.
\tag{17.20}
$$

The minimum exists in the finite labeled original graph class. As in
the proof of Theorem 14.2, a winning law index is in $[2,J_R]$,
and its supplier has $W\le M+B_RT_N$ for a fixed sufficiently
large $B_R$. Indeed $|\bar\chi_{j,N}|\le C_Ra^{7/2}$ there and
$a^5/N^2=o(T_N)$ uniformly over the present domain. Thus every
exact minimizer lies on the comparison sublevel with $B=B_R$.
Lemma 13.2 derives its actual partition and index, and Lemma 17.3,
with precisely these fixed constants, gives

$$
V_N\ge S_j+\bar\chi_{j,N}/N-C_{R,c}a^5/N^2
       \ge L_N-C_{R,c}a^5/N^2.
\tag{17.21}
$$

Together with (17.20) this proves (17.18), and comparison of the two
bounds proves (17.19) after enlarging $C_{R,c}$. The retained price
slack in (17.12) is nonnegative. The lower argument concerns every
actual minimizer in the full original class, without converting it into
a template. ∎

## 18. Actual core selection on the exact critical integer sequence

**Theorem 18.1 (Critical residues and the eventual actual core).**
Let $t$ range over positive integers and set

$$
a=6t^2,\qquad h=12t-1,\qquad N=120t^5.
\tag{18.1}
$$

Use $R=5$ and the actual threshold $b_5/a$ of (13.3). For all
sufficiently large $t$, every exact minimizer in the original graph
class has $|C|=a+2$. With $k=[t]_3\in\{0,1,2\}$ and
$E_{j,N}=S_j+\bar\chi_{j,N}/N$, the signed comparison is

$$
\begin{aligned}
d_{2,N}&=\frac{k(6t^2+1)+56t-6}{3},\qquad
 d_{3,N}=52t-3\quad(t\ge10),\\
E_{3,N}-E_{2,N}
 &=\frac{204-12k}{5}\,t+\frac{408+6k}{5}+R_k(t),\qquad
 |R_k(t)|\le\frac{132}{t}\quad(t\ge10).
\end{aligned}
\tag{18.2}
$$

In particular the signed gap is at least $36t$ for $t\ge10$,
whereas the full-class value error and actual-index allowance in
Theorem 17.4 are bounded independently of $t$. Moreover
$V_N=E_{2,N}+O(1)$. These conclusions concern the actual threshold
core, and do not identify every source neighborhood of an optimizer.

**Proof.** Here $h/\sqrt a=2\sqrt6-1/(\sqrt6t)$ lies in $[7/2,5]$
eventually and

$$
N/a^{5/2}=5\sqrt6/9=:D_c,\qquad a^5/N^2=27/50.
\tag{18.3}
$$

Take, for example, $c=1$ in Theorem 17.4, since $D_c>1$.
Its uniform error and actual-index comparison are therefore $O(1)$.

For the residue calculation, $a-1\equiv-j\pmod{a+j-1}$, so
$d_{j,N}=[n+jN]_{a+j-1}$. The exact divisions are

$$
\begin{aligned}
3(12t-2+240t^5)
 &=(120t^3-20t)(6t^2+1)+56t-6,\\
12t-3+360t^5
 &=(60t^3-20t)(6t^2+2)+52t-3.
\end{aligned}
\tag{18.4}
$$

The fractional part of $(120t^3-20t)/3$ is $k/3$. For $t\ge10$,
$0<56t-6<6t^2+1$ and $0<52t-3<6t^2+2$. Consequently the
expressions for $d_{2,N},d_{3,N}$ in (18.2) are integers in their
required residue intervals, not merely congruent real expressions.
This includes all three congruence classes of the parameter $t$.

For completeness the deciding rational remainder can be written without
an asymptotic sign assumption. Define

$$
\begin{aligned}
P_k(t)={}&(648k-72576)t^8+(864k+12960)t^7
 +(1656k-1764)t^6\\
&-(216k+77040)t^5+(246k+11928)t^4-15652t^3\\
&+(20k+278)t^2+(2k-1280)t+k+72.
\end{aligned}
\tag{18.5}
$$

Substitution of the actual residues into the exact rational formula
(11.11), together with $S_3-S_2$ in (11.10), gives the identity

$$
E_{3,N}-E_{2,N}
=\frac{204-12k}{5}t+\frac{408+6k}{5}
 +\frac{P_k(t)}{60t^5(6t^2-1)^2}.
\tag{18.6}
$$

One can obtain the same identity directly from (1.8): on branch $j$
insert $m=6t^2+j$, $r=6t^2+j-1$, $n=12t-j$,
$\alpha=(6t^2-1)/r$, $\eta=rn/j$ into $S_j+(nb_j+d_{j,N}c_j)/N$.
Clearing the denominator $60t^5(6t^2-1)^2$ after subtracting the
two displayed polynomial terms yields exactly (18.5). Thus the sign
uses the repair residues as well as the connection prices.

For $k=0,1,2$ the sum of the absolute values of the coefficients of
$P_k$ is bounded by

$$
72576+14688+1764+77472+12420+15652+318+1280+74
=196244.
\tag{18.7}
$$

For $t\ge1$ its numerator is consequently at most $196244t^8$
in absolute value, while its denominator is at least $1500t^9$,
since $6t^2-1\ge5t^2$. The quotient is less than $132/t$.
The coefficient $(204-12k)/5$ is at least $36$, and
$(408+6k)/5-132/t>0$ for $t\ge10$. This proves the explicit
positive gap in (18.2).

It remains to connect this comparison to every original minimizer.
The finite-index argument (15.6) applies with the same fixed $R=5$:
among $2\le j\le J_5$, the leading coefficients
$24/j+4j-2$ have their only minima at $j=2,3$. For every other
index there is a common positive order-$a^2$ gap from $S_2$,
because this is a fixed finite index set. Formula (11.11), with
$0\le d_{j,N}<r$ on each of these bounded branches, bounds every
price correction by $O(a^{7/2}/N)=O(a)$. Thus all other $E_{j,N}$
exceed $E_{2,N}$ by a positive multiple of $a^2$ eventually.
Equation (18.2) then proves $L_N=E_{2,N}$ eventually.

If an exact minimizer had actual index $j=3$, (17.19) would give
$E_{3,N}-E_{2,N}\le(27/50)C_{5,1}$, contradicting the gap
$36t$ once $t>(3/200)C_{5,1}$. The other bounded indices have
already been excluded by their order-$a^2$ gap and the same bounded
allowance. Every actual index therefore equals two for all sufficiently
large $t$, proving $|C|=a+2$. Lemma 13.2 also gives
$y_i\ge1-O(a^{-1/2})$ on this core and $y_k\asymp a^{-3/2}$
outside it, so the stated fixed marginal threshold does distinguish the
two parts of the actual graph. Finally (17.18) and (18.3) give
$V_N=E_{2,N}+O(1)$. ∎

## 19. Mathematical sources and the remaining finite structure

The incidence floor, its quantitative price-slack bound (17.2), the
coordinate-square absorption (17.17), and the critical residue sign
(18.6) are repo-derived relations for the graph class of Definition
1.1. Their prerequisites are the existing actual-graph localization in
Lemmas 13.2--13.3, the core defect identities (14.3)--(14.7), the
algebraic prices of Section 2, the connected contraction and edge
congruence of Section 4, and the legal upper suppliers of Lemma 11.2.
The nonlinear transfer separates the singleton baseline from exceptional
tail incidences; the incidence floor then pays the remaining concentration
error with price slack. Neither step assumes the desired finite envelope.
The rational critical comparison uses the exact branch formulas already
present in (11.10)--(11.11), with its own actual integer residues.

The CDSO normalization and broader fixed-order, fixed-cyclomatic
extremal question are those of Albalahi--Das--Ali--Barman--Hamza,
[*On the hyperbolic Sombor index and its counterpart*](https://arxiv.org/html/2510.24809v1),
§§1,4, DOI [10.47443/dml.2025.176](https://doi.org/10.47443/dml.2025.176),
with the repository's source note
[here](../../../Library/GraphInvariants/albalahidasalibarmanhamza2025hyperbolicsombor.md).
No external extremal theorem is a premise for (17.2) or (18.6), and
no literature-priority claim is attached to them. The full-text technical
overlap with Zhao--Zhao, DOI
[10.21136/CMJ.2026.0075-26](https://doi.org/10.21136/CMJ.2026.0075-26),
remains unassessed and supplies no premise.

Theorem 17.4 strengthens the precision of Theorem 14.2 on its same
full prescribed graph class. Theorem 18.1 decides the eventual actual
core for the particular exact critical sequence (18.1). It does not
determine a general finite critical transition curve. Complete source
support, global optimality of a particular source template, sufficiency
of $a^{5/2}$ for eventual law-winning exact source restriction, moving
$R$, varying the sink budget and the unrestricted connected-graph
extremal problem remain outside these conclusions. A bounded error
in a value and an actual threshold-core conclusion do not supply those
stronger assertions.

## 追加锚（本行以下为增补区）

## 20. Uniform exact support and finite reconstruction at the $a^{5/2}$ scale

The following statements use the actual threshold partition from Definition
13.1. The index $j$ is therefore allowed to be a nonwinning branch. The
finite formulas of Section 6 are extended algebraically to every
$2\le j\le J_R$; no occurrence of $j\in J_*$ is used in this section.

**Lemma 20.1 (The price slack has a uniform nonzero gap unless a core smoothing applies).**
Fix finite $R\ge4$ and $c>0$. After increasing the $R,c$-only lower
threshold for $a$, let $G$ be an exact minimizer at an integer budget
$N\ge ca^{5/2}$, and use the notation of Definitions 13.1 and 17.1. Then

$$
\Pi\le C_{R,c}\frac{a^5}{N}\le \frac{C_{R,c}}c\,a^{5/2}.
\tag{20.1}
$$

If $G$ has a bad tail-touching source, or has more than $n$ contracted
tail connections, or has $D_0>d_{j,N}$ after all tail sources are
singletons or connectors, (20.1) is impossible. If instead
$D_0=d_{j,N}$ and a core-only source has degree $L\notin\{m,m-1\}$,
then $G$ is not a minimizer.

**Proof.** Put $E_{j,N}=S_j+\bar\chi_{j,N}/N$ and write
$\varepsilon=C_{R,c}a^5/N^2$, enlarging the constant so that both
Theorem 17.4 and Lemma 17.3 use $\varepsilon$. Theorem 17.4 gives

$$
W(G)\le L_N+\varepsilon,\qquad E_{j,N}\le L_N+\varepsilon,
$$

whereas Lemma 17.3 gives

$$
W(G)\ge E_{j,N}+\frac{\Pi}{2N}-\varepsilon.
$$

Since $E_{j,N}\ge L_N$, these three inequalities imply (20.1).

The actual index supplied by Lemma 13.2 satisfies
$n^2/(j^2a)>5/2-O_R(a^{-1/2})$. The expansions in (14.12) therefore
give, uniformly for $2\le j\le J_R$,

$$
\eta^2\ge \kappa_Ra^3,\qquad rc_j\ge \kappa_Ra^3
\tag{20.2}
$$

for some $\kappa_R>0$. If a bad source exists, its $D_u$ in (17.4)
is at least $3$, so (17.5) and (17.9) give
$\Pi\ge 3\eta^2/4$. If there is no bad source but
$\tau>n$, (17.10) gives $\Pi\ge\eta^2$. Both bounds contradict
(20.1) and (20.2) for large $a$.

It remains to consider no bad source and $\tau=n$. Then the exact
identity (4.6), with $b=n$, reads

$$
\Pi=(D_0-d_{j,N})c_j+
\sum_{u:B_u=0}
\frac{(m-L_u)(r-L_u)(m+r+L_u)}{\alpha^2}.
\tag{20.3}
$$

The edge congruence (4.7) gives $D_0\equiv d_{j,N}\pmod r$ and
$D_0\ge d_{j,N}$. If $D_0>d_{j,N}$, then
$D_0-d_{j,N}\ge r$, so (20.2)--(20.3) give
$\Pi\ge rc_j$, again contradicting (20.1).

Suppose now $D_0=d_{j,N}$, and let $B\subseteq C$ be the neighborhood
of an intermediate core-only source, with $|B|=L\le m-2$. We first show
that a full-core source exists. Let $g$ be the number of core-only sources.
The tail marginal sum satisfies, by (13.19),

$$
u=\frac jr+O_{R,c}\!\left(\frac{T_N}{a^3}\right)=O_{R,c}(a^{-1}),
$$

because $T_N=a^{7/2}/N\le a/c$. Every source that touches $D$ uses
at least one tail incidence, hence $N-g\le Nu$, and therefore
$g\ge N(1-u)\ge N/2$. If no full-core source existed, every core-only
source would have $L_u\le r$, giving $D_0=\sum_{B_u=0}(m-L_u)\ge g>r$,
which contradicts $D_0=d_{j,N}<r$.

Choose a full-core source $U$. Since $B$ omits at least two core labels,
choose $x\in C\setminus B$, move the edge $Ux$ to the intermediate
source, and leave all other incidences unchanged. The two source degrees
become $m-1$ and $L+1$, while every sink degree and every budget remain
unchanged. Let $D_i$ denote the unchanged core sink degrees and put

$$
\Delta_k(D)=f_{k+1}(D)-f_k(D),\qquad
f_k(D)=\sqrt{1+k^2/D^2}-1.
$$

For fixed $D>0$, $k\mapsto f_k(D)$ is strictly convex because

$$
\frac{\partial^2}{\partial k^2}f_k(D)
=\frac{D^{-2}}{(1+k^2/D^2)^{3/2}}>0.
$$

Thus $\Delta_L(D_i)<\Delta_{m-1}(D_i)$. On every $i\in B$, the change
in the two source contributions is
$-\Delta_{m-1}(D_i)+\Delta_L(D_i)<0$. On every
$i\in C\setminus(B\cup\{x\})$, it is
$-\Delta_{m-1}(D_i)<0$, and at $x$ it is
$f_{L+1}(D_x)-f_m(D_x)<0$. The total $E$, and hence $W=2NE$,
strictly decreases.

The move preserves simplicity because $x\notin B$, and preserves the
source and edge counts. Lemma 13.2 gives core sink degrees at least
$N/2$, while both new core source degrees are at most $m$, so strict
orientation remains valid. The old full source still joins all core sinks
except $x$, and the enlarged intermediate source joins $x$ to a core
sink in $B$; all tails retain their connectors. Thus connectedness is
preserved. This contradicts minimality, so no intermediate source exists.

Consequently every exact minimizer has no bad source, exactly $n$ connectors,
and $D_0=d_{j,N}$ with every core-only source of degree $m$ or $m-1$.
The congruence and edge identity then give exactly $d_{j,N}$ sources of
degree $m-1$, exactly

$$
F_{j,N}=\frac{(a-1)N-n-(r-1)d_{j,N}}r
\tag{20.4}
$$

full-core sources, and all remaining sources are tail singletons. Since
$\tau=n$ and each tail must occur in a connector, there is exactly one
connector for every tail. ∎


**Theorem 20.2 (Uniform exact finite allocation and exhaustive reconstruction).**
For every fixed finite $R\ge4$ and $c>0$, there is a finite positive
$A_{R,c}$ such that, for every integer
$a\ge A_{R,c}$, every integer

$$
\frac72\sqrt a\le h\le R\sqrt a,\qquad N\ge ca^{5/2},
\tag{20.5}
$$

the original graph class is nonempty and, with the notation of
(6.1)--(6.5) extended to every $2\le j\le J_R$,

$$
V_N=\min_{2\le j\le J_R}\ \min_{z\in\mathcal Z_{m_j,n_j,d_{j,N}}}
\mathcal A_{j,N}(z).
\tag{20.6}
$$

Here $m_j=a+j$, $r_j=m_j-1$, $n_j=h+1-j$,
$d_{j,N}=[n_j-(a-1)N]_{r_j}$, and $F,Q,b,t$ and
$\mathcal A_{j,N}$ are the expressions in (6.1)--(6.5) for that branch;
$\mathcal J_N$ is not restricted to $J_*$.

Every exact minimizer, and only an exact minimizer, is obtained as follows.
Choose a minimizing pair $(j,z)$ in (20.6), a labelled partition
$C\dot\cup D=[s]$ of sizes $m_j,n_j$, and nonnegative
$\ell_i$ satisfying (6.9). Put

$$
e_i=z_i^++\ell_i,\qquad o_i=z_i^-+\ell_i.
\tag{20.7}
$$

Assign the $n_j$ labelled tails to connector endpoints with histogram $e$,
assign the $d_{j,N}$ missing-one sources with omission histogram $o$,
take $F_{j,N}$ full-core sources, and give the $Q-n_j$ singleton
sources to the tails so that $n_j-t$ tails have degree $b$ and $t$
tails have degree $b+1$. Finally permute all source labels. All ties,
all residues, all endpoint and omission assignments allowed by (20.7), and
all choices of the $t$ high-degree tail labels are included.

**Proof.** Uniformly for $2\le j\le J_R$,

$$
m_j,r_j=\Theta_R(a),\quad n_j=\Theta_R(\sqrt a),\quad
\alpha_j=\Theta_R(1),\quad \beta_j=\Theta_R(a^{-3/2}).
\tag{20.8}
$$

The residue satisfies $0\le d_{j,N}<r_j$, and (20.4) gives
$F_{j,N}=\alpha_jN-O_R(a)>N/3$ after increasing $A_{R,c}$. Also
$Q=n_j\beta_jN+O_R(a)$, so the balanced quotient obeys
$b=\beta_jN+O_R(\sqrt a)$ and hence $b>2$. These estimates are

uniform in $j,h,N$ and in the residue.

For every $z\in\mathcal Z_{m_j,n_j,d_{j,N}}$, the construction in the
proof of Lemma 6.3 produces (20.7): its sums are
$\sum e_i=n_j$, $\sum o_i=d_{j,N}$, and $L(z)$ units are placed only
at $I_0(z)$. The set $\mathcal Z_{m_j,n_j,d_{j,N}}$ is nonempty: if
$n_j\ge d_{j,N}$, place $n_j-d_{j,N}$ positive units, and if
$d_{j,N}>n_j$, place $d_{j,N}-n_j$ negative units on distinct core
labels. The displayed source counts are nonnegative. They total

$$
F_{j,N}+d_{j,N}+n_j+(Q-n_j)=N,
$$

and their edge count is

$$
m_jF_{j,N}+r_jd_{j,N}+2n_j+(Q-n_j)
=N+r_jF_{j,N}+(r_j-1)d_{j,N}+n_j=aN.
\tag{20.9}
$$

The graph is simple and bipartite by construction. A full-core source joins
all core sinks, and the one connector at each tail joins every tail to the
core, so it is connected. Its core sink degrees are
$F_{j,N}+d_{j,N}+z_i\ge F_{j,N}$, hence exceed every core source degree
$m_j$. Its tail degrees are $b$ or $b+1$, and $b>2$, so the
connector degree two and singleton degree one are strictly smaller.
Thus every reconstruction belongs to the original graph class, proving
nonemptiness and the upper inequality in (20.6).

Now let $G$ be an exact minimizer. Lemma 20.1 gives its exact source
support and an actual index $2\le j\le J_R$. The proof of Lemma 6.2
uses only the exact source types, strict orientation, and tail degrees
larger than $4$. For this actual graph, Lemma 13.2, (13.5), gives
$t_k=\beta_j(1+O_{R,c}(a^{-1/4}))$ for every $k\in D$. Thus (20.8) and
$N\ge ca^{5/2}$ give, for some $\kappa_R>0$ and after increasing $A_{R,c}$,

$$
q_k=d_G(k)=Nt_k\ge\frac12\beta_jN\ge\kappa_R c\,a>4
\qquad(k\in D).
$$

This is a lower bound for the actual tail degrees before balancing.
Consequently every minimizing graph has $n_j-t$ tail degrees
$b$ and $t$ tail degrees $b+1$. For its endpoint and omission
counts put $z=e-o$. The same summation argument as (6.4) gives
$z\in\mathcal Z_{m_j,n_j,d_{j,N}}$. Lemma 6.3 then gives the exact core
minimum $\mathcal C_{j,N}(z)$, with equality precisely when (20.7) holds;
the tail contribution is $\mathcal T_{j,N}$. Hence
$W(G)\ge\mathcal A_{j,N}(z)\ge$ the right side of (20.6), proving the
reverse inequality.

Conversely, for a minimizing pair in (20.6), the construction above has
core value $\mathcal C_{j,N}(z)$ by (6.9) and tail value
$\mathcal T_{j,N}$, so its exact objective is
$\mathcal A_{j,N}(z)=V_N$. The equality conditions in Lemma 6.3 and the
balancing equality in Lemma 6.2 show that no other source, endpoint,
omission, tail-label or tie case is present. This proves the exhaustive
reconstruction, including all labelled preimages and all branch and
allocation ties. ∎

**Corollary 20.3 (Scope and unresolved boundaries).** Theorem 20.2 proves
the complete fixed-$R$, fixed-$c$ source-support and finite-allocation
package at every integer $N\ge ca^{5/2}$, including nonwinning bounded
branches and every residue. It does not assert a law-winning branch, a
unique optimizer, a least threshold or period, a moving-$R$ statement, or
any conclusion outside Definition 1.1. The argument is a prose theorem;
it is not a Lean or kernel verification.

The proof reuses the actual-graph localization and nonlinear transfer in
Lemmas 13.2--13.3, the algebraic price identities and connected contraction
of Sections 2 and 4, the uniform slack estimate of Lemma 17.2, and the
exact allocation identities of Section 6. The scalar strict convexity used
in Lemma 20.1 is the one-variable criterion described in Boyd--Vandenberghe,
*Convex Optimization*, §3.1.4, [author text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
The graph normalization and source problem remain the CDSO definition of
Albalahi--Das--Ali--Barman--Hamza, *On the hyperbolic Sombor index and its
counterpart*, [arXiv:2510.24809v1](https://arxiv.org/html/2510.24809v1),
§1; no external extremal theorem is used as a premise.

## 追加锚（本行以下为增补区）
