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

in this neighborhood. No global convexity of $H$ is asserted.

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
The scalar supporting-tangent and strong-convexity steps in
(3.7) have the usual meaning of Boyd--Vandenberghe, *Convex
Optimization*, §§3.1.3 and 3.1.8,
[author text](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf);
their hypotheses were checked here for the scalar reciprocals,
rather than assumed for $H$. ∎

**Lemma 3.2 (Compact localization for actual graphs).** Fix $a,h$.
For any finite $L_0$, graphs in Definition 1.1 satisfying
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
