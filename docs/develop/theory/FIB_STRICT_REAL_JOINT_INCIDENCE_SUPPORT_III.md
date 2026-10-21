# FIB strict-real joint incidence: a global terminal-J tail

## 1. Original worlds, the full parent and the same-child quantifiers

**Definition 1.1 (Literal complete worlds).** Write
[O](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md) for the common-parent
volume, [F](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md) for the all-response
finite-fibre volume, [S](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md) for the
first strict-real support volume, and
[SII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md) for its continuation.
The complete worlds are exactly those of O, Definitions 1.1–1.3:

$$
W=(P,g,d),\qquad
P=\begin{pmatrix}r&b\\c&1-r\end{pmatrix},\qquad
0<r<1,\quad b,c>0,\quad bc=r(1-r),\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
\tag{1.1}
$$

The gain is one entire polynomial and the drift is one fixed number.
The actions, products and readings are

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP).
\tag{1.2}
$$

The acquired word is $J,M,J,M,M,M$, with the literal readings

$$
(y_0,y_1,y_2,y_3,y_4,y_5,y_6)
=(0,24,147/5,24,18,p,v).
\tag{1.3}
$$

Let $\mathcal H=\mathcal F(H_4)$, where
$H_4=(0,J,24,M,147/5,J,24,M,18)$. For real $p\ne24,v$ let
$C(p,v)=\mathcal F(H_4,M,p,M,v)$ be the entire actual child.
At the original clock seven put

$$
a(W)=d+g(7)\operatorname{tr}(JQ_6P),\qquad
m(W)=d+g(7)\operatorname{tr}(MQ_6P).
\tag{1.4}
$$

These are counterfactual alternatives on the same world. There is no
reset, copy, skipped reading, shifted clock, rebase or additional port.
All lower gain degrees, sampled or repeated gain roots, zero drift,
singular sources and worlds unused by a selected pair remain in the
domain. Cardinality and distinctness refer to complete triples.

Define the actual pair images, as in S, Definition 1.2, by

$$
\begin{aligned}
D_J&=\{(p,v):p\ne24,\ \exists W\ne W'\in C(p,v),\ a(W)=a(W')\},\\
D_M&=\{(p,v):p\ne24,\ \exists W\ne W'\in C(p,v),\ m(W)=m(W')\}.
\end{aligned}
\tag{1.5}
$$

The original joint relation is $D_J\cap D_M$. Its selected labels obey

$$
\begin{gathered}
W_i\in C(p,v)\ (0\le i\le3),\qquad
W_0\ne W_1,\quad a(W_0)=a(W_1),\\
W_2\ne W_3,\quad m(W_2)=m(W_3).
\end{gathered}
\tag{1.6}
$$

The pairs may overlap or be disjoint; their two common terminal values
may differ. Both pairs use the same acquired $p,v$ and the same entire
child. A boundary label or an equal-world limit is not an actual pair.

**Definition 1.2 (Zero-safe parent interface).** Put

$$
\begin{gathered}
j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\quad e=d-24,\\
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad
\kappa=\frac6T-\frac2U=\frac{2(2+5b)}{TU},\\
\eta=-\frac{24}{5}(b-1/8)\kappa.
\end{gathered}
\tag{1.7}
$$

O, Theorem 2.1, identifies the full parent with precisely the strict
source/drift triples satisfying

$$
e\Lambda=\eta.
\tag{1.8}
$$

The same entire gain is the unique degree-at-most-three interpolant
with samples at $0,1,2,3$

$$
\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right).
\tag{1.9}
$$

This is the public full-parent converse, including its singular branch;
it is used without division by $e$, $\Lambda$, $b-1/8$, a gain sample,
a leading gain coefficient or a root difference. In particular at
$b=1/8,\Lambda=0$ the drift remains arbitrary before the later readings
are imposed. The original traces at clocks $0,\ldots,6$ and the two
terminal traces are, respectively,

$$
(1,j,T,n,U,U+n,2U+n),\qquad T+2j+4r,\quad 3U+2n.
\tag{1.10}
$$

Thus $p=d+(U+n)g(5)$, $v=d+(2U+n)g(6)$,
$a=d+(T+2j+4r)g(7)$ and $m=d+(3U+2n)g(7)$.
Fixed-node interpolation is used at distinct nodes, regardless of sampled
zeros; its classical formula is Berrut–Trefethen, §2,
[Barycentric Lagrange Interpolation](https://doi.org/10.1137/S0036144502417715).

**Assumption 1.3 (Public supplier interfaces).** The following existing
ordinary mathematical results are used at exactly their owning scopes.

| Owner | Interface used |
| --- | --- |
| O, Definitions 1.1–1.3 and Theorem 2.1 | Equations (1.1)–(1.10), with one whole gain and the full zero-safe converse. Its $\epsilon$ is $e$ here; its sixth-$M$ response is $v$ here. |
| S, Corollary 11.4, using its Theorems 7.4, 11.2 and 11.3 | There are finite $B,C>0$ such that $(p,v)\in D_J\cup D_M$ implies $b(W)\le B,c(W)\le C$ for every $W\in C(p,v)$, including unused companions. No bound on $p$ is assumed. |
| S, Theorem 12.1 | For every $L,P_*>0$, a full parent world with $b\le L,|p|\le P_*$ has bounded $c,d$, all four padded coefficients of the whole gain, and $v,a,m$, with a bound depending only on $L,P_*$. This includes singular sources, degree drops and $p=24$. |
| SII, Theorem 14.3 | For every $P_*>0$, one $\varepsilon(P_*)>0$ gives $\max\{\delta(W),\delta(W')\}\ge\varepsilon(P_*)$ for every selected actual $J$ or $M$ pair with $|p|\le P_*$, where $\delta(W)=\min\{r,1-r,b,c\}$. |
| SII, Theorem 15.1 | For bounded $p$, one endpoint of each selected joint pair can be put in one compact strict-parent set; above a compact off-$24$ base set this can be taken inside the off-$24$ parent. The two anchors may coincide. |
| SII, Theorem 29.1 and Corollary 29.2 | There is $\epsilon>0$, uniform in all real $v$, for which $0<|p-24|<\epsilon$ excludes every distinct actual $M$ pair, and hence every original joint configuration. |

Only the all-companion source cap in the second row is used before the
new fifth-response bound below. Bounded-$p$ coercivity is used afterwards.
The new model-specific statements and certificates below are
repository-derived; the interpolation, Descartes sign rule, Bernstein
convex-hull bound and implicit/inverse function theorems are classical
tools, not source-specific collision conclusions.

## 2. The normalized infinite-drift source equations

**Definition 2.1 (Finite normalized boundary).** Let

$$
\mathcal Z=\{(r,b,c):0\le r\le1,\ b,c\ge0,\ bc=r(1-r),\
j=b+c>0,\ n=j+r>0,\ \Lambda=0\}.
\tag{2.1}
$$

Here $T,U,j,n,\Lambda$ retain (1.7), so they are defined at every
label of $\mathcal Z$. These labels are auxiliary source limits;
nonstrict labels are not worlds. At such a label $s$ let $q_s$ be the
unique polynomial of degree at most three with values

$$
\left(-1,-\frac1j,-\frac1T,-\frac1n\right)
\quad\text{at }0,1,2,3.
\tag{2.2}
$$

Define

$$
\begin{aligned}
A_5&=1+(U+n)q_s(5),\\
A_6&=1+(2U+n)q_s(6),\\
A_J&=1+(T+2j+4r)q_s(7).
\end{aligned}
\tag{2.3}
$$

Whenever $A_5\ne0$, put

$$
R_J(s)=\left(\frac{A_6}{A_5},\frac{A_J}{A_5}\right),\qquad
\theta(s)=\frac{A_J-3A_6}{A_5}.
\tag{2.4}
$$

These are mathematical functions of complete-world limits. They add no
observation. Section 5 proves that $A_5\ne0$ everywhere on $\mathcal Z$.

**Definition 2.2 (Exact source polynomials).** Use $\mathscr P$ for a
polynomial, distinct from the source matrix $P$ in (1.1). Define
$\mathscr P,D,N\in\mathbb Z[r,b]$ by the following coefficient table.
The last column gives $[b^k](N/2)$, so the factor two in $N$ is part of
the definition.

| $k$ | $[b^k]\mathscr P$ | $[b^k]D$ | $[b^k](N/2)$ |
| --- | --- | --- | --- |
| $6$ | $1$ | $3$ | $-15$ |
| $5$ | $r$ | $4r+17$ | $-r-77$ |
| $4$ | $-2r^2+6r-8$ | $-3r^2-35r+64$ | $25r^2+230r-294$ |
| $3$ | $-r^3-7r^2+6r-4$ | $-2r^3+25r^2-67r+50$ | $-18r^3-323r^2+621r-254$ |
| $2$ | $r^4-10r^3+13r^2-6r$ | $r^4+30r^3-15r^2-28r+10$ | $4r^4+160r^3-535r^2+434r-61$ |
| $1$ | $4r(1-r)^2(2r-1)$ | $-16r^4+56r^3-40r^2$ | $-32r^4+178r^3-232r^2+86r$ |
| $0$ | $4r^2(1-r)^2$ | $-12r^2(1-r)^2$ | $-21r^2(1-r)^2$ |

For arbitrary strict sources set

$$
\begin{aligned}
L_5&=\frac14-\frac5{2T}-\frac{15}{4U}+\frac5n,\\
L_6&=1-\frac9T-\frac9U+\frac{16}n,\\
L_7&=\frac52-\frac{21}T-\frac{35}{2U}+\frac{35}n,\\
\widetilde A_5&=1+(U+n)L_5,\quad
\widetilde A_6=1+(2U+n)L_6,\quad
\widetilde A_J=1+(T+2j+4r)L_7.
\end{aligned}
\tag{2.5}
$$

Put $q=r(1-r)$ and $t=1+rz$. The following are exact polynomial
quotients, interpreted by polynomial continuation at $r=0,1$:

$$
H(r,z)=\frac{\mathscr P(r,qt)}{rq^2},\qquad
N_L(r,z)=\frac{N(r,qt)}{q^2},\qquad
D_L(r,z)=\frac{D(r,qt)}{q^2}.
\tag{2.6}
$$

They are definitions in $\mathbb Q[r,z]$, not pointwise divisions by
zero. Define also the polynomial derivative circuits

$$
\begin{aligned}
J_U={}&(N_rD-ND_r)\mathscr P_b-(N_bD-ND_b)\mathscr P_r,\\
\mathcal B={}&((N_L)_rD_L-N_L(D_L)_r)H_z\\
&-((N_L)_zD_L-N_L(D_L)_z)H_r,\\
J_L={}&\frac{\mathcal B+16H}{r}\quad\text{in }\mathbb Q[r,z].
\end{aligned}
\tag{2.7}
$$

Every polynomial needed for the certificates is determined by this
coefficient table, substitution, differentiation and exact division.

**Lemma 2.3 (Polynomial identities and endpoint continuation).** On
strict sources,

$$
\begin{gathered}
\Lambda=\frac{2\mathscr P}{b^2TUjn},\\
q_s(5)-L_5=\frac{15}{4}\Lambda,\qquad
q_s(6)-L_6=9\Lambda,\qquad
q_s(7)-L_7=\frac{35}{2}\Lambda,\\
\widetilde A_5=\frac{D}{2b^2TUn},\qquad
\widetilde A_J-3\widetilde A_6=\frac{N}{2b^2TUn}.
\end{gathered}
\tag{2.8}
$$

In the middle line $q_s$ denotes the interpolant (2.2) at the source
in question, whether or not $\Lambda=0$. The divisions in (2.6) and
(2.7) have zero remainders. Their coordinate degrees are

$$
\begin{array}{c|cccccccc}
\text{polynomial}&\mathscr P&D&N&H&N_L&D_L&J_U&J_L\\ \hline
\text{degrees}&(4,6)&(4,6)&(4,6)&(13,6)&(14,6)&(14,6)&(11,16)&(37,16).
\end{array}
\tag{2.9}
$$

Moreover,

$$
\begin{gathered}
H(0,z)=2-4z,\qquad H(1,z)=4-2(1+z)^2,\\
\mathcal B+16H=rJ_L,\qquad
\mathcal B(0,z)=32(2z-1)=-16H(0,z).
\end{gathered}
\tag{2.10}
$$

Proof. Interpolation at the four nodes gives

$$
\begin{aligned}
q_s(5)&=4-15/j+20/T-10/n,\\
q_s(6)&=10-36/j+45/T-20/n,\\
q_s(7)&=20-70/j+84/T-35/n.
\end{aligned}
\tag{2.11}
$$

Subtracting (2.5) gives the middle line of (2.8). Substitute
$c=r(1-r)/b$ in the other expressions and collect powers of $b$;
their numerators are exactly the coefficient table in Definition 2.2.
Substitution $b=r(1-r)(1+rz)$ in that table cancels $rq^2$ or $q^2$
as specified in (2.6). The resulting endpoint substitutions give the
first line of (2.10); substituting those polynomial quotients into
$\mathcal B$ gives its last identity. Hence $\mathcal B+16H$ is
divisible by $r$. These operations give (2.9) and all the asserted
polynomial identities. They involve only finite rational polynomial
arithmetic. In particular they do not cancel an actual singular world. ∎

## 3. Exact rational sign certificates on closed rectangles

**Definition 3.1 (Coefficient certificate convention).** For a polynomial
$F(x,y)$ of coordinate degrees $(n,m)$ on
$[l_x,u_x]\times[l_y,u_y]$, first expand

$$
F(l_x+(u_x-l_x)X,l_y+(u_y-l_y)Y)
=\sum_{i=0}^n\sum_{j=0}^m c_{ij}X^iY^j.
\tag{3.1}
$$

Its tensor Bernstein coefficients in that degree are exactly

$$
\beta_{k\ell}=
\sum_{i\le k,\,j\le\ell}c_{ij}
\frac{\binom{k}{i}}{\binom{n}{i}}
\frac{\binom{\ell}{j}}{\binom{m}{j}},\qquad
0\le k\le n,\quad0\le\ell\le m.
\tag{3.2}
$$

Use the analogous one-variable formula for univariate rows. All tables
below specify the degree used; no degree elevation is implicit.
The scalar identity

$$
X^i=\sum_{k=i}^n\frac{\binom{k}{i}}{\binom{n}{i}}
\binom nkX^k(1-X)^{n-k}
\tag{3.3}
$$

proves (3.2). The Bernstein basis is nonnegative and sums to one on
the closed interval, so
$\min\beta_{k\ell}\le F\le\max\beta_{k\ell}$ on the closed
rectangle. This is the classical convex-hull property; see Patrikalakis,
Maekawa and Cho, *Shape Interrogation*,
[§1.3.4](https://web.mit.edu/hyperbook/Patrikalakis-Maekawa-Cho/node12.html).
Thus the displayed coefficients define finite exact rational sign
certificates, including every rectangle edge.

**Lemma 3.2 (Global box certificates).** Formula (3.2), applied to the
polynomials of Definition 2.2, gives the following minimum and maximum
Bernstein coefficients. In a row with domain $[0,1]$, the variable is $r$.
The polynomial quotient in the third row is defined before $r=0$ is
substituted.

| Polynomial | Closed domain | Degree | Minimum | Maximum |
| --- | --- | --- | --- | --- |
| $[b^4]\mathscr P$ | $[0,1]$ | $2$ | $-8$ | $-4$ |
| $[b^3]\mathscr P$ | $[0,1]$ | $3$ | $-6$ | $-2$ |
| $([b^2]\mathscr P)/r$ | $[0,1]$ | $3$ | $-6$ | $-2/3$ |
| $\mathscr P(r,2)$ | $[0,1]$ | $4$ | $-96$ | $-12$ |
| $\mathscr P(r,31/10)$ | $[0,1]$ | $4$ | $29522881/1000000$ | $606420791/1000000$ |
| $H(r,2/5)$ | $[0,1]$ | $13$ | $2/25$ | $67283/41250$ |
| $H(r,3/5)$ | $[0,1]$ | $13$ | $-1832/1625$ | $-13157/178750$ |
| $H_z$ | $[0,1]\times[2/5,3/5]$ in $(r,z)$ | $(13,5)$ | $-21030617/2234375$ | $-4$ |
| $D_L$ | $[0,1]\times[2/5,3/5]$ in $(r,z)$ | $(14,6)$ | $-50864/875$ | $-2$ |
| $N_L+5D_L$ | $[0,1]\times[2/5,3/5]$ in $(r,z)$ | $(14,6)$ | $-9974/25$ | $-2$ |
| $D$ | $[0,1]\times[2,31/10]$ in $(r,b)$ | $(4,6)$ | $1320$ | $15025651113/1000000$ |
| $N+5D$ | $[0,1]\times[2,31/10]$ in $(r,b)$ | $(4,6)$ | $-13239006041/200000$ | $-1128$ |

Proof. Substitute the rational endpoints into (3.1) and use (3.2).
For example $[b^4]\mathscr P=-8+6r-2r^2$ has degree-two coefficients
$(-8,-5,-4)$, and $([b^2]\mathscr P)/r=r^3-10r^2+13r-6$ has
degree-three coefficients $(-6,-5/3,-2/3,-2)$. The same finite sums,
with the displayed polynomial circuits and degrees, give the remaining
rows. Their extrema are the rational numbers in the table. No numerical
root approximation is part of these certificates. ∎

**Lemma 3.3 (Six lower rectangles).** The following closed rectangles
cover $[0,1]\times[2/5,3/5]$ in $(r,z)$. Every Bernstein coefficient
of the indicated polynomial is at most the last entry.

| $r$ interval | $z$ interval | Polynomial | Degree | Upper bound on every coefficient |
| --- | --- | --- | --- | --- |
| $[0,1/2]$ | $[2/5,1/2]$ | $J_L$ | $(37,16)$ | $-40$ |
| $[0,1/4]$ | $[1/2,11/20]$ | $J_L$ | $(37,16)$ | $-9$ |
| $[0,1/8]$ | $[11/20,3/5]$ | $H$ | $(13,6)$ | $-1/10$ |
| $[1/8,1/4]$ | $[11/20,3/5]$ | $J_L$ | $(37,16)$ | $-138$ |
| $[1/4,1/2]$ | $[1/2,3/5]$ | $J_L$ | $(37,16)$ | $-1207$ |
| $[1/2,1]$ | $[2/5,3/5]$ | $J_L$ | $(37,16)$ | $-25879$ |

Consequently $J_L<0$ at every zero of $H$ in the whole closed box.

Proof. Each coefficient inequality is the rational sum (3.2) with the
listed endpoints and degrees. The covering is seen by splitting first
at $r=1/2$, then at $r=1/4$ and $r=1/8$ where necessary, and splitting
the indicated $z$ intervals at $1/2,11/20$. The third rectangle has
$H<0$ and hence contains no zero of $H$. Every zero lies in one of the
other five closed rectangles, where $J_L<0$. Shared edges are included
in these statements. ∎

**Lemma 3.4 (Five upper rectangles).** The following closed rectangles
cover $[0,1]\times[2,31/10]$ in $(r,b)$. The coefficient inequalities
use (3.2) in the listed degrees.

| $r$ interval | $b$ interval | Polynomial | Degree | Bound on every coefficient |
| --- | --- | --- | --- | --- |
| $[0,1/4]$ | $[2,51/20]$ | $\mathscr P$ | $(4,6)$ | $\le-33$ |
| $[1/4,1/2]$ | $[2,91/40]$ | $\mathscr P$ | $(4,6)$ | $\le-16$ |
| $[1/4,1/2]$ | $[91/40,51/20]$ | $J_U$ | $(11,16)$ | $\ge2452054904$ |
| $[0,1/2]$ | $[51/20,31/10]$ | $J_U$ | $(11,16)$ | $\ge5037074268$ |
| $[1/2,1]$ | $[2,31/10]$ | $J_U$ | $(11,16)$ | $\ge198340608$ |

Consequently $J_U>0$ at every zero of $\mathscr P$ in the whole
closed box.

Proof. Formula (3.2) gives exactly the asserted rational inequalities.
The five rectangles cover the box, including its edges. The first two
have $\mathscr P<0$ and contain no zero. Every zero is therefore in a
positive-$J_U$ rectangle. ∎

## 4. Exhaustion by two closed analytic arcs

**Theorem 4.1 (The entire finite normalized source boundary).** The set
$\mathcal Z$ is the disjoint union of these two closed analytic arcs:

$$
\begin{aligned}
\mathcal Z_-&=\{(r,q(1+rz(r)),(1+rz(r))^{-1}):0\le r\le1\},\\
&\hspace{12mm}H(r,z(r))=0,\qquad 2/5<z(r)<3/5,\\
\mathcal Z_+&=\{(r,b_+(r),q/b_+(r)):0\le r\le1\},\\
&\hspace{12mm}\mathscr P(r,b_+(r))=0,\qquad 2<b_+(r)<31/10.
\end{aligned}
\tag{4.1}
$$

Each graph function is uniquely specified by its equation and interval.
Analyticity at an endpoint means analytic continuation to a neighbourhood
of that endpoint. The four endpoints are

$$
\begin{gathered}
\mathcal Z_-:\quad (0,0,1),\quad(1,0,1/\sqrt2),\\
\mathcal Z_+:\quad (0,\rho_0,0),\quad(1,\rho_1,0),\\
\rho_0^3-8\rho_0-4=0,\qquad
\rho_1^3-4\rho_1-2=0,\qquad 2<\rho_i<31/10.
\end{gathered}
\tag{4.2}
$$

There are no other finite nonnegative $\Lambda=0$ labels with $j,n>0$.

Proof. For $0<r<1$, the descending $b$-coefficient signs of
$\mathscr P$ are

$$
+,+,-,-,-,\text{arbitrary},+.
\tag{4.3}
$$

The three strict negative signs follow from the first three rows of
Lemma 3.2, including the polynomial quotient in the $b^2$ row. Removing
any zero penultimate coefficient, there are exactly two sign changes,
regardless of that coefficient's sign. Descartes' rule therefore gives
at most two positive roots counted with multiplicity. This is the
classical real-polynomial sign rule, applied only to the displayed
one-variable polynomial for a fixed $r$.

The signs $H(r,2/5)>0>H(r,3/5)$ and $H_z<0$ in Lemma 3.2 give exactly
one $z(r)$ in the stated interval for every $0\le r\le1$. The implicit
function theorem gives its analytic dependence, including across the
endpoints. For $0<r<1$ it supplies a positive root
$b=q(1+rz(r))<2/5$. The signs
$\mathscr P(r,2)<0<\mathscr P(r,31/10)$ give another positive root
in the upper interval. These disjoint roots exhaust Descartes' bound,
so each is simple. At the lower root, differentiation of (2.6) gives

$$
\mathscr P_b=qH_z<0;
\tag{4.4}
$$

at the upper root $\mathscr P_b>0$, since the polynomial changes from
negative to positive there. The upper graph is consequently analytic
for strict $r$.

At $r=0,1$ the exact factorizations are

$$
\mathscr P(0,b)=b^3(b^3-8b-4),\qquad
\mathscr P(1,b)=b^2(b+1)(b^3-4b-2).
\tag{4.5}
$$

Each cubic has one positive root: its coefficient sequence has one
sign variation, and the endpoint signs in Lemma 3.2 put that root in
$(2,31/10)$. It is simple; the derivatives $3b^2-8$ and $3b^2-4$ are
positive for $b>2$. Thus the upper graph extends analytically to both
endpoints and still has $\mathscr P_b>0$ there.

For completeness, one must evaluate the original $\Lambda$ on a
$b=0$ face rather than divide (2.8) by $b$. At $c>0$ its values are

$$
\Lambda(0,0,c)=\frac{8(c-1)}c,\qquad
\Lambda(1,0,c)=\frac{4(2c^2-1)}{c(c+1)}.
\tag{4.6}
$$

Their positive zeros are exactly $c=1,1/\sqrt2$. Equation (2.10)
gives $z(0)=1/2,z(1)=\sqrt2-1$, so these are exactly the lower
endpoints in (4.2). If $0<r<1$, rank one forces $b,c>0$. If $r=0$
or $1$, rank one forces $bc=0$; with $j>0$ precisely one of $b,c$
is positive. These cases exhaust all finite nonnegative sources in
(2.1). The two $j=0$ corners are outside (2.1); their relevance to
actual escaping sequences is treated in Theorem 7.1, not assumed away. ∎

## 5. Separation, strict order and the exceptional endpoint tangent

**Theorem 5.1 (Injectivity and immersion of the full boundary map).**
$A_5$ is nonzero throughout $\mathcal Z$, and $R_J$ is injective and
has nonzero tangent at every point of both closed arcs, including all
four face endpoints. On the upper arc $A_5>0,\theta<-5$; on the
lower arc $A_5<0,\theta>-5$. The function $\theta$ is strictly
increasing in $r$ on each closed arc.

Proof. On $\Lambda=0$, (2.8) identifies $A_i$ with their tilded
expressions. On the upper arc $D\ge1320>0$, so

$$
A_5=\frac{D}{2b^2TUn}>0,\qquad
\theta=\frac ND<-5,
\tag{5.1}
$$

where the last inequality follows from $N+5D\le-1128$.
On the lower arc substitute $b=qt$ before continuing to the endpoints:

$$
A_5=\frac{D_L}{2t^2TUn}<0,\qquad
\theta=\frac{N_L}{D_L}>-5.
\tag{5.2}
$$

All denominators here are positive on the entire lower closed arc:
$t>0,T,U>0,n>0$. The inequalities follow from
$D_L\le-2$ and $N_L+5D_L\le-2$, with the reversal caused by
$D_L<0$. Continuity proves the formula also at $r=0,1$.
Thus the two arc images under $R_J$ are disjoint.

Along the upper graph, implicit differentiation gives

$$
\frac{d\theta}{dr}=\frac{J_U}{D^2\mathscr P_b}>0.
\tag{5.3}
$$

The denominator is positive by Theorem 4.1, and Lemma 3.4 supplies the
strict numerator sign at every root, endpoints included. Along the
lower graph, $z'=-H_r/H_z$, whence

$$
\frac{d\theta}{dr}
=\frac{\mathcal B}{D_L^2H_z}
=\frac{rJ_L}{D_L^2H_z}.
\tag{5.4}
$$

It is positive for $r>0$ by Lemmas 3.2–3.3 and zero at $r=0$.
For any $0\le r_0<r_1\le1$, the derivative is positive on the
nonempty interval $(r_0,r_1)$, so the lower function is strictly
increasing on the full closed interval as well. Equality of $R_J$
first fixes the arc by (5.1)–(5.2), then fixes $r$ by strict order,
then fixes the source by Theorem 4.1. This proves global injectivity.

The nonzero $\theta$ derivatives already prove immersion except at
the lower endpoint $s_0=(0,0,1)$. There use source coordinates $(r,c)$
with $b=r(1-r)/c$. Direct differentiation of the original rational
functions gives the following exact endpoint data along $\Lambda=0$:

$$
\begin{gathered}
\Lambda_c(s_0)=8,\quad \Lambda_r(s_0)=4,\quad c'(0)=-1/2,\\
(A_5,A_6,A_J)(s_0)=(-1,-2,-2),\\
(A_5',A_6',A_J')(s_0)=(3/2,7/2,9/2),\\
\left(\frac{A_6}{A_5}\right)(s_0)=2,\qquad
\left(\frac{A_6}{A_5}\right)'(s_0)=-1/2,\qquad
\theta(s_0)=-4,\quad\theta'(s_0)=0.
\end{gathered}
\tag{5.5}
$$

To obtain these numbers directly, $b'=1,c'=-1/2$ gives
$j'=1/2,n'=3/2,T'=1,U'=2$ at $s_0$; substitution in (2.5) and
(2.3) gives the three displayed $A_i'$ values. The quotient rule then
gives $-1/2$. Thus the first coordinate of $R_J$ has nonzero tangent
there. At the other lower endpoint the useful exact values are

$$
\Lambda_c(1,0,1/\sqrt2)=16(2-\sqrt2)>0,\qquad
\theta(1)=\frac{67}{28}-\frac{5\sqrt2}{56}.
\tag{5.6}
$$

All four endpoint labels are retained. ∎

## 6. Local uniqueness on the full compactified parent

**Theorem 6.1 (Local injectivity at every infinite-drift label).** Near
each label of $\mathcal Z$, the full parent has an ambient analytic
chart in which

$$
\left(\frac1p,\frac vp,\frac ap\right)
\tag{6.1}
$$

extends analytically across infinite drift and is locally injective.
This local uniqueness applies to all nearby actual parent worlds with
large drift of either sign, including the singular parent sources.

Proof. Write $\sigma=1/e$ and retain the undivided equation

$$
\Lambda=\sigma\eta.
\tag{6.2}
$$

At an upper label use $(r,b)$ as source coordinates. Equation (2.8)
and $\mathscr P_b>0$ give $\Lambda_b\ne0$ at $\sigma=0$.
At a strict lower label the same conclusion follows from
$\mathscr P_b=qH_z\ne0$. At either lower endpoint use $(r,c)$
instead, with $b=r(1-r)/c$; the two nonzero $\Lambda_c$ values
are (5.5)–(5.6). All rational denominators in the chosen chart are
nonzero at its central label. The analytic implicit function theorem
therefore solves (6.2) for $b$ or $c$ as an analytic function of
$(r,\sigma)$ on an open ambient neighbourhood.

In this chart interpolate the single polynomial $Q_\sigma$ at the
original nodes $0,1,2,3$ with samples

$$
\left(-1-24\sigma,-\frac1j,
\frac{-1+(27/5)\sigma}{T},-\frac1n\right).
\tag{6.3}
$$

Its coefficients depend analytically on the chart. For $\sigma\ne0$
and an actual world, (1.9) gives exactly $Q_\sigma=\sigma g$.
Define in the same chart

$$
\begin{aligned}
F_5&=1+24\sigma+(U+n)Q_\sigma(5),\\
F_6&=1+24\sigma+(2U+n)Q_\sigma(6),\\
F_J&=1+24\sigma+(T+2j+4r)Q_\sigma(7).
\end{aligned}
\tag{6.4}
$$

For $\sigma\ne0$ these are exactly $(\sigma p,\sigma v,\sigma a)$.
At $\sigma=0$ they are $(A_5,A_6,A_J)$. By Theorem 5.1,
$F_5$ stays nonzero on a neighbourhood of the central label. Consequently

$$
w=\frac{\sigma}{F_5},\qquad
\frac vp=\frac{F_6}{F_5},\qquad
\frac ap=\frac{F_J}{F_5}
\tag{6.5}
$$

are analytic there, and $w_\sigma=1/A_5\ne0$ at $\sigma=0$.
Use $(w,r)$ as coordinates, with $w=0$ exactly when $\sigma=0$.
On this boundary the derivative in $r$ of

$$
\frac{a-3v}{p}=\frac{F_J-3F_6}{F_5}
\tag{6.6}
$$

is the strictly positive $\theta'$ of (5.3) or (5.4), except at
$s_0$. Hence $(w,(a-3v)/p)$ has nonzero Jacobian there. At $s_0$
use $(w,v/p)$ instead; (5.5) gives its nonzero derivative of the second coordinate
$-1/2$ in the $r$ direction. The inverse function theorem makes
these two-coordinate submaps locally injective, proving (6.1).
The classical implicit and inverse function theorems are used on open
Euclidean chart domains with the nonzero derivatives just displayed;
see Lebl, *Basic Analysis II*,
[§8.5](https://www.jirka.org/ra/realanal2.pdf).

Ambient continuation gives uniqueness only. The $r=0,1$ and
$\sigma=0$ labels are not admitted as strict worlds. Restriction to
actual worlds preserves every guard of Definition 1.1. Both signs of
$\sigma$ occur in the same neighbourhood. At a strict singular source
$b=1/8,\Lambda=0$, also $\eta=0$, and (6.2) still describes the
full parent without division by either side. The argument therefore
includes its arbitrary-drift branch, as well as lower gain degrees and
sampled or repeated gain roots. No gain factor has been removed.
Finally the chart parameters determine the source, $e=1/\sigma$ and,
by (1.9), the entire polynomial of every actual world with
$\sigma\ne0$. Local uniqueness of chart parameters is thus uniqueness
of complete worlds. ∎

## 7. The global terminal-J tail theorem

**Theorem 7.1 (Uniform qualitative terminal-J tail).** There exists a
finite $P_J>0$ such that, for every real $p\ne24$ and every real $v$,

$$
W\ne W'\in C(p,v),\quad a(W)=a(W')
\quad\Longrightarrow\quad |p|\le P_J.
\tag{7.1}
$$

Equivalently, terminal $J$ is injective on the entire actual $C(p,v)$
whenever $|p|>P_J$, uniformly over all real $v$. The bound is
qualitative; no numerical value is asserted.

Proof. Suppose the $p$-projection of $D_J$ is unbounded. Choose actual
distinct pairs $W_i,W_i'\in C(p_i,v_i)$ with equal terminal $a_i$,
$p_i\ne24$ and $|p_i|\to\infty$. S, Corollary 11.4, supplies
fixed finite $B,C$ bounding both offdiagonals at every endpoint and
indeed every companion of every such child. After simultaneous
subsequences the two source sequences converge in

$$
\{(r,b,c):0\le r\le1,\ 0\le b\le B,\ 0\le c\le C,
\ bc=r(1-r)\}.
\tag{7.2}
$$

No bounded-$p$ coercivity or advance bound on $v$ has been used.

First neither source limit has $j=0$. Indeed, $T,U\ge1$ and
$|\kappa|\le6$ give the uniform bound

$$
|\eta|\le K,\qquad K=\frac{144}{5}(B+1/8).
\tag{7.3}
$$

For $j\le1/4$, since $n\ge j>0$,

$$
j\Lambda=j(1+6/T+1/U)-4-4j/n\le8j-4\le-2.
\tag{7.4}
$$

The parent equation yields

$$
|e|\le Kj/2,\qquad |e/j|\le K/2,\qquad |e/n|\le K/2.
\tag{7.5}
$$

All four samples (1.9) are bounded there, so all coefficients of the
same whole gain are bounded. The source cap also bounds $U+n$.
Thus $p=d+(U+n)g(5)$ is bounded, contradicting $|p_i|\to\infty$
if either endpoint sequence tends to $j=0$. This explicitly disposes
of both rank-one corners, for every approach direction.

At either remaining source limit, $j,n$ are positive. On its
neighbourhood the four samples give
$|p|\le K_1(1+|e|)$ for some finite $K_1$. Therefore both
$|e_i|$ and $|e_i'|$ tend to infinity. Equation (1.8), with bounded
$\eta$, forces $\Lambda\to0$ at both limits. Theorem 4.1 places
them in the entire two-arc set $\mathcal Z$, including all four
possible face poles and every strict singular source.

For either endpoint sequence the interpolant $g_i/e_i$ converges
coefficientwise to (2.2). Thus, at its limiting label $s$,

$$
\frac{p_i}{e_i}\longrightarrow A_5(s)\ne0,\qquad
\left(\frac{v_i}{p_i},\frac{a_i}{p_i}\right)
\longrightarrow R_J(s).
\tag{7.6}
$$

The two endpoints have identical $p_i,v_i,a_i$, so their normalized
limits have equal $R_J$. Theorem 5.1 makes their source labels equal.
Both endpoint sequences consequently tend to the same point
$(s,\sigma=0)$ of a full-parent chart of Theorem 6.1. Eventually
both are in one neighbourhood on which (6.1) is injective, and have
identical $(1/p_i,v_i/p_i,a_i/p_i)$. Theorem 6.1 makes their chart
parameters, source, drift and whole gain identical. This contradicts
$W_i\ne W_i'$.

The $p$-projection of $D_J$ is therefore bounded. Enlarge a finite
bound to a positive $P_J$; if $D_J$ is empty, any positive choice
suffices. All original actual worlds were retained, and neither sign
of diverging drift was restricted. This proves (7.1). ∎

## 8. Every companion, the ambient joint region and the selected anchors

**Corollary 8.1 (Bounded bases and complete worlds over $D_J$).** There
are finite $V_J,C_J>0$ such that every $(p,v)\in D_J$ satisfies

$$
|p|\le P_J,\qquad |v|\le V_J,
\tag{8.1}
$$

and every actual $W=(P,g,d)\in C(p,v)$ satisfies

$$
0<b,c\le C_J,\qquad |d|\le C_J,\qquad
\max_{0\le k\le3}|[s^k]g|\le C_J.
\tag{8.2}
$$

The same bound can be enlarged to bound $|a(W)|,|m(W)|$ for every
companion. In particular these conclusions hold over $D_J\cap D_M$,
including all worlds unused by either selected pair.

Proof. Theorem 7.1 bounds $p$ using only the selected actual $J$ pair.
S, Corollary 11.4, bounds $b$ for every world of its entire child.
Only now apply S, Theorem 12.1, with $(L,P_*)=(B,P_J)$. Its
complete-world coercivity bounds $c,d$, every padded whole-gain
coefficient and $v,a,m$ at all those companions, not just the selected
endpoints. Enlarge the common bound and choose $V_J$ accordingly.
No individual positive lower bound for $b$ or $c$ is inferred. ∎

**Corollary 8.2 (A bounded ambient joint region separated from $24$).**
For the positive $\epsilon$ of SII, Theorem 29.1, every original
joint base lies in the compact ambient subset of $\mathbb R^2$

$$
K=\{(p,v):|p|\le P_J,\ |v|\le V_J,\ |p-24|\ge\epsilon\}.
\tag{8.3}
$$

All actual companions above these joint bases satisfy Corollary 8.1.
The constants $P_J,V_J,C_J,\epsilon$ are qualitative.

Proof. Corollary 8.1 bounds both acquired coordinates. The selected
actual $M$ pair cannot occur in $0<|p-24|<\epsilon$ by the public
P24-gap. Since the original target has $p\ne24$, its bases obey the
last inequality in (8.3). This $K$ is closed and bounded in finite
dimensional Euclidean space and is separated from the excluded line.
This proves compactness of the ambient enclosure only. ∎

**Corollary 8.3 (One compact strict anchor per selected pair).** There
are $\varepsilon_J>0$ and a compact set $\mathcal A$ in the strict
off-$24$ full parent such that every selected joint configuration
(1.6) can be relabelled within its two pairs to satisfy

$$
W_0,W_2\in\mathcal A,\qquad
\delta(W_0),\delta(W_2)\ge\varepsilon_J,\qquad
\delta(W)=\min\{r,1-r,b,c\}.
\tag{8.4}
$$

The anchors may coincide. This gives no lower bound for the other
endpoint of either pair or for any unused companion.

Proof. SII, Theorem 14.3, at $P_*=P_J$ gives
$\max\{\delta(W_0),\delta(W_1)\}\ge\varepsilon(P_J)$ and
independently
$\max\{\delta(W_2),\delta(W_3)\}\ge\varepsilon(P_J)$.
Select one endpoint of each pair and take
$\varepsilon_J=\varepsilon(P_J)$. SII, Theorem 15.1, gives a
single compact strict-parent set containing both anchors. Its refinement
above the compact off-$24$ base set $K$ in (8.3) puts $\mathcal A$
inside the off-$24$ parent. These are selections among existing complete
worlds, not changes to the child or its observations. ∎

## 9. Exact remaining joint obligation

**Proposition 9.1 (Bounded-region reduction with unchanged guards).**
The original joint problem is equivalent to finding one configuration
(1.6) over $K$, or excluding every such configuration there, with all
the actual-world guards of Definition 1.1. Theorems 4.1–7.1 exclude
every unbounded-fifth-response actual $J$-pair mechanism. They do not
settle that bounded-region joint alternative.

Proof. Every original joint base lies in $K$ by Corollary 8.2, while
every actual configuration (1.6) over $K$ is already an original joint
configuration. No constraint on cross-pair distinctness or equality of
the two terminal common values was added. Theorem 7.1 rules out any
actual selected $J$-pair sequence with $|p|\to\infty$, including
the entire finite-source infinite-drift boundary exhausted in
Theorem 4.1. Corollary 8.1 then bounds all complete-world coordinates
over joint bases. Neither argument constructs a joint configuration
or excludes all configurations over $K$. ∎

**Definition 9.2 (Scope of the unresolved alternative).** The remaining
relation is the actual strict-real fibre product of the $J$-pair and
$M$-pair relations over $K$. Strict interior components and isolated
incidences, exceptional-meeting candidates and all original gain and
drift strata retain their whole-world guards. At a convergent sequence
of selected pairs above $K$, SII, Theorem 16.1, gives, after selecting
one strict anchor, an actual strict pair, an augmented interior
critical-diagonal limit, or a mixed finite-boundary/interior incidence.
Its last two alternatives are necessary limiting conditions, not actual
distinct pairs. The finite-face exclusions of S, Sections 19–21, and
SII, Sections 17–24, apply only with their owning hypotheses; remaining
finite $c=0$ mixed incidences and their joint consumers are not decided
by the tail theorem.

The ambient bound (8.3) does not assert that $D_J$, $D_J\cap D_M$,
or the set of strict configurations is closed or compact, or that a
collision projection is proper. Strict sources may approach finite
faces, and distinct pairs may approach a critical diagonal. The compact
set in Corollary 8.3 contains one selected endpoint per pair; it does
not contain every endpoint or every companion with a uniform interior
margin. There is no separate positive $b$ or $c$ floor for those worlds,
no numerical tail or gap threshold, and no global $p$ bound for the
$M$-only locus $D_M$.

The unchanged global joint witness-or-exclusion problem remains open.
No physical realization, ancestor conjunction, fifth-$M$ $L_2$, $H_4$
$L_3$, root $L_7$, or eight-versus-nine conclusion follows from this
bounded-region reduction.

## 追加锚（本行以下为增补区）

## 10. The finite-drift full-parent response circuit

**Definition 10.1 (Ambient equation and response extension).** Use the
literal worlds, clocks, entire child and selected-pair quantifiers of
Definition 1.1. In the open coordinate domain

$$
\Omega=\{(r,b,e):0<r<1,\ b>0,\ e\in\mathbb R\}
$$

put $c=r(1-r)/b$ and retain $j,n,T,U,\Lambda,\kappa$ from (1.7).
The undivided parent equation is

$$
H(r,b,e)=e\Lambda+\frac{24}{5}(b-1/8)\kappa=0.
\tag{10.1}
$$

Here $H$ is a function, distinct from the history $H_4$. Define the
four entries of a column $G$ by

$$
G=\begin{pmatrix}G_0\\G_1\\G_2\\G_3\end{pmatrix}
=\begin{pmatrix}-24-e\\-e/j\\(27/5-e)/T\\-e/n\end{pmatrix}.
\tag{10.2}
$$

For every point of $\Omega$, let $g_{r,b,e}(s)$ be the single polynomial
of degree at most three given by

$$
g_{r,b,e}(s)=\sum_{\ell=0}^3G_\ell
 \prod_{\substack{0\le h\le3\\h\ne\ell}}
 \frac{s-h}{\ell-h}.
\tag{10.3}
$$

The following rows are its evaluations at the original clocks $5,6,7$:

$$
\begin{pmatrix}G_5\\G_6\\G_7\end{pmatrix}
=\begin{pmatrix}
-4&15&-20&10\\
-10&36&-45&20\\
-20&70&-84&35
\end{pmatrix}G.
\tag{10.4}
$$

Define an ambient analytic response extension $X=(X_0,X_1,X_2,X_3)$ by

$$
\begin{aligned}
X_0&=24+e+(U+n)G_5,\\
X_1&=24+e+(2U+n)G_6,\\
X_2&=24+e+(T+2j+4r)G_7,\\
X_3&=24+e+(3U+2n)G_7.
\end{aligned}
\tag{10.5}
$$

Off $H=0$ these expressions are only a rational extension for
calculus. They assert no additional worlds. On the parent they are
exactly $(p,v,a,m)$, with both terminal readings at clock seven on the
same complete world.

**Lemma 10.2 (Exact full-parent correspondence).** The zero set
$\{H=0\}\subset\Omega$ is in analytic one-to-one correspondence with
the entire strict parent $\mathcal H$ by

$$
(r,b,e)\longmapsto
\left(\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
 g_{r,b,e},24+e\right).
\tag{10.6}
$$

This correspondence uses the coefficients of the whole polynomial,
including zero leading coefficients, and (10.5) gives all four later
responses without changing the original observations.

Proof. This is the converse of Definition 1.2, equivalently O,
Theorem 2.1, in the present notation. Its original-row verification can
also be read directly from (10.2). At clocks $0,1,2,3$, the traces
$(1,j,T,n)$ give $0,24,147/5,24$. Interpolation gives

$$
g_{r,b,e}(4)=-G_0+4G_1-6G_2+4G_3,
\qquad
g_{r,b,e}(4)-\frac{18-(24+e)}U=H.
\tag{10.7}
$$

For the constant term of the second identity one uses

$$
24-\frac{162}{5T}+\frac6U
=\frac{24}{5}(b-1/8)\kappa.
$$

Consequently the original fourth-clock response is $18$ precisely on
$H=0$. The other responses follow from (1.10) and (10.4). If the
constructed gain were identically zero, the original readings at clocks
zero and one would both be $d$, contradicting $0\ne24$. Thus its
nonzeroness follows from the original data and imposes no sample or
leading-coefficient condition. Conversely every complete parent world
fixes $(r,b,e)$ and all four entries (10.2), which uniquely determine
its entire gain by (10.3).

All rational denominators $b,j,n,T,U$ are positive on $\Omega$.
Interpolation uses only the nonzero differences of the fixed nodes
$0,1,2,3$. Hence (10.6), with four padded gain coefficients, is
analytic; its inverse reads $r,b$ from $P$ and $e=d-24$. This also
identifies the local parent topology and its tangent spaces with those
of $H=0$. No division by $e$, $d$, $\Lambda$, a gain sample, a gain
coefficient or a root difference is involved. ∎

## 11. Both strict singular lines and their full tangent planes

**Proposition 11.1 (Exhaustive strict singular-source classification).**
Define

$$
\begin{aligned}
S(r)&=438272r^4-931328r^3+540800r^2-50728r-853,\\
A_s(r)&=64r^2-64r-1,\qquad
B_s(r)=64r^2-72r-1.
\end{aligned}
\tag{11.1}
$$

Exactly two roots of $S$ lie in $(0,1)$; both are simple. Denote them
by $r_-,r_+$, with

$$
\frac18<r_-<\frac3{20},\qquad
\frac9{10}<r_+<\frac{11}{12}.
\tag{11.2}
$$

The complete strict parent worlds with $\Lambda=0$ are precisely the
two lines (10.6) with

$$
(r,b,e)=(r_-,1/8,e)\quad\hbox{or}\quad(r_+,1/8,e),
\qquad e\in\mathbb R.
\tag{11.3}
$$

In particular every real drift $d=24+e$ is retained on each line.

Proof. Since $\kappa=2(2+5b)/(TU)>0$, equations $H=0$ and
$\Lambda=0$ force $b=1/8$. At this width

$$
\begin{gathered}
T=9/8,\quad U=5/4,\quad \kappa=56/15,\\
j=-A_s/8,\quad n=-B_s/8,\qquad
\Lambda(r,1/8)=\frac{S(r)}{15A_s(r)B_s(r)}.
\end{gathered}
\tag{11.4}
$$

For $0<r<1$, $A_s=-1-64r(1-r)<0$ and $B_s=A_s-8r<0$.
Thus all these denominators are nonzero, and the singular source
condition is exactly $S(r)=0$. This is the same quartic as O,
Theorem 4.2; the following explicit Sturm certificate also supplies
simplicity and the intervals needed here.

Start with $S_0=S$, $S_1=S'$. For each subsequent term take the
negative rational polynomial remainder, multiply by the positive least
common multiple of its coefficient denominators, and divide by its
positive integer coefficient gcd. The resulting chain is

$$
\begin{aligned}
S_0&=S,\\
S_1&=1753088r^3-2793984r^2+1081600r-50728,\\
S_2&=1610816r^2-1689664r+121445,\\
S_3&=64839740164r-26327821511,\\
S_4&=1.
\end{aligned}
\tag{11.5}
$$

Every normalization after taking a negative remainder has positive
scale, so this is a sign-preserving Sturm chain. Its endpoint signs,
with $V$ the number of sign changes after omitting zero entries, are

| $r$ | $S_0$ | $S_1$ | $S_2$ | $S_3$ | $S_4$ | $V(r)$ |
| --- | --- | --- | --- | --- | --- | --- |
| $0$ | $-$ | $-$ | $+$ | $-$ | $+$ | $3$ |
| $1/8$ | $-$ | $+$ | $-$ | $-$ | $+$ | $3$ |
| $3/20$ | $+$ | $+$ | $-$ | $-$ | $+$ | $2$ |
| $9/10$ | $+$ | $-$ | $-$ | $+$ | $+$ | $2$ |
| $11/12$ | $-$ | $-$ | $-$ | $+$ | $+$ | $1$ |
| $1$ | $-$ | $-$ | $+$ | $+$ | $+$ | $1$ |

The terminal constant gives $\gcd(S,S')=1$. Sturm's theorem counts
exactly one root in each interval (11.2) and two in the whole strict
interval. Conversely, at either root with $b=1/8$, both terms of $H$
vanish for every real $e$. Lemma 10.2 supplies exactly one legal whole
gain for each such triple, proving (11.3) without a regular-chart
restriction. ∎

**Lemma 11.2 (A tangent basis for every drift).** At every point of
(11.3), the full parent is a smooth analytic surface and its tangent
plane has the basis

$$
\partial_e,\qquad
V=H_b\partial_r-H_r\partial_b.
\tag{11.6}
$$

All partial derivatives here and below are taken in the independent
ambient coordinates $(r,b,e)$, with $c=r(1-r)/b$ already substituted.

Proof. At such a point $H_e=\Lambda=0$, so both vectors annihilate
$dH$. Along $b=1/8$ the other two derivatives are

$$
H_r=e\Lambda_r,\qquad H_b=e\Lambda_b+448/25.
\tag{11.7}
$$

At a root of $S$, (11.4) gives

$$
\Lambda_r=\frac{S'}{15A_sB_s}\ne0.
\tag{11.8}
$$

If $e\ne0$, then $H_r\ne0$; if $e=0$, then $H_b=448/25\ne0$.
Thus $dH\ne0$ in every case. The analytic implicit-function theorem
makes $H=0$ a two-dimensional surface near the point. The vector $V$
is nonzero and has no $e$ component, so it is independent of
$\partial_e$ and these two vectors span the tangent plane.

Here $e=0$ means $d=24$. Zero drift is instead $d=0$, namely
$e=-24$, and belongs to the $e\ne0$ case. Both are included. The
basis is for the full surface, rather than only the one-dimensional
fixed-source line: it retains its transverse source direction. ∎

## 12. Exact finite certificates for the augmented tangent minors

**Definition 12.1 (Three polynomial minor circuits).** Differentiate
(10.1)–(10.5) in $\Omega$ before substituting $b=1/8$. For
$0\le i\le3$ define rational functions of $(r,e)$ by

$$
\alpha_i=\left.\partial_eX_i\right|_{b=1/8},\qquad
\nu_i=\left.(H_b\partial_rX_i-H_r\partial_bX_i)\right|_{b=1/8}.
\tag{12.1}
$$

The minors using the first response row are

$$
M_i=\alpha_0\nu_i-\alpha_i\nu_0\quad (i=1,2,3).
\tag{12.2}
$$

These are defined for every $r$ with $A_sB_s\ne0$ and every $e$;
no reduction modulo $S$ is made in their definition. Define

$$
\begin{aligned}
F_1(r,e)&=\frac{6075}{128}B_s^3A_s^4M_1,\\
F_2(r,e)&=\frac{91125}{64}B_s^4A_s^4M_2,\\
F_3(r,e)&=\frac{91125}{256}B_s^3A_s^4M_3.
\end{aligned}
\tag{12.3}
$$

Equations (10.1)–(10.5), (11.1) and (12.1)–(12.3) are exact
coefficient circuits for these polynomials. The stated rational scalar
factors are part of their definition: no primitive-part operation,
coefficient rescaling or removal of a factor is implicit.

For clarity, the derivative rules needed to expand the circuits are

$$
\begin{gathered}
j_r=(1-2r)/b,\quad j_b=1-r(1-r)/b^2,\quad
n_r=1+j_r,\quad n_b=j_b,\\
T_r=U_r=0,\quad T_b=1,\quad U_b=2,\\
\Lambda_r=4j_r/j^2+4n_r/n^2,\\
\Lambda_b=-6/T^2-2/U^2+4j_b/j^2+4n_b/n^2,\quad
\kappa_b=-6/T^2+4/U^2,\\
H_r=e\Lambda_r,\qquad
H_b=e\Lambda_b+\frac{24}{5}\bigl(\kappa+(b-1/8)\kappa_b\bigr),\\
\partial_eG=(-1,-1/j,-1/T,-1/n)^{\mathsf T},\\
\partial_rG=(0,e j_r/j^2,0,e n_r/n^2)^{\mathsf T},\\
\partial_bG=(0,e j_b/j^2,-(27/5-e)/T^2,e n_b/n^2)^{\mathsf T}.
\end{gathered}
\tag{12.4}
$$

The rows (10.4) apply to these derivative columns as well. Differentiating
(10.5) by the product rule then specifies every entry of (12.1).
In particular substituting $b=1/8$ before taking $\partial_b$ would
not define the same circuits.

**Lemma 12.2 (Integral polynomial and degree certificate).** All three
$F_i$ belong to $\mathbb Z[r,e]$. Their exact degrees and numbers of
nonzero monomials are

| Polynomial | $\deg_e$ | $\deg_r$ | Number of monomials in $(e,r)$ |
| --- | --- | --- | --- |
| $F_1$ | $2$ | $17$ | $52$ |
| $F_2$ | $2$ | $19$ | $59$ |
| $F_3$ | $2$ | $17$ | $52$ |

For every strict $r$, the nonzero factors in (12.3) preserve the
vanishing or nonvanishing of each corresponding $M_i$.

Proof. Substitute the derivative rules (12.4) into (12.1), using
$j=-A_s/8$, $n=-B_s/8$, $T=9/8$, $U=5/4$. Collecting the
products in (12.2) gives the exact rational identities

$$
M_1=\frac{128F_1}{6075B_s^3A_s^4},\qquad
M_2=\frac{64F_2}{91125B_s^4A_s^4},\qquad
M_3=\frac{256F_3}{91125B_s^3A_s^4},
\tag{12.5}
$$

whose numerators, on expanding the defining circuits, have integer
coefficients and the degrees and support counts in the table. This is
an identity in $\mathbb Q(r,e)$ without using $S=0$. It can be
reproduced by polynomial multiplication and collection from (12.4);
thus (12.3) also specifies every coefficient without an external list.
The $e$ degree is at most two already because $X$ is affine in $e$,
$H_r,H_b$ are affine in $e$, and $\alpha_i$ is independent of $e$.
The table records the exact, nonvanishing top degrees after collection.
Finally $A_sB_s\ne0$ in the strict interval by Proposition 11.1,
and all scalar denominators in (12.3) are nonzero integers. ∎

**Definition 12.3 (Fixed quadratic Sylvester determinants).** Write

$$
F_i=f_{i,2}(r)e^2+f_{i,1}(r)e+f_{i,0}(r),
\qquad f_{i,k}=[e^k]F_i.
$$

For any two coefficient triples $f=(f_2,f_1,f_0)$ and
$g=(g_2,g_1,g_0)$ put

$$
\mathcal R(f,g)=\det\begin{pmatrix}
f_2&f_1&f_0&0\\
0&f_2&f_1&f_0\\
g_2&g_1&g_0&0\\
0&g_2&g_1&g_0
\end{pmatrix}.
\tag{12.6}
$$

Define the fixed integer polynomials

$$
R_J(r)=\mathcal R(f_1,f_2),\qquad
R_M(r)=\mathcal R(f_1,f_3).
\tag{12.7}
$$

Here $f_i$ denotes the whole coefficient triple of $F_i$, not its
linear coefficient. These are the degree-$(2,2)$ Sylvester resultants
in $e$ with rows $eF_1,F_1,eF_i,F_i$ and descending columns
$e^3,e^2,e,1$. The size is kept fixed at every value of $r$,
including values where one or both quadratic leading coefficients
vanish. No specialized degree or gain-degree hypothesis is imposed.

**Lemma 12.4 (Two modular coprimality certificates).** The fixed
resultants have

$$
\begin{array}{c|cc}
&\deg_r&\operatorname{lc}\pmod{101}\\ \hline
R_J&68&13\\
R_M&62&46.
\end{array}
\tag{12.8}
$$

Neither has a common complex root with $S$.

Proof. All finite-field expressions in this proof lie in
$\mathbb F_{101}[r]$. Reduction of $S$ is

$$
s=33r^4-7r^3+46r^2-26r-45.
\tag{12.9}
$$

Expand the coefficient circuits (12.3), form the two determinants
(12.6), and collect powers of $r$. This gives (12.8). Alternatively
the modular remainders can be obtained by reducing every entry of
(12.6) in $\mathbb F_{101}[r]/(s)$ before taking its determinant.
The resulting exact polynomial remainders are

$$
\begin{aligned}
\rho_J&=\operatorname{rem}(\overline{R_J},s)
       =-31r^3-r^2-39r+12,\\
\rho_M&=\operatorname{rem}(\overline{R_M},s)
       =-21r^3-48r^2-37r-17.
\end{aligned}
\tag{12.10}
$$

The bar means coefficient reduction modulo $101$; remainder always
means the unique remainder of degree less than four on division by
$s$, whose leading coefficient $33$ is invertible. The following
fully specified polynomials certify coprimality:

$$
\begin{aligned}
u_J&=43r^2-46r-3,&
w_J&=36r^3-24r^2+33r-28,\\
u_M&=29r^2-45r-18,&
w_M&=-41r^3+47r^2-9r+6.
\end{aligned}
\tag{12.11}
$$

Direct coefficient multiplication gives identities in the polynomial
ring, rather than only in its quotient,

$$
u_Js+w_J\rho_J=1,\qquad u_Ms+w_M\rho_M=1.
\tag{12.12}
$$

For an additional fixed-determinant check, the ordinary degree-$(4,3)$
Sylvester determinants are

$$
\operatorname{Res}_r(s,\rho_J)=61,\qquad
\operatorname{Res}_r(s,\rho_M)=84
\quad\hbox{in }\mathbb F_{101}.
\tag{12.13}
$$

These determinant conventions have the shifted rows of the first
polynomial first, those of the second next, and descending powers in
the columns, as in (12.6). Thus every coefficient and determinant in
(12.8)–(12.13) is fixed by the public circuits and finite arithmetic.

To pass to characteristic zero, the degrees of $S,R_J,R_M$ are
preserved modulo $101$: their leading residues are respectively
$33,13,46$. Polynomial remainder and the resultant product formula
therefore give the reductions of the fixed integer outer determinants

$$
\begin{aligned}
\operatorname{Res}_r(S,R_J)&\equiv33^{68-3}\,61\equiv27\pmod{101},\\
\operatorname{Res}_r(S,R_M)&\equiv33^{62-3}\,84\equiv49\pmod{101}.
\end{aligned}
\tag{12.14}
$$

Indeed for a degree-four first polynomial with leading coefficient
$33$, the resultant with a second polynomial of degree $N$ is
$33^{N-3}$ times the resultant with its degree-three remainder. This
follows directly from the product over the four roots, with multiplicity.
Both residues
are nonzero. Hence the corresponding integer Sylvester determinants
are nonzero, and the classical resultant criterion excludes a common
complex root of $S$ with either $R_J$ or $R_M$. The lifting argument
uses fixed integer determinants with preserved degrees; a modular
identity with an unguarded degree drop is not being used. ∎

## 13. All-drift immersion and the singular critical-diagonal exclusion

**Theorem 13.1 (Full-parent immersion on both entire singular lines).**
At every strict parent world with $\Lambda=0$, for every real
$e=d-24$, both maps

$$
\Psi_J=(p,v,a),\qquad \Psi_M=(p,v,m)
\tag{13.1}
$$

have differential rank two on the full analytic parent and are locally
injective there. This assertion includes both sources (11.2),
$e=0$ ($d=24$), zero drift $d=0$ ($e=-24$), all lower gain degrees,
and every sampled or repeated gain root allowed by Definition 1.1.
There is no restriction on the signs of drift or gain.

Proof. Proposition 11.1 places the world on exactly one of (11.3),
and Lemma 11.2 supplies the full-parent tangent basis
$(\partial_e,V)$. In this basis the differential of $X_i$ is the
row $(\alpha_i,\nu_i)$. For $J$, its two minors involving the first
row are $M_1,M_2$; for $M$, they are $M_1,M_3$.

Suppose both $J$ minors vanished at $(r_*,e_*)$. By (12.3) this
would give $F_1(r_*,e_*)=F_2(r_*,e_*)=0$. A common finite root in
$e$ forces the fixed determinant $R_J(r_*)$ to vanish, even if a
quadratic leading coefficient vanishes at $r_*$. Explicitly the
specialized matrix (12.6) annihilates the nonzero column

$$
(e_*^3,e_*^2,e_*,1)^{\mathsf T}.
\tag{13.2}
$$

Its rows evaluate to $e_*F_1,F_1,e_*F_2,F_2$, all zero. Thus its
determinant is zero without division by a leading coefficient. But
$S(r_*)=0$, contradicting Lemma 12.4. At least one of $M_1,M_2$
is consequently nonzero. The same argument with $F_1,F_3,R_M$ proves
that at least one of $M_1,M_3$ is nonzero. Each three-coordinate map
therefore has rank two.

Choose a local two-dimensional analytic chart of $H=0$ furnished by
Lemma 11.2. One of the two-coordinate submaps $(p,v)$ or $(p,a)$
for $J$, and one of $(p,v)$ or $(p,m)$ for $M$, has invertible
derivative in that chart. The real analytic inverse-function theorem
makes the chosen submap injective on an open neighbourhood of the
world. Its full three-coordinate map is injective on that same
neighbourhood. Through Lemma 10.2 this is uniqueness of the source,
fixed drift and entire polynomial gain of actual worlds, rather than
uniqueness of selected gain samples or of a fixed-source restriction.

The determinant argument uses a finite common $e_*$ and never divides
by $e_*$ or $e_*+24$. The only source denominators cleared in the
minor circuits are the strict positive original denominators, or their
nonzero $A_s,B_s$ forms. No gain factor, sample, leading coefficient,
degree equality or root separation was removed. Thus the proof covers
every real drift and every original gain stratum stated above. ∎

**Corollary 13.2 (Coalescing selected strict pairs have regular sources).**
Let $E\in\{J,M\}$. Suppose distinct actual selected endpoints obey

$$
\begin{gathered}
W_n,W'_n\in C(p_n,v_n),\quad W_n\ne W'_n,\quad
\tau_E(W_n)=\tau_E(W'_n),\qquad p_n\ne24,\\
(p_n,v_n)\longrightarrow(p_*,v_*),\quad p_*\ne24,\qquad
W_n\longrightarrow W,\quad W'_n\longrightarrow W,
\end{gathered}
\tag{13.3}
$$

where $W$ is a strict complete world and $\tau_J=a,\tau_M=m$.
Then $\Lambda(W)\ne0$. Consequently case 2 of SII, Theorem 16.1,
can occur only at a regular source, for either selected pair of the
original joint relation (1.6).

Proof. Continuity of the original readings and terminal response gives
$W\in C(p_*,v_*)$. If $\Lambda(W)=0$, Theorem 13.1 supplies a
neighbourhood in the full parent on which $\Psi_E$ is injective.
Both convergent endpoints eventually lie in this one neighbourhood.
They have equal $p_n,v_n,\tau_E$, so they have equal $\Psi_E$;
injectivity makes them equal as complete worlds, contradicting their
within-pair distinctness. This proves the assertion. In a joint
sequence the argument applies to either selected pair at its own
coalescence limit, independently of whether the pairs overlap or have
equal common terminal values. SII, Theorem 16.1, supplies precisely
these strict coalescing limits in its second alternative. ∎

**Proposition 13.3 (Exact scope of the remaining joint obligation).**
The singular critical-diagonal alternative in Definition 9.2 is
excluded by Corollary 13.2. The original problem remains the strict
same-entire-child witness-or-exclusion alternative of Proposition 9.1,
with all quantifiers of (1.6).

Proof. Theorem 13.1 is local at each finite singular-source world.
It rules out distinct equal-augmented-response endpoints converging to
that same world. The local neighbourhood may depend on the source and
the drift. The theorem gives no comparison between disjoint full-parent
neighbourhoods, between the two singular lines, or between a singular
world and a distant regular world. Distinct distant incidences not
already ruled out by the owning public results, and singular companions
unused by the selected pairs, are retained.

For regular sources $\Lambda\ne0$, the augmented critical loci and
their possible actual selected-pair limits remain to be analyzed.
Finite-boundary/interior limits remain subject only to their owning
public exclusions, and this argument adds no finite-face exclusion or
uniform interior margin. In particular it adds no separate positive
floor for a source entry. Cases 1 and 3 of SII, Theorem 16.1, are not
removed. Nothing here constructs an actual joint witness or excludes
all such witnesses over the ambient set $K$ of (8.3).

The precise all-drift statement concerns both complete lines (11.3)
and both terminal maps. It extends beyond the strict $p=24$ scope of
SII, Theorem 27.2, while leaving the bounded-region reduction of
Sections 7–9 in force. All responses still use the original clocks,
one fixed drift and one entire gain per world; the selected $J$ and
$M$ pairs still belong to the same entire child and have only their
original within-pair distinctness requirements. No physical realization,
Lean/kernel verification, ancestor conjunction, fifth-$M$ $L_2$,
$H_4$ $L_3$, root $L_7$, or eight-versus-nine conclusion follows. ∎

The polynomial and minor certificates above are model-specific
calculations. Fixed-node interpolation, the sign-preserving Sturm
criterion, Sylvester's resultant criterion, the polynomial Bézout
criterion and the analytic implicit/inverse function theorems are
classical tools. The interpolation attribution in Definition 1.2 and
the implicit/inverse-function reference in Theorem 6.1 apply here on
the explicit nonzero-denominator domains and two-dimensional charts
just proved. These ordinary mathematical results carry no claim of
literature-wide novelty or of formal-kernel verification. The unchanged
strict-real same-child joint problem remains open.

## 追加锚（本行以下为增补区）
