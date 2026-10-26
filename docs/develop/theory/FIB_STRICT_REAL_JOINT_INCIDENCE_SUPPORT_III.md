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

## 14. The actual strict singular locus and terminal-$M$ injectivity

**Definition 14.1 (Actual singular locus).**  In the coordinates of
Definition 10.1, let

$$
\mathcal S=\{W\in\mathcal H:0<r(W)<1,\ b(W)>0,\ H(r(W),b(W),e(W))=0,
\ \Lambda(r(W),b(W))=0\}.
\tag{14.1}
$$

Here $H=0$ means the parent-consistency equation (10.1), and only the
actual strict worlds in the full parent are included.  Thus $H$ in
(14.1) is neither the history $H_4$ nor a sextic or a scaled gain
polynomial.  Write

$$
\Psi_M(W)=(p(W),v(W),m(W)).
\tag{14.2}
$$

Proposition 11.1 identifies the set in (14.1) with the two complete
strict source lines $r=r_-$ and $r=r_+$, $b=1/8$, with arbitrary real
$e$.  No boundary label is included in $\mathcal S$.

**Lemma 14.2 (Response formulas on the two actual singular lines).**
Put

$$
D(n)=716n^2+31n-900,
$$

and, for $n>0$, put

$$
\begin{aligned}
A(n)&=-\frac{D(n)}{144n},\\
B(n)&=-\frac{142n^2+185n-400}{10n},\\
C(n)&=-\frac{1448n^2+1011n-3150}{24n}.
\end{aligned}
\tag{14.3}
$$

On a singular line, $U=5/4$, and interpolation of the one whole gain
at the original nodes gives

$$
\begin{aligned}
g(5)&=e\left(\frac5n-\frac{179}{36}\right),\\
g(6)&=24+e\left(\frac{16}{n}-\frac{71}{5}\right),\\
g(7)&=\frac{384}{5}+e\left(\frac{35}{n}-\frac{181}{6}\right).
\end{aligned}
\tag{14.4}
$$

Consequently the three original responses are

$$
\begin{aligned}
p&=24+eA(n),\\
v&=84+24n+eB(n),\\
m&=312+\frac{768}{5}n+eC(n).
\end{aligned}
\tag{14.5}
$$

Proof. On $\mathcal S$, Proposition 11.1 gives $b=1/8$, hence
$T=9/8$, $U=5/4$, $j=1/8+8r-8r^2$, and
$n=1/8+9r-8r^2$.  Equation (10.7) gives
$g(4)=(-6-e)/U$; applying the fixed-node interpolation formula to the
four values at $0,1,2,3$ gives (14.4).  Substitution into (1.10)
gives (14.5).  No gain coefficient, gain sample, drift, or source
factor is divided out. ∎

**Theorem 14.3 (Global injectivity of terminal $M$ on actual singular
sources).**  The map $\Psi_M$ is injective on $\mathcal S$, including
both singular lines, every real $e$ (in particular $e=0$ and
$e=-24$), lower gain degrees, and repeated or sampled gain roots.

Proof.  The exact evaluations

$$
\begin{aligned}
S(13/100)&=-89481543/390625,&
S(7/50)&=100610367/390625,\\
S(9/10)&=94967/625,&
S(91/100)&=-178093443/390625
\end{aligned}
$$

refine the two unique strict roots of Proposition 11.1 to

$$
\frac{13}{100}<r_-<\frac7{50},
\qquad
\frac9{10}<r_+<\frac{91}{100}.
\tag{14.6a}
$$

The monotonicity of $n(r)=1/8+9r-8r^2$ on these intervals then gives

$$
\frac{23}{20}<n_-<\frac54,
\qquad
\frac53<n_+<\frac74.
\tag{14.6}
$$

The polynomial $D$ is increasing for $n>0$, and

$$
D(23/20)=\frac{2064}{25}>0.
\tag{14.7}
$$

Thus $A(n_\pm)\ne0$.  If two points lie on the same singular line
and have equal $p$, (14.5) first gives equal $e$; Proposition 11.1 and
the zero-safe correspondence (10.6) then give the same complete world.

It remains to separate the two lines.  Define

$$
K(n)=\frac{C(n)-(32/5)B(n)}{A(n)}
 =-\frac{6(18328n^2+45765n-74850)}{25D(n)}.
\tag{14.8}
$$

Equation (14.5) gives the identity

$$
m-\frac{32}{5}v+\frac{1128}{5}=(p-24)K(n).
\tag{14.9}
$$

For independent variables $n,z$, direct subtraction gives

$$
K(n)-K(z)=
\frac{12(n-z)E(n,z)}{25D(n)D(z)},
\tag{14.10}
$$

where

$$
E(n,z)=16099786nz-18548700(n+z)+19434075.
\tag{14.11}
$$

The four corner values of this bilinear polynomial on
$[23/20,5/4]\times[5/3,7/4]$ are

$$
-\frac{11721041}{6},\quad
-\frac{78253427}{40},\quad
-\frac{6750475}{6},\quad
-\frac{7949945}{8}.
\tag{14.12}
$$

The bilinear interpolation formula on a rectangle is a convex
combination of its four corner values, so $E<0$ throughout that
rectangle.  Equations (14.6), (14.7), and (14.10) imply
$K(n_- )\ne K(n_+)$.

Suppose points on the two lines had equal $(p,v,m)$.  Comparing (14.9)
and using the unequal $K$ values forces $p=24$.  Equation (14.5) and
$A(n_\pm)\ne0$ then force both $e$ values to be zero.  The second
equation in (14.5) becomes $v=84+24n$, which differs on the two
disjoint intervals in (14.6), a contradiction.  This explicitly
handles the $p=24$ case even though selected children in Definition
1.1 use $p\ne24$.  Hence $\Psi_M$ is injective on all of $\mathcal S$.
∎

**Corollary 14.4 (Effect on a selected $M$ pair).**  If
$p\ne24$ and $W\ne W'$ are actual members of $C(p,v)$ with
$m(W)=m(W')$, at most one of $W,W'$ belongs to $\mathcal S$.

This removes the singular--singular endpoint possibility for the
selected $M$ pair.  It does not remove a singular--regular pair, a
regular--regular pair, or an unused singular companion in the same
child.  It leaves the selected $J$ pair, its shared $(p,v)$, and the
within-pair distinctness requirements exactly as in (1.6); no joint
witness or joint exclusion follows from this corollary.

## 15. A C1 boundary point and its strict interior continuation

**Definition 15.1 (Auxiliary C1 face).**  For $t>0$, use the boundary
source label $(r,b,c)=(1,t,0)$ only as an analytic extension.  It is not
an actual strict world.  Set

$$
q(t)=t^3-4t-2,\qquad D_1(t)=5(t+1)q(t).
\tag{15.1}
$$

On the C1 face the parent equation and its drift solution are

$$
\Lambda_1(t)=\frac{2q(t)}{t(t+1)(2t+1)},\qquad
e_1(t)=-\frac{3t(8t-1)(5t+2)}{5q(t)}.
\tag{15.2}
$$

For $q(t)\ne0$ define the boundary response extension by

$$
\begin{aligned}
p_1(t)-24&=-\frac{6(8t-1)(7t^3+11t^2+19t+10)}{D_1(t)},\\
v_1(t)-24&=-\frac{3(415t^4+921t^3+2326t^2+1466t+186)}{D_1(t)},\\
m_1(t)-24&=-\frac{3(1128t^4+3523t^3+9818t^2+6862t+1140)}{D_1(t)}.
\end{aligned}
\tag{15.3}
$$

These are the original-clock responses obtained from (10.2)--(10.5)
at the C1 boundary label.  They are used below only on a box where
$q$ and $\Lambda_1$ are separated from zero.

**Definition 15.2 (Exact four-variable equation).**  In the order
$x=(t,b,r,e)$, let

$$
F(t,b,r,e)=
\begin{pmatrix}
H(r,b,e)\\
X_0(r,b,e)-p_1(t)\\
X_1(r,b,e)-v_1(t)\\
X_3(r,b,e)-m_1(t)
\end{pmatrix},
\tag{15.4}
$$

where $H$ and $X_i$ are the parent-consistency and response functions
of (10.1) and (10.5).  The following centre consists of exact
terminating rationals:

Writing $H_B=H(r,b,e)$, $p_B=X_0(r,b,e)$,
$v_B=X_1(r,b,e)$, and $m_B=X_3(r,b,e)$, this is exactly

$$
F=(H_B,p_B-p_1(t),v_B-v_1(t),m_B-m_1(t))^{\mathsf T}.
\tag{15.4a}
$$

$$
x_0=\begin{pmatrix}
8987958556003912/10^{16}\\
8707641022982145/10^{16}\\
9275770846479353/10^{16}\\
4981230390477398/10^{15}
\end{pmatrix},
\qquad
Q=x_0+[-10^{-8},10^{-8}]^4.
\tag{15.5}
$$

Let

$$
R=10^{-6}
\begin{pmatrix}
-19276441&4040634&-1158716&124302\\
-32067794&7561101&-2554574&335613\\
-34766236&9531752&-3733207&557972\\
5399875&-17649922&12206129&-2425481
\end{pmatrix}.
\tag{15.6}
$$

**Lemma 15.3 (Reproducible rational contraction certificate).**  On
$Q$, exact rational interval arithmetic gives

$$
\|RF(x_0)\|_\infty<10^{-12},
\tag{15.7}
$$

and, entry by entry,

$$
\left|I-RDF(x)\right|\le10^{-6}
\begin{pmatrix}
258&1146&998&72\\
426&1854&1650&118\\
505&2270&2065&148\\
1550&6244&5691&402
\end{pmatrix}
\quad(x\in Q).
\tag{15.8}
$$

The certificate is specified without a floating-point convention as
follows.  For rational intervals $I=[a,b]$ and $J=[c,d]$, use

$$
I+J=[a+c,b+d],\quad I-J=[a-d,b-c],
$$

and let $IJ$ be the interval with endpoints the minimum and maximum of
$ac,ad,bc,bd$.  If $0\notin I$, let $I^{-1}$ be the interval hull of
$\{1/u:u\in I\}$ and put $I/J=I J^{-1}$.  Propagate a value and its
four derivatives as a pair $(I,I')$ by

$$
\begin{aligned}
(I,I')+(J,J')&=(I+J,I'+J'),\\
(I,I')(J,J')&=(IJ,I'J+IJ'),\\
\bigl(I^{-1},-(I')/I^2\bigr)&=\operatorname{D}(1/f)
\quad\text{when }(I,I')=\operatorname{D}(f).
\end{aligned}
\tag{15.9}
$$

Constants have zero derivative vectors and the four coordinate
functions have the corresponding standard basis vectors.  Horner
evaluation of the displayed polynomials, followed by (15.9), evaluates
both $F$ and $DF$ using outward rational endpoints.  Partition each
coordinate interval of $Q$ into four equal rational intervals.  This
is the explicit $4^4=256$-subbox grid; on each subbox all sixteen
entries of $I-RDF$ are evaluated by (15.9), and their componentwise
maxima give (15.8).  Thus the table is reproduced from (15.1)--(15.6)
by finite rational operations.  Direct fraction comparison after
clearing positive denominators gives the four inequalities in (15.7).

The largest row sum in (15.8) is

$$
\frac{13887}{10^6}<\frac1{50}.
\tag{15.10}
$$

Proof.  The preceding recurrence is ordinary interval automatic
differentiation, so every denominator used in a reciprocal is checked
to avoid zero on its subbox.  The grid is finite and rational, and the
convex-hull operation taking the maximum of the 256 bounds preserves
the displayed componentwise inequalities. ∎

**Proposition 15.4 (An exact boundary-to-interior mixed-$M$ solution).**
There is an exact $x_*\in Q$ with $F(x_*)=0$, and it has the following
strict sign and response bounds.  Every endpoint in the display is a
terminating rational; decimal notation is only a shorter rendering.

$$
\begin{array}{c|c}
\text{quantity}&\text{certified interval}\ \hline
t&[0.8987958456003912,\ 0.8987958656003912]\\
q(t)&[-4.869105644371515,-4.869105515901476]\\
\Lambda_1(t)&[-2.039649458741292,-2.039649308892886]\\
e_1(t)&[4.452361155628864,4.452361555816960]\\
b&[0.8707640922982145,0.8707641122982145]\\
r&[0.9275770746479353,0.9275770946479353]\\
r(1-r)/b&[0.07714813430547741,0.07714815904577490]\\
\Lambda(r,b)&[-1.780571070584005,-1.780570758182900]\\
e&[4.981230380477398,4.981230400477398]\\
p&[56.979126254089785,56.97915185049104]\\
v&[304.4973220331739,304.4974196326005]\\
m&[1226.7304798320263,1226.7307912592719]
\end{array}
\tag{15.11}
$$

In particular all source entries $r,b,c$, and the derived positive
quantities $j,n,T,U$ are strictly positive at $x_*$.  The two displayed
$\Lambda$ intervals are contained respectively in $(-2.040,-2.039)$
and $(-1.781,-1.780)$; $p>56$ and $e>0$.

Proof.  Define $T(x)=x-RF(x)$.  From (15.7)--(15.10), for $x\in Q$,

$$
\|T(x)-x_0\|_\infty
\le10^{-12}+\frac{13887}{10^6}10^{-8}<10^{-8},
\tag{15.12}
$$

and $T$ has Lipschitz constant at most $13887/10^6<1$.  Banach's
fixed-point theorem gives a unique $x_*\in Q$ with $T(x_*)=x_*$.  It
follows that $RF(x_*)=0$.  Since $\|I-RDF(x_*)\|_\infty<1$, the product
$RDF(x_*)$ is invertible by the Neumann series; hence both $R$ and
$DF(x_*)$ are invertible, and therefore $F(x_*)=0$.  The remaining
intervals in (15.11) are the same rational interval evaluations used
in (15.7)--(15.8).  The centre $x_0$ is only a rational test point; it
is not asserted to solve $F=0$. ∎

**Theorem 15.5 (Strict interior continuation and failure of an
$M$-only source margin).**  For every $\eta>0$ there are two distinct
actual strict worlds $W_A,W_B$ with the same $(p,v)$, the same terminal
$m$, and $p\ne24$, such that

$$
0<1-r(W_A)<\eta.
\tag{15.13}
$$

Proof.  For a first source with $(r,b)=(s,t)$ define

$$
c_A(s,t)=\frac{s(1-s)}t,
\qquad
\Lambda_A(s,t)=1+\frac6{1+t}+\frac1{1+2t}
 -\frac4{t+c_A(s,t)}-\frac4{t+c_A(s,t)+s},
$$

and

$$
E(s,t)=-\frac{(24/5)(t-1/8)\,2(2+5t)/((1+t)(1+2t))}
              {\Lambda_A(s,t)}.
\tag{15.14}
$$

This is defined in a neighbourhood of $(1,t_*)$ by (15.11), where
$t_*$ is the first coordinate of $x_*$.  Let $X_i^A(s,t)$ be the
original responses (10.5) evaluated at $(r,b,e)=(s,t,E(s,t))$, and set

$$
\mathcal F(s,t,b,r,e)=
\begin{pmatrix}
H(r,b,e)\\
X_0(r,b,e)-X_0^A(s,t)\\
X_1(r,b,e)-X_1^A(s,t)\\
X_3(r,b,e)-X_3^A(s,t)
\end{pmatrix}.
\tag{15.15}
$$

At $s=1$, the first source is the C1 boundary extension, so
$\mathcal F(1,x_*)=F(x_*)=0$.  Differentiating the exact rational
formulas (15.3) shows that the derivative of $\mathcal F$ in
$(t,b,r,e)$ at $(1,x_*)$ is $DF(x_*)$, which is invertible by
Proposition 15.4.  The analytic implicit function theorem therefore
gives functions $t(s),b(s),r(s),e(s)$ for $s$ near $1$ satisfying
$\mathcal F=0$.

Shrink the interval so that $0.98<s<1$, $0.92<r(s)<0.94$, both $b$
coordinates are positive, both $\Lambda$ values are nonzero, both
$e$ values are positive, and the common $p(s)$ is larger than $56$.
The first source has

$$
P_A(s)=\begin{pmatrix}s&t(s)\\s(1-s)/t(s)&1-s\end{pmatrix},
$$

and the second has

$$
P_B(s)=\begin{pmatrix}r(s)&b(s)\\r(s)(1-r(s))/b(s)&1-r(s)\end{pmatrix}.
$$

Both satisfy the undivided parent equation, so Lemma 10.2 reconstructs
one entire degree-at-most-three gain and one fixed drift for each.  The
positive $e$ values imply $g(0)=-24-e<0$, so neither gain is the zero
polynomial.  The equations in (15.15) give

$$
W_A(s),W_B(s)\in C(p(s),v(s)),\qquad m(W_A(s))=m(W_B(s)).
\tag{15.16}
$$

They use the original clocks and readings; $s$ is a parameter selecting
different worlds, not a new clock, reset, reclocking, or added port.
The worlds are distinct because their $r$ coordinates lie in the
disjoint intervals $(0.98,1)$ and $(0.92,0.94)$.  Given $\eta>0$, choose
$s$ also with $s>1-\eta$; then (15.13) follows. ∎

**Corollary 15.6 (Scope of the margin failure).**  No positive lower
bound for $1-r$ can follow from the $M$-pair hypotheses alone, even
with the original strict source guards and $p\ne24$.  The conclusion
does not assert that an additional selected $J$ pair exists on the
family (15.16), nor does it remove the shared $(p,v)$ and entire-child
requirements of (1.6).  Singular--regular possibilities, unused
singular companions, and the original joint $J/M$ question remain
separate obligations.

The contraction argument uses the classical Banach fixed-point theorem;
the continuation uses the analytic implicit function theorem, in the
same ordinary sense as the implicit/inverse-function use in Theorem
6.1.  The displayed source formulas, rational interval recurrence,
256-cell grid, and 16-entry matrix bound are the complete arithmetic
data for the two component conclusions.  They establish neither the
original joint witness nor a global joint exclusion.

## 追加锚（本行以下为增补区）

## 16. An actual strict $J$-pair arc

**Definition 16.1 (The strict parent and its rational response circuit).**
A world has one rank-one source

$$
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\qquad 0<r<1,\quad b>0,
$$

one fixed real drift $d$, and one entire nonzero real polynomial gain of
degree at most three.  Its original history is

$$
H_4=(0,J,24,M,147/5,J,24,M,18),
$$

with clocks $0,\ldots,7$ and acquired actions $J,M,J,M,M,M$.  Put

$$
\tau=r/b,\quad r=\tau b,\quad c=\tau(1-r),\quad
j=\tau+b(1-\tau^2),\quad n=j+r,\quad T=1+b,\quad U=1+2b.
$$

On the regular strict domain $\tau>0$, $b>0$, $\tau b<1$, $\Lambda\ne0$,
define

$$
\begin{aligned}
D&=5\bigl((b^2+8b+4)jn-2TU(j+n)\bigr),\\
A&=(8b-1)(2+5b),\\
C_0&=-24D+3Ajn,\\
C_1&=3An,\\
C_2&=3(49b+34)jn-54U(j+n),\\
C_3&=3Aj.
\end{aligned}
\tag{16.1}
$$

Then

$$
D=\frac52 TUjn\Lambda,
\qquad
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n.
\tag{16.2}
$$

Let

$$
L_i(s)=\prod_{0\le h\le3,\ h\ne i}\frac{s-h}{i-h},\qquad
 g(s)=\frac1D\sum_{i=0}^3 C_iL_i(s),\qquad d=-\frac{C_0}{D}.
\tag{16.3}
$$

The late gain values are

$$
\begin{pmatrix}B_5\\B_6\\B_7\end{pmatrix}
=\begin{pmatrix}-4&15&-20&10\\-10&36&-45&20\\-20&70&-84&35\end{pmatrix}
\begin{pmatrix}C_0\\C_1\\C_2\\C_3\end{pmatrix},
\tag{16.4}
$$

and the four actual response numerators are

$$
\begin{aligned}
N_p&=-C_0+(U+n)B_5,\quad
N_v=-C_0+(2U+n)B_6,\\
N_a&=-C_0+(T+2j+4r)B_7,\quad
N_m=-C_0+(3U+2n)B_7.
\end{aligned}
\tag{16.5}
$$

Thus $(p,v,a,m)=(N_p,N_v,N_a,N_m)/D$.  The first four gain values
in (16.3) give the original readings, and the fifth original reading is
$18$ exactly when the undivided parent equation of Definition 10.1 holds.  The two different original readings $0,24$ make the gain
nonzero.  No sign condition, nonzero sample, exact degree, simple-root
condition or drift condition is used.

**Definition 16.2 (The parameterized $J$-pair equations).**  For
$z=(\tau_H,b_H,\tau_L,b_L)$ let $p_H,v_H,a_H$ and
$p_L,v_L,a_L$ be the functions in (16.5), evaluated at the two
sources.  Define

$$
F(z,p)=
\begin{pmatrix}p_H-p\\p_L-p\\v_H-v_L\\a_H-a_L\end{pmatrix}.
\tag{16.6}
$$

For $10\le p\le34$, the following three polynomial centre maps are used.
Write $u=(2p-lo-hi)/(hi-lo)$ on each interval $[lo,hi]$ and evaluate
all displayed arrays by descending Horner evaluation; every coefficient
is divided by $10^{20}$.

$$
\begin{array}{c|c|l}
[lo,hi]&\text{coordinate}&\text{descending coefficients in }u\\ \hline
[10,20]&\tau_H&(140424816523,63061888678,4869392145790,9422220254092,16367777302301,630276181828344,-2569859053832832,5603034108518697,-37041257351967357,-1505934735965867648,12490031250788984569,228568262342139650098)\\
[10,20]&b_H&(74601904618,587008912224,1675974648672,11723020586798,59397097070359,150386442997205,1754747499208129,2385677598092312,28728120803558095,177713875178985043,-572693824085625149,31463174914130987601)\\
[10,20]&\tau_L&(-286517520774,-1458798946604,-4484619212987,-39378923335258,-95032360161001,-610511414047453,-3787735814587272,5327878585599447,-134291913516490829,725907457857128599,3554914500654767298,210788533712955551542)\\
[10,20]&b_L&(-21554952211,-167568989307,-719043316224,-5332188024970,-17244126711789,-76110792776341,-367687512419822,1518778661443952,1190131346284344,224217790257326402,4016662099446683744,4532053336144848092)\\
[20,30]&\tau_H&(-12315808697634,-35358573460527,-65168929859263,-187577008857516,-460805694809113,-653982348334417,239197229306581,5736610426433156,23437354454875396,58144898242609116,64422234909843396,-1593191583430201524,6146598888033105531,247283358291040373320)\\
[20,30]&b_H&(31099287400162,69087439877398,40389836240710,77075541049766,328726471334712,891748266951060,2645670584884721,8525243725658645,26871684563657704,79326856115586399,219589170335308014,662362580311566447,775133715320458502,31374675219118351686)\\
[20,30]&\tau_L&(-64760914995336,-141100470063114,-72520370219354,-145269729373691,-728244036456201,-2245702071706101,-7245822024720854,-23692327394115831,-73163432013250704,-197029754390717363,-528694944588356620,-584207156211347097,4492542348396760978,219625886685223990790)\\
[20,30]&b_L&(-1723603413335,-1880359411512,11905805971444,49433821136737,124147171707093,215207360044166,34937022519674,-1562471228161450,-7777580962203138,-22939857428839428,-39711075675135058,193301006165304340,4916488201945917316,13475282226511291486)\\
[30,34]&\tau_H&(-21186663398999,-37057132404672,40914447971722,70812107865864,-102330353651627,-180455567571802,-54805934140941,-105864219093171,-394844458459518,-736655406452101,-1304441637475744,-2492151173517882,-4891924901081503,-10042303762139665,-21030669569619674,-35167113554906297,-3648330232535577,-44722576554474052,1258092097632112164,253307428524817270116)\\
[30,34]&b_H&(29347534034381,51408606320622,-56384971999957,-97659234722679,142366377572888,251662178340788,80218110788675,156111574767403,567921626910113,1068911804392284,1928435193097555,3783054087737079,7627327934817957,15666933368157246,33309862423430195,77919118377939274,220731512868169448,756584067725632219,2373045543506880306,34932590811935921854)\\
[30,34]&\tau_L&(-55541680313275,-97404534628203,106298090982829,184220076471718,-270290783930968,-478620521827863,-157686308174145,-308182157741107,-1102948577953311,-2087793427689654,-3803786492746523,-7536086716159247,-15362660199585885,-32003595231890594,-70148176855102684,-175690543223014516,-538164996818189229,-1728970444713086177,-2173832085911805516,221845194568232864125)\\
[30,34]&b_L&(450135834043,791432409571,-853929166848,-1481671306073,2207327774598,3924165644115,1387884608488,2738482983299,9556425419917,18621330504658,34279898879426,63331218908555,127163137096159,401052794968752,1494889997020038,2689161815711592,-12134528603054534,-66100473199783546,1928352859377411297,20494322221751046893).
\end{array}
\tag{16.7}
$$

The coefficients in the three blocks are rational centres; they are not
asserted to be exact points of the zero set.

**Lemma 16.3 (A complete interval continuation).**  Put
$h=10^{-40}$ and $\rho=1/100000$.  In every block of (16.7), for
$k=0,\ldots,1023$, let

$$
I_k=[-1+2k/1024,-1+2(k+1)/1024],\quad
u_k=-1+(2k+1)/1024,\quad w=1/1024.
$$

Write $p(u)=(lo+hi)/2+(hi-lo)u/2$ and
$z_c=\widehat z(u_k)$, where $z_c$ is an exact rational vector.  Let
$Z=\widehat z(I_k)+[-2\rho,2\rho]^4$.  Interval evaluation encloses
these exact rational quantities; rounding a centre does not redefine it.
For a rational endpoint $x$, set

$$
\operatorname{rd}_-(x)=h\lfloor x/h\rfloor,\qquad
\operatorname{rd}_+(x)=h\lceil x/h\rceil.
$$

An interval $[a,b]$ is enclosed by
$[\operatorname{rd}_-(a),\operatorname{rd}_+(b)]$.  For addition,
subtraction and multiplication, first use the exact endpoint formulas

$$
\begin{aligned}
[a,b]+[c,d]&=[a+c,b+d],\\
[a,b]-[c,d]&=[a-d,b-c],\\
[a,b][c,d]&=[\min(ac,ad,bc,bd),\max(ac,ad,bc,bd)],
\end{aligned}
$$

and then round outwards.  If $0\notin[a,b]$, its reciprocal is the
outward enclosure of $[1/b,1/a]$.  Division means multiplication by
that rounded reciprocal.  Each rational input is enclosed
before its first use.  Matrix products and sums use increasing indices;
each scalar product is rounded before the next addition.

Expand $D,N_p,N_v,N_a,N_m$ from (16.1)–(16.5) as exact integer
polynomials.  Their coefficient arrays are given below.  An array has
rows indexed by $i=0,\ldots,6$ and columns by $j=0,\ldots,4$, both
in increasing order, and represents $\sum_{i,j}a_{ij}\tau^ib^j$.
All zero entries are retained.

$$
D : \begin{pmatrix}
0&-20&-40&0&5\\
-20&-30&30&30&5\\
20&80&65&-35&-10\\
0&-40&-100&-50&-5\\
0&0&20&40&5\\
0&0&0&0&0\\
0&0&0&0&0
\end{pmatrix}.
$$

$$
N_p : \begin{pmatrix}
0&-390&-1395&-2238&-216\\
-390&-1125&-1917&1437&1872\\
480&1500&4224&4869&-1368\\
-96&-384&-270&-5511&-3648\\
0&288&-1440&-2376&2232\\
0&0&-288&2112&1536\\
0&0&0&96&-768
\end{pmatrix}.
$$

$$
N_v : \begin{pmatrix}
0&-1032&-7458&-13293&-1125\\
-1032&-7320&-11472&9750&10650\\
750&6891&26640&25266&-9750\\
270&1695&-5574&-33168&-17880\\
0&-810&-8295&-5595&13050\\
0&0&810&8505&5310\\
0&0&0&-270&-2655
\end{pmatrix}.
$$

$$
N_a : \begin{pmatrix}
0&-1638&-10467&-18558&-1224\\
-1638&-12069&-28845&-7779&13344\\
-678&-1923&25848&64293&3432\\
2304&20652&44520&-22815&-51696\\
0&-6912&-51654&-78111&5376\\
0&0&6912&44064&37152\\
0&0&0&-2304&-12384
\end{pmatrix}.
$$

$$
N_m : \begin{pmatrix}
0&-3954&-28335&-49569&-3264\\
-3954&-29001&-46548&33873&39120\\
1626&23157&101658&100284&-35472\\
2304&13740&-11076&-125037&-71088\\
0&-6912&-44742&-32895&48720\\
0&0&6912&41760&24768\\
0&0&0&-2304&-12384
\end{pmatrix}.
$$

Evaluation starts at zero and uses descending Horner in $b$ inside
descending Horner in $\tau$, including every padded zero entry.
Differentiate the monomials before evaluating; pad every derivative
array to the same $(6,4)$ bidegree.  Centre maps and their first two
$u$ derivatives use descending Horner starting at zero, with their
exact differentiated coefficients divided by $10^{20}$.
For any numerator $N$ and denominator $D$, use

$$
\begin{aligned}
R&=N/D,\\
R_i&=N_i/D-ND_i/D^2,\\
R_{ij}&=N_{ij}/D-(N_iD_j+N_jD_i+ND_{ij})/D^2
                 +2ND_iD_j/D^3.
\end{aligned}
\tag{16.8}
$$

Here $i,j$ range over $\tau,b$.  Compute $V=D^{-1}$ once, then
$V_2=VV$ and $V_3=V_2V$.  The evaluation order in (16.8) is
$NV$, $N_iV-(ND_i)V_2$, and

$$
\bigl(N_{ij}V-((N_iD_j+N_jD_i)+ND_{ij})V_2\bigr)
       +(((2N)D_i)D_j)V_3.
$$

Every indicated product and addition is a separate outward operation.
Evaluate the Hessian entries in the order $\tau\tau,\tau b,bb$ and
copy the $\tau b$ enclosure into the $b\tau$ entry by symmetry.
The formulas also apply to linear combinations of responses after their
numerator coefficients are combined.  For row $i$ of $\mathcal C$, form
coefficient by coefficient, starting from zero and adding in the stated
order,

$$
\begin{aligned}
N_{iH}&=\mathcal C_{i0}N_p+\mathcal C_{i2}N_v+\mathcal C_{i3}N_a,\\
N_{iL}&=\mathcal C_{i1}N_p+(-\mathcal C_{i2})N_v+(-\mathcal C_{i3})N_a.
\end{aligned}
$$

Differentiate these interval coefficient arrays by the exact monomial
integer factors and apply (16.8) on the respective source tube.  This
gives the two $2\times2$ diagonal blocks of $\mathcal H_i$.  Entries
mixing the two sources are exactly zero.  The Hessian is therefore
formed from combined numerators, rather than separately enclosed
response Hessians.

Let $J_c=D_zF(z_c,p(u_k))$.  Apply interval Gauss–Jordan elimination
to $[J_c\mid I_4]$, enclosing all singleton rational inputs.  At column
$i$ scan rows $i,\ldots,3$ and choose the first whose pivot interval
excludes zero,
swap it into row $i$, and save that pivot interval.  Multiply all eight
entries of row $i$, in increasing column order, by its one computed
reciprocal.  For each other row $r$ in increasing order, save its
column-$i$ entry $a_{ri}$, then replace all eight entries by
$a_{rj}-a_{ri}a_{ij}$ in increasing $j$ order.  No entry is reset to an
exact zero or one after these operations.  Denote the resulting right
block, an interval enclosure of the exact inverse $C=J_c^{-1}$, by
$\mathcal C$.  The absolute pivot bound refers to the saved interval
before row normalization.  All four pivots in every cell exclude zero.
Set

$$
\begin{aligned}
\mathcal E&=I-\mathcal C J_c,\\
\mathcal H_{ijl}&\supset (C D_z^2F)_{ijl}(Z),\qquad
\delta_l=\sup_{z\in Z}|z_l-z_{c,l}|,\\
B_{ij}&=\sum_l\sup|\mathcal H_{ijl}|\,\delta_l,\\
q&=\max_i\sum_j(\sup|\mathcal E_{ij}|+B_{ij}).
\end{aligned}
\tag{16.9}
$$

Every product defining $B$ is rounded upwards separately.  Thus
$CD_zF(Z)$ is enclosed entrywise by its centre enclosure plus
$[-B_{ij},B_{ij}]$.  Define $\beta=(1,1,0,0)^{\mathsf T}$ and
$f(u)=CF(\widehat z(u),p(u))$, keeping $C$ constant in a cell.  Then

$$
\begin{aligned}
f'&=CD_zF\widehat z'-C\beta(hi-lo)/2,\\
f''&=CD_z^2F[\widehat z',\widehat z']+CD_zF\widehat z'',\\
\eta&=\max_i\left(\sup|f_i(u_k)|+w\sup|f_i'(u_k)|
                         +\frac{w^2}{2}\sup_{I_k}|f_i''|\right).
\end{aligned}
\tag{16.10}
$$

For completeness, all indices in the finite arithmetic prescription
start at zero.  Form $\mathcal J_c$ by the quotient gradients in
(16.8) on the enclosed exact centre, then $A_c=\mathcal C\mathcal J_c$
and $\mathcal E=I-A_c$.  Thus the symbol $J_c$ in an interval product
means this enclosure of the exact centre Jacobian.  Evaluate
$\delta_l=\sup|Z_l-[z_{c,l}]|$ with the enclosed exact centre, and use
upward scalar products and increasing-index sums for $B$ and $q$.
Here $[z_c]$ encloses $z_c$; it does not change that exact rational
centre.

Evaluate $p_H,p_L,v_H,v_L,a_H,a_L$ separately, form
$F(z_c,p(u_k))$, then multiply that vector by $\mathcal C$.  Evaluate $p(u_k)$ as
$(lo+hi)/2+((hi-lo)/2)u_k$.  Compute $f'(u_k)$ as
$A_c[\widehat z'(u_k)]-(\mathcal C_{i0}+\mathcal C_{i1})(hi-lo)/2$
in row $i$.  For $f''$, use the interval vector whose row $i$ is

$$
\sum_{j=0}^3\sum_{l=0}^3
   (\mathcal H_{ijl}[\widehat z'_j(I_k)])[\widehat z'_l(I_k)]
+\sum_{j=0}^3(A_{c,ij}+[-B_{ij},B_{ij}])[\widehat z''_j(I_k)].
$$

Each sum starts at zero; the double sum uses increasing $j$, then
increasing $l$, including its zero entries.  Add the two sums before
taking the absolute supremum.  In (16.10), form $w^2/2$ by the
outward operations $(ww)/[2,2]$, multiply absolute suprema upwards,
then add the three terms from left to right and maximize over rows.
For source hulls evaluate $r=\tau b$, $j=\tau+b(1-\tau\tau)$,
$n=j+r$, $T=1+b$, $U=1+2b$, and
$\Lambda=((1+6/T)+1/U)-4/j-4/n$ in that order on $Z$.
Every denominator used in (16.8) excludes zero on $Z$.
The following tables give rational bounds over each complete block of
1024 cells; all columns are upper bounds except those explicitly marked
as lower bounds.  The Hessian column bounds the largest absolute
component of $\mathcal H$, rather than its row sum.

| Parameter interval | $q$ | $\eta$ | Lower bound for $\rho-\eta-q\rho$ using the two uniform upper bounds |
| --- | --- | --- | --- |
| $[10,20]$ | $2/5$ | $19/10^7$ | $41/10^7$ |
| $[20,30]$ | $17/100$ | $41/10^8$ | $789/10^8$ |
| $[30,34]$ | $3/100$ | $2/10^7$ | $95/10^7$ |

| Parameter interval | Minimum cell margin, lower bound | Absolute pivot, lower bound | $|D|$ on both tubes, lower bound |
| --- | --- | --- | --- |
| $[10,20]$ | $41/10^7$ | $3/4$ | $2$ |
| $[20,30]$ | $789/10^8$ | $1/10^4$ | $4$ |
| $[30,34]$ | $95/10^7$ | $3/20$ | $11$ |

| Parameter interval | Hessian component | $\|\mathcal E\|_\infty$ | $\|B\|_\infty$ |
| --- | --- | --- | --- |
| $[10,20]$ | $8300$ | $1/10^{20}$ | $2/5$ |
| $[20,30]$ | $3800$ | $1/10^{20}$ | $17/100$ |
| $[30,34]$ | $500$ | $1/10^{20}$ | $3/100$ |

| Parameter interval | $\max_i\sup|f_i(u_k)|$ | $\max_i\sup|f_i'(u_k)|$ | $\max_i\sup|f_i''(I_k)|$ |
| --- | --- | --- | --- |
| $[10,20]$ | $3/10^{13}$ | $4/10^{11}$ | $197/50$ |
| $[20,30]$ | $7/10^{11}$ | $12/10^9$ | $17/20$ |
| $[30,34]$ | $2/10^{12}$ | $6/10^{10}$ | $41/100$ |

In particular the complete 3072-cell cover satisfies

$$
\begin{array}{c|c|c|c}
[10,20]&q<2/5&\eta<19/10^7&\rho-\eta-q\rho>41/10^7\\
[20,30]&q<17/100&\eta<41/10^8&\rho-\eta-q\rho>789/10^8\\
[30,34]&q<3/100&\eta<2/10^7&\rho-\eta-q\rho>95/10^7.
\end{array}
\tag{16.11}
$$

There are four nonzero pivots, two strict-source tubes and eight
two-variable Hessian blocks per cell.  Their unions have the
following rational source hulls; every table endpoint is divided by
$10^6$.

| Source quantity | Lower endpoint numerator | Upper endpoint numerator |
| --- | --- | --- |
| $r_H$ | $690674$ | $977760$ |
| $b_H$ | $310884$ | $384274$ |
| $\Lambda_H$ | $-5995235$ | $-294406$ |
| $r_L$ | $15353$ | $485283$ |
| $b_L$ | $7377$ | $223515$ |
| $\Lambda_L$ | $1421047$ | $4066100$ |

Thus throughout all radius-$2\rho$ tubes

$$
\begin{gathered}
69/100<r_H<98/100,\quad31/100<b_H<39/100,\\
15/1000<r_L<49/100,\quad7/1000<b_L<23/100,\\
-6<\Lambda_H<-29/100,\qquad 7/5<\Lambda_L<41/10.
\end{gathered}
\tag{16.12}
$$

The coordinate distances between the centre maps at the two seams,
in the order $(\tau_H,b_H,\tau_L,b_L)$, are

$$
\begin{aligned}
p=20:\quad&10^{-20}(431075459,1151569031,2419160976,66604473),\\
p=30:\quad&10^{-20}(1317470467,2902458603,6085312313,77463103).
\end{aligned}
\tag{16.13}
$$

Their infinity norms are less than $3/10^{11}$ and $7/10^{11}$,
respectively.  The seed identification uses the entire source box of O,
Theorem 18.2, not just its midpoint.  Put

$$
\begin{gathered}
\mathcal P=[2744214237/10^8,2744214238/10^8],\\
m_O=10^{-18}(798291691626185419,319422724668808667,
352720293321024633,159165804512783260),\\
\mathcal B_O=m_O+[-10^{-9},10^{-9}]^4,\\
\Psi(r_A,b_A,r_B,b_B)=(r_A/b_A,b_A,r_B/b_B,b_B).
\end{gathered}
$$

Positive denominator interval division on this whole box gives

$$
\sup_{p\in\mathcal P,\ x\in\mathcal B_O}
\|\Psi(x)-\widehat z_{[20,30]}((p-25)/5)\|_\infty
\le\frac{40562666853139892256554027043419}
 {2000000000000000000000000000000000000000}
<\frac{203}{10^{10}}<\rho.
\tag{16.14}
$$

*Proof.* The interval formulas (16.8)–(16.10), with the coefficient
lists (16.7), give the tabulated rational inequalities over all cells.
No information about an unknown zero enters these inclusions.  For each
$p=p(u)$, Taylor's theorem gives $\|CF(\widehat z(u),p)\|_\infty\le\eta$.
The convex ball of radius $2\rho$ about $\widehat z(u)$ is contained in
$Z$.  Equation (16.9) bounds the derivative of $z\mapsto z-CF(z,p)$
there by $q<1$.  On the closed ball of radius $\rho$ about
$\widehat z(u)$ the map has displacement at most $\eta+q\rho<\rho$.
The Banach fixed-point theorem gives a unique interior zero in that
ball.  Since $C$ is invertible, a fixed point is exactly a zero of $F$.
The same derivative bound gives uniqueness of a zero in the larger
radius-$2\rho$ ball, and the Neumann series for $CD_zF$ gives an
invertible Jacobian there.

The rational circuit is analytic on each strict tube, so the analytic
implicit function theorem gives a local analytic zero function.  The
continuous centre map and the larger uniqueness balls identify these
functions across adjacent cells.  At each parameter seam, the distances
(16.13) put each radius-$\rho$ root inside the other centre's
radius-$2\rho$ ball; uniqueness identifies the two roots and their
analytic germs.  Consequently there is one analytic map

$$
z_J:[10,34]\longrightarrow
\{(\tau_H,b_H,\tau_L,b_L):\tau_i,b_i>0,\ \tau_ib_i<1\},
\tag{16.15}
$$

where analyticity on the closed interval means analyticity in a
neighbourhood of every point, including each endpoint.  Its uniqueness
is asserted only in the certified pointwise balls.  At every
$p\in\mathcal P$, O, Theorem 18.2 gives the actual $A,B$ $J$ pair in
$\mathcal B_O$; (16.14) puts it in the middle block's uniqueness ball.
It is therefore this same arc.  Finally (16.12) gives disjoint source
$r$ intervals and nonzero $\Lambda$ values throughout. ∎

**Theorem 16.4 (Actual $J$-pair continuation).** For every
$10\le p\le34$, the two worlds represented by
$z_J(p)=(\tau_H,b_H,\tau_L,b_L)$ are distinct complete strict worlds in
one entire $C(p,v_J(p))$, where

$$
 v_J(p)=v_H(z_J(p))=v_L(z_J(p)),
\qquad a_H(z_J(p))=a_L(z_J(p)).
\tag{16.16}
$$

The omission of $p=24$ is only the original target restriction.  No
statement about other $J$ arcs or about the full strict real domain is
contained in this theorem.

*Proof.* Lemma 16.3 supplies the two strict zeros for every parameter in
the closed arc and identifies them across both seams.  Lemma 10.2 lifts
each zero to one complete parent world, and (16.12) separates the two
source matrices.  The four equations in (16.6) are exactly the equal
$p$, equal $v$, and equal clock-seven $J$ terminal response conditions. ∎

## 17. A fixed-ratio quartic and its zero-safe four-world bound

**Definition 17.1 (The fixed-ratio polynomial).** For $\tau>0$ and real
$p$, put $r=\tau b$ and define

$$
\mathsf S_p(r,b)=5b(p-24)N_4+6(8b-1)H(r,b),
$$

where $N_4,H$ are exactly the two polynomials of O, Definition 12.1,
(12.1)–(12.2); this polynomial $H(r,b)$ differs from the three-variable
ambient parent equation $H(r,b,e)$ of Definition 10.1. Direct substitution gives
$\mathsf S_p(\tau b,b)=b^3Q_p(\tau,b)$, where, in descending powers of
$b$, the five coefficients of $Q_p$ are

$$
\begin{aligned}
q_4={}&10p\tau^4-10p\tau^3-20p\tau^2+10p\tau+10p\\
 &+1536\tau^6-3072\tau^5-4464\tau^4+7296\tau^3+2736\tau^2-3744\tau+432,\\
q_3={}&80p\tau^4-100p\tau^3-70p\tau^2+60p\tau-192\tau^6-4224\tau^5+4752\tau^4\\
 &+11022\tau^3-9738\tau^2-2874\tau+4476,\\
q_2={}&40p\tau^4-200p\tau^3+130p\tau^2+60p\tau-80p+576\tau^5+2880\tau^4\\
 &+540\tau^3-8448\tau^2+3834\tau+2790,\\
q_1={}&-80p\tau^3+160p\tau^2-60p\tau-40p-576\tau^4+768\tau^3\\
 &-3000\tau^2+2250\tau+780,\\
q_0={}&40p\tau^2-40p\tau+192\tau^3-960\tau^2+780\tau.
\end{aligned}
\tag{17.1}
$$

On strict sources let

$$
\begin{gathered}
\kappa=\frac6T-\frac2U=\frac{2(2+5b)}{TU},\\
A_5=1+(U+n)\left(4-\frac{15}{j}+\frac{20}{T}-\frac{10}{n}\right),\\
K_5=\frac{96(b-1/8)(U+n)}T,\qquad X=bj,\quad N=bn.
\end{gathered}
\tag{17.2}
$$

The regular-circuit identity, as a polynomial identity also at $D=0$, is

$$
Q_p(\tau,b)=2(pD-N_p).
$$

The exact identity relating the quartic to the two parent/fifth equations is

$$
\Lambda(p-24-K_5)+\frac{24}{5}(b-1/8)\kappa A_5
=\frac{\mathsf S_p(r,b)}{5bTUXN}.
\tag{17.3}
$$

**Lemma 17.2 (Degree-preserving noncollapse).**  The polynomial
$Q_p(\tau,b)$ is nonzero for every real $p$ and every $\tau>0$.

*Proof.* At $\tau=1$, $q_0=12$. For $\tau\ne1$, the equation $q_0=0$
forces

$$
 p=\frac{-48\tau^2+240\tau-195}{10(\tau-1)}.
$$

After this substitution, the next two coefficients become

$$
q_1=-\frac{6\tau V(\tau)}{\tau-1},\qquad
q_2=\frac{3U_6(\tau)}{\tau-1},
$$

where

$$
\begin{aligned}
V(\tau)&=32\tau^4+224\tau^3-320\tau^2-147\tau+210,\\
U_6(\tau)&=128\tau^6+1408\tau^5-2848\tau^4-752\tau^3+3857\tau^2-1378\tau-410.
\end{aligned}
$$

The exact Bezout identity

$$
(-50\tau^3+47\tau^2+14\tau-48)U_6
+(-2\tau^5+6\tau^4+30\tau^3+45\tau^2+36\tau+2)V
=1+101R(\tau),
$$

has

$$
R=(-64,-640,2112,-754,-3320,3633,341,-2180,670,199)
$$

as its descending coefficient list.  For the exact integer certificate,
form the Sylvester matrix with four shifted coefficient rows of $U_6$
followed by six shifted coefficient rows of $V$, in descending powers.
The degree-preserving
$10\times10$ Sylvester determinant of degrees $6$ and $4$ is

$$
25954241625991256473600,
$$

and its independent reduction modulo $101$ is $5$, with leading
coefficients $27$ and $32$ modulo $101$.  Thus $V$ and $U_6$ have no
common complex root, so $q_0,q_1,q_2$ cannot vanish simultaneously. ∎

**Theorem 17.3 (Zero-safe lift and the fixed-$\tau$ bound).**  Let
$\tau>0$, $p\in\mathbb R$, and $0<b<1/\tau$.  A strict complete world
with this fixed ratio exists exactly when $Q_p(\tau,b)=0$, and then it is
unique at $(\tau,b)$.  Explicitly, with $\Lambda,A_5,\kappa,K_5$ from
(17.2), put

$$
 e=\frac{-\frac{24}{5}(b-1/8)\kappa\Lambda+A_5(p-24-K_5)}
          {\Lambda^2+A_5^2},\qquad d=24+e,
\tag{17.4}
$$

and interpolate the gain from

$$
\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right).
\tag{17.5}
$$

The denominator in (17.4) is positive on every strict source by O,
Lemma 12.2.  If $q=-(24/5)(b-1/8)\kappa$ and
$z=p-24-K_5$, the two equations are $e\Lambda=q$ and $eA_5=z$;
(17.3) is their compatibility equation.  The residuals of (17.4) in
these two equations are respectively

$$
\frac{A_5(\Lambda z-A_5q)}{\Lambda^2+A_5^2},\qquad
-\frac{\Lambda(\Lambda z-A_5q)}{\Lambda^2+A_5^2},
$$

so both directions hold, including $\Lambda=0$.  Since $b^3>0$ and
$Q_p(\tau,b)$ is nonzero, there are at most four legal roots $b$ for
fixed $(p,\tau)$.  Each root gives one complete world by (17.4)–(17.5),
and every strict world occurs in this way.  Therefore

$$
\#\{W:\tau(W)=\tau,\ p(W)=p\}\le4.
\tag{17.6}
$$

This is a fixed-ratio bound; it is not a bound on an entire child
$C(p,v)$, and it retains singular sources, zero drift, sampled gain
zeros, repeated gain roots, lower-degree gains, and all leading-coefficient
drops.

*Proof.* Equation (17.3) is the compatibility condition for the two
linear equations in $e$.  The positive denominator in (17.4) gives the
unique solution in both directions, including the case $\Lambda=0$.
Lemma 17.2 makes the quartic nonzero, so it has at most four real roots
in $b$; the strict inequality $b>0$ makes the factor $b^3$ harmless.
The interpolation in (17.5) and O, Theorem 2.1 give one and only one
whole gain and drift for each root, while every strict world satisfies
(17.3). ∎

## 18. Faithful independent-$M$ crossing interface

**Definition 18.1 (Regular five-variable interface on the $J$ arc).**
For $10\le p\le34$, $p\ne24$, let $z_J(p)$ and $v_J(p)$ be
(16.15)–(16.16).  A regular independent-$M$ crossing is a solution of

$$
\begin{gathered}
10\le p\le34,\quad p\ne24,\quad \tau_i>0,\quad b_i>0,
\quad \tau_i b_i<1,\quad D_i\ne0,\\
(\tau_2-\tau_3)^2+(b_2-b_3)^2>0,\\
p_2-p=0,\quad p_3-p=0,\\
v_2-v_J(p)=0,\quad v_3-v_J(p)=0,\quad m_2-m_3=0.
\end{gathered}
\tag{18.1}
$$

The variables are $(p,\tau_2,b_2,\tau_3,b_3)$ and each response is the
complete-world response (16.5).  The Jacobian, in this order, is

$$
\begin{pmatrix}
-1&p_{\tau}(2)&p_b(2)&0&0\\
-1&0&0&p_{\tau}(3)&p_b(3)\\
-v_J'&v_{\tau}(2)&v_b(2)&0&0\\
-v_J'&0&0&v_{\tau}(3)&v_b(3)\\
0&m_{\tau}(2)&m_b(2)&-m_{\tau}(3)&-m_b(3)
\end{pmatrix},
\tag{18.2}
$$

where

$$
 z_J'(p)=(D_zF(z_J(p),p))^{-1}(1,1,0,0)^{\mathsf T},\qquad
 v_J'=(v_{\tau}(H),v_b(H),0,0)z_J'.
\tag{18.3}
$$

Whenever an actual distinct $J$ pair is present in the same entire
off-$24$ child, S, Corollary 18.2 excludes a singular selected-$M$
endpoint.  Theorem 16.4 supplies exactly that actual $J$-pair hypothesis.
Consequently (18.1) is equivalent to the existence of any actual
independent $M$ pair in this entire child, with no regularity assumption
on unused companions.  The two pairs
may overlap or be disjoint, and their common terminal values are
independent.

**Definition 18.2 (Zero-safe seven-variable parent fallback).**  The
undivided parent interface uses

$$
(p,r_2,b_2,e_2,r_3,b_3,e_3),
$$

with $10\le p\le34$, $p\ne24$, $0<r_i<1$, $b_i>0$, and

$$
 e_i\Lambda_i+\frac{24}{5}(b_i-1/8)\kappa_i=0.
\tag{18.4}
$$

For each triple $(r,b,e)$ let

$$
G=(-24-e,-e/j,(27/5-e)/T,-e/n)^{\mathsf T},
$$

and define

$$
X_0=24+e+(U+n)G_5,\quad
X_1=24+e+(2U+n)G_6,\quad
X_3=24+e+(3U+2n)G_7,
\tag{18.5}
$$

where $(G_5,G_6,G_7)^{\mathsf T}$ is the matrix in (16.4) applied to
$G$, and $e_2,e_3$ range over all real numbers.  The five matching
equations are

$$
X_0(2)-p=0,\quad X_0(3)-p=0,\quad
X_1(2)-v_J(p)=0,\quad X_1(3)-v_J(p)=0,\quad X_3(2)-X_3(3)=0.
\tag{18.6}
$$

The distinctness guard is

$$
(r_2-r_3)^2+(b_2-b_3)^2+(e_2-e_3)^2>0.
\tag{18.7}
$$

**Theorem 18.3 (Faithfulness of the two interfaces).**  For each point of the actual
$J$ arc with $p\ne24$, the regular system (18.1) is equivalent to the
existence of an independent distinct equal-$M$ pair in the entire child.
The undivided system (18.4)–(18.7) represents the same relation directly
without eliminating $\Lambda=0$; it also gives the parent response
interface for arbitrary strict endpoints.  The undivided reconstruction uses
only the positive denominators $b,j,n,T,U$; it divides by neither
$\Lambda$, $e$, a drift, a gain sample, a gain coefficient nor a root
difference.  Thus the union of the regular system and the parent fallback
is equivalent to the original independent-$M$ pair relation on this
actual $J$ arc.  It asserts neither existence nor absence of a solution,
and it does not replace the full strict real target by the arc.

*Proof.*  Theorem 16.4 supplies the actual distinct $J$ pair and its
common $(p,v_J(p))$.  S, Corollary 18.2 then removes only the singular
selected-$M$ alternative, so every selected $M$ pair is regular and is represented by
(18.1).  O, Theorem 2.1 and Lemma 10.2 above identify each zero of
(18.4) with one complete world and (18.5) with its actual responses,
including all singular and zero-drift cases.  In the regular system,
$D_i\ne0$ is equivalent to $\Lambda_i\ne0$ by (16.2).  The map
$(\tau,b)\mapsto(r,b)=(\tau b,b)$ is injective, and O, Theorem 12.3
makes a complete world unique at fixed source and $p$; hence the
source-distinctness inequality loses no distinct selected endpoints.  The guards in (18.1) and
(18.7) are precisely within-pair distinctness and the original strict
source conditions.  The cross-pair labels and terminal common values
are unconstrained, which is the original fibre-product semantics. ∎

## 19. Mathematical dependencies and the full joint relation

**Definition 19.1 (The full independent-pair relation).**  On the whole
strict real domain of Definition 1.1, the joint relation is

$$
\begin{gathered}
\exists p,v\in\mathbb R,\quad p\ne24,\quad
W_{J0},W_{J1},W_{M0},W_{M1}\in C(p,v),\\
W_{J0}\ne W_{J1},\quad a(W_{J0})=a(W_{J1}),\\
W_{M0}\ne W_{M1},\quad m(W_{M0})=m(W_{M1}).
\end{gathered}
\tag{19.1}
$$

Here $C(p,v)$ is the entire acquired child.  The two pairs may overlap
or differ, their terminal common values are independent, and all unused
companions are retained.  There is no imposed sign of the gain, no
regularity restriction on every world, and no source or pair-distance
floor in (19.1).  Equation (18.1), equivalently (18.4)–(18.7), is exactly
the restriction of (19.1) to $v=v_J(p)$, $10\le p\le34$, $p\ne24$,
with the actual $J$ pair furnished by Theorem 16.4.  Neither existence
nor universal exclusion of (18.1) follows from that theorem or from the
fixed-$(p,\tau)$ bound (17.6).  Universal exclusion on this arc alone
would still leave every other possible $J$ base in (19.1).

**Proposition 19.2 (Suppliers and scope of the component conclusions).**
The parent reconstruction, original clocks, whole gain and fixed drift
are O, Definitions 1.1–1.3 and Theorem 2.1; its zero-safe source equation
and unique whole-world lift are O, Definition 12.1, Lemma 12.2 and
Theorem 12.3.  The seed identified by (16.14) is the $A,B$ pair of O,
Theorem 18.2 and box (18.7), over its whole interval (18.1).  Entire-child
and independent-pair semantics are F, Sections 30–33, in particular
Theorem 32.1 and Definition 33.1.  The selected-$M$ singular exclusion
used in Theorem 18.3 is S, Theorem 18.1 and Corollary 18.2.  Definition
10.1 and Lemma 10.2 above supply the ambient undivided response
extension.  The actual $M$-pair family of SII, Proposition 4.1 and
Theorem 9.3 has its own hypotheses; it is not an $M$ pair on the arc
(16.15) merely because both are pair families.

*Proof.* The parameter and response correspondence is (16.1)–(16.6);
its traces are the original products of O, Definition 1.3.  The
compatibility identity (17.3) is O, (12.8), with $r=\tau b$.
The whole-box conversion (16.14) and uniqueness in Lemma 16.3 identify
the inherited seed.  The selected-$M$ exclusion uses the actual $J$
pair of Theorem 16.4 and precisely the quantifiers of S, Corollary 18.2,
without removing any unused companion.  Thus the component extensions
are the continuation from O's seed interval to $[10,34]$ and the
all-real-$p$, fixed-positive-$\tau$ quartic noncollapse and bound;
(18.1) gives their independent-$M$ consumer.  Cubic interpolation,
Banach contraction, the analytic implicit function theorem and the
Sylvester resultant are the classical mathematical inputs used in the
displayed proofs.  The full joint relation (19.1) is outside their
conclusions. ∎

## 追加锚（本行以下为增补区）

## 20. Whole-world coordinates and the reused bounded-output interface

**Definition 20.1 (Ambient parent and parameter correspondence).**
Let $\mathcal H$ be the complete strict parent of Definition 1.1,
including $p=24$. Its coordinates are $b>0$, $0<r<1$ and
$e=d-24$, subject to the parent equation below. Each world has one
fixed real drift and one nonzero entire real polynomial gain of degree
at most three. Set

$$
\begin{gathered}
c=\frac{r(1-r)}b,\quad j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\\
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad
q=-\frac{6(8b-1)(5b+2)}{5TU},\qquad e\Lambda=q.
\end{gathered}
\tag{20.1}
$$

The symbol $q$ here is the parent right-hand side $\eta$ in (1.7),
not the contraction bound in Lemma 16.3. Write $h_i=g(i)$ for
$i=0,1,2,3$. The whole gain is the fixed-node interpolant of

$$
(h_0,h_1,h_2,h_3)
=\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right).
\tag{20.2}
$$

Apply the three rows of (16.4) to this sample vector to obtain
$G_5=g(5),G_6=g(6),G_7=g(7)$. Thus

$$
\begin{aligned}
p&=24+e+(U+n)G_5,&v&=24+e+(2U+n)G_6,\\
a&=24+e+(T+2j+4r)G_7,&m&=24+e+(3U+2n)G_7.
\end{aligned}
\tag{20.3}
$$

The identity $Tg(2)-g(0)=147/5$ excludes a zero limiting gain whenever
these samples have an interior source limit. The topology on complete
worlds uses $(r,b,c,d)$ and the four padded coefficients of $g$.
Padding retains every degree drop. The continuous reconstruction (20.2)
identifies this topology with the parent topology in $(b,r,e)$.

For the zero-safe fixed-$p$ lift define

$$
\begin{gathered}
A_5=1+(U+n)\left(4-\frac{15}j+\frac{20}T-\frac{10}n\right),\qquad
K_5=\frac{96(b-1/8)(U+n)}T,\\
p-24-K_5=eA_5,\qquad
 e=\frac{q\Lambda+A_5(p-24-K_5)}{\Lambda^2+A_5^2}.
\end{gathered}
\tag{20.4}
$$

O, Lemma 12.2 proves $\Lambda^2+A_5^2>0$ on every strict source;
O, Theorem 12.3 supplies this unique lift, including $\Lambda=0$.
Here O's $\epsilon$ is $e$, and the regular circuit coordinate in
Section 16 is $t=\tau=r/b$. Its $D,N_p,N_v,N_a,N_m$ give precisely
(20.3). No drift, gain sample, leading coefficient or root difference
is divided out.

The following supplier map fixes the scopes used below. These are
existing source results, rather than additional boundary classifications.

| Owner | Interface and correspondence |
| --- | --- |
| O, Definitions 1.1–1.3 and Theorem 2.1 | Original clocks $0,\ldots,7$, left products, full parent (20.1), one whole gain (20.2), fixed drift and responses (20.3). |
| O, Lemma 12.2 and Theorem 12.3 | The strictly positive denominator in (20.4), and the unique fixed-$p$ whole-world lift on all strict source strata. |
| F, Definitions 30.1 and 33.1 | The entire actual child and independently selected within-pair-distinct $J,M$ pairs; no restriction on cross-pair overlap or equality of their terminal common values. |
| S, Definition 7.1 | Uniform $b\to\infty$ response limit $(-216/5,-225,-1224/5,-3264/5)$. Its local variables $(t,w)=(1/b,r/b)$ differ from the $t=r/b$ used in Section 22 below. |
| S, Theorem 12.1 | Bounded $b,p$ bound $c,d$, all padded gain coefficients and $v,a,m$, including $p=24$ and every singular or lower-degree case. |
| S, Definition 12.2, Theorem 12.3 and Proposition 12.4; SII, Definition 12.1, Lemma 12.2 and Lemma 14.2 | Four finite boundary fractions, both corners, pole exclusions and finite exhaustion including the ambient line $p=24$. |
| Lemma 16.3 and Theorem 16.4 | The analytic actual $J$ arc on $[10,34]$, its exact centres (16.7), radius-$\rho$ enclosure and positive $\Lambda_L$ guard on the larger tubes. |
| SII, Theorem 29.1 | One positive off-$24$ exclusion width for actual $M$ pairs, uniform in every real $v$. |
| Theorem 13.1 and Corollary 13.2; S, Corollary 18.2 | Singular coalescence exclusion and, in the presence of the actual $J$ pair, regularity of distinct selected $M$ endpoints. Unused singular companions are retained. |

**Lemma 20.2 (Bounded-$p$ extraction before a finite output limit).**
Every sequence $W_i\in\mathcal H$ with $10\le p(W_i)\le34$ has
bounded $b,c,d$, all four padded gain coefficients and all four late
responses. If a subsequential source limit is nonstrict, its finite
response limit is one of the four face fractions or their two corner
extensions in SII, Definition 12.1 and Lemma 12.2. This statement
retains a limiting $p=24$ and assumes no bound on $v$.

*Proof.* If $b$ is unbounded, take a subsequence with $b\to\infty$.
The uniform limit in S, Definition 7.1 gives $p\to-216/5$, contradicting
$p\ge10$. Uniformity is essential: with $(s,w)=(1/b,r/b)$ one has
$0<w<s$, and the rational response extension is analytic near $(0,0)$
with all scaled denominators nonzero there. Thus the same limit applies
even while $r$ varies through its whole strict interval.

Consequently some finite $L$ bounds $b$ along the sequence. Apply S,
Theorem 12.1 with that $L$ and $P=34$. It bounds $c,d$, all gain
coefficients and $v,a,m$ before taking any finite $(p,v)$ limit. In
particular an attempted $|v|\to\infty$ subsequence is impossible.
The coercivity theorem uses the undivided parent: if bounded $b$ were
accompanied by $j\to\infty$, then $b\to0$, $\Lambda\to8$,
$e\to3/10$, $G_5\to-24/5$ and $p\to-\infty$. Interior drift escape
is excluded by (20.4); the finite faces and corners are covered by that
theorem's pole and sample bounds. It makes no regular-source assumption.

The resulting bounded complete tuple has a convergent subsequence.
If its source is nonstrict, SII, Lemma 14.2 applies and gives exactly
the four nonpole faces or the two corners, with their finite full-world
response limits. Its statement includes $p\to24$, unlike an assertion
restricted to the relative off-$24$ target. The pole exclusions and
corner extensions are the existing ones in S, Theorem 12.1 and
Definition 12.2. Hence no unbounded-$v$ branch has been omitted before
boundary extraction. ∎

## 21. An explicit affine barrier on the finite source boundary

**Definition 21.1 (Barrier and inherited face polynomials).** Put

$$
\ell(p)=\frac{37p+421}{10},\qquad
f_0(x)=x^3-8x-4,\qquad f_1(x)=x^3-4x-2.
\tag{21.1}
$$

For the existing faces use the names $R_0=C_0$, $R_1=C_1$,
$E_0=B_0$, $E_1=B_1$ of SII, Definition 12.1. The parameter $x>0$
is the surviving offdiagonal: $(r,b,c)$ tends respectively to
$(0,x,0),(1,x,0),(0,0,x),(1,0,x)$. The following are the $p,v$
fractions of SII, Lemma 12.2, rewritten as $p=P/\delta$, $v=V/\delta$.
Arrays in this section are in descending powers of $x$.

| Face | $\delta(x)$ | Coefficients of $P$ | Coefficients of $V$ |
| --- | --- | --- | --- |
| $R_0$ | $5f_0$ | $(-216,-2238,-1395,-390)$ | $(-1125,-13293,-7458,-1032)$ |
| $R_1$ | $5(1+x)f_1$ | $(-216,-366,-1326,-1086,-180)$ | $(-1125,-2643,-7458,-5118,-798)$ |
| $E_0$ | $10(x-1)$ | $(-48,240,-195)$ | $(135,375,-516)$ |
| $E_1$ | $5(2x^2-1)$ | $(-48,144,12,-90)$ | $(135,645,-99,-399)$ |

Remove the zeros of each denominator. Extend to $x=0$ using the existing
corner values $(39/2,258/5)$ for $R_0,E_0$, and $(18,399/5)$ for
$R_1,E_1$. These are boundary outputs, not additional strict worlds.
The existing whole-world lifts, poles and both full corner vectors
remain those of S, Definition 12.2 and Theorem 12.3. Define the new
barrier numerator on each row by

$$
N=10V-37P-421\delta,\qquad
v-\ell(p)=\frac{N}{10\delta}.
\tag{21.2}
$$

Exact coefficient subtraction gives

$$
\begin{array}{c|l}
R_0&(-5363,-50124,-6125,12530)\\
R_1&(-5363,-14993,-17098,1632,2890)\\
E_0&(3126,-9340,6265)\\
E_1&(3126,-3088,-1434,1445).
\end{array}
\tag{21.3}
$$

**Theorem 21.2 (Strict finite-boundary output barrier).** Every finite
source-boundary output with $10\le p\le34$ satisfies

$$
v<\ell(p)-\frac1{25}.
\tag{21.4}
$$

This includes boundary outputs with $p=24$ and both corner extensions.
The boundary exhaustion and actual face lifts are reused; the assertion
here is the explicit inequality for their original fixed $(p,v)$ projection.

*Proof.* Use (21.2) on each existing face, with no cleared pole retained.
For $R_0$, $P<0$ on $x\ge0$, so $p\ge10$ forces $f_0<0$.
Multiplying $p\le34$ by this negative denominator gives

$$
Q_0(x)=386x^3+2238x^2+35x-290\le0.
$$

Since $Q_0'=1158x^2+4476x+35>0$ on $x\ge0$ and
$Q_0(7/20)=51819/4000>0$, one has $x<7/20$.
The first $N$ in (21.3) is strictly decreasing there, since
$N'=-16089x^2-100248x-6125<0$. Moreover

$$
N(7/20)=\frac{32128971}{8000}>4000,\qquad
50|f_0|=50(4+8x-x^3)<340<350.
$$

Thus $\ell-v=N/(50|f_0|)>4000/350>1/25$.

For $R_1$ the negative coefficients of $P$ likewise force $f_1<0$.
The condition $p\le34$ implies

$$
Q_1(x)=386x^4+536x^3+646x^2+66x-160\le0.
$$

Its derivative is positive for $x\ge0$, while
$Q_1(77/200)=185385713/800000000>0$. Hence $x<77/200$.
Here $N''=-64356x^2-89958x-34196<0$. Concavity bounds $N$ below
by the smaller endpoint value on $[0,77/200]$, and

$$
\begin{gathered}
N(0)=2890,\qquad
N(77/200)=\frac{16864707317}{1600000000}>10,\\
50(1+x)|f_1|<50\frac{277}{200}\frac{177}{50}
=\frac{49029}{200}<250.
\end{gathered}
$$

Therefore $\ell-v=N/(50(1+x)|f_1|)>10/250=1/25$.

For $E_0$ with $0\le x<1$, $N'=6252x-9340<0$ and $N(1)=51$.
Consequently $\ell-v=N/(100(1-x))>51/100$. If $x>1$, the condition
$p\ge10$ gives

$$
R(x)=48x^2-140x+95\le0.
$$

Since $R(2)=7$ and $R'>0$ for $x\ge2$, necessarily $x<2$.
The exact coefficient identity

$$
8N=521R+625-1780x
$$

gives $N<-1155/8$. Thus $\ell-v=-N/(100(x-1))>1155/800>1/25$.

For $E_1$, first suppose $x>1/\sqrt2$. Define

$$
R_*(x)=12x^3-11x^2-3x+10,\qquad
p-10=-\frac{4R_*}{5(2x^2-1)}.
$$

On $0\le x\le1$,
$R_*=10-8x+x(12x^2-11x+5)\ge2$: the quadratic is positive,
with discriminant $-119$. On $x\ge1$,
$R_*=(x-1)(12x^2+x-2)+8\ge8$. Hence this positive-denominator
branch has $p<10$ and contributes no point.

On the remaining branch $0\le x<1/\sqrt2$, the inequality $p\le34$
gives

$$
R_{34}(x)=12x^3+49x^2-3x-20\le0.
$$

Its derivative is positive for $x\ge5/8$, and
$R_{34}(5/8)=25/128>0$, so $x<5/8$.
The derivative $N'=9378x^2-6176x-1434$ is convex. Its endpoint
values on $[0,5/8]$ are $-1434$ and $-52183/32$, both negative;
therefore $N'<0$ throughout that interval. Finally

$$
N(5/8)=\frac{27055}{256}>100,\qquad
50(1-2x^2)\le50,
$$

and $\ell-v=N/(50(1-2x^2))>2>1/25$.
These estimates also hold at the allowed $x=0$ extensions. The infinity
response has $p=-216/5$ and lies outside the parameter window.
Lemma 20.2 and the cited finite exhaustion supply all other possible
source-boundary outputs, without an off-$24$ exception. ∎

## 22. A scalar certificate above the barrier on the actual J arc

**Definition 22.1 (Scalar polynomial and public coefficient data).**
Use $t=\tau=r/b$ and the circuit (16.1)–(16.5), without changing
any of its parameters. Thus

$$
\begin{gathered}
r=tb,\quad j=t+b(1-t^2),\quad n=j+r,\quad T=1+b,\quad U=1+2b,\\
D=5((b^2+8b+4)jn-2TU(j+n)),\quad A=(8b-1)(2+5b),\\
C_0=-24D+3Ajn,\quad C_1=3An,\\
C_2=3(49b+34)jn-54U(j+n),\quad C_3=3Aj,\\
B_6=-10C_0+36C_1-45C_2+20C_3,\qquad
N_v=-C_0+(2U+n)B_6.
\end{gathered}
\tag{22.1}
$$

Define

$$
\mathcal R(t,b,p)=10N_v-(37p+426)D=P_0(t,b)+pP_1(t,b),\qquad
P_0=10N_v-426D,\quad P_1=-37D.
\tag{22.2}
$$

The following integer matrices specify $P_0,P_1$ as
$\sum_{i=0}^6\sum_{j=0}^4 A_{ij}t^ib^j$; both indices increase
from zero. They follow by exact expansion of (22.1), or directly from
the $D,N_v$ arrays of Lemma 16.3:

$$
P_0:\begin{pmatrix}
0&-1800&-57540&-132930&-13380\\
-1800&-60420&-127500&84720&104370\\
-1020&34830&238710&267570&-93240\\
2700&33990&-13140&-310380&-176670\\
0&-8100&-91470&-72990&128370\\
0&0&8100&85050&53100\\
0&0&0&-2700&-26550
\end{pmatrix},\qquad
P_1:\begin{pmatrix}
0&740&1480&0&-185\\
740&1110&-1110&-1110&-185\\
-740&-2960&-2405&1295&370\\
0&1480&3700&1850&185\\
0&0&-740&-1480&-185\\
0&0&0&0&0\\
0&0&0&0&0
\end{pmatrix}.
\tag{22.3}
$$

Their exact bidegrees are $(6,4)$ and $(4,4)$. No centre coefficients
are changed: only the $\tau_L,b_L$ rows of (16.7), with denominator
$10^{20}$, enter this scalar certificate. Put $\rho=1/100000$.

**Lemma 22.2 (A reproducible 3072-cell scalar lower bound).** On the
radius-$\rho$ enclosures of the actual $L$ endpoint in Lemma 16.3,
$\mathcal R>0$ for every $10\le p\le34$. The following interval
recipe gives a complete finite certificate.

For each $(lo,hi)=(10,20),(20,30),(30,34)$ use exactly the 1024
closed cells

$$
\begin{gathered}
I_k=[-1+2k/1024,-1+2(k+1)/1024],\quad
u_k=-1+(2k+1)/1024,\quad 0\le k\le1023,\\
p(u)=\frac{lo+hi}2+\frac{hi-lo}2u,\qquad
p_c=p(u_k),\qquad P_k=p(I_k).
\end{gathered}
\tag{22.4}
$$

All interval endpoints are on the grid $h=10^{-30}$. For any rational
$x$ define $\operatorname{rd}_-(x)=h\lfloor x/h\rfloor$ and
$\operatorname{rd}_+(x)=h\lceil x/h\rceil$. Enclose every rational
input by these two endpoints. Addition and subtraction use exact
interval endpoints; they remain on the grid. For multiplication use
the minimum and maximum of the four endpoint products and round the
minimum down, the maximum up. Every multiplication is rounded before
the next addition. All zero coefficients are retained. No floating
point operation or division of intervals is used in this certificate.

Let $\widehat t,\widehat b$ be the two exact $L$ centre polynomials
from (16.7) for this block. Evaluate each by descending Horner from
zero, with the preceding operations. Write

$$
\begin{gathered}
C_t=\operatorname{Horner}(\widehat t,[u_k,u_k]),\qquad
C_b=\operatorname{Horner}(\widehat b,[u_k,u_k]),\\
X_t=\operatorname{Horner}(\widehat t,I_k)+[-\rho,\rho],\qquad
X_b=\operatorname{Horner}(\widehat b,I_k)+[-\rho,\rho].
\end{gathered}
\tag{22.5}
$$

The exact centre is $(\widehat t(u_k),\widehat b(u_k),p_c)$, not a
rounded midpoint of $C_t,C_b$. The intervals in (22.5) enclose it and
the whole actual $L$ endpoint over the cell, respectively.

Here is the polynomial evaluation order, including derivatives. For
any pair of integer coefficient matrices $(A^0,A^1)$ and parameter
interval $P$, form each coefficient interval as
$[A^0_{ij},A^0_{ij}]+P[A^1_{ij},A^1_{ij}]$, multiplying first and
then adding. Pad each matrix to $i=0,\ldots,6$, $j=0,\ldots,4$,
including after exact differentiation. In each row run Horner from
zero in $b$, visiting $j=4,3,2,1,0$. Run the outer Horner from zero
in $t$, visiting $i=6,5,4,3,2,1,0$. Thus $p$ is combined once into
the coefficients before either spatial Horner loop. Derivatives use
$\partial_t(t^ib^j)=it^{i-1}b^j$ and
$\partial_b(t^ib^j)=jt^ib^{j-1}$ before padding.

Evaluate $\mathcal R_c$ with matrices $(P_0,P_1)$, parameter
$[p_c,p_c]$ and spatial intervals $(C_t,C_b)$. Evaluate
$\mathcal R_t,\mathcal R_b$ with matrices
$(\partial_tP_0,\partial_tP_1)$ and
$(\partial_bP_0,\partial_bP_1)$, parameter $P_k$ and spatial
intervals $(X_t,X_b)$. Evaluate $\mathcal R_p=P_1$ by the same
padded rule with matrices $(P_1,0)$. Denote these three derivative
intervals by $H_t,H_b,H_p$.

For an interval $H=[a,b]$ put $|H|_{\max}=\max(|a|,|b|)$. Define
nonnegative grid numbers

$$
\begin{aligned}
\delta_t&=\max(\sup C_t-\inf X_t,\ \sup X_t-\inf C_t),\\
\delta_b&=\max(\sup C_b-\inf X_b,\ \sup X_b-\inf C_b),\\
\delta_p&=\max(p_c-\inf P_k,\ \sup P_k-p_c),\\
E_i&=\operatorname{rd}_+(|H_i|_{\max}\delta_i)
\quad (i=t,b,p),\\
L_k&=\inf\mathcal R_c-E_t-E_b-E_p.
\end{aligned}
\tag{22.6}
$$

The three error products are rounded up separately. The final
subtractions are exact grid subtractions in the displayed order.
The centre enclosures contribute to both $\inf\mathcal R_c$ and the
spatial displacement bounds; replacing them by rounded point centres
is not this recipe.

The exact results, with a common denominator $10^{30}$, are:

| $[lo,hi]$ | Completed cells | Nonpositive lower bounds | Numerator of $\min_k L_k$ | Minimizing $k$ |
| --- | --- | --- | --- | --- |
| $[10,20]$ | $1024$ | $0$ | $173903350897027038369423464062764$ | $1023$ |
| $[20,30]$ | $1024$ | $0$ | $52901519073726829319802022686438$ | $1023$ |
| $[30,34]$ | $1024$ | $0$ | $18553152424991317187833579224406$ | $1023$ |

All 3072 cells are included; there is no uncompleted cell.

*Proof.* Integer coefficient expansion gives (22.3). The interval rules
enclose exact rational arithmetic at every operation. Descending Horner
therefore encloses the exact centres and the polynomial images on each
box. For a point of $X_t\times X_b\times P_k$, the line segment from
the exact centre stays in this convex box. The integral mean-value
formula gives

$$
\mathcal R(t,b,p)\ge
\mathcal R(\widehat t(u_k),\widehat b(u_k),p_c)
-\sum_{i=t,b,p}\sup|\mathcal R_i|\delta_i\ge L_k.
\tag{22.7}
$$

Formula (22.6) bounds the displacement even when the centre enclosure
has nonzero width. Executing the finite endpoint operations (22.4)–(22.6)
with (16.7) and (22.3) gives the displayed positive integers. The cells
cover all three closed parameter intervals, including both seams.
Lemma 16.3 puts the actual $L$ endpoint in the corresponding box.
Hence $\mathcal R>0$ at every actual endpoint. This is the classical
interval mean-value bound applied to a scalar polynomial; the existence,
gluing and pointwise-ball uniqueness of the $J$ arc are reused from
Lemma 16.3, not inferred anew from this scalar test. ∎

**Theorem 22.3 (Strict output margin on the actual J arc).** The arc of
Theorem 16.4 satisfies, for every $p\in[10,34]$,

$$
v_J(p)>\ell(p)+\frac12.
\tag{22.8}
$$

*Proof.* Use the actual $L$ endpoint, so $v_J=N_v/D$. The strict
source guards give $T,U,j,n>0$. Lemma 16.3 gives
$\Lambda_L\ge1421047/10^6>0$ on its radius-$2\rho$ tubes, which
contain the actual radius-$\rho$ endpoint enclosures. By (16.2),
$D=(5/2)TUjn\Lambda_L>0$ at this endpoint. Lemma 22.2 and (22.2)
then imply

$$
v_J-\ell(p)-\frac12=\frac{\mathcal R(t_L,b_L,p)}{10D(t_L,b_L)}>0.
$$

Thus positivity of the denominator is an existing guard on this actual
endpoint, with its source and parameter hypotheses satisfied. It is
not a regularity condition imposed on every world in its child. ∎

## 23. Compactness of every complete companion above the arc

**Definition 23.1 (Closed output region and whole arc region).** In the
ambient parent $\mathcal H$, with $p=24$ retained, define

$$
\begin{aligned}
K_+&=\{W\in\mathcal H:10\le p(W)\le34,
\ v(W)\ge\ell(p(W))-1/25\},\\
K_J&=\{W\in\mathcal H:10\le p(W)\le34,
\ v(W)=v_J(p(W))\}.
\end{aligned}
\tag{23.1}
$$

At each $p\ne24$ the latter fibre is the entire actual
$C(p,v_J(p))$ of F, Definition 30.1. At $p=24$ it means the same
complete-world equations in $\mathcal H$, without importing an
off-$24$ restriction into this ambient definition. All companions,
including unused or singular ones, are included.

**Theorem 23.2 (Compactness in the original complete-world space).**
Both $K_+$ and $K_J$ are compact in $(b,r,e)$ and in the full
source/drift/padded-gain coordinates. No positivity of gains, full
gain degree, nonzero drift, all-world regularity or positive
within-pair separation is a hypothesis.

*Proof.* Take any sequence in $K_+$. Lemma 20.2 first bounds $b$,
then invokes bounded-$b,p$ coercivity to bound $c,d$, all gain
coefficients and $v,a,m$. In particular $v$ is bounded before a finite
boundary output is extracted. Pass to a convergent full tuple, and
write its output limit as $(p_*,v_*)$. The closed output inequalities
give

$$
10\le p_*\le34,\qquad v_*\ge\ell(p_*)-1/25.
\tag{23.2}
$$

An unbounded-$b$ subsequence has already been excluded by the uniform
infinity value $p=-216/5$. If the limiting source were nonstrict,
Lemma 20.2 and SII, Lemma 14.2 would identify its finite output with a
nonpole face or corner. Theorem 21.2 would give
$v_*<\ell(p_*)-1/25$, contradicting (23.2), including when $p_*=24$.
Thus the limiting source is strict.

The parent equation and original clock equations pass to this interior
limit by continuity. Equation (20.2) implies
$Tg(2)-g(0)=147/5$, which excludes an identically zero limiting gain.
The limit is therefore a complete world in $\mathcal H$, and (23.2)
puts it in $K_+$. This proves sequential compactness in the finite
source/drift/gain coordinates, hence compactness by the classical
finite-dimensional compactness criterion. The coordinate projection
to $(b,r,e)$ and reconstruction (20.2) give compactness there as well.
The zero-safe formula (20.4) also explicitly bounds drift on any of
the resulting compact interior source sets with bounded $p$.

By Theorem 22.3, $K_J\subset K_+$; the difference between the arc
threshold and the boundary threshold is
$1/2+1/25=27/50$. The analytic function $v_J$ is continuous on
$[10,34]$, so $W\mapsto v(W)-v_J(p(W))$ is continuous on $K_+$.
Its zero set is exactly $K_J$. Hence $K_J$ is a closed subset of a
compact set and is compact. This uses the entire fibre, not a bound
for only the selected $H,L$ worlds. ∎

**Corollary 23.3 (The precise role of the retained twenty-four fibre).**
Put $K_J^\times=K_J\cap\{p\ne24\}$. In the full complete-world
coordinate topology,

$$
\overline{K_J^\times}\subseteq K_J,
\tag{23.3}
$$

and the closure on the left is compact. For every closed parameter
interval $I\subset[10,34]$ with $24\notin I$, the entire region
$K_J(I)=K_J\cap p^{-1}(I)$ is compact. There are qualitative uniform
positive interior margins for $r,1-r,b,c$ on $K_J$, and finite bounds
for drift and all gain coefficients.

*Proof.* The compact set $K_J$ is closed in the finite-dimensional
ambient coordinate space, so it contains the closure in (23.3).
That closure and $K_J(I)$ are closed subsets of $K_J$. Each source
entry in the stated list is continuous and strictly positive on
$K_J$, so its minimum is positive; the remaining coordinate bounds
follow from compactness. These are qualitative extrema, without a
numerical value supplied by the proof. No assertion is made that
$K_J^\times$ itself is compact or that (23.3) is equality. Equality
would require approximability of every unused $p=24$ companion by
off-$24$ companions, which these arguments do not establish. ∎

## 24. Selected M limits and the remaining incidence obligation

**Proposition 24.1 (Reused exclusions and the classical regular secant
condition).** Suppose $p_i\in[10,34]\setminus\{24\}$ and
$W_i\ne W'_i\in C(p_i,v_J(p_i))$ are actual selected equal-$M$
endpoints. They have simultaneous subsequential limits in $K_J$.
Every such limiting parameter $p_*$ is off $24$. If the limiting
endpoints are distinct, both are regular and form an actual equal-$M$
pair in the child of the actual $J$ pair. If the limiting endpoints
coincide, their common source is regular, and the augmented regular
map $f_M=(N_p/D,N_v/D,N_m/D)$ has rank less than two there.

*Proof.* Theorem 23.2 gives simultaneous complete-world limits and
continuity gives equal terminal $M$ responses. SII, Theorem 29.1 gives
one $\epsilon>0$, uniform for all real $v$, excluding every actual
$M$ pair with $0<|p-24|<\epsilon$. Thus $|p_i-24|\ge\epsilon$ and
$p_*\ne24$. This already published exclusion covers singular sources
and all gain strata, and does not depend on this compactness proof.

If the limits are distinct, they are an actual $M$ pair, while
Theorem 16.4 supplies an actual distinct $J$ pair at the same limiting
base. S, Corollary 18.2 then excludes a singular selected $M$
endpoint. If the limits coincide, Theorem 13.1 and Corollary 13.2
exclude singular coalescence: local injectivity on the full parent at
such a singular world would contradict the distinctness of the nearby
matching endpoints. These are existing exclusions for selected pairs;
they remove no unused singular companion from $K_J$.

For completeness, at a regular coalescence write $x=(t,b)$ with
$t=r/b$ and $D(x_*)\ne0$. The regular reconstruction is analytic
in a neighbourhood of $x_*$. The nearby distinct complete endpoints
have distinct coordinates $x_i,y_i$ and $f_M(x_i)=f_M(y_i)$.
Take a subsequence of
$w_i=(x_i-y_i)/\|x_i-y_i\|$ converging to a unit vector $w$.
On a small convex neighbourhood the ordinary integral difference
formula gives

$$
0=\int_0^1 Df_M(y_i+s(x_i-y_i))w_i\,ds
\longrightarrow Df_M(x_*)w.
\tag{24.1}
$$

The derivative therefore has a nonzero kernel. This standard calculus
argument is a necessary condition only. In polynomial form, for
$f\in\{p,v,m\}$ define

$$
B_{f,t}=D\partial_tN_f-N_f\partial_tD,\qquad
B_{f,b}=D\partial_bN_f-N_f\partial_bD.
\tag{24.2}
$$

Use the original circuit
$N_m=-C_0+(3U+2n)B_7$,
$B_7=-20C_0+70C_1-84C_2+35C_3$.
All three polynomials

$$
\begin{gathered}
B_{p,t}B_{v,b}-B_{p,b}B_{v,t},\qquad
B_{p,t}B_{m,b}-B_{p,b}B_{m,t},\\
B_{v,t}B_{m,b}-B_{v,b}B_{m,t}
\end{gathered}
\tag{24.3}
$$

must vanish at a regular coalescence, because the corresponding
Jacobian minors have common denominator $D^4$. Nothing here proves
that this rank-drop set is empty or excludes an actual incidence. ∎

**Definition 24.2 (Applicability and unresolved alternative).** The
explicit boundary inequality (21.4), scalar arc inequality (22.8) and
their all-companion application (23.1)–(23.3) concern this original
fixed projection and the actual arc of Theorem 16.4. Finite-dimensional
compactness, closed-subset compactness, interval mean-value bounds and
the secant argument are classical methods. The boundary fractions,
pole exclusions, corner vectors, uniform infinity limit, zero-safe lift
and source-coercivity machinery are the cited source-owner results.
This application does not supply a numerical source box, a numerical
interior distance, or a completed finite search certificate.

The remaining arc question is still an actual independently chosen
within-pair-distinct equal-$M$ pair at some $p\ne24$ on this $J$ arc,
or a complete exclusion of all such pairs. The published uniform
$p=24$ gap and singular-coalescence exclusion are already available;
the unresolved cases include regular critical-diagonal limits,
separated regular incidences and nontransverse incidences. There is no
imposed positive pair-separation floor. Cross-pair overlap is free,
and the two terminal common values remain independent. Compactness
retains all companions and does not give a new whole-child cardinality
bound. Every other $J$ branch and base in (19.1) remains outside this
arc application. Neither an actual joint witness nor an arcwise or
global absence theorem, original-goal completion, literature-wide
originality, formal-kernel certification or physical realization is a
conclusion of these results.

## 追加锚（本行以下为增补区）

## 25. Singular-line coordinates for the terminal-J separation

**Definition 25.1 (Ambient children and the inherited singular lines).**
For every real $p,v$, including $p=24$, write

$$
\widehat C(p,v)=\{W\in\mathcal H:p(W)=p,\ v(W)=v\}.
\tag{25.1}
$$

For $p\ne24$ this is exactly the entire child $C(p,v)$ of Definition
1.1. Retain the actual singular locus $\mathcal S$ of Definition 14.1.
Use the two simple roots $r_-,r_+$ of Proposition 11.1, without a new
source-classification hypothesis. For $\rho\in\{r_-,r_+\}$ put

$$
\begin{gathered}
j_\rho=\frac18+8\rho(1-\rho),\qquad n_\rho=j_\rho+\rho,
\qquad q_\rho=\frac98+2j_\rho+4\rho,\\
P(\rho)=\begin{pmatrix}\rho&1/8\\8\rho(1-\rho)&1-\rho\end{pmatrix},\\
G_{\rho,e}=\left(-24-e,-\frac e{j_\rho},
                   \frac{24}{5}-\frac{8e}{9},-\frac e{n_\rho}\right),\\
g_{\rho,e}(s)=\sum_{i=0}^3(G_{\rho,e})_i
 \prod_{\substack{0\le k\le3\\k\ne i}}\frac{s-k}{i-k},
\qquad W_\rho(e)=(P(\rho),g_{\rho,e},24+e).
\end{gathered}
\tag{25.2}
$$

O, Theorem 2.1, and Proposition 11.1 identify $\mathcal S$ with
precisely these worlds for every $e\in\mathbb R$. The matrix has
strictly positive entries, trace one and determinant zero. The gain
in (25.2) is the one entire polynomial, with zero leading coefficients
allowed. Its first five responses are the original
$(0,24,147/5,24,18)$; it cannot be identically zero because the first
two responses differ. These are the reused whole-world lift and
classification, rather than additional results about the source set.

For compact response notation put

$$
\begin{aligned}
h_{5,\rho}&=\frac{71}{18}-\frac5{j_\rho},&
h_{6,\rho}&=\frac{43}{3}-\frac{16}{j_\rho},&
h_{7,\rho}&=\frac{129}{4}-\frac{35}{j_\rho},\\
P_\rho&=1+(5/4+n_\rho)h_{5,\rho},&
V_\rho&=1+(5/2+n_\rho)h_{6,\rho},\\
M_\rho&=1+(15/4+2n_\rho)h_{7,\rho},&
A_\rho&=1+q_\rho h_{7,\rho}.
\end{aligned}
\tag{25.3}
$$

Here $P_\rho$ is a scalar coefficient, distinct from the source matrix
$P(\rho)$. Subscripts $-$ and $+$ on these scalars mean evaluation at
$r_-$ and $r_+$. The same sign convention applies to the worlds
and response functions in (25.2) and (25.4).

The response interface of Lemma 14.2, with the terminal-$J$ trace of
(1.10), gives

$$
\begin{aligned}
p_\rho(e)&=24+P_\rho e,\\
v_\rho(e)&=84+24n_\rho+V_\rho e,\\
m_\rho(e)&=312+\frac{768}{5}n_\rho+M_\rho e,\\
a_\rho(e)&=24+\frac{384}{5}q_\rho+A_\rho e.
\end{aligned}
\tag{25.4}
$$

To spell out the correspondence, at $b=1/8$ the singular equation is

$$
\frac1{j_\rho}+\frac1{n_\rho}=\frac{107}{60}.
\tag{25.5}
$$

Thus the three $h$ coefficients in (25.3) are respectively
$5/n_\rho-179/36$, $16/n_\rho-71/5$ and
$35/n_\rho-181/6$. They are exactly the gain slopes in (14.4), so
$P_\rho=A(n_\rho)$, $V_\rho=B(n_\rho)$ and
$M_\rho=C(n_\rho)$ in (14.3). In particular

$$
g_{\rho,e}(5)=e h_{5,\rho},\qquad
 g_{\rho,e}(6)=24+e h_{6,\rho},\qquad
 g_{\rho,e}(7)=\frac{384}{5}+e h_{7,\rho}.
\tag{25.6}
$$

The original left products have traces $U+n_\rho$, $2U+n_\rho$,
$q_\rho$ and $3U+2n_\rho$ for $p,v,a,m$, respectively, with
$U=5/4$. Substitution of (25.6) proves all four expressions (25.4),
including the constant terms of both clock-seven alternatives.
Only $j_\rho,n_\rho,T=9/8,U=5/4$ and fixed interpolation-node
differences occur as divisors. No drift, gain sample, leading
coefficient or difference of gain roots is cancelled.

## 26. The unique common acquired history of the two singular lines

**Lemma 26.1 (Exact refinement and rational interval bounds).** Put
$q=10^{18}$ and

$$
k_-=134815875067638653,\qquad k_+=902449681772056265,
\qquad I_\pm=[k_\pm/q,(k_\pm+1)/q].
\tag{26.1}
$$

Then $r_\pm$ lies in the interior of $I_\pm$. Define

$$
\begin{gathered}
\delta n=n_+-n_-,\qquad
\Delta=P_+V_--P_-V_+,\\
e_-^*=\frac{24\delta n P_+}{\Delta},\qquad
e_+^*=\frac{24\delta n P_-}{\Delta},\qquad
W_\pm^*=W_{r_\pm}(e_\pm^*).
\end{gathered}
\tag{26.2}
$$

These expressions are well-defined. Every entry $z$ of the following
table satisfies its displayed strict rational inequalities $L<z<R$:

| $z$ | $L$ | $R$ |
| --- | --- | --- |
| $P_-$ | $-227/250$ | $-907/1000$ |
| $P_+$ | $-5217/1000$ | $-652/125$ |
| $\Delta$ | $-41/5$ | $-81/10$ |
| $p_-(e_-^*)$ and $p_+(e_+^*)$ | $826067/50000$ | $330427/20000$ |
| $v_-(e_-^*)$ and $v_+(e_+^*)$ | $4845027/50000$ | $1211257/12500$ |
| $24+e_-^*$ | $128957/4000$ | $1611963/50000$ |
| $24+e_+^*$ | $15896/625$ | $1271681/50000$ |
| $m_-(e_-^*)$ | $2308229/5000$ | $230823/500$ |
| $m_+(e_+^*)$ | $476473/1000$ | $4764733/10000$ |
| $a_-(e_-^*)$ | $2968103/10000$ | $1484053/5000$ |
| $a_+(e_+^*)$ | $212597/500$ | $850389/2000$ |
| $m_+(e_+^*)-m_-(e_-^*)$ | $9267/625$ | $148273/10000$ |
| $a_+(e_+^*)-a_-(e_-^*)$ | $1283837/10000$ | $1283839/10000$ |

*Proof.* Write $S$ for the quartic of (11.1), and define the integer
polynomial

$$
N(k)=438272k^4-931328k^3q+540800k^2q^2-50728kq^3-853q^4.
\tag{26.3}
$$

Since $q^4S(k/q)=N(k)$, the exact evaluations below give opposite
endpoint signs in each interval:

$$
\begin{aligned}
N(k_-)&=-17838134996954211531422327095735626915094241356898701037568,\\
N(k_-+1)&=30764791282455917421090534653063668386495135773775454994432,\\
N(k_+)&=23290885118885097788421262912838626831916532827618987520000,\\
N(k_++1)&=-38345978620711463093335455465648306161854810425249946206208.
\end{aligned}
\tag{26.4}
$$

The two intervals are contained respectively in the disjoint intervals
(11.2). The intermediate value theorem and the already proved unique
root in each interval (11.2) refine precisely $r_-,r_+$; no new root
exhaustion is inferred from this table.

Here are the finite rational operations determining all bounds above.
For closed rational intervals $X=[x_0,x_1]$, $Y=[y_0,y_1]$, define

$$
\begin{aligned}
X+Y&=[x_0+y_0,x_1+y_1],& -X&=[-x_1,-x_0],\\
X-Y&=X+(-Y),&
XY&=[\min E,\max E],\\
E&=\{x_0y_0,x_0y_1,x_1y_0,x_1y_1\},&
X^{-1}&=[1/x_1,1/x_0]\quad(0\notin X),\\
X/Y&=XY^{-1}\quad(0\notin Y),&
[c]&=[c,c]\quad(c\in\mathbb Q).
\end{aligned}
\tag{26.5}
$$

Every constant in an interval expression means its singleton interval;
products and differences always use (26.5), including repeated
occurrences of the same interval. Thus no independence assumption is
made and no squaring operation is left unspecified. These operations
contain the corresponding operations on any represented real numbers.

For each sign $\sigma\in\{-,+\}$ form, in the displayed order,

$$
\begin{aligned}
\mathcal J_\sigma&=[1/8]+[8]I_\sigma([1]-I_\sigma),&
\mathcal N_\sigma&=\mathcal J_\sigma+I_\sigma,\\
\mathcal Q_\sigma&=[9/8]+[2]\mathcal J_\sigma+[4]I_\sigma,\\
\mathcal H_{5,\sigma}&=[71/18]-[5]/\mathcal J_\sigma,&
\mathcal H_{6,\sigma}&=[43/3]-[16]/\mathcal J_\sigma,\\
\mathcal H_{7,\sigma}&=[129/4]-[35]/\mathcal J_\sigma,\\
\mathcal P_\sigma&=[1]+([5/4]+\mathcal N_\sigma)\mathcal H_{5,\sigma},&
\mathcal V_\sigma&=[1]+([5/2]+\mathcal N_\sigma)\mathcal H_{6,\sigma},\\
\mathcal M_\sigma&=[1]+([15/4]+[2]\mathcal N_\sigma)\mathcal H_{7,\sigma},&
\mathcal A_\sigma&=[1]+\mathcal Q_\sigma\mathcal H_{7,\sigma},\\
\mathcal D&=\mathcal P_+\mathcal V_--\mathcal P_-\mathcal V_+,\\
\mathcal E_-&=([24](\mathcal N_+-\mathcal N_-)\mathcal P_+)/\mathcal D,&
\mathcal E_+&=([24](\mathcal N_+-\mathcal N_-)\mathcal P_-)/\mathcal D.
\end{aligned}
\tag{26.6}
$$

All divisions in (26.6) have the following rational guards. For an
interval $X$, write $\inf X$ and $\sup X$ for its two endpoints.
The first line of (26.6) gives

$$
\begin{gathered}
1<\inf\mathcal J_-\le\sup\mathcal J_-<11/10,\qquad
4/5<\inf\mathcal J_+\le\sup\mathcal J_+<9/10,\\
23/20<\inf\mathcal N_-\le\sup\mathcal N_-<5/4,\qquad
5/3<\inf\mathcal N_+\le\sup\mathcal N_+<7/4.
\end{gathered}
\tag{26.7}
$$

After the reciprocal $\mathcal J_\sigma^{-1}$ operations, the same
endpoint rules give

$$
\begin{gathered}
-227/250<\inf\mathcal P_-\le\sup\mathcal P_-<-907/1000,\\
-5217/1000<\inf\mathcal P_+\le\sup\mathcal P_+<-652/125,\\
-41/5<\inf\mathcal D\le\sup\mathcal D<-81/10.
\end{gathered}
\tag{26.8}
$$

In particular $0\notin\mathcal D$, so the last line of (26.6) is
legal. The nonzero scalar $P_\pm$ needed below is certified separately
by the first two inequalities of (26.8); no inverse of these scalar
coefficients is needed in the interval expressions.

Finally form

$$
\begin{aligned}
\mathcal X_\sigma&=[24]+\mathcal P_\sigma\mathcal E_\sigma,\\
\mathcal Y_\sigma&=[84]+[24]\mathcal N_\sigma
                       +\mathcal V_\sigma\mathcal E_\sigma,\\
\mathcal B_\sigma&=[24]+\mathcal E_\sigma,\\
\mathcal Z_\sigma&=[312]+[768/5]\mathcal N_\sigma
                       +\mathcal M_\sigma\mathcal E_\sigma,\\
\mathcal T_\sigma&=[24]+[384/5]\mathcal Q_\sigma
                       +\mathcal A_\sigma\mathcal E_\sigma.
\end{aligned}
\tag{26.9}
$$

The interval for a row of the table is, respectively,
$\mathcal P_-$, $\mathcal P_+$, $\mathcal D$,
$\mathcal X_\pm$, $\mathcal Y_\pm$, $\mathcal B_\pm$,
$\mathcal Z_\pm$, $\mathcal T_\pm$,
$\mathcal Z_+-\mathcal Z_-$ or $\mathcal T_+-\mathcal T_-$.
For each row its two rational endpoints satisfy
$L<\inf X\le\sup X<R$. These inequalities are obtained solely by
(26.1) and (26.5)–(26.9): for example, the last one is exactly

$$
\frac{1283837}{10000}
 <\inf\mathcal T_+-\sup\mathcal T_-
 \le\sup\mathcal T_+-\inf\mathcal T_-
 <\frac{1283839}{10000}.
\tag{26.10}
$$

Every comparison is a rational endpoint comparison, equivalently an
integer comparison after multiplying by its positive denominators.
This specifies the two initial intervals, every arithmetic operation,
each reciprocal guard and the strict outer bounds, without rounded
root substitutions. Interval containment and (25.3)–(25.4) now prove
all stated strict bounds. ∎

**Theorem 26.2 (Unique actual common-history pair and terminal gaps).**
The two complete singular lines have exactly one common acquired base.
More precisely, if $e_-,e_+\in\mathbb R$, then

$$
\bigl(p_-(e_-),v_-(e_-)\bigr)
 =\bigl(p_+(e_+),v_+(e_+)\bigr)
\quad\Longleftrightarrow\quad
(e_-,e_+)=(e_-^*,e_+^*).
\tag{26.11}
$$

Its exact base is

$$
\begin{aligned}
p_*&=24+\frac{24\delta n P_-P_+}{\Delta},\\
v_*&=84+24n_-+\frac{24\delta n P_+V_-}{\Delta}.
\end{aligned}
\tag{26.12}
$$

The worlds $W_-^*,W_+^*$ are actual strict complete worlds, are
distinct, and satisfy the positive terminal gaps in Lemma 26.1.
In particular $p_*\ne24$, $a(W_+^*)>a(W_-^*)$ and
$m(W_+^*)>m(W_-^*)$.

*Proof.* Equality of the acquired histories in (25.4) is exactly

$$
P_-e_--P_+e_+=0,\qquad
V_-e_--V_+e_+=24\delta n.
\tag{26.13}
$$

The determinant of this two-by-two system is $\Delta\ne0$ by
(26.8), so Cramer's rule gives precisely (26.2). Conversely those
values satisfy the first equation because both products are
$24\delta n P_-P_+/\Delta$, and satisfy the second because

$$
V_-e_-^*-V_+e_+^*
 =\frac{24\delta n(P_+V_--P_-V_+)}{\Delta}=24\delta n.
\tag{26.14}
$$

Substitution gives (26.12). The reused lift (25.2) makes both worlds
actual for these real drifts; their sources differ since $r_-<r_+$.
Lemma 26.1 puts $p_*$ strictly between $826067/50000$ and
$330427/20000$, both less than $24$, and supplies both positive gaps.
Thus this is a common history of two actual whole worlds, rather than
only an intersection of projected source equations. The positive
$m$ gap records the response of this particular pair; injectivity of
$(p,v,m)$ on all of $\mathcal S$ is already Theorem 14.3. ∎

## 27. Entire-singular-source terminal-J injectivity

**Theorem 27.1 (Terminal-J separation on the entire singular locus).**
The map

$$
\Psi_J:\mathcal S\longrightarrow\mathbb R^3,\qquad
\Psi_J(W)=(p(W),v(W),a(W))
\tag{27.1}
$$

is injective. Equivalently, for every real $p,v$, including $p=24$,
terminal $a$ is injective on $\widehat C(p,v)\cap\mathcal S$.
The domain contains all real drifts, all permitted lower degrees and
all repeated or sampled gain roots; no sign condition is imposed on
the entire gain or its samples.

*Proof.* Reuse Proposition 11.1 and the lift of O, Theorem 2.1,
to write any two singular worlds as $W_\rho(e),W_{\rho'}(e')$.
If $\rho=\rho'$, equality of $p$ and (25.4) give
$P_\rho(e-e')=0$. By (26.8), $P_\rho\ne0$, so $e=e'$.
The fixed-node interpolant (25.2) then gives the same entire gain,
the same fixed drift and the same matrix, hence the identical world.

If $\rho\ne\rho'$, interchange the labels to put them on the minus
and plus lines. Equal $p,v$ force precisely $W_-^*,W_+^*$ by
Theorem 26.2. Their terminal-$J$ difference is strictly greater than
$1283837/10000>0$, contradicting equality of $a$. This exhausts the
singular-source alternatives, with no restriction on $e$ or $e'$.
At $p=24$, the nonzero $P_\pm$ additionally force $e=e'=0$;
the two cross-line $v$ values differ by $24(n_+-n_-)>0$ using
(26.7), so this ambient fibre is included as well.

All original rows are retained through the reused lift. The proof uses
no division by $e,d,g(i)$ or a leading coefficient. In particular
$e=0$ and $e=-24$, degree drops and every legal gain-zero stratum
remain in the theorem's domain. ∎

**Corollary 27.2 (Necessary selected endpoints in the original joint
relation).** Suppose the four actual labels satisfy exactly (1.6) with
$p\ne24$. Put $\chi_i=n(W_i)/U(W_i)$. Then

$$
\begin{gathered}
\Lambda(W_0)\ne0\ \hbox{or}\ \Lambda(W_1)\ne0,\\
\Lambda(W_2)\ne0,\qquad\Lambda(W_3)\ne0,\\
\chi_2\ne\chi_3,\qquad b(W_2)\ne b(W_3).
\end{gathered}
\tag{27.2}
$$

*Proof.* If both selected $J$ endpoints were singular, their common
$p,v,a$ would contradict Theorem 27.1 and $W_0\ne W_1$.
The two regular selected $M$ endpoints are the already established
conclusion of S, Corollary 18.2, based on S, Theorem 18.1, with the
independent actual $J$ pair in the same entire child. The earlier
singular-$M$ injectivity Theorem 14.3 and Corollary 14.4 are reused;
they alone would only exclude two singular $M$ endpoints.

For equal $\chi_2,\chi_3$, F, Theorem 26.4, using its entire
exceptional-source Theorem 26.3, would give identical worlds or one of
its reflected pairs at $p=24$. Here F's $u$ is the present $v$,
its $\chi=n/U$ is unchanged, and it uses the same original clocks,
whole cubic gain bound and fixed real drift. The reflected alternative
is excluded by $p\ne24$, and equality by $W_2\ne W_3$.
Finally [SVII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md),
Theorem 4.1, already excludes equal $b$ for such an off-$24$ actual
$M$ pair. These three $M$ restrictions are applications of those
existing exclusions. No additional equal-ratio or singular-$M$
classification is required. ∎

**Definition 27.3 (Unrestricted residual incidence question).** The
remaining existence question is still (19.1), over all real off-$24$
bases and independently chosen actual pairs in the entire child.
Corollary 27.2 restricts only the selected labels: the $J$ pair has
at least one regular endpoint, and the $M$ pair has two regular
endpoints with different $\chi$ and different $b$. Regular–singular
and regular–regular $J$ pairs remain admissible endpoint types.
Cross-pair overlaps remain free; the two common terminal values are
independent. There is no sign condition on gains, exact-degree
condition, extra reading, pair-separation floor or deletion of any
unused companion.

At the base (26.12), Theorem 26.2 determines only the cross-line
singular pair. It neither determines the regular members of
$C(p_*,v_*)$ nor asserts that this entire child consists of those two
worlds. The remaining joint question retains distant source
components, other $J$ branches, unused singular companions and all
strict-boundary and nonproper-base alternatives not excluded by the
specific cited results. Existence or exhaustive absence in (19.1)
is not decided by the singular separation (27.1).

## 追加锚（本行以下为增补区）
