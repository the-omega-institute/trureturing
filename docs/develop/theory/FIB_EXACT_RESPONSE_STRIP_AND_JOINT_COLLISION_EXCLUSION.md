# FIB exact response strip and exclusion of joint collisions

## 1. The complete-world question and the result

This volume proves a uniform statement about one literal parent and one
closed strip of its actual responses. Its mathematical suppliers are
the definitions, integer coefficient table and fixed determinants in
[FIB common-parent geometry and two exact mixed children](https://github.com/the-omega-institute/trureturing/blob/3185602855df9c3f79f19ae165404ef1885777c3/docs/develop/theory/FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
hereafter the **owning volume**. A reference such as “owning (20.3)”
means that equation in this specified source. The finite rational proof
data are in [the rational-certificate companion](FIB_EXACT_RESPONSE_STRIP_RATIONAL_CERTIFICATE.md).
They are coefficients, boxes and inequalities of the proof, rather than
observations at selected parameters. The argument is ordinary
mathematics; it makes no claim of Lean kernel verification.

**Definition 1.1 (Original model).** A legal world is a complete triple
$W=(P,g,d)$ with

$$
P=P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
\tag{1.1}
$$

There is no upper bound on $b$ or on $c=r(1-r)/b$. The actions and
readings are exactly

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad E_i\in\{J,M\},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP).
\tag{1.2}
$$

The clocks are $0,\ldots,7$, including the initial read. A world has
one entire polynomial and one fixed drift, also when alternative
continuations are compared. Lower degrees, sampled zeros, repeated gain
roots and zero drift are included.

Write $\mathcal F(H)$ for all complete legal worlds realizing the
literal history $H$, and fix

$$
H_4=(0,J,24,M,147/5,J,24,M,18),\qquad
\mathcal C(p,v)=\mathcal F(H_4,M,p,M,v).
\tag{1.3}
$$

Distinctness concerns complete triples, not only projected sources.

**Definition 1.2 (Actual responses).** Put

$$
j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\quad V=U+n.
\tag{1.4}
$$

The parent traces at clocks $0,1,2,3,4$ are $1,j,T,n,U$. The subsequent
traces, with words in chronological order, are

| Word | Trace against $P$ |
| --- | --- |
| $JMJMM$ | $V$ |
| $JMJMMJ$ | $T+j+2r$ |
| $JMJMMM$ | $2U+n$ |
| $JMJMMJJ$ | $V$ |
| $JMJMMJM$ | $2U+j$ |
| $JMJMMMJ$ | $T+2j+4r$ |
| $JMJMMMM$ | $3U+2n$ |

Thus, on each fixed world,

$$
\begin{aligned}
p(W)&=d+Vg(5),\\
u_J(W)&=d+(T+j+2r)g(6),&u_M(W)&=d+(2U+n)g(6),\\
f_{JJ}(W)&=d+Vg(7),&f_{JM}(W)&=d+(2U+j)g(7),\\
f_{MJ}(W)&=d+(T+2j+4r)g(7),&f_{MM}(W)&=d+(3U+2n)g(7).
\end{aligned}
\tag{1.5}
$$

Multiplication in (1.2) gives these original left-product traces; for
example $Q_{JMJMMM}=\left(\begin{smallmatrix}3&1\\5&2\end{smallmatrix}\right)$
and $Q_{JMJMMMM}=\left(\begin{smallmatrix}5&2\\8&3\end{smallmatrix}\right)$.
Alternative values in (1.5) are not additional acquired observations.

**Theorem 1.3 (Uniform entire-child strip).** Set

$$
p_c=\frac{2744214237392974691433531179656369993836520133001835}{10^{50}},
\qquad h_p=10^{-40},\qquad K=[p_c-h_p,p_c+h_p].
\tag{1.6}
$$

For every real $p\in K$ and every real $v\in[142,150]$, the entire
set $\mathcal C(p,v)$ contains exactly four distinct complete legal
worlds. Label them $W_0,W_1,W_2,W_3$ in increasing order of $r$. Then

$$
f_{MM}(W_0)<f_{MM}(W_2)<f_{MM}(W_1)<f_{MM}(W_3),
\tag{1.7}
$$

and the successive differences in this order are greater than
$6$, $14$ and $4/25$, respectively. In particular $f_{MM}$ is
injective on each entire child.

The proof occupies Sections 3–7. Section 8 identifies two additional
actual roots of the owning response polynomial inside this strip.
Section 9 gives the resulting necessary-candidate reduction.

## 2. The inherited exact parameter is unchanged

**Definition 2.1 (The original exact $p_J$).** For a regular parent
source, let $W(r,b)$ be the complete world of Lemma 3.1. For
$z=(r_0,b_0,r_1,b_1,r_2,b_2)$ put $W_i^J=W(r_i,b_i)$ and

$$
F_J(z)=\begin{pmatrix}
p(W_0^J)-p(W_1^J)\\p(W_0^J)-p(W_2^J)\\
u_J(W_0^J)-u_J(W_1^J)\\u_J(W_0^J)-u_J(W_2^J)\\
f_{JJ}(W_0^J)-f_{JJ}(W_1^J)\\
f_{JM}(W_0^J)-f_{JM}(W_2^J)
\end{pmatrix}.
\tag{2.1}
$$

This is the original owning (8.1), with the original rational box

$$
\begin{gathered}
m_J=10^{-18}(371676286016453570,158678203745512165,
530842632335007806,374463489524972148,\\
657472562317377937,380228166766336695),\qquad
\mathcal B_J=\{z:\|z-m_J\|_\infty\le10^{-12}\}.
\end{gathered}
\tag{2.2}
$$

Owning Theorem 8.1 proves that $F_J$ has exactly one zero $z_J$ in
this box, with algebraic coordinates, and defines

$$
p_J=p(W_0^J(z_J)).
\tag{2.3}
$$

The superscript distinguishes these inherited worlds from the four
worlds of Theorem 1.3.

**Proposition 2.2 (Exact parameter transport).** The number (2.3) is
algebraic and belongs to the closed interval $K$ of (1.6).

Proof. The original unique zero and its algebraicity are supplied by
owning Theorem 8.1, with the rational system, box and preconditioner
(8.1)–(8.3). Owning Definition 26.1 and Theorem 26.2 prove
$p(W_0^J(z_J))\in K$ for that same zero. Their rational vector (26.2)
refines the location of $z_J$: its preconditioned residual is less than
$2\cdot10^{-51}$ and the contraction bound is $115486/10^8$ on the
original box. The resulting enclosure gives
$|p(W_0^J(z_J))-p_c|<10^{-44}<h_p$.
These are the exact published suppliers of the correspondence. ∎

All strip statements below quantify over every $p\in K$. They are
specialized to (2.3) only after their proofs. No rational center is
substituted for the inherited parameter.

## 3. Sources, complete lifts and actual rational responses

**Lemma 3.1 (Zero-safe parent reconstruction).** Define

$$
\Lambda=1+6/T+1/U-4/j-4/n,\qquad
B_{\rm coef}=6/T-2/U=\frac{2(2+5b)}{TU}>0.
\tag{3.1}
$$

The complete worlds at $H_4$ are in bijection with
$(r,b,\epsilon)$ satisfying $0<r<1$, $b>0$ and

$$
\epsilon\Lambda+\frac{24}{5}(b-1/8)B_{\rm coef}=0.
\tag{3.2}
$$

The lift has $d=24+\epsilon$ and the unique polynomial of degree at
most three with samples at $0,1,2,3$

$$
(q_0,q_1,q_2,q_3)=
(-24-\epsilon,-\epsilon/j,(27/5-\epsilon)/T,-\epsilon/n).
\tag{3.3}
$$

On $\Lambda\ne0$ the source alone fixes this whole world, by
$\epsilon=-(24/5)(b-1/8)B_{\rm coef}/\Lambda$.

Proof. The first four readings force (3.3). Cubic interpolation gives
$g(4)=-q_0+4q_1-6q_2+4q_3$ and hence

$$
d+Ug(4)-18
=U\{\epsilon\Lambda+(24/5)(b-1/8)B_{\rm coef}\}.
\tag{3.4}
$$

Thus the fifth parent row is equivalent to (3.2). Conversely the
samples fix one entire polynomial, all parent readings then hold, and
the unequal readings $0,24$ prevent that polynomial from being
identically zero. Strict sources give $j,n,T,U>0$.
This proves both directions, including $\epsilon=0$ and
$\Lambda=0$, without dividing by any gain sample. It is the direct
interpolation proof of owning Theorem 2.1. ∎

The same interpolant at the unchanged clocks gives

$$
\begin{aligned}
g(5)&=-4q_0+15q_1-20q_2+10q_3,\\
g(6)&=-10q_0+36q_1-45q_2+20q_3,\\
g(7)&=-20q_0+70q_1-84q_2+35q_3.
\end{aligned}
\tag{3.5}
$$

**Definition 3.2 (Exact source polynomials).** These are the owning
polynomials (12.1)–(12.3), (20.1) and (27.1), with $D$ denoting
$D_\Lambda$, never the different $p=24$ graph denominator:

$$
\begin{aligned}
X&=b^2+r-r^2,&N&=X+br,\\
D&=(b^2+8b+4)XN-2bTU(X+N),&K_\Lambda&=(8b-1)(2+5b),\\
H&=14b^6+(95-73r)b^5+(47r^2-39r+30)b^4\\
&\quad+r(147r^2-232r+105)b^3
+2r(1-r)(44r^2-55r+15)b^2\\
&\quad-64r^3(1-r)^2b-32r^3(1-r)^3,\\
Z_6&=N+2bU,&Z_7&=2N+3bU,\\
G_6&=(10T+45)XN-bT(36N+20X),\\
G_7&=(20T+84)XN-bT(70N+35X),\\
D_m&=5bD,&N_p&=120bD-3(8b-1)H,\\
N_u&=\frac{120bTD+15Z_6D(80b-1)
-3K_\Lambda(bTXN+Z_6G_6)}{T},\\
N_m&=\frac{120bTD+12Z_7D(200b+11)
-3K_\Lambda(bTXN+Z_7G_7)}{T},\\
\mathsf A&=D_mp-N_p,&\mathsf B&=D_mv-N_u.
\end{aligned}
\tag{3.6}
$$

Both divisions by $T=b+1$ in (3.6) are exact in $\mathbb Z[r,b]$:
substitution $b=-1$ annihilates their numerators.
The four polynomials $D_m,N_p,N_u,N_m$ have total degree at most
seven. Wherever $D_m\ne0$, set

$$
\pi=N_p/D_m,\qquad \upsilon=N_u/D_m,\qquad \omega=N_m/D_m.
\tag{3.7}
$$

**Lemma 3.3 (Actual response correspondence).** On every legal regular
parent source, $\pi=p(W)$, $\upsilon=u_M(W)$ and
$\omega=f_{MM}(W)$. The regular complete worlds of $\mathcal C(p,v)$
therefore correspond exactly to the strict sources
$\mathsf A=\mathsf B=0$, $D\ne0$, and their lifts are unique.

Proof. Since $j=X/b$, $n=N/b$, multiplication in (3.1) gives

$$
\Lambda=\frac{2D}{TU XN},\qquad
\epsilon=-\frac{3K_\Lambda XN}{5D}.
\tag{3.8}
$$

For strict sources all factors $b,T,U,X,N$ are positive, so $D\ne0$
is exactly regularity. Substituting (3.3), (3.5), (3.8) into (1.5)
gives numerators $N_p,N_u,N_m$ with denominator $5bD$.
These are also owning (20.9) and Theorem 27.2 in the identical
normalization. Thus the polynomial equalities are equivalent to the
two acquired equalities after the complete parent lift.
Lemma 3.1 gives its legality and uniqueness. Neither $\mathcal L_1$,
a drift, a sampled gain nor a gain leading coefficient was divided
out. ∎

## 4. Fixed base projections, corank and exhaustive projection

**Definition 4.1 (The owning eliminant and ordered minors).** Put

$$
\begin{aligned}
\Psi_2&=4r^2-2r-1,\\
\Psi_4&=625r^4-1000r^3+50r^2+260r+36,\\
\Phi&=438272r^4-931328r^3+540800r^2-50728r-853,\\
E&=\Psi_2\Psi_4\Phi.
\end{aligned}
\tag{4.1}
$$

Let $S$ be the fixed $14$ by $14$ matrix of coefficient rows
$b^6\mathsf A,\ldots,\mathsf A,b^6\mathsf B,\ldots,\mathsf B$
and columns $b^{13},\ldots,1$, retaining zero coefficients under
specialization. The integer polynomial $R=R_{18}(r,p,v)$ is exactly
the 668-term table in owning Definition 24.1, with monomial order
$(r,p,v)$ and coordinate degrees $(18,7,7)$. It satisfies

$$
\det S=52488000\,r^{11}(r-1)^9E(r)R(r,p,v).
\tag{4.2}
$$

This is owning (20.3), fixing scale and sign. The table and (3.6)
are finite coefficient definitions for the rational proof below.

Also retain the actual $12$ by $13$ matrix $S_1$ of ordered rows
$b^5\mathsf A,\ldots,\mathsf A,b^5\mathsf B,\ldots,\mathsf B$ and
columns $c_{12},c_{11},\ldots,c_0$ for descending powers. Define

$$
\begin{aligned}
\Delta_1&=\det(c_{12},\ldots,c_2,c_1),&
\Delta_0&=\det(c_{12},\ldots,c_2,c_0),\\
\mathcal L_i&=\Delta_i/(72900r^6(r-1)^4),&&i=0,1.
\end{aligned}
\tag{4.3}
$$

These are precisely the integer quotient polynomials of owning
(20.5), of coordinate degrees $(26,6,6)$; no rescaling or
primitive-part operation is implicit.

**Lemma 4.2 (Base points and simple base factors).** For arbitrary
$p,v$, the equations $\mathsf A=\mathsf B=D=0$ have the following
fixed points over the roots of the indicated factors:

| Factor | Fixed $b$ | $D$ at that $b$ |
| --- | --- | --- |
| $\Psi_2$ | $-1/2$ | $(4r^2-4r-1)\Psi_2/64$ |
| $\Psi_4$ | $-2/5$ | $24\Psi_4/15625$ |
| $\Phi$ | $1/8$ | $3\Phi/262144$ |

The factors are squarefree and pairwise coprime.

Proof. Substitute in (3.6). At $b=-1/2$ the quotients of
$\mathsf A,\mathsf B$ by $\Psi_2$ are respectively

$$
\begin{aligned}
-\frac5{128}\{&p(4r^2-4r-1)+3072r^4-4608r^3-672r^2+1644r+360\},\\
-\frac5{128}\{&6768r^4-10152r^3-1416r^2+3522r+777
+v(4r^2-4r-1)\}.
\end{aligned}
\tag{4.4}
$$

At $b=-2/5$ the quotients by $\Psi_4$ are
$-48(5p+1050r^2-630r-204)/78125$ and
$-24(825r^2-495r+2v-48)/15625$.
At $b=1/8$ the quotients by $\Phi$ are
$15(p-24)/2097152$ and
$15(192r^2-216r+v-87)/2097152$.
The exact univariate resultants are

| Inputs | Resultant |
| --- | --- |
| $\Psi_2,\Psi_2'$ | $-80$ |
| $\Psi_4,\Psi_4'$ | $1052148437500000000$ |
| $\Phi,\Phi'$ | $1599002682601002815300829777913446400$ |
| $\Psi_2,\Psi_4$ | $-19319$ |
| $\Psi_2,\Phi$ | $167160966400$ |
| $\Psi_4,\Phi$ | $25020641227626799334847923761$ |

Their nonvanishing proves the assertion, including simplicity of
every zero of $E$. ∎

**Lemma 4.3 (Corank counts finite sources).** Fix arbitrary real
$p,v$. Every finite source with $0<r<1$, $\mathsf A=\mathsf B=0$,
$D\ne0$ projects to $R(r,p,v)=0$. If this root of $R$ is simple,
there is at most one such source above it. No sign restriction on
$b$ is needed for this assertion.

Proof. A finite common root $b=t$ gives the null vector
$(t^{13},\ldots,t,1)^{\mathsf T}$ of $S$.
For $k$ distinct roots the corresponding vectors are independent by
the Vandermonde identity, for the values $k\le3$ needed here.
Thus the corank is at least $k$.

A polynomial matrix of corank at least $k$ at $r_0$ has determinant
vanishing to order at least $k$. Constant invertible row and column
operations put its value at $r_0$ in rank normal form; at least $k$
columns then vanish at $r_0$, contributing $k$ factors $r-r_0$.
The argument concerns the fixed matrix, whatever the specialized
source degrees.

Off $E$, (4.2) directly forces $R=0$. On $E$, Lemma 4.2 supplies a
common root with $D=0$. A proposed $D\ne0$ root is distinct from it,
so the determinant has order at least two. The $E$ factor has order
exactly one and $r_0(r_0-1)\ne0$, forcing $R(r_0,p,v)=0$ again.

If $R$ is simple, the determinant has order one off $E$ and order
two on $E$. Two different $D\ne0$ sources would force order at
least two off $E$, or at least three on $E$ including its base
point. Both contradict (4.2). This proves uniqueness without
assuming $\mathcal L_1\ne0$. Padded source-degree drops, including
$v=-225$, do not alter the proof. ∎

## 5. Uniform roots and affine source lifts on the closed strip

**Lemma 5.1 (Six simple projected roots).** For every
$(p,v)\in K\times[142,150]$, $R(r,p,v)$ has exactly six roots in
$0<r<1$, all simple.

Proof. Companion Sections 2–3 specify the exact tensor-Bernstein
conversion of the owning integer table, the error bound on the whole
$p$ interval, the dyadic subdivision rule and all twenty closed
$v$ intervals. On each, the rule excludes the complement in $[0,1]$
of six listed disjoint $r$ intervals. Each listed interval has
strictly opposite endpoint signs and a derivative of one strict sign.
These are finite rational coefficient inequalities, with their
complete reconstruction specified there. The intermediate value
theorem and monotonicity give one simple root in each; the
complementary sign-variation tests exclude every other root.
The strict endpoint signs also exclude $r=0,1$ and the outer
endpoints of the six isolating intervals.

The parameter error covers all $K$, and the twenty closed intervals
meet and cover $[142,150]$. Thus the conclusion includes all
parameter boundaries. ∎

**Lemma 5.2 (Six actual regular source solutions).** For every pair
in that closed rectangle there are six distinct solutions
$z_i=(r_i,b_i)$ of $\pi=p$, $\upsilon=v$, ordered by increasing $r$.
They have $0<r_i<1$, $D_m(z_i)\ne0$, $\Lambda(z_i)\ne0$ and
invertible source Jacobians.
Their $b$ signs are positive for $i=0,1,2,3$ and negative for $i=4,5$.
The four positive sources lift to complete legal worlds in
$\mathcal C(p,v)$.

Proof. The companion gives 190 closed cells partitioning the strip
and six rational records $(m,C,\rho)$ on each. Write $v_c,h_v$ for
the cell midpoint and radius, and set

$$
F=(\pi,\upsilon)^{\mathsf T},\qquad
H(z)=C\{F(z)-(p_c,v_c)^{\mathsf T}\},\qquad
L=C(0,1)^{\mathsf T},\quad E_0(z)=I-DH(z).
\tag{5.1}
$$

The matrix $E_0$ is distinct from the polynomial $E$. For each record
the entire rectangle

$$
\mathcal B=\{z:|z_j-m_j|\le |L_j|h_v+\rho,\ j=0,1\}
\tag{5.2}
$$

is free of all response and regular-chart poles. Put

$$
q=\sup_{\mathcal B}\|E_0\|_\infty,\qquad
\eta_i=|H_i(m)|+h_v\sup_{\mathcal B}|(E_0L)_i|+|C_{i0}|h_p.
\tag{5.3}
$$

The companion's outward rational bounds prove for every record that
$C$ is invertible, $\rho>0$, and

$$
q<9/20,\qquad \max_i\eta_i+q\rho<\rho.
\tag{5.4}
$$

Fix the actual $t=p-p_c$, $x=v-v_c$. A solution in
$z=m+Lx+\delta$, $\|\delta\|_\infty\le\rho$, is a fixed point of

$$
\delta\longmapsto
\delta-H(m+Lx+\delta)+Lx+C(t,0)^{\mathsf T}.
\tag{5.5}
$$

The derivative is $E_0$, and the value at zero has component bounds
$\eta_i$, by integrating $I-DH$ from $m$ to $m+Lx$.
Thus (5.4) gives a contraction strictly mapping the closed
radius-$\rho$ ball into itself. Banach's theorem gives one fixed
point for each actual $p,v$, equivalent to $F=(p,v)$ because $C$
is invertible. Also $DH=I-E_0$ and hence $DF$ are invertible.

The six entire rectangles have strictly ordered, disjoint $r$ bounds
inside $(0,1)$, with the asserted $b$ signs; these are further
rational table inequalities. Lemma 3.3 gives the four positive
complete lifts, with all original parent, fifth and sixth readings.
The two negative sources serve only to exhaust algebraic projections;
they are not legal worlds. ∎

## 6. Every singular source is accounted for

**Lemma 6.1 (Actual singular responses miss the strip).** There is no
world in $\mathcal C(p,v)$ with $\Lambda=0$ when $p\in K$ and
$v\in[142,150]$.

Proof. Equation (3.2) and $B_{\rm coef}>0$ force $b=1/8$.
At this width,

$$
j=1/8+8r(1-r),\quad n=j+r,\quad T=9/8,\quad U=5/4,
\qquad \Lambda=\Phi(r)/(960jn).
\tag{6.1}
$$

There are exactly two roots $r_-,r_+$ of $\Phi$ in $(0,1)$, in

$$
I_-=[149383/1108052,182914/1356769],\qquad
I_+=[1412683/1565387,1774115/1965888].
\tag{6.2}
$$

Indeed the signed Sturm chain
$f_0=\Phi,f_1=\Phi',f_{i+1}=-\operatorname{rem}(f_{i-1},f_i)$
has degrees $4,3,2,1,0$, signs $(-,-,+,-,+)$ at zero and
$(-,-,+,+,+)$ at one. Its variation drop is two; both intervals
in (6.2) have opposite polynomial endpoint signs. These are the
owning Section 21 root isolations.

At $b=1/8$ put

$$
\begin{aligned}
A_5(r)&=1+(n+5/4)(4-15/j+160/9-10/n),\\
a_6(r)&=50-36/j-20/n,\\
\epsilon&=(p-24)/A_5(r),\\
s(r,p)&=24+\epsilon+(5/2+n)\{24+\epsilon a_6(r)\}.
\end{aligned}
\tag{6.3}
$$

The interpolant gives $p=24+\epsilon A_5$ and the actual sixth-M
response $s(r,p)$. Rational interval evaluation on all of (6.2)
and $K$ gives

| $r$ interval | Guard for $A_5$ | Enclosure of $s(r,p)$ |
| --- | --- | --- |
| $I_-$ | $(-908,-907)/10^3$ | $(1198704988168,1198704988252)/10^{10}$ |
| $I_+$ | $(-5217,-5216)/10^3$ | $(1387528570299,1387528570311)/10^{10}$ |

The arithmetic and order of evaluation are specified in companion
Section 8. Both guards exclude zero, so each fifth response selects
exactly one $\epsilon$ on each whole singular line. Lemma 3.1
selects its unique entire gain and drift. Both actual acquired
response intervals are strictly below $142$. This excludes the
singular stratum by actual responses, without deleting a chart
or requiring a generic-rank premise there. ∎

## 7. Exhaustion and terminal separation at one common parameter pair

**Lemma 7.1 (Entire-child exhaustion and compatible branches).**
The four positive lifts in Lemma 5.2 are every world of
$\mathcal C(p,v)$. Their increasing-$r$ source functions agree on
shared cell boundaries and are locally continuously differentiable
in the parameters.

Proof. Lemma 6.1 excludes singular worlds. Every other actual world
has $\mathsf A=\mathsf B=0$, $D\ne0$ by Lemma 3.3, hence projects
to $R=0$ by Lemma 4.3. The six distinct regular points in Lemma 5.2
already occupy all six simple projections of Lemma 5.1. Lemma 4.3
allows at most one regular source above each, even on a fixed base
projection. Two sources have $b<0$; the other four have their unique
complete lifts. This applies to every finite strict source without
bounding either offdiagonal, and also when $\mathcal L_1$ vanishes.

At a shared cell boundary both constructions give the same sorted
six projections and unique regular sources above them. They agree
pointwise. The implicit function theorem applies to the invertible
Jacobians. Strict box and contraction bounds give local extensions
also at the closed parameter boundaries. Thus the source branches
are compatible and locally continuously differentiable. ∎

**Lemma 7.2 (Correlated output bounds).** For a single cell use the
common $x=v-v_c$ and the record for branch $i$. Put

$$
\begin{aligned}
w_i&=\omega(m_i),\qquad a_i=D\omega(m_i)L_i,\\
e_i&=\rho_i\sup_{\mathcal B_i}\|D\omega\|_1
+h_v\sup_{\mathcal B_i}|(D\omega-D\omega(m_i))L_i|.
\end{aligned}
\tag{7.1}
$$

At the actual source for the same $p,v$,
$|\omega(z_i)-w_i-a_ix|\le e_i$. On all 190 cells the rational
lower bounds for the differences $(i,j)=(0,2),(2,1),(1,3)$ are
strictly greater than, respectively,

$$
\frac{69947968847}{10^{10}}>6,\qquad
\frac{144190706814}{10^{10}}>14,\qquad
\frac{1614405690}{10^{10}}>\frac4{25}.
\tag{7.2}
$$

Proof. Write $z_i=m_i+L_ix+\delta_i$ with
$\|\delta_i\|_\infty\le\rho_i$. Integrate $D\omega$ first from
$m_i+L_ix$ to $z_i$, then from $m_i$ to $m_i+L_ix$ after
subtracting $D\omega(m_i)$. Both segments lie inside (5.2).
This proves (7.1), and therefore

$$
\omega(z_j)-\omega(z_i)
\ge(w_j-w_i)-|a_j-a_i|h_v-e_i-e_j.
\tag{7.3}
$$

Companion Sections 4–7 specify outward rational enclosures for
every term and the resulting bounds (7.2). The affine part uses
$a_j-a_i$ times one shared $x$; it never combines independently
attained extrema at different sixth responses.
The remainders hold uniformly for the same actual $p\in K$.
The decisions are exact rational inequalities. ∎

Proof of Theorem 1.3. Lemma 7.1 proves exactly four complete legal
worlds, and Lemma 3.3 identifies their terminal-M readings with
$\omega$. Lemma 7.2 gives the order and gaps. Distinct sources give
distinct complete triples. The closed cells cover every boundary
point. ∎

## 8. Two additional genuine roots of the published necessary polynomial

**Definition 8.1 (The same fixed response polynomial).** Retain
exactly owning Definition 28.1.
For bounds $m,n$, $\operatorname{Res}^{m,n}_x(A,B)$ has ordered rows
$x^{n-1}A,\ldots,A,x^{m-1}B,\ldots,B$ and descending coefficient
columns, with all absent coefficients retained as zeros.
For $C(r,b)=\sum_{k=0}^7C_k(r)b^k$ padded to degree seven, put

$$
\mathcal H(C)=\sum_{k=0}^7 C_k(-\mathcal L_0)^k\mathcal L_1^{7-k},
\qquad F_*=\mathcal H(N_m),\quad G_*=\mathcal H(D_m).
\tag{8.1}
$$

The exact owning polynomial is

$$
\begin{aligned}
a(p,v)&=[r^{18}]R,\\
E_1&=\operatorname{Res}^{18,26}_r(R,\mathcal L_1),&
E_2&=\operatorname{Res}^{10,26}_r(E,\mathcal L_1),\\
E_3&=\operatorname{Res}^{18,186}_r(R,G_*),&
T_*&=\operatorname{Res}^{18,188}_r(R,F_*-wG_*),\\
E_4&=\operatorname{Res}^{18,17}_w(T_*,\partial_wT_*),&
Q&=aE_1E_2E_3E_4.
\end{aligned}
\tag{8.2}
$$

Here $F_*,G_*$ are owning $F,G$, renamed to distinguish the source
map in (5.1). Fixed padding, ordered minors and the divisor (4.3)
are part of the definition.

**Theorem 8.2 (Two designated branch crossings).** Let

$$
\alpha=\frac{1+\sqrt5}{4},\quad
B_x=\left(\frac{143750631793}{10^9},\frac{143750631794}{10^9}\right),
\quad
B_y=\left(\frac{145067443732}{10^9},\frac{145067443733}{10^9}\right).
\tag{8.3}
$$

For each $p\in K$ there is exactly one $v_x(p)\in B_x$ with
$r_2(p,v_x(p))=\alpha$, and exactly one $v_y(p)\in B_y$ with
$r_3(p,v_y(p))=\alpha$. Both are roots of the actual $Q(p,v)$.
At $p=p_J$ they are real algebraic numbers, distinct from each
other and from the old $v_\star$. Their entire actual children
contain no distinct terminal-M collision pair.

Proof. At fixed $p$, differentiating $F(z)=(p,v)$ gives

$$
\frac{\partial z}{\partial v}=(I-E_0)^{-1}L,\qquad
\left\|\frac{\partial z}{\partial v}-L\right\|_\infty
\le\frac q{1-q}\|L\|_\infty.
\tag{8.4}
$$

Every lift cell has $|L_0|>q\|L\|_\infty/(1-q)$ on the positive
branches, with $L_0<0$ for branches 2 and 3. These are explicit
companion inequalities. Both $r_2,r_3$ therefore strictly decrease
with $v$ throughout the strip, using the compatible differentiable
branches of Lemma 7.1.

The two event cells in companion Section 7 use the closed endpoints
of $B_x,B_y$. Set

$$
\alpha_L=\frac{809016994374947424102293417182}{10^{30}},
\qquad \alpha_U=\alpha_L+10^{-30}.
\tag{8.5}
$$

The exact signs of $\Psi_2$ give $\alpha_L<\alpha<\alpha_U$.
For the designated branch in each event cell its affine box gives,
uniformly on $K$,

$$
m_r+L_0(v_L-v_c)-\rho>\alpha_U,\qquad
m_r+L_0(v_U-v_c)+\rho<\alpha_L.
\tag{8.6}
$$

Continuity and strict decrease prove existence and uniqueness of the
specified crossings. This is uniqueness of those branch crossings;
it does not isolate every zero of $Q$ in either bracket.

At either crossing the actual source has $b>0$, $D\ne0$,
$\mathsf A=\mathsf B=0$ and $r=\alpha$. At the same $r,p,v$,
Lemma 4.2 supplies the distinct common root $b=-1/2$ with $D=0$.
Lemma 4.3 gives $R(\alpha,p,v)=0$, including this base projection
coincidence. For the actual matrix $S_1$ in (4.3), the two
independent evaluation vectors $(t^{12},\ldots,t,1)^{\mathsf T}$
at these two $b$ roots lie in its kernel. Its rank is at most
eleven, so all $12$ by $12$ minors vanish, in particular
$\Delta_1,\Delta_0$. Because
$72900\alpha^6(\alpha-1)^4\ne0$, the precise quotient (4.3) gives
$\mathcal L_1(\alpha,p,v)=0$.

Thus $R,\mathcal L_1$ have a finite common $r$ root. Its evaluation
vector annihilates the fixed padded Sylvester matrix in $E_1$,
so $E_1(p,v)=0$ and $Q(p,v)=0$. No division by $\mathcal L_1$ or
differently normalized subresultant is used.

Now specialize to the unchanged algebraic $p_J$. The leading
$b$ coefficient of $\mathsf A(\alpha,b,p_J)$ is $5p_J+216>0$.
This nonzero polynomial over the algebraic numbers makes its
crossing $b$ algebraic. The actual response $N_u/D_m$, with nonzero
denominator, is algebraic as well. The two brackets are disjoint,
and both are disjoint from

$$
\left(\frac{144397245334493}{10^{12}},
\frac{144397245371500}{10^{12}}\right),
\tag{8.7}
$$

which contains the old $v_\star$ by owning Theorem 19.1.
Both new responses lie in $[142,150]$, so Theorem 1.3 excludes a
terminal-M pair in each entire child, not just in a chosen support. ∎

## 9. At most 74935 necessary candidates remain for the original question

**Definition 9.1 (Original joint-pair predicate).** At the original
exact $p_J$, let $\mathcal J(v)$ mean that there are
$A,B,C,D\in\mathcal C(p_J,v)$ with

$$
A\ne B,\quad C\ne D,\qquad
f_{MJ}(A)=f_{MJ}(B),\quad f_{MM}(C)=f_{MM}(D).
\tag{9.1}
$$

Labels from different pairs may coincide: the original question
does not require four distinct worlds. Set

$$
\mathcal U=\{v\in\mathbb R:Q(p_J,v)=0\}
\ \cup\ \{s_-(p_J),s_+(p_J)\},\qquad s_\pm(p)=s(r_\pm,p),
\tag{9.2}
$$

using exactly the singular sources and actual responses (6.2)–(6.3).

**Theorem 9.2 (Equivalent necessary-candidate remainder).**

$$
\exists v\in\mathbb R\;\mathcal J(v)
\quad\Longleftrightarrow\quad
\exists v\in\mathcal U\setminus[142,150]\;\mathcal J(v),
\qquad |\mathcal U\setminus[142,150]|\le74935.
\tag{9.3}
$$

Proof. Owning Theorems 28.2, 30.2 and 31.1 give, for this same
$p_J$, $Q(p_J,0)\ne0$, $\deg_vQ(p_J,v)\le74935$, and the
necessary condition that any distinct actual terminal-M pair has
$v\in\mathcal U$. The nonzero-polynomial assertion is supplied
there by the exact root-disk and image-separation proof at $v=0$;
it is not inferred from the strip computation.

Thus (9.1) forces $v\in\mathcal U$. Theorem 1.3 makes (9.1)
false throughout $[142,150]$, even with overlap between its pairs,
by excluding a terminal-M pair altogether. This proves the forward
implication. The reverse is restriction to a subset of $\mathbb R$.

Theorem 8.2 exhibits two distinct roots of $Q(p_J,v)$ inside the
removed strip. A nonzero polynomial of degree at most $74935$ has
at most $74935$ distinct real roots; at most $74933$ remain outside
the strip. Adding the two singular responses gives at most $74935$
distinct members. Coincidences can only lower the count. No assertion
that $v_\star$ is itself a root of $Q$ is needed for this subtraction. ∎

**Open problem 9.3 (The remaining actual joint decision).**
Whether (9.1) holds at any member of the remainder (9.2) is unresolved
here. A root of $Q$ can be extraneous and supplies neither a legal
world nor either collision pair. Both singular responses, any
degree-drop candidate such as $v=-225$, and every other outside-strip
candidate retain their original complete-world obligations.

The argument does not resolve other fifth responses, the all-fifth
or common-parent question, earlier histories, global eight-versus-nine
recovery, or full-original-domain nine-read sufficiency. It gives no
physical realization or physical claim. These boundaries identify
the remaining quantifiers; they do not restrict the original domain.

## 10. Mathematical sources and the new content

| Supplier | Exact use and boundary |
| --- | --- |
| Owning volume, Definitions 1.1–1.3, Theorem 2.1, (8.1)–(8.4), Theorem 26.2 | Original model, parent interpolation, original algebraic $p_J$ and its membership in $K$. |
| Owning volume, (12.1)–(12.3), (20.1)–(20.6), Definition 24.1, Theorem 27.2 | Actual rational responses, integer eliminant table, ordered determinants and terminal-M numerator. The corank argument here handles fixed-base coincidences without a nonzero linear-subresultant premise. |
| Owning volume, Theorems 19.1, 28.2, 30.2, 31.1 and (29.1) | Old response enclosure, nonzero-polynomial and degree facts, necessary finite restriction and singular responses. The old one-child conclusion is a supplier, not the new uniform conclusion. |
| Cox–Little–O'Shea, [Ideals, Varieties, and Algorithms](https://doi.org/10.1007/978-3-319-16721-3), Chapter 3 | Standard Sylvester elimination; all matrix orders and divisors used here are fixed explicitly. |
| Basu–Pollack–Roy, [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2), univariate root methods; owning Section 21 | Standard Descartes/Bernstein and Sturm principles. The companion specifies positive de Casteljau subdivision and the actual coefficient inequalities for this strip. |
| Jiří Lebl, [Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf), Theorem 8.5.6 | Implicit function theorem, after invertibility of the source Jacobians is established. Banach contraction is used with the explicit closed self-map bounds (5.4). |
| Owning Section 30 | Inherited Rouché root-disk and padded-resultant product proof of $Q(p,0)\ne0$ on $K$; no new complex root claim is needed for this strip proof. |

The source-specific new content is Theorem 1.3, the two actual
additional candidate exclusions of Theorem 8.2, and (9.3).
This is repository-derived ordinary mathematics. The standard methods,
the previous one-child result and any separate global cardinality
bound are not claimed as new contributions of this volume.

## 追加锚（本行以下为增补区）

## 11. Exact polynomial data on the second response strip

**Definition 11.1 (Parameter rectangle and unchanged suppliers).**
Retain the complete worlds, actual response functions, exact $p_J$,
$K$, and polynomial normalizations of Definitions 1.1–4.1 and 8.1.
Write $O$ for the owning volume, $F$ for
[FIB all-response finite-fibre geometry](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md),
and $S$ for
[FIB entire singular-response children and terminal-M injectivity](FIB_SINGULAR_RESPONSE_CHILDREN_EXCLUSION.md).
The auxiliary parameter interval is exactly $F$, Section 1:

$$
\begin{gathered}
p_0=\frac{219537139}{8000000},\qquad
h=\frac1{200000000},\qquad
\mathcal P=[p_0-h,p_0+h]
 =\left[\frac{2744214237}{10^8},\frac{2744214238}{10^8}\right],\\
v_c=\frac{251}{2},\qquad I=[125,126],\qquad
\rho_* =\frac1{10000}.
\end{gathered}
\tag{11.1}
$$

All these numbers are rational. Direct comparison with (1.6) gives

$$
p_0-h<p_c-h_p<p_c+h_p<p_0+h,
\qquad p_J\in K\subset\mathcal P.
\tag{11.2}
$$

The membership of the original root-defined $p_J$ uses Proposition
2.2. The interval $\mathcal P$ supplies polynomial bounds; the
entire-child conclusions below have $p\in K$.

For $z=(r,b)$ set

$$
F_s(z;p,v)=
\begin{pmatrix}\mathsf A(r,b,p)\\\mathsf B(r,b,v)\end{pmatrix}
=\begin{pmatrix}D_m(r,b)p-N_p(r,b)\\D_m(r,b)v-N_u(r,b)\end{pmatrix}.
\tag{11.3}
$$

Here $\mathsf A=\mathsf S_p/2$, $D=D_\Lambda=N_4/2$,
$D_m=5bD$, and $N_u,N_m$ include the exact divisions by $1+b$
in (3.6). Thus (11.3) is the polynomial source system, distinct
from the rational map used in (5.1). The eliminant remains the
668-integer polynomial of $O$, Definition 24.1, with the order
$(r,p,v)$ and the scale and sign fixed by (4.2).

**Definition 11.2 (Bernstein coefficients for $I$).** Write
$R=\sum_{k=0}^{18}a_k(p,v)r^k$ with zero padding, and put

$$
\begin{aligned}
\beta_i(p,v)&=\sum_{k=0}^i
 \frac{\binom{i}{k}}{\binom{18}{k}}a_k(p,v),\\
\beta_i(p_0+hx,v_c+\theta/2)
 &=\sum_{a,d\ge0}\gamma_{iad}x^a\theta^d,\qquad
 B_i=\sum_{(a,d)\ne(0,0)}|\gamma_{iad}|.
\end{aligned}
\tag{11.4}
$$

In particular $|x|,|\theta|\le1$. If $c_{kj\ell}$ is the
literal coefficient of $r^kp^jv^\ell$ in the owning table, every
coefficient in (11.4) is the following finite rational sum:

$$
\gamma_{iad}=
\sum_{\substack{k\le i,\ j\ge a,\ \ell\ge d}}
c_{kj\ell}\frac{\binom{i}{k}}{\binom{18}{k}}
\binom ja p_0^{j-a}h^a
\binom\ell d v_c^{\ell-d}2^{-d}.
\tag{11.5}
$$

Absent coefficients are zero. The normalized Bernstein parameter
$\theta=2(v-v_c)$ is distinct from the displacement $t=v-v_c$
used in the source tubes.

**Definition 11.3 (Four affine polynomial-source tubes).** The
centres $m_i$ have the following integer numerators, each with
denominator $10^{12}$:

| $i$ | $(m_i)_r$ numerator | $(m_i)_b$ numerator |
| --- | --- | --- |
| $0$ | $137255688262$ | $186017503303$ |
| $1$ | $166072995880$ | $146057648221$ |
| $2$ | $872912893446$ | $-368334211937$ |
| $3$ | $888398398627$ | $-595719530583$ |

Define exact rational matrices and vectors by

$$
\begin{aligned}
J_i&=D_zF_s(m_i;p_0,v_c),& C_i&=J_i^{-1},\\
L_i&=-C_i\begin{pmatrix}0\\D_m(m_i)\end{pmatrix},&
\mathcal P_i(y,e,t)&=C_iF_s(m_i+L_it+y;p_0+e,v_c+t).
\end{aligned}
\tag{11.6}
$$

Invertibility is included in Lemma 11.4. Equivalently,
$C_i=(\det J_i)^{-1}
\left(\begin{smallmatrix}(J_i)_{11}&-(J_i)_{01}\\
-(J_i)_{10}&(J_i)_{00}\end{smallmatrix}\right)$ with indices
$0,1$. No rounded inverse enters these definitions.
The closed tube has

$$
z=m_i+L_it+y,\qquad
\|y\|_\infty\le\rho_*,\quad |e|\le h,\quad |t|\le\tfrac12.
\tag{11.7}
$$

For a polynomial
$H(y_0,y_1,e,t)=\sum H_{abcd}y_0^ay_1^be^ct^d$ define

$$
\begin{aligned}
\mathcal N(H)&=\sum_{a,b,c,d}|H_{abcd}|
 \rho_*^{a+b}h^c2^{-d},\\
\eta_i&=\max_{k=0,1}\mathcal N(\mathcal P_{ik}(0,0,e,t)),\\
q_i&=\max_{k=0,1}\sum_{j=0}^1
 \mathcal N(\delta_{kj}-\partial_{y_j}\mathcal P_{ik}).
\end{aligned}
\tag{11.8}
$$

The entries $\delta_{kj}$ in (11.8) are constant polynomials.
For a polynomial $H(r,b)$ write
$\widehat H_i(y,t)=H(m_i+L_it+y)$, and define its uncoarsened
coefficient interval

$$
\mathcal I_i(H)=[H(m_i)-s_i(H),H(m_i)+s_i(H)],\qquad
s_i(H)=\mathcal N(\widehat H_i-H(m_i)).
\tag{11.9}
$$

These intervals contain $H$ on the entire tube. For intervals
$X,Y$ with $0\notin Y$, $X/Y$ denotes the interval whose endpoints
are the minimum and maximum of the four endpoint quotients.

**Lemma 11.4 (Finite rational inequalities for the second strip).**
For $i\notin\{2,5,13\}$, the constant coefficient in (11.4)
has the sign below and $B_i/|\gamma_{i00}|<u_i/1000$:

| $i$ | Sign of $\gamma_{i00}$ | $u_i$ |
| --- | --- | --- |
| $0$ | $-$ | $100$ |
| $1$ | $-$ | $123$ |
| $2$ | unrestricted | — |
| $3$ | $+$ | $34$ |
| $4$ | $+$ | $79$ |
| $5$ | unrestricted | — |
| $6$ | $-$ | $29$ |
| $7$ | $-$ | $3$ |
| $8$ | $-$ | $6$ |
| $9$ | $-$ | $7$ |
| $10$ | $-$ | $6$ |
| $11$ | $-$ | $1$ |
| $12$ | $-$ | $17$ |
| $13$ | unrestricted | — |
| $14$ | $+$ | $18$ |
| $15$ | $+$ | $50$ |
| $16$ | $-$ | $287$ |
| $17$ | $-$ | $39$ |
| $18$ | $-$ | $141$ |

In particular all sixteen ratios are less than $3/10$.
For the four tubes the following bounds are strict:

| $i$ | Interval containing $\det J_i$ | Upper bound $\bar\eta_i$ for $\eta_i$ | Upper bound $\bar q_i$ for $q_i$ | Interval containing $\mathcal I_i(D_m)$ |
| --- | --- | --- | --- | --- |
| $0$ | $(-15,-14)$ | $42/10^6$ | $74/1000$ | $(-49/1000,-44/1000)$ |
| $1$ | $(-1,-1/2)$ | $37/10^6$ | $282/1000$ | $(21/10000,36/10000)$ |
| $2$ | $(22,24)$ | $19/10^6$ | $7/10$ | $(15/10000,19/10000)$ |
| $3$ | $(5217,5218)$ | $4/10^7$ | $24/1000$ | $(61/1000,63/1000)$ |

Each row satisfies $\bar\eta_i+\bar q_i\rho_*<\rho_*$.
The coordinate projections of the whole tubes lie strictly inside
the following intervals; entries in the last two columns have
denominator $1000$:

| $i$ | $r$ interval numerator pair | $b$ interval numerator pair |
| --- | --- | --- |
| $0$ | $(132,142)$ | $(185,187)$ |
| $1$ | $(162,170)$ | $(144,148)$ |
| $2$ | $(872,874)$ | $(-370,-367)$ |
| $3$ | $(888,889)$ | $(-596,-595)$ |

Finally, using the exact intervals (11.9) before any coarsening,

$$
\begin{aligned}
\frac{\mathcal I_0(N_m-526D_m)}{\mathcal I_0(D_m)}
 &\subset\left(-\frac{387}{100},\frac{379}{100}\right),\\
\frac{\mathcal I_1(N_m-540D_m)}{\mathcal I_1(D_m)}
 &\subset\left(-\frac{491}{100},\frac{999}{200}\right).
\end{aligned}
\tag{11.10}
$$

Proof. Formula (11.5) expresses every entry of the first table as
a rational sum of the original integers. For each fixed-sign row,
sum the absolute values of all terms except $(a,d)=(0,0)$ after
collecting equal powers. Comparison with
$u_i|\gamma_{i00}|/1000$ gives the strict bounds in that table.
The three unrestricted rows require no comparison.

Here is an explicit coefficient formula for the remaining tables.
For $H(r,b)=\sum h_{k\ell}r^kb^\ell$, the coefficient of
$y_0^ay_1^bt^d$ in $\widehat H_i$ is

$$
\sum_{\substack{k\ge a,\ \ell\ge b,\ u+w=d\\
 0\le u\le k-a,\ 0\le w\le\ell-b}}
h_{k\ell}\binom ka\binom{k-a}{u}
(m_i)_r^{k-a-u}(L_i)_r^u
\binom\ell b\binom{\ell-b}{w}
(m_i)_b^{\ell-b-w}(L_i)_b^w.
\tag{11.11}
$$

Use the integer polynomials (3.6), taking both exact divisions by
$T$ before this expansion. Their correspondence to the original
responses can also be seen directly: substitute (3.3), (3.5) and
$\epsilon=-3K_\Lambda XN/(5D)$ into (1.5). Multiplying the fifth,
sixth-M and terminal-M expressions by $5bD$ gives respectively
$N_p,N_u,N_m$. Subtracting each stated numerator leaves the zero
polynomial after clearing $b,T,D,X,N$. For strict regular sources
these are nonzero denominators. Also (3.6) gives
$\mathsf A=5b(p-24)D+3(8b-1)H=\mathsf S_p/2$.
This fixes the source correspondence of the finite coefficients.

Evaluate the first derivatives of (11.3) at the listed $m_i,p_0,v_c$
and form the two-by-two determinants and inverses (11.6).
Equation (11.11) then gives $\widehat D_{m,i}$,
$\widehat N_{p,i}$, $\widehat N_{u,i}$ and $\widehat N_{m,i}$.
The preconditioned polynomials are explicitly

$$
\mathcal P_i=C_i
\begin{pmatrix}
(p_0+e)\widehat D_{m,i}-\widehat N_{p,i}\\
(v_c+t)\widehat D_{m,i}-\widehat N_{u,i}
\end{pmatrix}.
\tag{11.12}
$$

Collect equal monomials in (11.12), differentiate for (11.8),
and sum their absolute coefficients with the weights shown there.
The results are strictly below the displayed $\bar\eta_i,\bar q_i$.
The determinant comparisons give the four stated open intervals.
The coordinate comparisons use exactly
$[(m_i)_j-|(L_i)_j|/2-\rho_*,
  (m_i)_j+|(L_i)_j|/2+\rho_*]$.
The same coefficient sums (11.9) for $D_m$ give its guards.
Thus (3.6), (11.1), the four centre rows and (11.6), (11.11)
specify every rational number in these comparisons.

For (11.10) apply (11.11) to $N_m-526D_m$ or $N_m-540D_m$
and to $D_m$. Form their two endpoint pairs by (11.9), then take
the four endpoint quotients. All four quotients are strictly between
the indicated bounds in each row. The denominator intervals in
this operation are the uncoarsened (11.9), not their displayed
nonvanishing guards. This proves the finite inequalities. ∎

## 12. Entire two-world children on $K\times[125,126]$

**Theorem 12.1 (Two complete worlds with separated terminal-M values).**
For every real $p\in K$ and $v\in[125,126]$, the entire
$\mathcal C(p,v)$ has exactly two complete legal worlds.
In increasing order of $r$, call them $W_0,W_1$. Then

$$
522<f_{MM}(W_0)<530,\qquad
535<f_{MM}(W_1)<545,\qquad
f_{MM}(W_1)-f_{MM}(W_0)>5.
\tag{12.1}
$$

Consequently $\mathcal J(v)$ of (9.1) is false for every
$v\in[125,126]$ at the original $p_J$.

Proof. First fix any $p\in\mathcal P$, $v\in I$ for the
polynomial argument. Lemma 11.4 makes the Bernstein signs

$$
(-,-,?,+,+,?,-,-,-,-,-,-,-,?,+,+,-,-,-).
\tag{12.2}
$$

Each question mark stands alone between opposite fixed signs.
Replacing it by either sign, or by zero and omitting it, gives
one variation across those two fixed signs. There are three such
transitions and one further transition from index $15$ to $16$.
Thus the number of variations is always four. The identity

$$
(1+x)^{18}R\!\left(\frac{x}{1+x},p,v\right)
 =\sum_{i=0}^{18}\binom{18}{i}\beta_i(p,v)x^i
\tag{12.3}
$$

and Descartes' rule give at most four roots in $0<r<1$, counted
with multiplicity. This is the standard Bernstein/Descartes method
cited in Section 10, applied to this different coefficient table.
The first and last Bernstein coefficients are nonzero, so $R$ is
not the zero polynomial. The change $r=x/(1+x)$ preserves the
multiplicity of every root with $0<r<1$; no specialized degree
assumption has been made.

For each $i$, fix $e=p-p_0$ and $t=v-v_c$. The map

$$
y\longmapsto y-\mathcal P_i(y,e,t)
\tag{12.4}
$$

has Lipschitz constant at most $q_i<\bar q_i<1$ on the closed
radius-$\rho_*$ ball in $\mathbb R^2$. Its norm there is at most
$\eta_i+q_i\rho_*<\rho_*$. This is a self-map of a nonempty
complete metric space, so Banach contraction gives one fixed point
in its interior. The invertible $C_i$ makes that point exactly a
zero of the original $F_s$. Also
$\|I-\partial_y\mathcal P_i\|_\infty\le q_i<1$, so the source
Jacobian is invertible. The coordinate and denominator guards of
Lemma 11.4 give four distinct real projections in $(0,1)$,
with $D_m\ne0$, two positive and two negative $b$ values.
Banach's theorem here is the standard intermediate result of
Lebl, [Basic Analysis, Theorem 7.6.2](https://www.jirka.org/ra/html/sec_metpicard.html).

We apply the local multiplicity comparison from the proof of $F$,
Theorem 10.2, not just its bound eighteen. At a real projection
$\alpha\in(0,1)$, let $n_\alpha$ be the number of distinct
finite complex $b$ roots with $\mathsf A=\mathsf B=0$ and
$D_m\ne0$. The coefficient $[b^7]\mathsf A=5p+216$ is nonzero
on $\mathcal P$, so this number is finite, at most seven.
Their evaluation vectors in the fixed $14$ by $14$ matrix $S$
are independent. The determinant has order at least $n_\alpha$.
If $E(\alpha)=0$, Lemma 4.2 supplies one further common $b$
root with $D=0$, distinct from those counted by $n_\alpha$.
The corank is then at least $n_\alpha+1$. Since $E$ has a
simple zero there, (4.2) gives in both cases

$$
n_\alpha\le\operatorname{ord}_{r=\alpha}R(r,p,v).
\tag{12.5}
$$

This is precisely the base-factor compensation in $F$ (10.5)–(10.6).
It holds for the fixed matrices under degree drops and requires
neither a simple projected root nor $\mathcal L_1\ne0$.

Summing (12.5) over real $\alpha\in(0,1)$ gives a budget of at
most four regular complex lifts over these real projections.
The four tube points attain the budget. Therefore they are every
such point; each projection is simple and has exactly one regular
lift. In particular a negative-$b$ point consumes its projected
multiplicity and admits no hidden positive-$b$ companion, including
at a base projection. This exhausts every strict regular source
without imposing an upper bound on positive $b$ or on $r(1-r)/b$.

Now take $p\in K$. By $O$, Theorem 29.2, every legal singular
world at this fifth response has actual sixth-M response
$s_-(p)$ or $s_+(p)$. By $S$, Lemma 2.4, on the whole of $K$
these lie respectively in the rational boxes $V_-$ and $V_+$ of
$S$ (2.1), contained in $(119,120)$ and $(138,139)$.
Both are disjoint from $I$. Thus there is no singular world in
the child being classified.

Every remaining world has one regular source, and Lemma 3.3
identifies it with a zero of $F_s$. Conversely the two positive
tube points have unique complete legal lifts by that lemma.
The two negative points are auxiliary polynomial solutions only.
This proves exactly two worlds in the entire actual child.
The lift uses the unique entire interpolant (3.3) and its fixed
drift; its gain is nonzero since the first two readings are $0,24$.
No gain sample, gain leading coefficient, root difference or drift
has been divided out. Lower degrees, sampled zeros, repeated gain
roots and zero drift remain included, and the gains and drifts of
the two worlds need not agree.

On these worlds $f_{MM}=N_m/D_m$ by Lemma 3.3. The exact identity
$N_m/D_m=c+(N_m-cD_m)/D_m$ and (11.10) give, respectively,

$$
f_{MM}(W_0)\in(52213/100,52979/100),\qquad
f_{MM}(W_1)\in(53509/100,108999/200).
\tag{12.6}
$$

These imply (12.1). There is no distinct terminal-M pair in this
entire child. That excludes (9.1) irrespective of overlap between
its terminal-J and terminal-M labels, and uses no terminal-J
injectivity assertion. Proposition 2.2 permits the specialization
to the original exact $p_J$. ∎

## 13. A distinguished original-$Q$ crossing at the lower $\Phi$ root

**Definition 13.1 (The designated source and exact root bracket).**
Let $z_i(p,v)=(r_i(p,v),b_i(p,v))$ be the unique point in tube
$i$ from the proof of Theorem 12.1, for $p\in K$, $v\in I$.
The two legal lifts are the worlds with indices $0,1$ there.
Retain the original lower strict root $r_-$ of $\Phi$.
By $S$, Definition 2.3 and Lemma 2.4, with

$$
\nu_-=134815875067638653367017716061081265110899687,
\qquad
\frac{\nu_-}{10^{45}}<r_-<\frac{\nu_-+1}{10^{45}}.
\tag{13.1}
$$

This designates the original algebraic source, not a bracket centre.

**Lemma 13.2 (Derivative and endpoint inequalities for tube zero).**
The rational data (11.6) satisfy

$$
\frac8{1000}<(L_0)_r<\frac9{1000},\qquad
\max_{k=0,1}\mathcal N(\partial_t\mathcal P_{0k})
 <\frac1{5000}.
\tag{13.2}
$$

For $a\ge0$ let $\mathcal N_a$ be (11.8) with $a^d$ in
place of $2^{-d}$, and define

$$
E(t)=\max_{k=0,1}\mathcal N_{|t|}
 (\mathcal P_{0k}(0,0,e,t)).
\tag{13.3}
$$

Here the polynomial in (13.3) is expanded in $e,t$ before the
weight $|t|^d$ is assigned. Then the following comparisons hold:

$$
\begin{aligned}
\frac{E(-29/100)}{1-74/1000}&<\frac{15}{10^6},&
(m_0)_r-\frac{29}{100}(L_0)_r+\frac{15}{10^6}
 &<\frac{\nu_-}{10^{45}},\\
\frac{E(-28/100)}{1-74/1000}&<\frac{14}{10^6},&
\frac{\nu_-+1}{10^{45}}
 &<(m_0)_r-\frac{28}{100}(L_0)_r-\frac{14}{10^6}.
\end{aligned}
\tag{13.4}
$$

Proof. Use the same finite coefficient formula (11.11) and exact
$C_0,L_0$ as in Lemma 11.4. For the second comparison in (13.2),
multiply each coefficient of $\mathcal P_{0k}$ by its $t$
exponent, lower that exponent by one, then use the weights (11.8).
Both resulting sums are less than $1/5000$.
For (13.4), retain only the terms with $y_0,y_1$ exponents zero,
and replace the $t$ weight by $(29/100)^d$ or $(28/100)^d$.
After division by $1-74/1000$, the sums are strictly below the
stated $15/10^6$ and $14/10^6$. Substitution of the exact
$(m_0)_r,(L_0)_r$ and the integer $\nu_-$ gives the other two
strict rational comparisons. These are finite sums from the same
source polynomials and centre, without a new response normalization. ∎

**Theorem 13.3 (Unique designated crossing and original candidate).**
For every real $p\in K$ there is exactly one $v_\diamond(p)\in I$
such that $r_0(p,v_\diamond(p))=r_-$. It satisfies

$$
\frac{12521}{100}<v_\diamond(p)<\frac{6261}{50},\qquad
Q(p,v_\diamond(p))=0.
\tag{13.5}
$$

At the unchanged exact $p_J$, $v_\diamond=v_\diamond(p_J)$ is
real algebraic. Its entire child consists of the two separated
worlds of Theorem 12.1, so it has no distinct terminal-M pair.
It differs from both singular responses and lies outside
$[142,150]$. Uniqueness in this statement concerns the designated
branch crossing, not all roots of $Q$ in the bracket (13.5).

Proof. At every tube fixed point the source Jacobian is invertible
by (11.8). The polynomial equations are continuously differentiable
on an open ambient space. The implicit function theorem therefore
gives local continuously differentiable branches. Their fixed
points lie strictly inside the $y$ ball, so the local branches
remain in that tube for nearby parameters. Contraction uniqueness
makes these branches agree wherever they overlap. This gives a
continuously differentiable $z_0(p,v)$ on the strip, with local
extensions at its closed boundaries. These are the hypotheses of
the standard implicit function theorem cited in Section 10;
see also Lebl, [Theorem 8.5.6](https://www.jirka.org/ra/html/sec_svinvfuncthm.html).

Fix $p$ and write $z_0=m_0+L_0t+y(p,t)$, with $t=v-v_c$.
Differentiating $\mathcal P_0(y(p,t),p-p_0,t)=0$ gives

$$
\partial_t y=-(\partial_y\mathcal P_0)^{-1}
 \partial_t\mathcal P_0,\qquad
\|\partial_t y\|_\infty
 <\frac{1/5000}{1-74/1000}<\frac1{1000}.
\tag{13.6}
$$

The inverse bound is the Neumann series for
$\|I-\partial_y\mathcal P_0\|_\infty<74/1000$.
Here $dt/dv=1$, so (13.2) implies
$\partial_v r_0>7/1000$ throughout $I$.

At a fixed $t$, the fixed-point equation also gives
$\|y(p,t)\|_\infty\le E(t)+q_0\|y(p,t)\|_\infty$.
Thus (13.4) bounds this displacement by $15/10^6$ at
$t=-29/100$ and by $14/10^6$ at $t=-28/100$.
Together with (13.1), the other two comparisons in (13.4) give

$$
r_0(p,12521/100)<r_-<r_0(p,6261/50).
\tag{13.7}
$$

Continuity gives a crossing strictly between these endpoints.
Strict increase gives exactly one on the entire $I$.
Its source has $b\in(185/1000,187/1000)$ and $D_m\ne0$,
so it is regular and its $b$ differs from $1/8$.

Put $\alpha=r_-$ and $v=v_\diamond(p)$. The actual positive
$b=b_0(p,v)$ is a common root of the original $\mathsf A,\mathsf B$.
At the same $\alpha,p,v$, Lemma 4.2 supplies the distinct
common root $b=1/8$ with $D=0$, since $\Phi(\alpha)=0$.
Equation (12.5), or Lemma 4.3, gives $R(\alpha,p,v)=0$.
The base point is used as an algebraic root; its legal singular
lift has actual response $s_-(p)$, outside $I$, and is not an
additional world in this child.

In the original $12$ by $13$ matrix $S_1$ of (4.3), both vectors
$(b^{12},b^{11},\ldots,1)^{\mathsf T}$ for these two distinct
$b$ roots lie in the kernel. They are independent: their last
coordinates are $1$ and their penultimate coordinates differ.
Hence the rank is at most eleven. All $12$ by $12$ minors vanish,
in particular the original ordered $\Delta_1,\Delta_0$.
Since $\alpha\notin\{0,1\}$, the exact divisor
$72900\alpha^6(\alpha-1)^4$ is nonzero. The same quotient
polynomial of (4.3) therefore satisfies
$\mathcal L_1(\alpha,p,v)=0$.

The original $R$ and $\mathcal L_1$ have a finite common $r$ root.
Its evaluation vector annihilates the fixed padded Sylvester
matrix for $E_1=\operatorname{Res}^{18,26}_r(R,\mathcal L_1)$
in (8.2), so $E_1(p,v)=0$ and the unchanged
$Q=aE_1E_2E_3E_4$ vanishes. The fixed padding includes every
specialized degree drop. No quotient by $\mathcal L_1$, different
minor normalization, or expanded replacement for $Q$ is used.

Finally specialize to $p=p_J$. Proposition 2.2 and (13.1) make
$p_J,\alpha$ algebraic. The polynomial
$\mathsf A(\alpha,b,p_J)$ has leading coefficient $5p_J+216>0$
in degree seven, so its crossing $b$ is algebraic. Since $D_m$
is nonzero there, its actual acquired response $N_u/D_m$ is
algebraic. This proves algebraicity at the exact $p_J$, without
asserting it for arbitrary real $p$. The bracket (13.5) is inside
$I$ and disjoint from both singular-response boxes and from
$[142,150]$. Theorem 12.1 supplies the claimed entire-child
exclusion. ∎

## 14. The residual domain for the original joint predicate

**Corollary 14.1 (Equivalent remaining original obligation).**
For the unchanged predicate $\mathcal J$ of (9.1), set

$$
\begin{aligned}
\mathcal V_{\rm old}
 &=\{v\in\mathbb R:Q(p_J,v)=0\}
   \setminus\bigl([142,150]\cup\{s_-(p_J),s_+(p_J)\}\bigr),\\
\mathcal V_{\rm rem}
 &=\{v\in\mathbb R:Q(p_J,v)=0\}
   \setminus\bigl([125,126]\cup[142,150]
                  \cup\{s_-(p_J),s_+(p_J)\}\bigr).
\end{aligned}
\tag{14.1}
$$

Then

$$
\exists v\in\mathbb R\;\mathcal J(v)
\quad\Longleftrightarrow\quad
\exists v\in\mathcal V_{\rm rem}\;\mathcal J(v),\qquad
v_\diamond\in\mathcal V_{\rm old}\setminus\mathcal V_{\rm rem}.
\tag{14.2}
$$

Every world in any hypothetical witness child on the right is
regular. The assertion still requires a distinct terminal-J pair
and a distinct terminal-M pair in the same entire acquired child;
labels may coincide across the pairs.

Proof. By $S$, Corollary 9.1, a witness to (9.1) has $Q(p_J,v)=0$,
misses the two singular responses, and has no singular world in
its entire child. Theorem 1.3 excludes $[142,150]$ and Theorem
12.1 excludes $[125,126]$. This proves the forward implication;
the reverse merely restricts the quantified set of real responses.
Theorem 13.3 puts the exact $v_\diamond$ in the old necessary set
and in the newly excluded strip. Thus (14.2) deletes at least this
specified member of that necessary set, even though a root of $Q$
alone need not supply a collision. ∎

**Definition 14.2 (Unresolved quantifiers and mathematical attribution).**
The remaining question in (14.2) is unresolved: no remaining
candidate, actual distinct terminal-M pair, or compatible same-child
terminal-J pair is classified here. The original positive source
coordinates remain unbounded, with one entire nonzero real gain of
degree at most three and one fixed real drift per world, all the
specializations of Definition 1.1, and one actual history without
additional observations, resets or copies.

The source-specific content of Sections 11–14 is repository-derived:
the finite coefficient inequalities on this second strip, their
exhaustion into two complete worlds, and the designated lower-$\Phi$
crossing with its residual-domain consequence. Bernstein/Descartes,
Banach contraction, Neumann inversion, implicit differentiation and
Sylvester elimination are the known intermediate methods cited in
Section 10 and in the corresponding proofs. The local multiplicity
comparison is reused from $F$, Theorem 10.2. The singular-response
enclosures and entire singular-child exclusions are supplied by
$S$, Lemma 2.4 and Corollary 9.1; the original model, parameter,
polynomials and determinant identities are supplied by $O$ at the
interfaces fixed above. These are ordinary conditional mathematical
suppliers. The conclusions do not assert global joint exclusion,
an enumeration or improved bound on actual collision pairs,
terminal-J injectivity, a universal optimal protocol, kernel
verification, physical realization or worldwide priority.
