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

