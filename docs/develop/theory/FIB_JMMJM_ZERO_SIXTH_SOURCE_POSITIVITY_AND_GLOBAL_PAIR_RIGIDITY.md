# FIB JMMJM Zero-Sixth Source Positivity and Global Pair Rigidity

## 1. Complete worlds and the common literal history

A legal complete world is $W=(P,g,\delta)$, where $P$ is a strictly
entrywise positive real $2\times2$ matrix of rank one and trace one,
$g\in\mathbb R[T]\setminus\{0\}$ has degree at most three, and
$\delta\in\mathbb R$. No source symmetry is imposed. Both gain signs,
all lower degrees, sampled roots and repeated roots are allowed.
Put

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{J,M\}.
\tag{1.1}
$$

The original-clock reading is $g(i)\operatorname{tr}(A_iP)+\delta$.
The initial reading counts. Each selected atom is immediately read on
one unresettable, uncopyable trajectory. Chronological $EF$ acts by
$FE$ and includes both immediate readings. Policies, stops and answers
may be arbitrary deterministic functions of the entire actual history,
without regularity or computability assumptions. Recovery means
recovery of the entire $(P,g,\delta)$.

For arbitrary fixed $D_0,Y,z\in\mathbb R$ and $\lambda\ne0$, fix

$$
H=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
                M,D_0+312\lambda/5,J,Y,M,z).
\tag{1.2}
$$

Write $\mathcal F(H)$ for all legal complete worlds realizing its six
readings. Thus the word is literally $JMMJM$. Define

$$
f=g/\lambda,\quad d=(\delta-D_0)/\lambda,\quad
y=(Y-D_0)/\lambda,\quad \zeta=(z-D_0)/\lambda,\qquad
\mathbf c=(0,24,48,312/5,y,\zeta).
\tag{1.3}
$$

The inverse is $g=\lambda f$, $\delta=D_0+\lambda d$.
The response map $w\mapsto D_0+\lambda w$ is a bijection of all real
values for either sign of $\lambda$. It preserves every equality and
actual retained set. In particular $D_0$ need not equal $\delta$.

Use source coordinates

$$
P=\begin{pmatrix}s&p\\q&1-s\end{pmatrix},\qquad
0<s<1,\quad p,q>0,\quad pq=s(1-s),
\qquad u=p+q,\quad v=1+p.
\tag{1.4}
$$

These conditions are exactly source legality. Source coordinates
$s,p,q$ will remain distinct from the terminal-matrix entries
$a,b,c,e$ below. The cumulative matrices are

$$
\begin{gathered}
(A_0,\ldots,A_5)=(I,J,L,J+L,C_{\rm mat},Q),\\
L=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
J+L=\begin{pmatrix}1&1\\2&1\end{pmatrix},\quad
C_{\rm mat}=\begin{pmatrix}2&1\\1&1\end{pmatrix},\\
Q=\begin{pmatrix}1&1\\3&2\end{pmatrix},\qquad
Q^{-1}=\begin{pmatrix}-2&1\\3&-1\end{pmatrix}.
\end{gathered}
\tag{1.5}
$$

Consequently the complete ancestor equations on each same world are

$$
\begin{aligned}
f(0)+d&=0,\\
u f(1)+d&=24,\\
v f(2)+d&=48,\\
(u+v)f(3)+d&=312/5,\\
(1+s+u)f(4)+d&=y,\\
(u+2v-s)f(5)+d&=\zeta.
\end{aligned}
\tag{1.6}
$$

Write $t=(1,u,v,u+v,1+s+u,u+2v-s)$. Every $t_j$ is positive.
For arbitrary but fixed common $d$, let

$$
\mathcal K_{\mathbf c,d}
=\{W\in\mathcal F(H):(\delta-D_0)/\lambda=d,\ f(6)=0,\ f(7)\ne0\}.
\tag{1.7}
$$

The same $y,\zeta,d$ are used for every member. There is no cardinality,
source-sum, gain-shape or terminal-sign restriction on this class.
The sixth and seventh sample promises are not labels obtained from $H$.

We also distinguish two auxiliary source domains:

$$
\begin{aligned}
\mathcal N&=\{P:0\le s\le1,\ p,q\ge0,\ p+q>0\},\\
\mathcal N_1&=\{P\in\mathcal N:pq=s(1-s)\}.
\end{aligned}
\tag{1.8}
$$

Here $P$ always has the form in (1.4). Rank one is required in
$\mathcal N_1$ and need not hold in $\mathcal N$.
All six traces are positive on $\mathcal N$, since $v\ge1$,
$t_4\ge1+u$ and $t_5\ge u+1$. A member of $\mathcal N_1$ is a legal
physical source only when it is strictly positive.

The model is that of
[IX, Definitions 1.1–1.4](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md).
We use the permanent predecessor
[Pair injectivity, Sections 1–5](FIB_JMMJM_ZERO_SIXTH_PAIR_INJECTIVITY_AND_JOINT_COLLISION_OBSTRUCTIONS.md),
abbreviated Pairs, at its exact whole-class scope.

## 2. Interpolation and the exact source-conditioned graph

Put

$$
q_0=-d,\quad q_1=(24-d)/u,\quad q_2=(48-d)/v,\quad
q_3=(312/5-d)/(u+v).
\tag{2.1}
$$

The symbol $q_j$ denotes gain samples; $q$ without a subscript is the
source entry. All divisions in (2.1) are by positive traces.
The four Lagrange polynomials and their full increasing-power rows are

$$
\begin{array}{c|c|c}
j&\ell_j(T)&([T^0],[T^1],[T^2],[T^3])\\ \hline
0&-(T-1)(T-2)(T-3)/6&(1,-11/6,1,-1/6)\\
1&T(T-2)(T-3)/2&(0,3,-5/2,1/2)\\
2&-T(T-1)(T-3)/2&(0,-3/2,2,-1/2)\\
3&T(T-1)(T-2)/6&(0,1/3,-1/2,1/6).
\end{array}
\tag{2.2}
$$

Expansion of the displayed products gives every coefficient, and
$\ell_j(k)$ at $k=0,1,2,3$ is the interpolation identity. Thus

$$
f=\sum_{j=0}^3q_j\ell_j,\qquad
[f]=\left(q_0,-\frac{11}6q_0+3q_1-\frac32q_2+\frac13q_3,
q_0-\frac52q_1+2q_2-\frac12q_3,
-\frac16q_0+\frac12q_1-\frac12q_2+\frac16q_3\right).
\tag{2.3}
$$

Two polynomials of degree at most three with those four samples have
four distinct roots in their difference and hence coincide.
Substitution in (2.2) gives all sixteen entries of

$$
\begin{pmatrix}f(4)\\f(5)\\f(6)\\f(7)\end{pmatrix}
=
\begin{pmatrix}
-1&4&-6&4\\
-4&15&-20&10\\
-10&36&-45&20\\
-20&70&-84&35
\end{pmatrix}
\begin{pmatrix}q_0\\q_1\\q_2\\q_3\end{pmatrix}.
\tag{2.4}
$$

The coefficient and evaluation identities include all degree drops.

For comparison with the exact full fiber, define on $\mathcal N$

$$
\begin{aligned}
V_P&=\sum_{j=0}^3\ell_j/t_j,&
U_{P;\mathbf c}&=\sum_{j=0}^3c_j\ell_j/t_j,\\
\alpha_i&=1-t_iV_P(i),&
\beta_i&=c_i-t_iU_{P;\mathbf c}(i)\quad(i=4,5),\\
\Delta&=\alpha_4^2+\alpha_5^2,&
\mathcal C&=\alpha_4\beta_5-\alpha_5\beta_4.
\end{aligned}
\tag{2.5}
$$

[IX, Theorem 2.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md)
establishes, on all of $\mathcal N$,

$$
\alpha_4=0\ \Longrightarrow\
V_P(5)>V_P(3)=1/t_3\ge1/t_5,\quad\alpha_5<0;
\qquad \Delta>0.
\tag{2.6}
$$

This does not require rank one. Reuse its nonvanishing theorem and put

$$
d_P=\frac{\alpha_4\beta_4+\alpha_5\beta_5}{\Delta},\qquad
f_P=U_{P;\mathbf c}-d_PV_P.
\tag{2.7}
$$

The first four equations give $f=U-dV$; the actual last two are
$\alpha_i d=\beta_i$. Direct subtraction yields

$$
\begin{pmatrix}\beta_4\\\beta_5\end{pmatrix}
-d_P\begin{pmatrix}\alpha_4\\\alpha_5\end{pmatrix}
=\frac{\mathcal C}{\Delta}
       \begin{pmatrix}-\alpha_5\\\alpha_4\end{pmatrix}.
\tag{2.8}
$$

Hence compatibility is exactly $\mathcal C=0$, and the pair $(f,d)$
is then unique for a supplied $P$, as in IX, Theorem 3.1. Its
source-conditioned rank-five statement uses the first-four Vandermonde
determinant $12t_0t_1t_2t_3$ and the nonzero residual column
$(0,0,0,0,\alpha_4,\alpha_5)^{\mathsf T}$. No choice of a possibly
zero $\alpha_i$ as divisor is needed. In particular

$$
\mathcal Z_{\mathbf c,d}
=\{P\text{ legal}:\mathcal C(P;\mathbf c)=0,\ d_P=d,\
                     f_P(6)=0,\ f_P(7)\ne0\}
\tag{2.9}
$$

maps bijectively to $\mathcal K_{\mathbf c,d}$ by

$$
P\longmapsto(P,\lambda f_P,D_0+\lambda d).
\tag{2.10}
$$

The reconstructed gain is nonzero because the readings zero and 24
differ. Distinct complete worlds therefore have distinct sources.
This is conditional recovery once $P$ is supplied, not identification
of the unknown $P$ by the ancestor. Both actual late equations remain
in (2.9).

## 3. Fourth-gain positivity from rank one

**Theorem 3.1.** Suppose $P\in\mathcal N_1$, the first four actual
normalized readings are $(0,24,48,312/5)$, $\deg f\le3$, and $f(6)=0$.
Then

$$
0\le d\le24\quad\Longrightarrow\quad f(4)>0.
\tag{3.1}
$$

This statement needs no seventh-gain promise. If both late readings
are present, their actual fourth equation consequently gives $y>d$.

**Proof.** The $f(6)$ evaluation row of (2.4) gives

$$
0=10d+36q_1-45q_2+20q_3.
\tag{3.2}
$$

Substitution into the $f(4)$ evaluation row gives

$$
f(4)=d+4q_1-6q_2+4q_3=-d-\frac{16}5q_1+3q_2.
\tag{3.3}
$$

Indeed $4q_3=-2d-(36/5)q_1+9q_2$. Set $r=u/v>0$.
Multiplication of (3.2) by $v>0$ gives

$$
10dv=45(48-d)-\frac{36(24-d)}r
                         -\frac{20(312/5-d)}{r+1}.
\tag{3.4}
$$

Assume $f(4)\le0$. Equation (3.3) then requires

$$
dv\ge3(48-d)-\frac{16(24-d)}{5r}.
\tag{3.5}
$$

Using (3.4), this implies

$$
0\le\frac32(48-d)-\frac{2(24-d)}{5r}
                              -\frac{2(312/5-d)}{r+1}.
\tag{3.6}
$$

The multiplier $10r(r+1)$ is positive. Thus $P_d(r)\ge0$, where

$$
\begin{aligned}
P_d(r)
 &=15(48-d)r(r+1)-4(24-d)(r+1)-20(312/5-d)r\\
 &=15(48-d)r^2+(9d-624)r+4(d-24).
\end{aligned}
\tag{3.7}
$$

The full increasing-power coefficient row is
$(4d-96,9d-624,720-15d)$: the linear coefficient is
$(720-15d)+(-96+4d)+(-1248+20d)=9d-624$.
On $0\le d\le24$, write $A_d=15(48-d)>0$. Then

$$
P_d(0)=4(d-24)\le0,\quad P_d(1)=-2d\le0,\qquad
P_d(r)=(1-r)P_d(0)+rP_d(1)-A_dr(1-r).
\tag{3.8}
$$

The last identity makes $P_d(r)<0$ for $0<r<1$.
For $d>0$ it is also negative at $r=1$. Therefore the necessary
$P_d(r)\ge0$ forces $r>1$ if $0<d\le24$, and $r\ge1$ if $d=0$.
Both drift endpoints, including the vanishing constant coefficient
at $d=24$, are retained.

First take $d=0$, before dividing by $d$. For $r\ge1$ the right side
of (3.4) is at least

$$
45\cdot48-36\cdot24-10(312/5)=2160-864-624=672>0,
\tag{3.9}
$$

contrary to its zero left side. Now let $0<d\le24$. Since $r>1$,
$24-d\ge0$ and $312/5-d>0$, that right side is strictly greater than

$$
45(48-d)-36(24-d)-10(312/5-d)=672+d.
\tag{3.10}
$$

The strictness still holds at $d=24$ through the last term. Hence,
dividing only by the now positive $10d$,

$$
v>\frac{672+d}{10d}\ge\frac{29}{10},
\tag{3.11}
$$

where the last inequality is $672\ge28d$. But $r>1$ gives
$u>v$, so $p+q>1+p$ and $q>1$. Also $p=v-1>19/10$.
Thus $pq>19/10>1/4$, contradicting
$pq=s(1-s)\le1/4$. This proves (3.1), including all permitted
nonnegative source entries. Positivity of $t_4$ in the actual
fourth equation then gives $y>d$. ∎

This rank-one conclusion is stronger than an inequality on arbitrary
positive trace coordinates. The determinant bound is its final
essential constraint; no common source sum, gain ratio or leading
coefficient has been assumed.

## 4. Consequences at the fixed history H*

Set

$$
H_*=(0,J,24,M,48,M,312/5,J,48/5,M,-532/5).
\tag{4.1}
$$

**Corollary 4.1.** No complete zero-sixth world on $H_*$ has
$d\in[48/5,24]$. This holds also for sources in $\mathcal N_1$
and without assuming $f(7)\ne0$.

Indeed the actual fourth equation would give
$f(4)=(48/5-d)/t_4\le0$, contradicting Theorem 3.1.
The sampled fourth root at $d=48/5$ and sampled first root at $d=24$
are both covered.

**Proposition 4.2.** There is no complete zero-sixth world on $H_*$
with $d=0$, also on $\mathcal N_1$ and without a seventh promise.

**Proof.** Both actual late equations are used here. At $d=0$ they
give $f(4)>0$ and $f(5)<0$. The first four give $f(0)=0$ and
$f(1),f(2),f(3)>0$. With $f(6)=0$, the intermediate value theorem
supplies a third distinct root $\tau\in(4,5)$.
A nonzero polynomial of degree at most three must therefore be

$$
f(T)=kT(T-\tau)(T-6),\qquad
[f]=k(0,6\tau,-(\tau+6),1).
\tag{4.2}
$$

Its clock-one product is positive, so $k>0$. All three roots are
simple, and lower degrees are excluded by these three distinct roots.
The samples at one, two and three are respectively
$5k(\tau-1)$, $8k(\tau-2)$ and $9k(\tau-3)$.
Since $t_3=t_1+t_2$,

$$
\frac{24}{5k(\tau-1)}+\frac{48}{8k(\tau-2)}
                  =\frac{312/5}{9k(\tau-3)}.
\tag{4.3}
$$

Here $k>0$ and $\tau>4$ justify all divisions. Multiplication by
$15k(\tau-1)(\tau-2)(\tau-3)>0$ gives

$$
\begin{aligned}
0={}&72(\tau-2)(\tau-3)+90(\tau-1)(\tau-3)
                                      -104(\tau-1)(\tau-2)\\
={}&72(\tau^2-5\tau+6)+90(\tau^2-4\tau+3)
                                      -104(\tau^2-3\tau+2)\\
={}&2(29\tau^2-204\tau+247).
\end{aligned}
\tag{4.4}
$$

The inner quadratic has full row $(247,-204,29)$, values $-105$
and $-48$ at four and five, and derivative $58\tau-204>0$ on
$[4,5]$. It stays strictly negative there. This contradicts (4.4). ∎

For completeness, finite nonnegative rank-one trace-one sources with
$u=0$ have $p=q=0$, $s=0$ or $1$. Clock one forces $d=24$.
With $q_1=f(1)$ now treated as an independent sample, the other samples
are $f(0)=-24$, $f(2)=24$, $f(3)=192/5$.
Interpolation gives $f(4)=168/5+4q_1$ and $f(5)=15q_1$.
The two possible actual late pairs are

$$
\begin{array}{c|cc}
s&y&\zeta\\ \hline
0&288/5+4q_1&24+30q_1\\
1&456/5+8q_1&24+15q_1.
\end{array}
\tag{4.5}
$$

At $y=48/5$, these force $q_1=-12$ or $-51/5$ and then
$\zeta=-336$ or $-129$. Neither equals $-532/5$; the differences
$-532/5-\zeta$ are $1148/5$ and $113/5$. Thus there is no omitted
finite $u=0$ complete $H_*$ world, even without the sixth promise.

## 5. Signed terminal coordinates and reused pair injections

For any world in (1.7), define terminal coordinates by

$$
X=f(7)QP=\begin{pmatrix}a&b\\c&e\end{pmatrix},\qquad
S=Q^{-1}X=f(7)P,\qquad h=f/f(7),\qquad
\sigma_j=\operatorname{tr}(A_jS)=f(7)t_j.
\tag{5.1}
$$

Every entry of $X$ is nonzero with the sign of $f(7)$, $ae=bc$,
and every $\sigma_j$ is nonzero with that sign. Both terminal signs
are permitted. We have

$$
\deg h\le3,\quad h(6)=0,\quad h(7)=1,\qquad
h(j)\sigma_j=c_j-d\quad(0\le j\le5).
\tag{5.2}
$$

The two sixth predictions are both $d$. The alternative seventh
predictions in chronological order are

$$
\begin{array}{c|c|c}
EF&FE&r_{EF}=d+\operatorname{tr}(FEX)\\ \hline
JJ&I&A=d+a+e\\
JM&\begin{pmatrix}1&0\\1&1\end{pmatrix}&B=d+a+b+e\\
MJ&\begin{pmatrix}1&1\\0&1\end{pmatrix}&C=d+a+c+e\\
MM&\begin{pmatrix}1&1\\1&2\end{pmatrix}&D=d+a+b+c+2e.
\end{array}
\tag{5.3}
$$

These follow from $J^2$, $MJ$, $JM$ and $M^2$, respectively.
They are mathematical functions on fixed candidates; only one of
the chronological words is executed on a trajectory.

Direct multiplication gives

$$
S=\begin{pmatrix}-2a+c&-2b+e\\3a-c&3b-e\end{pmatrix},
\qquad
\begin{pmatrix}\sigma_0\\\sigma_1\\\sigma_2\\\sigma_3\\\sigma_4\\\sigma_5\end{pmatrix}
=
\begin{pmatrix}
-2&3&1&-1\\
3&-2&-1&1\\
-2&1&1&0\\
1&-1&0&1\\
-1&1&1&0\\
1&0&0&1
\end{pmatrix}
\begin{pmatrix}a\\b\\c\\e\end{pmatrix}.
\tag{5.4}
$$

The six traces are $-2a+3b+c-e$, $3a-2b-c+e$, $-2a+b+c$,
$a-b+e$, $-a+b+c$, $a+e$: taking traces against the six matrices
in (1.5) verifies all 24 coefficients. In particular

$$
\sigma_3=\sigma_1+\sigma_2.
\tag{5.5}
$$

If two worlds have the same $X$, then their $S$ coincide.
Taking traces recovers the same nonzero $f(7)$ because
$\operatorname{tr}P=1$, and division recovers the same $P$.
At common $d$, the first four positive trace factors give equal
gain samples, so (2.3) recovers the same entire $f$ and original world.
This is complete-target reconstruction, including degree drops
and multiplicities. Equality of any terminal scalar at common $d$
also forces the two terminal gains to have the same sign: its offset
from $d$ is $f_i(7)$ times a positive trace.
Thus $\sigma_{1,j}\sigma_{2,j}>0$ for a colliding pair.

Write $\Delta X=X_2-X_1$ and $\Delta\sigma=\sigma_2-\sigma_1$.
Solving the equalities in (5.3) and using (5.4) gives

$$
\begin{array}{c|c|l}
\text{pair}&\Delta X&(\Delta\sigma_0,\ldots,\Delta\sigma_5)\\ \hline
AB&\begin{pmatrix}-\epsilon&0\\\gamma&\epsilon\end{pmatrix}
 &(\epsilon+\gamma,-2\epsilon-\gamma,2\epsilon+\gamma,0,\epsilon+\gamma,0)\\
AD&\begin{pmatrix}-\epsilon&\beta\\-\epsilon-\beta&\epsilon\end{pmatrix}
 &(2\beta,-\beta-\epsilon,\epsilon,-\beta,0,0)\\
AC&\begin{pmatrix}-\epsilon&\beta\\0&\epsilon\end{pmatrix}
 &(\epsilon+3\beta,-2\epsilon-2\beta,2\epsilon+\beta,-\beta,\epsilon+\beta,0).
\end{array}
\tag{5.6}
$$

Here equal $A$ gives $\Delta a=-\Delta e=-\epsilon$;
$AB$ adds $\Delta b=0$; $AD$ adds $\Delta c=-\epsilon-\beta$;
$AC$ adds $\Delta c=0$. Substitution into all six rows of (5.4)
gives every displayed difference, including both late rows.

**Proposition 5.1 (Pairs, Theorem 4.1).** For every fixed
$\mathbf c,d$, the maps $AB$ and $AD$ are injective on the entire
$\mathcal K_{\mathbf c,d}$. There is no source-sum, shape, cardinality
or sign hypothesis.

The following proof records the reused interface. For $AB$, clocks
three and five have equal nonzero $\sigma$, so (5.2) gives equal
$h$ values there. Along with six and seven, four distinct roots
force $h_1=h_2=h$. Clocks one and two then give

$$
h(1)(-2\epsilon-\gamma)=0,\qquad h(2)(2\epsilon+\gamma)=0.
\tag{5.7}
$$

Their samples cannot both vanish, as that would force $d=24=48$.
Hence $\gamma=-2\epsilon$. If $\epsilon\ne0$, clocks zero and four
force $h(0)=h(4)=0$ and $d=0$. The other two normalized samples force

$$
h(T)=T(T-4)(T-6)/21,\quad
[h]=(0,24/21,-10/21,1/21),
\quad (h(1),h(2),h(3))=(5/7,16/21,3/7).
\tag{5.8}
$$

Consequently $(\sigma_1,\sigma_2,\sigma_3)=(168/5,63,728/5)$,
whereas (5.5) requires $\sigma_3=483/5$, a discrepancy of 49.
Thus $\epsilon=\gamma=0$ and the worlds agree.

For $AD$, equal nonzero $\sigma$ at four and five gives common
$h$ through the four nodes $4,5,6,7$. If $\beta\ne0$, clocks
zero and three force $d=0=312/5$, impossible. Thus $\beta=0$.
If $\epsilon\ne0$, clocks one and two force $d=24=48$.
All parameters therefore vanish, proving the proposition.
No ancestor gain was canceled without first proving it nonzero. ∎

## 6. The exhaustive predecessor AC alternatives

**Proposition 6.1 (Pairs, Theorem 5.1).** A distinct $AC$ collision
in $\mathcal K_{\mathbf c,d}$ must satisfy exactly one of the
following necessary alternatives:

$$
\begin{array}{ll}
\mathrm{I}:&0<d<24,\quad y<d,\quad\zeta<d,\\
\mathrm{II}:&24<d<48,\quad y>d.
\end{array}
\tag{6.1}
$$

In I, every world on the entire same-ancestor common-$d$ zero-sixth
slice is exactly cubic with three simple roots
$\rho_0\in(0,1)$, $\tau_0\in(3,4)$ and six, and with positive
normalized leading coefficient and positive $f(7)$.
In II every sixth root on that entire slice is simple.
Neither alternative asserts existence. No additional terminal-sign
claim belongs to II.

Here is the exhaustive difference certificate used from Pairs.
In the $AC$ row of (5.6), $\epsilon=0$ would leave common $a,c,e$;
the nonzero common $c$ and $ae=bc$ would give common $b$.
Distinctness thus proves $\epsilon\ne0$. Equal $A$ gives equal
nonzero $\sigma_5$, and the actual fifth equation yields
$h_1(5)=h_2(5)$, even at a fifth gain root. Therefore

$$
h_2-h_1=kR_5,\qquad
R_5=(T-5)(T-6)(T-7)=T^3-18T^2+107T-210.
\tag{6.2}
$$

Its full coefficient row is $(-210,107,-18,1)$ and its sample row
at $0,\ldots,7$ is $(-210,-120,-60,-24,-6,0,0,0)$.
If $k=0$, the common $h$ and clocks one and two force
$\epsilon+\beta=2\epsilon+\beta=0$ when $d\notin\{24,48\}$.
At $d=24$, use clocks zero and two to obtain
$\epsilon+3\beta=2\epsilon+\beta=0$.
At $d=48$, use clocks zero and one to obtain
$\epsilon+3\beta=\epsilon+\beta=0$.
Each case gives equal matrices, a contradiction. Thus $k\ne0$.
For $0\le j\le4$, neither $c_j-d$ nor $\Delta\sigma_j$ can vanish:
either would make the two $h(j)$ equal, contrary to (6.2).
In particular

$$
d\notin\{0,24,48,312/5,y\}.
\tag{6.3}
$$

Only now put $\theta=\beta/\epsilon$. Then

$$
\Delta\sigma=\epsilon F,\qquad
F=(1+3\theta,-2(1+\theta),2+\theta,-\theta,1+\theta,0),
\quad \theta\notin\{-2,-1,-1/3,0\}.
\tag{6.4}
$$

The common $A-d$ forces equal terminal-gain signs. Subtracting the
two actual equations in their divided-by-trace form gives

$$
kR_5(j)=-\frac{(c_j-d)\epsilon F_j}
                      {\sigma_{1,j}\sigma_{2,j}},\qquad
\operatorname{sgn}(k/\epsilon)
 =\operatorname{sgn}((c_j-d)F_j)\quad(0\le j\le4).
\tag{6.5}
$$

The denominator is positive and $R_5(j)<0$ at all these nodes.
All signs of the five nonzero entries of $F$ are

| $\theta$ interval | $(F_0,F_1,F_2,F_3,F_4)$ | Negative of the first four |
| --- | --- | --- |
| $\theta<-2$ | $(-,+,-,+,-)$ | $(+,-,+,-)$ |
| $-2<\theta<-1$ | $(-,+,+,+,-)$ | $(+,-,-,-)$ |
| $-1<\theta<-1/3$ | $(-,-,+,+,+)$ | $(+,+,-,-)$ |
| $-1/3<\theta<0$ | $(+,-,+,+,+)$ | $(-,+,-,-)$ |
| $\theta>0$ | $(+,-,+,-,+)$ | $(-,+,-,+)$ |

Every entry follows from the displayed linear factors. The complete
possible first-four residual sign rows, after (6.3), are

$$
\begin{array}{c|c}
d&\operatorname{sgn}(c_0-d,c_1-d,c_2-d,c_3-d)\\ \hline
d<0&(+,+,+,+)\\
0<d<24&(-,+,+,+)\\
24<d<48&(-,-,+,+)\\
48<d<312/5&(-,-,-,+)\\
d>312/5&(-,-,-,-).
\end{array}
\tag{6.6}
$$

Only the second and third $F$ rows match, and none of the negative
rows matches. Thus $k/\epsilon>0$ and either
$-2<\theta<-1$, $0<d<24$, or
$-1<\theta<-1/3$, $24<d<48$.
The clock-four identity gives $(y-d)(1+\theta)>0$, yielding the
stated strict $y$ inequalities. No condition $d\ne\zeta$ is imposed.

For the entire-slice assertion in I, every such world has
$f(0)<0$, $f(1),f(2),f(3)>0$ and $f(4)<0$.
The intermediate value theorem gives roots in $(0,1)$ and $(3,4)$,
besides six. The degree bound forces
$f(T)=\kappa(T-\rho_0)(T-\tau_0)(T-6)$ with exactly three simple
roots. At three the factor product is positive, so $\kappa>0$;
at five it is negative, and at seven positive. The actual fifth
equation therefore gives $\zeta<d$ and $f(7)>0$.
For II, the reused repeated-sixth theorem
[G, Theorem 2.1](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md)
permits a repeated sixth root on this exact ancestor only when
$d<0$, $0<d<24$ or $48<d<312/5$. Hence all sixth roots in II
are simple. The large repeated-root certificate is not needed
for either new exclusion below.

## 7. A legal-source trace obstruction to the second alternative

**Lemma 7.1.** For a legal source in the chart

$$
\frac13<x<\frac12,\quad \rho>0,\quad
t=\frac{3x-1}{1-2x}>0,\qquad
P=\frac1{1+\rho t}\begin{pmatrix}1&\rho\\t&\rho t\end{pmatrix},
\tag{7.1}
$$

suppose $x+1/3<\rho<3/2$. Let $Z_P(D)$ be the sixth value of
the first-four-reading interpolant at drift $D$. Then
$Z_P(D)<0$ for every $D\in[24,48]$.

**Chart conversions.** For a legal terminal matrix (5.1), put

$$
x=b/e=a/c,\quad \rho=e/c,\qquad
S=\begin{pmatrix}c(1-2x)&e(1-2x)\\c(3x-1)&e(3x-1)\end{pmatrix}.
\tag{7.2}
$$

The ratios are positive. Since $S=f(7)P$ and $c,e$ have the sign
of $f(7)$, strict positivity gives exactly $1/3<x<1/2$.
Taking the trace normalizes (7.2) to (7.1).
Conversely (7.1) has positive entries, trace one and determinant zero.
Its full conversions are

$$
\begin{gathered}
x=(t+1)/(2t+3),\quad s=1/(1+\rho t),\quad
p=\rho/(1+\rho t),\quad q=t/(1+\rho t),\\
j=u=\frac{\rho+t}{1+\rho t},\qquad
\ell=v=\frac{1+\rho+\rho t}{1+\rho t},\qquad
m=u+v=\frac{2\rho+1+(\rho+1)t}{1+\rho t}.
\end{gathered}
\tag{7.3}
$$

All denominators are positive; the ratios in (7.2) cancel either
terminal sign. The symbol $t$ in this chart is a scalar parameter,
whereas $t_j$ always denotes an ancestor trace.

**Proof of the trace lemma.** From (2.4),

$$
Z_P(D)=10D+\frac{36(24-D)}j-\frac{45(48-D)}\ell
                              +\frac{20(312/5-D)}m.
\tag{7.4}
$$

This is affine in $D$, and $Z_P(d)=f(6)$ for an actual world.
At $D=24$,

$$
Z_P(24)=240-1080/\ell+768/m,
\tag{7.5}
$$

and multiplication by $\ell m/24>0$ gives

$$
(10p-35)(1+2p+q)+32(1+p)
             =20p^2-28p-3+(10p-35)q.
\tag{7.6}
$$

Here $0<p<\rho<3/2$ and $q>0$.
The convex quadratic $20p^2-28p-3$ has endpoint values $-3$ and
$0$ on $[0,3/2]$; its chord is strictly negative in the interior,
and the quadratic lies below it. Also $10p-35<0$.
Thus (7.6) is strictly negative and $Z_P(24)<0$.

At $D=48$, let

$$
s_0=1+\rho t,\quad j_N=\rho+t,\quad
m_N=2\rho+1+(\rho+1)t.
$$

These three quantities are positive. Clearing only these denominators
in $Z_P(48)=480-864/j+288/m$ gives

$$
Z_P(48)=\frac{96N}{j_Nm_N},\qquad
N=5j_Nm_N-9s_0m_N+3s_0j_N.
\tag{7.7}
$$

The complete increasing-power-in-$t$ coefficient rows are

$$
\begin{array}{c|ccc}
&[t^0]&[t^1]&[t^2]\\ \hline
5j_Nm_N&10\rho^2+5\rho&5\rho^2+15\rho+5&5\rho+5\\
-9s_0m_N&-18\rho-9&-18\rho^2-18\rho-9&-9\rho^2-9\rho\\
3s_0j_N&3\rho&3+3\rho^2&3\rho\\ \hline
N&10\rho^2-10\rho-9&-10\rho^2-3\rho-1&-9\rho^2-\rho+5.
\end{array}
\tag{7.8}
$$

Multiplication of the two linear factors in each of the first three
rows and columnwise addition proves every entry.

The lower chart inequality becomes

$$
\rho>\frac{5t+6}{6t+9}>\frac23.
\tag{7.9}
$$

If $2/3<\rho<7/10$, then $5-6\rho>0$ and

$$
0<t<\frac{9\rho-6}{5-6\rho}<\frac38.
\tag{7.10}
$$

The last bound uses $9\rho-6<3/10$ and $5-6\rho>4/5$.
In this subcase the constant coefficient of $N$ is below $-9$,
its linear coefficient is negative, and its quadratic coefficient
is at most $1/3$, by

$$
(-9\rho^2-\rho+5)-1/3=-(\rho-2/3)(9\rho+7)\le0.
\tag{7.11}
$$

Consequently

$$
N<-9+\frac13(3/8)^2=-573/64<0.
\tag{7.12}
$$

This bound is valid even if the quadratic coefficient is negative.
If $7/10\le\rho<3/2$, convexity bounds the constant coefficient
by the larger of its endpoint values $-111/10$ and $-3/2$ on
$[7/10,3/2]$, hence by $-3/2$.
The linear coefficient is negative. The quadratic coefficient is
at most $-11/100$, its value at $7/10$, because its difference is

$$
-(\rho-7/10)\bigl(9(\rho+7/10)+1\bigr)\le0.
\tag{7.13}
$$

Thus all three coefficients are strictly negative and $N<0$.
The equality $\rho=7/10$ belongs to this second subcase.
This proves $Z_P(48)<0$ on the whole lemma domain.
For $D\in[24,48]$, the exact affine identity is

$$
Z_P(D)=\frac{48-D}{24}Z_P(24)
                          +\frac{D-24}{24}Z_P(48)<0.
\tag{7.14}
$$

A zero drift coefficient is included; none was divided out. ∎

**Proposition 7.2.** Alternative II of Proposition 6.1 is impossible.

**Proof.** For an $AC$ pair the entries $c$ and $m_A=a+e$ are common.
For world $i$,

$$
a_i=cx_i,\quad e_i=m_A-cx_i,\quad
\rho_i=m_A/c-x_i,\quad b_i=x_i(m_A-cx_i).
\tag{7.15}
$$

Distinctness forces $x_1\ne x_2$; otherwise these formulas give
equal matrices. From their differences, using the already proved
$\epsilon\ne0$,

$$
\theta=\beta/\epsilon=x_1+x_2-m_A/c
                         =x_2-\rho_1=x_1-\rho_2.
\tag{7.16}
$$

Relabel the worlds so $x_1<x_2$. In II, $-1<\theta<-1/3$, so

$$
x_2+1/3<\rho_1<x_2+1,\qquad
x_1+1/3<\rho_1<3/2.
\tag{7.17}
$$

The first world thus satisfies Lemma 7.1, while $24<d<48$.
It would have $f_1(6)=Z_{P_1}(d)<0$, a contradiction.
Both late readings have remained fixed actual equations throughout
the collision analysis. A necessary first-four obstruction suffices
to contradict the full six-equation system. ∎

This proof is confined to legal strictly positive sources.
The divisions by $c,e,1-2x,2t+3,1+\rho t,j_N,m_N$ have been
justified. Division by $5-6\rho$ occurs only in (7.10).
No assertion extends Lemma 7.1 or Proposition 7.2 to arbitrary
nonnegative boundary sources, where this chart can degenerate.

## 8. All-drift AC injection and global pattern reduction

**Theorem 8.1 (all-drift AC injection).** For every fixed arbitrary
$y,\zeta,d\in\mathbb R$, the map $W\mapsto(A(W),C(W))$ is injective
on the entire positive class $\mathcal K_{\mathbf c,d}$.

**Proof.** Proposition 6.1 exhausts distinct $AC$ pairs.
In I, Theorem 3.1 and the actual fourth equation force $y>d$,
contrary to $y<d$. Proposition 7.2 excludes II.
All endpoints and sample-zero breakpoints were excluded within the
distinct-pair proof in Section 6. Thus no distinct pair exists. ∎

Together with Proposition 5.1, all three pair maps involving $A$
are globally injective in this fixed-word, fixed-first-four family.
This conclusion is global across $y,\zeta,d$ for (1.2), not across
other words or arbitrary first-four readings.

A terminal column on three distinct worlds is called proper when
it is nonconstant but noninjective; it then has exactly one colliding
unordered pair. A constant column uses all three pairs.

**Theorem 8.2 (global necessary TT patterns).** If three distinct
members of $\mathcal K_{\mathbf c,d}$ have all four terminal columns
noninjective, no column is constant and the three pair multiplicities
are exactly $(2,1,1)$. The repeated coordinate subset is $BC$, $BD$
or $CD$. Up to relabeling worlds, the complete canonical assignments
are

$$
\begin{array}{c|cccc}
\text{repeat}&A&B&C&D\\ \hline
BC&A_1=A_2\ne A_3&B_1=B_3\ne B_2&C_1=C_3\ne C_2&D_2=D_3\ne D_1\\
BD&A_1=A_2\ne A_3&B_1=B_3\ne B_2&C_2=C_3\ne C_1&D_1=D_3\ne D_2\\
CD&A_1=A_2\ne A_3&B_2=B_3\ne B_1&C_1=C_3\ne C_2&D_1=D_3\ne D_2.
\end{array}
\tag{8.1}
$$

All three normalized seventh gains have one common nonzero sign.
None of the listed assignments is asserted feasible.

**Proof.** If $A$ is constant, a collision in $B$ violates $AB$
injection. If $B,C$ or $D$ is constant, a collision in $A$ violates,
respectively, $AB,AC$ or $AD$ injection. This excludes every
constant-column configuration.

For completeness, a distinct pair cannot share $B,C,D$.
Their terminal gains have a common sign; multiply both $X$ by that
sign to make them positive. Solving the three equalities gives

$$
X_1=\begin{pmatrix}a&b\\c&e\end{pmatrix},\quad
X_2=\begin{pmatrix}a&b-\epsilon\\c-\epsilon&e+\epsilon\end{pmatrix},
\qquad
\det X_2=\epsilon(a+b+c-\epsilon).
\tag{8.2}
$$

Here $ae=bc$. If $\epsilon=0$, reconstruction gives equal worlds.
The only other root, $\epsilon=a+b+c$, gives $b_2=-a-c<0$,
contradicting positivity. Even if the two displayed determinant
roots coincide, factorization leaves no additional branch.
Every other three-coordinate subset contains one of $AB,AC,AD$.
Thus each pair can occupy at most two columns.

All four columns are now proper. Let the $A$ pair be $\{1,2\}$.
It cannot occur in $B,C,D$. Those three columns use the other
two pairs, and cannot all use one pair by (8.2).
One pair therefore occurs twice and the other once.
Swapping worlds one and two if necessary makes the repeated pair
$\{1,3\}$, giving exactly (8.1).
Equivalently, each possible $(2,2,0)$ partition
$AB\mid CD$, $AC\mid BD$, $AD\mid BC$ contains a forbidden
pair involving $A$, so all such configurations are excluded.

Finally every terminal offset from $d$ has the sign of $f_i(7)$.
With mixed signs among three worlds, only one same-sign pair can
collide in any column. Four colliding columns would make that pair
share $AB$, impossible. Thus all three signs agree.
Original seventh signs are obtained by multiplication by the one
common $\lambda$. ∎

This strengthens the predecessor's remaining constant-$C$,
$AC\mid BD$ and repeated-$AC$ possibilities: they are all excluded
for every $\mathbf c,d$ in (1.2), rather than only at $H_*$.

## 9. The remaining pair maps on a closed drift interval

**Theorem 9.1.** For every fixed $y,\zeta$ and
$d\in[48,312/5]$, the maps $BC,BD,CD$ are injective on the entire
$\mathcal K_{\mathbf c,d}$. In addition $BD$ is injective at $d=24$.

**Difference certificates.** Put $w=\Delta a+\Delta e=\Delta(A-d)$
and $\epsilon=\Delta e$. In a distinct $BC$ or $BD$ collision,
$w=0$ would add $A$ and contradict $AB$ injection.
In a distinct $CD$ collision it would contradict $AD$ injection.
Hence $w\ne0$ before introducing $\theta=\epsilon/w$.

Solving the terminal equalities gives the following full matrices
and all six trace differences:

$$
\begin{array}{c|c|l}
&\Delta X&(\Delta\sigma_0,\ldots,\Delta\sigma_5)\\ \hline
BC&\begin{pmatrix}w-\epsilon&-w\\-w&\epsilon\end{pmatrix}
 &(-6w+\epsilon,6w-2\epsilon,-4w+2\epsilon,2w,-3w+\epsilon,w)\\
BD&\begin{pmatrix}w-\epsilon&-w\\-\epsilon&\epsilon\end{pmatrix}
 &(-5w,5w-\epsilon,-3w+\epsilon,2w,-2w,w)\\
CD&\begin{pmatrix}w-\epsilon&-\epsilon\\-w&\epsilon\end{pmatrix}
 &(-3w-2\epsilon,4w,-3w+\epsilon,w+\epsilon,-2w,w).
\end{array}
\tag{9.1}
$$

Indeed $\Delta a=w-\epsilon$. The $BC$ equalities give
$\Delta b=\Delta c=-w$; $BD$ gives $\Delta b=-w$,
$\Delta c=-\epsilon$; $CD$ gives $\Delta c=-w$,
$\Delta b=-\epsilon$. Substitution into each of the six rows of
(5.4) proves all entries of (9.1). In units of $w$ the rows are

$$
\begin{aligned}
F^{BC}&=(\theta-6,6-2\theta,2\theta-4,2,\theta-3,1),\\
F^{BD}&=(-5,5-\theta,\theta-3,2,-2,1),\\
F^{CD}&=(-3-2\theta,4,\theta-3,1+\theta,-2,1).
\end{aligned}
\tag{9.2}
$$

**Affine identity.** The common normalizations at six and seven imply

$$
h_2-h_1=R_2L,\qquad
R_2=(T-6)(T-7)=T^2-13T+42,\qquad \deg L\le1,
\tag{9.3}
$$

where $L$ may be zero. The complete coefficient row of $R_2$ is
$(42,-13,1)$ and its sample row at $0,\ldots,7$ is
$(42,30,20,12,6,2,0,0)$, directly from the product.
For residuals $Q_j=c_j-d$, the exact identity is

$$
R_2(j)L(j)=-\frac{Q_jwF_j}{\sigma_{1,j}\sigma_{2,j}}
                   \quad(0\le j\le5).
\tag{9.4}
$$

The denominator is positive because this pair shares a terminal scalar.
All six displayed $R_2(j)$ are positive.
Thus $Q_jF_j=0$ gives $L(j)=0$ exactly, and otherwise

$$
\operatorname{sgn}L(j)
=-\operatorname{sgn}(w)\operatorname{sgn}(Q_jF_j).
\tag{9.5}
$$

A nonzero affine polynomial has at most one sign change on ordered
nodes after zero samples are deleted: a nonconstant affine polynomial
has only one real root, and a nonzero constant has none.
The zero polynomial has no nonzero samples.

**Interior signs.** When $48<d<312/5$, the first-four residual
signs are $(-,-,-,+)$. The signs of $Q_jF_j$, $j=0,1,2,3$,
are consequently the signs of the following linear factors:

$$
\begin{array}{c|cccc}
BC&6-\theta&2\theta-6&4-2\theta&2\\
BD&5&\theta-5&3-\theta&2\\
CD&3+2\theta&-4&3-\theta&1+\theta.
\end{array}
\tag{9.6}
$$

All interval and equality cases are listed here.

| Pair | $\theta$ | $\operatorname{sgn}(Q_0F_0,Q_1F_1,Q_2F_2,Q_3F_3)$ |
| --- | --- | --- |
| $BC$ | $\theta<2$ | $(+,-,+,+)$ |
| $BC$ | $\theta=2$ | $(+,-,0,+)$ |
| $BC$ | $2<\theta<3$ | $(+,-,-,+)$ |
| $BC$ | $\theta=3$ | $(+,0,-,+)$ |
| $BC$ | $3<\theta<6$ | $(+,+,-,+)$ |
| $BC$ | $\theta=6$ | $(0,+,-,+)$ |
| $BC$ | $\theta>6$ | $(-,+,-,+)$ |
| $BD$ | $\theta<3$ | $(+,-,+,+)$ |
| $BD$ | $\theta=3$ | $(+,-,0,+)$ |
| $BD$ | $3<\theta<5$ | $(+,-,-,+)$ |
| $BD$ | $\theta=5$ | $(+,0,-,+)$ |
| $BD$ | $\theta>5$ | $(+,+,-,+)$ |
| $CD$ | $\theta<-3/2$ | $(-,-,+,-)$ |
| $CD$ | $\theta=-3/2$ | $(0,-,+,-)$ |
| $CD$ | $-3/2<\theta<-1$ | $(+,-,+,-)$ |
| $CD$ | $\theta=-1$ | $(+,-,+,0)$ |
| $CD$ | $-1<\theta<3$ | $(+,-,+,+)$ |
| $CD$ | $\theta=3$ | $(+,-,0,+)$ |
| $CD$ | $\theta>3$ | $(+,-,-,+)$ |

Each row follows by the roots of the four linear factors in (9.6).
After deleting zeros every row has at least two sign changes and
contains nonzero entries. Multiplication by the common sign in (9.5)
does not alter the count. Thus neither nonzero affine $L$ nor $L=0$
can realize any row. Values causing only a late $F_4$ or $F_5$ zero
are already included in these exhaustive rows. This proves all three
injections on the open interval.

**The endpoint $d=48$.** Here $Q_2=0$, so (9.4) gives $L(2)=0$.
If $L=0$, the nonzero-residual clocks zero, one and three require
$F_0=F_1=F_3=0$. This is impossible for $BC$ since $F_3=2$,
for $BD$ since $F_0=-5$, and for $CD$ since $F_1=4$.
Thus $L$ is a nonzero multiple of $T-2$.
Its values at zero and one have the same nonzero sign, and its value
at three has the opposite sign. Equivalently, $Q_0F_0,Q_1F_1$
have one sign and $Q_3F_3$ has the opposite sign.
Because $Q_0,Q_1<0<Q_3$, the resulting requirement is that
$F_0,F_1,F_3$ have the same nonzero sign.
For $BC$, $F_3>0$ would require $\theta>6$ and $\theta<3$.
For $BD$, $F_0<0<F_3$ already contradicts the requirement.
For $CD$, $F_1>0$ would require $\theta<-3/2$ and $\theta>-1$.
All three possibilities are excluded.

**The endpoint $d=312/5$.** Now $Q_3=0$, hence $L(3)=0$.
If $L=0$, the first three residuals force
$F_0=F_1=F_2=0$. For $BD$ and $CD$ their nonzero constant entries
exclude this, and for $BC$ it would require both $\theta=6$ and
$\theta=3$. Thus $L$ is a nonzero multiple of $T-3$, and its
values at zero, one and two have the same nonzero sign.
All three corresponding residuals are negative, so
$F_0,F_1,F_2$ must have the same nonzero sign.
For $BC$, positivity requires $\theta>6$ and $\theta<3$;
negativity requires $\theta>3$ and $\theta<2$.
For $BD$, $F_0<0$ would require $\theta>5$ and $\theta<3$.
For $CD$, $F_1>0$ would require $\theta<-3/2$ and $\theta>3$.
These contradictions prove all endpoint injections.
Extra parameter zeros are excluded by the nonzero affine samples,
rather than silently discarded.

**The additional $BD$ endpoint $d=24$.** Here $Q_1=0$ and $L(1)=0$.
But $Q_0F_0=(-24)(-5)>0$ and
$Q_3F_3=(312/5-24)2>0$ make $L(0)$ and $L(3)$ nonzero with the
same sign $-\operatorname{sgn}w$. An affine polynomial vanishing
at one must have opposite signs at zero and three unless it is zero;
the nonzero samples exclude the latter case. This proves the
additional injection and completes Theorem 9.1. ∎

All sample-zero branches at the drift endpoints and every relevant
$\theta$ equality are retained. Divisibility in (9.3) covers all
lower degrees, repeated sixth roots, and zero slope or zero $L$.
No ancestor gain, residual $Q_j$, sixth gain, root difference,
leading coefficient or discriminant was divided out.

## 10. All six pair maps, actual TT and the limited scalar policy

**Corollary 10.1.** For every fixed $y,\zeta$ and
$d\in[48,312/5]$, all six terminal-pair maps
$AB,AC,AD,BC,BD,CD$ are injective on the entire
$\mathcal K_{\mathbf c,d}$, equivalently on (2.9).
No triple of distinct worlds in that class has all four terminal
columns noninjective.

The pair assertions follow from Proposition 5.1 and Theorems 8.1
and 9.1. For the triple assertion, choose one colliding unordered
pair in each of four noninjective columns. There are only three
unordered pairs on the same three worlds, so one chosen pair recurs
in two columns. The corresponding pair map is injective, a
contradiction. This includes constant columns, all collision
assignments, both terminal signs, simple and repeated sixth roots.

To relate this to actual acquisition, for any known compatible set
$K$ and literal history $H'$ use

$$
\begin{aligned}
L_0(K,H')&\Longleftrightarrow |K|\ge2,\\
L_{r+1}(K,H')&\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{J,M\}}\exists w\in\mathbb R:\
L_r(K\cap\mathcal F(H',E,w),(H',E,w)).
\end{aligned}
\tag{10.1}
$$

For a triple $K=\{W_1,W_2,W_3\}\subseteq\mathcal K_{\mathbf c,d}$
and either sixth action, every raw response gives exactly

$$
K\cap\mathcal F(H,E,w)=
\begin{cases}
K,&w=D_0+\lambda d,\\
\varnothing,&w\ne D_0+\lambda d.
\end{cases}
\tag{10.2}
$$

After the nonempty child, the raw terminal response $v$ for word
$EF$ retains

$$
\{W_i\in K:D_0+\lambda r_{EF}(W_i)=v\}.
\tag{10.3}
$$

Therefore, writing
$\Pi(R)=(R_1-R_2)(R_1-R_3)(R_2-R_3)$,

$$
L_2(K,H)\quad\Longleftrightarrow\quad
\Pi(A)=\Pi(B)=\Pi(C)=\Pi(D)=0.
\tag{10.4}
$$

Necessity follows from the sole nonempty sixth child and the
last-action pair requirement. Conversely choose raw sixth response
$D_0+\lambda d$ for each sixth action, and for each last action
separately choose its colliding pair's common raw terminal value.
These witness both recursive levels. Pairs and terminal values may
differ among the four columns. Every raw value is covered by
(10.2)–(10.3), for both signs of $\lambda$.
This is the interface of Pairs, Proposition 6.1,
[G, Proposition 5.1](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md)
and [IX, Definition 5.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md).

**Corollary 10.2.** A supplied known set
$K\subseteq\mathcal K_{\mathbf c,d}$ with $|K|\le3$ and
$d\in[48,312/5]$ has a lawful terminal policy using at most two
further readings, hence at most eight total including the ancestor.

For $|K|=3$, Corollary 10.1 proves that some scalar in $A,B,C,D$
is injective on $K$. For $|K|=2$, if all four scalars collided,
$AB$ would contradict pair injection. The empty set has no reachable
response, and a singleton can stop.
For a nonsingleton choose the first injective scalar in the order
$A,B,C,D$ and its corresponding word $EF$. Execute sixth $E$ and
read immediately, then seventh $F$ and read immediately.
For every pair of raw responses $w,v$, the retained set is empty
when $w\ne D_0+\lambda d$, and otherwise has at most one member
by scalar injectivity. At a reachable response return its unique
entire $(P,g,\delta)$.

This policy assumes the entire known $K$ and its promises.
Two-coordinate injection alone does not give a scalar injective on
an arbitrary triple; all six pair maps and the same-triple argument
are used here. The result supplies neither acquisition of both
alternative coordinates nor a scalar policy on larger or infinite
sets, the entire fiber, or other histories. No reduction of a larger
losing family to a losing triple is asserted.

## 11. The exact remaining common-world obligation and boundary scope

For the same fixed $\mathbf c=(0,24,48,312/5,y,\zeta)$ and common
$d$, choose three pairwise distinct sources and impose

$$
\begin{gathered}
P_i=\begin{pmatrix}s_i&p_i\\q_i&1-s_i\end{pmatrix},\quad
0<s_i<1,\quad p_i,q_i>0,\quad p_iq_i=s_i(1-s_i),\\
\mathcal C(P_i;\mathbf c)=0,\quad d_{P_i}=d,\quad
f_{P_i}(6)=0,\quad f_{P_i}(7)\ne0,\qquad i=1,2,3,\\
X_i=f_{P_i}(7)QP_i,\qquad
\Pi(A)=\Pi(B)=\Pi(C)=\Pi(D)=0.
\end{gathered}
\tag{11.1}
$$

The gains in these equations are the same reconstructed polynomials
(2.7); both actual late equations remain in compatibility.
For clarity, their unreduced common-world form is, for every $i$,

$$
\begin{aligned}
f_i(0)+d&=0,\\
(p_i+q_i)f_i(1)+d&=24,\\
(1+p_i)f_i(2)+d&=48,\\
(1+2p_i+q_i)f_i(3)+d&=312/5,\\
(1+s_i+p_i+q_i)f_i(4)+d&=y,\\
(2-s_i+3p_i+q_i)f_i(5)+d&=\zeta.
\end{aligned}
\tag{11.2}
$$

There is no separate selection of $y,\zeta$, gains or drifts for
individual worlds or terminal words.

By (2.10) and (10.4), solutions of (11.1) correspond bijectively to
ordered distinct legal triples with $L_2(K,H)$ through
$W_i=(P_i,\lambda f_{P_i},D_0+\lambda d)$.
For necessity, project a legal triple onto its three distinct sources,
apply the exact IX graph and then (10.4).
For sufficiency, legality and compatibility give all six equations,
a nonzero interpolated gain and the prescribed drift; the two future
sample conditions give membership in (1.7), and the four products
give the actual recursive witnesses. Projection and reconstruction
are inverse. This proves the equivalence without replacing joint
realizability by pairwise compatibility.

The results above require any solution to have $d\notin[48,312/5]$
and exactly one canonical assignment from (8.1), with common nonzero
terminal sign. At $d=24$ the repeated-$BD$ assignment is excluded
as well, leaving only repeated $BC$ or $CD$.
At $H_*$ every member also avoids $d=0$ and $[48/5,24]$.
These necessary restrictions do not make any remaining assignment
sufficient or exhibit a legal solution.

The inherited repeated-sixth theorem has its exact limited role.
[G, Theorem 2.1](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md)
gives at most one world with $f(6)=f'(6)=0$ per fixed full ancestor
and $d$. Such a gain is exactly cubic, has exactly a double sixth
root and one simple root $\rho_0$, has positive normalized leading
coefficient and $f(7)>0$, and requires one of

$$
\begin{array}{c|c}
d<0&-3<\rho_0<0\\
0<d<24&0<\rho_0<1\\
48<d<312/5&2<\rho_0<3.
\end{array}
\tag{11.3}
$$

These are necessary ranges, not existence statements.
Quadratic double-sixth and triple-sixth gains are excluded by that
baseline theorem. Corollary 10.1 excludes TT throughout the last
range, including all-simple triples there; it does not exclude the
individual repeated-root worlds. A TT triple containing a
repeated-sixth member has common positive normalized seventh sign
and at most one such member. A negative-sign triple has only simple
sixth roots. The large baseline coefficient and Bernstein certificates
are reused only through their stated theorem, not presented as new
calculations.

The new positivity theorem and both $H_*$ world exclusions hold
throughout $\mathcal N_1$, without a seventh promise.
In particular a finite nonnegative limit of zero-sixth $H_*$ worlds
still cannot have $d=0$ or $d\in[48/5,24]$, even if its limiting
$f(7)$ is zero: the six equations and $f(6)=0$ pass to the limit.
The gain remains nonzero since the readings zero and 24 differ.
The pair-map theorems, in contrast, are asserted on the legal
strictly positive class with $f(7)\ne0$.
The legal chart in Section 7 is not extended across arbitrary
nonnegative sources. If $f(7)=0$, $h=f/f(7)$ is undefined and
none of the normalized pair arguments is applied there.
If two members coalesce, their identical copies are not distinct
targets or a triple witness.

For geometric context,
[IX, Theorem 7.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md)
gives the exact source-escape locus, in the normalized late coordinates,

$$
\zeta=12y-288/5,\qquad -1788/25<y\le-5268/155.
\tag{11.4}
$$

IX, Theorems 8.1, 9.2 and 10.1 give a positive finite trace corridor
for the fixed $H_*$ fiber and its compact complete-world closure
obtained by adjoining six nonnegative source-boundary targets.
The legal positive fiber itself is nonclosed and noncompact.
These are fixed-history results, transported to each fixed affine
copy, not arbitrary-$y,\zeta$ compactness.
IX, Definition 11.1 retains possible incidence on diagonals and
nonlegal boundary targets. Compactness alone neither produces nor
excludes a distinct legal TT triple. It also does not settle the
seventh-zero strata. None of these geometric statements is a premise
of the new pair or positivity proofs.

## 12. Mathematical correspondence and the preserved full target

The permanent mathematical dependencies and the new deductions have
the following precise roles.

| Source and location | Reused result, new deduction and scope |
| --- | --- |
| [IX](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md), Definitions 1.1–1.4 and Theorems 2.1, 3.1 | Complete worlds, literal ancestor, affine normalization, positive traces, $\Delta>0$ on the rank-one-free nonnegative domain, and the exact source-conditioned graph in Sections 1–2. Conditional gain/drift recovery leaves the source unknown. |
| IX, Theorem 4.1 and Proposition 4.2 | A fixed positive finite trace corridor and fixed or bounded readings yield coefficient/drift bounds. Moving late readings do not yield a uniform drift bound. No arbitrary-history compactness is imported. |
| IX, Definitions 5.2–5.3 | The same fixed worlds, actual-child recursion and all raw responses in Sections 10–11; the original-root eight-versus-nine quantifiers remain unchanged. |
| IX, Theorems 7.2, 8.1, 9.2, 10.1 and Definition 11.1 | The exact escape locus and fixed-$H_*$ six-point compactification are context in Section 11. They do not settle legal incidence, diagonals or seventh-zero limits. Their large boundary certificates are not new work here. |
| [Pairs](FIB_JMMJM_ZERO_SIXTH_PAIR_INJECTIVITY_AND_JOINT_COLLISION_OBSTRUCTIONS.md), Sections 3–5 | Signed terminal/ancestor conversions, whole-class $AB$ and $AD$ injection, and exhaustive $AC$ alternatives. Sections 5–6 state and validate their exact interfaces. Theorem 3.1 eliminates I; the legal-source trace lemma eliminates II. |
| Pairs, Sections 6–7 | Actual TT equivalence, complete-source simultaneous system, and known-set scalar-policy boundary. Theorem 8.2 strengthens its pattern reduction globally; Corollary 10.1 removes TT on the entire closed interval. |
| [G](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md), Theorem 2.1, Section 3, Theorems 4.1, 6.1 and Propositions 5.1–5.2, 7.1 | Repeated-sixth singleton/ranges/sign, signed reconstruction, three-coordinate injection, incidence and actual TT interfaces. Repeated-root facts have the scope in (11.3); the large certificate is not a premise of the new exclusions. |
| [F](FIB_JMMJM_NONZERO_TERMINAL_COLLISION_SPARSITY_AND_RATIO_DIVERSITY.md), Sections 1–2, Theorem 4.1, Corollary 4.2, Theorem 6.1 and Section 7 | Positive terminal chart, chronological coordinates and complete-target inverse agree with Sections 5 and 7. Common source sum from five ratios needs nonzero sixth gains; diagonal-swap exclusion needs common $f(6)/f(7)\ne0$. Neither inference is made at zero sixth gain. The PP/PT/TP/TT interface remains an actual-child interface. |
| This volume, Theorem 3.1 and Section 4 | New rank-one fourth-gain positivity on $0\le d\le24$, its strict actual-late inequality, and the closed $H_*$ world gap and separate $d=0$ exclusion. The positivity statements permit seventh-zero limits at the expressly stated nonnegative domain. |
| This volume, Lemma 7.1, Proposition 7.2 and Theorem 8.1 | New legal-source endpoint trace estimates and affine extension remove the second $AC$ branch; combining complementary exclusions proves whole-class $AC$ injection for every fixed $y,\zeta,d$ in this family. |
| This volume, Theorem 8.2, Theorem 9.1 and Corollaries 10.1–10.2 | New global removal of every constant column and every $(2,2,0)$ TT assignment; exact remaining proper patterns; closed-interval $BC/BD/CD$ injections including both endpoints, extra $BD$ injection at 24, whole TT exclusion on that interval, and the limited known-set policy. |

The new mathematical ingredients are exact Lagrange evaluation,
coefficient collection, a quadratic chord identity with the source
determinant bound, endpoint trace estimates in a legal rank-one chart,
polynomial divisibility, affine sign changes and same-triple
pigeonhole reasoning. Root counting and the intermediate value theorem
retain their stated multiplicity and sign conditions.
These are source-relative mathematical deductions in the prescribed
model; no exhaustive literature or worldwide-originality assertion is
made. The results carry no Lean/kernel certification, empirical or
general neural-network conclusion, nor stability, conditioning,
efficiency or computational-resource claim.

The full remaining zero-sixth question is still an exact legal
simultaneous solution of (11.1), for some common $y,\zeta,d$, versus
a universal all-drift exclusion of all such solutions.
Every possible solution is now restricted to (8.1), outside the
closed interval of Corollary 10.1, with the stated endpoint and
$H_*$ restrictions. No surviving $BC$, $BD$ or $CD$ assignment is
asserted attainable or impossible in the remaining ranges.

The common-drift nonzero-sixth varying-ratio PP system remains open.
Arbitrary or differing drifts, seventh-zero strata, other terminal-root
strata, larger and infinite losing families and their full actual
fibers, other literal histories, the earlier $JMMJ$ parent-arm gluing
and the separate $MMJM$ and $MJMMJ$ obligations remain outside the
proved exclusions. No larger-family-to-triple reduction or acquisition
of unchosen terminal coordinates is supplied.

The original-root target remains a lawful complete-target decoder on
every legal world with at most eight total readings versus
$n_{\mathrm{det}}(3,0)\ge9$. It includes both initial actions,
every actual history and early stop, arbitrary constant drift,
all positive nonsymmetric rank-one trace-one sources and all nonzero
cubic-or-lower gains with both signs, sampled roots and multiplicities.
The fixed-ancestor results here still require the appropriate
earlier-history bridge for that target. The strengthened pair and
pattern obstructions do not redefine or settle the full problem.
