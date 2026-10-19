# FIB JMMJM Zero-Sixth Root Rigidity and Terminal Collision Geometry

## 1. Complete worlds, original clocks and the entire ancestor

A complete world is $W=(P,g,\delta)$, where $P$ is a strictly
entrywise positive real $2\times2$ matrix of rank one and trace one,
$0\ne g\in\mathbb R[T]$ has degree at most three, and
$\delta\in\mathbb R$. Let $\mathcal W_3$ be the set of all these
complete worlds. Symmetry of $P$ is not assumed. Put

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{J,M\}.
\tag{1.1}
$$

The reading at original clock $i$ is

$$
z_i(W)=g(i)\operatorname{tr}(A_iP)+\delta.
\tag{1.2}
$$

The initial reading counts. Each individual atom is immediately read
on one unresettable, uncopyable trajectory. Eight total readings use
clocks $0,\ldots,7$. There are no skipped readings, unread compound
actions, empty-action readings, renumbered clocks or additional ports.
Actions, stops and complete-target answers may be arbitrary
deterministic functions of the entire actual history, without
regularity or computability assumptions. The target is the entire
$(P,g,\delta)$. Both gain signs, every lower actual degree, all other
roots and all root multiplicities are initially permitted.

Fix arbitrary real $D_0,Y,z$ and $\lambda\ne0$. The literal history is

$$
H=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
       M,D_0+312\lambda/5,J,Y,M,z).
\tag{1.3}
$$

Let $\mathcal F(H)$ denote the complete worlds realizing every action
and reading of this history. Normalize by

$$
f=g/\lambda,\quad d=(\delta-D_0)/\lambda,\quad
\widehat Y=(Y-D_0)/\lambda,\quad \widehat z=(z-D_0)/\lambda.
\tag{1.4}
$$

The inverse is $g=\lambda f$, $\delta=D_0+\lambda d$.
A normalized response $r$ has raw value $D_0+\lambda r$.
This is a bijection of all real response values for either sign of
$\lambda$; it preserves equality, actual children and complete-world
distinction. The observed $D_0$ is not assumed to equal the drift.

Write

$$
P=\begin{pmatrix}r&u\\v&1-r\end{pmatrix},\qquad
0<r<1,\quad u>0,\quad v>0,\quad uv=r(1-r)\le\frac14.
\tag{1.5}
$$

These conditions are equivalent to source legality: the determinant
vanishes and the nonzero trace is one. The inequality follows from
$r(1-r)=1/4-(r-1/2)^2$. Set $j=u+v>0$ and $\ell=1+u>1$.
The six actual cumulative matrices are

$$
\begin{gathered}
(A_0,A_1,A_2,A_3,A_4,A_5)=(I,J,L,J+L,C,Q),\\
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
J+L=\begin{pmatrix}1&1\\2&1\end{pmatrix},\\
C=J(J+L)=\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
Q=MC=\begin{pmatrix}1&1\\3&2\end{pmatrix},\quad
Q^{-1}=\begin{pmatrix}-2&1\\3&-1\end{pmatrix}.
\tag{1.6}
\end{gathered}
$$

Direct multiplication gives all six ancestor equations:

$$
\begin{aligned}
f(0)+d&=0,\\
f(1)(u+v)+d&=24,\\
f(2)(1+u)+d&=48,\\
f(3)(1+2u+v)+d&=312/5,\\
f(4)(1+r+u+v)+d&=\widehat Y,\\
f(5)(2-r+3u+v)+d&=\widehat z.
\end{aligned}
\tag{1.7}
$$

Every trace factor is strictly positive: its matrix is nonzero and
entrywise nonnegative and $P$ is strictly positive. In particular,
both late equations remain constraints with fixed readings.
For a fixed arbitrary real $d$, define the whole promised class

$$
\mathcal C_d(H)=\{W\in\mathcal F(H):
 (\delta-D_0)/\lambda=d,\ f(6)=0,\ f(7)\ne0\}.
\tag{1.8}
$$

The common drift and root restrictions are promises about candidates;
they are not inferred from the six readings. The model, normalization,
literal ancestor and actual-fiber conventions are established in
[VII, Definitions 1.1–1.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md).

## 2. Rigidity of a repeated root at six

**Theorem 2.1.** Fix the entire history (1.3) and $d$. Among all legal
worlds on that ancestor with $f(6)=f'(6)=0$, there is at most one
complete world. Every such gain is exactly cubic and has precisely a
double root at six and one simple root $\rho$. Its necessary alternatives
are

$$
\begin{array}{c|c}
\text{normalized drift}&\text{third root}\\ \hline
d<0&-3<\rho<0\\
0<d<24&0<\rho<1\\
48<d<312/5&2<\rho<3.
\end{array}
\tag{2.1}
$$

The normalized leading coefficient is positive and $f(7)>0$.
The ranges are necessary restrictions, without an existence assertion
at any parameter. The statement does not require terminal nonvanishing
as a premise.

**Proof, factorization and exceptional drifts.** Repeated-root
factorization, including every degree drop and a possible triple root,
gives

$$
f(T)=(T-6)^2(a+bT),\qquad 36a=-d.
\tag{2.2}
$$

If $d=0$, then $a=0$ and $b\ne0$. Clocks one, two and three give

$$
j=\frac{24}{25b},\qquad \ell=\frac3{2b},\qquad
j+\ell=\frac{104}{45b}.
$$

The first two sum to $123/(50b)$, while
$123/50-104/45=67/450\ne0$. Thus $d=0$ is impossible.

If $d=24$, then $a=-2/3$. Positivity of $j$ makes $f(1)=0$,
so $b=2/3$. Thus $f(2)=32/3$ and $f(3)=12$; (1.7) gives
$\ell=9/4$, $j+\ell=16/5$ and $j=19/20$. Consequently
$u=5/4$ and $v=j-u=-3/10$, a contradiction.

If $d=48$, then $a=-4/3$. Positivity of $\ell$ forces $f(2)=0$,
so again $b=2/3$. Now $f(1)=-50/3$ and $f(3)=6$, giving
$j=36/25$, $j+\ell=12/5$, hence $\ell=24/25<1$.
This contradicts $u>0$.

For all remaining candidates put $\mu=b/a$. We have $a\ne0$ and

$$
1+\mu\ne0,\qquad 1+2\mu\ne0:
\tag{2.3}
$$

otherwise clocks one or two would force the excluded $d=24$ or $48$.
No nonvanishing assertion about $1+3\mu$ is needed.

**Proof, the complete gain quadratic and denominator identities.**
The first two noninitial equations give

$$
j=\frac{36(d-24)}{25d(1+\mu)},\qquad
\ell=\frac{9(d-48)}{4d(1+2\mu)}.
\tag{2.4}
$$

Substitution into the clock-three equation, clearing only the
established nonzero denominators, gives

$$
\begin{aligned}
0={}&144(d-24)(1+2\mu)(1+3\mu)\\
 &+225(d-48)(1+\mu)(1+3\mu)\\
 &-400(d-312/5)(1+\mu)(1+2\mu).
\end{aligned}
\tag{2.5}
$$

The constant, linear and quadratic coefficients are respectively
$10704-31d$, $14400+420d$, and $-3216+739d$. Hence

$$
Q_d(\mu)=(739d-3216)\mu^2+(420d+14400)\mu+10704-31d=0.
\tag{2.6}
$$

This identity includes a clock-three root; no division by
$1+3\mu$ has occurred. Define

$$
K=67\mu^2-300\mu-223,\qquad
H_*=739\mu^2+420\mu-31.
\tag{2.7}
$$

Here $H_*$ is an auxiliary polynomial, unrelated to a history.
The exact identities are

$$
\begin{aligned}
Q_d&=dH_*-48K,\\
2K-H_*&=-5(\mu+1)(121\mu+83),\\
K-H_*&=-48(2\mu+1)(7\mu+4).
\end{aligned}
\tag{2.8}
$$

If $K=0$, (2.6), $d\ne0$ and (2.8) imply $H_*=0$.
The second identity and $\mu\ne-1$ then give $\mu=-83/121$,
but

$$
K(-83/121)=\frac{209520}{14641}\ne0.
$$

Thus $K\ne0$. Also $H_*\ne0$, since $dH_*=48K$.
Multiplying (2.4) by the identities

$$
2K(d-24)=d(2K-H_*),\qquad K(d-48)=d(K-H_*)
$$

now yields

$$
\begin{aligned}
j&=-\frac{18(121\mu+83)}{5K},&
\ell&=-\frac{108(7\mu+4)}K,\\
u&=\frac UK,&v&=\frac V{5K},\\
U&=-67\mu^2-456\mu-209,&
V&=335\mu^2+102\mu-449.
\end{aligned}
\tag{2.9}
$$

Indeed $u=\ell-1$ and $v=j-\ell+1$ give exactly these numerators.
The canceled factors in this derivation are only those in (2.3).
The expressions retain the off-diagonal legality conditions.

**Proof, positivity before the rank-one certificate.** Since $j,\ell>0$,
the nonzero factors $121\mu+83$ and $7\mu+4$ have the same sign.
Their roots satisfy $-83/121<-4/7$. Thus either

$$
\mu<-83/121,\ K>0,
\qquad\text{or}\qquad
\mu>-4/7,\ K<0.
\tag{2.10}
$$

In the first case, if $\mu\ge-1$ then
$-1\le\mu<-83/121$. Here $V'=670\mu+102<0$ and
$V(-1)=-216$, so $V<0$, contradicting $v>0$.
Therefore the first case requires $\mu<-1$.
In the second case, if $\mu\le-1/2$ then
$-4/7<\mu\le-1/2$. Here $U'=-134\mu-456<0$ and
$U(-1/2)=9/4$, so $U\ge9/4>0$ and $u<0$.
Therefore the second case requires $\mu>-1/2$.

**Proof, every coefficient of the rank-one obstruction.** By (1.5)
and (2.9), $uv=UV/(5K^2)\le1/4$. Therefore

$$
\Omega(\mu)=5K^2-4UV\ge0.
\tag{2.11}
$$

Complete multiplication, in increasing powers, is

$$
\begin{array}{c|rrrrr}
 &\mu^0&\mu^1&\mu^2&\mu^3&\mu^4\\ \hline
5K^2&248645&669000&300590&-201000&22445\\
4UV&375364&733704&-345776&-638376&-89780\\
\Omega&-126719&-64704&646366&437376&112225.
\end{array}
\tag{2.12}
$$

In particular the full quartic is

$$
\Omega=112225\mu^4+437376\mu^3+646366\mu^2-64704\mu-126719.
\tag{2.13}
$$

For $-1/3\le\mu\le0$, put $X=-3\mu\in[0,1]$ and
$B_{i,4}(X)=\binom4iX^i(1-X)^{4-i}$. The complete scaled
power-coefficient vector is

$$
81\Omega(-X/3)
=-10264239+1747008X+5817294X^2-1312128X^3+112225X^4.
\tag{2.14}
$$

The exact Bernstein identity is

$$
\begin{aligned}
81\Omega(-X/3)={}&-10264239B_{0,4}-9827487B_{1,4}
 -8421186B_{2,4}\\
 &-6373368B_{3,4}-3899840B_{4,4}.
\end{aligned}
\tag{2.15}
$$

Here and below each $B_{i,4}$ has argument $X$. To verify every
coefficient, if $(p_0,\ldots,p_4)$ is the vector in (2.14), the five
coefficient sums are

$$
\begin{array}{c|l|r}
i&\text{sum}&\text{value}\\ \hline
0&p_0&-10264239\\
1&p_0+p_1/4&-9827487\\
2&p_0+p_1/2+p_2/6&-8421186\\
3&p_0+3p_1/4+p_2/2+p_3/4&-6373368\\
4&p_0+p_1+p_2+p_3+p_4&-3899840.
\end{array}
\tag{2.16}
$$

The conversion itself follows from the binomial theorem:

$$
X^a=\sum_{i=a}^4\frac{\binom ia}{\binom4a}B_{i,4}(X),
\qquad
\frac{\binom4i\binom ia}{\binom4a}=\binom{4-a}{i-a}.
\tag{2.17}
$$

Indeed the sum on the right is $X^a(X+1-X)^{4-a}$.
Substituting it into each power term gives (2.16) and (2.15).
The Bernstein terms are nonnegative and sum to one on $[0,1]$;
every coefficient in (2.15) is strictly negative. Thus $\Omega<0$
on the entire closed interval $[-1/3,0]$. The endpoint values are
$-3899840/81$ at $-1/3$ and $-126719$ at zero.

For $0\le\mu\le1/3$, the negative linear term is at most zero,
and each positive power term is at most its value at $1/3$.
Consequently

$$
\begin{aligned}
\Omega(\mu)
&\le-126719+\frac{646366}{9}+\frac{437376}{27}
                 +\frac{112225}{81}\\
&=\frac{-10264239+5817294+1312128+112225}{81}
=-\frac{3022592}{81}<0.
\end{aligned}
\tag{2.18}
$$

This includes both endpoints. Combining (2.10)–(2.18), every legal
candidate satisfies exactly one of the following necessary alternatives:

$$
\mu<-1,\qquad -\frac12<\mu<-\frac13,\qquad \mu>\frac13.
\tag{2.19}
$$

**Proof, drift and root ranges.** If $\mu<-1$, then
$f(1)=25a(1+\mu)$ has the sign of $d$. Its positive trace equation
requires $\operatorname{sgn}(24-d)=\operatorname{sgn}d$, hence
$0<d<24$. Its third root $\rho=-1/\mu$ lies in $(0,1)$.

If $-1/2<\mu<-1/3$, then $f(3)=9a(1+3\mu)$ has the sign
of $d$. Thus $\operatorname{sgn}(312/5-d)=\operatorname{sgn}d$,
giving $0<d<312/5$. Meanwhile $f(2)=16a(1+2\mu)$ has the
opposite sign to $d$, so its positive trace equation gives $d>48$.
Here $48<d<312/5$ and $2<\rho<3$.

If $\mu>1/3$, (2.10) gives $K<0$. Also
$H_*=739\mu^2+420\mu-31>109>0$ on this interval. Thus
$d=48K/H_*<0$ and $-3<\rho<0$.
In particular $\mu\ne0$ and $\rho\ne6$. Since $a\ne0$,
$b=a\mu\ne0$, so the gain is exactly cubic, the sixth root is
exactly double, and its third root is simple. This excludes quadratic
double-six gains and triple-six gains by source legality, without
adding degree or multiplicity promises. All boundaries in (2.1) and
(2.19) are excluded by these strict deductions; $d=0,24,48$ were
also treated directly.

**Proof, uniqueness including degree drops of the quadratic.** For
$0<d<24$, all legal $\mu$ are below $-1$, while

$$
Q_d(-1)=288(d-24)<0,\qquad Q_d(0)=10704-31d>0.
\tag{2.20}
$$

The intermediate value theorem gives a root in $(-1,0)$.
The nonzero polynomial $Q_d$ has degree at most two, so it has at
most one further root below $-1$. This also covers its vanishing
quadratic leading coefficient $739d-3216=0$: no division by that
coefficient is made in this interval.

For $d<0$, let $A=739d-3216<0$. At the translated origin,

$$
Q_d(-1/2)=\frac{225(48-d)}4>0.
\tag{2.21}
$$

The polynomial $Q_d(-1/2+w)$ has leading coefficient $A$ and
constant term of opposite sign. Its discriminant is strictly positive,
since it equals its linear coefficient squared minus four times a
negative product. Its two real roots have negative product, so one
is positive and one negative. Exactly one $\mu$ is to the right of
$-1/2$, where all legal candidates in this drift case must lie.

For $48<d<312/5$, $A>0$ and $Q_d(-1/2)<0$.
The same translated argument again gives exactly one root to the
right of $-1/2$, containing the legal interval $(-1/2,-1/3)$.
No other drift admits a legal alternative. These arguments count
all real roots, including any multiplicity; in the two translated
cases the opposite-sign product itself excludes a repeated root.
Hence there is at most one legal $\mu$ at each fixed $d$.

It fixes $a=-d/36$, $b=a\mu$, the whole gain, and $u,v$ by (2.9).
At least one of $f(4),f(5)$ is nonzero: otherwise the nonzero gain
would have the degree-four divisor $(T-6)^2(T-4)(T-5)$.
If $f(4)\ne0$, its actual equation fixes

$$
r=\frac{\widehat Y-d}{f(4)}-1-u-v;
\tag{2.22}
$$

if $f(5)\ne0$, its actual equation fixes

$$
r=2+3u+v-\frac{\widehat z-d}{f(5)}.
\tag{2.23}
$$

When both apply they must agree. Both late equations,
$0<r<1$ and $uv=r(1-r)$ remain required. These formulas give at
most one complete world, without asserting it exists or discarding
the determinant equation.

Finally, in each positive-$d$ alternative $a<0$ and $\mu<0$;
in the negative-$d$ alternative $a>0$ and $\mu>1/3$.
Thus $b=a\mu>0$ in every legal case. Since

$$
f(T)=b(T-6)^2(T-\rho),\qquad \rho<3,
\quad f(7)=b(7-\rho)>0,
\tag{2.24}
$$

the sign assertion follows. The original terminal gain
$g(7)=\lambda f(7)$ has the sign of $\lambda$.
The exceptional $d=0$ calculation divides only by its established
$b\ne0$ and nonzero integers. Elsewhere $a=-d/36\ne0$ permits
$\mu=b/a$, (2.3) and (2.8) establish the rational trace divisors,
and (2.19) establishes $\mu\ne0$ for $\rho=-1/\mu$.
The root-product argument uses the quadratic leading coefficient
only in the two intervals where it was proved nonzero; its vanishing
case is covered separately by (2.20). The late reconstruction uses
only the particular nonzero sample in (2.22) or (2.23). ∎

## 3. Terminal interfaces and their established positive chart

For a world in $\mathcal C_d(H)$ set

$$
X=f(7)QP=\begin{pmatrix}a&b\\c&e\end{pmatrix},\qquad
S=Q^{-1}X=f(7)P.
\tag{3.1}
$$

Every entry of $X$ is nonzero and has the sign of $f(7)$, and
$ae=bc$. Direct multiplication gives the complete terminal table:

$$
\begin{array}{c|c|c}
\text{chronological word }EF&FE& r_{EF}\\ \hline
JJ&I&A=d+a+e\\
JM&\begin{pmatrix}1&0\\1&1\end{pmatrix}&B=d+a+b+e\\
MJ&\begin{pmatrix}1&1\\0&1\end{pmatrix}&C=d+a+c+e\\
MM&\begin{pmatrix}1&1\\1&2\end{pmatrix}&D=d+a+b+c+2e.
\end{array}
\tag{3.2}
$$

The word $EF$ means execute and immediately read sixth $E$, then
execute and immediately read seventh $F$; the cumulative terminal
matrix is $FEQ$. The four entries are response functions on fixed
candidates, rather than four readings on a single trajectory.

For clarity, the established four-terminal inverse is fully algebraic:

$$
b=B-A,\quad c=C-A,\quad e=D-C-B+A,\quad
a=bc/e,\quad d=A-a-e.
\tag{3.3}
$$

The divisor $e=f(7)(QP)_{22}$ is nonzero. Rank one gives $a=bc/e$.
Next $f(7)=\operatorname{tr}(Q^{-1}X)\ne0$ and
$P=Q^{-1}X/\operatorname{tr}(Q^{-1}X)$. The recovered source and
drift determine $f(0),\ldots,f(3)$ through the positive first four
trace factors in (1.7). Four distinct arguments determine a polynomial
of degree at most three: their difference has four roots and must
vanish. This recovers the complete world, including degree drops
and repeated roots. This interface is established in
[Nonzero-Terminal, Lemma 2.3](FIB_JMMJM_NONZERO_TERMINAL_COLLISION_SPARSITY_AND_RATIO_DIVERSITY.md)
and [VII, equation (4.2)](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md),
which credits V, Theorem 7.1.

The positive chart from VII, Definition 1.3, also fixes the exact
comparison with nonzero-sixth results. Put $\eta=(QP)_{22}>0$,
$R=P/\eta$, $F=\eta f$. Defining $x=(QR)_{12}$ and
$y=(QR)_{21}$, rank one and $(QR)_{22}=1$ give

$$
QR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
R=\begin{pmatrix}(1-2x)y&1-2x\\(3x-1)y&3x-1\end{pmatrix},
\qquad \frac13<x<\frac12,\quad y>0.
\tag{3.4}
$$

The second identity is multiplication by $Q^{-1}$; positivity gives
exactly the displayed strip. Conversely the strip makes every entry
positive and the columns proportional. Its trace $T_0>0$ normalizes
it to $P=R/T_0$. Also $T_0=1/\eta$ and $f=T_0F$.
With $s=x+y$, $p=xy$, the six traces are

$$
(T_0,T_1,T_2,T_3,T_4,T_5)
=(s+2x-2p-1,\ 1-x-s+3p,\ s-2p,\ 1-x+p,\ s-p,\ p+1).
\tag{3.5}
$$

For verification, $T_0=\operatorname{tr}R$,
$T_1=R_{12}+R_{21}$, $T_2=T_0+R_{12}$,
$T_3=T_1+T_2$, $T_4=2R_{11}+R_{21}+R_{12}+R_{22}$,
and $T_5=\operatorname{tr}(QR)$. These yield (3.5); all are positive.
The entire ancestor is $d+F(i)T_i=c_i$, with
$c=(0,24,48,312/5,\widehat Y,\widehat z)$.

The traces of $JQR,MQR$ are $s,s+1$; those of
$QR,MJQR,JMQR,M^2QR$ give respectively
$p+1,p+x+1,p+y+1,p+s+2$. Thus the two sixth predictions and four
terminal predictions are

$$
\begin{gathered}
U=d+F(6)s,\qquad V=d+F(6)(s+1),\\
A=d+F(7)(p+1),\quad B=A+F(7)x,\quad
C=A+F(7)y,\quad D=A+F(7)(s+1).
\tag{3.6}
\end{gathered}
$$

In the present class $F(6)=0$, so $U=V=d$ gives no common-$s$
conclusion. In particular the common-source-sum step of
Nonzero-Terminal, Theorem 4.1, requires $F(6)\ne0$ and is not
available here. Its five monotone ratios are not applied here.
Likewise its Theorem 6.1 cancels a common
$q=f(6)/f(7)\ne0$; the present $q=0$ does not satisfy that
hypothesis. Neither argument is used to settle this stratum.

## 4. Any three terminal coordinates are injective

**Theorem 4.1.** Each of the maps

$$
W\longmapsto(A,B,C),\quad(A,B,D),\quad(A,C,D),\quad(B,C,D)
\tag{4.1}
$$

is injective on the entire $\mathcal C_d(H)$, without a cardinality
bound. Consequently two distinct members can collide in at most two
terminal coordinates. No common source, gain shape, source sum or
terminal amplitude is assumed.

**Proof, nonzero trace denominators and all linear certificates.**
For two worlds set $X_i=f_i(7)QP_i$, $S_i=Q^{-1}X_i$ and
$h_i=f_i/f_i(7)$. Then

$$
\deg h_i\le3,\quad h_i(6)=0,\quad h_i(7)=1,
\qquad \sigma_{i,k}=\operatorname{tr}(A_kS_i)\ne0.
\tag{4.2}
$$

The last assertion holds since $\sigma_{i,k}$ is $f_i(7)$ times a
strictly positive trace. The actual equation at every ancestor clock is

$$
h_i(k)\sigma_{i,k}=c_k-d\qquad(0\le k\le5).
\tag{4.3}
$$

Thus equal $\sigma$ at a clock force equal $h$ values there by a
nonzero common denominator, even when that gain sample vanishes.

Write $\Delta X=X_2-X_1$ and $\Delta S=S_2-S_1$.
Solving each set of three linear terminal equalities in (3.2) gives
the following complete table, where the scalar $\alpha$ may differ
between rows:

$$
\begin{array}{c|c|c|c}
\text{equal coordinates}&\Delta X/\alpha&\Delta S/\alpha&
(\Delta\sigma_0,\ldots,\Delta\sigma_5)/\alpha\\ \hline
A,B,C&\begin{pmatrix}1&0\\0&-1\end{pmatrix}&
\begin{pmatrix}-2&-1\\3&1\end{pmatrix}&(-1,2,-2,0,-1,0)\\[2mm]
A,B,D&\begin{pmatrix}1&0\\1&-1\end{pmatrix}&
\begin{pmatrix}-1&-1\\2&1\end{pmatrix}&(0,1,-1,0,0,0)\\[2mm]
A,C,D&\begin{pmatrix}1&1\\0&-1\end{pmatrix}&
\begin{pmatrix}-2&-3\\3&4\end{pmatrix}&(2,0,-1,-1,0,0)\\[2mm]
B,C,D&\begin{pmatrix}0&-1\\-1&1\end{pmatrix}&
\begin{pmatrix}-1&3\\1&-4\end{pmatrix}&(-5,4,-2,2,-2,1).
\end{array}
\tag{4.4}
$$

The quotient notation means the stated scalar-multiple identity,
including $\alpha=0$, without dividing by an unproved scalar.
For an arbitrary $Z=(z_{ij})$, the six trace forms used to verify
every row are

$$
\begin{aligned}
\operatorname{tr}(IZ)&=z_{11}+z_{22},\\
\operatorname{tr}(JZ)&=z_{12}+z_{21},\\
\operatorname{tr}(LZ)&=z_{11}+z_{22}+z_{12},\\
\operatorname{tr}((J+L)Z)&=z_{11}+z_{22}+2z_{12}+z_{21},\\
\operatorname{tr}(CZ)&=2z_{11}+z_{21}+z_{12}+z_{22},\\
\operatorname{tr}(QZ)&=z_{11}+z_{21}+3z_{12}+2z_{22}.
\end{aligned}
\tag{4.5}
$$

The middle column of (4.4) is multiplication by the explicit
$Q^{-1}$, and (4.5) gives every one of its six trace entries.
For example, the fourth row follows directly by writing
$\Delta e=\alpha$: the equations for $B,C$ give
$\Delta b=\Delta c=-\Delta a-\alpha$, and the equation for $D$
then forces $\Delta a=0$. This yields all four entries shown.
The other rows follow from $\Delta(A-d)=\Delta a+\Delta e=0$
and the respective additional equalities.

If $\Delta X=0$, then $S_1=S_2$. Taking traces recovers the same
nonzero $f_i(7)$, hence $P_1=P_2$. The common $d$ and the first four
positive trace factors in (1.7) force equal gain samples at $0,1,2,3$,
and thus the entire gain is equal. Normalization recovers equal
complete worlds. In the remaining cases it suffices to exclude
$\alpha\ne0$.

**Proof for $A,B,C$.** The first row gives equal $\sigma$ at clocks
three and five. Therefore $h_2-h_1$ has the four distinct zeros
$3,5,6,7$. Its degree is at most three, so $h_1=h_2=h$.
Subtract (4.3) at clocks zero and one. The corresponding trace
differences are $-\alpha$ and $2\alpha$, forcing $h(0)=h(1)=0$.
The actual readings would give simultaneously $d=0$ and $d=24$,
a contradiction.

**Proof for $A,B,D$.** Equal trace factors at clocks $0,3,4,5$
give zeros of $h_2-h_1$ at those four distinct clocks; its values
also agree at six and seven. Hence $h_1=h_2=h$.
The nonzero trace differences at one and two force
$h(1)=h(2)=0$, giving $d=24$ and $d=48$ simultaneously.

**Proof for $A,C,D$.** Equal trace factors at clocks $1,4,5$,
together with the common sixth root and seventh normalization,
give zeros $1,4,5,6,7$ of $h_2-h_1$, so it vanishes.
Trace differences at zero and two then force $h(0)=h(2)=0$,
giving $d=0$ and $d=48$ simultaneously. These three arguments
use actual ancestor clocks; the late readings and their equations
have not been replaced by freely chosen samples.

**Proof for $B,C,D$.** The trace coefficient in any terminal reading
is positive. Equality of one such reading with common $d$ implies
that $f_1(7)$ and $f_2(7)$ have the same sign. Multiply both $X_i$
by this common sign; they become strictly positive rank-one matrices,
and the three linear equalities, after subtracting $d$, persist.
Write the first sign-adjusted matrix as

$$
X_1=\begin{pmatrix}a&b\\c&e\end{pmatrix},\qquad
a,b,c,e>0,\quad ae=bc.
$$

The fourth row of (4.4) says that the second has the form

$$
X_2=\begin{pmatrix}a&b-\varepsilon\\c-\varepsilon&e+\varepsilon\end{pmatrix}.
\tag{4.6}
$$

Its rank-one determinant condition is exactly

$$
0=a(e+\varepsilon)-(b-\varepsilon)(c-\varepsilon)
=\varepsilon(a+b+c-\varepsilon).
\tag{4.7}
$$

Either $\varepsilon=0$, giving the same matrix and complete world,
or $\varepsilon=a+b+c$. The second root makes the upper-right
entry $b-\varepsilon=-a-c<0$, contradicting positivity.
Both roots are accounted for; $a+b+c>0$ excludes their coincidence.
This case needs no further root inference.

All four coordinate triples have now been treated. Polynomial root
counting covers every lower degree and multiplicity; the only gain
division was by the promised $f_i(7)\ne0$. This proves injectivity
on the whole class, and hence the pair collision bound. ∎

Three-coordinate injectivity is a statement about mathematical response
vectors. Three terminal coordinates are not jointly acquired on one
trajectory. In particular this theorem alone does not choose an
injective single terminal coordinate for every three-world subset.

## 5. Exact actual-child TT interface and finite-set policies

For a known compatible set $G$ at a history $H'$ define, within the
remaining original-clock horizon,

$$
\begin{aligned}
L_0(G,H')&\Longleftrightarrow |G|\ge2,\\
L_{r+1}(G,H')&\Longleftrightarrow |G|\ge2\ \land\
\bigwedge_{E\in\{J,M\}}\exists w\in\mathbb R:
L_r(G\cap\mathcal F(H',E,w),(H',E,w)).
\end{aligned}
\tag{5.1}
$$

Every $w$ here is a real raw response. All retained worlds and all
ancestor equations stay fixed. A zero- or one-world child fails $L_0$.

**Proposition 5.1 (established TT specialization).** Let
$K=\{W_1,W_2,W_3\}\subseteq\mathcal C_d(H)$ consist of three
distinct worlds, and let

$$
\Delta(R)=(R_1-R_2)(R_1-R_3)(R_2-R_3)
\tag{5.2}
$$

for a scalar terminal column. Then

$$
L_2(K,H)\quad\Longleftrightarrow\quad
\Delta(A)=\Delta(B)=\Delta(C)=\Delta(D)=0.
\tag{5.3}
$$

The collision pair may differ in each of the four columns.

**Proof.** For either sixth action $E$ and every real raw response $w$,
the actual child is exactly

$$
K\cap\mathcal F(H,E,w)=
\begin{cases}
K,&w=\delta=D_0+\lambda d,\\
\varnothing,&w\ne\delta.
\end{cases}
\tag{5.4}
$$

This follows from $f_i(6)=0$, independently of the selected action.
Thus the sole child that can witness $L_1$ for either sixth action
is the entire same $K$ at raw response $\delta$.
For a last action $F$ and every real raw response $v$, its child is

$$
\{W_i\in K:D_0+\lambda r_{EF}(W_i)=v\}.
\tag{5.5}
$$

It has at least two members for some $v$ if and only if the scalar
$r_{EF}$ has a collision on $K$, equivalently its product (5.2)
vanishes. For sixth $J$ the two columns are $A,B$; for sixth $M$
they are $C,D$, with the literal chronological words in (3.2).
Unfolding the two action conjuncts of (5.1) proves necessity.
For sufficiency choose $w=\delta$ for each sixth action and, for
each last action separately, choose a colliding pair in its column
and its common raw value in (5.5). These four pairs need not agree.
They witness exactly $L_0$ for each last action, hence $L_1$ in
both actual sixth children and $L_2$ on $K$. The real-response
bijection (1.4) proves the statement also for $\lambda<0$. ∎

**Proposition 5.2 (an injective scalar gives a lawful inverse).** For
any known finite $K\subseteq\mathcal C_d(H)$, if one of $A,B,C,D$
is injective on the whole $K$, its corresponding chronological word
gives a complete-target inverse using at most eight total readings.

**Proof.** Select the first injective coordinate in the order
$A,B,C,D$, with word $EF$ as in (3.2).
Execute sixth $E$ and immediately read. Its only reachable raw
response is $\delta$ and its retained child is $K$, as in (5.4).
Then execute seventh $F$ and immediately read the actual raw $v$.
For every real $w,v$, the retained set

$$
K\cap\mathcal F(H,E,w)\cap\mathcal F(H,E,w,F,v)
\tag{5.6}
$$

has at most one member by injectivity of the selected scalar on $K$.
At a reachable $v$, actual membership gives a member, so return its
entire $(P,g,\delta)$; this is unique. On unreachable responses the
policy can have any fixed answer. A known singleton may stop earlier;
an empty known set has no actual input. The six acquired ancestor
readings and the two immediate further readings give at most eight.
For a three-world $K$, an injective coordinate makes its collision
product nonzero, so (5.3) also directly gives $\neg L_2(K,H)$.
No unchosen response or three-coordinate vector is acquired. ∎

This TT interface and the distinction between whole-three and proper-pair
children are established in
[Nonzero-Terminal, Proposition 7.2](FIB_JMMJM_NONZERO_TERMINAL_COLLISION_SPARSITY_AND_RATIO_DIVERSITY.md).
The proofs above give their exact zero-sixth raw-response specialization.

## 6. Consequences for a simultaneous losing triple

**Theorem 6.1.** Suppose the same three distinct worlds
$K\subseteq\mathcal C_d(H)$ have $L_2(K,H)$. Then:

1. At least two gains have a simple root at six, and at most one
   has a double root there. No member has a triple root at six.
   Outside $(-\infty,0)\cup(0,24)\cup(48,312/5)$, all three
   sixth roots are simple.
2. Each pair collides in at most two terminal coordinates. At most
   one column is constant on all three worlds. If one is constant,
   the other three columns collide on three different proper pairs.
   If none is constant, the three pair multiplicities are $(2,2,0)$
   or $(2,1,1)$, up to ordering the unordered pairs.
3. The three normalized terminal gains have one common sign. If a
   double-sixth world occurs, that common sign is positive. A losing
   triple with negative normalized terminal sign has all three
   sixth roots simple.

**Proof.** Theorem 2.1 gives at most one repeated-sixth complete world
at this fixed $d$ and entire ancestor, and makes any repeated sixth
root exactly double. Every other sixth root must be simple. Its
necessary drift ranges prove the assertion outside the three stated
intervals, including their excluded endpoints.

Theorem 4.1 gives at most two coordinate collisions per pair. There
are three unordered pairs, so at most six pair-coordinate incidences.
By (5.3), every one of the four columns collides. A proper colliding
column, meaning a nonconstant column on the triple, contributes
exactly one incidence; a column constant on all three contributes
three. If $c$ columns are constant, there are
$3c+(4-c)=4+2c\le6$ incidences, so $c\le1$.

If $c=1$, this constant column already uses one incidence for every
pair. Each pair can occur at most once more. The remaining three
columns must therefore use three distinct proper pairs, once each.
If $c=0$, four incidences are distributed among three pairs, each
with count at most two. Sorting the counts, either the largest two
are both two, giving $(2,2,0)$, or only one is two, giving
$(2,1,1)$. A largest count of at most one would sum to at most three.
This exhausts the possibilities. The ordering of terminal columns
is still $JJ,JM,MJ,MM$; only pair counts have been sorted.

For the sign assertion, every terminal response minus $d$ has the
sign of $f_i(7)$, since its trace is positive. If the three nonzero
signs were mixed, precisely one unordered pair would have matching
signs; only that pair could collide in any column. Noninjectivity
of all four columns would make it agree in all four, contradicting
Theorem 4.1 (or the established inverse (3.3)). Thus there is a
common terminal sign. This is the established terminal-sign
restriction specialized to the present stratum. Theorem 2.1 makes
the repeated-root world's $f(7)$ positive, forcing that common sign
positive. Conversely a negative-sign losing triple contains no
repeated sixth root, so all three are simple. For original gains the
single fixed nonzero $\lambda$ transports this common sign as in
(1.4). ∎

These are restrictions on the same simultaneously realized $K$.
Neither a pair collision certificate nor the singleton repeated-root
class constructs the remaining triple or proves it impossible.

## 7. A complete conditional joint-feasibility system

The following system retains every same-world condition and all six
ancestor equations. It is a necessary-and-sufficient interface for the
remaining three-world TT question, without a feasibility verdict.
Fix $D_0,\lambda,Y,z$ as above and choose one common real $d$.
For $i=1,2,3$, choose

$$
0<r_i<1,\quad u_i>0,\quad v_i>0,\quad
u_iv_i=r_i(1-r_i),\qquad
(r_i,u_i,v_i)\ne(r_j,u_j,v_j)\ (i\ne j).
\tag{7.1}
$$

Put $j_i=u_i+v_i>0$, $\ell_i=1+u_i>1$ and set

$$
\alpha_{i,0}=-d,\quad
\alpha_{i,1}=\frac{24-d}{j_i},\quad
\alpha_{i,2}=\frac{48-d}{\ell_i},\quad
\alpha_{i,3}=\frac{312/5-d}{j_i+\ell_i}.
\tag{7.2}
$$

Every denominator is strictly positive. The four exact Lagrange
polynomials and the gain are

$$
\begin{aligned}
\mathcal L_0(T)&=-(T-1)(T-2)(T-3)/6,\\
\mathcal L_1(T)&=T(T-2)(T-3)/2,\\
\mathcal L_2(T)&=-T(T-1)(T-3)/2,\\
\mathcal L_3(T)&=T(T-1)(T-2)/6,\\
f_i(T)&=\sum_{k=0}^3\alpha_{i,k}\mathcal L_k(T).
\end{aligned}
\tag{7.3}
$$

For each row of four sample values $(\alpha_0,\ldots,\alpha_3)$,
the full increasing-power coefficient vector is

$$
\left(
\alpha_0,
-\frac{11}6\alpha_0+3\alpha_1-\frac32\alpha_2+\frac13\alpha_3,
\alpha_0-\frac52\alpha_1+2\alpha_2-\frac12\alpha_3,
-\frac16\alpha_0+\frac12\alpha_1-\frac12\alpha_2+\frac16\alpha_3
\right).
\tag{7.4}
$$

The complete sample rows are

$$
\begin{pmatrix}f_i(4)\\f_i(5)\\f_i(6)\\f_i(7)\end{pmatrix}
=\begin{pmatrix}
-1&4&-6&4\\
-4&15&-20&10\\
-10&36&-45&20\\
-20&70&-84&35
\end{pmatrix}
\begin{pmatrix}\alpha_{i,0}\\\alpha_{i,1}\\\alpha_{i,2}\\\alpha_{i,3}\end{pmatrix}.
\tag{7.5}
$$

For explicit coefficient verification, the increasing-power vectors
of $\mathcal L_0,\ldots,\mathcal L_3$ are respectively

$$
(1,-11/6,1,-1/6),\quad(0,3,-5/2,1/2),\quad
(0,-3/2,2,-1/2),\quad(0,1/3,-1/2,1/6).
\tag{7.6}
$$

Expanding the four factored products in (7.3) gives (7.6), and their
linear combination gives (7.4). Substituting each of $4,5,6,7$
into those same products gives the four rows of (7.5). At $0,1,2,3$
they satisfy $\mathcal L_k(m)=1$ for $k=m$ and zero otherwise,
which proves the asserted interpolation including every degree drop.

Retain both actual late readings for each of the same three worlds:

$$
\begin{aligned}
d+f_i(4)(1+r_i+u_i+v_i)&=\widehat Y,\\
d+f_i(5)(2-r_i+3u_i+v_i)&=\widehat z.
\end{aligned}
\tag{7.7}
$$

Impose also exactly

$$
\begin{aligned}
-10\alpha_{i,0}+36\alpha_{i,1}-45\alpha_{i,2}
                         +20\alpha_{i,3}&=0,\\
-20\alpha_{i,0}+70\alpha_{i,1}-84\alpha_{i,2}
                         +35\alpha_{i,3}&\ne0.
\end{aligned}
\tag{7.8}
$$

These are precisely the sixth zero and seventh nonzero conditions.
Form

$$
P_i=\begin{pmatrix}r_i&u_i\\v_i&1-r_i\end{pmatrix},\quad
g_i=\lambda f_i,\quad \delta_i=D_0+\lambda d,\quad
X_i=f_i(7)QP_i,
\tag{7.9}
$$

and its four columns $A_i,B_i,C_i,D_i$ by (3.2). The last conditions
are the four simultaneous collision products

$$
\Delta(A)=\Delta(B)=\Delta(C)=\Delta(D)=0.
\tag{7.10}
$$

**Proposition 7.1.** Solutions of (7.1)–(7.10) are in bijection with
ordered triples of distinct worlds in $\mathcal C_d(H)$ having
$L_2(K,H)$. Thus the existence question, allowing arbitrary $d$ and
arbitrary fixed common late readings, is exactly the simultaneous
solvability of this system.

**Proof of necessity.** A legal world gives (7.1) and the positive
denominators in (7.2). The first four ancestor equations force the
four samples (7.2), and uniqueness of degree-at-most-three
interpolation gives precisely (7.3). The actual last two ancestor
equations are (7.7), and the two future sample conditions are (7.8)
by (7.5). If two sources agreed at the common $d$, their first four
gain samples would agree by (7.2), hence their gains and original
drifts would agree. Complete-world distinctness therefore gives
exactly the distinct sources required in (7.1). Definitions give
(7.9), and Proposition 5.1 gives (7.10).

**Proof of sufficiency.** Conditions (7.1) give strictly positive
rank-one trace-one sources. The polynomial (7.3) has degree at most
three and exactly the four samples (7.2), so all first four ancestor
equations hold. It is nonzero: an identically zero gain would force
the distinct readings zero and 24 both to equal $d$.
Conditions (7.7) give the remaining two actual equations for the same
worlds, and (7.8) gives $f_i(6)=0$, $f_i(7)\ne0$.
The affine inverse (7.9) works for either sign of $\lambda$.
Distinct sources ensure distinct complete worlds. Finally (7.10)
and Proposition 5.1 give $L_2(K,H)$ with its actual raw-response
witnesses, permitting a different pair in each terminal column.
The construction and extraction are inverse because all source
entries, gain samples and original drift are fixed by them. ∎

Theorem 2.1 and Theorems 4.1 and 6.1 can be imposed as additional
necessary restrictions without changing this equivalence. No solution
of the system, and no contradiction for all its solutions, is asserted.
This conditional interface does not assemble three worlds from
separately compatible pairs or from separately attainable parameter
extrema.

## 8. Permanent correspondence and unresolved scope

The source-relative deductions here are the repeated-sixth-root
rigidity with its explicit root/drift ranges and normalized sign,
the four three-coordinate terminal injections on the whole promised
class, and their root-multiplicity and collision-incidence consequences
for a simultaneous TT triple. Polynomial factorization, interpolation,
root counting, the intermediate value theorem, quadratic root products,
two-by-two matrix algebra, sign checks and Bernstein conversion are
standard tools within these deductions. No external priority or
literature-completeness claim is made.

| Permanent source | Reused interface and boundary |
| --- | --- |
| [FIB JMMJM Nonzero-Terminal Collision Sparsity and Ratio Diversity](FIB_JMMJM_NONZERO_TERMINAL_COLLISION_SPARSITY_AND_RATIO_DIVERSITY.md), Sections 1–2 and Proposition 7.2 | Complete worlds, all six ancestor equations, normalization for both signs, positive chart, four-terminal inverse and actual-child PP/PT/TP/TT interface. Sections 3 and 5–7 give the established terminal-sign and common-drift residual distinctions. The needed zero-sixth specialization, inverse and raw-response quantifiers are proved in full above; they are baseline reuse. |
| Nonzero-Terminal, Theorem 4.1 and Corollary 4.2 | The five strict ratios and the fixed-sum exchanged-source argument require a nonzero sixth chart gain to infer common $s$. At zero sixth gain this inference fails. Their stronger one-coordinate conclusion is not imported here. |
| Nonzero-Terminal, Theorem 6.1 | The diagonal-swap proof requires a common nonzero $q=f(6)/f(7)$. Here $q=0$; its cancellation is unavailable. The present terminal-triple determinant proof uses only the explicitly displayed positivity and rank-one conditions. |
| [FIB Self-Calibrating Relation Mathematics VII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md), Definitions 1.1–1.3 and equation (4.2) | Original-clock model, actual-fiber recursion, fixed matrices and positive chart. VII credits its terminal reconstruction to V, Theorem 7.1. All algebra needed here is supplied in Sections 1, 3 and 5. |
| VII, Lemma 2.1 and Sections 3–4 | Its roots at six and seven are a distinct class. Neither that lemma, its pair exclusion, its nine coefficient matrices nor their tensor Bernstein identities are premises here. The complete small certificate (2.12)–(2.18) is specific to $(T-6)^2(a+bT)$. |
| VII, Sections 6 and 8–11 | Its separate $MMJM$ known-common-response consumer and its exact-history gain-ray, source-slice, interval, local-inverse and whole-band results retain their own histories and promises. None places the present whole fiber in such a restricted class. |
| [FIB JMMJM Late-Root Rigidity and Terminal Collision Reductions](FIB_JMMJM_LATE_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_REDUCTIONS.md), Sections 1, 5–7 | Full source legality, chronological terminal table, proper-pair versus whole-three quantifiers and common-drift terminal-sign reduction. The terminal-sign deduction above is reuse of this interface with the terminal inverse. No conditional appeal to VII's pair exclusion is needed. |
| Late-Root Rigidity, Theorem 3.1 and its coefficient certificate | Its simultaneous roots at four and five define a different class, with factor $(T-4)(T-5)(a+bT)$ and different polynomials. Its two-world sharpness example is not a zero-sixth TT witness. No coefficient or feasibility conclusion from that class is transferred to the present repeated-sixth class. |

The remaining all-sixth-zero question is whether three distinct legal
worlds satisfy the simultaneous system in Section 7 for some common
$d$ and late readings, with all four terminal columns noninjective.
The surviving configurations include three simple sixth roots, or
two simple sixth roots with the one possible double-sixth world,
subject to the proved sign and pair-incidence restrictions. The
necessary ranges and incidence patterns assert no actual realization.
Neither an exact legal TT witness nor a uniform TT exclusion is given.

The common-drift nonzero-sixth varying-ratio PP system remains outside
this result. Variable drifts, terminal-root strata, other literal
histories, arbitrary-cardinality losing families and their entire
actual fibers retain their own obligations. An injective vector of
three terminal functions supplies no joint physical acquisition of
those functions and no unrestricted single-trajectory decoder.
The finite-set scalar policy in Proposition 5.2 assumes an injective
scalar on the entire supplied known set.

At the earlier $JMMJ$ parent, losing children of its different actions
would still need one simultaneous fixed-ancestor realization. No
parent-arm gluing is provided. The distinct $MMJM$ and $MJMMJ$
histories are not identified with this $JMMJM$ history.
Pairwise restrictions alone neither give a policy on every larger
family nor extract a losing triple from every larger losing family.

The original-root alternative remains
$n_{\mathrm{det}}(3,0)\ge9$ versus a lawful complete-target decoder
on all of $\mathcal W_3$ using at most eight total readings. It still
quantifies over every initial action, actual history and early stop,
all constant drifts, every positive nonsymmetric rank-one trace-one
source, and every nonzero cubic-or-lower gain with both signs and
all sampled roots and multiplicities. The present deductions decide
neither alternative.
