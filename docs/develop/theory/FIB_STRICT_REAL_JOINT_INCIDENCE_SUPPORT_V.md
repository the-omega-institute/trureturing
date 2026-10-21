# FIB strict-real joint incidence: regional whole-child exclusion and a strict M point

## 1. Scope, model, and regional conclusion

This volume records an ordinary exact-rational result for the complete-world model of
[the common-parent volume](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
Definitions 1.1–1.3 and Theorem 2.1. A complete world is

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad 0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
$$

The actions are the original $J$ and $M$, the products are left products, and every
clock $0,\ldots,7$ is read once. The gain $g$, source $P$, and drift $d$ are fixed for
the entire world. Put

$$
H_4=(0,J,24,M,147/5,J,24,M,18),\qquad
C(p,v)=\mathcal F(H_4,M,p,M,v),\qquad p\ne24.
$$

For $W\in C(p,v)$ write

$$
a(W)=d+(T+2j+4r)g(7),\qquad
m(W)=d+(3U+2n)g(7),
$$
where

$$
c=\frac{r(1-r)}b,\qquad j=b+c,\qquad n=j+r,\qquad T=1+b,\qquad U=1+2b.
$$

The strict same-child sets retain the original quantifiers:

$$
\begin{aligned}
(p,v)\in D_J&\iff \exists W_0\ne W_1\in C(p,v),\ a(W_0)=a(W_1),\\
(p,v)\in D_M&\iff \exists W_2\ne W_3\in C(p,v),\ m(W_2)=m(W_3).
\end{aligned}
$$

The two pairs are independently chosen in the same entire child; they may overlap, and
their two common terminal values need not be equal. The original objective is the
unsettled global question about $D_J\cap D_M$ over all real off-$24$ bases.

Define

$$
K=[56,58]\times[304,305],\qquad
R=[3/10,1]\times[13/20,1].
$$

**Theorem 1.1 (Regional whole-child result).** Every complete world in every
$C(p,v)$ with $(p,v)\in K$ has $(r,b)\in R$. For each fixed $p\in[56,58]$,
the regular original response has exactly one source $b=b_p(r)$ in
$[13/20,1]$ for every $r\in[3/10,1]$, and

$$
\frac{d}{dr}a(r,b_p(r))>0.
$$

Consequently terminal $J$ is injective on every entire actual $C(p,v)$ over $K$,
so

$$
D_J\cap K=\varnothing,\qquad (D_J\cap D_M)\cap K=\varnothing.
$$

The endpoint $r=1$ in $R$ is only an analytic extension of the response map. Actual
worlds have $r<1$; this theorem asserts no positive lower bound on $1-r$.

**Theorem 1.2 (A strict M point).** There is a base $(p_*,v_*)\in K$ and distinct
$W_A,W_B\in C(p_*,v_*)$ such that $m(W_A)=m(W_B)$. Thus

$$
(p_*,v_*)\in D_M\setminus D_J.
$$

The point is certified below by a rational contraction argument. This is a regional
component only and is not a global witness or a global exclusion for the original
joint objective.

## 2. Public interfaces and the undivided parent equation

The original full-parent converse is [the common-parent volume](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Theorem 2.1. In the notation here put $e=d-24$. The four interpolated samples of the one entire gain are

$$
\bigl(g(0),g(1),g(2),g(3)\bigr)=
\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right).
$$

The fixed-node rows at clocks $4,5,6,7$ are respectively

$$
(-1,4,-6,4),\quad(-4,15,-20,10),\quad
(-10,36,-45,20),\quad(-20,70,-84,35).
$$

The parent equation, with no division by $e$, $\Lambda$, a gain sample, or a gain
coefficient, is

$$
\Lambda e=-D,\qquad
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad
D=\frac{24}{5}\left(b-\frac18\right)\left(\frac6T-\frac2U\right).
\tag{2.1}
$$

The clock-four identity that checks the equation is

$$
g(4)-\frac{18-(24+e)}U
=e\Lambda+\frac{24}{5}\left(b-\frac18\right)\left(\frac6T-\frac2U\right).
\tag{2.2}
$$

The first four original readings are therefore identically $0,24,147/5,24$, and
(2.1) is necessary and sufficient for the fourth reading $18$. Fixed-node
interpolation supplies one whole polynomial of degree at most three, including all
lower-degree and sampled-zero cases. It cannot be identically zero because the first
two original readings differ.

For the regional cover, use only [support IV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IV.md),
Theorem 12.1, in the form

$$
b<30,\qquad c<10,\qquad j>1/16,\qquad |e|<655000
\tag{2.3}
$$

for every actual companion over $K$. No $\Lambda$ separation, selected-endpoint
collar, or boundary classification from that theorem is used here.

## 3. Exact all-companion localization circuit

Set $z=j=b+c$. Every actual companion over $K$ is contained in the closed initial
source box

$$
\mathcal B_0=[0,1]_r\times[0,30]_b\times[1/16,40]_z,
\qquad E_0=[-655000,655000]_e.
$$

The upper bound $40$ follows from (2.3), and strict inequalities are enlarged only
for enclosure. On a source box $I=I_r\times I_b\times I_z$, define

$$
T=1+b,\quad U=1+2b,\quad n=z+r,
$$

and the six rational coefficient circuits

$$
\begin{aligned}
\Lambda&=1+6/T+1/U-4/z-4/n,\\
D&=(24/5)(b-1/8)(6/T-2/U),\\
p_0&=24+(U+n)(96-108/T),\\
A&=1+(U+n)(4-15/z+20/T-10/n),\\
v_0&=24+(2U+n)(240-243/T),\\
B&=1+(2U+n)(10-36/z+45/T-20/n).
\end{aligned}
\tag{3.1}
$$

The three common-$e$ equations are

$$
b(z-b)=r(1-r),\qquad
\Lambda e=-D,\qquad
Ae=p-p_0,\qquad Be=v-v_0.
\tag{3.2}
$$

The last two identities are the acquired-response identities from the entire
interpolant. They hold as rational identities even away from (2.1), so interval
rejection using them is sound.

### 3.1 Closed rational interval rules

All endpoints are rationals. For intervals $I,J$, addition and subtraction use the
endpoint rules, and multiplication is the minimum and maximum of the four endpoint
products. A reciprocal is formed as $[1/u,1/l]$ only when $0\notin[l,u]$.
Every composite expression is evaluated by these rules in the displayed circuit
order. No floating-point operation is part of the certificate.

The deterministic visit procedure is the following.

1. If
   
   $$
   \inf I_r\ge3/10,\qquad \inf I_b\ge13/20,
   \qquad \sup I_b\le1,
   $$
   retain the source box immediately. This early-retain rule is an enclosure rule;
   it never discards a point.

2. Otherwise intersect $I_z$ with
   $[\inf I_b,\sup I_b+10]$. If the lower endpoint of $I_b$ is positive, also
   intersect it with the natural interval evaluation of
   
   $$
   b+\frac{r(1-r)}b.
   $$
   An empty intersection is discarded. The division is skipped when $0\in I_b$.

3. Evaluate the rank residual $b(z-b)-r(1-r)$. Discard if its interval excludes
   zero. The tightened $z$ interval is used for all subsequent evaluations, while
   the original $I_r,I_b,I_z$ remain the splitting box.

4. Initialize $E=E_0$. In order, use the pairs
   
   $$
   (a,h)=(\Lambda,-D),\quad
   (A,[56,58]-p_0),\quad
   (B,[304,305]-v_0).
   $$
   Whenever $0\notin a$, replace $E$ by the exact interval intersection
   $E\cap(h/a)$. If $E$ becomes empty, discard immediately. If $0\in a$, do not
   divide and retain that branch for the residual tests; in particular
   coefficient-zero and $\Lambda=0$ branches are not silently removed.

5. With the resulting common interval $E$, evaluate all three residuals
   
   $$
   \Lambda E+D,\qquad AE-([56,58]-p_0),\qquad
   BE-([304,305]-v_0).
   $$
   Discard if any residual interval excludes zero.

6. Otherwise bisect the original source box at a rational midpoint. Choose the
   coordinate maximizing
   
   $$
   \left(\operatorname{width}(I_r),\quad
   \operatorname{width}(I_b)/3,\quad
   \operatorname{width}(I_z)/4\right),
   $$
   with ties resolved in the order $r,b,z$. Visit the lower half before the upper
   half. The two closed halves cover the original box exactly.

The recursion has no runtime cap and accepts no unresolved box. The resulting exact cover has

$$
\begin{array}{c|c}
\text{quantity}&\text{value}\\ \hline
\text{visited nodes}&204939\\
\text{discarded leaves}&101831\\
\text{retained leaves}&639\\
\text{maximum depth}&49\\
\text{unresolved leaves}&0
\end{array}
$$

and the retained leaves satisfy

$$
\inf r\ge\frac{1229}{4096},\qquad
\inf b\ge\frac{1335}{2048},\qquad
\sup b\le\frac{255}{256}.
\tag{3.3}
$$

Thus every actual companion is enclosed in $R$. The node count also satisfies
$204939=2(101831+639)-1$. The finite cover removes only points violating a necessary
rank equation, one of the four supplied bounds, or one of the common-$e$ equations;
all retained branches share the same $E$. Therefore no actual companion is lost, and
termination is the finite exact cover recorded above and is independent of any
runtime or depth cap.

## 4. Integer regular-response circuit

On the regular domain $\Lambda\ne0$, use the circuit of [support II](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md), Definition 2.2 and Proposition 2.3. In $\mathbb Z[r,b]$ define

$$
\begin{gathered}
X=b^2+r-r^2,\qquad N=X+rb,\qquad T=1+b,\qquad U=1+2b,\\
L=(b^2+8b+4)XN-2bTU(X+N),\qquad \ell=2L,\\
E=-6(8b-1)(2+5b)XN,\qquad d_N=120\ell+E,\qquad Q=5bT\ell,\\
q=\bigl(-d_NT,\;6(8b-1)(2+5b)bNT,\;27\ell-E,
\;6(8b-1)(2+5b)bXT\bigr).
\end{gathered}
\tag{4.1}
$$

Let the integer row products be

$$
\begin{aligned}
G_5&=(-4,15,-20,10)\mathbin{\cdot}q,\\
G_6&=(-10,36,-45,20)\mathbin{\cdot}q,\\
G_7&=(-20,70,-84,35)\mathbin{\cdot}q.
\end{aligned}
$$

Define

$$
\begin{aligned}
P&=d_NbT+(bU+N)G_5,\\
V&=d_NbT+(2bU+N)G_6,\\
Z&=d_NbT+(bT+2X+4rb)G_7,\\
W&=d_NbT+(3bU+2N)G_7.
\end{aligned}
\tag{4.2}
$$

The identities $j=X/b$, $n=N/b$,
$\Lambda=\ell/(TUXN)=2L/(TUXN)$, $e=E/(5\ell)$, and
$d=d_N/(5\ell)$ show directly that $q/(5T\ell)$ is the four original gain
samples. Consequently the original whole response is exactly

$$
(p,v,a,m)=\left(\frac P Q,\frac V Q,\frac Z Q,\frac W Q\right).
\tag{4.3}
$$

This is an identity for the one fixed interpolating gain, not a response projection
with independent gain values. The original parent correspondence of Theorem 2.1 and
[support III](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md), Definitions 1.1–1.2
and 10.1 with Lemma 10.2, supplies the converse, including zero leading
coefficients, lower degrees, zero drift, and the complete original clocks.

For a polynomial $f$ among $P,Z$, set

$$
N_{f,t}=(\partial_t f)Q-f(\partial_tQ),\qquad t\in\{r,b\}.
$$

The following divisions have exact zero remainder in $\mathbb Z[r,b]$:

$$
B_p=\frac{N_{P,b}}{120T^2},\qquad
C_J=\frac{N_{Z,r}N_{P,b}-N_{Z,b}N_{P,r}}
{3600b^2T^4L}.
\tag{4.4}
$$

Differentiating the displayed rational circuit gives the checkable identities

$$
\Lambda=\frac{2L}{TUXN},\qquad
\partial_b p=\frac{6B_p}{5b^2L^2},\qquad
(\partial_ra)(\partial_bp)-(\partial_ba)(\partial_rp)
=\frac{9C_J}{25b^2L^3}.
\tag{4.5}
$$

All denominators in (4.3)–(4.5) are guarded on $R$ below; no division is used on
the discarded zero branches of Section 3.

## 5. Bernstein signs on the regional rectangle

For a polynomial $f$ of coordinate degrees $(n,m)$, first substitute

$$
 r=\frac3{10}+\frac7{10}s,\qquad
 b=\frac{13}{20}+\frac7{20}t,\qquad 0\le s,t\le1,
$$

and write $f=\sum_{i,j}c_{ij}s^it^j$. Its tensor Bernstein coefficient is

$$
\beta_{k\ell}=
\sum_{i\le k,\ j\le\ell}c_{ij}
\frac{\binom{k}{i}}{\binom{n}{i}}
\frac{\binom{\ell}{j}}{\binom{m}{j}}.
\tag{5.1}
$$

The Bernstein convex-hull property reduces each sign to the minimum of its exact
rational coefficients. The five checks have $35+143+288+7+7=480$ coefficients:

$$
\begin{array}{c|c|c|c}
\text{polynomial}&(\deg_r,\deg_b)&\text{coefficient count}&\text{minimum coefficient}\\ \hline
-L&(4,6)&35&42570057/32000000\\
B_p&(10,12)&143&7085797469216029393/102400000000000000\\
-C_J&(15,17)&288&72157265456855164438356699/1024000000000000000000\\
(P-56Q)|_{b=13/20}&(6,0)&7&15519730743/640000000\\
(58Q-P)|_{b=1}&(6,0)&7&1096
\end{array}
\tag{5.2}
$$

The first three minima occur at Bernstein indices $(2,0),(4,0),(11,0)$ and the
last two at $(1,0),(6,0)$, respectively. Every coefficient in (5.2) is positive.
Hence on $R$, $L<0$, $\ell<0$, $Q<0$, $B_p>0$, and $C_J<0$. Equations (4.5)
then give

$$
\partial_b p>0,\qquad
(\partial_ra)(\partial_bp)-(\partial_ba)(\partial_rp)>0.
\tag{5.3}
$$

The boundary checks in (5.2), together with $Q<0$, give

$$
 p(r,13/20)<56,\qquad p(r,1)>58
\quad(3/10\le r\le1).
\tag{5.4}
$$

Therefore the intermediate value theorem and $\partial_b p>0$ give exactly one
$b_p(r)\in(13/20,1)$ with $p(r,b_p(r))=p$, for every
$p\in[56,58]$ and $r\in[3/10,1]$. The implicit-function theorem applies there, and
(5.3) yields

$$
\frac{d}{dr}a(r,b_p(r))
=\frac{(\partial_ra)(\partial_bp)-(\partial_ba)(\partial_rp)}
{\partial_bp}>0.
\tag{5.5}
$$

## 6. Entire-child terminal-J injectivity

Take any $(p,v)\in K$ and any two worlds $W,W'\in C(p,v)$ with
$a(W)=a(W')$. Section 3 applies to every companion, including companions not selected
for a proposed pair, so both sources lie in $R$. Section 4 is regular on $R$ because
$L<0$ and $X,N,T,U>0$. By (5.4)–(5.5), each world has the unique representation
$b=b_p(r)$ and the terminal-$J$ value is strictly increasing with $r$.
The equality $a(W)=a(W')$ therefore implies $r=r'$, then $b=b'$. The undivided
full-parent correspondence in Theorem 2.1, equivalently III, Lemma 10.2, fixes
$e$ from (2.1), then fixes $d$ and the entire interpolating gain from its four
samples. Thus $W=W'$. This proves Theorem 1.1, including the unused companions.

No terminal-$M$ equality, selected-endpoint restriction, or pair-overlap assumption
was used in this injectivity argument.

## 7. Certified strict equal-M point

Set

$$
r_A=\frac{99}{100},\qquad x=(b_A,r_B,b_B),
$$

and put $F=(p_A-p_B,v_A-v_B,m_A-m_B)$. All interval values and derivatives
in this section use the public original gain-sample lift of
[support II](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md), Definition 2.1,
in the following evaluation order. For each world, first compute
$c=r(1-r)/b$, $j=b+c$, $n=j+r$, $T=1+b$, and $U=1+2b$.
Then compute $\Lambda,D$ by (2.1), $e=-D/\Lambda$, and $d=24+e$.
Evaluate the four gain samples displayed in Section 2, and apply its interpolation
rows at clocks $5,6,7$ to obtain $g(5),g(6),g(7)$, respectively. Each row product
is summed in sample order $0,1,2,3$. Next form
$p=d+(U+n)g(5)$, $v=d+(2U+n)g(6)$, and $m=d+(3U+2n)g(7)$,
then take the two-world differences defining $F$. These are the original
whole-gain responses identified with (4.3); the bounds (7.2)–(7.5) use the
gain-sample evaluation order just specified.

Let the exact rational center be

$$
\bar x=\left(
0.895717129219469386,
0.938647204769207016,
0.875817481084238252
\right),
$$

and let

$$
\mathcal Q=\{x:\|x-\bar x\|_\infty\le10^{-10}\}.
$$

The explicit rational preconditioner is

$$
R_*=10^{-8}
\begin{pmatrix}
-546967580&154697260&-16273831\\
-1318809200&516408400&-77174079\\
-1041709400&350131100&-45748945
\end{pmatrix},
$$

with

$$
\det R_*=
\frac{2835442353395849767}{500000000000000000000}\ne0.
\tag{7.1}
$$

On the entire closed cube $\mathcal Q$, value intervals use the rational rules of
Section 3. Derivative intervals use

$$
(uv)'=u'v+uv',\qquad
(u/v)'=\frac{u'-(u/v)v'}{v},
$$

and every quotient denominator is required to exclude zero. Exact interval
automatic differentiation gives the three row-sum bounds

$$
\operatorname{rowsum}_i(I-R_*DF(x))
<\left(\frac{25559}{10^8},\frac{71315}{10^8},
\frac{51557}{10^8}\right)_i.
\tag{7.2}
$$

Exact singleton evaluation at $\bar x$ gives

$$
\|R_*F(\bar x)\|_\infty<\frac3{10^{19}}.
\tag{7.3}
$$

Thus $q:=\|I-R_*DF\|_\infty<1/1000$. For $\rho=10^{-10}$,

$$
\|x-R_*F(x)-\bar x\|_\infty
\le \|R_*F(\bar x)\|_\infty+q\rho
<\rho.
$$

The map $x\mapsto x-R_*F(x)$ is therefore a strict self-map and contraction of
$\mathcal Q$. Banach's theorem gives a fixed point $x_*$ in its interior. By
(7.1), $R_*$ is invertible, so the fixed-point equation is $F(x_*)=0$. The three
equalities are exact rational bounds on the whole cube, and the equalities follow
from this certified zero rather than from overlapping response enclosures.

The strict guards on the two reconstructed worlds are

$$
\begin{array}{c|c|c}
& A&B\\ \hline
b&(0.895717,0.895718)&(0.875817,0.875818)\\
r&(0.99)&(0.938647,0.938648)\\
j&(0.906769,0.906770)&(0.941571,0.941572)\\
 n&(1.896769,1.896770)&(1.880218,1.880219)\\
\Lambda&(-1.996844,-1.996843)&(-1.813603,-1.813602)\\
e&(4.536296,4.536297)&(4.911799,4.911800)
\end{array}
\tag{7.4}
$$

Here $c=r(1-r)/b>0$, $bc=r(1-r)$, and $d=24+e$ is one fixed drift for each
world. The strict source and regular divisions follow from (7.4); the entire gain
is the nonzero degree-at-most-three interpolant of the original samples. Both worlds
use the original clocks $0,\ldots,7$ and only the original $J/M$ products, with no
extra operation or acquired label. On the whole cube $r_A>r_B$, so the two worlds
are distinct while both satisfy $0<r<1$, $b>0$, and all original-clock guards.

The response enclosures, valid for each of the two worlds throughout the cube, are

$$
57.024793<p<57.024796,\qquad
304.771484<v<304.771493,\qquad
1227.801824<m<1227.801848.
\tag{7.5}
$$

At $x_*$, $F(x_*)=0$, so the two worlds have equal acquired $(p,v)$ and equal
terminal $m$. The first two inequalities in (7.5) put their common base strictly
inside $K$ (and in particular $p_*\ne24$); (7.4) gives strict distinctness and
legal original worlds. Theorem 1.1
then gives $D_J$ exclusion for the entire child, while the equal-$m$ pair gives
$D_M$ membership. This proves Theorem 1.2.

## 8. Boundary of the result and preserved global objective

The volume proves only

$$
D_J\cap K=\varnothing,\qquad
D_M\cap D_J\cap K=\varnothing,\qquad
D_M\setminus D_J\ne\varnothing.
$$

It does not classify either collision locus outside $K$, continue the exclusion beyond
$K$, or construct a joint configuration. The original objective still requires
independently chosen distinct $J$ and $M$ pairs in one complete child, with possible
pair overlap and separate terminal values. No assertion here changes those quantifiers.
The $r=1$ rectangle edge in Sections 1 and 5 is an analytic response extension only;
actual worlds remain $r<1$ and no $1-r$ margin is claimed.

The proof uses the public whole-parent correspondence (common-parent Theorem 2.1;
III Definitions 1.1, 1.2, 10.1 and Lemma 10.2), the public regular integer circuit
(II Definition 2.2 and Proposition 2.3), and only the four all-companion bounds from
IV Theorem 12.1. Interval arithmetic, Bernstein convex-hull positivity, the
implicit-function theorem, and Banach contraction are classical tools applied to the
explicit circuits above. Every constant, division guard, recursion rule, polynomial
identity, coefficient minimum, and contraction bound needed for this regional result
is stated in this volume.

## 追加锚（本行以下为增补区）
