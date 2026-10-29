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

## 9. Enlarged whole-child rectangle

**Definition 9.1 (Enlarged base and inherited worlds).** Retain exactly the
complete worlds, literal history, entire children, and independently selected
pairs of Section 1. Put

$$
K_+=[56,58]\times[304,306],\qquad
R=[3/10,1]\times[13/20,1].
\tag{9.1}
$$

Thus each world still has one strict rank-one trace-one source, one fixed real
drift, and one whole nonzero real gain of degree at most three. All original
clocks, lower degrees, sampled gain zeros, repeated roots, zero drift, and
companions unused by a selected pair remain in the domain. In particular no
regularity condition is added to $C(p,v)$.

**Theorem 9.2 (Enlarged entire-child terminal-J exclusion).** For every
$(p,v)\in K_+$ and all complete worlds $W,W'\in C(p,v)$,

$$
a(W)=a(W')\quad\Longrightarrow\quad W=W'.
\tag{9.2}
$$

Consequently

$$
D_J\cap K_+=\varnothing,\qquad
(D_J\cap D_M)\cap K_+=\varnothing.
\tag{9.3}
$$

There is no hypothesis about terminal $M$, the locations of selected $J$
endpoints, or overlap between the two pairs. The source edge $r=1$ in $R$ is
used only for analytic extension; actual worlds still satisfy $r<1$.

*Proof.* Lemma 10.2 places every actual companion over $K_+$ in $R$, using the
undivided parent. Section 11 then applies the unchanged integer-response and
Bernstein certificates of Sections 4–5 to all these companions and proves
(9.2). The new input is the enlarged all-companion localization of Section 10;
Theorem 1.1, whose upper $v$ bound is $305$, is not an exclusion theorem for
$K_+$. ∎

## 10. Exact finite cover for the enlarged rectangle

**Definition 10.1 (Closed rational cover).** Set

$$
S=2^{80}=1208925819614629174706176,\qquad
\mathcal B_0=[0,1]_r\times[0,30]_b\times[1/16,40]_z,
\qquad E_0=[-655000,655000].
\tag{10.1}
$$

Here $z=j$, rather than a further free physical parameter. A rational constant
$q$ is enclosed by

$$
\langle q\rangle_S=
\left[\frac{\lfloor Sq\rfloor}{S},
      \frac{\lceil Sq\rceil}{S}\right].
\tag{10.2}
$$

Every interval endpoint in this definition belongs to $S^{-1}\mathbb Z$.
For $I=[l,u]$, $J=[v,w]$, addition is $[l+v,u+w]$, negation is
$[-u,-l]$, and subtraction is addition of the negative. For multiplication
let $H=\{lv,lw,uv,uw\}$ and use

$$
I\odot J=
\left[\frac{\lfloor S\min H\rfloor}{S},
      \frac{\lceil S\max H\rceil}{S}\right].
\tag{10.3}
$$

If $0\notin J$, division uses the same formula with
$H=\{l/v,l/w,u/v,u/w\}$. It is one outward rounding of these four
quotients, not multiplication by a separately rounded reciprocal. No quotient
is defined when its divisor interval contains zero. Intersection is the exact
endpoint intersection, empty when its lower endpoint exceeds its upper
endpoint. All comparisons with rational thresholds are exact rational
comparisons. These conventions also specify the enclosure of every rational
constant occurring inside a composite expression.

Use the six existing coefficient circuits $(\Lambda,D,p_0,A,v_0,B)$ of
(3.1), with the same meaning as in that equation. To fix their interval
evaluation completely, first form $T=1+b$, $U=1+2b$, $n=z+r$, and then
$U+n$ and $2U+n$. The additive grouping in $\Lambda,A,B$ is respectively

$$
\begin{aligned}
&(((1+6/T)+1/U)-4/z)-4/n,\\
&1+(U+n)(((4-15/z)+20/T)-10/n),\\
&1+(2U+n)(((10-36/z)+45/T)-20/n).
\end{aligned}
\tag{10.4}
$$

In $D$, first multiply $\langle24/5\rangle_S$ by
$b-\langle1/8\rangle_S$, then multiply by $6/T-2/U$.
The circuits for $p_0,v_0$ are grouped exactly as in (3.1). Every displayed
binary operation uses (10.2)–(10.3), in the specified order.

The visit of an original source box
$I=I_r\times I_b\times I_z$ is the following ordered mathematical recursion.

1. If $\inf I_r\ge3/10$, $\inf I_b\ge13/20$, and $\sup I_b\le1$,
   terminate with a retained box. This test precedes all other tests.

2. Otherwise set
   $J_z=I_z\cap[\inf I_b,\sup I_b+10]$.
   If this is empty, terminate with a $z$ rejection. Form
   $H=I_r\odot(1-I_r)$. If $\inf I_b>0$, further replace
   $J_z$ by $J_z\cap(I_b+H/I_b)$, again terminating with a $z$
   rejection if empty. If $\inf I_b=0$, skip this quotient.

3. Evaluate $I_b\odot(J_z-I_b)-H$. If it excludes zero, terminate
   with a rank rejection. For the rest of this visit only, evaluate the six
   circuits (3.1) at $(I_r,I_b,J_z)$. The original splitting box is still
   $(I_r,I_b,I_z)$.

4. Start afresh with $E=E_0$. In the stated order form

   $$
   (a_0,h_0)=(\Lambda,-D),\qquad
   (a_1,h_1)=(A,[56,58]-p_0),\qquad
   (a_2,h_2)=(B,[304,306]-v_0).
   \tag{10.5}
   $$

   For $i=0,1,2$, if $0\notin a_i$, replace $E$ by
   $E\cap(h_i/a_i)$; an empty intersection terminates with an $e$
   rejection. If $0\in a_i$, skip only that quotient, keeping the
   equation for the next step. The three coefficient and right-hand-side
   intervals are not recomputed during these intersections.

5. Using the final common $E$, test the three intervals
   $a_i\odot E-h_i$ in the order $i=0,1,2$. If any excludes zero,
   terminate with a residual rejection.

6. Otherwise split the original box. Choose the coordinate with largest
   normalized width

   $$
   \left(\operatorname{width}(I_r),
          \frac{\operatorname{width}(I_b)}3,
          \frac{\operatorname{width}(I_z)}4\right),
   \tag{10.6}
   $$

   resolving ties in the order $r,b,z$. If its interval is $[l,u]$, set
   $m=S^{-1}\lfloor S(l+u)/2\rfloor$ and visit the two closed
   intervals $[l,m]$ and $[m,u]$, lower half first. If $m$ is not
   strictly between $l$ and $u$, the box is unresolved and cannot be
   retained or rejected by this step. Tightened $J_z$ and $E$ are not
   inherited by the children; each child begins again at step 1.

There is no other stopping or acceptance rule. Depth starts at zero for
$\mathcal B_0$. For a level-by-level definition, let $\mathcal F_0$ contain
only $\mathcal B_0$; classify every member of $\mathcal F_d$ by the six
steps and let $\mathcal F_{d+1}$ consist of the two children of every split
box. Thus a zero split count at a level ends this finite recursion if that
level contains no unresolved box.

**Lemma 10.2 (All companions and the complete enlarged cover).** Every actual
complete world over $K_+$ starts in $\mathcal B_0$ with $e=d-24\in E_0$.
The recursion of Definition 10.1 has $206439$ nodes, $640$ retained leaves,
$102580$ rejected leaves, maximum depth $49$, and no unresolved leaves.
Every actual source is in a retained box, and in particular lies in $R$.

*Proof.* The source estimates in [support IV](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IV.md),
Theorem 8.3, have the following precise dependence on the acquired response:
its proof excludes $b\ge30$ and $c\ge10$ whenever $p\ge0$, and excludes
$j\le1/16$ whenever $p\ge33$. Those arguments do not use $v$. Since
$p\ge56$ on $K_+$, they give

$$
b<30,\qquad c<10,\qquad 1/16<j=b+c<40,
\qquad U<61,\quad n=j+r<41.
\tag{10.7}
$$

For the drift estimate, use IV, (8.2), (9.1)–(9.3), on their stated global
domain $b\ge0,n>0$. To distinguish their two drift coefficients from the
ambient coefficients $A,B$ in (3.1), write them as
$A_{\rm IV},B_{\rm IV}$. The parameter correspondence is the same
$b,T,U,n,e=d-24$, and the identities on the undivided original parent are

$$
\begin{gathered}
C_5=\frac{3(8b-1)(b+2)}{2TU},\qquad
C_6=\frac{3(80b^2+192b+31)}{5TU},\\
P_0=(U+n)C_5,\qquad V_0=(2U+n)C_6,\\
p-24=P_0+eA_{\rm IV},\qquad
v-24=V_0+eB_{\rm IV},\qquad
\max\{|A_{\rm IV}|,|B_{\rm IV}|\}>1/100.
\end{gathered}
\tag{10.8}
$$

Here the last inequality is the global coefficient-separation part of IV,
Theorem 9.1, not its conclusion restricted to $v\le305$. Its proof also
gives $|C_5|\le12$ and $0<C_6\le192/5$ for all $b\ge0$. Consequently

$$
|P_0|<102\cdot12=1224,\qquad
|V_0|<163\cdot\frac{192}{5}=\frac{31296}{5}.
\tag{10.9}
$$

On the enlarged rectangle $|p-24|\le34$ and $|v-24|\le282$. Selecting
whichever coefficient in (10.8) has magnitude greater than $1/100$ proves

$$
|e|<100\max\left\{34+1224,\ 282+\frac{31296}{5}\right\}
=654120<655000.
\tag{10.10}
$$

This derives the initial enclosure for $v\le306$ directly. No division by
$e$, $d$, $\Lambda$, a gain sample, or a leading coefficient occurs in
(10.7)–(10.10). The values $e=0$ and $d=0$ are included.

The necessary equations for every actual point of the initial box are exactly
(3.2), with $p\in[56,58]$ and $v\in[304,306]$. In particular the same
single scalar $e$ satisfies all three equations (10.5). On the initial box,
$T,U\ge1$, $z\ge1/16$, and $n=z+r\ge1/16$; tightening $z$ preserves
these inequalities. Thus every denominator in (3.1) is positive throughout
each visit. The only additional quotients in the recursion are explicitly
guarded by exclusion of zero from the whole divisor interval.

The finite rational evaluation of Definition 10.1 is given below. At depth
$d$, the columns count split boxes, retained boxes, and the four mutually
exclusive first rejection types, respectively. In every row the unresolved
count is zero. The row sum is $|\mathcal F_d|$; the next row sum is twice
the current split count. These rows specify the complete evaluation from the
single initial box through the empty next frontier.

| $d$ | split | retain | $z$ | rank | $e$ | residual |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 1 | 0 | 0 | 0 | 0 | 0 |
| 1 | 2 | 0 | 0 | 0 | 0 | 0 |
| 2 | 4 | 0 | 0 | 0 | 0 | 0 |
| 3 | 5 | 0 | 3 | 0 | 0 | 0 |
| 4 | 8 | 0 | 2 | 0 | 0 | 0 |
| 5 | 12 | 0 | 4 | 0 | 0 | 0 |
| 6 | 17 | 0 | 7 | 0 | 0 | 0 |
| 7 | 25 | 0 | 9 | 0 | 0 | 0 |
| 8 | 35 | 0 | 15 | 0 | 0 | 0 |
| 9 | 66 | 0 | 4 | 0 | 0 | 0 |
| 10 | 98 | 0 | 34 | 0 | 0 | 0 |
| 11 | 134 | 0 | 62 | 0 | 0 | 0 |
| 12 | 258 | 0 | 10 | 0 | 0 | 0 |
| 13 | 390 | 0 | 126 | 0 | 0 | 0 |
| 14 | 524 | 0 | 256 | 0 | 0 | 0 |
| 15 | 1036 | 0 | 12 | 0 | 0 | 0 |
| 16 | 1518 | 14 | 504 | 2 | 32 | 2 |
| 17 | 2016 | 0 | 983 | 4 | 26 | 7 |
| 18 | 3860 | 3 | 34 | 4 | 119 | 12 |
| 19 | 863 | 0 | 1719 | 30 | 5044 | 64 |
| 20 | 1278 | 0 | 239 | 4 | 175 | 30 |
| 21 | 2321 | 0 | 78 | 7 | 111 | 39 |
| 22 | 795 | 50 | 1584 | 51 | 2079 | 83 |
| 23 | 1001 | 0 | 320 | 2 | 254 | 13 |
| 24 | 1620 | 0 | 190 | 4 | 182 | 6 |
| 25 | 1276 | 109 | 498 | 11 | 1312 | 34 |
| 26 | 1429 | 0 | 435 | 0 | 653 | 35 |
| 27 | 2269 | 19 | 185 | 4 | 346 | 35 |
| 28 | 1630 | 179 | 670 | 8 | 1970 | 81 |
| 29 | 1832 | 0 | 542 | 0 | 812 | 74 |
| 30 | 2892 | 25 | 249 | 3 | 444 | 51 |
| 31 | 2299 | 197 | 893 | 7 | 2207 | 181 |
| 32 | 2433 | 0 | 811 | 0 | 1149 | 205 |
| 33 | 3903 | 0 | 402 | 0 | 496 | 65 |
| 34 | 3563 | 0 | 1304 | 4 | 2707 | 228 |
| 35 | 4241 | 0 | 1594 | 0 | 1246 | 45 |
| 36 | 6886 | 0 | 626 | 0 | 970 | 0 |
| 37 | 6104 | 0 | 2065 | 0 | 5603 | 0 |
| 38 | 7188 | 0 | 2659 | 0 | 2361 | 0 |
| 39 | 11182 | 29 | 912 | 0 | 2253 | 0 |
| 40 | 6944 | 0 | 2833 | 0 | 12587 | 0 |
| 41 | 5892 | 0 | 1844 | 0 | 6152 | 0 |
| 42 | 7468 | 15 | 279 | 0 | 4022 | 0 |
| 43 | 1877 | 0 | 772 | 0 | 12287 | 0 |
| 44 | 1574 | 0 | 570 | 0 | 1610 | 0 |
| 45 | 1929 | 0 | 84 | 0 | 1135 | 0 |
| 46 | 329 | 0 | 189 | 0 | 3340 | 0 |
| 47 | 115 | 0 | 28 | 0 | 515 | 0 |
| 48 | 77 | 0 | 0 | 0 | 153 | 0 |
| 49 | 0 | 0 | 0 | 0 | 154 | 0 |
| total | 103219 | 640 | 26639 | 145 | 74506 | 1290 |

For the original boxes retained by step 1, the coordinate extrema of this
recursion are

$$
\begin{aligned}
\min\inf I_r&=1229/4096,&\quad \max\sup I_r&=1,\\
\min\inf I_b&=1335/2048,& \max\sup I_b&=255/256,\\
\min\inf I_z&=1/16,& \max\sup I_z&=1981/1024.
\end{aligned}
\tag{10.11}
$$

The four rejected-leaf totals sum to $102580$, and
$206439=2(102580+640)-1$. At depth $49$ all $154$ boxes terminate by
the common-$e$ intersection test; the split count is zero, so
$\mathcal F_{50}$ is empty. In particular the table ends by the actual
branch rules, not by imposing a depth cutoff. The grid-stall alternative in
step 6 never occurs in this finite evaluation.

For completeness, interval inclusion supplies the logical connection between
this finite evaluation and the original quantified assertion. Each elementary
operation (10.2)–(10.3) contains every real result of that operation on its
argument intervals: addition and subtraction are monotone in their indicated
endpoints; multiplication has its extrema among the four corner products;
division has its extrema among the four corner quotients when the divisor
has constant sign. Floor and ceiling only enlarge those extrema. Structural
induction therefore gives inclusion for every displayed composite circuit.
These are the ordinary interval rules of Moore–Kearfott–Cloud,
*Introduction to Interval Analysis*, applied here with an explicitly fixed
outward rational grid.

An actual point survives the $z$ intersections because $c<10$ and
$z=b+r(1-r)/b$. It survives the rank test because its rank residual is
zero. If its scalar $e$ lies in $E$ before an intersection in step 4, the
equation $a_i e=h_i$ puts that same scalar in the quotient enclosure and
hence in the intersection. When $0\in a_i$, skipping division removes
nothing. It survives every final residual test because its three residuals
vanish using this same $e$. Finally each split covers its original box by
two closed halves. Induction down the resulting finite tree puts every
actual point in a retained box. Step 1 and (10.11) place all such sources
in $R$.

In particular no $\Lambda=0$ point was removed by an unguarded quotient.
Coefficient-zero cases, zero gain samples, lower degrees and every unused
companion have been retained until excluded by these necessary equations or
placed in $R$. This is the new finite cover with upper $v$ bound $306$;
the cover table of Section 3 has upper bound $305$ and does not replace
this calculation. ∎

## 11. Whole-child consumer of the inherited regional signs

*Proof of Theorem 9.2.* Use exactly $X,N,L,\ell,E,d_N,Q,P,V,Z,W,B_p,C_J$
from (4.1)–(4.4), with the same variables $r,b$. In particular
$X=bj$, $N=bn$, $\ell=2L$, $e=E/(5\ell)$, and the response
correspondence is precisely (4.3). These are the original interpolating
gain and fixed drift of Section 2, identified with complete worlds by the
zero-safe converse of [the common-parent volume](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
Theorem 2.1. There is no second gain circuit or new terminal observation.

The five polynomial certificates (5.1)–(5.2) are on the same closed $R$
as in (9.1). Neither their polynomials nor their affine Bernstein
substitution involves $v$. Their positive coefficient minima therefore
still give, on all of $R$,

$$
L<0,\quad Q<0,\quad B_p>0,\quad C_J<0,
\qquad p_b>0,\quad a_rp_b-a_bp_r>0,
\tag{11.1}
$$

and the same boundary inequalities (5.4). The sign argument uses the
nonnegative tensor Bernstein basis and its partition of unity, namely the
classical convex-hull property; see Patrikalakis–Maekawa–Cho,
*Shape Interrogation*, [Section 1.3.4](https://web.mit.edu/hyperbook/Patrikalakis-Maekawa-Cho/node12.html).
Only the companions to which these existing signs apply have changed:
Lemma 10.2 now places the entire child over every point of $K_+$ in $R$.

Fix $p\in[56,58]$. The boundary inequalities and $p_b>0$ give one
and only one $b_p(r)\in(13/20,1)$ for each $r\in[3/10,1]$.
The implicit-function theorem, applied to this rational map where its
denominators are nonzero, gives the derivative (5.5), strictly positive
by (11.1). The graph need not keep $v$ in $[304,306]$ between its
points: the derivative signs hold on the whole source rectangle $R$.
Thus the usual one-variable monotonicity argument compares any two
points on this graph.

Now take any $W,W'\in C(p,v)$ with $(p,v)\in K_+$ and
$a(W)=a(W')$. Lemma 10.2 applies separately to these two worlds and
to every other companion, so both sources belong to $R$. Strict
monotonicity on $b=b_p(r)$ gives $r=r'$, and uniqueness of $b_p(r)$
then gives $b=b'$. Since $X,N,T,U>0$ on $R$, (4.5) and $L<0$
give $\Lambda\ne0$. The undivided parent (2.1) now fixes $e$, hence
the one drift $d=24+e$. Its first four gain samples in Section 2 fix
the entire degree-at-most-three polynomial uniquely by fixed-node
interpolation. The latter is the classical Lagrange interpolation
principle; see Berrut–Trefethen, *Barycentric Lagrange Interpolation*,
Section 2. Thus the complete triples coincide, proving (9.2)–(9.3).

This use of the regional signs occurs only after the zero-safe
localization. It introduces no preliminary deletion of the singular
parent, the $e=0$ stratum, the $d=0$ stratum, lower degrees, or sampled
gain zeros. ∎

## 12. Fourth critical source patch and the original joint-accumulation test

**Definition 12.1 (Exact fourth world and source patch).** Let $W_4$
be the algebraic complete world of [support VI](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VI.md),
Definition 13.1, with its strict lift and rational enclosures from VI,
Lemma 13.2. Write its source and drift as $(r_4,b_4,d_4)$; these
symbols denote that exact algebraic world, not a rounded substitute.
Define

$$
\begin{gathered}
B_4=
\left[\frac{9648629}{10^7},\frac{964863}{10^6}\right]_r
\times
\left[\frac{2216907}{2500000},\frac{8867629}{10^7}\right]_b,\\
U_4=(57,571/10)\times(305,3051/10),\qquad
\epsilon_*=\frac3{10^8}.
\end{gathered}
\tag{12.1}
$$

Use $\mathscr W,\mathscr I,z(w)=(r,b,d),z_4=(r_4,b_4,d_4)$ and
$\mathsf Q_4$ exactly as in VI, Definition 16.3, (16.5)–(16.8).
In particular the neighbourhood condition defining $\mathsf Q_4$ is
the sum of the squared Euclidean distances of the two selected $M$
triples to $z_4$, not a norm on gain coefficients. VI, Theorem 16.4,
identifies these polynomial relations with the entire original children
and independent-pair quantifiers.

**Theorem 12.2 (Explicit fourth neighbourhood and actual-germ exclusion).**
Every source in $B_4$ has a unique original complete-parent lift, and
its acquired base is in $U_4\subset K_+$. More precisely the entire
closed patch has the rational enclosures

$$
\begin{array}{c|c}
\text{quantity}&\text{closed enclosure}\\ \hline
\Lambda&[-1900311/10^6,-1900309/10^6]\\
e&[4731353/10^6,4731359/10^6]\\
p&[28535187/500000,1426783/25000]\\
v&[38130779/125000,305049717/10^6].
\end{array}
\tag{12.2}
$$

There is no original joint configuration with even one selected $M$
endpoint whose source satisfies

$$
\max\{|r-r_4|,|b-b_4|\}<\epsilon_*.
\tag{12.3}
$$

In the exact terminology of VI, Definition 16.3, both $\mathsf J_4$
and $\mathsf Q_4$ are false. Moreover, for the actual analytic
double-point maps $W_4^+(h),W_4^-(h)$ of VI, Theorem 15.1, there is
$\delta>0$ such that for every $0<|h|<\delta$, both sources are in
$\operatorname{int}B_4$, the pair is an actual distinct equal-$M$
pair, and its entire common child has injective terminal $J$.

*Proof.* First evaluate the original parent and gain on $B_4$.
The rational interval rules (10.2)–(10.3) make the following finite
calculation explicit. Enclose each patch endpoint outward on the
$S^{-1}$ grid; form, in order,

$$
c=r(1-r)/b,\quad j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b.
\tag{12.4}
$$

Use (2.1) for $\Lambda,D$ with the grouping of (10.4). Its
$\Lambda$ interval is contained in the first enclosure of (12.2), hence strictly
negative. Only after this sign test form $e=-D/\Lambda$ and
$d=24+e$. Use the four original gain samples in Section 2 in the
order $0,1,2,3$, computing $g(0)=-d$. Apply the rows at clocks
$5,6$ from that section, accumulating each row product from zero
in sample order. Finally form

$$
p=d+(U+n)g(5),\qquad v=d+(2U+n)g(6).
\tag{12.5}
$$

All rational constants are enclosed by (10.2), each product and
quotient is rounded outward once as in (10.3), and additions use
their endpoint sums. Enlarging the four resulting intervals outward
to the $10^{-6}$ grid gives exactly (12.2). Thus the displayed
table is a finite interval evaluation of the original whole-gain
circuit, with all operations and their order fixed. The denominators
$b,T,U,j,n$ are positive on the entire patch, and $\Lambda<0$
is certified before the additional division. Equation (2.1) and the
common-parent Theorem 2.1 give the unique complete lift. It is strict
because $B_4\subset(0,1)\times(0,\infty)$, and its interpolating
gain is nonzero because the original readings $0$ and $24$ differ.
No exact-degree or nonzero-sample assumption is involved.

The endpoints in (12.2) give, by strict rational comparisons,

$$
57<\frac{28535187}{500000}
\le p\le\frac{1426783}{25000}<\frac{571}{10},
\qquad
305<\frac{38130779}{125000}
\le v\le\frac{305049717}{10^6}<\frac{3051}{10}.
\tag{12.6}
$$

This proves the full patch-image inclusion. In particular an actual
world whose source lies anywhere in $B_4$ fixes a base in $K_+$;
Theorem 9.2 applies to every companion in that child, not just to
worlds with sources in $B_4$.

VI, Lemma 13.2, gives the strict enclosures

$$
\frac{9648629529}{10^{10}}<r_4<\frac{9648629530}{10^{10}},
\qquad
\frac{8867628398}{10^{10}}<b_4<\frac{8867628399}{10^{10}}.
\tag{12.7}
$$

Subtracting the four edges of $B_4$ shows that the distances from
$(r_4,b_4)$ to its left, right, lower and upper edges are strictly
greater than, respectively,

$$
\frac{529}{10^{10}},\qquad
\frac{47}{10^9},\qquad
\frac{199}{5\cdot10^9},\qquad
\frac{601}{10^{10}}.
\tag{12.8}
$$

Each exceeds $\epsilon_*$; the smallest displayed margin minus
$\epsilon_*$ is $49/(5\cdot10^9)>0$. Thus (12.3) puts the
source strictly inside $B_4$.

Suppose an original joint configuration had such a selected $M$
endpoint. That endpoint's base belongs to $U_4$, so the entire common
child has injective terminal $J$ by Theorem 9.2. The independently
selected distinct equal-$J$ pair required by $\mathscr I$ is
therefore impossible. No restriction on the other selected $M$
endpoint, either $J$ endpoint, cross-pair overlap, or the two
terminal values was used. This proves (12.3)'s exclusion. Applying
the same reasoning to $W_4$ itself also gives
$(p_4,v_4)\notin D_J$, equivalently $\neg\mathsf J_4$ by VI,
Theorem 16.4.

For the neighbourhood sentence use precisely
$\epsilon=\epsilon_*=3/10^8$ in VI, (16.8). If its witnesses
existed, their original condition would be

$$
\|z(w_2)-z_4\|_2^2+
\|z(w_3)-z_4\|_2^2<\left(\frac3{10^8}\right)^2.
\tag{12.9}
$$

Every summand and every coordinate square in this expression is
nonnegative. In particular each of $|r(w_2)-r_4|$ and
$|b(w_2)-b_4|$ is strictly less than $3/10^8$; the same holds for
$w_3$. Already $w_2$ contradicts the preceding endpoint exclusion.
Thus this one explicit positive $\epsilon$ has no witnesses, proving
$\neg\mathsf Q_4$. The deduction uses the exact sum in (12.9);
it does not replace the original topology by a stronger norm.

Finally VI, Theorem 15.1, supplies actual analytic complete-world
maps $W_4^\pm(h)$, both tending to the exact $W_4$, with distinct
endpoints and equal $(p,v,m)$ for every sufficiently small nonzero
$h$. Since (12.7)–(12.8) place the limit source in
$\operatorname{int}B_4$, continuity gives $\delta>0$ for which
both sources lie in that interior whenever $|h|<\delta$.
Reduce $\delta$ if necessary to the germ's original strict and
off-$24$ domain. For $0<|h|<\delta$, (12.6) places its common
base in $U_4$, and Theorem 9.2 makes its whole common child
$J$-injective. These are actual original $M$ collisions entering
the patch; they cannot acquire an independent $J$ pair from any
other part of their children. In particular distant $J$ endpoints,
boundary escape of such endpoints, or their merging in a limit
cannot evade this pointwise entire-child exclusion. ∎

The first three exact critical bases of VI, Definition 13.1, their
independent-$J$ compatibility, and their sentences $\mathsf Q_1$,
$\mathsf Q_2$, $\mathsf Q_3$ remain unresolved by these theorems.
So do separated actual equal-$M$ pairs outside $K_+$ and all other
possible original joint configurations outside this rectangle.
The global sentence $\mathsf I$ of VI, Definition 16.3, still asks
for independently chosen distinct equal-$J$ and equal-$M$ pairs in
one entire off-$24$ child, permitting cross-pair overlap and unrelated
terminal values. Its witness-or-exclusion problem is unchanged.
Neither classification of critical worlds nor existence of their
double-point germs reduces that problem to the critical bases.

## 追加锚（本行以下为增补区）
## 13. Second critical rectangle and source interfaces

**Definition 13.1 (Second rectangle).** Retain the complete worlds, the original
left products, the clocks $0,\ldots,7$, and the entire-child quantifiers of
Section 1.  Put

$$
\begin{aligned}
K_2&=\left[\frac{22881}{12500},\frac{183049}{100000}\right]
      \times\left[\frac{4397801}{25000},\frac{8795603}{50000}\right],\\
R_2&=\left[\frac{517}{1000},\frac{261}{500}\right]
      \times\left[\frac{4227}{100000},\frac{423}{10000}\right],\\
B_2&=\left[\frac{259767971}{500000000},\frac{64941993}{125000000}\right]
      \times\left[\frac{84567661}{2000000000},\frac{5285479}{125000000}\right].
\end{aligned}
\tag{13.1}
$$

Thus $K_2=[1.83048,1.83049]\times[175.91204,175.91206]$,
$R_2=[.517,.522]\times[.04227,.04230]$, and
$B_2=[.519535942,.519535944]\times[.0422838305,.0422838320]$.
Write $D_J,D_M$ for the entire-child sets in Section 1.  Put $p_{\rm lo}=22881/12500$, $p_{\rm hi}=183049/100000$, $v_{\rm lo}=4397801/25000$, and $v_{\rm hi}=8795603/50000$.  Retain
independent $J$- and $M$-pairs with arbitrary cross-pair sharing.

**Theorem 13.2 (Second-region whole-child exclusion).** Every complete world
in an entire child over $K_2$ has source in $R_2$.  On $R_2$,

$$
\Lambda>6,\qquad p_b>600,\qquad
 a_r-a_b\frac{p_r}{p_b}>100.
\tag{13.2}
$$

For every $r\in[.517,.522]$,
$p(r,.04227)<1.83048$ and $p(r,.04230)>1.83049$.  Hence terminal $J$
is injective on every entire $C(p,v)$ with $(p,v)\in K_2$, and

$$
D_J\cap K_2=\varnothing,
\qquad (D_J\cap D_M)\cap K_2=\varnothing.
\tag{13.3}
$$

Every actual source in $B_2$ has its acquired $(p,v)$ image in
$\operatorname{int}K_2$.  Therefore
no original joint configuration has a selected $M$-endpoint in $B_2$.  For the
second critical world $W_2$ of VI, Definition 13.1, the exact sentences
$\mathsf J_2$ and $\mathsf Q_2$ of VI, (16.7)–(16.8), are false when
$\epsilon=10^{-10}$.  The already constructed actual $M$-collision germ at
$W_2$ has sufficiently small nonzero endpoints in $B_2$, while their
entire common child is $J$-injective.

The proof is divided into the zero-safe source equations, the finite closed cover,
and the quantitative response order.

## 14. Zero-safe source equations and the eliminant

Put

$$
X=b^2+r-r^2,\qquad N=X+br,\qquad \Delta=b-\frac18,
$$

and define

$$
\begin{aligned}
D_\Lambda&=(b^2+8b+4)XN-2bTU(X+N),\\
\Lambda&=1+\frac6T+\frac1U-\frac4j-\frac4n,
\qquad \kappa=\frac6T-\frac2U,\\
A_5&=1+(U+n)\left(4-\frac{15}{j}+\frac{20}{T}-\frac{10}{n}\right),\\
A_6&=1+(2U+n)\left(10-\frac{36}{j}+\frac{45}{T}-\frac{20}{n}\right),\\
K_5&=\frac{96\Delta(U+n)}T,\\
K_6&=24(2U+n)+\frac{216\Delta(2U+n)}T.
\end{aligned}
\tag{14.1}
$$

Here $j=b+r(1-r)/b$, $n=j+r$, $T=1+b$, and $U=1+2b$.  Let
$H(r,b)$ be the sextic of O, (12.2), and let $R_{18}(r,p,v)$ be the
integer polynomial of O, Definition 24.1.  The two source polynomials are

$$
\begin{aligned}
\mathcal A(r,b,p)&=5b(p-24)D_\Lambda+3(8b-1)H(r,b),\\
\mathcal C(r,b,p,v)&=b^2TXN\{A_5(v-24-K_6)-A_6(p-24-K_5)\}.
\end{aligned}
\tag{14.2}
$$

After expansion their coordinate degrees in $(r,b,p,v)$ are respectively
$(6,7,1,0)$ and $(8,8,1,1)$, and $\mathcal C$ has $89$ terms.
Every complete world satisfies $\mathcal A=\mathcal C=0$.  Indeed, the first
identity is O, Theorem 12.3.  The whole gain gives

$$
 p=24+K_5+eA_5,\qquad v=24+K_6+eA_6,\qquad e=d-24,
\tag{14.3}
$$

so the second identity is obtained after multiplying by the positive denominator
$b^2TXN$.  No gain sample, coefficient, drift, or $\Lambda$ is divided out.

Define

$$
\Phi=438272r^4-931328r^3+540800r^2-50728r-853,
\quad \Psi_2=4r^2-2r-1,
\quad \Psi_4=625r^4-1000r^3+50r^2+260r+36,
\tag{14.4}
$$

and $Q(r,p,v)=\Phi(r)\Psi_2(r)\Psi_4(r)R_{18}(r,p,v)$.  The exact
eliminant identity, as a polynomial identity after eliminating the source
coordinate $b$, is

$$
\operatorname {Res}_b(\mathcal A,\mathcal B)
 =52488000\,r^{11}(r-1)^9\Phi(r)\Psi_2(r)\Psi_4(r)R_{18}(r,p,v),
\tag{14.5}
$$

Here $\mathcal B=Ev-V_\star$ is the response polynomial of Section 16.
Thus $b$ occurs only in the two input polynomials to the resultant; no
$b$ coordinate remains in $Q$.  The published $R_{18}$ is the exact
668-term polynomial of O, Definition 24.1, with monomial order
$(r,p,v)$ and coordinate degrees $(18,7,7)$.  Both sides of (14.5) have
$p$- and $v$-degree at most $7$.  At every point of the $8\times8$ grid
$p,v\in\{0,1,\ldots,7\}$ the two sides agree as polynomials in $r$;
coefficient comparison in $r$, followed by interpolation in $p$ and $v$,
gives the full identity.  Every factor in (14.5), every coefficient in the
published table, and every degree-drop specialization is retained.  Only
the strict-domain factors $r^{11}(r-1)^9$ are removed when projecting to the
open source domain.

At $\Lambda=0$, the undivided parent equation of Section 2 gives
$b=1/8$, and O, Theorem 29.2, gives $\Phi(r)=0$.  Consequently every
actual source, including $\Lambda=0$, satisfies $Q=0$; no singular source is
removed before the cover is applied.

## 15. Finite closed cover of the second rectangle

For a polynomial of degree $n$ on $[l,h]$, use the exact power-to-Bernstein
conversion

$$
T_{ik}(l,h;n)=\sum_{j=0}^{\min(i,k)}
 {k\choose j}l^{\,k-j}(h-l)^j
 \frac{{i\choose j}}{{n\choose j}},
\qquad 0\le i,k\le n.
\tag{15.1}
$$

Apply (15.1) in each variable, padding with zero coefficients to the actual
coordinate degree.  A tensor Bernstein polynomial with coefficients of one
strict sign has that sign on its closed box, by the nonnegative tensor basis and
partition of unity.  Every subdivision below is the exact midpoint de Casteljau
subdivision, with rational arithmetic; a retained cell is closed, and adjacent
cells share their endpoints.

### 15.1 Reciprocal $b$-cap

The polynomial $z^7\mathcal A(r,1/z,p)$ has $112$ positive Bernstein
coefficients on

$$
[0,1]_r\times[0,1/3]_z\times
\left[\frac{22881}{12500},\frac{183049}{100000}\right]_p.
\tag{15.2}
$$

Their coefficient interval is

$$
\left[\frac{562881}{2500},\frac{8483291}{7500}\right]
=\left[\frac{6893716183200}{30618000000},
        \frac{8483291}{7500}\right].
\tag{15.3}
$$

If an actual source had $b\ge3$, then $z=1/b\in[0,1/3]$ and (15.2)
would contradict $\mathcal A=0$.  Thus every actual source over $K_2$ has
$b<3$.  This argument includes the endpoint $z=0$ in the closed certificate
and uses no reciprocal at an actual zero.

### 15.2 The $Q$-cover in $r$

The resultant polynomial has no source coordinate.  The product $Q$ has
coordinate degrees $(28,7,7)$ in $(r,p,v)$: the published $R_{18}$ has
$(18,7,7)$ and the three retained factors contribute ten degrees in $r$.
Apply (15.1) to $Q(r,p,v)$ on the actual target
rectangle $[0,1]_r\times K_2$, subdividing undecided tensor cells to depth
$12$.  The strict-sign leaves number $65$.  Projecting the remaining closed
cells to $r$ gives the following eight-strip cover:

$$
\begin{array}{c|c}
\text{strip}&\text{interval}\\ \hline
1 &[69/512,553/4096]\\
2 &[1063/2048,1065/2048]\\
3 &[347/512,2777/4096]\\
4 &[3313/4096,1657/2048]\\
5 &[221/256,3537/4096]\\
6 &[3557/4096,1779/2048]\\
7 &[231/256,3697/4096]\\
8 &[3725/4096,1863/2048]
\end{array}
\tag{15.4}
$$

The discarded cells and the retained closed cells form a complete partition of
$[0,1]_r\times K_2$.  The displayed endpoints are exact dyadic rationals;
for example $69/512=552/4096$ and
$1063/2048=2126/4096$.  Therefore every zero of $Q$ in the target rectangle,
including every singular, degree-drop, sampled-zero, and unused companion,
projects to one of the intervals in (15.4).

### 15.3 The $\mathcal A,\mathcal C$-cover

For each strip in (15.4), apply the tensor conversion to $\mathcal A$ and
$\mathcal C$ on its product with $[0,3]_b\times K_2$.  A cell is discarded
when either tensor has a strict sign; it is retained when its source rectangle is
contained in $R_2$.  Otherwise bisect $r$ when

$$
\frac{\operatorname{width}(I_r)}{1/1000}
  >\frac{\operatorname{width}(I_b)}{1/10000},
\tag{15.5}
$$

and bisect $b$ otherwise.  All bisections are closed and exact.  The finite
partition has $214$ visited cells, $107$ discarded leaves, and the four
retained leaves

$$
\begin{array}{c|c}
I_r&I_b\\ \hline
[2129/4096,1065/2048]&[5541/131072,693/16384]\\
[133/256,2129/4096]&[5541/131072,693/16384]\\
[2127/4096,133/256]&[5541/131072,693/16384]\\
[1063/2048,2127/4096]&[5541/131072,693/16384]
\end{array}
\tag{15.6}
$$

Their union is exactly

$$
\left[\frac{2126}{4096},\frac{2130}{4096}\right]
\times
\left[\frac{5541}{131072},\frac{5544}{131072}\right]
\subset R_2.
\tag{15.7}
$$

The closed partition argument is inductive: an actual zero of both source
polynomials survives every strict-sign rejection, and each split is the union
of its two closed children.  Hence (15.6) localizes every complete companion,
without a regularity, degree, gain-zero, or selected-pair hypothesis.

## 16. Quantitative fixed-$p$ order

Set

$$
\begin{aligned}
L&=(8b-1)(2+5b),&D_0&=5D_\Lambda,&E&=bD_0,\\
c_0&=-24D_0+3LXN,&c_1&=3LbN,\\
c_2&=3(49b+34)XN-54Ub(X+N),&c_3&=3LbX,\\
G_5&=-4c_0+15c_1-20c_2+10c_3,\\
G_6&=-10c_0+36c_1-45c_2+20c_3,\\
G_7&=-20c_0+70c_1-84c_2+35c_3,\\
P_\star&=-bc_0+(bU+N)G_5,\\
V_\star&=-bc_0+(2bU+N)G_6,\\
J_\star&=-bc_0+(bT+2X+4rb)G_7.
\end{aligned}
\tag{16.1}
$$

The four values $c_i/D_0$ are the gain samples at (0,1,2,3), and
$d=-c_0/D_0$.  The original response is

$$
(p,v,a)=\frac{(P_\star,V_\star,J_\star)}E.
\tag{16.2}
$$

Write $\mathcal B(r,b,v)=Ev-V_\star$.  With
$K_\Lambda=(8b-1)(2+5b)$,
$Z_6=N+2bU$, and
$G_{6,\Lambda}=(10T+45)XN-bT(36N+20X)$, direct expansion gives

$$
E=5bD_\Lambda,
\qquad
V_\star=\frac{120bTD_\Lambda+15Z_6D_\Lambda(80b-1)
 -3K_\Lambda\bigl(bTXN+Z_6G_{6,\Lambda}\bigr)}{T}.
$$

Consequently $\mathcal B$ is exactly the polynomial $\mathsf B$ of O,
(20.1), rather than a new response equation.  The identities at clocks
$0,\ldots,4$ are the literal left-product identities of III,
(16.1)–(16.5); fixed-node interpolation then reconstructs the one whole
cubic-or-lower gain.  Define, for $i=r,b$,

$$
P_i=(\partial_iP_\star)E-P_\star\partial_iE,
\qquad
J_i=(\partial_iJ_\star)E-J_\star\partial_iE,
\qquad F=J_rP_b-J_bP_r.
\tag{16.3}
$$

The following coefficient intervals are the exact tensor-Bernstein bounds on
$R_2$.  The entry $N_c$ is the number of coefficients in the indicated
common-sign tensor.

$$
\begin{array}{c|c|c}
\text{polynomial}&\text{coefficient interval}&N_c\\ \hline
TUXN&[38827573436562470052416792289/500000000000000000000000000000,\\
\quad38861603468245048936599/500000000000000000000000]&35\\
2D_\Lambda-6TUXN&[3000369608678090161251/100000000000000000000000,\\
\quad3014235008209676080466051211/100000000000000000000000000000]&35\\
E&[1048325640422948994096665597655603/20000000000000000000000000000000000,\\
\quad104989039317544620086596377/2000000000000000000000000000]&40\\
E^2&[1098986648368186150026372220663966299696876332396878920209797293609/400000000000000000000000000000000000000000000000000000000000000000000,\\
\quad11022698376820930105858286550164233263182412509526129/4000000000000000000000000000000000000000000000000000000]&135\\
E^4&[1207771653291539229850576877846859588964794958475786599166338571256747817337040685725478385600929460356428571032940548965660952244881/160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,\\
\quad121499879506370767265981212723980370607961397283201975288661327432118680360866163822489474103172133724641/16000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]&493\\
P_b&[12146411187517987110463702478527555289925408333624395355010017/6250000000000000000000000000000000000000000000000000000000000,\\
\quad48687322621122364763399116219882576434198168388173/25000000000000000000000000000000000000000000000000]&143\\
F&[4079636333881816266739549891697389822153963209622482423674491450654042193042205949897098430225710089754289420214147475579/6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,\\
\quad463084163990943898842623200926692144780989068514012603165788626651130046305033948828279458100801/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]&520\\
P_b-600E^2&[5855039069247112898533398134949684355377064484906613/20000000000000000000000000000000000000000000000000000,\\
\quad592573173031149165631721472589424422304483154248059666580481010173/2000000000000000000000000000000000000000000000000000000000000000000]&165\\
F-100P_bE^2&[2969801614855032600952985888179520693784169471194503600170946832436610164462239137212711249603227162771508845294817576630918647/25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,\\
\quad204268990357907795860083526593690811392053872385925755315743159218149949061494254371108761969323527683/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]&540
\end{array}
\tag{16.4}
$$

Every interval in (16.4) is strictly positive.  The lower and upper $b$-edge
certificates for $P_\star-pE$ are respectively strictly negative and strictly
positive; their coefficient intervals and counts are

$$
\begin{array}{c|c|c}
\text{edge}&\text{coefficient interval}&N_c\\ \hline
p=22881/12500&[-134695671420015040215560837207472243/250000000000000000000000000000000000000,\\
\quad-110034801047392073108157960215167743/250000000000000000000000000000000000000]&7\\
p=183049/100000&[114530288272338851021793366477/200000000000000000000000000000000,\\
\quad134548701329506110573459946527/200000000000000000000000000000000]&7
\end{array}
\tag{16.5}
$$

Since $\Lambda=2D_\Lambda/(TUXN)$, (16.4) gives
$\Lambda>6$, $E>0$, $p_b=P_b/E^2>600$, and

$$
 a_r-a_b\frac{p_r}{p_b}=\frac{F}{P_bE^2}>100.
\tag{16.6}
$$

For fixed $p\in[p_{\rm lo},p_{\rm hi}]$, the edge signs in (16.5) and
$p_b>0$ give one and only one $b=b_p(r)$ on the full $r$-interval of
$R_2$.  Implicit differentiation gives $b_p'=-p_r/p_b$, and (16.6) makes
$a(r,b_p(r))$ strictly increasing.  If two complete worlds in the same
$C(p,v)$ have equal $a$, their sources therefore have equal $r$, then equal
$b$.  The nonzero $\Lambda$ fixes $e$ through the undivided parent equation,
and the four fixed-node samples fix the entire gain.  The complete worlds are equal.
Together with the cover in Section 15 this proves (13.2)–(13.3) for every
companion, including singular, lower-degree, sampled-zero, and unused companions.

## 17. Endpoint collar and the second critical consumer

On $B_2$, the four tensor signs for
$P_\star-p_{\rm lo}E$, $P_\star-p_{\rm hi}E$,
$V_\star-v_{\rm lo}E$, and $V_\star-v_{\rm hi}E$ are respectively
$+,-,+,-$, with $E>0$.  Their coefficient intervals are

$$
\begin{array}{c|c}
\text{polynomial}&\text{coefficient interval}\\ \hline
P_\star-p_{\rm lo}E&[15632871249295034892899101863589135503503564225604976260708207/64000000000000000000000000000000000000000000000000000000000000000000,\\
\quad18306868805882728350506043194571853383464463262006135713/61035156250000000000000000000000000000000000000000000000000000]\\
P_\star-p_{\rm hi}E&[-143513940503677688145026587497654979597799806166268865419025497/512000000000000000000000000000000000000000000000000000000000000000000,\\
\quad-109679960121835866240682337107470049878838089735172940823/488281250000000000000000000000000000000000000000000000000000000]\\
V_\star-v_{\rm lo}E&[116437808364870343161240787916944000232973076332998112621/244140625000000000000000000000000000000000000000000000000000000,\\
\quad77191997698005018186359560886774831716883491109761887968220447/128000000000000000000000000000000000000000000000000000000000000000000]\\
V_\star-v_{\rm hi}E&[-69848551102013674941744947373550438356790359749111956953/122070312500000000000000000000000000000000000000000000000000000,\\
\quad-114192915102027930915500280632818400192061337751584899568250259/256000000000000000000000000000000000000000000000000000000000000000000]
\end{array}
\tag{17.1}
$$

Thus every source in $B_2$ has acquired base in
$\operatorname{int}K_2$.  VI, Lemma 13.2, gives the strict enclosures

$$
\begin{gathered}
0.5195359430<r_2<0.5195359431,\qquad
0.0422838313<b_2<0.0422838314,\\
1.830485<p_2<1.830486,\qquad
175.912050<v_2<175.912051.
\end{gathered}
\tag{17.2}
$$

Hence $W_2$ lies over $K_2$, and Theorem 13.2 gives
$\neg\mathsf J_2$.  In VI, Definition 16.3, $\mathsf Q_2$ uses
$z=(r,b,d)$ and the sum of the two squared Euclidean distances to $z_2$.
In exact form, VI, (16.7), defines

$$
\mathsf J_2\;\Longleftrightarrow\;
\exists w_0,w_1:\mathscr W(p_2,v_2;w_0)\land
\mathscr W(p_2,v_2;w_1)\land
\mathfrak a(w_0)=\mathfrak a(w_1)\land
\lVert w_0-w_1\rVert^2>0,
$$

where the norm is on the full eight-coordinate world tuple.  VI, (16.8),
defines

$$
\mathsf Q_2\;\Longleftrightarrow\;
\forall\epsilon>0\;\exists p,v,w_0,w_1,w_2,w_3:
\mathscr I(p,v;w_0,w_1,w_2,w_3)\land
\lVert z(w_2)-z_2\rVert^2+\lVert z(w_3)-z_2\rVert^2<\epsilon^2.
$$

Here $\mathscr I$ retains $p\ne24$, all four entire-child witnesses,
the independent equal-$\mathfrak a$ pair with positive full-world squared
norm, and the independent equal-$\mathfrak m$ pair with positive full-world
squared norm; it imposes no cross-pair sharing restriction and no equality of
the two common terminal values.  If the displayed sum is less than
$\epsilon^2$, every $r$- and $b$-coordinate deviation is less than
$\epsilon$.  With

$$
\epsilon=\frac1{10^{10}},
\tag{17.3}
$$

(17.2) places both such coordinate intervals strictly inside $B_2$, since

$$
[0.5195359429,0.5195359432]
 \subset(0.519535942,0.519535944),
\quad
[0.0422838312,0.0422838315]
 \subset(0.0422838305,0.0422838320).
\tag{17.4}
$$

A selected $M$-endpoint satisfying the $Q_2$ neighbourhood condition would
therefore lie in $B_2$, contradicting the endpoint exclusion in Theorem 13.2.
Thus $\neg\mathsf Q_2$, with no condition on the other endpoint, on cross-pair
sharing, or on the common terminal values.  VI, Theorem 15.1, supplies actual
strict off-(24) equal-$M$ germs converging to $W_2$; continuity and the
interior of $B_2$ put their sufficiently small nonzero endpoints in $B_2$.
Their entire children are $J$-injective by Theorem 13.2.

## 18. Scope of the exclusion

The preceding assertions concern the closed base $K_2$ and the source collar
$B_2$ only.  The original global sentence remains the existence of independent
distinct equal-$J$ and equal-$M$ pairs in one entire off-(24) child, with
arbitrary cross-pair sharing and unrelated terminal common values.  The first and
third critical sectors, separated $M$-pairs outside these collars, boundary and
nonproper limits, other $J$-arcs, and nontransverse incidences are not covered by
(13.3) or (17.4).  No finite cover here changes that global quantifier.

## 追加锚（本行以下为增补区）

## 19. Singleton children on the entire negative nonzero-drift F0 component

In Sections 19–25, let S denote
[the strict-real support](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md),
F denote [the all-response volume](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md),
X denote [support X](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md), and
O denote [the common-parent volume](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md).
Their world and history conventions are unchanged.

**Definition 19.1 (Actual locator and entire child).** A complete world is

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\quad0<r<1,\quad b>0,
\quad0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
\tag{19.1}
$$

For real $p<0,v$, retain the literal entire child

$$
C(p,v)=\mathcal F(0,J,24,M,147/5,J,24,M,18,M,p,M,v).
\tag{19.2}
$$

Thus the acquired actions are $J,M,J,M,M,M$ at clocks $1,\ldots,6$;
the initial read is at clock zero. Products act on the left as in O,
(1.2). Each world has its own fixed source, entire gain and constant drift,
used at every original clock. For that world put

$$
j=b+r(1-r)/b,\quad n=j+r,\quad U=1+2b,\quad T=1+b,
\quad x=n/U>0,
\tag{19.3}
$$

and retain the exact polynomial of F, (31.7),

$$
F_0(x,p,v)=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480.
\tag{19.4}
$$

An actual negative nonzero-drift F0 locator is a member $W\in C(p,v)$
with $d(W)\ne0$ and $F_0(x(W),p,v)=0$. Membership in $C(p,v)$,
including every original reading and every strict source guard, is part
of this definition. A projected polynomial zero alone is not a locator.

**Theorem 19.2 (Whole-component singleton).** For every real $p<0,v$
and every actual negative nonzero-drift F0 locator $W$,

$$
C(p,v)=\{W\}.
\tag{19.5}
$$

The quantifier over this entire child includes unused companions,
singular sources, zero drift, lower gain degrees, all allowed signs,
sampled zeros, repeated gain roots, and every failure of an algebraic
inverse chart. The locator need not be an endpoint in either terminal
pair. No equality of gains or drifts between distinct candidate worlds
is assumed.

The proof uses the entire strict source classification in the proof of
S, Theorem 3.2, the all-world carrier of S, Theorem 4.1, and the
undivided quadratic X, (14.8)–(14.10). Sections 20–23 give the
source-specific uniform exclusions needed to pass from those suppliers
to the entire-child conclusion.

## 20. Exact source responses on a closed interval containing the component

**Definition 20.1 (Algebraic source branch).** In this section $t$ is a
source parameter, distinct from a companion's variable $x$. Set

$$
\begin{gathered}
I=[4719/10000,5453/10000],\qquad
D_t=t(t+1)(t+2),\qquad c_t=45t^3+89t^2-32t-40,\\
U_t=-c_t/D_t,\quad b_t=(U_t-1)/2,\quad
T_t=(U_t+1)/2,\quad n_t=tU_t,\quad q_t=b_t(n_t-b_t),\\
\Delta_t=T_t^2-4q_t,\qquad
r_t=(T_t-\sqrt{\Delta_t})/2.
\end{gathered}
\tag{20.1}
$$

The square root is the nonnegative real square root. Its strict domain
on all of $I$ follows from (23.4). No assertion that every point of
this larger closed interval is a strict source is made.

The proof of S, Theorem 3.2, supplies the following precise source
interface. Its complete strict nonzero-drift F0 source locus consists
of two open arcs. The negative-response arc has

$$
t\in(a_1,b_1),\quad
4719/10000<a_1<4720/10000,\quad
5452/10000<b_1<5453/10000,
\tag{20.2}
$$

with source $(r_t,b_t)$ of (20.1). The other arc has positive $p$.
On each arc the strict root of $z^2-T_tz+q_t$ is the smaller root;
the other root exceeds one. The source is regular, its parent lift is
unique, and its drift is nonzero. Every zero-drift strict parent world
has positive fifth response. These are the supplied classification and
uniqueness statements, rather than additional classifications here.
In particular every locator in Theorem 19.2 uses (20.2).

**Definition 20.2 (Rational response coefficients).** All the following
algebra is over $\mathbb Q(t)$. In

$$
\mathcal Q_t=\mathbb Q(t)[z]/(z^2-T_tz+q_t)
\tag{20.3}
$$

represent a residue by the ordered pair $(A,B)$ for $A+Bz$. Addition
is componentwise and multiplication and inversion mean

$$
\begin{aligned}
(A,B)(C,E)&=(AC-q_tBE,\ AE+BC+T_tBE),\\
(A,B)^{-1}&=
\frac{(A+T_tB,-B)}{A^2+T_tAB+q_tB^2},
\end{aligned}
\tag{20.4}
$$

whenever the displayed rational-function denominator is nonzero.
Embed a scalar as $(A,0)$. Put

$$
\begin{gathered}
\jmath_t=n_t-z,\qquad
\lambda_t=1+6/T_t+1/U_t-4/\jmath_t-4/n_t,\\
\eta_t=-\frac{24}{5}(b_t-1/8)(6/T_t-2/U_t),\\
\mathcal P_t=24+(U_t+n_t)(96-108/T_t)\\
\hspace{13mm}
+\frac{\eta_t}{\lambda_t}
 \{1+(U_t+n_t)(4-15/\jmath_t+20/T_t-10/n_t)\}.
\end{gathered}
\tag{20.5}
$$

Define $a(t),h(t)$ to be the two coordinates of $\mathcal P_t$ after
(20.4), so that $\mathcal P_t=a+hz$. These rules determine the
coefficients without choosing a numerical root. The inverses exist
in $\mathcal Q_t$: at $t=1/2$ the norms of $\jmath_t$ and
$\lambda_t$ are respectively $-1/4$ and $292969/3600$, both nonzero.
All scalar denominators in (20.5) are nonzero rational functions.

Set

$$
\begin{gathered}
k(t)=\frac{18(t+2)}{5(t+1)},\qquad
c(t)=-\frac{3(t+2)(135t^2+55t-80)}{5t(t+1)},\\
w_0(t)=(k(t)-11/2)a(t)+c(t),\qquad
w_1(t)=(k(t)-11/2)h(t),\\
p_t=a(t)+h(t)r_t,\qquad w_t=w_0(t)+w_1(t)r_t,
\qquad v_t=11p_t/2+w_t.
\end{gathered}
\tag{20.6}
$$

**Lemma 20.3 (Original-response correspondence).** For an actual locator
with $t=x(W)$, the pair $(p_t,v_t)$ is its actual acquired base $(p,v)$.

Proof. The source interface (20.2) identifies its strict source as
$(r_t,b_t)$. The parent equation O, Theorem 2.1, is
$e\Lambda=\eta_t$, with $e=d-24$ and $\Lambda$ the evaluation of
$\lambda_t$ at $z=r_t$. On this strict arc $\Lambda\ne0$ by the
supplied classification. The fifth-response identity (3.1) of this
volume, or equivalently O's clock-five interpolating row, is exactly
(20.5) with $e=\eta_t/\Lambda$. Hence $p=p_t$ using the one
whole parent gain, without refitting it. Solving $F_0(t,p,v)=0$ for
$v$ gives $v=k(t)p+c(t)$; its denominator $5t(t+1)$ is positive.
Equations (20.6) give the asserted $v_t$ and $w_t$.
The rational-algebra reductions hold at this source because its original
$j,n,T,U,\Lambda$ denominators are nonzero. The reduced coefficient
denominators are also separated from zero on $I$ by (23.4). ∎

## 21. Two uniform strict-source exclusions from the published quadratic

Use $D_x=x(x+1)(x+2)$ and the literal quadratic $\Phi(U)$ of X,
(14.8)–(14.10). Define its cleared multiple

$$
L(x,U,p,v)=-5D_x\Phi(U)
           =\mathcal A(x,p,v)U^2+2\mathcal B(x,p,v)U+5\mathcal C(x,p,v),
\tag{21.1}
$$

where the expansion needed below is

$$
\begin{aligned}
\mathcal A={}&-20px^2-40px+5vx^2+5vx
              +834x^3+2022x^2+228x-960,\\
\mathcal B={}&260px^2+350px-320p-85vx^2-25vx+50v\\
             &\quad+2835x^3+2058x^2-8409x+3120,\\
\mathcal C={}&36px^2+4px-128p-15vx^2+9vx+20v
              -738x^2-1050x+1872.
\end{aligned}
\tag{21.2}
$$

This is the supplied quadratic, with its normalization fixed by (21.1).
Its undivided identity is a rational identity in $x,U,p,v,d$;
the base rectangle used for estimates in X does not restrict that
identity. Every actual world therefore satisfies $L=0$.
In particular X, (14.10), obtains $\Phi=0$ as a polynomial combination
of its two original clock equations $A_U=B_U=0$, with no division
by $d$ or $U-\tau$. Thus (21.1) applies also to zero drift and
failed drift inverses. It is a necessary equation, not a converse
world-realization criterion.

**Definition 21.1 (Finite tensor coefficients).** For a polynomial
$G$ in $m$ variables $z_1,\ldots,z_m$ on a rational box
$\prod_\nu[l_\nu,u_\nu]$, fix a degree vector $\mathbf n$ at least
its coordinate degrees. Expand exactly

$$
G(l_1+(u_1-l_1)y_1,\ldots,l_m+(u_m-l_m)y_m)
       =\sum_{\mathbf k}g_{\mathbf k}\mathbf y^{\mathbf k}.
$$

The tensor Bernstein coefficient with index
$0\le i_\nu\le n_\nu$ is

$$
\mathcal B_{\mathbf i}(G)
 =\sum_{\mathbf k\le\mathbf i}g_{\mathbf k}
       \prod_{\nu=1}^m
           \frac{\binom{i_\nu}{k_\nu}}{\binom{n_\nu}{k_\nu}}.
\tag{21.3}
$$

Missing power coefficients are zero. All substitutions and sums in
(21.3) are exact rational operations. The identity

$$
y^k=\sum_{i=k}^n
 \frac{\binom{i}{k}}{\binom nk}\binom ni y^i(1-y)^{n-i}
$$

shows that these are precisely the coefficients in a nonnegative
basis summing to one on the box. Their minimum therefore bounds $G$
from below, including the box boundary.

**Lemma 21.2 (Excluded companion intervals).** Suppose an actual world
belongs to a base with

$$
(p,w)\in Z=[-115,-70]\times[-13,-8],\qquad v=11p/2+w.
\tag{21.4}
$$

Its tail ratio $x$ belongs neither to $[1/5,3/10]$ nor to $[4/5,+\infty)$.

Proof. First suppose $1/5\le x\le3/10$. Strict source positivity gives

$$
xU=b+r+\frac{r(1-r)}b>b=\frac{U-1}{2}.
$$

Since $x<1/2$ and $U>1$, it follows that

$$
1<U<\frac1{1-2x},\qquad
U=1+\frac{2xy}{1-2x}\quad\text{for some }0<y<1.
\tag{21.5}
$$

Define the polynomial

$$
G_-(x,p,w,y)=(1-2x)^2
 L\left(x,1+\frac{2xy}{1-2x},p,11p/2+w\right).
\tag{21.6}
$$

The denominator cancels exactly. On the box
$[1/5,3/10]_x\times[-115,-70]_p\times[-13,-8]_w\times[0,1]_y$,
use the degree vector $(5,1,1,2)$ in (21.3). The complete family
of $6\cdot2\cdot2\cdot3=72$ rational coefficients satisfies

$$
\min_{\mathbf i}\mathcal B_{\mathbf i}(G_-)=\frac{568697}{500},
\qquad
\max_{\mathbf i}\mathcal B_{\mathbf i}(G_-)=\frac{861092}{125}.
\tag{21.7}
$$

These finite identities follow by substituting (21.2) into (21.6)
and applying the sum (21.3) for every
$\mathbf i\in\{0,\ldots,5\}\times\{0,1\}^2\times\{0,1,2\}$.
Their positive lower bound, the partition of unity, and
$(1-2x)^2>0$ imply $L>0$, contradicting its necessary vanishing.

For $x\ge4/5$ write $x=4/5+s$, $U=1+z$, with $s,z\ge0$.
There is the exact finite expansion

$$
L(4/5+s,1+z,p,11p/2+w)
       =\sum_{i=0}^3\sum_{j=0}^2 c_{ij}(p,w)s^iz^j.
\tag{21.8}
$$

There are no other monomials. Each coefficient has coordinate degrees
at most $(1,1)$ in $(p,w)$. In the order
$(0,0),(0,1),(1,0),(1,1)$, its four Bernstein coefficients on $Z$
are the following exact rational numbers:

| $(i,j)$ | Four coefficients of $c_{ij}$ |
|---|---|
| $(0,0)$ | $(838196,867196,581696,610696)/125$ |
| $(0,1)$ | $(455882,434382,309632,288132)/125$ |
| $(0,2)$ | $(180986,185486,151736,156236)/125$ |
| $(1,0)$ | $(977912,929912,590912,542912)/25$ |
| $(1,1)$ | $(1055774,1018774,785774,748774)/25$ |
| $(1,2)$ | $(247649,250899,246524,249774)/50$ |
| $(2,0)$ | $(473888,467888,329888,323888)/5$ |
| $(2,1)$ | $(369256,365256,279256,275256)/5$ |
| $(2,2)$ | $(30961,31211,34336,34586)/10$ |
| $(3,0)$ | $(6504,6504,6504,6504)$ |
| $(3,1)$ | $(7338,7338,7338,7338)$ |
| $(3,2)$ | $(834,834,834,834)$ |

To obtain each row, extract $[s^iz^j]$ from the explicit left side
of (21.8) and use (21.3) with degree $(1,1)$ and box $Z$.
All $48$ numbers are positive, so every $c_{ij}>0$ on $Z$.
In particular $c_{00}>0$, and (21.8) is positive throughout the
closed quadrant. This again contradicts $L=0$. ∎

## 22. The fixed carrier and finite root-variation families

The polynomial $R(x,p,v)$ here is exactly the integer polynomial of
F, (31.8), with its published normalization. Equivalently, using the
literal denominator-free $f$ and $k$ in F, (31.3)–(31.4), and
$K=4k$, it is determined by exact polynomial division in

$$
\operatorname{Res}_d(f,K)=256D_x^8F_0(x,p,v)^2R(x,p,v).
\tag{22.1}
$$

The quotient has $512$ nonzero monomials and coordinate degrees
$(18,6,6)$. No primitive-part or monic rescaling is applied to $R$.
The all-world assertion S, Theorem 4.1, gives

$$
R(x(W'),p,v)=0\qquad\text{for every }W'\in C(p,v),
\tag{22.2}
$$

including $d=0$, $F_0=0$ and $\Lambda=0$. Its use here does not
substitute a generic inverse for the faithful reconstruction F,
Lemma 30.2 and Sections 34–36.

**Definition 22.1 (Four finite coefficient families).** Write
$R=\sum_{i=0}^{18}R_i(p,v)x^i$, padding with zero coefficients
under every specialization. Use the ordered interval pairs

$$
\mathcal E=
\bigl((0,1/5),(3/10,2/5),(2/5,3/5),(3/5,4/5)\bigr).
\tag{22.3}
$$

For $(\alpha,\beta)\in\mathcal E$ define

$$
Q_{\alpha\beta}(z;p,w)
 =(1+z)^{18}R\left(\frac{\alpha+\beta z}{1+z},p,11p/2+w\right)
 =\sum_{k=0}^{18}q_{\alpha\beta,k}(p,w)z^k.
\tag{22.4}
$$

There are $4\cdot19=76$ coefficient polynomials, defined exactly by

$$
q_{\alpha\beta,k}(p,w)=
 \sum_{i=0}^{18}R_i(p,11p/2+w)
 \sum_{j=\max(0,k-18+i)}^{\min(i,k)}
   \binom ij\binom{18-i}{k-j}\alpha^{i-j}\beta^j.
\tag{22.5}
$$

A zero exponent, including $0^0$, has value one. Empty sums are zero.
Thus this formula also defines the family with $\alpha=0$.
For evaluation only, make the exact translation

$$
P=p+90,\qquad W=w+10,\qquad
q_{\alpha\beta,k}(P-90,W-10)
       =\sum_{j=0}^{m}\sum_{l=0}^{n}e_{jl}P^jW^l,
\tag{22.6}
$$

where $m,n$ are the actual coordinate degrees of this polynomial,
zero coefficients being inserted. The zero polynomial has $m=n=0$.
Evaluate (22.6) by Horner in $W$ for each row $j$, then by Horner
in $P$, in both cases starting with the highest degree and proceeding
down to the constant coefficient. This fixes both the polynomial
normalization and the order of all interval operations.

For a nonzero real polynomial, Descartes' rule bounds its positive
roots counted with multiplicity by the coefficient sign variation,
after zero coefficients are omitted. The fractional linear map in
(22.4) is a bijection from $z>0$ to $x\in(\alpha,\beta)$;
its derivative is $(\beta-\alpha)/(1+z)^2>0$.
The nonzero factor $(1+z)^{18}$ therefore preserves multiplicity at
these roots. Also

$$
q_{\alpha\beta,0}=R(\alpha,p,v),\qquad
q_{\alpha\beta,18}=R(\beta,p,v).
\tag{22.7}
$$

These endpoint identities are valid even if the degree in $x$ drops.

## 23. A complete closed cover for the algebraic source and carrier

**Definition 23.1 (Dyadic enclosures).** Put $N=2^{160}$. Represent
a dyadic interval by an integer pair $[l,u]$, denoting
$[l/N,u/N]$. A rational number $a/b$, with $b>0$, has enclosure

$$
\left[\left\lfloor\frac{Na}{b}\right\rfloor,
      \left\lceil\frac{Na}{b}\right\rceil\right].
\tag{23.1}
$$

A rational interval is enclosed by rounding its lower endpoint down
and its upper endpoint up. Negation sends $[l,u]$ to $[-u,-l]$;
addition is $[l,u]+[l',u']=[l+l',u+u']$. For multiplication let
$m,M$ be the minimum and maximum of $ll',lu',ul',uu'$ and use
$[\lfloor m/N\rfloor,\lceil M/N\rceil]$. If $lu>0$, the reciprocal
is $[\lfloor N^2/u\rfloor,\lceil N^2/l\rceil]$; otherwise division
is not defined. Division is multiplication by this reciprocal.
For $0\le l\le u$, the square-root interval is

$$
\left[\left\lfloor\sqrt{lN}\right\rfloor,
      \left\lceil\sqrt{uN}\right\rceil\right].
\tag{23.2}
$$

The integer square roots in (23.2) are uniquely specified by
$m^2\le lN<(m+1)^2$ and $(n-1)^2<uN\le n^2$, respectively;
for $u=0$ take the upper endpoint zero. Multiplication and division
by a rational constant mean enclosing that constant by (23.1) and
using the stated operations. Thus even division by two has a fixed
meaning. There is no rounding to nearest.

For each rational function in the ordered list

$$
\mathcal H=(U_t,T_t,b_t,\Delta_t,a,h,w_0,w_1),
\tag{23.3}
$$

cancel its rational-function gcd. Choose its numerator and denominator
in $\mathbb Z[t]$ with joint integer content one and positive leading
denominator coefficient. This fixes the pair uniquely. Substitute
$t=y+1/2$ into each polynomial and expand exactly in powers of $y$.
Enclose every resulting rational coefficient by (23.1), evaluate
numerator and denominator by descending Horner in the same interval
$y$, then divide. In particular $\Delta_t$ is cancelled as a rational
function before interval evaluation; it is not evaluated by subtracting
two interval expressions for $T_t^2$ and $4q_t$.

**Lemma 23.2 (Finite arithmetic bounds).** For $0\le i\le2048$, let

$$
t_i=\frac{4719}{10000}
          +\frac{734i}{10000\cdot2048}.
$$

For $0\le i<2048$ set $I_i=[t_i,t_{i+1}]$.

Enclose $y\in I_i-1/2$ by (23.1), and evaluate all eight functions
in (23.3) by the prescribed rational Horner rule. Denote their
resulting real intervals by $\mathbf U_i,\mathbf T_i,\mathbf b_i,
\boldsymbol\Delta_i,\mathbf a_i,\mathbf h_i,
\mathbf w_{0i},\mathbf w_{1i}$.
Every rational-function denominator interval excludes zero. More
precisely, the degree pairs of the normalized numerator and denominator,
and uniform strict lower bounds for the distance of each denominator
interval from zero, are

$$
\begin{array}{c|c|c}
\text{function}&(\deg\mathrm{num},\deg\mathrm{den})&
 \operatorname{dist}(0,\text{denominator interval})>\\ \hline
U_t&(3,3)&1\\
T_t&(3,3)&1\\
b_t&(3,3)&1\\
\Delta_t&(7,6)&2\\
a&(22,21)&475000\\
h&(19,20)&871000\\
w_0&(22,21)&4750000\\
w_1&(19,20)&8710000
\end{array}
\qquad
\inf\boldsymbol\Delta_i>16.
\tag{23.4}
$$

Next, in exactly this order, form

$$
\begin{aligned}
\mathbf r_i&=(\mathbf T_i-\sqrt{\boldsymbol\Delta_i})/2,\\
\mathbf p_i&=\mathbf a_i+\mathbf h_i\mathbf r_i,\qquad
\mathbf w_i=\mathbf w_{0i}+\mathbf w_{1i}\mathbf r_i,\\
\mathbf P_i&=\mathbf p_i+90,\qquad
\mathbf W_i=\mathbf w_i+10.
\end{aligned}
\tag{23.5}
$$

The following inclusions hold for every cell, with finite decimals
interpreted as exact rationals:

$$
\begin{gathered}
\mathbf p_i\subset[-114.436330,-70.198698]\subset(-115,-70),\\
\mathbf w_i\subset[-12.665012,-8.442640]\subset(-13,-8).
\end{gathered}
\tag{23.6}
$$

For every pair in (22.3), evaluate each of its nineteen polynomials
(22.6) at $(\mathbf P_i,\mathbf W_i)$ using (23.1) and its Horner
order; call the resulting intervals $\mathbf q_{i,k}$.
All of their first and last coefficient intervals exclude zero.
The maximal possible sign variations and their endpoint signs are

$$
\begin{array}{c|c|c|c}
(\alpha,\beta)&
 \operatorname{sgn}\mathbf q_{i,0}&
 \operatorname{sgn}\mathbf q_{i,18}&
 \text{maximal variation}\ \le\\ \hline
(0,1/5)&+&+&0\\
(3/10,2/5)&-&-&0\\
(2/5,3/5)&-&+&1\\
(3/5,4/5)&+&+&0
\end{array}
\tag{23.7}
$$

Here every first and last coefficient interval has distance greater
than one from zero, uniformly over all $2048$ cells and all four rows.

For completeness, the finite variation operation in (23.7) includes
all signs compatible with each interval. For an interval $J$, let

$$
\Sigma(J)=\bigl(\{-1\}:\inf J<0\bigr)
 \cup\bigl(\{0\}:0\in J\bigr)
 \cup\bigl(\{1\}:\sup J>0\bigr),
\tag{23.8}
$$

where a parenthesized set contributes the empty set when its condition
is false. The maximal variation is the maximum of the ordinary
zero-omitting variation of $(s_0,\ldots,s_{18})$ over
$\prod_{k=0}^{18}\Sigma(\mathbf q_{i,k})$. In particular an interval
straddling zero permits both nonzero signs and zero. No sign is chosen
from a midpoint.

Proof. The families in this lemma consist of exactly $2048$ closed
cells, eight normalized rational functions per cell, and $76$
coefficient polynomials per cell. The following finite expansion rules
give the stated bounds using integer arithmetic. For any normalized
numerator or denominator $A(t)=\sum_j A_jt^j$, its shifted coefficient
of $y^k$ is exactly

$$
\sum_{j\ge k} A_j\binom jk2^{k-j}.
\tag{23.9}
$$

Obtain the eight pairs $A$ by (20.1), (20.4)–(20.6) and the normalization
(23.3); their degrees are the middle column of (23.4). For each of the
$2048$ explicitly given pairs $(t_i,t_{i+1})$, apply the integer
rounding (23.1), (23.9) and the Horner recurrence

$$
H_m=C_m,\qquad H_j=H_{j+1}Y+C_j\quad(j=m-1,\ldots,0).
\tag{23.10}
$$

The resulting denominator distances have the strict lower bounds in
(23.4); the same recurrence for the numerator of $\Delta_t$, followed
by its division, gives $\inf\boldsymbol\Delta_i>16$. Thus every
reciprocal and square root in (23.5) is defined. Applying (23.5) gives
(23.6). For the carrier coefficients, expand the fixed quotient
(22.1), extract $R_i$, use the binomial sum (22.5), translate by
(22.6), and apply (23.10) first in $\mathbf W_i$ and then in
$\mathbf P_i$. This gives the endpoint signs and distances in (23.7).

The finite maximum in (23.8) can be evaluated by the following exact
recurrence, which also specifies the treatment of every coefficient
interval containing zero. Initially the sole state is $(0,0)$,
meaning no preceding nonzero sign and zero variation. On processing a
sign $s\in\Sigma(J)$, a state $(h,v)$ contributes

$$
\begin{cases}
(h,v),&s=0,\\
(s,v+\mathbf1_{h\ne0,\ h\ne s}),&s\ne0.
\end{cases}
\tag{23.11}
$$

For each last sign retain the largest variation. Processing all
nineteen coefficients yields the bounds $(0,0,1,0)$ in (23.7).
The complete index ranges are $0\le i<2048$, the four rows of
(22.3), and $0\le k\le18$; there is no omitted cell, subdivision,
endpoint family or unresolved branch in these finite inequalities.
Equations (20.4), (22.5), (23.1), (23.9)–(23.11) and the displayed
index ranges specify every rational and integer in this calculation.

Finally, the rounding rules enclose each exact operation: the four
endpoint products give the product extrema, reciprocal reverses the
endpoints on either component of $\mathbb R\setminus\{0\}$, and
the square function is increasing on nonnegative reals. Induction on
(23.10) and then on (23.5) encloses the exact response of each
$t\in I_i$. Induction on (23.11) takes the maximum over every allowed
sign prefix, so its result bounds the variation of the exact
coefficient sequence at that same $t$. These inclusions prove the
uniform, rather than pointwise, interpretation of the finite bounds.
The closed cells join at their common rational endpoints and have
union $I$. ∎

**Corollary 23.3 (Uniform carrier localization).** For every $t\in I$,
at the exact base $(p_t,v_t)$ of (20.6), $R(x,p_t,v_t)$ has no root
in

$$
(0,1/5),\qquad(3/10,2/5),\qquad(3/5,4/5),
\tag{23.12}
$$

and has at most one root, counted with multiplicity, in $(2/5,3/5)$.
It is nonzero at each endpoint
$0,1/5,3/10,2/5,3/5,4/5$.

Proof. Choose a closed cell containing $t$. Lemma 23.2 encloses the
exact source responses and every coefficient of (22.4) at this same
$t$. The exact coefficient signs are among (23.8), so (23.7),
Descartes' rule and the multiplicity-preserving map (22.4) give the
claimed open-interval bounds. The first and last coefficient signs,
together with (22.7), exclude all listed endpoints. ∎

## 24. Proof of the singleton theorem and its independent-pair consumer

Proof of Theorem 19.2. Fix the stated real $(p,v)$ and locator $W$.
The supplied classification (20.2) puts $t=x(W)$ in $(a_1,b_1)$,
which is contained in $I\cap(2/5,3/5)$. Lemma 20.3 identifies its
actual base with $(p_t,v_t)$. In particular (23.6) gives
$(p,v-11p/2)\in Z$.

Take an arbitrary actual companion $W'\in C(p,v)$. Use its own
source, gain and drift, and put $x'=x(W')>0$, $U'=1+2b(W')>1$.
The all-world carrier (22.2) gives $R(x',p,v)=0$, without any
regularity assumption on $W'$. Corollary 23.3 excludes the three
intervals (23.12) and all their listed endpoints. Lemma 21.2, using
this companion's own strict source inequality and the same exact
$(p,w)$, excludes $[1/5,3/10]$ and $[4/5,+\infty)$.
The only remaining possibility is

$$
x'\in(2/5,3/5).
\tag{24.1}
$$

The locator itself also satisfies $R(t,p,v)=0$ by (22.2).
Corollary 23.3 bounds the number of roots in this interval by one,
so $x'=t$. Consequently $F_0(x',p,v)=0$.

A zero-drift companion is impossible: the zero-drift part of the
proof of S, Theorem 3.2, gives positive $p$ for every strict
zero-drift world of the parent, contrary to the fixed $p<0$.
Thus $W'$ lies on the nonzero-drift F0 source classification. At
this fixed tail ratio $t$ the supplied quadratic source equation has
one strict root, namely $r_t$, and fixes $b_t$; the parent lift is
regular and unique. Hence its fixed drift and entire interpolating
gain coincide with those of $W$, and $W'=W$. Since $W'$ was
arbitrary, (19.5) follows. In particular singular companions and
failed inverse charts have been retained until this argument identifies
or excludes them; they were never removed as initial assumptions. ∎

**Corollary 24.1 (No independent terminal pairs at the identical base).**
At every base in Theorem 19.2 both original clock-seven functions
$f_{MJ}$ and $f_{MM}$ are injective on the entire child. In particular
there are no four actual worlds in that child satisfying

$$
W_0\ne W_1,\quad f_{MJ}(W_0)=f_{MJ}(W_1),\qquad
W_2\ne W_3,\quad f_{MM}(W_2)=f_{MM}(W_3).
\tag{24.2}
$$

The two pairs may otherwise share any labels, have independent gains
and drifts, and have unrelated common terminal values. The locator
need not be any $W_i$.

Proof. Theorem 19.2 identifies every actual label in this one child
with $W$. Each within-pair distinctness in (24.2) is therefore
impossible, and each of the two functions is injective. Both use the
same source, gain, drift and clock seven of their respective worlds,
as in F, (30.9); the alternatives are not acquired as extra ports. ∎

**Corollary 24.2 (The retained Q24 outer set with an actual locator).**
Retain, without removing any factor or exceptional point, the finite
outer set of S, Theorem 9.10,

$$
\mathcal T_{24}=
 V_{\mathbb C}(Q_{24},e_{24}n_{24,J},e_{24}n_{24,M}),
\tag{24.3}
$$

where all four polynomials are those of S, Definitions 9.3, 9.6 and
9.7. A real point of $\mathcal T_{24}$ with $p<0$ whose entire
original child contains an actual nonzero-drift F0 locator has no
actual joint lift (24.2). This includes every such point with
$e_{24}=0$.

Proof. Actual membership and the stated locator guards put this same
base under Theorem 19.2, so Corollary 24.1 excludes the lift. Neither
proof evaluates an inverse from S, Definitions 9.6–9.7, or assumes
$e_{24}\ne0$. The source-response denominators are justified instead
in Lemma 20.3 and (23.4). The assertion therefore holds equally on
$V(Q_{24},e_{24})$. The condition $Q_{24}=0$ by itself supplies no
actual locator and is not sufficient for applying this corollary. ∎

## 25. Mathematical suppliers, comparison and remaining scope

The exact strict arcs, their response signs, the exclusion of
zero-drift negative-response sources and the uniqueness at fixed
F0 tail ratio are supplied by the proof of S, Theorem 3.2. Its
M-injectivity theorem concerns the exceptional subfamily; it does not
assert that every other companion is absent. S, Theorem 4.1, supplies
the carrier for every actual companion. F, Lemma 30.2 and Sections
31, 34–36, supply its normalization and faithful original-world
meaning. X, (14.8)–(14.10), supplies the undivided quadratic; the
new sign domains (21.4)–(21.8) consume that same quadratic.
The new conclusion is the entire-child singleton assertion on the
whole negative nonzero-drift F0 component, obtained from the explicit
closed-interval response and root-variation bounds above.

S, Theorem 7.4, gives a singleton neighborhood of its limiting base,
without a radius covering this component. Support VII, Theorems
25.1–25.2 and Sections 28–30, give the two exact critical singleton
children and M-injectivity on unspecified open base neighborhoods.
Support XI, Sections 7–8, gives the attached finite second-J arc,
its singular passage and its closed-rectangle entire-child M
exclusion. X, Section 14, already classifies its first negative-J
family. None of those source assertions is rederived or identified
with the F0 component here. The known exact $p_J$ conclusion remains
F, Theorems 24.2–24.3.

The algebra in (20.4) is ordinary quadratic-algebra arithmetic.
The Bernstein identity (21.3), positivity of its basis and
Descartes' multiplicity bound are classical. For the latter two
methods and their fractional-linear relation, see B. Mourrain,
F. Rouillier and M.-F. Roy, *Bernstein's basis and real root isolation*,
INRIA RR-5149, Theorem 1.1 and Propositions 2.3–2.4,
[primary text](https://inria.hal.science/inria-00071434/document).
The tensor positivity used here follows directly by multiplying the
one-variable identity displayed after (21.3). The fixed resultant
construction is the Sylvester determinant; see M. Moreno Maza,
*The resultant*, Definition 4 and Propositions 5–7,
[primary text](https://www.csd.uwo.ca/~mmorenom/AM583/Lectures/ResultantGcd.html/node3.html).
It is used only through the owning polynomial and all-world theorem,
without a converse from resultant vanishing. These standard methods
supply no FIB-specific singleton theorem. The source comparison is
with the named published results; no worldwide priority assertion
is made.

The decided class is inhabited: the exact $t=1/2$ world in the proof
of S, Theorem 3.2, has $b=7$, $r=4-(5/2)\sqrt2$, nonzero drift,
negative fifth response

$$
p_0=\frac{10179984-26282025\sqrt2}{292969},\qquad
v_0=6p_0+75/2,
$$

and $F_0(1/2,p_0,v_0)=0$. That published world supplies nonvacuity;
the uniform conclusion is not inferred from this one point.

The positive-response nonzero-drift F0 component, Q24 points without
an actual locator, and every other actual or retained T24 stratum
retain their original lifting questions. Regular–regular terminal-M
joint incidence outside the decided locus is unaffected. No bases
from different responses or branches have been pooled. Every world
used in a child has the actual common history (19.2), hence its
actual ancestor under the original actions; a projected compatibility
condition has not been substituted for that history.
The fixed48 assertion V(18.12)(i), rootQ, genuine common-parent and
ancestor obligations, the other child at a given fifth response, and
the full original deterministic history-dependent eight/nine-read
problem, including early stopping and complete-target answers, retain
their original quantifiers. The result introduces no reset, copy,
idle or skipped read, unread composite action, extra port or clock
renumbering. It is an ordinary mathematical conclusion in the stated
world model, with no additional recovery or physical-realization claim.

## 追加锚（本行以下为增补区）
