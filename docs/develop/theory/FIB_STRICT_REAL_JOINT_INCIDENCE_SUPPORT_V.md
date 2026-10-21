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
