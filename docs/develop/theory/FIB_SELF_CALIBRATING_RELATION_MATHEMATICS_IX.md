# FIB 自校准关系数学 IX

## 1. 固定世界、实际祖先与漂移残差

**定义 1.1（完整目标与原时钟）。** A legal complete world is a triple
$W=(P,g,\delta)$, where $P$ is a strictly entrywise positive real
$2\times2$ matrix of rank one and trace one,
$g\in\mathbb R[T]\setminus\{0\}$ has degree at most three, and
$\delta\in\mathbb R$. Set

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
A_0=I,\qquad A_i=E_iA_{i-1},\quad E_i\in\{J,M\}.
\tag{1.1}
$$

The reading at original clock $i$ is
$g(i)\operatorname{tr}(A_iP)+\delta$. The initial reading counts;
every atom is followed immediately by its reading on one unresettable,
uncopyable trajectory. A chronological word $EF$ acts by $FE$ and
includes both immediate readings. Actions, stops and answers may be
arbitrary deterministic functions of the entire actual history, without
regularity or computability assumptions. The gain may have either sign,
lower degree, sampled roots and repeated roots.

The complete-target and acquisition conventions are those of
[I, Definitions 39.1 and 44.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md),
[II, Definitions 51.1 and 56.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md),
and [VIII, Definition 1.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md).
In particular, distinctions concern the entire triple, rather than only
the source or a gain ray.

**定义 1.2（同一 JMMJM 祖先）。** For arbitrary
$D_0,Y,z\in\mathbb R$ and $\lambda\in\mathbb R\setminus\{0\}$,
fix the literal history

$$
H=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
            M,D_0+312\lambda/5,J,Y,M,z).
\tag{1.2}
$$

Write $\mathcal F(H)$ for the set of legal fixed worlds realizing
all six readings of this one history. Its cumulative matrices are

$$
\begin{aligned}
(A_0,A_1,A_2,A_3,A_4,A_5)
 &=\left(I,J,
 \begin{pmatrix}1&0\\1&1\end{pmatrix},
 \begin{pmatrix}1&1\\2&1\end{pmatrix},
 \begin{pmatrix}2&1\\1&1\end{pmatrix},Q\right),\\
Q&=\begin{pmatrix}1&1\\3&2\end{pmatrix}.
\end{aligned}
\tag{1.3}
$$

Use the affine normalization of
[VII, Definitions 1.1–1.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md)
and the [whole-class companion, Section 1](FIB_JMMJM_WHOLE_CLASS_AFFINE_DECODERS.md):

$$
\begin{gathered}
f=g/\lambda,\qquad d=(\delta-D_0)/\lambda,\qquad
y=(Y-D_0)/\lambda,\qquad \zeta=(z-D_0)/\lambda,\\
\mathbf c=(c_0,\ldots,c_5)=(0,24,48,312/5,y,\zeta),\\
t_i=\operatorname{tr}(A_iP),\qquad
t_i f(i)+d=c_i\quad(0\le i\le5).
\end{gathered}
\tag{1.4}
$$

The original target returns by $g=\lambda f$ and
$\delta=D_0+\lambda d$, with the same source and clocks. In particular,
$D_0$ is an observed value, not an assumption that $\delta=D_0$.
The bijection $s\mapsto D_0+\lambda s$ preserves equality and every
actual response partition for both signs of $\lambda$.

**定义 1.3（秩一条件以外的非负源域）。** Define

$$
\begin{aligned}
\mathcal N&=\left\{
 P=\begin{pmatrix}a&b\\c&1-a\end{pmatrix}:
 0\le a\le1,\ b,c\ge0,\ b+c>0\right\},\\
\mathcal P&=\left\{P\in\mathcal N:
 0<a<1,\ b,c>0,\ bc=a(1-a)\right\}.
\end{aligned}
\tag{1.5}
$$

Thus $\mathcal P$ is exactly the legal source set, whereas
$\mathcal N$ requires neither rank one nor determinant zero. Put

$$
u=b+c=\operatorname{tr}(JP)>0,\qquad v=1+b\ge1.
\tag{1.6}
$$

The trace coordinates in (1.3), also used in
[VII, Definition 8.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md), are

$$
(t_0,t_1,t_2,t_3,t_4,t_5)
 =(1,u,v,u+v,1+a+u,u+2v-a).
\tag{1.7}
$$

Every one is positive on $\mathcal N$: in particular
$t_4\ge1+u>0$ and $t_5\ge u+1>0$. Boundary entries
$a=0$, $a=1$, $b=0$ or $c=0$ are permitted whenever $u>0$.

**定义 1.4（插值及最后两读的残差）。** For $P\in\mathcal N$ and,
more generally, any $\mathbf c\in\mathbb R^6$, use the four-node
interpolation of the
[whole-class companion, equations (5.2)–(5.3)](FIB_JMMJM_WHOLE_CLASS_AFFINE_DECODERS.md):

$$
\begin{aligned}
\ell_j(T)&=\prod_{\substack{0\le k\le3\\k\ne j}}
                         \frac{T-k}{j-k},\\
V_P(T)&=\sum_{j=0}^3\frac{\ell_j(T)}{t_j},\qquad
U_{P;\mathbf c}(T)=\sum_{j=0}^3\frac{c_j\ell_j(T)}{t_j},\\
\alpha_i(P)&=1-t_iV_P(i),\qquad
\beta_i(P;\mathbf c)=c_i-t_iU_{P;\mathbf c}(i)
                    \quad(i=4,5),\\
\Delta(P)&=\alpha_4(P)^2+\alpha_5(P)^2,\\
\mathcal C(P;\mathbf c)&=
 \alpha_4(P)\beta_5(P;\mathbf c)
 -\alpha_5(P)\beta_4(P;\mathbf c).
\end{aligned}
\tag{1.8}
$$

All denominators here are the positive $t_0,t_1,t_2,t_3$ and the
nonzero integers $j-k$. None is a gain sample. The polynomial
$U_{P;\mathbf c}-dV_P$ is the unique polynomial of degree at most
three satisfying the first four equations in (1.4) for that $P,d$.
Indeed its values there are $(c_j-d)/t_j$; any second such polynomial
has four distinct roots in their difference and hence is equal to it.
The remaining two equations are exactly
$\alpha_i d=\beta_i$, $i=4,5$.

## 2. 整个非负源域上的严格祖先不等式

**定理 2.1（祖先漂移残差严格非退化）。** For every
$P\in\mathcal N$,

$$
\alpha_4(P)=0
\quad\Longrightarrow\quad
V_P(5)>V_P(3)=\frac1{t_3}\ge\frac1{t_5},
\quad \alpha_5(P)<0.
\tag{2.1}
$$

Consequently $\Delta(P)>0$ throughout $\mathcal N$. Neither assertion
requires rank one, a reading vector, a gain polynomial or a drift.

**证明。** The Lagrange weights at clocks four and five are

$$
\begin{aligned}
(\ell_0(4),\ell_1(4),\ell_2(4),\ell_3(4))&=(-1,4,-6,4),\\
(\ell_0(5),\ell_1(5),\ell_2(5),\ell_3(5))&=(-4,15,-20,10).
\end{aligned}
\tag{2.2}
$$

Substitution of (1.7) therefore gives

$$
\begin{aligned}
V_P(4)&=-1+\frac4u-\frac6v+\frac4{u+v},\\
V_P(5)&=-4+\frac{15}u-\frac{20}v+\frac{10}{u+v},\\
V_P(3)&=\frac1{u+v}.
\end{aligned}
\tag{2.3}
$$

Assume $\alpha_4=0$. Introduce positive-denominator coordinates

$$
\begin{gathered}
r=u/v>0,\qquad h=r(r+1)>0,\\
N=4+2r-6r^2=2(1-r)(3r+2),\qquad B=15+4r-20r^2,\\
A=N/h,\qquad D=B/h.
\end{gathered}
\tag{2.4}
$$

Here $A,D$ are scalar expressions, distinct from the cumulative
matrices $A_i$. Equations (2.3) become

$$
V_P(4)=-1+\frac Av=\frac1{1+a+rv}>0,
\qquad V_P(5)-V_P(3)=-4+\frac Dv.
\tag{2.5}
$$

In particular $A>v\ge1$. Thus $N>0$, so $r<1$, and $A>1$ gives

$$
N>h,\qquad 7r^2-r-4<0.
\tag{2.6}
$$

The quadratic on the right has one negative and one positive root.
Its value at $5/6$ is $1/36>0$, so (2.6) implies

$$
0<r<5/6.
\tag{2.7}
$$

Since $a\le1$, the first identity in (2.5) also gives

$$
\left(-1+\frac Av\right)(2+rv)
 =\frac{2+rv}{1+a+rv}\ge1.
\tag{2.8}
$$

Multiplying by $v>0$ and rearranging yields $F(v)\ge0$, where

$$
F(w)=-rw^2+(rA-3)w+2A.
\tag{2.9}
$$

Here $r,A>0$. The discriminant is $(rA-3)^2+8rA>0$ and the
product of the two roots is $-2A/r<0$. Hence the roots are
$w_-<0<w_+$; since $v>0$ and $F(v)\ge0$, one has $v\le w_+$.

The following polynomial identity decides the comparison with $D/4$:

$$
\begin{aligned}
16h^2 F(D/4)
 &=-rB^2+4(rN-3h)B+32Nh\\
 &=80r^5-48r^4+28r^2-37r\\
 &=rR(r),\\
R(r)&=80r^4-48r^3+28r-37
     =16r^3(5r-3)+28r-37.
\end{aligned}
\tag{2.10}
$$

For completeness, the first equality follows by substituting
$D=B/h$ and $A=N/h$ in (2.9) and multiplying its three terms
by $16h^2$; expansion with (2.4) gives the second equality.
On $0<r\le3/5$, the first term in the final expression for $R$
is nonpositive, and

$$
R(r)\le28(3/5)-37=-101/5<0.
\tag{2.11}
$$

On $3/5\le r<5/6$, both $r^3$ and $5r-3$ are nonnegative
and bounded above by their values at $5/6$. Therefore

$$
R(r)\le16\frac{125}{216}\frac76+\frac{70}3-37
      =-\frac{232}{81}<0.
\tag{2.12}
$$

Thus $F(D/4)<0$. To determine which side of the roots contains
$D/4$, note that $B(r)$ is concave on $[0,5/6]$, with endpoint
values $B(0)=15$ and $B(5/6)=40/9$. It lies above the chord
joining those positive values. Hence $B>0$, so $D/4>0$.
The negative-root alternative is excluded; (2.9) now implies

$$
D/4>w_+\ge v.
\tag{2.13}
$$

The second identity in (2.5) proves $V_P(5)>V_P(3)$.
Finally,

$$
t_5-t_3=v-a\ge0,
\tag{2.14}
$$

because $v\ge1$ and $a\le1$. Positivity of both traces gives
$V_P(3)=1/t_3\ge1/t_5$. Multiplication by $t_5>0$ proves
$\alpha_5=1-t_5V_P(5)<0$. If $\Delta$ vanished, both real
residuals would vanish, contradicting this implication. The proof
used only the inequalities defining $\mathcal N$ and did not remove
any of its permitted boundary entries. ∎

## 3. 源条件秩五与整个实际纤维的有理图

**定理 3.1（六读祖先上的源条件恢复）。** For every
$P\in\mathcal N$, the real $6\times5$ matrix

$$
\mathsf B_P=
\bigl(t_i,\ i t_i,\ i^2t_i,\ i^3t_i,\ 1\bigr)_{i=0}^5
\tag{3.1}
$$

has rank five. Thus for every $\mathbf c\in\mathbb R^6$ there is
at most one pair $(f,d)\in\mathbb R[T]_{\le3}\times\mathbb R$
satisfying all six equations $t_if(i)+d=c_i$.
Such a pair exists if and only if $\mathcal C(P;\mathbf c)=0$,
and when it exists it is

$$
\begin{aligned}
d(P;\mathbf c)&=
 \frac{\alpha_4\beta_4+\alpha_5\beta_5}{\Delta(P)},\\
f_{P;\mathbf c}(T)&=U_{P;\mathbf c}(T)-d(P;\mathbf c)V_P(T).
\end{aligned}
\tag{3.2}
$$

For the particular ancestor vector in (1.4), define the source set

$$
\mathcal S_{\mathbf c}
 =\{P\in\mathcal P:\mathcal C(P;\mathbf c)=0\}.
\tag{3.3}
$$

Then $\mathcal F(H)$ is exactly the rational graph

$$
P\in\mathcal S_{\mathbf c}\longmapsto
\bigl(P,\lambda f_{P;\mathbf c},D_0+\lambda d(P;\mathbf c)\bigr).
\tag{3.4}
$$

Projection onto $P$ is a bijection between these two sets. In
particular distinct complete targets on $H$ have pairwise distinct
sources. These statements recover gain and drift once the source
is supplied; they do not identify the unknown source from $H$.

**证明。** Write $V_P(T)=\sum_{j=0}^3v_jT^j$, and let $C_j$
be the column of $\mathsf B_P$ corresponding to $T^j$, $0\le j\le3$.
Replace the last column $C_{\mathrm{last}}$ by
$C_{\mathrm{last}}-\sum_{j=0}^3v_jC_j$. The new last column is

$$
(0,0,0,0,\alpha_4,\alpha_5)^{\mathsf T}.
\tag{3.5}
$$

The first four rows of the polynomial columns form the product of
$\operatorname{diag}(t_0,t_1,t_2,t_3)$ and the Vandermonde matrix
at $0,1,2,3$. Its determinant is
$12t_0t_1t_2t_3\ne0$. Thus these four columns are independent, and
no nonzero vector in their span has its first four entries zero.
By Theorem 2.1 the column (3.5) is nonzero, so it supplies a fifth
independent column. This also proves that rank five is equivalent
to $\Delta>0$ in these coordinates.

The first-four-equation interpolation in Definition 1.4 leaves
exactly $\alpha_4d=\beta_4$ and $\alpha_5d=\beta_5$.
For the value $d$ in (3.2), direct subtraction gives

$$
\begin{pmatrix}\beta_4\\\beta_5\end{pmatrix}
 -d\begin{pmatrix}\alpha_4\\\alpha_5\end{pmatrix}
 =\frac{\mathcal C(P;\mathbf c)}{\Delta(P)}
       \begin{pmatrix}-\alpha_5\\\alpha_4\end{pmatrix}.
\tag{3.6}
$$

Because $\Delta>0$, the two residual equations hold exactly when
$\mathcal C=0$, and their solution is unique. No choice between
dividing by $\alpha_4$ and dividing by $\alpha_5$ is needed.
This establishes (3.2) for every real vector $\mathbf c$.

For (1.4), the reconstructed $f$ cannot be the zero polynomial:
otherwise all six readings would equal $d$, whereas $c_0=0$ and
$c_1=24$. Thus each $P\in\mathcal S_{\mathbf c}$ gives a legal
nonzero gain, all six equations, and exactly one complete world.
Conversely every world on $H$ has its source in (3.3) and its
gain and drift forced by (3.2). This proves the bijection and the
assertion about distinct sources. Rank five also proves conditional
uniqueness for other reading vectors, including constant vectors;
for a constant vector its unique pair has zero gain and hence is
excluded from the legal-world set.

An explicit polynomial form of the source condition makes the
rational-graph assertion precise. Put

$$
\begin{gathered}
S=uv(u+v)>0,\qquad p_i=SV_P(i),\qquad
q_i=SU_{P;\mathbf c}(i),\\
H_i=S-t_ip_i,\qquad K_i=Sc_i-t_iq_i\quad(i=4,5).
\end{gathered}
\tag{3.7}
$$

Here $S/t_0=S$, $S/t_1=v(u+v)$, $S/t_2=u(u+v)$ and
$S/t_3=uv$ are polynomials. Thus every $p_i,q_i,H_i,K_i$ is
polynomial in source entries and reading coordinates, with rational
coefficients. In particular

$$
\begin{aligned}
p_4&=-S+4v(u+v)-6u(u+v)+4uv,\\
p_5&=-4S+15v(u+v)-20u(u+v)+10uv.
\end{aligned}
\tag{3.8}
$$

The source set (3.3) is exactly

$$
\left\{(a,b,c):
0<a<1,\ b,c>0,\ bc=a(1-a),\ H_4K_5-H_5K_4=0\right\},
\tag{3.9}
$$

with $u=b+c$, $v=1+b$ and the same fixed $\mathbf c$ everywhere.
Indeed its last expression is $S^2\mathcal C$. Moreover

$$
H_4^2+H_5^2=S^2\Delta>0,\qquad
d=\frac{H_4K_4+H_5K_5}{H_4^2+H_5^2}.
\tag{3.10}
$$

Formula (3.2) and $S>0$ now show explicitly that all four gain
coefficients and the drift are rational functions on this source
set, without a deleted denominator-zero stratum. This is the exact
graph of the full actual fiber, rather than a local parametrization
or a restriction to one gain shape. ∎

## 4. 固定或有界读数的整个迹走廊

**定理 4.1（正有限迹走廊上的一致有界性）。** For every
$0<\varepsilon\le R<\infty$ and $B_0<\infty$ with $B_0\ge0$,
there is a finite constant $C_{\varepsilon,R,B_0}$ such that the
following holds. If $P\in\mathcal N$,
$\varepsilon\le\operatorname{tr}(JP)\le R$,
$\|\mathbf c\|_\infty\le B_0$, and
$\mathcal C(P;\mathbf c)=0$, then the pair in (3.2), written
$f(T)=\sum_{j=0}^3f_jT^j$, satisfies

$$
|d|+\sum_{j=0}^3|f_j|\le C_{\varepsilon,R,B_0}.
\tag{4.1}
$$

The conclusion includes nonnegative source limits and does not
require rank one. In particular it applies to every fixed ancestor
vector in (1.4), and uniformly to any bounded family of those
vectors. For fixed $D_0$ and $\lambda\ne0$, it also bounds the
original drift and gain coefficients of the corresponding legal
worlds.

**证明。** Consider the closed source corridor

$$
\mathcal K_{\varepsilon,R}
 =\{(a,b,c):0\le a\le1,\ b,c\ge0,
                          \varepsilon\le b+c\le R\}.
\tag{4.2}
$$

It is compact: it is closed and $0\le b,c\le R$. It lies in
$\mathcal N$, and on it

$$
t_0=1,\qquad t_1\ge\varepsilon,\qquad
t_2\ge1,\qquad t_3\ge1+\varepsilon.
\tag{4.3}
$$

The coefficients of $V_P$ and $U_{P;\mathbf c}$, and all
$\alpha_i,\beta_i$, are therefore continuous on
$\mathcal K_{\varepsilon,R}\times[-B_0,B_0]^6$.
Theorem 2.1 applies on all of the closed corridor, so

$$
\min_{P\in\mathcal K_{\varepsilon,R}}\Delta(P)
 =m_{\varepsilon,R}>0.
\tag{4.4}
$$

Consequently (3.2) defines continuous gain coefficients and drift
on this entire compact product, even before imposing $\mathcal C=0$.
Their displayed absolute-value sum attains a finite maximum, proving
(4.1). Restriction to compatible sources or to determinant-zero
sources preserves the bound. For the original parameters,

$$
|\delta|\le |D_0|+|\lambda||d|,\qquad
\sum_{j=0}^3|g_j|=|\lambda|\sum_{j=0}^3|f_j|.
\tag{4.5}
$$

This proves the stated transfer with these normalization parameters
fixed. In particular any sequence of compatible legal sources in
one corridor, with a fixed ancestor vector, has a subsequence whose
source, gain coefficients and drift converge. The source limit is
nonnegative, trace one and determinant zero, still with $u>0$;
all six equations pass to the limit. For the nonconstant vector
(1.4) its gain limit is nonzero, by $c_0\ne c_1$. The limiting
source need not be strictly positive. ∎

**命题 4.2（不固定祖先末两读时的边界）。** Even for one fixed
legal source in a positive finite trace corridor, no drift bound
uniform over all $y,\zeta\in\mathbb R$ is possible while the first
four readings remain $(0,24,48,312/5)$.

**证明。** Fix any $P\in\mathcal P$ and use its first-four-reading
polynomial $U$ from (1.8). For every $d\in\mathbb R$ put
$f_d=U-dV_P$ and choose

$$
y_d=d+t_4f_d(4),\qquad \zeta_d=d+t_5f_d(5).
\tag{4.6}
$$

These are six compatible readings of the same fixed source and
the indicated gain and drift. The gain is always nonzero, because
otherwise its initial and first readings would require $d=0=24$.
Its constant coefficient is $f_d(0)=-d$, and $d$ is arbitrary.
Moreover $(y_d,\zeta_d)$ is affine in $d$ with slope
$(\alpha_4,\alpha_5)\ne(0,0)$, so these ancestor vectors are
unbounded as $|d|\to\infty$. This does not contradict Theorem 4.1,
whose reading vectors are fixed or bounded. That theorem also makes
no uniform assertion as $\varepsilon\downarrow0$ or $R\uparrow\infty$,
or when the original normalization parameters are unbounded. ∎

## 5. 三源共同相容与完整实际子分支的未决系统

**定义 5.1（已有条件结论的接口）。** The source coordinate in
Theorem 3.1 is a supplied coordinate, not a class label acquired
from the readings. The whole fixed-shape and fixed-source inverses
of the [whole-class companion, Theorems 4.1 and 5.1](FIB_JMMJM_WHOLE_CLASS_AFFINE_DECODERS.md)
are conditional on the respective known class. Theorem 3.1 strengthens
the fixed-source conclusion at this ancestor to an empty or singleton
class before any further read. The common interpolation formula is
reused; the additional ingredient is Theorem 2.1.

The known-initial-root inverse of
[VIII, Theorem 2.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md)
retains its promise $g(0)=0$, equivalent here to $\delta=D_0$.
VIII, Theorem 4.2 and Corollary 4.3 give an uncountable mixed-drift
fiber at

$$
H_*=(0,J,24,M,48,M,312/5,J,48/5,M,-532/5).
\tag{5.1}
$$

In particular those six readings do not identify the initial-root
label or the drift. This is consistent with (3.4), which leaves the
source to be determined. At this same $H_*$,
[VII, Theorem 8.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md)
gives at most one world per gain ray on the whole fiber; its
Theorems 9.1 and 10.2 give an exact closed $u=1$ slice and an
injective sixth-$J$ response on the whole known band
$|u-1|<\eta$ for some $\eta>0$. These are neither ray labels nor
band-membership information extracted from $H_*$. Theorem 4.1 supplies
a no-unbounded-drift conclusion on every positive finite trace
corridor for fixed readings; it supplies no injective sixth response
outside that known band.

The [late-root companion, Theorems 3.1, 6.1 and 7.1](FIB_JMMJM_LATE_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_REDUCTIONS.md)
concerns respectively the known class $f(4)=f(5)=0$, triples with
exactly two terminal roots, and common-drift triples with different
terminal signs. Those strata are distinct from the rank-one-free
inequality in Theorem 2.1 and are not premises of it. The pair
exclusion in VII, Theorem 4.1 likewise remains a separate result;
the present proofs do not require it. Pair exclusion and conditional
class inverses do not by themselves exclude different collision
pairs in different actual children of a larger set.

**定义 5.2（同一祖先上的未决三源相容义务）。** For the one common
vector $\mathbf c(y,\zeta)=(0,24,48,312/5,y,\zeta)$, choose three
pairwise distinct sources

$$
P_k=\begin{pmatrix}a_k&b_k\\e_k&1-a_k\end{pmatrix}\in\mathcal P,
\qquad \mathcal C(P_k;\mathbf c(y,\zeta))=0,
\quad k=1,2,3.
\tag{5.2}
$$

Each source must satisfy the positivity, determinant and polynomial
conditions in (3.9), for these same $y,\zeta$. Define, without any
additional choices of gains or drifts,

$$
d_k=d(P_k;\mathbf c),\qquad f_k=f_{P_k;\mathbf c},\qquad
W_k=(P_k,\lambda f_k,D_0+\lambda d_k).
\tag{5.3}
$$

These are exactly all possible distinct three-world realizations on
the same $H$, by Theorem 3.1. Both of the following response functions
are evaluated in each same fixed world and at the original clocks:

$$
\begin{aligned}
s_E(k)&=d_k+f_k(6)\operatorname{tr}(EQP_k),\\
r_{EF}(k)&=d_k+f_k(7)\operatorname{tr}(FEQP_k),
                    \qquad E,F\in\{J,M\}.
\end{aligned}
\tag{5.4}
$$

They are mathematical counterfactual functions, not jointly acquired
observations. Only one $E$ and then one $F$ are executed, with a read
after each. To state the unresolved obligation, retain the complete
actual-child recursion of
[II, Definition 56.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md)
and the whole-class companion, equation (1.5). For any known
$K\subseteq\mathcal F(H')$ and nonnegative integer $r$ within the
remaining reading horizon, it is

$$
\begin{aligned}
L_0(K,H')&\Longleftrightarrow |K|\ge2,\\
L_{r+1}(K,H')&\Longleftrightarrow |K|\ge2\ \land\
 \bigwedge_{E\in\{J,M\}}\exists v\in\mathbb R:\
 L_r(K\cap\mathcal F(H',E,v),(H',E,v)).
\end{aligned}
\tag{5.5}
$$

For $K=\{W_1,W_2,W_3\}$ from (5.2)–(5.3), its $L_2$ requirement
is exactly the following finite-index system, with real response
values:

$$
\forall E\in\{J,M\}\ \exists v_E\in\mathbb R\
\forall F\in\{J,M\}\ \exists\,1\le i<j\le3:
\quad s_E(i)=s_E(j)=v_E,\qquad r_{EF}(i)=r_{EF}(j).
\tag{5.6}
$$

Indeed, for real normalized responses $v,w$, the literal histories
and their actual response partitions are

$$
\begin{aligned}
H_{E,v}&=(H,E,D_0+\lambda v),\\
K_{E,v}&=K\cap\mathcal F(H_{E,v})
       =\{W_k:s_E(k)=v\},\\
K_{E,v;F,w}&=K_{E,v}\cap
       \mathcal F(H_{E,v},F,D_0+\lambda w)\\
       &=\{W_k:s_E(k)=v,\ r_{EF}(k)=w\}.
\end{aligned}
\tag{5.7}
$$

On the same sixth child $K_{E,v_E}$, the last action $F$ has a
response retaining $L_0$ exactly when two members have equal
$r_{EF}$. This expands both recursion levels. The pair may depend
on $E$ and $F$, but $v_E$ must be shared across the two last-action
requirements for that fixed $E$. If the sixth response is constant
on all three, all three remain in that child and the last actions
may use different pairs. The cardinality clauses then hold because
each required pair has two distinct complete targets. Normalization
transports these response values to the raw history by
$v\mapsto D_0+\lambda v$, bijectively for either sign of $\lambda$.

The unresolved mathematical obligation is to produce one exact
solution of (5.2) and (5.6), for one common real $y,\zeta$, or to
prove, for every $y,\zeta\in\mathbb R$, that the system has no legal
source triple.
All sources, shapes, drifts, lower degrees and sampled or repeated
roots allowed by Definition 1.1 remain in this system. In particular
no division by $f_k(6)$, $f_k(7)$ or any ancestor gain value occurs.
The source equation and nonvanishing denominator give exact
elimination of gain and drift, not a solution or an obstruction for
this joint system. Separately realized marginal pairs, independently
chosen reading vectors or per-word separating suffixes do not meet
(5.2)–(5.6).

**定义 5.3（原始八读与九读问题的保留量词）。** Let
$n_{\mathrm{det}}(3,0)$ be the least uniform total reading budget
for recovering every legal complete target under Definition 1.1
from its original root. The full alternative is a lawful decoder
with at most eight total readings on all legal worlds versus the
lower bound $n_{\mathrm{det}}(3,0)\ge9$. Eight total readings use
the initial clock and clocks one through seven. Both initial actions,
all subsequent actual histories, arbitrary deterministic policies
and early stops are included. A solution or impossibility proof for
the triple system at this one ancestor would still require its
appropriate joint bridge to those earlier histories or a full-domain
decoder. Neither such a bridge nor an unrestricted decoder or lower
bound is asserted by Theorems 2.1–4.1.

## 6. 数学来源与适用对应

**定义 6.1（先例与所用数学工具）。** The mathematical interfaces to
the series and its companions have the following scopes.

| Mathematical source | Correspondence and hypothesis limit |
| --- | --- |
| [I](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md), Definitions 39.1 and 44.1; [II](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md), Definitions 51.1 and 56.1 | Complete targets, the counted initial reading, original clocks and the whole-set actual-child recursion used in Definitions 1.1 and 5.2. |
| [III](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md); [IV](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md); [V](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md); [VI](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VI.md) | The earlier gain-shape, continuation and actual-history theory supplies the surrounding complete-target problem. The literal $JMMJ$ history is V, Definition 5.1. No decoder or obstruction on a different literal ancestor is a premise of Theorem 2.1. |
| [VII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md), Definitions 1.1–1.3 and 8.1; Theorems 8.2, 9.1 and 10.2 | The exact $JMMJM$ and $H_*$ histories, first-four-reading interpolation, the full-$H_*$ gain-ray exclusion, closed $u=1$ slice and known source-band inverse. The slice and band hypotheses are retained in Definition 5.1. |
| [VIII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md), Theorems 2.1 and 4.2; Corollary 4.3 | Known-initial-root recovery and the mixed-drift $H_*$ family. Initial-root membership is not observation-derived, and six-read compatibility is not $L_2$. |
| [Whole-class affine decoders](FIB_JMMJM_WHOLE_CLASS_AFFINE_DECODERS.md), Sections 1–2, Theorems 4.1 and 5.1, equations (5.2)–(5.3) | Normalization, trace coordinates, whole known-shape/source decoders and $f=U-dV$. Theorem 2.1 supplies nonvanishing already at ancestor clocks four and five, without terminal-slope selection. |
| [Late-root rigidity and terminal collision reductions](FIB_JMMJM_LATE_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_REDUCTIONS.md), Theorems 3.1, 6.1 and 7.1 | The specified late-double-root class and the two terminal-pattern reductions of Definition 5.1, rather than a full mixed-source/mixed-shape exclusion. |

The inequality in Theorem 2.1 and its rank-five, source-graph and
trace-corridor consequences are `repo-derived` deductions in this
prescribed model. Four-node Lagrange interpolation, Vandermonde
invertibility, polynomial root counting and compactness are established
tools used inside their proofs; no new general interpolation or
compactness theorem is intended.

For comparison with conditional identifiability, Yanjun Li, Kiryung Lee
and Yoram Bresler, *A Unified Framework for Identifiability Analysis in
Bilinear Inverse Problems with Applications to Subspace and Sparsity
Models*, [Theorem 2.8, arXiv:1501.06120v1](https://arxiv.org/html/1501.06120v1),
is `literature-attested`: for a constrained bilinear problem with
nonzero factors and a specified ambiguity transformation group, it
requires both identification of the first factor's orbit among all
compatible pairs and identification of the pair's orbit conditional on
that first factor. Theorem 3.1 establishes only the conditional
gain/drift statement for a supplied source in the present model. The
affine drift and prescribed sequential actions are retained here; no
identification of the first factor, ambiguity-group equivalence or
adaptive sampling conclusion is imported from that bilinear theorem.

Sunav Choudhary and Urbashi Mitra, *Identifiability Scaling Laws in
Bilinear Inverse Problems*,
[Proposition 1 and Remark 5, arXiv:1402.2637v2](https://arxiv.org/html/1402.2637v2),
are `literature-attested`: their lifted universal criterion uses the
specified linear measurement map and the difference set of realizable
constrained rank-one products. Remark 5 retains observations realizable
in the original factor model. The correspondence here is the need for
one common realizable history, expressed explicitly by (5.2)–(5.6).
No lifted-map criterion, random-map threshold or independently
realized pair is substituted for that system. These citations are
comparisons of hypotheses, not premises for Theorem 2.1 or claims of
external originality or an exhaustive classification.

## 追加锚（本行以下为增补区）
