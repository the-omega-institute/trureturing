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

## 7. 任意末两读的精确源逃逸集合

**定义 7.1（归一化整纤维及其最后两式）。** In this section
$Y,z$ denote normalized readings: set $D_0=0$, $\lambda=1$ in
Definition 1.2 and write

$$
H(Y,z)=(0,J,24,M,48,M,312/5,J,Y,M,z),\qquad
\mathcal F_{Y,z}=\mathcal F(H(Y,z)).
\tag{7.1}
$$

Thus $Y=y$ and $z=\zeta$ in (1.4). All six equations use the
same fixed $(P,g,d)$ and the original clocks. No source, gain shape,
root or drift label is supplied. For $P$ as in (1.5), retain $u,v$
and the interpolation of Definition 1.4. Put $T_4=1+a+u$,
$T_5=u+2v-a$ and

$$
\begin{aligned}
\gamma_4&=\frac{96}{u}-\frac{288}{v}+\frac{1248/5}{u+v},&
\kappa_4&=1-\frac4u+\frac6v-\frac4{u+v},\\
\gamma_5&=\frac{360}{u}-\frac{960}{v}+\frac{624}{u+v},&
\kappa_5&=4-\frac{15}{u}+\frac{20}{v}-\frac{10}{u+v}.
\end{aligned}
\tag{7.2}
$$

The first four readings determine the interpolant with samples

$$
(q_0,q_1,q_2,q_3)=
\left(-d,\frac{24-d}{u},\frac{48-d}{v},
                         \frac{312/5-d}{u+v}\right).
\tag{7.3}
$$

Its last two evaluations are $g(i)=\gamma_i+\kappa_i d$.
Consequently compatibility is exactly the pair of simultaneous
remaining equations

$$
Y=T_4\gamma_4+(1+T_4\kappa_4)d,\qquad
z=T_5\gamma_5+(1+T_5\kappa_5)d.
\tag{7.4}
$$

These are the coordinates of Theorem 3.1, with
$\alpha_i=1+T_i\kappa_i$. The interpolant is nonzero because
its readings at zero and one are different. Every division so far
is by a positive trace or a nonzero interpolation integer.

**定理 7.2（整纤维源无界性的半开线段及解析实现）。** For every
$(Y,z)\in\mathbb R^2$, the source projection of $\mathcal F_{Y,z}$
is unbounded if and only if

$$
z=12Y-\frac{288}{5},\qquad
-\frac{1788}{25}<Y\le-\frac{5268}{155}.
\tag{7.5}
$$

For each fixed $Y$ in this half-open interval there are
$\epsilon_Y>0$ and a real-analytic family of legal worlds
$W_t=(P_t,g_t,d_t)$, $0<t<\epsilon_Y$, all in the same
$\mathcal F_{Y,12Y-288/5}$, such that $(P_t)_{12}=1/t$.
After decreasing $\epsilon_Y$, different parameters give distinct
sources and nonproportional gains over $\mathbb R$.
At the excluded lower endpoint the entire source projection is
bounded. The boundedness assertion off (7.5) also holds if sources
are allowed to be nonnegative, rank one and trace one, provided
$u>0$. Bounds concern each fixed history, not all histories at once.

**证明。** Rank one and trace one give
$bc=a(1-a)\le1/4$, with $a\in[0,1]$ in the nonnegative
extension. Hence an unbounded sequence of sources has a subsequence
with $b\to\infty$ or $c\to\infty$.

First suppose $c_n\to\infty$. Then $b_n\to0$,
$u_n\to\infty$, $v_n\to1$ and $T_{4,n},T_{5,n}\to\infty$.
Uniformly for $a_n\in[0,1]$, (7.2) gives

$$
(\gamma_{4,n},\kappa_{4,n},\gamma_{5,n},\kappa_{5,n})
 \longrightarrow(-288,7,-960,24).
\tag{7.6}
$$

Divide the first equation of (7.4) by $T_{4,n}>0$ and solve it:

$$
d_n=\frac{Y/T_{4,n}-\gamma_{4,n}}
              {1/T_{4,n}+\kappa_{4,n}}
\longrightarrow\frac{288}{7}.
\tag{7.7}
$$

The denominator tends to $7$, justifying the division without
assuming bounded drift. The second equation divided by $T_{5,n}$
would now require
$0=-960+24(288/7)=192/7$, a contradiction. This excludes this
orientation for every fixed real $Y,z$.

For $b$ large put $t=1/b$ and $h=a(1-a)$. Define

$$
\begin{gathered}
U=1+ht^2,\quad V=1+t,\quad W=2+t+ht^2,\\
A=1+(1+a)t+ht^2,\qquad B=3+(2-a)t+ht^2,\\
G_4=96/U-288/V+(1248/5)/W,\\
G_5=360/U-960/V+624/W,\\
K_4=1+t(-4/U+6/V-4/W),\\
K_5=4+t(-15/U+20/V-10/W),\qquad C=t+AK_4.
\end{gathered}
\tag{7.8}
$$

Then $u=U/t$, $v=V/t$, $u+v=W/t$, $T_4=A/t$,
$T_5=B/t$, $\gamma_i=tG_i$ and $\kappa_i=K_i$.
At $t=0$, for every $a\in[0,1]$,

$$
(U,V,W,A,B,K_4,K_5,C)=(1,1,2,1,3,1,4,1).
\tag{7.9}
$$

All these rational functions extend real-analytically to a
neighborhood of $[0,1]\times\{0\}$. Compactness gives a common
strip on which their denominator factors and $C$ stay away from
zero. In particular the first equation of (7.4), for every
compatible source in that strip with $t>0$, is equivalent to

$$
d=tR_Y(a,t),\qquad R_Y=\frac{Y-AG_4}{C}.
\tag{7.10}
$$

Substitution into the other equation gives the exact function

$$
z=Z_Y(a,t),\qquad
Z_Y=BG_5+(t+BK_5)R_Y.
\tag{7.11}
$$

No large-$b$ branch is omitted: $1+T_4\kappa_4=C/t\ne0$ there.
For each fixed $Y$, expansion on the common closed strip gives

$$
\begin{aligned}
G_4&=-336/5+(1128/5)t+O(t^2),\\
K_4&=1-5t^2+(11/2+5h)t^3+O(t^4),\\
G_5&=-288+804t+O(t^2),\qquad
K_5=4-(35/2)t^2+O(t^3),\\
C&=1+(2+a)t+O(t^2),\\
d&=(Y+336/5)t+\bigl(-(a+2)Y-1464/5\bigr)t^2+O(t^3),\\
Z_Y(a,t)&=12Y-288/5+tN_Y(a)+t^2M_Y(a)+O(t^3),\\
N_Y(a)&=-(15+16a)Y+(96a-5364)/5,\\
M_Y(a)&=21162/5+(75/2)Y+(7536/5+39Y)a
                              +(-1668/5+24Y)a^2.
\end{aligned}
\tag{7.12}
$$

Every remainder is uniform for $0\le a\le1$. Indeed the rational
extensions have bounded derivatives on a compact smaller strip.
The following polynomial certificate also fixes the two coefficients
needed at the endpoints. With $L=UVW$, put

$$
\begin{aligned}
G_{4n}&=96VW-288UW+(1248/5)UV,\\
K_{4n}&=L+t(-4VW+6UW-4UV),\\
G_{5n}&=360VW-960UW+624UV,\\
K_{5n}&=4L+t(-15VW+20UW-10UV),\\
D_n&=tL+AK_{4n},\qquad R_n=YL-AG_{4n},\\
E&=BG_{5n}D_n+(tL+BK_{5n})R_n
                         -(12Y-288/5)LD_n.
\end{aligned}
\tag{7.13}
$$

These are polynomials in $a,Y,t$. Substitution in (7.10)–(7.11)
gives $d=tR_n/D_n$ and $Z_Y-(12Y-288/5)=E/(LD_n)$.
Their exact coefficients are

$$
\begin{gathered}
L|_{t=0}=D_n|_{t=0}=2,\qquad
[t^0]E=0,\qquad [t^0](LD_n)=4,\qquad [t](LD_n)=20+4a,\\
[t]E=4N_Y(a),\qquad
[t^2]E=4M_Y(a)+(20+4a)N_Y(a).
\end{gathered}
\tag{7.14}
$$

Thus division by the nonzero constant term yields exactly (7.12),
including its quadratic coefficient, uniformly at both source endpoints.

Suppose now $b_n\to\infty$ in a fixed fiber. Choose a subsequence
with $a_n\to a_0\in[0,1]$ and $t_n\downarrow0$. The constant
term of (7.12) forces $z=12Y-288/5$; subtracting it and dividing
by $t_n>0$ forces $N_Y(a_0)=0$. Equivalently

$$
Y=r(a_0):=\frac{96a_0-5364}{5(15+16a_0)},\qquad
r'(a)=\frac{87264}{5(15+16a)^2}>0.
\tag{7.15}
$$

The denominator is positive on $[0,1]$, and
$r(0)=-1788/25$, $r(1)=-5268/155$. This proves necessity of
the corresponding closed segment, for positive and nonnegative
sources alike.

Fix $Y$ strictly between these endpoint values and put
$z=12Y-288/5$. The unique zero of $N_Y$ is

$$
a_0=\frac{5364+75Y}{96-80Y}\in(0,1).
\tag{7.16}
$$

The quotient
$F_Y(a,t)=(Z_Y(a,t)-z)/t$ extends real-analytically across
$t=0$, since the numerator vanishes identically there. It satisfies

$$
F_Y(a,0)=N_Y(a),\qquad
\partial_aF_Y(a_0,0)=96/5-16Y>0.
\tag{7.17}
$$

The real-analytic implicit function theorem gives a unique local
analytic solution $a(t)$ through $(a_0,0)$. For positive small
$t$, it has $0<a(t)<1$. Define

$$
P_t=\begin{pmatrix}
a(t)&1/t\\a(t)(1-a(t))t&1-a(t)
\end{pmatrix},\qquad d_t=tR_Y(a(t),t),
\tag{7.18}
$$

and define $g_t$ by (7.3). Its source is strictly positive, has
trace one and determinant zero, hence rank one. Interpolation
realizes clocks zero through three, (7.10) realizes clock four,
and $F_Y(a(t),t)=0$ realizes clock five. Explicitly, in this same
world the six readings are

$$
\begin{aligned}
g_t(0)+d_t&=0,&
(b_t+c_t)g_t(1)+d_t&=24,\\
(1+b_t)g_t(2)+d_t&=48,&
(1+2b_t+c_t)g_t(3)+d_t&=312/5,\\
(1+a_t+b_t+c_t)g_t(4)+d_t&=Y,&
(2-a_t+3b_t+c_t)g_t(5)+d_t&=z.
\end{aligned}
\tag{7.19}
$$

The gain is nonzero; more specifically $g_t(1)=24t+O(t^2)$.
Every parameter specifies one fixed world for the entire trajectory,
not a source or gain varying with the clock. Distinct parameters
have distinct $b_t=1/t$.

For gain shapes use the exact ratio, legitimate for positive small
$t$ because $g_t(1)\ne0$:

$$
\frac{g_t(2)}{g_t(1)}
 =\frac{48-d_t}{24-d_t}\frac{U}{V}
 =2+\frac{Y+96/5}{24}t+O(t^2).
\tag{7.20}
$$

The linear coefficient is independent of $a$. Composing with
$a(t)$ therefore preserves it. It is strictly negative throughout
the closed segment, since $-5268/155<-96/5$. The derivative of
this analytically extended ratio remains negative on a sufficiently
small interval. Thus the ratio is strictly decreasing there, and
two different gains cannot be proportional, with either sign of
proportionality.

It remains to decide both endpoints rather than discarding them.
The same analytic extension and nonzero derivative (7.17) apply at
$a_0=0$ and $a_0=1$. Differentiating $F_Y(a(t),t)=0$ gives

$$
a'(0)=-\frac{M_Y(a_0)}{96/5-16Y}.
\tag{7.21}
$$

The exact endpoint values are

$$
\begin{array}{c|c|c|c|c}
Y&a_0&M_Y(a_0)&96/5-16Y&a'(0)\\ \hline
-1788/25&0&7752/5&29088/25&-1615/1212\\
-5268/155&1&308496/155&87264/155&-6427/1818
\end{array}
\tag{7.22}
$$

At the lower endpoint the unique branch has $a(t)<0$ for positive
small $t$. Any unbounded sequence at that history would have
$b_n\to\infty$, $a_n\to0$ and $F_Y(a_n,t_n)=0$ by the preceding
necessity proof. Local uniqueness places it on this illegal branch,
a contradiction even for nonnegative sources. At the upper endpoint
the branch has $0<a(t)<1$ for positive small $t$; (7.18)–(7.20)
therefore give legal worlds and pairwise nonproportional gains there
also. The excluded orientation, the necessary segment, its interior
realizations and these two endpoint decisions prove (7.5). The
sequential contradiction also proves boundedness for each fixed
history outside that half-open segment. No gain sample was divided
out in the necessary direction; lower degrees, signs and all roots
were retained. ∎

## 8. 零 J 迹退化及固定 H* 的全走廊

**定理 8.1（零迹极限的两个必要读数关系）。** Fix any real $Y,z$.
If complete worlds realizing $H(Y,z)$ have nonnegative rank-one
trace-one sources with $u_n>0$ and $u_n\to0$, then

$$
z=\frac{15}{2}Y-408\qquad\hbox{or}\qquad
z=\frac{15}{8}Y-147.
\tag{8.1}
$$

No boundedness of their drifts or gains is assumed. A finite
nonnegative complete-world solution with $u=0$ must also satisfy
one of these relations.

For the fixed $H_*=H(48/5,-532/5)$ there are
$0<\varepsilon\le R<\infty$ such that every compatible
nonnegative rank-one trace-one source has
$\varepsilon\le u\le R$. Every corresponding drift and every
one of the four gain coefficients is bounded by constants depending
on this fixed history.

**证明。** If $u_n\to0$, then $b_n,c_n\to0$, $v_n\to1$,
and a subsequence of $a_n$ tends to $a_0\in\{0,1\}$, by
$bc=a(1-a)$. Instead of dividing a gain sample, treat
$d$ and $q_1=(24-d)/u$ as independent linear unknowns in the
last two equations, using $q_0=-d$, $q_2=(48-d)/v$ and
$q_3=(312/5-d)/(u+v)$. The equations are

$$
\begin{pmatrix}
1+T_4(1+6/v-4/(u+v))&4T_4\\
1+T_5(4+20/v-10/(u+v))&15T_5
\end{pmatrix}
\begin{pmatrix}d\\q_1\end{pmatrix}
=
\begin{pmatrix}
Y-T_4(-288/v+(1248/5)/(u+v))\\
z-T_5(-960/v+624/(u+v))
\end{pmatrix}.
\tag{8.2}
$$

Their limiting coefficient matrices, for $a_0=0$ and $a_0=1$
respectively, are

$$
\begin{pmatrix}4&4\\29&30\end{pmatrix},\qquad
\begin{pmatrix}7&8\\15&15\end{pmatrix},\qquad
\det=4,\ -15.
\tag{8.3}
$$

The right sides converge. Inversion near these nonzero determinants
bounds both $d_n$ and $q_{1,n}$ before any limit is taken. The
identity $d_n=24-u_nq_{1,n}$ gives $d_n\to24$. Passing to a
subsequence for $q_{1,n}\to q$ yields respectively

$$
\begin{array}{c|cc}
a_0&Y&z\\ \hline
0&288/5+4q&24+30q\\
1&456/5+8q&24+15q
\end{array}
\tag{8.4}
$$

Eliminating $q$ gives (8.1). For a finite solution with $u=0$,
clock one forces $d=24$. The same interpolation identities use
$q=g(1)$ without dividing by $u$, and give (8.4) directly.

For $H_*$ the residuals against the infinity line of Theorem 7.2
and the two zero-trace lines are exactly

$$
\begin{aligned}
-532/5-(12(48/5)-288/5)&=-164,\\
-532/5-((15/2)(48/5)-408)&=1148/5,\\
-532/5-((15/8)(48/5)-147)&=113/5.
\end{aligned}
\tag{8.5}
$$

They are nonzero. Theorem 7.2 bounds the whole nonnegative source
projection with $u>0$, and (8.1) excludes a sequence with $u\to0$.
There are no finite $u=0$ targets either. Thus a common positive
finite corridor contains every compatible source. Theorem 4.1 now
bounds the drift and all four gain coefficients on that entire
corridor. This application uses the global nonvanishing of
Theorem 2.1, including nonnegative source limits; it is stronger
than merely bounding the source entries. All bounds here fix the
six readings. ∎

## 9. H* 的四条源边界射线与六个完整目标

**定义 9.1（非负完整纤维与消元坐标）。** Use Euclidean coordinates

$$
(a,b,c,k_0,k_1,k_2,k_3,d)\in\mathbb R^8,\qquad
P=\begin{pmatrix}a&b\\c&1-a\end{pmatrix},\qquad
 g(T)=\sum_{j=0}^3k_jT^j.
\tag{9.1}
$$

Let $\mathcal F=\mathcal F_{48/5,-532/5}$ and let
$\mathcal F^+$ be the set satisfying the same six equations,
with $g\ne0$ and source conditions
$0\le a\le1$, $b,c\ge0$, $bc=a(1-a)$. These auxiliary
sources have rank one because their trace is one and determinant
is zero. They are legal witnesses only when all entries are positive.
Theorem 8.1 excludes $u=0$ throughout $\mathcal F^+$.
Degree drops remain present through zero leading coefficients.

For $u>0$ put $D=uv(u+v)>0$, and define

$$
\begin{aligned}
A_4&=96v(u+v)-288u(u+v)+(1248/5)uv,\\
B_4&=D-4v(u+v)+6u(u+v)-4uv,\\
A_5&=360v(u+v)-960u(u+v)+624uv,\\
B_5&=4D-15v(u+v)+20u(u+v)-10uv,\\
Q_i&=D+T_iB_i,\qquad N_i=y_iD-T_iA_i\quad(i=4,5),\\
y_4&=48/5,\qquad y_5=-532/5,\qquad
\mathscr E=N_4Q_5-N_5Q_4.
\end{aligned}
\tag{9.2}
$$

Here $A_i=D\gamma_i$ and $B_i=D\kappa_i$ are scalars,
not cumulative matrices. The remaining equations are exactly
$dQ_i=N_i$. Thus no denominator clearing changes compatibility.

**定理 9.2（全部六个有限源边界目标及合法解析趋近）。** The set
$\mathcal F^+\setminus\mathcal F$ has exactly six members.
Each is specified exactly by one root interval below, its source
$P_j(\tau)$, drift $N_4(\tau)/Q_4(\tau)$, and the interpolant
(7.3). There are two members on each of rays $j=1,2,3$ and
none on ray $j=4$. Exactly three have $u>2$: the larger root
on ray one and both roots on ray three. Every one of the six is
approached by a real-analytic one-sided arc of strictly positive
complete worlds in this same $\mathcal F$. On a sufficiently
small arc the sources are pairwise distinct and the gains are
pairwise nonproportional.

**证明。** A nonnegative source which is not positive has
$a=0$ or $a=1$ and $bc=0$. Since $u=0$ is excluded, exactly
one of $b,c$ is positive. These are precisely the four rays

$$
\begin{aligned}
P_1(t)&=\begin{pmatrix}0&0\\t&1\end{pmatrix},&
P_2(t)&=\begin{pmatrix}1&0\\t&0\end{pmatrix},\\
P_3(t)&=\begin{pmatrix}0&t\\0&1\end{pmatrix},&
P_4(t)&=\begin{pmatrix}1&t\\0&0\end{pmatrix},\qquad t>0.
\end{aligned}
\tag{9.3}
$$

For a coefficient vector $[p_0,\ldots,p_n]$, write
$[p_0,\ldots,p_n](t)=\sum_{i=0}^np_it^i$; all vectors below
use ascending powers. Exact substitution in (9.2) gives

$$
\mathscr E(P_j(t))=\frac45t f_j(t),
\tag{9.4}
$$

where

$$
\begin{aligned}
f_1&=[1148,796,-2571,-2038,421,240],\\
f_2&=[226,-349,-591,165,421,240],\\
f_3&=[1148,5868,9787,3898,-3973,-1984,820],\\
f_4&=[226,2295,6029,3879,-2737,-1836,820].
\end{aligned}
\tag{9.5}
$$

The full denominator and numerator coefficient identities are

$$
\begin{array}{c|l|l}
j&D&Q_4\\ \hline
1&[0,1,1]&[-4,-4,7,7]\\
2&[0,1,1]&[-8,-5,14,7]\\
3&[0,1,3,2]&[-4,-12,-3,7,2]\\
4&[0,1,3,2]&[-8,-21,0,9,2]
\end{array}
\tag{9.6}
$$

$$
\begin{array}{c|l|l}
j&5N_4&Q_5\\ \hline
1&[-480,-720,1200,1440]&[-30,-16,48,24]\\
2&[-960,-1008,2640,1440]&[-15,-15,24,24]\\
3&[-480,-1680,-432,768]&[-30,-106,-66,54,24]\\
4&[-960,-2928,240,768]&[-15,-75,-78,46,24]
\end{array}
\tag{9.7}
$$

$$
\begin{array}{c|l}
j&5N_5\\ \hline
1&[-3600,-2572,8948,4800]\\
2&[-1800,-2452,4148,4800]\\
3&[-3600,-13372,-6996,7576]\\
4&[-1800,-9652,-9876,7576]
\end{array}
\tag{9.8}
$$

These arrays together give (9.4) by polynomial multiplication,
without division by $Q_4$, $Q_5$ or any gain value.

Each of $f_1,f_2,f_3$ has exactly two sign variations in its
coefficient list. The following rational endpoint values exhibit
two disjoint sign-changing intervals for each:

$$
\begin{array}{c|c|r|r}
j&(l,r)&f_j(l)&f_j(r)\\ \hline
1&(67/100,68/100)&15741163989/500000000&-30181284/1953125\\
1&(266/100,267/100)&-7671169863/31250000&57630107989/500000000\\
2&(42/100,43/100)&113404679/31250000&-1152945079/500000000\\
2&(92/100,93/100)&-13745856/1953125&2444054921/500000000\\
3&(221/100,222/100)&8038599171741/50000000000&-12934588499/48828125\\
3&(295/100,296/100)&-2120439/640000&52535222784/48828125
\end{array}
\tag{9.9}
$$

The intermediate value theorem supplies a root in each interval.
Descartes' rule, counting multiplicity, bounds the total positive
roots by two. Hence each interval contains exactly one root, each
root is simple, and there are no others, including positive repeated
roots outside the intervals.

For $f_4$ a positivity certificate exhausts the entire positive
axis. For a polynomial of degree at most $n$, if
$p(l+(r-l)x)=\sum_{j=0}^nc_jx^j$, its degree-$n$ Bernstein
coefficients are

$$
\mathcal B_k=\sum_{j=0}^k c_j
                    \frac{\binom{k}{j}}{\binom{n}{j}},
\qquad 0\le k\le n.
\tag{9.10}
$$

On $[0,1]$ the Bernstein basis is nonnegative and sums to one,
so $p$ lies between the minimum and maximum of these coefficients.
The vectors for $f_4$ on the three indicated intervals are

$$
\begin{aligned}
[0,1]:\;&[226,1217/2,20894/15,11093/4,71414/15,6879,8676],\\
[1,2]:\;&[8676,10473,179234/15,253047/20,36472/3,21155/2,9900],\\
[2,3]:\;&[9900,18445/2,28342/3,251233/20,336392/15,46109,96040].
\end{aligned}
\tag{9.11}
$$

All entries are positive. For the remaining ray, ordinary powers give

$$
f_4(3+s)=[96040,299586,393722,248595,80423,12924,820](s)>0
\quad(s\ge0).
\tag{9.12}
$$

Thus $f_4$ has no positive root.

It remains essential to justify the drift divisions at the six
roots. Applying (9.10) to $Q_4$ from (9.6) on each closed root
interval gives the following containing bounds:

$$
\begin{array}{c|c|c}
j&[l,r]&Q_4([l,r])\text{ is contained in}\\ \hline
1&[67/100,68/100]&[-3/2,-6/5]\\
1&[266/100,267/100]&[166,169]\\
2&[42/100,43/100]&[-36/5,-7]\\
2&[92/100,93/100]&[4,6]\\
3&[221/100,222/100]&[78,80]\\
3&[295/100,296/100]&[265,270]
\end{array}
\tag{9.13}
$$

The coefficient formula (9.10) with the displayed rational inputs
proves every bound; each interval avoids zero. At a root $\tau$
define $d=N_4(\tau)/Q_4(\tau)$ and $g$ by (7.3).
Then $dQ_4=N_4$, and (9.4) gives $dQ_5=N_5$, without dividing
by $Q_5$. All six readings are therefore satisfied exactly. The
source is nonnegative rank one and trace one, $D>0$, the gain is
nonzero by the first two readings, and all coefficients are finite.
Conversely every target on a ray forces $\mathscr E=0$, so the
exhaustive roots just found include every possible target. A possible
$Q_4=0$ solution cannot escape this reasoning, since every positive
root lies in (9.13). Theorem 3.1 also gives uniqueness of the
complete target conditional on each such source. Since $u=t$ on
all four rays, (9.9) proves the asserted exact count with $u>2$.

For legal approach use an analytic source chart near each boundary
point. On rays one and two set

$$
P(a,t)=\begin{pmatrix}a&a(1-a)/t\\t&1-a\end{pmatrix};
\tag{9.14}
$$

on rays three and four set

$$
P(a,t)=\begin{pmatrix}a&t\\a(1-a)/t&1-a\end{pmatrix}.
\tag{9.15}
$$

These charts are analytic near $(a_0,\tau)$, where $a_0=0$
or $1$ and $\tau>0$; $u,v,u+v$ remain positive in a small
neighborhood. Define $g$ by interpolation for each $(a,t,d)$,
and let

$$
R_i(a,t,d)=d+T_i g(i)-y_i=\frac{dQ_i-N_i}{D},\quad i=4,5.
\tag{9.16}
$$

At a simultaneous solution the determinant in the variables $(t,d)$
is exactly

$$
\det\frac{\partial(R_4,R_5)}{\partial(t,d)}
=-\frac{\partial_t\mathscr E}{D^2}.
\tag{9.17}
$$

Indeed multiplication by $D^2$ and addition of
$\partial_t\mathscr E$ leaves
$(\partial_tQ_4)(dQ_5-N_5)-(\partial_tQ_5)(dQ_4-N_4)=0$.
At $a=a_0$, (9.4) and simplicity give
$\partial_t\mathscr E=(4/5)\tau f_j'(\tau)\ne0$.
The real-analytic implicit function theorem supplies analytic
$t(a),d(a)$ solving both equations near $a_0$.
Choose $a=s$ if $a_0=0$ and $a=1-s$ if $a_0=1$, for small
$s>0$. Then $0<a<1$, $t(a)>0$, and both off-diagonal entries
are positive with product $a(1-a)$. These are legal sources,
and interpolation plus (9.16) realize all six fixed readings in
one fixed world for every $s$. The nonzero gain and all coefficients
converge to those of the stated target. Different $s$ give different
$a$, hence different sources. The whole-fiber gain-ray result
[VII, Theorem 8.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md)
applies to these legal $H_*$ worlds and makes their gains
nonproportional. At the three boundary targets with $u>2$,
continuity preserves $u>2$ along a sufficiently small positive arc.
This proves approach to every target, without assuming any count
or smoothness of interior components. ∎

## 10. H* 的精确紧完备化

**定理 10.1（整个完整目标纤维的六点紧闭包）。** In the ambient
space (9.1),

$$
\overline{\mathcal F}^{\,\mathbb R^8}
=\mathcal F^+
=\mathcal F\ \sqcup\ \{\text{the six targets of Theorem 9.2}\}.
\tag{10.1}
$$

This closure is compact. The positive fiber $\mathcal F$ is
bounded, relatively open and dense in $\mathcal F^+$, and is
nonclosed and noncompact in $\mathbb R^8$. Every sequence in
$\mathcal F$ has a subsequence converging to a member of
$\mathcal F$ or one of the six added targets. Projection onto
sources is a homeomorphism from $\mathcal F^+$ to its compact
compatible source set, with inverse given by (3.2).

The relative boundary of $\mathcal F$ inside $\mathcal F^+$
is exactly the six added points. This is the source boundary meant
here. Its ambient topological boundary in $\mathbb R^8$ is instead
all of $\mathcal F^+$.

All statements hold, with transformed gain and drift, for each
fixed affine copy $H_*^{D_0,\lambda}$, $D_0\in\mathbb R$,
$\lambda\ne0$ of either sign. The constants may depend on the
fixed history and normalization parameters.

**证明。** Theorem 8.1 puts all nonnegative compatible sources
inside one compact corridor $\mathcal K_{\varepsilon,R}$ of
(4.2). Theorems 2.1, 3.1 and 4.1 apply on this entire corridor:
$\Delta>0$, its minimum there is positive, and the unique drift
and all four coefficients of the gain are bounded and continuous
functions of the source. Thus $\mathcal F^+$ is bounded in
$\mathbb R^8$, including every drift and gain coordinate, rather
than just its source projection.

The source inequalities, determinant and six reading equations
are closed polynomial conditions in (9.1). The only apparently
open condition in the definition of $\mathcal F^+$ is $g\ne0$;
it is redundant, since a zero gain would give the same reading
$d$ at clocks zero and one, contrary to $0\ne24$. Hence
$\mathcal F^+$ is closed as well as bounded, and is compact by
Heine–Borel. Every Euclidean limit of legal worlds retains the
nonnegative source conditions and all six equations, with nonzero
gain, so lies in $\mathcal F^+$. This rules out a zero-gain limit
without an extra gain assumption.

Conversely Theorem 9.2 exhausts $\mathcal F^+\setminus\mathcal F$
and gives a legal arc approaching each member of that difference.
Together with $\mathcal F\subset\mathcal F^+$ this proves (10.1).
Sequential compactness gives the subsequence statement. Theorem 3.1
gives a bijection under projection, and (3.2) is continuous on the
entire corridor, proving the homeomorphism, including at every
added source. It is conditional reconstruction at a supplied source,
not identification of that source from the history.

Strict positivity makes $\mathcal F$ relatively open in
$\mathcal F^+$, and (10.1) makes it dense. Each of the six missing
points is approached by legal worlds, so $\mathcal F$ is not
closed and cannot be compact in Euclidean space. Its relative
boundary is consequently $\mathcal F^+\setminus\mathcal F$.
In the ambient space it has empty interior, since every member
satisfies the hyperplane equation $k_0+d=0$. Its ambient boundary
is therefore its whole closure, not just the six added points.

Finally the affine map

$$
(P,g,d)\longmapsto(P,\lambda g,D_0+\lambda d)
\tag{10.2}
$$

is a homeomorphism of the coefficient/source ambient spaces for
fixed $\lambda\ne0$. At every original clock and actual action
it changes a reading $v$ to $D_0+\lambda v$. It preserves source
conditions, nonzero gain, degree and roots, and transports all six
ancestor equations and each approach arc. Both signs of $\lambda$
are permitted. The same map also transports Theorem 7.2 to every
fixed affine normalization of its histories. There is no bound
uniform over unbounded $Y,z,D_0,\lambda$, nor over an implicit
function interval as $Y$ varies. ∎

## 11. 全局几何与共同实际子分支的接口

**定义 11.1（完备化后仍需满足的联合条件）。** The unknown-source
and unknown-shape task remains the common-source system of
Definition 5.2. For any three distinct legal sources on one common
$H(Y,z)$, gains and drifts are forced by (3.2). The exact
$L_2$ obligation is (5.6), with the responses (5.4) evaluated on
those same three fixed worlds: for each sixth atom $E$, one
response $v_E$ must retain a set on which both seventh atoms have
a collision. The colliding pair may depend on both atoms, while
$v_E$ is shared across the seventh-action requirements for that
$E$. These are actual response partitions, not labels acquired
from the ancestor or separately realized pairs.

Theorem 7.2 supplies an exact family with different sources and
gain shapes at every history in (7.5); compatibility of all six
ancestor readings alone does not impose (5.6). At $H_*$,
Theorem 10.1 supplies a compact domain for the entire complete-world
fiber after adjoining its exact six source-boundary targets. The
responses (5.4), being polynomial in the coefficient/source ambient
coordinates, extend continuously to that closure. On
$(\mathcal F^+)^3$, the equations (5.6) define a closed incidence
set: for each $E$, choose the two collision pairs, equate their
common sixth responses and the two respective seventh responses,
and take the finite union over those choices, then the intersection
over $E$. This incidence set is compact. The needed locus also
requires three distinct legal positive members; a limit may instead
coalesce on a diagonal or meet an added boundary target. Compactness
alone therefore supplies neither such a legal triple nor its
exclusion. This is a constraint on the exact common-history system,
not a claim that an auxiliary boundary target is physically legal.

The known-shape and known-source conclusions of the
[whole-class companion, Theorems 4.1 and 5.1](FIB_JMMJM_WHOLE_CLASS_AFFINE_DECODERS.md),
the known-initial-root inverse of
[VIII, Theorem 2.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md),
and the gain-ray, slice and band results of
[VII, Theorems 8.2, 9.1 and 10.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md)
retain exactly the hypotheses in Definition 5.1. In particular the
six-point source boundary does not count interior components or
exclude interior singularities, and gives no global smoothness,
sixth-response injectivity, effective inverse, conditioning or
stability conclusion. The open mathematical alternatives are still
an exact legal solution of (5.2) and (5.6) for one common real
$Y,z$, or an everywhere obstruction for those equations. Theorem
10.1 restricts only $H_*$ and its fixed affine copies. Neither
that restriction nor a solution of its triple question would alone
supply the earlier-history bridge required by Definition 5.3 for
the unrestricted original eight-versus-nine problem.

**定义 11.2（数学来源与假设对应）。** The source-escape locus,
its endpoint decisions, the four-ray exhaustion and the complete-world
compactification are repository-derived deductions for this prescribed
actual observation map. They extend the source graph of Theorem 3.1
and the conditional geometry of VII; they are not external-priority
claims. The interpolation, Descartes root count with multiplicity,
Bernstein convex-hull identity, real-analytic implicit function theorem
and Heine–Borel theorem are established tools inside these proofs.

Yanjun Li, Kiryung Lee and Yoram Bresler, *A Unified Framework for
Identifiability Analysis in Bilinear Inverse Problems with Applications
to Subspace and Sparsity Models*,
[Definition 2.7 and Theorem 2.8, arXiv:1501.06120v1](https://arxiv.org/html/1501.06120v1),
require orbit identification among every compatible pair and a
conditional second-factor identification. Conditional reconstruction
by (3.2) does not establish the first condition. Their Theorem 3.3
also assumes a nonvanishing gain vector, full-row-rank coefficient
matrix and full-column-rank nondecomposable sensing matrix. Those
hypotheses do not supply a result for the present arbitrary-root,
additive-drift trajectory; no such bilinear identifiability theorem
is a premise of Theorems 7.2–10.1.

Paul Breiding, Fulvio Gesmundo, Mateusz Michałek and Nick Vannieuwenhoven,
*Algebraic compressed sensing*,
[Answers 7–9 and Theorem 4.12, arXiv:2108.13208v2](https://arxiv.org/html/2108.13208v2),
distinguish generic-point from everywhere identification. Theorem 4.12
uses a variety over an infinite field and a generic affine linear
projection to its dimension to obtain a finite map. No such genericity
hypothesis has been established for these prescribed actions and
readings. In particular neither its finite-fiber conclusion nor the
generic identification thresholds substitute for the explicit
source-escape and boundary calculations here. These citations compare
hypotheses; they do not assert an exhaustive literature classification.

## 追加锚（本行以下为增补区）
