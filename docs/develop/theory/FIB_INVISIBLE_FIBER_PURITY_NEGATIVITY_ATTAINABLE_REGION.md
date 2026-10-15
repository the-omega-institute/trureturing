# FIB invisible fiber: the sharp purity–negativity attainable region

## 1. Scope, proof status and source ownership

This volume determines the entire joint attainable region of whole-state purity
and negativity in the fixed five-coordinate invisible skew fiber. Its universal
statements include every legal real skew matrix, with arbitrary signs, dense
entries and positive semidefinite boundary states. Negativity always refers to
the original two five-dimensional factors.

The proofs are ordinary finite-dimensional mathematics. This is a theory
reference source, not a Lean/kernel certificate. No numerical certificate,
external priority claim or physical implementation claim is asserted. The
literature status of the additional deductions is `repo-derived`, relative to
the supplied source identified below; literature-wide originality is unresolved.

The inherited source is
[the mixed-state capacity and certification volume, C-106–C-108](AURIC_FIB_ATOM_HIDDEN_RELATIONS_MIXED_STATE_CAPACITY_AND_CERTIFICATION.md).
C-106 owns the matched-support reduction and its already attributed
partial-transpose blocks. C-107 owns the whole-state purity identity and the
distinction between the original tensor split and independent copies of the
whole source. C-108 owns the invisible skew fiber, its purity interval and
equal-two-block purity attainers, and the conditional actual-menu and fixed
fourteen-flag erasure statements. Those results are reused here.

The additional mathematical content relative to that source is the sharp lower
and upper negativity at every purity, the sign-matrix obstruction and exact
crossovers, the dense upper attainers, the maximum and the full interval between
the boundaries. Complete proofs and actual common-state constructions appear
below. The purely matrix-theoretic result does not require the operational
suppliers. Its interpretation as an actual-menu invisible fiber and as a fiber
erased by the specified port remains conditional on the C-108 interfaces in
Section 11. Their nested QMB/QFA and other source-specific suppliers are not
independently verified here.

Corrections or extensions after incorporation belong after the final append anchor with new
section numbers; the final append anchor and existing text are retained.

## 2. The fixed source class and its two coordinates

**定义 2.1（Original tensor split and matching embedding）。** Fix

$$
\mathcal H=H^{(1)}\otimes H^{(2)},\qquad
H^{(1)}=H^{(2)}=\mathbb C^5,
\qquad B=(0,1,2,3,13).
$$

Both local computational bases have this order. Define

$$
f(0)=13,\quad f(13)=0,\quad f(1)=3,\quad f(3)=1,\quad f(2)=2,
\qquad e_s=|s,f(s)\rangle.
$$

The isometry $J:\mathbb C^5\to\mathcal H$ is $J|s\rangle=e_s$;
thus $J^\dagger J=I_5$. Write
$\mathcal E=\operatorname{ran}J$ and

$$
S=\frac15JI_5J^\dagger
 =\frac15\sum_{s\in B}|s\rangle\langle s|
                    \otimes|f(s)\rangle\langle f(s)|.
$$

Matrix indices $1,2,3,4,5$ in the constructions below mean the positions in
$(0,1,2,3,13)$, not a different ordering or tensor split.
Write $\varepsilon_i$ for standard real coordinate vectors in $\mathbb R^5$
and $E_{sa}=|s\rangle\langle a|$ for the compressed $5\times5$ matrix units.

**定义 2.2（Every legal skew state）。** The class in this volume is exactly

$$
\mathfrak I=
\left\{\Gamma(X)=J C(X)J^\dagger:
 X\in M_5(\mathbb R),\quad X^T=-X,\quad
 C(X)=\frac{I_5+iX}{5}\succeq0\right\}.
\tag{2.1}
$$

In the inherited notation $C=I_5/5+iA$, one has $X=5A$.
No sign pattern, sparsity condition, fixed rank or particular block family is
imposed in (2.1). The skew condition gives zero diagonal, so every such $C$
has trace one and diagonal $1/5$.

Define

$$
\begin{aligned}
s(X)&=\sum_{i<j}X_{ij}^2,&
L(X)&=\sum_{i<j}|X_{ij}|,\\
p(X)&=\operatorname{tr}(\Gamma(X)^2),&
\mathcal N(X)&=\frac{\|\Gamma(X)^{\mathsf T_2}\|_1-1}{2}.
\end{aligned}
\tag{2.2}
$$

Here $\mathsf T_2$ transposes the original second five-dimensional factor:

$$
(|s,u\rangle\langle a,v|)^{\mathsf T_2}
 =|s,v\rangle\langle a,u|.
$$

The trace norm is the sum of singular values. In particular $p$ is the purity
of the whole $25$-dimensional source, not a marginal purity or a conditional
four-mode purity. This negativity is not concurrence in a single source's
bottom face, nor negativity across a later pair of independent source copies.

**引理 2.3（Exact matched populations force the support）。** Suppose an arbitrary
complex density matrix $\Gamma$ on $\mathcal H$ has all $25$ populations

$$
\langle s,u|\Gamma|s,u\rangle
  =\frac15\mathbf1_{\{u=f(s)\}}\qquad(s,u\in B).
\tag{2.3}
$$

Then it has a unique representation $\Gamma=JCJ^\dagger$ with
$C\succeq0$ and $C_{ss}=1/5$. Within this population class,
$\operatorname{Re}C=I_5/5$ is equivalent to membership in (2.1).

Proof. Positivity of every two-coordinate principal submatrix gives
$|\Gamma_{xy}|^2\le\Gamma_{xx}\Gamma_{yy}$.
An unmatched computational vector has zero diagonal entry by (2.3), so its
whole row and column vanish. All remaining entries lie in $\mathcal E$,
which gives $C=J^\dagger\Gamma J$ and the claimed uniqueness and positivity.
For Hermitian $C$, an entrywise vanishing real part of $C-I_5/5$ means that
it is $iX/5$ with $X$ real skew; conversely such a matrix has precisely that
real part. Positivity remains an explicit requirement. $\square$

## 3. The complete sharp region

**定理 3.1（Universal bounds and full joint attainment）。** For every state in
(2.1),

$$
0\le s\le2,\qquad p=\frac15+\frac{2s}{25},\qquad
\mathcal N=\frac{L}{5}.
\tag{3.1}
$$

At each $s\in[0,2]$, the exact lower and upper negativities are

$$
\mathcal N_{\min}(s)=
\begin{cases}
\sqrt{s}/5,&0\le s\le1,\\
(1+\sqrt{s-1})/5,&1\le s\le2,
\end{cases}
\tag{3.2}
$$

$$
\mathcal N_{\max}(s)=
\begin{cases}
\sqrt{10s}/5,&0\le s\le10/7,\\
(\sqrt7+\sqrt{3(s-1)})/5,&10/7\le s\le2.
\end{cases}
\tag{3.3}
$$

Equivalently, in whole-state purity,

$$
\mathcal N_{\min}(p)=
\begin{cases}
\sqrt{(5p-1)/10},&1/5\le p\le7/25,\\
\bigl(1+\sqrt{(25p-7)/2}\bigr)/5,&7/25\le p\le9/25,
\end{cases}
\tag{3.4}
$$

$$
\mathcal N_{\max}(p)=
\begin{cases}
\sqrt{5p-1},&1/5\le p\le11/35,\\
\bigl(\sqrt7+\sqrt{3(25p-7)/2}\bigr)/5,&11/35\le p\le9/25.
\end{cases}
\tag{3.5}
$$

The entire joint attainable set is exactly

$$
\left\{(p,n):\frac15\le p\le\frac9{25},\quad
 \mathcal N_{\min}(p)\le n\le\mathcal N_{\max}(p)\right\}.
\tag{3.6}
$$

In particular both endpoints and every intermediate $n$ at each fixed $p$
belong to actual states $\Gamma(X)$ with those same two coordinates. The
unrestricted maximum within this fiber is

$$
\max_{\Gamma\in\mathfrak I}\mathcal N(\Gamma)
 =\frac{\sqrt7+\sqrt3}{5}.
\tag{3.7}
$$

Every maximizer has purity $9/25$ and rank three, with compressed nonzero
eigenvalues $2/5,2/5,1/5$. This is not a maximum over arbitrary bipartite
$5\times5$ density matrices.

Proof. Section 4 proves (3.1) with its full positivity condition. Section 5
proves (3.2) and realizes each lower endpoint. Sections 6–8 prove (3.3) for
every legal matrix and realize each upper endpoint. Section 9 constructs a
legal path at fixed $s$ filling the interval, proving (3.6). The substitution
$s=(25p-5)/2$ gives (3.4)–(3.5). Section 10 proves the crossovers, maximum,
equality and rank statements. All component proofs are given below. $\square$

## 4. Spectral legality, purity and the original-split negativity

**引理 4.1（Real skew normal form, including degeneracies）。** Every real skew
$5\times5$ matrix is orthogonally conjugate to

$$
\mathcal D(a,b)=aR\oplus bR\oplus0,
\qquad R=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad a,b\ge0.
\tag{4.1}
$$

Its Hermitian matrix $iX$ has eigenvalues $a,-a,b,-b,0$. Consequently

$$
I_5+iX\succeq0\quad\Longleftrightarrow\quad
a,b\le1\quad\Longleftrightarrow\quad\|X\|_{\mathrm{op}}\le1,
\qquad s=a^2+b^2.
\tag{4.2}
$$

Proof. The real symmetric matrix $-X^2=X^TX$ is positive semidefinite. For
a real unit eigenvector $v$ with positive eigenvalue $a^2$, set
$w=-Xv/a$. Then

$$
v^Tw=0,\qquad\|w\|=1,\qquad Xv=-aw,\qquad Xw=av.
$$

The orthonormal plane spanned by $v,w$ is invariant. Its orthogonal complement
is also invariant: if $z$ is perpendicular to that plane, skewness gives
$\langle Xz,v\rangle=-\langle z,Xv\rangle=0$ and likewise for $w$.
Repeat on the complement. A remaining one-dimensional skew block is zero;
if a larger residual space has only zero eigenvalues of $-X^2$, then
$\|Xz\|^2=\langle z,-X^2z\rangle=0$ there, so $X$ vanishes on it.
This yields (4.1) with zero parameters allowed.

The two blocks give the listed eigenvalues of $iX$ and the singular values
$a,a,b,b,0$ of $X$. This proves the positivity and norm equivalences.
Finally $\operatorname{tr}(X^TX)=2s=2(a^2+b^2)$. $\square$

**命题 4.2（Exact two-coordinate reduction and separability）。** For every
$\Gamma(X)\in\mathfrak I$,

$$
p=\operatorname{tr}(C(X)^2)
 =\frac15-\frac{\operatorname{tr}X^2}{25}
 =\frac15+\frac{2s}{25},\qquad \mathcal N=\frac{L}{5}.
\tag{4.3}
$$

Moreover $S$ is the unique separable state in this class; every nonzero $X$
gives a non-PPT entangled state on $H^{(1)}\mid H^{(2)}$.

Proof. The first equality uses $J^\dagger J=I_5$ and cyclicity of trace.
Expanding $(I_5+iX)^2$ and using $\operatorname{tr}X=0$ gives the second,
and $\operatorname{tr}X^2=-2s$ gives the third. Lemma 4.1 gives $0\le s\le2$.

Write $C=(c_{ij})$. Partial transpose sends
$c_{ij}|i,f(i)\rangle\langle j,f(j)|$ to
$c_{ij}|i,f(j)\rangle\langle j,f(i)|$. On each matched vector $e_i$ there
is a scalar block $1/5$. For each of the ten unordered pairs $i\ne j$,
the two vectors $|i,f(j)\rangle,|j,f(i)\rangle$ give a block

$$
\begin{pmatrix}0&c_{ij}\\\overline{c_{ij}}&0\end{pmatrix},
\qquad \det\left(zI-
\begin{pmatrix}0&c_{ij}\\\overline{c_{ij}}&0\end{pmatrix}\right)
 =z^2-|c_{ij}|^2.
\tag{4.4}
$$

Its eigenvalues are $\pm|c_{ij}|$. Because $f$ is a permutation, these ten
two-dimensional blocks and five scalar blocks are mutually orthogonal and
exhaust the $25$ dimensions. Thus, including zero entries,

$$
\|\Gamma^{\mathsf T_2}\|_1
 =1+2\sum_{i<j}|c_{ij}|=1+\frac{2L}{5},
$$

which proves the negativity identity. This is the inherited maximally
correlated block calculation, with the split and normalization explicit.

If $X\ne0$, some block has a strictly negative eigenvalue, so the state is
not PPT. A product positive matrix remains positive when its second factor
is transposed, and convex combinations preserve positivity. Every separable
state is therefore PPT, so $X\ne0$ is entangled. At $X=0$, the explicit
product-state mixture defining $S$ is separable. No general PPT sufficiency
in dimension $5\times5$ has been used. $\square$

## 5. The lower envelope and all its equality patterns

**定理 5.1（Capped-entry lower frontier）。** Every legal $X$ satisfies

$$
L\ge\begin{cases}
\sqrt{s},&0\le s\le1,\\
1+\sqrt{s-1},&1\le s\le2.
\end{cases}
\tag{5.1}
$$

Equality states exist throughout. More precisely, up to the positions and
signs of their upper entries, the lower equality patterns are:

| Parameter | Nonzero upper entries at lower equality |
| --- | --- |
| $s=0$ | None |
| $0<s<1$ | One entry of magnitude $\sqrt{s}$ |
| $s=1$ | One unit entry |
| $1<s<2$ | Two disjoint edges of magnitudes $1,\sqrt{s-1}$ |
| $s=2$ | Two disjoint unit edges |

Proof. Let $z_1,\ldots,z_{10}$ be the absolute upper entries. They are in
$[0,1]$ since $|\varepsilon_i^TX\varepsilon_j|\le\|X\|_{\mathrm{op}}\le1$. Also

$$
\sum_jz_j=L,\qquad\sum_jz_j^2=s,\qquad
L^2=s+2\sum_{j<k}z_jz_k\ge s.
\tag{5.2}
$$

Equality in the last inequality holds exactly when at most one entry is
nonzero. This proves the first branch and its equality patterns.

For $1\le s\le2$ one has $L\ge\sqrt{s}\ge1$. If $L\ge2$, then
$L\ge1+\sqrt{s-1}$. If $1\le L<2$, consider two strictly fractional
entries $x,y\in(0,1)$. When $x+y\le1$, replace them by $(x+y,0)$;
the square sum increases by $2xy>0$. When $x+y\ge1$, replace them by
$(1,x+y-1)$; the square sum increases by $2(1-x)(1-y)>0$.
These replacements preserve the sum and the caps, and each reduces the
number of strictly fractional entries. After finitely many steps, at most
one fractional entry remains. With sum $L\in[1,2)$ the final list must be
$1,L-1,0,\ldots,0$. Therefore

$$
s\le1+(L-1)^2,\qquad L\ge1+\sqrt{s-1}.
\tag{5.3}
$$

For $1<s<2$, equality has $L<2$ and requires that no strict increase was
possible in the replacement argument. The original list already consists of
one unit entry and one fractional entry $\sqrt{s-1}$, with the others zero.
The Euclidean norm of row $i$ is $\|X^T\varepsilon_i\|\le\|X\|_{\mathrm{op}}\le1$.
A row containing a unit entry consequently contains no other nonzero entry.
The two edges must be disjoint. At $s=1$, equality in (5.2) gives one unit
edge. At $s=2$, lower equality gives $L=2$ and
$\sum_j(z_j-z_j^2)=L-s=0$; every entry is zero or one, so there are exactly
two unit edges, again disjoint. At $s=0$ all entries vanish.

For actual attainment take

$$
X_{\mathrm{low}}(s)=
\begin{cases}
\mathcal D(\sqrt{s},0),&0\le s\le1,\\
\mathcal D(1,\sqrt{s-1}),&1\le s\le2.
\end{cases}
\tag{5.4}
$$

These matrices have singular parameters at most one, square sum $s$, and
absolute sum equal to (5.1). They give positive trace-one matrices
$J(I_5+iX_{\mathrm{low}}(s))J^\dagger/5$ with the required $p$ and
$\mathcal N$ simultaneously. Arbitrary signs on the listed disjoint edges
are legal by the same two-block spectrum, and their positions can be
permuted. This also proves sufficiency of all equality patterns. $\square$

The replacement argument is an inequality for capped scalar entries; it
does not assume that every intermediate scalar list represents a legal skew
contraction. Legality is supplied separately by (5.4).

## 6. An obstruction for every five-coordinate skew sign matrix

**引理 6.1（Determinant and parity obstruction）。** Let $T$ be any real skew
$5\times5$ matrix with all ten upper entries in $\{-1,1\}$. If its skew
singular parameters are $\alpha\ge\beta\ge0$, then

$$
\alpha^2+\beta^2=10,\qquad
\alpha^2\beta^2\in\{5,13,21\},\qquad
\alpha^2\ge7,\quad0<\beta^2\le3.
\tag{6.1}
$$

The membership assertion is a necessary restriction, not a claim that every
listed product is realized.

Proof. Lemma 4.1 and the ten squared unit upper entries give
$\alpha^2+\beta^2=10$. For a skew $4\times4$ matrix with lexicographically
ordered upper entries $(a,b,c,d,e,f)$, determinant expansion is

$$
\begin{aligned}
\det\begin{pmatrix}
0&a&b&c\\-a&0&d&e\\-b&-d&0&f\\-c&-e&-f&0
\end{pmatrix}
 &=a^2f^2+b^2e^2+c^2d^2-2abef+2acdf-2bcde\\
 &=(af-be+cd)^2.
\end{aligned}
\tag{6.2}
$$

For each principal four-coordinate submatrix of $T$, the three summands
inside the square are signed units. Their sum is $\pm1$ or $\pm3$, so
its determinant is $1$ or $9$.

The coefficient of $z$ in $\det(zI_5-T)$ is the sum of these five principal
determinants. Indeed, choosing one diagonal $z$ in the determinant expansion
leaves the determinant of the complementary four-coordinate submatrix of
$-T$; the even dimension makes this equal to the corresponding determinant
of $T$. On the other hand the normal form gives

$$
\det(zI_5-T)=z(z^2+\alpha^2)(z^2+\beta^2).
$$

If $k$ of those five determinants are $9$, comparison yields
$\alpha^2\beta^2=5+8k$. The nonnegative parameters with sum of squares ten
satisfy $\alpha^2\beta^2\le25$, so the integer $k$ is at most two.
In particular the product is at least five, hence $\beta>0$, and is at most
twenty-one. Since $\alpha^2\ge5$,

$$
(\alpha^2-5)^2=25-\alpha^2\beta^2\ge4
$$

forces $\alpha^2\ge7$. The sum identity gives $\beta^2\le3$.
This proves the obstruction for every sign pattern without enumeration.
$\square$

## 7. The universal upper envelope

**定理 7.1（Upper bound for arbitrary legal skew matrices）。** For every $X$
in (2.1),

$$
L\le\begin{cases}
\sqrt{10s},&0\le s\le10/7,\\
\sqrt7+\sqrt{3(s-1)},&10/7\le s\le2.
\end{cases}
\tag{7.1}
$$

Proof. Choose a skew sign matrix $T$ whose upper signs agree with those of
$X$, choosing either sign at a zero entry. Then

$$
L=\frac12\operatorname{tr}(T^TX).
$$

Orthogonally conjugate $T$ to $\mathcal D(\alpha,\beta)$ with
$\alpha\ge\beta$, and let $Y$ be $X$ in the same coordinates. Orthogonal
conjugation preserves skewness, the operator norm and the Frobenius norm.
Consequently

$$
L=\alpha Y_{12}+\beta Y_{34}\le\alpha u+\beta v,
\qquad u=|Y_{12}|,\quad v=|Y_{34}|,
$$

where $0\le u,v\le1$ and $u^2+v^2\le s$. By Lemma 6.1 and
Cauchy–Schwarz,

$$
L\le\sqrt{(\alpha^2+\beta^2)(u^2+v^2)}\le\sqrt{10s}.
\tag{7.2}
$$

For $10/7\le s\le2$, discard the cap on $v$ and write

$$
L\le F(u)=\alpha u+\beta\sqrt{s-u^2},\qquad 0\le u\le1.
$$

The square root is positive throughout this interval, since $s>1$. Its
derivative satisfies

$$
F'(u)=\alpha-\frac{\beta u}{\sqrt{s-u^2}}\ge0,
$$

because the equivalent squared inequality is
$\alpha^2s\ge(\alpha^2+\beta^2)u^2$, and

$$
\alpha^2s\ge7s\ge10\ge10u^2
 =(\alpha^2+\beta^2)u^2.
$$

Thus $L\le F(1)=\alpha+\beta\sqrt{s-1}$. Put $r=\sqrt{s-1}$.
For $0\le\beta\le\sqrt3$, the function

$$
g(\beta)=\sqrt{10-\beta^2}+r\beta
$$

has derivative

$$
g'(\beta)=r-\frac{\beta}{\sqrt{10-\beta^2}}
 \ge r-\sqrt{3/7}\ge0.
$$

Here the first inequality follows by squaring the nonnegative ratio and
using $\beta^2\le3$; the second uses $s\ge10/7$. Therefore

$$
L\le g(\sqrt3)=\sqrt7+\sqrt{3(s-1)}.
\tag{7.3}
$$

At $s=10/7$, (7.2) and (7.3) both equal $10/\sqrt7$.
Every relaxation in this argument enlarges the admissible scalar set and
therefore preserves the direction of the upper bound. The next section
supplies legal equality matrices, so realizability is not assumed from a
relaxation optimum. $\square$

## 8. Dense legal upper attainers at every purity

**定理 8.1（Seven-plus-three-entry construction）。** In the fixed positional
order define the real skew matrix

$$
M(a,b)=
\begin{pmatrix}
0&a&a&a&a\\
-a&0&b&-b&a\\
-a&-b&0&b&a\\
-a&b&-b&0&a\\
-a&-a&-a&-a&0
\end{pmatrix}.
\tag{8.1}
$$

Its skew singular parameters are $\sqrt7|a|,\sqrt3|b|$, with one zero
direction and with further zeros when either parameter vanishes. For
$a,b\ge0$,

$$
s(M)=7a^2+3b^2,\qquad L(M)=7a+3b.
\tag{8.2}
$$

The upper endpoint at each $s$ is the actual state

$$
\Gamma_{\mathrm{up}}(s)
 =\frac15J(I_5+iX_{\mathrm{up}}(s))J^\dagger,
\qquad X_{\mathrm{up}}(s)=M(a(s),b(s)),
\tag{8.3}
$$

where

$$
(a(s),b(s))=
\begin{cases}
\bigl(\sqrt{s/10},\sqrt{s/10}\bigr),&0\le s\le10/7,\\
\bigl(1/\sqrt7,\sqrt{(s-1)/3}\bigr),&10/7\le s\le2.
\end{cases}
\tag{8.4}
$$

Proof. Put $G=M(1,0)$, $H=M(0,1)$, so $M(a,b)=aG+bH$. An explicit
plane certificate for $G$ is

$$
G=uv^T-vu^T,\qquad
u=(1,0,0,0,-1)^T,\qquad
v=(1/2,1,1,1,1/2)^T.
\tag{8.5}
$$

Indeed this expression gives exactly the seven unit upper entries in the
$a$ positions of (8.1), and zero in the other three positions. The vectors
are orthogonal, with $\|u\|^2=2$, $\|v\|^2=7/2$. Hence

$$
Gu=-2v,\qquad Gv=(7/2)u,
\qquad G|_{\operatorname{span}(u,v)^\perp}=0.
$$

On the normalized basis of this plane, $G$ has off-diagonal magnitudes
$\sqrt2\sqrt{7/2}=\sqrt7$; its sole nonzero skew singular parameter is
$\sqrt7$. In particular $G$ has rank two. Equivalently, its middle three
rows coincide, its fifth row is minus its first plus its second, and its
first two rows are independent.

The matrix $H$ vanishes outside the middle three coordinates, where it is

$$
\begin{pmatrix}0&1&-1\\-1&0&1\\1&-1&0\end{pmatrix}.
$$

It acts on the two-dimensional plane

$$
W=\{x\in\mathbb R^5:x_1=x_5=0,\quad x_2+x_3+x_4=0\}.
\tag{8.6}
$$

The square of the middle block has diagonal $-2$ and off-diagonal $1$,
so $H^2x=-3x$ on $W$. It kills the outer coordinate axes and the middle
all-ones vector, which span $W^\perp$. Thus $H$ has rank two and sole
nonzero skew singular parameter $\sqrt3$. Both $u$ and $v$ are perpendicular
to $W$, so the active planes of $G$ and $H$ are orthogonal. The two matrices
act independently on them and vanish on the remaining common direction.
This proves the singular parameters of $M(a,b)$. Counting its seven $a$
positions and three $b$ positions proves (8.2), without cancellation.

On the first branch of (8.4) the squared singular parameters are
$7s/10,3s/10$, both at most one precisely throughout the indicated range.
The square sum is $s$ and
$L=10\sqrt{s/10}=\sqrt{10s}$. On the second branch the singular parameters
are $1,\sqrt{s-1}$, both at most one, and

$$
s=7\left(\frac1{\sqrt7}\right)^2
  +3\left(\sqrt{\frac{s-1}{3}}\right)^2,
\qquad L=\sqrt7+\sqrt{3(s-1)}.
$$

Lemma 4.1 proves positivity; the zero skew diagonal proves trace one. Thus
the same state (8.3) realizes the given purity and the upper negativity
simultaneously. At $s=10/7$ the two formulas give the identical matrix
$M(1/\sqrt7,1/\sqrt7)$. At $s=2$ the parameters are both one, so the
compressed spectrum is $2/5,2/5,1/5,0,0$. $\square$

The construction is dense for $s>0$. Its invariant-plane certificate proves
that the upper bound is attainable within the original legal source class;
it is not an optimization over independently chosen entry magnitudes.

## 9. No gaps at fixed whole-state purity

**定理 9.1（Legal fixed-purity interval filling）。** At each $s\in[0,2]$, every
value of $L$ between the two established boundary values occurs at an actual
legal $X$ with that same $s$. Thus (3.6) is the full joint attainable set.

Proof. If $s=0$, then $X=0$ and the assertion is immediate. Fix $s>0$ and put

$$
c=\min(\sqrt{s},1),\qquad d=\sqrt{s-c^2}.
$$

The lower matrix is $\mathcal D(c,d)$. Let $(a_*,b_*)$ be the ordered skew
singular parameters of the upper matrix from Section 8:

$$
(a_*,b_*)=
\begin{cases}
\bigl(\sqrt{7s/10},\sqrt{3s/10}\bigr),&0<s\le10/7,\\
\bigl(1,\sqrt{s-1}\bigr),&10/7\le s\le2.
\end{cases}
\tag{9.1}
$$

They satisfy $\sqrt{s/2}\le a_*\le c$. On the first branch,
$7s/10\ge s/2$; for $s\le1$ one has $7s/10\le s$, and for
$1\le s\le10/7$ one has $7s/10\le1$. On the second branch $a_*=c=1$
and $s\le2$ gives the remaining inequality.

First vary $a$ continuously from $c$ down to $a_*$ and set
$b=\sqrt{s-a^2}$. Throughout this segment,

$$
\sqrt{s/2}\le a\le1,\qquad0\le b\le a\le1.
$$

Consequently $\mathcal D(a,b)$ is a continuous legal fixed-$s$ path from
the lower matrix to $\mathcal D(a_*,b_*)$.

By Lemma 4.1 there is an orthogonal matrix $Q_0$ with

$$
X_{\mathrm{up}}(s)=Q_0\mathcal D(a_*,b_*)Q_0^T.
\tag{9.2}
$$

There is always a zero direction: the fifth coordinate of $\mathcal D$.
Right multiplication of $Q_0$ by $\operatorname{diag}(1,1,1,1,-1)$
reverses its determinant and leaves (9.2) unchanged. Choose $Q_0\in SO(5)$.
This also works when a skew parameter is zero or when the two are equal.

For completeness, a matrix in $SO(5)$ is joined to the identity by a finite
product of coordinate-plane rotations. To see this, left multiply by plane
rotations containing the first coordinate to eliminate the other entries
of its first column and make that column $\varepsilon_1$; a rotation by $\pi$ in a
two-coordinate plane can correct a negative first direction. Orthogonality
then leaves a block of determinant $+1$ on the last four coordinates.
Repeat on that block, down to a two-coordinate rotation. The remaining
one-coordinate block is $+1$ by the determinant condition. Reversing these
steps writes $Q_0$ as a finite product of plane rotations. Replace every
angle in that product by $t$ times the angle. This gives a continuous
$Q(t)\in SO(5)$ with $Q(0)=I_5$ and $Q(1)=Q_0$.

The second path

$$
X(t)=Q(t)\mathcal D(a_*,b_*)Q(t)^T
\tag{9.3}
$$

preserves skewness, singular parameters, legality and $s$, and ends at the
upper matrix. Concatenating the two paths gives a continuous path of legal
states from the lower to the upper endpoint at exactly the same purity.
The function $L(X)$ is a continuous sum of absolute entries. The intermediate
value theorem therefore supplies an actual state for every value between
the endpoint values; monotonicity along the path is unnecessary. Universal
lower and upper bounds exclude every value outside this interval.
This proves the full region. $\square$

The orthogonal conjugations here are constructions of mathematical states
in the fixed class. They are not asserted to be available local operations
on the original two subsystems.

## 10. Crossovers, maximum, endpoints and ranks

**命题 10.1（Exact obstruction to the Cauchy–Schwarz branch）。** For $s>0$,
the equality $L=\sqrt{10s}$ is attainable in the legal class exactly when
$s\le10/7$. In purity coordinates the exact upper crossover is $p=11/35$.
The lower crossover is $s=1$, equivalently $p=7/25$.

Proof. Applied directly to the ten absolute upper entries, Cauchy–Schwarz
has equality exactly when all ten are $\sqrt{s/10}$. Thus any such equality
matrix is $X=\sqrt{s/10}\,T$ for a skew sign matrix $T$. Lemma 6.1 gives

$$
\|X\|_{\mathrm{op}}^2=\frac{s}{10}\alpha^2\ge\frac{7s}{10}.
$$

It is illegal when $s>10/7$. Section 8 realizes equality for every
$s\le10/7$, including the boundary. This rules out all possible sign
patterns above the crossover, not just the displayed family. At the join,

$$
\mathcal N_{\max}(10/7)
 =\frac{10}{5\sqrt7}=\frac2{\sqrt7},\qquad
\frac15+\frac{2(10/7)}{25}=\frac{11}{35}.
$$

The lower proof also identifies its exact change: for $s>1$ an equality
$L=\sqrt{s}$ would require a single entry larger than one, violating the
entry cap. The second lower branch is attained and is strictly larger
there. At $s=1$ both lower formulas are one before division by five, and
the corresponding purity is $7/25$. $\square$

**定理 10.2（Maximum and the purity and rank of every maximizer）。** The maximum
is (3.7), attained by

$$
X_{\max}=M(1/\sqrt7,1/\sqrt3),\qquad
\Gamma_{\max}=\frac15J(I_5+iX_{\max})J^\dagger.
\tag{10.1}
$$

Every maximizer has $s=2$, $p=9/25$ and rank three.

Proof. The attained upper envelope for $L$ is continuous at $10/7$ and
strictly increasing on both branches. Hence its largest value occurs only
at $s=2$, where it is $\sqrt7+\sqrt3$. Section 8 gives the legal matrix
(10.1) attaining it. A different maximizer at $s<2$ would have $L$ bounded
by a strictly smaller upper-envelope value, a contradiction. For every
legal $X$ with $s=2$, its parameters obey $a,b\le1$ and $a^2+b^2=2$,
so both are one. The compressed spectrum is therefore

$$
\operatorname{spec}C=(2/5,2/5,1/5,0,0).
$$

The isometry $J$ preserves nonzero eigenvalues and rank. This proves the
purity and rank statement for every maximizer, without claiming a
classification of their entrywise sign patterns. $\square$

**命题 10.3（All boundary and rank degeneracies）。** The distinguished endpoints
and joins are as follows. Ranks in the last column are those of the lower
and upper constructions respectively.

| $s$ | Whole-state purity $p$ | Exact negativity interval | Lower and upper rank |
| --- | --- | --- | --- |
| $0$ | $1/5$ | $\{0\}$ | $5,5$ |
| $1$ | $7/25$ | $[1/5,\sqrt{10}/5]$ | $4,5$ |
| $10/7$ | $11/35$ | $[(1+\sqrt{3/7})/5,2/\sqrt7]$ | $4,4$ |
| $2$ | $9/25$ | $[2/5,(\sqrt7+\sqrt3)/5]$ | $3,3$ |

For the lower construction the rank is five for $0\le s<1$, four for
$1\le s<2$, and three at $s=2$. For the upper construction the rank is five
for $0\le s<10/7$, four for $10/7\le s<2$, and three at $s=2$.

Proof. For any legal skew parameters $a,b$, the five compressed eigenvalues
are

$$
\frac{1+a}{5},\quad\frac{1-a}{5},\quad
\frac{1+b}{5},\quad\frac{1-b}{5},\quad\frac15.
\tag{10.2}
$$

Each parameter equal to one creates exactly one zero eigenvalue; a zero
parameter gives two positive eigenvalues $1/5$, not new zero eigenvalues.
The remaining twenty ambient dimensions always have zero eigenvalue.

At $s=0$, the square sum forces $X=0$, so $S$ is the unique state and both
envelopes vanish. At $s=1$, the lower matrix is $\mathcal D(1,0)$, with
rank four, whereas the upper matrix is $M(1/\sqrt{10},1/\sqrt{10})$ with
parameters $\sqrt{7/10},\sqrt{3/10}<1$ and rank five. Their negativity
values are the second row of the table.

At $s=10/7$, the two upper constructions coincide at
$M(1/\sqrt7,1/\sqrt7)$ with parameters $1,\sqrt{3/7}$ and rank four.
The lower matrix is $\mathcal D(1,\sqrt{3/7})$, also rank four, giving the
listed lower value. At $s=2$, the lower matrix $\mathcal D(1,1)$ has
$L=2$, while (10.1) has $L=\sqrt7+\sqrt3$. Both have parameters $1,1$
and rank three. They are different states at the same purity; Section 9
fills their full negativity interval. Substituting the parameters of
(5.4) and (8.4) in (10.2) proves all the intervening rank claims. No
division by a zero parameter or strict-positivity assumption is needed.
$\square$

## 11. Matched-source observations and conditional operational interpretation

### 11.1 Exact populations, both marginals and the original Q

**命题 11.1（The same source realizes every coordinate and every fixed readout）。**
Every state $\Gamma(X)$ in (2.1), including every endpoint and every state
on the interval paths, satisfies

$$
\begin{aligned}
\langle s,u|\Gamma(X)|s,u\rangle
 &=\tfrac15\mathbf1_{\{u=f(s)\}},\\
\operatorname{Tr}_2\Gamma(X)&=\operatorname{Tr}_1\Gamma(X)=I_5/5.
\end{aligned}
\tag{11.1}
$$

For the original normalized vector and effect

$$
|\Omega\rangle=\tfrac12(e_0+e_{13}-e_1-e_3),\qquad
Q=|\Omega\rangle\langle\Omega|,
$$

one has

$$
\operatorname{tr}(Q\Gamma(X))=\frac15,
\qquad \operatorname{tr}\bigl(Q(\Gamma(X)-I_{25}/25)\bigr)=\frac4{25}.
\tag{11.2}
$$

Proof. The zero skew diagonal gives $C_{ss}=1/5$, proving every one of the
$25$ populations. The partial traces of a matching matrix unit are

$$
\begin{aligned}
\operatorname{Tr}_2(|e_s\rangle\langle e_a|)
 &=\langle f(a)|f(s)\rangle\,|s\rangle\langle a|,\\
\operatorname{Tr}_1(|e_s\rangle\langle e_a|)
 &=\langle a|s\rangle\,|f(s)\rangle\langle f(a)|.
\end{aligned}
$$

The permutation $f$ kills every off-diagonal term in either partial trace;
the diagonal terms give $I_5/5$ on each side. The compressed real vector is

$$
q=J^\dagger\Omega=(1,-1,0,-1,1)^T/2,\qquad q^Tq=1.
$$

Since $q^TXq=(q^TXq)^T=q^TX^Tq=-q^TXq$, its value is zero. Therefore
$q^TCq=1/5$, proving the first equality of (11.2). The rank-one normalized
$Q$ has expectation $1/25$ on $I_{25}/25$, proving the second. The same
calculation holds for every legal $X$, so none of the constructions changes
these fixed readouts. $\square$

In particular each marginal has purity $1/5$ throughout. If
$P_{\mathrm b}=I_5-|2\rangle\langle2|$ is the inherited bottom-face
projection, each marginal has bottom mass $4/5$ and normalized bottom state
$I_4/4$. The joint bottom mass is also $4/5$: exactly the four matched
vectors with $s\ne2$ lie in the joint bottom space. This is a correlated
source; the independent product of the two marginals would instead give
joint bottom mass $16/25$. These statements follow directly from (11.1)
and do not alter the original split used for negativity.

### 11.2 The exact inherited local-menu contract

**假设 11.2（Fixed C-108 local access, conditional on its suppliers）。** On each
of the two original factors use the fixed walk operator $K$, waits
$U(t)=e^{-itK}$ with $t\ge0$, complete five-result rank-one Lüders readings,
and Stop from C-108.1. The ordered identification on each side is

| Original label | $0$ | $1$ | $2$ | $3$ | $13$ |
| --- | --- | --- | --- | --- | --- |
| Walk label | $N$ | $2$ | $3$ | $5$ | $25$ |

The conditional two-sided interface permits $U(t)\otimes I$,
$I\otimes U(u)$ with separately chosen nonnegative waits, complete local
readings, and subsequent local choices based on retained classical records
from both sides. After a local Stop that side is not acted on. Every
strategy has finite depth, and the comparison includes all finite depths.
The input-independent random control resources, strategy and record rule
are identical for compared inputs. Complete histories retain both sides'
outcomes, actions and stops; event grouping is classical postprocessing.
Denote these strategies by $\mathcal M_{\mathrm{loc}}$ and their laws by
$P_\Gamma^\pi$.

The passive-frame interface inherited from C-108.2 is the following:

$$
D_\phi=\operatorname{diag}(1,i,i,i,1),\qquad
D_\phi^\dagger U(t)D_\phi\text{ is real orthogonal},
\tag{11.3}
$$

the complete reading branches in this frame are real coordinate projections,
and the real span of the single-side actual effects is
$D_\phi\operatorname{Sym}_5(\mathbb R)D_\phi^\dagger$.
These facts about the fixed $K$ and available effects are inherited
assumptions here. Their unprovided nested suppliers are not independently
verified. The passive matrix $D_\phi$ and the spanning argument do not grant
a phase control, a derivative measurement or the execution of every matrix
in a real linear span.

Access is to two local factors of the same possibly correlated $\Gamma$;
it does not require $\Gamma=\rho_1\otimes\rho_2$. It does not follow merely
from single-system state preparation or a native tree-memory contract, and
grants no arbitrary unitary, reset, source copy, swap instrument, quantum
side information or hidden Kraus record. Different settings are defined on
the same matrix $\Gamma$; realizing their laws by sampling a common stable
source is an additional preparation requirement.

**定理 11.3（All finite histories and the complete invisible fiber, conditionally）。**
Under Assumption 11.2, every state in (2.1) obeys

$$
P_{\Gamma(X)}^\pi=P_S^\pi\qquad\text{for every }\pi\in\mathcal M_{\mathrm{loc}}.
\tag{11.4}
$$

Conversely, among all complex density states with populations (2.3), equality
of all these laws with those of $S$ forces membership in (2.1). Thus the
matrix theorem concerns the entire fiber under this interface. On the
twenty-dimensional zero-diagonal Hermitian direction space, the menu has
rank ten and kernel $i\operatorname{Skew}_5(\mathbb R)$ of dimension ten.
With the original $Q$ constraint already known, its rank is nine on the
nineteen-dimensional constrained direction space, with the same kernel.

Proof. Define

$$
\eta_s=(D_\phi)_{ss}(D_\phi)_{f(s)f(s)},\qquad
(\eta_0,\eta_1,\eta_2,\eta_3,\eta_{13})=(1,-1,-1,-1,1),\qquad
Z=\operatorname{diag}(\eta_s).
$$

Direct multiplication gives $(D_\phi\otimes D_\phi)J=JZ$.
Fix a random control seed and a complete adaptive history. Every chosen
local action is now fixed. Operators on different factors commute, so its
branch Kraus operator factors as

$$
M_h^{(1)}\otimes M_h^{(2)},\qquad
M_h^{(j)}=D_\phi L_h^{(j)}D_\phi^\dagger,
\qquad L_h^{(j)}\text{ real}.
$$

Each $L_h^{(j)}$ is the ordered product of the real waits and reading
branches on that side. The empty product for an unread side is the
identity. Hence each complete branch effect is

$$
D_\phi H D_\phi^\dagger\otimes D_\phi L D_\phi^\dagger,
\qquad H,L\text{ real symmetric and positive semidefinite}.
$$

Its compressed matrix has entries

$$
\left[J^\dagger(D_\phi HD_\phi^\dagger\otimes
 D_\phi LD_\phi^\dagger)J\right]_{sa}
 =\eta_s\eta_aH_{sa}L_{f(s)f(a)},
\tag{11.5}
$$

which are real symmetric. For any real symmetric matrix $B_0$ and real skew
$X$,

$$
\operatorname{tr}(XB_0)
 =\operatorname{tr}((XB_0)^T)
 =-\operatorname{tr}(B_0X)=-\operatorname{tr}(XB_0)=0.
\tag{11.6}
$$

The last equality uses characteristic zero. Thus the difference of each
branch probability is $i\operatorname{tr}(XB_0)/5=0$. Nonnegative sums
over events and integration over the same input-independent random seed
preserve this equality. Unnormalized branch probabilities handle zero
probability records without conditioning on them. This proves (11.4),
including the stated random and adaptive closure.

For the converse, independently preselected allowed single-side protocols
can be run on the two sides. Their product effects have a real span containing
the tensor product of the two single-side effect spans. In (11.5), choosing
real symmetric representatives
$H=E_{ss}$, $L=E_{f(s)f(s)}$ gives $E_{ss}$. For $s\ne a$, choosing

$$
H=E_{sa}+E_{as},\qquad
L=E_{f(s)f(a)}+E_{f(a)f(s)}
$$

gives $\eta_s\eta_a(E_{sa}+E_{as})$. Each representative is a finite real
linear combination of actual local effects by the inherited span contract;
their products are consequently finite real linear combinations of actual
product effects. These matrices span all of $\operatorname{Sym}_5(\mathbb R)$.
Equality of actual laws therefore forces the real parts of every off-diagonal
entry of $C-I_5/5$ to vanish. The diagonal is already zero by (2.3).
Lemma 2.3 now gives exactly (2.1).

There are ten complex off-diagonal pairs, hence twenty real directions;
the menu retains exactly their ten real parts and kills their ten imaginary
parts. Small multiples of every such Hermitian direction are legal since
$I_5/5$ is positive definite on the matching support. This is not a count
of purely illegal perturbations. The original $Q$ is real symmetric after
compression and gives the nonzero real constraint

$$
\ell_Q(Y)=\frac12\left(
\operatorname{Re}Y_{0,13}+\operatorname{Re}Y_{1,3}
-\operatorname{Re}Y_{0,1}-\operatorname{Re}Y_{0,3}
-\operatorname{Re}Y_{1,13}-\operatorname{Re}Y_{3,13}\right).
\tag{11.7}
$$

For instance $Y=E_{0,13}+E_{13,0}$ gives $\ell_Q(Y)=1/2$.
Knowing this constraint removes one visible real direction and no imaginary
one, proving the rank-nine assertion. These rank and fiber statements are
the inherited C-108 conclusions under its interface. $\square$

### 11.3 The same fixed fourteen-flag port on the same correlated source

**假设 11.4（The fixed C-108.6 port, conditional on its supplier）。** Retain
exactly the inherited flag set and weights

$$
\begin{aligned}
F_{14}&=\{(\mathrm A,k,\ell):0\le k,\ell<3\}
 \sqcup\{(\mathrm B,k):0\le k<5\},\\
c_{\mathrm A,k,\ell}&=10/27,\qquad c_{\mathrm B,k}=1/3.
\end{aligned}
$$

Its fixed vectors have the inherited properties

$$
v_\nu\in\mathbb R^5,\qquad \|v_\nu\|=1,\qquad
P_\nu=v_\nu v_\nu^T,\qquad \sum_\nu c_\nu P_\nu=I_5.
\tag{11.8}
$$

They are the specified vectors of C-108.6, with its QFA coefficients and
rotation planes; none is replaced or optimized here. Their unprovided
nested definitions and normalization certificate are not independently
verified. The conditional statement uses precisely (11.8) for those fixed
data. Put

$$
\begin{aligned}
R_\nu&=D_\phi P_\nu D_\phi^\dagger,\qquad E_\nu=c_\nu R_\nu,\\
\widetilde T(Y)&=\sum_{\nu\in F_{14}}\operatorname{tr}(E_\nu Y)R_\nu.
\end{aligned}
\tag{11.9}
$$

Under (11.8) this is the specified normalized rank-one measure-and-prepare
channel. Indeed its Kraus operators $K_\nu=\sqrt{c_\nu}R_\nu$ satisfy
$\sum_\nu K_\nu^\dagger K_\nu=\sum_\nu E_\nu=I_5$, and the rank-one identity
$R_\nu YR_\nu=\operatorname{tr}(R_\nu Y)R_\nu$ gives (11.9).

**定理 11.5（Equal joint flag law and equal separable erased output, conditionally）。**
Under Assumption 11.4, for every legal $X$ and every one of the fixed
$14\times14$ flag pairs,

$$
\begin{aligned}
p_{\nu\mu}(X)
 &=\operatorname{tr}((E_\nu\otimes E_\mu)\Gamma(X))\\
 &=\frac{c_\nu c_\mu}{5}\sum_{s\in B}
       v_\nu(s)^2v_\mu(f(s))^2
 =p_{\nu\mu}(0).
\end{aligned}
\tag{11.10}
$$

The same correlated input therefore obeys

$$
\begin{aligned}
(\widetilde T\otimes\widetilde T)(\Gamma(X))
 &=(\widetilde T\otimes\widetilde T)(S)\\
 &=\sum_{\nu,\mu}p_{\nu\mu}(0)R_\nu\otimes R_\mu\\
 &=\frac15\sum_{s\in B}
 \widetilde T(|s\rangle\langle s|)\otimes
 \widetilde T(|f(s)\rangle\langle f(s)|).
\end{aligned}
\tag{11.11}
$$

This common output is separable on the original split.

Proof. For one fixed pair put $r_s=v_\nu(s)v_\mu(f(s))\in\mathbb R$ and
$Z=\operatorname{diag}(1,-1,-1,-1,1)$. Directly
$(D_\phi\otimes D_\phi)J=JZ$, so the same joint source gives

$$
\begin{aligned}
p_{\nu\mu}(X)
 &=\frac{c_\nu c_\mu}{5}\,r^TZ(I_5+iX)Zr\\
 &=\frac{c_\nu c_\mu}{5}
   \left(\sum_sr_s^2+i\,r^TZXZr\right)\\
 &=\frac{c_\nu c_\mu}{5}\sum_sr_s^2.
\end{aligned}
$$

The matrix $ZXZ$ is real skew; its diagonal terms vanish and its opposite
off-diagonal terms cancel in this quadratic form. This proves (11.10) for
each actual flag pair. These probabilities are nonnegative, and (11.8) gives

$$
\sum_{\nu,\mu}p_{\nu\mu}(X)
 =\frac15\sum_s
 \left(\sum_\nu c_\nu v_\nu(s)^2\right)
 \left(\sum_\mu c_\mu v_\mu(f(s))^2\right)
 =\frac15\sum_s1=1.
$$

Applying the two local measure-and-prepare channels to a general correlated
input uses these joint Born probabilities, so it yields the middle sum of
(11.11). Each $R_\nu$ is a normalized pure state; this is an explicit convex
combination of normalized product states and is separable. Expanding the
middle sum first in $s$ gives the last line of (11.11), which is also the
direct channel image of $S$. No product of marginal input probabilities
has replaced the joint source probability. $\square$

This proves a containment of the stated invisible fiber in a channel fiber.
It does not classify every input of that channel fiber, change the port,
or turn a single-system attained history error into a correlated-input
uniform error, a diamond distance or an unconstrained minimax value.

## 12. What the optimization does and does not operationally determine

**推论 12.1（Identical inherited records do not determine the source coordinates）。**
Under the corresponding conditional interfaces of Section 11, the full
actual-menu history laws, even with the complete fixed joint flag law,
cannot determine original-source purity, negativity or separability within
$\mathfrak I$.

Proof. All states in $\mathfrak I$ have the same such laws by Theorems 11.3
and 11.5. At $s=0$, the state $S$ is separable with $p=1/5$ and
$\mathcal N=0$. At any $s>0$, the lower construction is entangled with
$p>1/5$ and $\mathcal N>0$. These already give unequal answers for the same
record laws. The exact region gives the stronger statement that every
permitted purity and every negativity in its full fixed-purity interval
occurs among states with those same laws. A function of identical data
cannot return all these different values correctly. $\square$

Equal histories or equal erased outputs do not assert equality of the input
density matrices. The formulas in this volume describe mathematical source
properties; the inherited menu provides no purity or negativity measurement.
A new distinguishing procedure requires an explicitly allowed readout and
the appropriate same-source assumptions.

**命题 12.2（Independent whole-source copies are a separate interface）。** If
one additionally supplies an actual input
$\Gamma_{AB}\otimes\Gamma_{A'B'}$ with identical independent whole-source
copies and permits the whole-copy swap $W$ with its spectral instrument,
then $\operatorname{tr}(W(\Gamma\otimes\Gamma))=p$. This statement concerns
the four factors $A,B,A',B'$ with $A=H^{(1)}$, $B=H^{(2)}$; it does not
change the original $A\mid B$ split of the negativity. Equal whole-source
marginals alone do not imply the swap identity.

Proof. Define $W|a,b,a',b'\rangle=|a',b',a,b\rangle$. For any two matrices
$G,H$ on the original $25$-dimensional space, a basis expansion gives

$$
\operatorname{tr}(W(G\otimes H))
 =\sum_{u,v}G_{vu}H_{uv}=\operatorname{tr}(GH).
$$

Taking $G=H=\Gamma$ gives the conditional identity. To see the failure of
equal marginals as a substitute, take the positive trace-one state

$$
\Xi=\frac15\sum_{s\in B}
 |e_s\rangle\langle e_s|_{AB}\otimes
 |e_s\rangle\langle e_s|_{A'B'}.
$$

Both whole-source marginals are $S$, by taking either partial trace.
Each vector $e_s\otimes e_s$ has swap eigenvalue $+1$, so
$\operatorname{tr}(W\Xi)=1$, whereas $\operatorname{tr}S^2=1/5$.
Thus the actual tensor-square input is essential. This reuses the C-107
source-copy boundary; it supplies no new copy or instrument permission.
$\square$

The menu and port in Section 11 grant none of the extra resources in
Proposition 12.2. Independent re-preparation is a source contract, and the
mathematical expression $\Gamma\otimes\Gamma$ is not a cloning operation
on one unknown input. Neither the state matrices nor the orthogonal path
give physical preparation, local phase references, free controls, physical
storage, empirical learning or a cost advantage. No setting count, sample
complexity, native waiting cost or instrument equivalence follows from
the two-coordinate optimization.

## 13. Attribution and exact limits of the result

| Source or result | Scope and ownership |
| --- | --- |
| Inherited C-106 | Exact matched support and maximally correlated partial-transpose blocks; its PPT argument is a necessary-condition argument, not general $5\times5$ PPT sufficiency. Its source attributes the mechanisms to Peres and Rains. |
| Inherited C-107 | Whole-source purity identity, the separate original and whole-copy tensor splits, and the independent-copy swap requirement. |
| Inherited C-108 | Legal invisible skew class, purity interval $[1/5,9/25]$, equal-two-block purity attainers, and conditional all-history and fixed fourteen-flag erasure interfaces. |
| Additional `repo-derived` deductions here | Sharp capped-entry lower frontier with equality patterns; determinant/parity sign obstruction; universal two-branch upper frontier; dense simultaneous upper attainers; both exact crossovers; maximum and maximizer purity/rank; fixed-purity interval filling and the full joint region. |

This attribution compares the additional deductions only with the supplied
C-106–C-108 text, which leaves negativity unoptimized. It does not establish
literature-wide novelty. External primary citations and unprovided nested
mathematical suppliers are not independently verified here; the ordinary
matrix proofs above carry the optimization without relying on such a claim.

There is no deferred mathematical step in the exact optimization over
(2.1): universal inequalities, legal common-state endpoints, all interval
values, crossover obstruction and all asserted ranks are proved in the
volume. Formal kernel verification is not supplied. The operational
identification remains conditional on the precisely stated fixed menu and
fixed-port interfaces; their physical realization remains unestablished.

The theorem does not cover arbitrary population fibers, invisible directions
with nonzero real part, leakage, approximate population zeros, finite-sample
frequencies, different menus, arbitrary bipartite states or a different
tensor split. Exact zero populations are essential to the support argument;
zero observed counts do not establish them. Conditional equal histories
are statements about exact source laws, not a finite-data test. Extensions
to these settings require new assumptions and proofs. This bounded result
does not settle a broader research program or its physical applications.

## 追加锚（本行以下为增补区）
