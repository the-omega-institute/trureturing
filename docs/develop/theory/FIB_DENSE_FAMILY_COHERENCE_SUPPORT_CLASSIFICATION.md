# FIB dense family: partial fixed-basis coherence-support classification

This volume gives a partial pointwise classification for the same actual dense
two-parameter matrix family in the ordered basis $(0,1,2,3,13)$. It settles
support one and two on the entire legal rectangle, both outer-edge transitions
between support three and four, and a sufficient polygon of finite
three-support realizations. The exact unclassified set $U$ is in Section 9;
the whole-family classification remains open there.

The evidence is ordinary finite-dimensional proof. This is a theory reference
source, not a Lean/kernel certificate. Its additional deductions have status
$\texttt{repo-derived}$ relative to the canonical sources named below; no
literature-wide originality claim is made. The volume uses the numbered
generic-v1 source skeleton.

## 1. Fixed object, evidence, and ingredient ownership

**定义 1.1（Original coordinates and matching）。** Write $e_1,\ldots,e_5$ for
positions in the ordered orthonormal basis $B=(0,1,2,3,13)$, and put
$m_j=e_{j+2}$ for $j=0,1,2$, read modulo three. Positions $1,5$ are called the
outers; positions $2,3,4$ are the middles. For the original factors
$H^{(1)}=H^{(2)}=\mathbb C^5$, define

$$
f(0)=13,\quad f(13)=0,\quad f(1)=3,\quad f(3)=1,\quad f(2)=2,
\qquad J|r\rangle=|r,f(r)\rangle.
\tag{1.1}
$$

Thus $J^\dagger J=I_5$. Every Schmidt-number interpretation uses the original
split $H^{(1)}\mid H^{(2)}$, with no independent copies substituted for these
factors.

**定义 1.2（The same actual dense family）。** For real $s,t$, let

$$
F(s,t)=
\begin{pmatrix}
0&s&s&s&s\\
-s&0&t&-t&s\\
-s&-t&0&t&s\\
-s&t&-t&0&s\\
-s&-s&-s&-s&0
\end{pmatrix},
\qquad
M(s,t)=I_5+iF(s,t),\qquad C(s,t)=\frac{M(s,t)}5.
\tag{1.2}
$$

Set

$$
A=\frac1{\sqrt7},\qquad B_0=\frac1{\sqrt3},\qquad
\mathcal R=[-A,A]\times[-B_0,B_0],
\qquad \Gamma(s,t)=JC(s,t)J^\dagger.
\tag{1.3}
$$

The symbol $B_0$ is a scalar bound and is distinct from the ordered basis $B$.
No sign, axis, rank, strict-positivity, or unequal-eigenvalue restriction is
imposed.

**定义 1.3（All finite complex competitors）。** For nonzero $C\succeq0$ define

$$
k(C)=\min\left\{
\max_{1\le\ell\le N}|\operatorname{supp}_B z_\ell|:
C=\sum_{\ell=1}^N z_\ell z_\ell^\dagger,\quad
1\le N<\infty,\quad z_\ell\in\mathbb C^5\setminus\{0\}
\right\}.
\tag{1.4}
$$

All finite lengths, arbitrary norms, complex phases, overlapping supports and support
patterns are allowed. Positive coefficients are absorbed into the vectors.
The spectral theorem ensures that the set of decompositions is nonempty, so
the minimum is an integer. Positive scalar multiplication leaves $k$
unchanged by scaling every vector. Unless a normalization is explicitly built
in, the lists below realize $M$; division of every vector by $\sqrt5$ realizes
the actual $C$. Zero slots are removed. Equality of Gram sums with $M$ gives
total squared norm five, and the normalized $C$ lists consequently have total
squared norm one.

**约定 1.4（Canonical source ownership and bounded novelty）。** The following
ownership fixes the scope of the results.

| Source | Ingredients used and scope |
| --- | --- |
| [Sharp purity–negativity attainable region](FIB_INVISIBLE_FIBER_PURITY_NEGATIVITY_ATTAINABLE_REGION.md), Sections 4, 8, 10 | Owns this seven-plus-three $F$ family, its two perpendicular active planes, spectrum, legal rectangle, purity and original-split negativity formulas, sharp attainable region and dense negativity maximizer. |
| [Sharp fixed-basis coherence number](FIB_INVISIBLE_FIBER_SHARP_COHERENCE_NUMBER.md), Sections 3–5 | Owns the explicit finite coordinate-cancellation upper construction for the entire skew fiber, its maximum-four attainer, and the positive-on-three-coordinate-subspaces witness. |
| [Mixed-state capacity and certification](AURIC_FIB_ATOM_HIDDEN_RELATIONS_MIXED_STATE_CAPACITY_AND_CERTIFICATION.md), C-106–C-110 | Owns matched support and tensor split, the invisible real-skew fiber, conditional actual-menu/erasure interfaces, finite complex coherence definition, edge/triangle examples, fixed-Schur-channel resource dictionary, and its necessary error/leakage relations. |
| The same capacity source, latest C-111.1–C-111.7 | Already owns the whole-fiber maximum four and its separate Fourier-coordinate four-support attainer, five-vector realization, and same-spectrum maximal-purity examples with resources two and four. The whole-fiber maximum is already settled. |
| This volume, Theorems 3.1, 4.1, and 5.2 | Supplies the support-two criterion, both edge kernel/budget arguments, and the matching sparse lists proved in full below. |

The main additional family-specific results are Theorem 3.1 and the two edge
thresholds, Theorems 4.1 and 5.2. Support one is a supporting consequence of the
definition. The polygon is a constructive convexity consequence of the edge
lists. Immediate substitution in the inherited witness gives an inherited
exclusion and adds no mechanism. Neither the generic coherence framework nor
the whole-fiber maximum is newly claimed. The deductions use the canonical
sources above and the explicit proofs in this volume; they make no claim about
external citations or nested operational suppliers.

## 2. Legality, sign transport, and spectral boundary cases

**引理 2.1（Exact closed rectangle and spectrum）。** The matrix $M(s,t)$ is
positive semidefinite exactly on $\mathcal R$. On that rectangle, putting
$a=|s|$, $b=|t|$, its compressed spectrum is

$$
\operatorname{spec} C(s,t)=
\left\{\frac{1+\sqrt7a}{5},\frac{1-\sqrt7a}{5},
\frac{1+\sqrt3b}{5},\frac{1-\sqrt3b}{5},\frac15\right\}.
\tag{2.1}
$$

Proof. Write $G=F(1,0)$, $K=F(0,1)$ and

$$
r=(1,0,0,0,-1)^{\mathsf T},\qquad
h=(1/2,1,1,1,1/2)^{\mathsf T}.
$$

The formula $G=rh^{\mathsf T}-hr^{\mathsf T}$ produces precisely its seven
nonzero upper entries. The vectors are orthogonal, with squared norms $2$
and $7/2$; moreover $Gr=-2h$, $Gh=(7/2)r$, and $G$ kills the perpendicular
complement of their plane. In its normalized real basis the skew block has
off-diagonal magnitudes $\sqrt7$. The matrix $K$ is zero outside the middle
triple, where its block is

$$
K_3=
\begin{pmatrix}0&1&-1\\-1&0&1\\1&-1&0\end{pmatrix},
\qquad K_3\mathbf1=0,\qquad K_3^2=\mathbf1\mathbf1^{\mathsf T}-3I_3.
\tag{2.2}
$$

It acts as a skew block of magnitude $\sqrt3$ on the real middle plane of
coordinate sum zero and kills its complement. That plane is perpendicular
to both $r,h$. Thus $sG+tK$ acts on two perpendicular planes with magnitudes
$\sqrt7|s|,\sqrt3|t|$, and is zero on the remaining line. Multiplication by
$i$ gives opposite Hermitian eigenvalues on each plane. Adding the identity
and dividing by five proves (2.1) and the necessary and sufficient closed
bounds in (1.3). No division by $s,t$ or by a spectral gap is used. At an axis,
the corresponding pair in (2.1) repeats $1/5$; equal nonzero magnitudes also
permit repeated eigenvalues. One zero eigenvalue of $C$ occurs for each
saturated outer bound, so the corner has rank three. The skew diagonal is
zero, hence $C_{ii}=1/5$ and $\operatorname{tr}C=1$. $\square$

**引理 2.2（Signed transport in the original coordinates）。** The value
$k(C(s,t))$ depends only on $a=|s|,b=|t|$. Every list and exclusion for
$(a,b)$ transfers to the corresponding signed point.

Proof. Let $P$ exchange $e_1,e_5$ and let $R$ exchange any two middle
coordinates. The outer-middle entries are constant across the middles, while
a middle reflection reverses the skew cycle. Inspecting (1.2) gives

$$
P F(s,t)P^{\mathsf T}=F(-s,t),\qquad
R F(s,t)R^{\mathsf T}=F(s,-t).
\tag{2.3}
$$

Both fix the identity and commute with each other. A permutation sends a
finite complex Gram sum to the Gram sum of the permuted vectors, preserves
the number of nonzero original coordinates, and has the inverse
permutation. This is a bijection of the entire competitor domains. If a
parameter is zero either choice of its sign transport gives the same matrix.
These maps construct vectors in the fixed original coordinates; they grant
no physically available permutation or new basis for measuring support.
$\square$

For orientation, the inherited family formulas are
$p=\operatorname{tr}\Gamma^2=(5+14a^2+6b^2)/25$ and
$\mathcal N=(7a+3b)/5$. They are not extra classification premises. The first
follows by squaring (2.1). For the second, partial transpose on the original
second factor places each off-diagonal $C_{ij}$ in an orthogonal block
$\left(\begin{smallmatrix}0&C_{ij}\\\bar C_{ij}&0\end{smallmatrix}\right)$
with eigenvalues $\pm|C_{ij}|$, and leaves five diagonal blocks $1/5$.
The ten two-dimensional blocks and five singletons exhaust dimension
twenty-five. Its trace norm is $1+2\sum_{i<j}|C_{ij}|$, giving the stated
negativity. This explains the parameter correspondence with the
sharp-negativity owner without re-optimizing its result.

## 3. The entire-rectangle support-two criterion

**定理 3.1（Exact support one and two, with a finite converse）。** For every
legal $(s,t)$, let $a=|s|$, $b=|t|$. Then

$$
k(C(s,t))=1\quad\Longleftrightarrow\quad a=b=0,
\tag{3.1}
$$

and

$$
k(C(s,t))\le2
\quad\Longleftrightarrow\quad
6a^2\le(1-a)(1-2b).
\tag{3.2}
$$

Every nonzero point satisfying (3.2) has exact value two; every point
violating it has value at least three.

Proof. A one-support Gram sum is diagonal, whereas (1.2) has a nonzero
off-diagonal entry whenever $a$ or $b$ is nonzero. At the origin the five
coordinate vectors realize $M=I_5$. This proves (3.1).

Suppose $M(a,b)=\sum_\ell z_\ell z_\ell^\dagger$ with all supports at most
two. For any nonnegative real weights $w_i$, triangle inequality gives

$$
2\sum_{i<j}w_iw_j|M_{ij}|
\le \sum_\ell 2\sum_{i<j}w_iw_j|(z_\ell)_i||(z_\ell)_j|
\le \sum_\ell\sum_i w_i^2|(z_\ell)_i|^2
=\sum_iw_i^2.
\tag{3.3}
$$

In the second step each term has at most one nonzero unordered pair and
uses $2xy\le x^2+y^2$; a singleton term satisfies the same inequality. Thus
this bound covers every complex phase and every finite length. Give both
outers weight $x\ge0$ and all middles weight $y\ge0$. The one outer edge,
six outer-middle edges and three middle edges yield

$$
2(1-a)x^2+3(1-2b)y^2-12axy\ge0\qquad(x,y\ge0).
\tag{3.4}
$$

Taking $x=0$ excludes $b>1/2$. At $b=1/2$, any $a>0$ is excluded by a fixed
positive $x$ and arbitrarily large $y$. If $b<1/2$ and $a>0$, use
$x=1,y=2a/(1-2b)$; (3.4) becomes
$2(1-a)-12a^2/(1-2b)\ge0$. At $a=0$, the necessary condition is just
$b\le1/2$. Since $1-a>0$ on the entire rectangle, these cases give exactly
(3.2), including the equality cases.

For sufficiency with $a>0$, (3.2) forces $b<1/2$. Set

$$
\rho=\frac{2a}{1-2b}>0,\qquad
w_1=w_5=1,\quad w_2=w_3=w_4=\rho,\qquad X=F(a,b).
$$

For each nonzero upper entry $X_{ij}$ take

$$
v_{ij}=\sqrt{|X_{ij}|\,w_j/w_i}\,e_i
-i\operatorname{sgn}(X_{ij})\sqrt{|X_{ij}|\,w_i/w_j}\,e_j.
\tag{3.5}
$$

The $(i,j)$ entry of its outer product is exactly $iX_{ij}$; no other pair
is affected. At a middle coordinate its incident edges contribute
$2a/\rho+2b=1$ to the diagonal. At either outer they contribute
$a+3a\rho$. Add

$$
\sqrt{1-a-3a\rho}\,e_1,\qquad
\sqrt{1-a-3a\rho}\,e_5.
\tag{3.6}
$$

Their radicand equals $1-a-6a^2/(1-2b)\ge0$ by (3.2). Hence all diagonals
and all off-diagonals of the finite sum equal those of $M(a,b)$.

For $a=0$ and $0\le b\le1/2$, use $e_1,e_5$, the three vectors
$\sqrt b(m_j-i m_{j+1})$, and the three vectors
$\sqrt{1-2b}\,m_j$. Each middle diagonal is $2b+1-2b=1$, and each oriented
cyclic edge is $ib$, exactly as in (2.2). This includes $b=0$ and $b=1/2$.
All displayed supports are at most two. Divide by $\sqrt5$, remove zero
slots, and use Lemma 2.2 to restore the actual signs. A useful consequence
of (3.2) is

$$
6a^2\le1-a,\qquad (3a-1)(2a+1)\le0,\qquad a\le1/3.
\tag{3.7}
$$

This will exclude support two everywhere on the vertical outer edge.
$\square$

## 4. The horizontal outer edge: kernel energy and a matching list

On the original middle triple define

$$
\omega=\frac{-1+i\sqrt3}{2},\qquad
u=\frac{(1,1,1)}{\sqrt3},\quad
v=\frac{(1,\bar\omega,\omega)}{\sqrt3},\quad
n=\frac{(1,\omega,\bar\omega)}{\sqrt3}.
\tag{4.1}
$$

The equations $1+\omega+\bar\omega=0$, $|\omega|=1$ make them orthonormal.
Multiplication by $K_3$ gives
$K_3u=0$, $K_3v=-i\sqrt3v$, $K_3n=i\sqrt3n$. Consequently

$$
I_3+iB_0K_3=uu^\dagger+2vv^\dagger,\qquad
(I_3+iB_0K_3)n=0.
\tag{4.2}
$$

The full $M(a,B_0)$ also kills the embedded $(0,n,0)$: its outer-middle
rows are constant and the coordinates of $n$ sum to zero. For each cyclic
$j$ put

$$
w_j=\frac{m_j-\omega m_{j+1}}{1-\omega}.
\tag{4.3}
$$

Since $|1-\omega|^2=3$,

$$
\sum_jw_j=\sqrt3u,\qquad
\sum_jw_jw_j^\dagger=uu^\dagger+vv^\dagger.
\tag{4.4}
$$

For the second identity, its diagonals are $2/3$ and its oriented cyclic
entries are $-\bar\omega/3=(1+\omega)/3$, exactly those of the two
projections. The first identity follows by collecting each middle
coordinate's coefficient $(1-\omega)/(1-\omega)=1$.

**定理 4.1（Exact horizontal outer-edge transition）。** For $0\le a\le A$,

$$
k(C(a,B_0))=
\begin{cases}
3,&0\le a\le1/3,\\
4,&1/3<a\le A.
\end{cases}
\tag{4.5}
$$

Both signs of each parameter are covered by Lemma 2.2.

Proof. First construct $M(a,B_0)$ for $a\le1/3$. Put

$$
d=1-a,\qquad c=\frac{3a^2}{d},\qquad g=\sqrt{d/3}.
$$

Here $d>0$, $g\sqrt c=a$, and $c\le1/2$ is equivalent to
$6a^2\le1-a$, which holds precisely for $0\le a\le1/3$. Take

$$
\sqrt a(e_1-i e_5),
\quad
g e_1-i\sqrt c\,w_j,\quad g e_5+i\sqrt c\,w_j\quad(j=0,1,2),
\quad
\sqrt{1-2c}\,u,\quad \sqrt{2-2c}\,v.
\tag{4.6}
$$

The six mixed terms have outer diagonals $3g^2=d$, no outer-pair entry,
and middle block $2c(uu^\dagger+vv^\dagger)$. Equation (4.4) makes each
first-outer/middle entry $ig\sqrt c=ia$ and each last-outer/middle entry
$-ia$. The outer-pair vector adds outer diagonals $a$ and entry $ia$ at
$(1,5)$. The last two vectors add
$(1-2c)uu^\dagger+(2-2c)vv^\dagger$, giving (4.2). This verifies every
entry of $M(a,B_0)$. All nine slots have original support at most three,
and all radicands are nonnegative. At $a=0$ the zero slots disappear; at
$a=1/3$ the coefficient $1-2c$ is zero. Divide by $\sqrt5$ for $C$.

For necessity let any finite at-most-three-support decomposition of
$M(a,B_0)$ be given. Its kernel vector implies

$$
0=\sum_\ell|n^\dagger(z_\ell)_{\rm mid}|^2,
$$

so every term's middle part is perpendicular to $n$. A vector with both
outers could use at most one middle; because every coordinate of $n$ is
nonzero, that middle must vanish. Group terms into $E_{15}$ using both
outers, $E_1$ using only outer 1, $E_5$ using only outer 5, and middle-only
terms. This partitions actual nonzero supports without assumptions on phases.
Let

$$
o_i=\sum_{E_{15}}|(z_\ell)_i|^2,\quad
d_i=\sum_{E_i}|(z_\ell)_i|^2=1-o_i,\quad
c_i=\sum_{E_i}|u^\dagger(z_\ell)_{\rm mid}|^2
\qquad(i=1,5).
$$

Only $E_{15}$ contributes the outer entry $ia$. Complex Cauchy–Schwarz gives
$o_1o_5\ge a^2$, so $o_1+o_5\ge2a$ and
$d_1+d_5\le2(1-a)$. The total middle $u$-energy is one by (4.2), giving
$c_1+c_5\le1$. Only $E_i$ contributes the corresponding outer-to-$u$ entry,
whose magnitude is $\sqrt3a$, and hence $d_ic_i\ge3a^2$. Therefore

$$
12a^2\le(\sqrt{d_1c_1}+\sqrt{d_5c_5})^2
\le(d_1+d_5)(c_1+c_5)\le2(1-a).
\tag{4.7}
$$

No division by a possibly zero budget occurs. Factoring as in (3.7) forces
$a\le1/3$, excluding every complex finite three-support sum above that
threshold. On the constructed segment, $B_0>1/2$ excludes support two by
Theorem 3.1. Above the threshold Theorem 6.1 below supplies an actual finite
four-support upper list, giving exact value four. $\square$

## 5. The vertical outer edge: zero-sum triples and their budget

On $a=A$, perform only the following diagonal algebraic transport:

$$
d_0=\frac{1+i\sqrt7}{2},\qquad
D=\operatorname{diag}(d_0,1,1,1,\bar d_0),\qquad
L=D M(A,b)D^\dagger.
\tag{5.1}
$$

Here $|d_0|^2=2$, so $D$ is invertible. Put

$$
c_*=-\frac12-\frac{3i}{2\sqrt7},\qquad
h_*=-\frac12+\frac{i}{2\sqrt7},\qquad
\kappa=|c_*|=\frac2{\sqrt7}.
\tag{5.2}
$$

The outer diagonals of $L$ are two, its middle diagonals one, and

$$
L_{15}=iA d_0^2=c_*,
\qquad L_{1j}=iA d_0=h_*,
\qquad L_{5j}=\bar h_*,
\qquad L_{\rm mid}=I_3+ibK_3.
\tag{5.3}
$$

Every row sums to zero since
$2+3h_*+c_*=0$, $2+3\bar h_*+\bar c_*=0$, and
$1+h_*+\bar h_*=0$. Thus $L\mathbf1=0$. Diagonal invertibility means that
$D$ bijects decompositions of $M(A,b)$ and $L$ with each actual coordinate
support unchanged.

**引理 5.1（All-complex zero-sum triple budget）。** A finite three-support
Gram decomposition of $L$ implies

$$
b\le\beta=\frac{4}{3\sqrt3}\left(1-\frac1{\sqrt7}\right).
\tag{5.4}
$$

Proof. In any Gram sum,
$0=\mathbf1^\dagger L\mathbf1=\sum_\ell|\mathbf1^\dagger z_\ell|^2$,
so every vector has coordinate sum zero. Let $Q$ cyclically permute the
middles, and let $\mathcal T$ be complex conjugation followed by exchanging
the outers and reflecting middle indices $j\mapsto-j$. Both fix $L$.
For $\mathcal T$, conjugation reverses $ibK_3$, reflection reverses it back,
and outer exchange restores the conjugated $c_*,h_*$ entries in (5.3).
They preserve supports and the zero-sum equation. The six maps
$Q^j$ and $Q^j\mathcal T$, $j=0,1,2$, form the resulting symmetry group.
Applying each to every vector and dividing the vector by $\sqrt6$ averages
its rank-one matrix, also for an antiunitary map. Their finite sum is still
$L$. We may therefore use a decomposition invariant as a labelled collection
under these six maps, with no loss of a possible complex competitor.

Separate the terms into B-type using both outers, C-type using exactly one
outer, and D-type using none. B-type has at most one middle; C-type at most
two. Assign a containing middle label to pure-outer B terms, and an oriented
cyclic middle pair to smaller C supports. Make these assignments on the
initial list and propagate the labels when forming its six images.
These choices exist for every support of the required size and
do not change any vector. No nonzero singleton can satisfy the zero-sum
condition.

The total B contribution has equal outer diagonals, say $V$, and its outer
edge is $c_*$ because no other group uses both outers. Its PSD compression
$\left(\begin{smallmatrix}V&c_*\\\bar c_*&V\end{smallmatrix}\right)$
forces $V\ge\kappa$. The total C diagonal at each outer is then $U=2-V$.
Thus

$$
0\le U\le2-\kappa.
\tag{5.5}
$$

Cyclic averaging puts one third of the B outer compression at each middle
label. In such a term the middle coordinate is minus the sum of the two
outer coordinates. Consequently B gives each middle diagonal
$(2V+2\operatorname{Re}c_*)/3=(2V-1)/3$, each first-outer/middle entry
$-(V+c_*)/3$, its conjugate at the other outer, and no middle off-diagonal.
This remains true for a pure-outer labelled term because its outer sum is
zero.

Sum the C-type terms with label $(1,m_j,m_{j+1})$. Each resulting block is
PSD, Hermitian and has row sum zero. Solving its row equations gives exactly

$$
A(x,y,z,q)=
\begin{pmatrix}
x+y&-x+iq&-y-iq\\
-x-iq&x+z&-z+iq\\
-y+iq&-z-iq&y+z
\end{pmatrix},
\qquad x,y,z,q\in\mathbb R.
\tag{5.6}
$$

For example the real parts of its first two off-diagonals define $-x,-y$,
their imaginary parts are opposite by the first row equation, and the
remaining equations force the third off-diagonal and the two remaining
diagonals in (5.6). Cyclic invariance makes the three outer-1 blocks identical
in their ordered coordinates. Conjugation and reflection reverse the ordered
middle pair together; the outer-5 partner is $A(y,x,z,q)$, with the same
$q$. Write

$$
S=x+y=U/3\ge0.
$$

Its outer/first-middle principal minor gives

$$
0\le S(x+z)-|-x+iq|^2=xy+Sz-q^2,\qquad
q^2\le S^2/4+Sz.
\tag{5.7}
$$

Here $xy\le(x+y)^2/4$ for any real $x,y$. Adding all six C blocks gives
oriented middle edge $-2z+2iq$, middle diagonal $2S+4z$, and each
outer-to-middle entry $-S$.

The D group is a PSD middle circulant with zero row sum. Its diagonal can
be written $2w$, and its oriented edge $-w+ir$ with $w,r$ real. On
$u,v,n$ from (4.1) its eigenvalues are $0,3w+\sqrt3r,3w-\sqrt3r$.
Thus

$$
w\ge0,\qquad |r|\le\sqrt3\,w.
\tag{5.8}
$$

The target middle edge has real part zero and imaginary part $b$. The B
group has no such edge, so
$w=-2z$, $z\le0$, and $b=2q+r$.

If $S=0$, PSD with zero outer diagonal forces that entire row to vanish
by its two-coordinate principal minors. Hence $x=y=q=0$ in (5.6).
The remaining middle block is
$\left(\begin{smallmatrix}z&-z\\-z&z\end{smallmatrix}\right)\succeq0$,
so $z\ge0$. Together with $z\le0$ this gives $z=w=r=b=0$.
If $S>0$, define $Y=\sqrt{S^2/4+Sz}$. Equation (5.7) makes the radicand
nonnegative and $z\le0$ gives $0\le Y\le S/2$. Therefore

$$
\begin{aligned}
b&\le2|q|+|r|\le2Y-2\sqrt3z\\
&=\frac{2S}{\sqrt3}
-\frac{2\sqrt3}{S}\left(Y-\frac{S}{2\sqrt3}\right)^2
\le\frac{2S}{\sqrt3}.
\end{aligned}
\tag{5.9}
$$

Using $S=U/3$ and (5.5) gives
$b\le2(2-\kappa)/(3\sqrt3)=\beta$. All zero budgets have been treated
without division; the proof covers all finite lengths and complex phases.
$\square$

**定理 5.2（Exact vertical outer-edge transition and thirteen-slot list）。**
For $0\le b\le B_0$,

$$
k(C(A,b))=
\begin{cases}
3,&0\le b\le\beta,\\
4,&\beta<b\le B_0.
\end{cases}
\tag{5.10}
$$

Proof. On the constructive segment put

$$
U=\frac{3\sqrt3b}{2},\qquad S=U/3=\frac{\sqrt3b}{2},\qquad V=2-U,
\qquad
\eta=\frac{c_*}{\kappa}=-\frac{\sqrt7+3i}{4},\qquad
\alpha=-\frac12-\frac{i}{2\sqrt3}.
\tag{5.11}
$$

One has $S\ge0$, $V\ge\kappa$, $|\eta|=1$,
$\alpha+\bar\alpha=-1$, $|\alpha|^2=1/3$, and
$\alpha^2=1/6+i/(2\sqrt3)$. First realize $L$ by the following vectors:

$$
r_{j,\varepsilon}
=\sqrt{\frac{V+\varepsilon\kappa}{6}}\,
[\varepsilon\eta e_1-(1+\varepsilon\eta)m_j+e_5],
\qquad j=0,1,2,\quad\varepsilon=\pm1;
\tag{5.12}
$$

$$
p_{o,j}=\sqrt S[e_o+\alpha m_j+\bar\alpha m_{j+1}],
\qquad o\in\{1,5\},\quad j=0,1,2;
\qquad q_0=\sqrt{2S}\,v.
\tag{5.13}
$$

All thirteen slots have support at most three and coordinate sum zero.
Every square root is of a nonnegative real number.

For fixed $j$, summing the two $r$ outer compressions yields
$\frac13\left(\begin{smallmatrix}V&c_*\\\bar c_*&V\end{smallmatrix}\right)$:
the diagonal weights sum to $V/3$ and the cross weights sum to
$\kappa\eta/3=c_*/3$. Their middle coordinate is minus their outer sum.
All six $r$ terms together therefore give outer diagonals $V$, outer edge
$c_*$, outer-middle entries $-(V+c_*)/3$ and its conjugate, each middle
diagonal $(2V-1)/3$, and no middle off-diagonal.

The six $p$ terms contribute each outer diagonal $3S=U$. A given middle
coordinate occurs in two cyclic pairs at each outer, so their outer-middle
entry is $S(\alpha+\bar\alpha)=-S$, and their middle diagonal is
$4S|\alpha|^2=4S/3$. A given oriented middle edge receives
$2S\alpha^2=S/3+iS/\sqrt3$. Finally $vv^\dagger$ has middle diagonal $1/3$
and oriented edge $\omega/3$, so $q_0$ contributes diagonal $2S/3$ and edge
$-S/3+iS/\sqrt3$.

Thus the total middle edge is $2iS/\sqrt3=ib$, and its diagonal is
$(2V-1)/3+2S=1$ since $V+3S=2$. Outer diagonals are $V+U=2$, the outer
edge is $c_*$, and the first-outer/middle entry is

$$
-\frac{V+c_*}{3}-S=-\frac{2+c_*}{3}=h_*,
$$

with its conjugate at the other outer. These are every entry in (5.3).
The finite list (5.12)–(5.13) therefore realizes exactly $L$.

Return every displayed vector $x$ to the actual state by

$$
z=\frac1{\sqrt5}D^{-1}x.
\tag{5.14}
$$

The outer products sum to $D^{-1}L(D^{-1})^\dagger/5=C(A,b)$, and diagonal
invertibility preserves each original support. This also verifies the
normalization, with trace one after transport. At $b=0$ all $p,q_0$ slots
vanish; at $b=\beta$, $V=\kappa$, so the three $\varepsilon=-1$ slots vanish
and at most ten nonzero terms remain. No denominator vanishes at either
endpoint.

By (3.7), support two is impossible anywhere on $a=A>1/3$, so this
construction has exact value three. Lemma 5.1 excludes every three-support
decomposition for $b>\beta$ and Theorem 6.1 supplies a finite four-support
upper realization there. Lemma 2.2 covers all original signs. $\square$

## 6. Inherited finite upper construction and strict witness exclusion

**定理 6.1（Explicit universal upper list in original coordinates）。**
Every legal $C(s,t)$ has a finite four-support realization with at most
sixty nonzero vectors. The construction also works for any real skew
$X\in M_5(\mathbb R)$ with $I_5+iX\succeq0$.

Proof. Hermiticity of $iX$ and $\overline{iX}=-iX$ pair its real eigenvalues
by conjugation, including equal eigenspace dimensions. Choose an orthonormal
original-coordinate eigenbasis
$h_{1,+},h_{1,-},h_{2,+},h_{2,-},w$ with eigenvalues
$\lambda,-\lambda,\mu,-\mu,0$, where $0\le\lambda,\mu\le1$.
Positivity gives these bounds; in a zero or repeated eigenspace any
orthonormal choice supplies the slots. No sparse eigenvectors are assumed.

For $\varepsilon,\delta=\pm1$ put
$p_{\varepsilon\delta}=(1+\varepsilon\lambda)(1+\delta\mu)/4$,
$u=h_{1,\varepsilon}$, $v=h_{2,\delta}$, and
$Q_{\varepsilon\delta}=2uu^\dagger+2vv^\dagger+ww^\dagger$.
The four weights are nonnegative and sum to one.
The first pair's spectral coefficients in $\sum pQ$ are
$2\sum_\delta p_{\varepsilon\delta}=1+\varepsilon\lambda$;
the second pair's are $1+\delta\mu$, and that of $ww^\dagger$ is one.
Thus $\sum pQ=I_5+iX$.

For any orthonormal complex $x,y$, set
$f_r(x,y)=y_rx-x_ry$ in the original coordinate positions. Its $r$ coordinate
is zero. Expanding its outer products gives

$$
\sum_{r=1}^5 f_r(x,y)f_r(x,y)^\dagger=xx^\dagger+yy^\dagger,
\tag{6.1}
$$

because the squared-coordinate sums are one and the cross coefficient
$\sum_r y_r\bar x_r=x^\dagger y$ is zero. For each sign pair and each $r$,
take the three vectors

$$
\sqrt{\frac{3p_{\varepsilon\delta}}{10}}\,f_r(u,v),\qquad
\sqrt{\frac{p_{\varepsilon\delta}}{10}}\,f_r(u,w),\qquad
\sqrt{\frac{p_{\varepsilon\delta}}{10}}\,f_r(v,w).
\tag{6.2}
$$

Writing $P_x=xx^\dagger$, equation (6.1) and the projection identity

$$
2P_u+2P_v+P_w
=\frac32(P_u+P_v)+\frac12(P_u+P_w)+\frac12(P_v+P_w)
$$

show that their sum for a sign pair is $p_{\varepsilon\delta}Q_{\varepsilon\delta}/5$.
Summing the four pairs gives exactly $(I_5+iX)/5$.
Each vector misses its selected original coordinate, so has support at most
four. The total squared norm is
$\sum p_{\varepsilon\delta}\operatorname{tr}Q_{\varepsilon\delta}/5=1$.
There are sixty slots. All zero weights and cancellations can be omitted.
There is no division by an eigenvalue, coordinate, parameter, or gap, so
zero, repeated and saturated spectral cases are included. This is the
coordinate-cancellation construction owned by the sharp fixed-basis coherence
source. $\square$

**命题 6.2（Inherited witness halfspace, with no converse）。** For $a,b\ge0$
in the legal rectangle,

$$
7a+3b>\frac{5\sqrt3}{2}\quad\Longrightarrow\quad k(C(a,b))=4.
\tag{6.3}
$$

Proof. Use the inherited witness $T=F(1,1)$,
$H=I_5-iT/\sqrt3$. On any three-coordinate set, the compressed real skew
matrix $R$ has unit-magnitude upper entries. Odd skew dimension gives
$\det R=0$; $iR$ is Hermitian with trace zero and square trace six.
Its eigenvalues are therefore $0,\sqrt3,-\sqrt3$.
The corresponding compression of $H$ has spectrum $1,0,2$, hence is PSD
on the full complex coordinate subspace. Any smaller support embeds in a
triple, so $z^\dagger Hz\ge0$ for every at-most-three-support complex vector.

For the actual family, the seven $a$ entries and three $b$ entries give

$$
\operatorname{tr}(TF(a,b))=-2(7a+3b),\qquad
\operatorname{tr}(HC(a,b))=1-\frac{2(7a+3b)}{5\sqrt3}.
\tag{6.4}
$$

The second identity follows by expanding $H(I+iF)/5$; both skew traces vanish.
A finite three-support Gram decomposition would give
$\operatorname{tr}(HC)=\sum_\ell z_\ell^\dagger Hz_\ell\ge0$.
The strict inequality (6.3) contradicts that, and Theorem 6.1 gives the
upper bound four. The signed witness is obtained by the same permutations
as the state. Equality or positive pairing in (6.4) gives no converse.
The halfspace is an immediate inherited witness application and adds no
mechanism. $\square$

In particular the legal dense corner $(A,B_0)$ has negative pairing since
$2\sqrt7>3\sqrt3$ is equivalent to $28>27$. It is the inherited dense
negativity maximizer and coherence-four example. This does not classify
other maximizers.

## 7. The constructive polygon

Set $a_0=1/3$ and, for $a_0\le a\le A$, define

$$
\phi(a)=B_0+(\beta-B_0)\frac{a-a_0}{A-a_0}.
\tag{7.1}
$$

Here $A>a_0$ since $9>7$ and $0<\beta<B_0$ since
$1>A>1/4$ (the latter inequality follows from $16>7$). Hence $\phi>0$
on its whole closed interval. Let

$$
P_3=
\{(a,b):0\le a\le a_0,\ 0\le b\le B_0\}
\ \cup\
\{(a,b):a_0\le a\le A,\ 0\le b\le\phi(a)\}.
\tag{7.2}
$$

**定理 7.1（Finite three-support lists throughout the sufficient polygon）。**
Every point of $P_3$ has an actual finite three-support Gram realization.
The points outside the support-two set have exact value three.

Proof. If two matrices have finite lists $x_\ell$ and $y_h$, their mixture
with weights $1-\theta,\theta\ge0$ has the concatenated list
$\sqrt{1-\theta}\,x_\ell,\sqrt\theta\,y_h$. This proves the support bound
by actual vectors rather than a cone-feasibility assertion.

For $a\le a_0$, take the list (4.6) for $M(a,B_0)$ and its middle-reflected
list for $M(a,-B_0)$. Multiply the first list by
$\sqrt{(1+b/B_0)/2}$ and the second by $\sqrt{(1-b/B_0)/2}$,
then concatenate. Both radicands are nonnegative on $0\le b\le B_0$.
Affineness of (1.2) gives exactly $M(a,b)$.

For $a_0\le a\le A$, put $\theta=(a-a_0)/(A-a_0)\in[0,1]$.
Mix the horizontal endpoint list for $M(a_0,B_0)$ with the vertical endpoint
list for $M(A,\beta)$, with weights $1-\theta,\theta$.
For this paragraph use $M$ lists throughout: the vertical endpoint is
obtained from (5.12)–(5.13) by $D^{-1}$, without the factor $1/\sqrt5$.
Their affine mixture is $M(a,\phi(a))$. Reflect the middles to get a list
for $M(a,-\phi(a))$. Mix those two lists with weights
$(1+b/\phi(a))/2,(1-b/\phi(a))/2$. They are nonnegative and give exactly
$M(a,b)$ for $0\le b\le\phi(a)$.

In both cases divide the final concatenated list by $\sqrt5$ once, omit
zero terms, and restore original signs by Lemma 2.2. This covers the axes,
endpoints, chord and their intersections with the support-two region.
Theorem 3.1 gives the lower bound three outside that region, proving exact
value three there. Convex interpolation supplies no necessity of the chord.
$\square$

## 8. Conditional interpretation for each specified Schur channel

The matrix classification above needs no operational assumptions. Its inherited
interpretation, when used, fixes the same matrix in
$T_C(Y)=(5C)\circ Y$ and the same original state $JCJ^\dagger$.

From a normalized sparse list $C=\sum_\ell z_\ell z_\ell^\dagger$ of maximal
support $q$, set $K_\ell=\sqrt5\,\operatorname{diag}z_\ell$.
The diagonal $C_{ii}=1/5$ gives
$\sum_\ell K_\ell^\dagger K_\ell=I_5$ and
$\sum_\ell K_\ell YK_\ell^\dagger=(5C)\circ Y$ on every complex matrix.
For each nonzero slot choose a fixed coordinate isometry
$V_\ell:\mathbb C^q\to\mathbb C^5$ containing its support, filling smaller
supports to $q$ coordinates. Put $B_\ell=V_\ell^\dagger K_\ell$ and use

$$
\operatorname{Enc}(Y)=(B_\ell YB_\ell^\dagger)_\ell,\qquad
\operatorname{Dec}_\ell(Z)=V_\ell ZV_\ell^\dagger.
\tag{8.1}
$$

The finite classical flag set is fixed for this $C$. Each decoder is CPTP on
the entire $M_q$ block because $V_\ell^\dagger V_\ell=I_q$, and the encoder
is trace preserving since
$\sum_\ell B_\ell^\dagger B_\ell=I_5$.
Sandwiching is completely positive under every reference amplification.
All quantum paths pass through the block, and the composite equals the
specified $T_C$ on all complex inputs.

For completeness, a competing finite fixed-flag entire-block scheme yields
a finite Kraus family $K_{fab}=R_{fb}B_{fa}$ of rank at most $q$, with
completeness following from decoder and encoder trace preservation.
Since $T_C(E_{ii})=E_{ii}$, for $r\ne i$ its nonnegative Kraus squares sum
to zero:
$\sum_{fab}|K_{fab}(r,i)|^2=0$. Each of these same low-rank Kraus matrices
is diagonal. Its rank equals the number of nonzero diagonal entries, giving
a support-at-most-$q$ Gram decomposition of $5C$, and hence of $C$.
There is no Kraus mixing followed by an unsupported rank assertion.

Similarly, in any finite pure-state decomposition of $JCJ^\dagger$,
positivity against the orthogonal complement of $\operatorname{ran}J$
forces every term to be $Jz_\ell$. Its coefficient matrix is a diagonal
matrix followed by the matching permutation, so its Schmidt rank across
$H^{(1)}\mid H^{(2)}$ is exactly $|\operatorname{supp}_Bz_\ell|$.
The converse follows by applying $J$ to a Gram list. These arguments recover
the inherited C-109 same-matrix identity

$$
q_{\rm exact}(T_C)=k(C)
=\operatorname{SN}_{H^{(1)}\mid H^{(2)}}(JCJ^\dagger).
\tag{8.2}
$$

This is a per-fixed-$C$ statement about an exact specified channel on all
inputs. It is not a channel programmed by an unknown source, and not one
set of $C$-independent flags implementing every different $T_C$.
For a matched input $JD'J^\dagger$ its local Schur action is
$D'\mapsto(5C)\circ D'$; in particular it keeps $JI_5J^\dagger/5$ fixed,
rather than preparing $JCJ^\dagger$ from it.

The capacity source's actual-menu and fixed-erasure conclusions retain their
C-108/C-111 conditional scope. In particular its scalar dephasing simulation
of the promised invisible histories is compatible with (8.2): exact
specified-channel realization and promised-history simulation are distinct
targets. No history-simulation lower bound follows from this volume.
No mathematical permutation, diagonal scaling, spectral choice, witness or
Gram list supplies a physical preparation, available phase control,
measurement, source copy, independent re-preparation, or reference access.
Term counts are not physical storage bounds or minimal flag counts.
There is no empirical machine-learning/general-neural conclusion, BP
error optimum, unconstrained port-error solution, or wider program completion.

## 9. Exact classified branches and the precise residual set

Let

$$
Q_2=\{(a,b)\in[0,A]\times[0,B_0]:
6a^2\le(1-a)(1-2b)\}.
\tag{9.1}
$$

The exact values established by the preceding proofs, always with
$a=|s|,b=|t|$, are:

| Parameter branch | Exact value and proof |
| --- | --- |
| $a=b=0$ | $k=1$, Theorem 3.1. |
| $Q_2\setminus\{(0,0)\}$ | $k=2$, with a finite list and all-complex necessity in Theorem 3.1. |
| $P_3\setminus Q_2$ | $k=3$, finite polygon lists and the support-two lower bound. |
| $b=B_0$, $a_0<a\le A$ | $k=4$, horizontal kernel exclusion and finite universal upper list. |
| $a=A$, $\beta<b\le B_0$ | $k=4$, vertical budget exclusion and finite universal upper list. |
| $7a+3b>5\sqrt3/2$ | $k=4$, solely the inherited strict witness and finite universal upper list. |

All branch endpoints stated as closed are included. In particular
$(a_0,B_0)$ and $(A,\beta)$ have exact value three.
The support-two region lies in $a\le a_0$ by (3.7).
Every signed axis and every zero/singular/repeated case is included by
Sections 2–7.

**开放问题 9.1（Unchanged full-family target on the exact residual $U$）。**
The unclassified original parameters are precisely

$$
U=\left\{(s,t):
\begin{aligned}
&a=|s|,\quad b=|t|,\quad a_0<a<A,\\
&\phi(a)<b<B_0,\qquad 7a+3b\le5\sqrt3/2
\end{aligned}
\right\}.
\tag{9.2}
$$

To verify this remainder, every $a\le a_0$ lies in $P_3$.
For $a>a_0$, the portion $b\le\phi(a)$ is also in $P_3$.
The vertical edge above $\beta=\phi(A)$ and the horizontal edge above
$a_0$ have value four. The only points left before using the witness are
the strict interior above the chord; removing its strict witness halfspace
leaves exactly (9.2). In particular witness equality remains in $U$ unless
another displayed branch applies.

At every point of $U$, Theorem 3.1 excludes support two and Theorem 6.1
constructs support four. Thus the established range is

$$
3\le k(C(s,t))\le4\qquad((s,t)\in U),
\tag{9.3}
$$

and neither value is selected by this result. The remainder has a genuine
two-dimensional portion: at $(a_0,B_0)$ the witness expression is strictly
below threshold since
$7/3+\sqrt3<5\sqrt3/2$ follows from $196<243$.
Immediately to the right the chord is below $B_0$ and continuity leaves
an open region between it and $B_0$ still below the witness threshold.

The completion criterion is unchanged: for every remaining legal parameter
of this same $F(s,t)$ family and this same ordered basis, decide existence of
a finite complex support-at-most-three Gram decomposition. Each feasible
portion requires actual finite original-coordinate vectors; each infeasible
portion requires exclusion of all finite complex decompositions, with every
tie and boundary assigned. Support one and two are completely settled, but
the full support-three/four classification is not complete until $U$ is
resolved. The chord is sufficient only. A nonnegative witness pairing is
not a feasibility certificate. Edge kernel equations do not extend without
proof to nonsingular interior points.

## 10. Evidence ceiling and exact limits

The complete ordinary proofs here supply the family definition and rectangle,
sign transports, support-two necessity and finite converse, two independent
edge kernel/budget exclusions, matching sparse lists, a finite universal
upper realization, the inherited strict witness exclusion, and constructive
polygon interpolation. All realizations return to the actual original
$C=(I+iF)/5$; no real-only ensemble, eigenbasis support substitution or physical
control is presumed. The symmetric and antiunitary operations in the vertical
proof were verified on the actual matrix and act only within its complex
competitor domain.

The deductions use the canonical sources named in Convention 1.4 and the
explicit ordinary arguments in this volume. No Lean/kernel, numerical,
experimental, or external-research conclusion is asserted. No global priority,
sterility or model-diversity claim is made. Latest C-111's existing maximum
and examples, and the sharp-negativity owner's results, retain their ownership.

No classification of all skew-fiber members, all coherence-four maximizers
or all negativity maximizers is inferred. The result does not cover another
basis, tensor split, dimension, population fiber, non-skew invisible
direction, approximate zero population, finite-sample substitute, new
operational interface, or physical implementation. Its complete partial
branches and its unresolved domain (9.2) concern exactly the original closed
rectangle, with the full finite complex competitor class (1.4).

## 追加锚（本行以下为增补区）
