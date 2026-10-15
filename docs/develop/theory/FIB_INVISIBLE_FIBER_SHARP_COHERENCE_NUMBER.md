# FIB invisible fiber: the sharp fixed-basis coherence number

## 1. Result, proof status and ownership

The maximum finite complex Gram coherence number over the entire original
five-coordinate invisible skew fiber is exactly four. Every member has an
actual decomposition into at most sixty complex vectors, each missing an
original coordinate. The inherited dense negativity maximizer attains four:
an exact Hermitian witness excludes every finite decomposition of that state
into complex vectors supported on at most three original coordinates.

This volume supplies complete ordinary finite-dimensional proofs. It is a
theory reference source, not a Lean or kernel certificate. Its additional
deductions have status `repo-derived` relative to the supplied mathematics;
no literature-wide priority claim is made. The document uses `generic-v1`
numbered claims and retains a terminal append anchor. After incorporation,
extensions and corrections belong after that anchor in new sections.

The ownership of the ingredients is as follows.

| Mathematical source | Inherited content and contribution used here |
| --- | --- |
| [Mixed-state capacity and certification volume, C-106–C-108](AURIC_FIB_ATOM_HIDDEN_RELATIONS_MIXED_STATE_CAPACITY_AND_CERTIFICATION.md) | Exact matched support, the original tensor split and real-skew invisible fiber, purity facts, and conditional local-menu and flag-erasure interfaces. |
| The same capacity volume, C-109 | The finite complex, fixed-basis definition of coherence number; the coherence/Schmidt/fixed-channel dictionary; and the edge/triangle examples with exact values two and three. C-109.11 leaves the entire-fiber maximum open. |
| The same capacity volume, C-110 | Necessary relations between finite-block port error and population leakage on the same sources, with their stated scope and limitations. |
| Supplied volume *FIB invisible fiber: the sharp purity–negativity attainable region*, Sections 4, 8 and 10 | Skew spectral structure, the dense matrix used below, its legality and spectrum, and its negativity-maximizing role. That source owns its sharp purity–negativity region and the construction of that matrix. |
| Supplied coherence-maximum proposal, `proposed-coherence-maximum.json` | The coordinate-cancellation identity, four-sign spectral mixture, and three-coordinate-positive witness underlying the two bounds below. |
| Supplied mathematical check, `independent-coherence-maximum-check.json` | Complete algebraic checking of those constructions, including original-coordinate supports, degeneracies, normalization and the direction of the witness inference. |

The increment relative to the two ordinary source volumes is precisely the
universal finite four-support construction and the all-decomposition lower
bound for the inherited dense state. The proposal and check supply mathematical
arguments, not proof premises by virtue of their verdicts. The identities and
inequalities needed for the result are proved below. The inherited fiber,
resource dictionary, edge/triangle examples and dense negativity attainer are
not presented as new constructions of this volume.

## 2. The exact domain and the sharp assertion

**定义 2.1（Fixed original coordinates and matched source）。** Fix the ordered
orthonormal mode basis

$$
B=(0,1,2,3,13),\qquad H^{(1)}=H^{(2)}=\mathbb C^5.
$$

In displayed matrices and vector coordinates, positions $1,2,3,4,5$ mean
these labels in exactly this order. Define the permutation

$$
f(0)=13,\quad f(13)=0,\quad f(1)=3,\quad f(3)=1,\quad f(2)=2
$$

and the isometry

$$
J:\mathbb C^5\longrightarrow H^{(1)}\otimes H^{(2)},\qquad
J|s\rangle=|s,f(s)\rangle,\qquad J^\dagger J=I_5.
\tag{2.1}
$$

All Schmidt-number interpretations use the original split
$H^{(1)}\mid H^{(2)}$. This is not a split between independent copies of
the whole source.

**定义 2.2（Entire original invisible skew fiber）。** Set

$$
\begin{aligned}
\mathcal X&=\{X\in M_5(\mathbb R):X^T=-X,\ I_5+iX\succeq0\},\\
C(X)&=\frac{I_5+iX}{5},\qquad
\Gamma(X)=JC(X)J^\dagger,\\
\mathfrak I&=\{\Gamma(X):X\in\mathcal X\}.
\end{aligned}
\tag{2.2}
$$

This is the C-108 fiber with $X=5A$ in its notation
$C=I_5/5+iA$. The skew condition makes the diagonal of $X$ zero. Thus
$C(X)$ is positive semidefinite with diagonal $1/5$ and trace one, and
$\Gamma(X)$ is also a density operator. There is no additional sign,
sparsity, purity, rank, source-independence or operation hypothesis in
$\mathcal X$. The description as an invisible fiber for an actual menu is
conditional on the inherited C-108 interface; the matrix class (2.2) itself
is defined without that operational assumption.

**定义 2.3（Finite complex Gram coherence number）。** For a nonzero positive
semidefinite $5\times5$ matrix $C$, let

$$
k(C)=\min\left\{
\max_{1\le a\le m}|\operatorname{supp}_B z_a|:
m\ge1,\quad z_a\in\mathbb C^5\setminus\{0\},\quad
C=\sum_{a=1}^m z_az_a^\dagger
\right\}.
\tag{2.3}
$$

Here $\operatorname{supp}_B z$ is the set of nonzero coordinates in the
fixed original basis $B$. All finite lengths and all complex phases and
norms are allowed. Nonnegative coefficients can be absorbed into the
vectors by their square roots, and zero terms are omitted. The Hermitian
spectral theorem gives a finite decomposition, so the set of possible
maximal supports is a nonempty subset of $\{1,2,3,4,5\}$ and has a minimum.
Multiplication of $C$ by a positive scalar leaves $k(C)$ unchanged, since
scaling every vector by the corresponding positive square root is a
bijection between its decompositions. This is the inherited C-109
definition, with its quantifiers explicit.

**定理 2.4（Sharp maximum on the entire fiber）。** For every $X\in\mathcal X$,
$C(X)$ has a finite complex Gram decomposition into at most sixty nonzero
vectors, every one of support at most four in $B$. There is an explicit
$X_*\in\mathcal X$ such that no finite complex Gram decomposition of
$C(X_*)$ has every vector supported on at most three coordinates. In
particular,

$$
\boxed{\quad\max_{X\in\mathcal X} k\!\left(\frac{I_5+iX}{5}\right)=4.\quad}
\tag{2.4}
$$

Proof. Section 3 constructs the universal decomposition. Section 4 verifies
the explicit state's legality and its inherited spectral facts. Section 5
excludes every finite complex three-support decomposition of that same
state. These yield both inequalities and actual attainment in (2.4).
$\square$

## 3. A universal finite construction in the original coordinates

**引理 3.1（Cancellation of one original coordinate）。** Let $u,v\in\mathbb C^5$
be orthonormal. For each original coordinate position $r\in\{1,2,3,4,5\}$
define

$$
F_r(u,v)=v_r u-u_r v.
\tag{3.1}
$$

Then $F_r(u,v)$ has its $r$-th coordinate zero, and

$$
\sum_{r=1}^5 F_r(u,v)F_r(u,v)^\dagger
=uu^\dagger+vv^\dagger.
\tag{3.2}
$$

Proof. The $r$-th coordinate is $v_ru_r-u_rv_r=0$, including when either
coefficient vanishes. Expansion of the left side gives

$$
\begin{aligned}
\sum_rF_rF_r^\dagger
&=\left(\sum_r|v_r|^2\right)uu^\dagger
 +\left(\sum_r|u_r|^2\right)vv^\dagger\\
&\quad-\left(\sum_r v_r\overline{u_r}\right)uv^\dagger
 -\left(\sum_r u_r\overline{v_r}\right)vu^\dagger.
\end{aligned}
\tag{3.3}
$$

The first two sums are one; the last two are $u^\dagger v=0$ and
$v^\dagger u=0$. This proves (3.2) for complex vectors in the original
coordinates. Each nonzero $F_r$ therefore has support at most four.
$\square$

**引理 3.2（Paired spectrum with all degeneracies）。** For every $X\in\mathcal X$
there are $a,b\in[0,1]$ and an orthonormal basis

$$
h_{1,+},h_{1,-},h_{2,+},h_{2,-},w
$$

of $\mathbb C^5$ in which the eigenvalues of $iX$ are respectively
$a,-a,b,-b,0$. The vectors are expressed in the original coordinates;
their supports are not asserted to be small.

Proof. Since $X$ is real skew,

$$
(iX)^\dagger=iX,\qquad \overline{iX}=-iX.
$$

If $(iX)h=t h$, Hermiticity gives $t\in\mathbb R$. Conjugation yields
$(iX)\overline h=-t\overline h$. Conjugation is an invertible antilinear
map between the $t$ and $-t$ eigenspaces; their dimensions agree. The five
eigenvalues can therefore be listed as $a,-a,b,-b,0$ with $a,b\ge0$.
When there are fewer than two nonzero pairs, the remaining entries in this
list are zero. The zero eigenspace has odd dimension and supplies all the
needed zero slots. The Hermitian spectral theorem permits orthonormal
choices within every eigenspace, including repeated positive or negative
eigenvalues. Thus all five chosen vectors can be mutually orthogonal.

The corresponding eigenvalues of $I_5+iX$ are $1+a,1-a,1+b,1-b,1$.
Its assumed positive semidefiniteness forces $a,b\le1$. This also proves
that no positive-definiteness or distinct-eigenvalue assumption was used.
$\square$

**引理 3.3（Four nonnegative spectral weights）。** In the notation of Lemma 3.2,
for $\epsilon,\delta\in\{+1,-1\}$ put

$$
\begin{aligned}
p_{\epsilon\delta}&=\frac{(1+\epsilon a)(1+\delta b)}4,\\
u_{\epsilon\delta}&=h_{1,\epsilon},\qquad
v_{\epsilon\delta}=h_{2,\delta},\\
Q_{\epsilon\delta}&=2u_{\epsilon\delta}u_{\epsilon\delta}^\dagger
 +2v_{\epsilon\delta}v_{\epsilon\delta}^\dagger+ww^\dagger.
\end{aligned}
\tag{3.4}
$$

All $p_{\epsilon\delta}$ are nonnegative, sum to one, and satisfy

$$
I_5+iX=\sum_{\epsilon,\delta}p_{\epsilon\delta}Q_{\epsilon\delta}.
\tag{3.5}
$$

Proof. Every factor $1\pm a,1\pm b$ is nonnegative. Summing their products
gives $\sum p_{\epsilon\delta}=1$. For a fixed $\epsilon$, the coefficient
of $h_{1,\epsilon}h_{1,\epsilon}^\dagger$ on the right of (3.5) is

$$
2\sum_\delta p_{\epsilon\delta}=1+\epsilon a.
$$

The coefficient of $h_{2,\delta}h_{2,\delta}^\dagger$ is likewise
$1+\delta b$, and the coefficient of $ww^\dagger$ is one. These are exactly
the spectral coefficients of $I_5+iX$. Equality of these coefficients in
an orthonormal basis proves the matrix identity (3.5), also when some of
the coefficients coincide or vanish. $\square$

**定理 3.4（Explicit at-most-sixty-vector upper bound）。** For every $X\in\mathcal X$,
use (3.4), and for each sign pair write $p=p_{\epsilon\delta}$,
$u=u_{\epsilon\delta}$, $v=v_{\epsilon\delta}$. For each $r=1,\ldots,5$
take the following three complex vectors:

$$
\begin{aligned}
z^{(1)}_{\epsilon\delta r}&=\sqrt{\frac{3p}{10}}\,F_r(u,v),\\
z^{(2)}_{\epsilon\delta r}&=\sqrt{\frac{p}{10}}\,F_r(u,w),\\
z^{(3)}_{\epsilon\delta r}&=\sqrt{\frac{p}{10}}\,F_r(v,w).
\end{aligned}
\tag{3.6}
$$

Their outer products sum exactly to $C(X)$. Each vector has support at
most four in the original basis, and deleting zero vectors leaves at most
sixty terms. Consequently $k(C(X))\le4$ for the entire fiber.

Proof. The triple $u,v,w$ is orthonormal. With $P_x=xx^\dagger$, the identity

$$
2P_u+2P_v+P_w
=\frac32(P_u+P_v)+\frac12(P_u+P_w)+\frac12(P_v+P_w)
\tag{3.7}
$$

follows by adding the three coefficients of each projection. Applying
Lemma 3.1 to each parenthesis and multiplying by $p/5$ gives

$$
\sum_{r=1}^5\sum_{j=1}^3
z^{(j)}_{\epsilon\delta r}
\bigl(z^{(j)}_{\epsilon\delta r}\bigr)^\dagger
=\frac p5Q_{\epsilon\delta}.
\tag{3.8}
$$

Summing over the four sign pairs and using (3.5) proves

$$
C(X)=\sum_{\epsilon,\delta}\sum_{r=1}^5\sum_{j=1}^3
z^{(j)}_{\epsilon\delta r}
\bigl(z^{(j)}_{\epsilon\delta r}\bigr)^\dagger.
\tag{3.9}
$$

All weights in (3.6) are explicitly nonnegative. The normalization is
exact: $\operatorname{tr}Q_{\epsilon\delta}=2+2+1=5$, so (3.8) has trace
$p$, and (3.9) has trace $\sum p=1$. Equivalently the squared norms of all
retained Gram vectors sum to one. The cancellation in (3.1) makes their
$r$-th original coordinate zero. There are $4\cdot5\cdot3=60$ slots,
with zero terms harmlessly omitted. No inference about support in an
eigenbasis is used. $\square$

**命题 3.5（Zero, repeated and boundary spectral cases）。** The construction
(3.6)–(3.9) covers every degenerate spectrum allowed in (2.2), including
$X=0$ and all singular states.

Proof. The only numerical denominator in the vector weights is the fixed
positive integer ten; there is no division by $a$, $b$, an eigenvalue gap
or a coordinate of an eigenvector. If $a=0$ or $b=0$, Lemma 3.2 supplies
orthonormal vectors in the zero eigenspace and the same weights apply.
If $a=b$, the orthonormal choices in the repeated eigenspaces still give
the same projection identity (3.5). If $a=1$ or $b=1$, some weights vanish;
their entire groups may be removed. At $a=b=1$ only $p_{++}=1$ remains,
and (3.7) still decomposes its $Q$ with eigenvalues $2,2,1,0,0$. At
$a=b=0$, all four weights are $1/4$ and any orthonormal basis may fill the
five slots. Lemma 3.1 also includes cancellations that yield zero vectors.
These cases exhaust the degeneracies of the paired spectrum. $\square$

## 4. The inherited dense state is an actual legal lower-bound state

**定义 4.1（Dense matrix in the original order）。** For real $\alpha,\beta$ put

$$
F(\alpha,\beta)=
\begin{pmatrix}
0&\alpha&\alpha&\alpha&\alpha\\
-\alpha&0&\beta&-\beta&\alpha\\
-\alpha&-\beta&0&\beta&\alpha\\
-\alpha&\beta&-\beta&0&\alpha\\
-\alpha&-\alpha&-\alpha&-\alpha&0
\end{pmatrix}.
\tag{4.1}
$$

Define

$$
G=F(1,0),\qquad K=F(0,1),\qquad
X_*=\frac{G}{\sqrt7}+\frac{K}{\sqrt3},\qquad
C_*=\frac{I_5+iX_*}{5},\qquad \Gamma_*=JC_*J^\dagger.
\tag{4.2}
$$

The matrix $F$ is the matrix denoted $M$ in Section 8 of the supplied
sharp-negativity volume. Thus $X_*$ is exactly its dense negativity
maximizer, in the same positional order. Its construction and
negativity-maximizing property are inherited. The legality calculation
below is included to make the coherence lower bound a statement about an
actual member of (2.2).

**引理 4.2（Two orthogonal active planes）。** The matrix $X_*$ has two unit
skew blocks on perpendicular real two-planes and vanishes on their
one-dimensional orthogonal complement. In particular

$$
\operatorname{spec}(iX_*)=\{1,-1,1,-1,0\}.
\tag{4.3}
$$

Proof. Let

$$
r=(1,0,0,0,-1)^T,\qquad
s=(1/2,1,1,1,1/2)^T.
$$

The entry formula $G=rs^T-sr^T$ gives exactly the seven unit upper
entries in the $\alpha$ positions of (4.1), and zero in its three
$\beta$ positions. Moreover

$$
r^Ts=0,\quad r^Tr=2,\quad s^Ts=7/2,\quad
Gr=-2s,\quad Gs=(7/2)r.
\tag{4.4}
$$

It follows directly from the same outer-product formula that $G$ kills
$\operatorname{span}(r,s)^\perp$. On the orthonormal basis
$r/\sqrt2,s/\sqrt{7/2}$ of $U=\operatorname{span}(r,s)$ its block is

$$
\begin{pmatrix}0&\sqrt7\\-\sqrt7&0\end{pmatrix}.
\tag{4.5}
$$

The matrix $K$ is zero outside its middle three coordinates, where its block
is

$$
K_3=\begin{pmatrix}0&1&-1\\-1&0&1\\1&-1&0\end{pmatrix},
\qquad K_3\mathbf1=0,\qquad K_3^2=\mathbf1\mathbf1^T-3I_3.
\tag{4.6}
$$

Consequently it acts on

$$
W=\{x\in\mathbb R^5:x_1=x_5=0,\ x_2+x_3+x_4=0\}
\tag{4.7}
$$

with $K^2=-3I$, and it kills $W^\perp$, which is spanned by the two outer
coordinate axes and the middle all-ones vector. Both $r$ and $s$ are
orthogonal to $W$: their middle coordinates are respectively zero and
all one. Thus $U$ and $W$ are perpendicular real two-planes. The action
of $G/\sqrt7$ is a unit skew block on $U$ and zero on $U^\perp$; the
action of $K/\sqrt3$ is a unit skew block on $W$ and zero on $W^\perp$.
For the latter statement, a unit vector $x\in W$ and
$y=-Kx/\sqrt3$ are orthonormal, and $Kx=-\sqrt3y$, $Ky=\sqrt3x$.
Their sum $X_*$ therefore has the asserted block structure. Multiplication
of each unit skew block by $i$ gives Hermitian eigenvalues $1,-1$,
proving (4.3). $\square$

**命题 4.3（Positivity, normalization and inherited source facts）。** The
matrix $X_*$ is real skew and belongs to $\mathcal X$. Its compressed
density matrix has

$$
\operatorname{spec}C_*=\{2/5,2/5,1/5,0,0\},\qquad
(C_*)_{ss}=1/5,\qquad \operatorname{tr}C_*=1.
\tag{4.8}
$$

Both $C_*$ and $\Gamma_*$ have rank three, and
$\operatorname{tr}(\Gamma_*^2)=9/25$. The original matched populations,
marginals and original $Q$ readout have their inherited values.

Proof. Real skewness follows from (4.1). Adding one to the eigenvalues
in (4.3), then dividing by five, gives (4.8) and positive
semidefiniteness. Zero skew diagonal gives the stated diagonal and trace.
The isometry $J$ preserves nonzero eigenvalues; $\Gamma_*$ has twenty
additional ambient zero eigenvalues. The sum of squared nonzero
eigenvalues is $(4+4+1)/25=9/25$.

For completeness the matching matrix units obey

$$
\begin{aligned}
\operatorname{Tr}_2(|s,f(s)\rangle\langle t,f(t)|)
 &=\delta_{st}|s\rangle\langle t|,\\
\operatorname{Tr}_1(|s,f(s)\rangle\langle t,f(t)|)
 &=\delta_{st}|f(s)\rangle\langle f(t)|.
\end{aligned}
\tag{4.9}
$$

Here injectivity of $f$ gives the first Kronecker symbol. Thus the diagonal
$1/5$ yields all matched populations
$p_{su}=\mathbf1_{\{u=f(s)\}}/5$ and both marginals $I_5/5$.
The inherited normalized vector

$$
\Omega=\tfrac12\bigl(|0,13\rangle+|13,0\rangle
                         -|1,3\rangle-|3,1\rangle\bigr),\qquad
q=J^\dagger\Omega=(1,-1,0,-1,1)^T/2
$$

is real with $q^Tq=1$. Skewness implies $q^TX_*q=0$, so for
$Q=|\Omega\rangle\langle\Omega|$ one has
$\operatorname{tr}(Q\Gamma_*)=q^TC_*q=1/5$.
These are inherited fiber properties, not additional preparation or
measurement permissions. $\square$

## 5. A witness against every finite complex three-support decomposition

**定义 5.1（Sparse-support witness）。** Set

$$
T=G+K=F(1,1),\qquad H=I_5-\frac{iT}{\sqrt3}.
\tag{5.1}
$$

Every upper entry of $T$ is $+1$ or $-1$, and $H$ is Hermitian. The matrix
$H$ is a mathematical separating witness; it is not asserted to be an
available menu effect.

**引理 5.2（Positivity on every three-coordinate complex subspace）。** For
every three-element subset $A$ of the five original coordinates,

$$
\operatorname{spec}(iT[A,A])=\{0,\sqrt3,-\sqrt3\},\qquad
\operatorname{spec}(H[A,A])=\{1,0,2\}.
\tag{5.2}
$$

Consequently $z^\dagger H z\ge0$ for every complex vector $z$ supported
on at most three original coordinates.

Proof. Write $R=T[A,A]$. This is a real skew $3\times3$ matrix with
three upper entries of magnitude one. Since the dimension is odd,

$$
\det R=\det R^T=\det(-R)=-\det R,
$$

so $\det R=0$. The matrix $iR$ is Hermitian and has trace zero. The trace
of its square is

$$
\operatorname{tr}((iR)^2)
=-\operatorname{tr}(R^2)
=2\sum_{j<k,\ j,k\in A}|T_{jk}|^2=6.
\tag{5.3}
$$

At least one of its three real eigenvalues is zero by its determinant.
The other two sum to zero by its trace, so they are $t,-t$.
Equation (5.3) gives $2t^2=6$, proving the first spectrum in (5.2).
The affine map $x\mapsto1-x/\sqrt3$ gives the second spectrum. Thus
$H[A,A]$ is positive semidefinite on $\mathbb C^3$, including its zero
eigenvalue.

Every set of at most three original coordinates lies in a three-element
set $A$. A vector supported there has
$z^\dagger H z=z_A^\dagger H[A,A]z_A\ge0$, allowing the unused entries of
$z_A$ to be zero. This proves the assertion for all complex phases and
all such supports at once, without enumerating triples or restricting
the vectors to be real. $\square$

**引理 5.3（Exact negative pairing with the legal dense state）。** The same
$C_*$ and $H$ satisfy

$$
\operatorname{tr}(HC_*)
=\frac{3\sqrt3-2\sqrt7}{5\sqrt3}<0.
\tag{5.4}
$$

Proof. The upper entries of $X_*$ and $T$ have the same signs. There are
seven entries of magnitude $1/\sqrt7$ and three of magnitude $1/\sqrt3$.
For two real skew matrices, the two ordered terms of each unordered
pair give

$$
\begin{aligned}
\operatorname{tr}(TX_*)
&=-2\sum_{j<k}T_{jk}(X_*)_{jk}\\
&=-2\left(\frac7{\sqrt7}+\frac3{\sqrt3}\right)
=-2(\sqrt7+\sqrt3).
\end{aligned}
\tag{5.5}
$$

Expanding the product before taking the trace gives

$$
HC_*=\frac15\left(I_5+iX_*-\frac{iT}{\sqrt3}
                                      +\frac{TX_*}{\sqrt3}\right).
\tag{5.6}
$$

Both skew matrices have trace zero. Therefore (5.5) implies

$$
\operatorname{tr}(HC_*)
=1-\frac{2(\sqrt7+\sqrt3)}{5\sqrt3}
=\frac{3\sqrt3-2\sqrt7}{5\sqrt3}.
$$

The denominator is positive. The two compared radicals are positive and
$(2\sqrt7)^2=28>27=(3\sqrt3)^2$, so the numerator is strictly negative.
This sign is symbolic and exact. $\square$

**定理 5.4（All-decomposition lower bound and attainment of four）。** Every
finite complex Gram decomposition of $C_*$ has a vector supported on
at least four original coordinates. Together with Theorem 3.4 this yields
$k(C_*)=4$ and proves Theorem 2.4.

Proof. Suppose there were any finite decomposition

$$
C_*=\sum_{a=1}^m z_az_a^\dagger,\qquad
z_a\in\mathbb C^5,\quad |\operatorname{supp}_B z_a|\le3.
\tag{5.7}
$$

By finite linearity and the rank-one trace identity,

$$
\operatorname{tr}(HC_*)
=\sum_{a=1}^m\operatorname{tr}(H z_az_a^\dagger)
=\sum_{a=1}^m z_a^\dagger H z_a\ge0,
\tag{5.8}
$$

where the last inequality is Lemma 5.2 applied to each term. This
contradicts Lemma 5.3. The argument imposes no limit on $m$ except
finiteness and no restriction on the phases, norms, overlap or patterns
of the supports. It therefore excludes every decomposition in (5.7),
including every positively weighted version after absorption of its
weights into the vectors. Hence $k(C_*)\ge4$.

Proposition 4.3 proves $X_*\in\mathcal X$, so the actual finite upper
construction of Theorem 3.4 applies to it and gives $k(C_*)\le4$.
The universal upper bound and this legal attaining state establish the
maximum four over all of $\mathcal X$. Only positivity of the small
compressions is used in (5.8); no positivity of $H$ on the whole space,
nor any converse of the witness criterion, is assumed. $\square$

## 6. Meaning of the inherited dictionary and the operational limits

**命题 6.1（Conditional resource interpretation for the specified channels）。**
Retain exactly the finite classical-flag, entire-block CPTP interface of
C-109.1–C-109.3. For each $C=C(X)$ define its specified Schur channel
$T_C(Y)=(5C)\circ Y$. The inherited dictionary is

$$
q_{\rm exact}(T_C)=k(C)
=\operatorname{SN}_{H^{(1)}\mid H^{(2)}}(JCJ^\dagger).
\tag{6.1}
$$

Under that interface, the maximum of these specified exact-channel
resources, and of these matched-source Schmidt numbers, is four. The
state $\Gamma_*$ and channel $T_{C_*}$ attain it.

Proof. C-109.3 supplies (6.1) with finite decompositions, original
coordinates, a fixed finite classical flag space and CPTP decoding on
each entire $M_q$ block. Applying Theorem 2.4 to its $C$ gives the upper
bound four, and applying Theorem 5.4 to $C_*$ gives attainment. This is
an application of the inherited dictionary; the new argument is the
matrix maximum proved in Sections 3–5. $\square$

**注记 6.2（Exact realization and history simulation are different targets）。**
The quantity $q_{\rm exact}(T_C)$ specifies one channel on all complex
inputs under (6.1). It is not the minimum dimension needed merely to
simulate the histories of sources in the invisible fiber. Under the
conditional C-108 local-menu contract all those sources have the same
allowed histories as $S=JI_5J^\dagger/5$; C-109 also gives a scalar
dephasing simulation of those promised histories. The coherence maximum
does not reverse that indistinguishability or furnish a new readout.
The sixty-vector upper bound counts Gram terms. It is not a minimum flag
count, a physical storage bound or an implementation cost.

**注记 6.3（Preparation, leakage and learning boundaries）。** Spectral choices
and coordinate cancellations construct mathematical vectors; they do
not supply available gates or preparation of $\Gamma(X)$ from a native
FIB system. Likewise the witness is not a granted measurement, and an
arbitrary Gram decomposition is not a physically executable ensemble
preparation. Source copies, joint instruments, local phase references,
external reference access and other controls require their own
interfaces. Equal local marginals do not supply independent copies of
the source.

C-110's same-source population-leakage identities and necessary
error–leakage bounds remain inherited. Neither those necessary bounds
nor the maximum in (2.4) supplies a sufficient port design, an exact
unconstrained error optimum, a physical preparation map or a transfer
to neural computation. No empirical machine-learning improvement,
sample complexity, running-time advantage or physical memory advantage
is established here. The Gram result does not resolve other port,
error or broader FIB objectives.

## 7. Exact completion boundary

**注记 7.1（What is settled and what is not classified）。** The full universal
statement (2.4) has two complete ordinary proofs of its required bounds:
(3.6)–(3.9) construct at most sixty actual four-support vectors for every
legal $X$, and (5.2)–(5.8) exclude every finite complex three-support
decomposition of an actual legal $C_*$. Repeated eigenvalues, zero
parameters, zero terms and singular positive semidefinite boundaries
are included. There is no remaining mathematical construction or
exclusion obligation for this sharp maximum.

This establishes a maximum over the entire fiber, not a pointwise
classification of $k(C)$ for every member or a classification of all
maximizers. In particular, the use of one inherited negativity maximizer
does not classify the coherence numbers of all negativity maximizers.
The inherited edge/triangle examples retain their original two/three
values and ownership. No conclusion is made for different populations,
non-skew invisible directions, another coordinate basis, another
dimension, approximate population zeros or finite-sample substitutes
for exact source laws.

**注记 7.2（Evidence and source boundary）。** The proof evidence here consists
of the complete ordinary identities, spectral arguments and exact
inequalities in this source. External literature and nested operational
suppliers are not independently certified here. The new mathematical
conclusion is relative to the stated sources and exact domain; global
originality, Lean/kernel verification, physical realization, empirical
learning and completion of a wider research program are not asserted.
The conditional menu and port interpretations retain the hypotheses and
unresolved implementation boundaries of C-108–C-110.

## 追加锚（本行以下为增补区）
