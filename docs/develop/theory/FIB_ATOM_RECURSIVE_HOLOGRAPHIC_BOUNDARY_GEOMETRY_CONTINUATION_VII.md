# FIB atomic boundary geometry VII: pointwise number-orbit separability

**Convention 177.0 (Predecessor and numbering).** This volume continues
[Continuation VI, §§169–176](https://github.com/the-omega-institute/trureturing/blob/c420a44f812a4a41fafcb10a2a48995255fbd503/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md).
References numbered 139–176 refer to that volume; numbers 177–185 refer
to this volume. The sector orbit, tensor cut and PPT criterion of VI
§§169–170 are the prerequisites for the common-factor construction below.

## 177. AURIC FIB ATOM boundary geometry: finite number orbits and pointwise separability

The finite Gibbs construction of §§139–146 fixes a three-mode model with
one-particle Hamiltonian $H=I_3-|V\rangle\langle V|$, where $\|V\|=1$.
Its spectrum is $(0,1,1)$. Retaining the zero mode and all fermionic
occupations gives the sector weights

$$
N=0:(1),\qquad N=1:(1,t,t),\qquad
N=2:(t,t,t^2),\qquad N=3:(t^2),
\tag{177.1}
$$

where $t=e^{-\beta}\in(0,1]$, $s=1-t$, and $Z=2(1+t)^2$.
There is no chemical potential or sector conditioning.

Fix the A-first creation order $(\ell,r,R)$ and the ordinary tensor
identification

$$
|n_A,n_r,n_R\rangle
=(a_\ell^\dagger)^{n_A}(a_r^\dagger)^{n_r}
 (a_R^\dagger)^{n_R}|\Omega\rangle
=|n_A\rangle\otimes|n_r,n_R\rangle_B.
$$

Alice holds the single mode $\ell$; Bob holds $(r,R)$, with basis

$$
b_0=|00\rangle,\qquad b_1=|01\rangle\;(R),\qquad
b_2=|10\rangle\;(r),\qquad b_{12}=|11\rangle\;(r\wedge R).
$$

Thus the product order is
$(0b_0,0b_1,0b_2,0b_{12},1b_0,1b_1,1b_2,1b_{12})$.
Use sector orders $(\ell,R,r)$ for $N=1$ and
$(r\wedge R,\ell\wedge R,\ell\wedge r)$ for $N=2$.
Every transpose below is the ordinary transpose of Alice's matrix indices
in this fixed tensor identification.

**Notation 177.1 (Independent sector-orbit family of VI (169.2)).** Let
$v=(\alpha,u)$ and $w=(\gamma,h)$ be independent unit vectors in
$\mathbb C\oplus\mathbb C^2$. In the stated sector orders define

$$
R(v,w)=1\oplus(tI_3+s vv^*)\oplus(tI_3-ts ww^*)\oplus t^2,
\qquad \rho(v,w)=\frac{R(v,w)}Z.
\tag{177.2}
$$

By Continuation VI §169, (177.2) is the complete orbit with spectra
(177.1) under independent global $U(3)$ actions in the $N=1$ and $N=2$
sectors. This number-preserving orbit enlarges passive one-particle
operations. Its actions are not assumed to be local at $A|B$ or physically
available. The native model supplies the spectra and cut; independence of
the two rays remains the enlarged mathematical premise of VI (169.2).

The eigenvalues of $R$ are $1,1,t,t,t,t,t^2,t^2$. Hence $R\succ0$ and
$\operatorname{tr}R=Z$ throughout the stated range. Define

$$
x=|\alpha|^2,\qquad y=|\gamma|^2,\qquad z=|u^*h|^2,
\qquad \|u\|^2=1-x,\quad \|h\|^2=1-y.
\tag{177.3}
$$

Here $x,y,z$ are scalar data of the specified rays. Their use in a
separability test does not assert that they classify entire states under
local unitaries.

## 178. Matrix notation and the published Schur criterion

Put

$$
\begin{aligned}
D&=tI_2+suu^*,& E&=tI_2-tshh^*,\\
f&=s\bar\alpha u,& g&=-ts\bar\gamma h,\\
c&=t+sx,& b&=t(1-sy).
\end{aligned}
\tag{178.1}
$$

The vectors $f,g$ are columns. In the declared product order, the entire
matrix is

$$
R=\begin{pmatrix}
1&0&0&0&0&0&0&0\\
0&D_{11}&D_{12}&0&f_1&0&0&0\\
0&D_{21}&D_{22}&0&f_2&0&0&0\\
0&0&0&b&0&\bar g_1&\bar g_2&0\\
0&\bar f_1&\bar f_2&0&c&0&0&0\\
0&0&0&g_1&0&E_{11}&E_{12}&0\\
0&0&0&g_2&0&E_{21}&E_{22}&0\\
0&0&0&0&0&0&0&t^2
\end{pmatrix}.
\tag{178.2}
$$

Equivalently, in Alice blocks $`R=\begin{pmatrix}A_0&C\\C^*&A_1\end{pmatrix}`$,
with Bob block sizes $(1,2,1)$,

$$
A_0=\operatorname{diag}(1,D,b),\qquad
A_1=\operatorname{diag}(c,E,t^2),\qquad
C=\begin{pmatrix}0&0&0\\f&0&0\\0&g^*&0\end{pmatrix}.
\tag{178.3}
$$

In particular the original number-sector blocks are
$`\begin{pmatrix}c&f^*\\f&D\end{pmatrix}`$ and
$`\begin{pmatrix}b&g^*\\g&E\end{pmatrix}`$.
The conjugations in (178.2) are retained for arbitrary complex rays.

**Notation 178.1 (Schur data from Continuation VI §170).** The common-factor
construction uses the exact PPT criterion (170.1)–(170.5) of VI. In the
notation (178.1), its scalar quantities are

$$
\begin{aligned}
q_0&=f^*E^{-1}f
=\frac{s^2x}{t}\left((1-x)+\frac{sz}{t+sy}\right),\\
q_3&=\frac{g^*D^{-1}g}{t^2}
=\frac{s^2y}{t}\left((1-y)-\frac{sz}{t+s(1-x)}\right).
\end{aligned}
\tag{178.4}
$$

Thus $\rho^{T_A}\succeq0$ if and only if $q_0\le1$ and $q_3\le1$,
including equality. The same published block reduction has singleton
entries $c$ on $|1b_0\rangle$ and $b$ on $|0b_{12}\rangle$, and blocks

$$
M_0=\begin{pmatrix}1&f^*\\f&E\end{pmatrix}
\quad\text{on }(0b_0,1b_1,1b_2),\qquad
M_3=\begin{pmatrix}t^2&g^*\\g&D\end{pmatrix}
\quad\text{on }(1b_{12},0b_1,0b_2).
\tag{178.5}
$$

The published bounds $D\succeq tI_2$ and $E\succeq t^2I_2$ ensure
invertibility. For the endpoint calculations in the common-factor identity,
the rank-one inverse formulas are

$$
\begin{aligned}
D^{-1}&=\frac1t\left(I_2-
 \frac{s}{t+s(1-x)}uu^*\right),\\
E^{-1}&=\frac1t\left(I_2+
 \frac{s}{t+sy}hh^*\right).
\end{aligned}
\tag{178.6}
$$

Here $1-s\|h\|^2=t+sy$ and $t+s\|u\|^2=t+s(1-x)$ are
strictly positive. The Schur residuals $1-q_0$ and $t^2(1-q_3)$
from VI §170 enter the new product identity (180.1); the inverses in
(178.6) also give its original-state endpoint residuals (180.5).

## 179. One common factorization and eight product vectors

Let $\iota(a)=a_1b_1+a_2b_2$ embed $\mathbb C^2$ into Bob's
one-particle plane. Spectrally decompose the positive matrix

$$
D^{-1/2}ED^{-1/2}=U\Lambda U^*,\qquad
\Lambda=\operatorname{diag}(\lambda_1,\lambda_2),\qquad
\lambda_j>0,
$$

and set

$$
X=D^{1/2}U,\qquad x_j=Xe_j,\qquad
\eta=X^{-1}f,\qquad \zeta=X^{-1}g.
\tag{179.1}
$$

The columns $x_j$ are vectors, distinct from the scalar $x$ in (177.3).
One and the same invertible $X$ gives

$$
\begin{aligned}
D&=XX^*=\sum_{j=1}^2x_jx_j^*,&
E&=X\Lambda X^*=\sum_{j=1}^2\lambda_jx_jx_j^*,\\
f&=X\eta=\sum_{j=1}^2x_j\eta_j,&
g&=X\zeta=\sum_{j=1}^2x_j\zeta_j.
\end{aligned}
\tag{179.2}
$$

This common congruence is an algebraic factorization used in the proof.
It is not a transformation applied to the state or an assertion of
independent local symmetries in the particle sectors.

Define nonzero unnormalized product vectors

$$
\Psi_j=(|0\rangle+\sqrt{\lambda_j}|1\rangle)\otimes
\left(\frac{\bar\eta_j}{\sqrt{\lambda_j}}b_0
 +\iota(x_j)+\frac{\bar\zeta_j}{\sqrt{\lambda_j}}b_{12}\right).
\tag{179.3}
$$

For $k=0,1,2,3$ put

$$
A_k=\operatorname{diag}(1,i^k),\qquad
B_k=\operatorname{diag}(1,i^k,i^k,i^{2k}),\qquad L_k=A_k\otimes B_k,
$$

and use the finite product-phase average

$$
\mathcal T_4(Y)=\frac14\sum_{k=0}^3L_kYL_k^*.
\tag{179.4}
$$

This is the product-phase average of VI (173.3): for total numbers
$n,m\in\{0,1,2,3\}$,
$\frac14\sum_{k=0}^3i^{k(n-m)}=\delta_{nm}$.
It therefore deletes exactly the unequal-total-number coherences.
Each $L_k\Psi_j$ remains an ordinary product vector.
There are eight such vectors, without a real-phase restriction on
$\alpha,u,\gamma,h$.

## 180. The exact product-projector identity

Write $P_{ab}=|a\rangle\langle a|\otimes|b\rangle\langle b|$
for the normalized occupation-basis endpoint projectors.

**Theorem 180.1 (Common-factor product identity).** For every member of
(177.2), whether PPT or NPT, the following identity holds:

$$
\boxed{\begin{aligned}
R={}&\sum_{j=1}^2\mathcal T_4(|\Psi_j\rangle\langle\Psi_j|)
 +(1-q_0)P_{0b_0}\\
 &+\frac{t}{t+s(1-x)}P_{1b_0}
 +\frac{t^2}{t+sy}P_{0b_{12}}
 +t^2(1-q_3)P_{1b_{12}}.
\end{aligned}}
\tag{180.1}
$$

Proof. In the fixed sector orders the components of $\Psi_j$ are

$$
\begin{array}{c|c}
N&\text{component}\\ \hline
0&\bar\eta_j/\sqrt{\lambda_j}\\
1&(\bar\eta_j,x_j)^{\mathsf T}\\
2&(\bar\zeta_j/\sqrt{\lambda_j},\sqrt{\lambda_j}x_j)^{\mathsf T}\\
3&\bar\zeta_j
\end{array}
\tag{180.2}
$$

The phase average retains their four projectors and no cross-sector
terms. Within $N=1$ the lower-left column is $x_j\eta_j$ and the
upper-right row is $`\bar\eta_jx_j^*`$. Within $N=2$ these are
$x_j\zeta_j$ and $`\bar\zeta_jx_j^*`$: the two square-root factors
cancel. Summing over $j$ therefore gives exactly $`f,f^*,g,g^*`$.
In particular the minus sign and conjugations defining $g$ in (178.1)
are reconstructed, rather than removed by a change of phase convention.

Let $S=\sum_j\mathcal T_4(|\Psi_j\rangle\langle\Psi_j|)$.
The middle blocks are $D$ and $E$ by (179.2). All four endpoint sums are

$$
\begin{aligned}
\sum_j\frac{|\eta_j|^2}{\lambda_j}
 &=f^*X^{-*}\Lambda^{-1}X^{-1}f=f^*E^{-1}f=q_0,\\
\sum_j|\eta_j|^2
 &=f^*X^{-*}X^{-1}f=f^*D^{-1}f,\\
\sum_j\frac{|\zeta_j|^2}{\lambda_j}
 &=g^*X^{-*}\Lambda^{-1}X^{-1}g=g^*E^{-1}g,\\
\sum_j|\zeta_j|^2
 &=g^*X^{-*}X^{-1}g=g^*D^{-1}g=t^2q_3.
\end{aligned}
\tag{180.3}
$$

Here $`X^{-*}=(X^{-1})^*`$. Consequently the complete sector blocks of $S$
are

$$
S_{N=0}=q_0,\qquad
S_{N=1}=\begin{pmatrix}f^*D^{-1}f&f^*\\f&D\end{pmatrix},
$$

$$
S_{N=2}=\begin{pmatrix}g^*E^{-1}g&g^*\\g&E\end{pmatrix},\qquad
S_{N=3}=t^2q_3.
\tag{180.4}
$$

These equations account for every off-diagonal entry and for both
one-particle-plane diagonal blocks of (178.2). Only the four endpoint
diagonals can differ. Besides $1-q_0$ and $t^2(1-q_3)$, the differences
are the original-state Schur residuals

$$
\begin{aligned}
c-f^*D^{-1}f
 &=t+sx-\frac{s^2x(1-x)}{t+s(1-x)}
 =\frac{t}{t+s(1-x)},\\
b-g^*E^{-1}g
 &=t(1-sy)-\frac{ts^2y(1-y)}{t+sy}
 =\frac{t^2}{t+sy}.
\end{aligned}
\tag{180.5}
$$

For the first simplification, multiplying by $t+s(1-x)$ leaves
$t^2+ts=t$. For the second, multiplying by $t+sy$ leaves
$t[(1-sy)(t+sy)-s^2y(1-y)]=t^2$.
This establishes all remaining entries and proves (180.1).

## 181. The exact pointwise separable region

**Theorem 181.1 (Pointwise classification at the fixed finite cut).**
For every $0<t\le1$ and every pair of independent complex unit vectors
$v,w$ in (177.2),

$$
\boxed{\rho(v,w)\text{ is ordinary }A|B\text{ tensor-separable}
\ \Longleftrightarrow\ \rho(v,w)^{T_A}\succeq0
\ \Longleftrightarrow\ q_0\le1\ \text{and}\ q_3\le1.}
\tag{181.1}
$$

Whenever these conditions hold, at most twelve normalized pure product
projectors suffice for a convex decomposition of $\rho$.

Proof. Under the two inequalities, every residual coefficient in (180.1)
is nonnegative; the middle two coefficients are strictly positive for
$t>0$. Its other terms are the eight positive product projectors
$\frac14|L_k\Psi_j\rangle\langle L_k\Psi_j|$.
Dividing by $Z$ proves ordinary separability.

Explicitly, write $a_{jk}=A_k(|0\rangle+\sqrt{\lambda_j}|1\rangle)$
and let $b_{jk}$ be $B_k$ applied to the Bob factor in (179.3).
Normalize both factors separately. The corresponding convex weight is

$$
p_{jk}=\frac{(1+\lambda_j)}{4Z}
\left(\frac{|\eta_j|^2}{\lambda_j}+\|x_j\|^2
 +\frac{|\zeta_j|^2}{\lambda_j}\right).
\tag{181.2}
$$

The other four weights are the residuals in (180.1) divided by $Z$.
All weights sum to one by taking the trace of that identity.
Zero-weight endpoints may be omitted, giving at most twelve terms.
No minimal-length assertion is needed.

Conversely a pure product projector has partial transpose
$|\bar a\rangle\langle\bar a|\otimes|b\rangle\langle b|\succeq0$.
Convex sums preserve positivity. Thus separability implies PPT, and
the Schur criterion of VI §170, recalled in (178.4)–(178.5), supplies
the scalar equivalence.

**Proposition 181.2 (Realizable scalar region).** At fixed $t$, the exact
region of scalar data realized by separable members is

$$
\left\{(x,y,z):\ 0\le x,y\le1,\quad
0\le z\le(1-x)(1-y),\quad q_0(t,x,y,z)\le1,\quad
q_3(t,x,y,z)\le1\right\}.
\tag{181.3}
$$

Proof. The unit-vector conditions and Cauchy–Schwarz give the first three
bounds. Every triple satisfying them is realized. For $x<1$, choose

$$
\alpha=\sqrt x,\quad \gamma=\sqrt y,\quad
u=\begin{pmatrix}\sqrt{1-x}\\0\end{pmatrix},\quad
h=\begin{pmatrix}\sqrt{z/(1-x)}\\
\sqrt{1-y-z/(1-x)}\end{pmatrix}.
\tag{181.4}
$$

The square roots are nonnegative, the two full vectors have unit norm,
and $`|u^*h|^2=z`$. For $x=1$, necessarily $z=0$; use $u=0$ and
$h=(\sqrt{1-y},0)^{\mathsf T}$. Theorem 181.1 then proves necessity and
sufficiency of the remaining two bounds for every realization, including
complex ones with those data.

For interior $0<t<1$ and $0<x,y<1$, define

$$
\begin{aligned}
L_3&=\frac{t+s(1-x)}s
 \left((1-y)-\frac{t}{s^2y}\right),\\
U_0&=\frac{t+sy}s
 \left(\frac{t}{s^2x}-(1-x)\right).
\end{aligned}
$$

Equivalently, the exact allowed overlaps at those fixed $t,x,y$ form

$$
\max\{0,L_3\}\le z\le
\min\{(1-x)(1-y),U_0\},
\tag{181.5}
$$

with an empty region when the lower endpoint exceeds the upper endpoint.
This follows by solving $q_3\le1$ and $q_0\le1$ for $z$.
At fixed interior $t,x,y$, increasing overlap increases $q_0$ and
decreases $q_3$; both constraints must concern the same pair $u,h$.
The endpoint cases use (181.3) directly, without division by $x$, $y$ or $s$.

The uniform statement of §§171–172 has a different quantifier:
all independent-ray members are PPT and separable exactly when $t\ge1/3$.
Equation (181.1) instead decides each member, including $0<t<1/3$.
It is a theorem for (177.2), not a PPT-sufficiency theorem for arbitrary
$2\times4$ states.

## 182. Equality, vanishing couplings and finite-temperature endpoints

**Proposition 182.1 (No excluded finite-parameter degeneracies).**
The identity and classification include repeated $\lambda_j$, vanishing
$u,h,\alpha,\gamma$, all $x,y$ endpoints, $q_0=1$, $q_3=1$, and $t=1$.

Proof. Since $D,E\succ0$, the only spectral denominators in (179.3) are
positive $\sqrt{\lambda_j}$. An arbitrary orthonormal eigenbasis of
$D^{-1/2}ED^{-1/2}$ works, even when the eigenvalues coincide; no
eigenvalue difference is divided out. Invertibility of $X$ also makes
its columns nonzero, so both product factors are nonzero.
All other denominators are positive $t$, $t+s(1-x)$ or $t+sy$.
Vanishing couplings therefore require no limiting convention.

At $q_0=1$ or $q_3=1$ the associated endpoint coefficient is simply zero.
For example $(1,-E^{-1}f)^{\mathsf T}$ is a nullvector of $M_0$ when
$q_0=1$, and $(1,-D^{-1}g)^{\mathsf T}$ is a nullvector of $M_3$ when
$q_3=1$. The underlying $R$ remains positive definite for $t>0$.
Equality of a PPT constraint is not loss of rank of $\rho$.

At $t=1$, $s=0$, $D=E=I_2$, $f=g=0$, and $q_0=q_3=0$.
Take $U=I_2$, so $\lambda_j=1$ and $x_j=e_j$.
Then $\Psi_j=(|0\rangle+|1\rangle)\otimes b_j$, and its phase average
is $P_{0b_j}+P_{1b_j}$. The four residuals in (180.1) are all one.
Thus (180.1) is $R=I_8$, and $\rho=I_8/8$, independently of the rays.
The inverse arguments assume $t>0$ throughout; $t=0$ is outside the
parameter range of these statements.

## 183. Exact failures of the earlier sufficient residual certificate

The separate-coherence product construction in §173 leaves the two
operators on Bob's one-particle plane

$$
K_0=tI_2+\frac{st}{t+sx}uu^*-s^2y\,hh^*,\qquad
K_1=tI_2-s^2x\,uu^*-\frac{ts}{1-sy}hh^*.
\tag{183.1}
$$

Their joint positivity is sufficient for the decomposition in that
construction to be a separable one. It is not a necessary condition for
the state itself to be separable. The following examples prove this
failure with exact entries.

**Proposition 183.1 (A strictly PPT nonpassive member at $t=1/4$).**
Choose

$$
t=\frac14,\qquad v=\frac{(1,1,0)}{\sqrt2},\qquad
w=\left(\frac1{\sqrt2},\frac{\sqrt6}{4},\frac{\sqrt2}{4}\right).
\tag{183.2}
$$

Then $\rho$ is PPT and separable, while $K_1\not\succeq0$.

Proof. Both vectors have norm one, and
$x=y=1/2$, $z=3/16$. The actual blocks and columns are

$$
D=\begin{pmatrix}5/8&0\\0&1/4\end{pmatrix},\qquad
E=\frac1{128}\begin{pmatrix}23&-3\sqrt3\\-3\sqrt3&29\end{pmatrix},
$$

$$
f=\begin{pmatrix}3/8\\0\end{pmatrix},\qquad
 g=-\frac3{64}\begin{pmatrix}\sqrt3\\1\end{pmatrix},\qquad
 c=\frac58,\quad b=\frac5{32}.
\tag{183.3}
$$

In particular
$E^{-1}=\frac15\begin{pmatrix}29&3\sqrt3\\3\sqrt3&23\end{pmatrix}$.
Thus

$$
q_0=\frac9{64}\frac{29}5=\frac{261}{320}<1,\qquad
q_3=16\left(\frac{27}{4096}\frac85
 +\frac9{4096}\,4\right)=\frac{99}{320}<1.
\tag{183.4}
$$

Both Schur blocks are positive definite. In endpoint order
$(0b_0,1b_0,0b_{12},1b_{12})$, the residuals of (180.1) are

$$
\frac{59}{320},\qquad\frac25,\qquad\frac1{10},\qquad
\frac{221}{5120}.
\tag{183.5}
$$

All are positive, so Theorem 181.1 gives separability.
On the other hand (183.1) gives

$$
(K_1)_{11}=\frac14-\frac9{64}-\frac9{80}=-\frac1{320},\qquad
K_1=\begin{pmatrix}-1/320&-3\sqrt3/80\\-3\sqrt3/80&17/80\end{pmatrix}.
\tag{183.6}
$$

A negative diagonal entry precludes positive semidefiniteness.
For $0<t<1$, the passive exterior-power subset obeys
$w\sim Jv$, where
$J(\alpha,u_1,u_2)=(\bar\alpha,-\bar u_2,\bar u_1)$.
It consequently has $y=x$ and $z=0$. Here $z>0$, proving that the
example is nonpassive. It also has $t<1/3$.

**Proposition 183.2 (A second exact obstruction with unequal endpoint weights).**
Choose

$$
t=\frac1{10},\qquad
v=\frac{(1,\sqrt{19},0)}{\sqrt{20}},\qquad
w=\frac{(\sqrt5,2,1)}{\sqrt{10}}.
\tag{183.7}
$$

Then the same failure of necessity holds, with

$$
x=\frac1{20},\quad y=\frac12,\quad z=\frac{19}{50},\qquad
q_0=\frac{140049}{220000}<1,\quad
q_3=\frac{21951}{38200}<1.
\tag{183.8}
$$

Proof. The squared coordinates of each full vector sum to one, and
$z=(19/20)(4/10)=19/50$. Substitution in (178.4) gives (183.8).
The four residuals in (180.1), in the same order as (183.5), are

$$
\frac{79951}{220000},\qquad\frac{20}{191},\qquad
\frac1{55},\qquad\frac{16249}{3820000}.
\tag{183.9}
$$

They are all positive. In contrast, (183.1) yields the directly
reproducible diagonal entry

$$
(K_1)_{11}=\frac1{10}-\frac{1539}{40000}-\frac{18}{275}
=-\frac{1729}{440000}<0.
\tag{183.10}
$$

This is again a nonpassive member below $t=1/3$: $z>0$ and $x\ne y$.
Indeed $0<19/50<19/40=(1-x)(1-y)$, so its two middle vectors are
neither orthogonal nor collinear. Theorem 181.1 establishes separability.

Both propositions are counterexamples to necessity of $K_0,K_1\succeq0$.
They are separable states, not examples of PPT entanglement. The common
factorization in (179.2) lets one product direction carry both actual
couplings; a failure of the separate-coherence allocation does not
obstruct that identity.

## 184. Explicit witnesses when a PPT inequality fails

**Proposition 184.1 (Normalized Schur witnesses).** If $q_0>1$ or $q_3>1$,
an explicit decomposable entanglement witness detects the corresponding
state at the same fixed cut.

Proof. Define vectors in the original product coordinates by

$$
\chi_0=|0b_0\rangle-|1\rangle\otimes\iota(E^{-1}f),\qquad
\chi_3=|1b_{12}\rangle-|0\rangle\otimes\iota(D^{-1}g).
\tag{184.1}
$$

In the blocks (178.5) these are $(1,-E^{-1}f)^{\mathsf T}$ and
$(1,-D^{-1}g)^{\mathsf T}$, respectively. Hermiticity gives

$$
\begin{aligned}
\chi_0^*R^{T_A}\chi_0
 &=1-2f^*E^{-1}f+f^*E^{-1}EE^{-1}f=1-q_0,\\
\chi_3^*R^{T_A}\chi_3
 &=t^2-2g^*D^{-1}g+g^*D^{-1}DD^{-1}g=t^2(1-q_3).
\end{aligned}
\tag{184.2}
$$

Let

$$
n_0=\|\chi_0\|^2=1+f^*E^{-2}f,\qquad
n_3=\|\chi_3\|^2=1+g^*D^{-2}g,
$$

and set $\widehat\chi_i=\chi_i/\sqrt{n_i}$,
$W_i=(|\widehat\chi_i\rangle\langle\widehat\chi_i|)^{T_A}$.
These are Hermitian trace-one operators of the decomposable form
$Q^{T_A}$ with $Q\succeq0$. For every normalized product vector $a\otimes d$,

$$
\langle a\otimes d|W_i|a\otimes d\rangle
=|\langle\widehat\chi_i|\bar a\otimes d\rangle|^2\ge0.
$$

They therefore have nonnegative expectation on every separable state.
Self-adjointness of partial transpose for the trace pairing gives

$$
\operatorname{Tr}(W_0\rho)=\frac{1-q_0}{Zn_0},\qquad
\operatorname{Tr}(W_3\rho)=\frac{t^2(1-q_3)}{Zn_3}.
\tag{184.3}
$$

The relevant expectation is strictly negative when its inequality fails.
This proves entanglement on the complementary side of (181.1).
These vectors need not be eigenvectors of $R^{T_A}$; no optimal
negativity or optimal-witness assertion is implied.

## 185. Sources and mathematical scope

The native finite source is
[FIB ATOM Recursive Holographic Boundary Geometry, Continuation VI,
§§139–156](https://github.com/the-omega-institute/trureturing/blob/c420a44f812a4a41fafcb10a2a48995255fbd503/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md).
Equations (140.1), (141.1)–(141.3), and (142.1)–(142.2) supply,
respectively, the native rank-one one-particle Hamiltonian, the full finite
Gibbs spectrum and normalization, and the A-first occupation convention.
They do not specify arbitrary independent actions in the two
three-dimensional sectors.

The published prerequisite
[Continuation VI, §§169–176](https://github.com/the-omega-institute/trureturing/blob/c420a44f812a4a41fafcb10a2a48995255fbd503/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md)
supplies the complete number-preserving independent-ray orbit (169.2),
the exact PPT criterion (170.1)–(170.5), the uniform threshold (172.5),
the sufficient residual operators (173.4)–(173.6), and the passive Hodge
relation (174.1)–(174.3). Equations (177.2) and (178.4)–(178.5) retain
the family and Schur data as prerequisites of the common-factor argument.
The uniform threshold is used only to distinguish the all-members
quantifier from the individual-state classification; its proof is not
needed for (180.1) or (181.1). The complete orbit enlarges passive
one-particle operations and supplies no native physical control.

The common-factor product identity, the resulting pointwise region,
the exact failures of necessity in §183, and the Schur witnesses in §184
are source-specific algebraic deductions from this finite family.
Spectral decomposition, Schur complementation and positivity of product
projectors are established finite-dimensional tools. Their use does not
attach a literature-priority claim to these deductions or import a
stronger separability theorem for general $2\times4$ states.

Every conclusion concerns ordinary separability on the fixed
$\mathbb C^2_A\otimes\mathbb C^4_B$ occupation tensor with $0<t\le1$.
The product constituents in (179.3) can superpose local particle numbers.
Their convex representation supplies no number-SSR-legal preparation,
access or extraction protocol. The factorization of $D,E$ is proof
bookkeeping, and the independent global sector orbit is not identified
with native physical control. The native $G_q$ image is not identified
with that entire orbit. Changes of tensor convention, additional copies,
fermionic composition laws, infinite inverse temperature and larger
models require their own hypotheses and arguments.

## 185.99 追加锚（本行以下为增补区）
