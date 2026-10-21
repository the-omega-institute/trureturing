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

## 186. Native-filter covariance and discord: source and normalized cut

**Definition 186.1 (Native prerequisites and normalized coordinates).**
Use the stopped history and metric family of Continuation VI,
§§139–140 [N]. The source is the stopped singleton substitution
$\beta_{\mathrm{src}}\mapsto\langle\beta_{\mathrm{src}},\alpha\rangle$,
with its two actual children, at the first accepted epoch. The source symbol
$\beta_{\mathrm{src}}$ is distinct from inverse temperature. In actual-coordinate
order $(r,\ell,R)$, retain the native data

$$
T=\begin{pmatrix}1\\1\\1\end{pmatrix},\quad
W=\begin{pmatrix}1&0&0\\1&1&0\\1&0&1\end{pmatrix},\quad
L_\star=\begin{pmatrix}2&-1&-1\\-1&1&0\\-1&0&1\end{pmatrix}.
$$

The old scalar norm and child residual metric are $G_0=[1]$ and $K=I_2$.
For $q=(u,v)^{\mathsf T}$ put $\pi_q=(1-u-v,u,v)^{\mathsf T}$ and

$$
G_q=L_\star+\pi_q\pi_q^{\mathsf T},\qquad
W^{\mathsf T}G_qW=
\begin{pmatrix}1&q^{\mathsf T}\\q&I_2+qq^{\mathsf T}\end{pmatrix}.
$$

Equations VI (139.2)–(139.3) give

$$
G_qT=\pi_q,\qquad T^{\mathsf T}G_qT=1,\qquad
Q_q=T\pi_q^{\mathsf T}-I_3,\qquad G_qQ_q=-L_\star.
$$

Thus the occurrence form, inherited norm and accepted history remain fixed
while the metric varies. The native instances are

$$
q_a=(1/6,1/6)^{\mathsf T},\quad \pi_a=(2/3,1/6,1/6)^{\mathsf T},\qquad
q_b=(1/3,1/3)^{\mathsf T},\quad \pi_b=T/3,
$$

$$
G_a=\frac1{36}\begin{pmatrix}88&-32&-32\\-32&37&1\\-32&1&37\end{pmatrix},
\qquad
G_b=\frac1{9}\begin{pmatrix}19&-8&-8\\-8&10&1\\-8&1&10\end{pmatrix}.
$$

Every off-diagonal rate $(Q_q)_{ij}=(\pi_q)_j$ is positive for these two
instances. Their finite generators are conservative and irreducible; this
is a statement about the stopped history, not about subsequent epochs.

Use the positive principal square root of VI (140.1), $S_q=G_q^{1/2}$, normalize by
$z_{\mathrm{coord}}=S_qx$, and complexify to standard $\mathbb C^3$.
The vectors $V_q=S_qT$ have norm one. Because $S_q^{-1}\pi_q=S_qT$,

$$
H_q=S_q^{-1}L_\star S_q^{-1}=I_3-V_qV_q^*,\qquad
\operatorname{spec}H_q=\{0,1,1\}.
$$

The principal root fixes the coordinate model; an arbitrary metric factor
followed by an unspecified unitary would not fix the cut. Equations VI (140.2)–(140.4) fix the principal-root vectors and cut:

$$
V_a=\frac{(10,7,7)^{\mathsf T}}{\sqrt{198}},\qquad V_b=\frac T{\sqrt3},\qquad
\mathfrak h_A=\mathbb C e_\ell,\quad
\mathfrak h_B=\operatorname{span}_{\mathbb C}\{e_r,e_R\},
$$

$$
p_q=|(V_q)_\ell|^2,\qquad p_a=\frac{49}{198},\qquad p_b=\frac13.
$$

This is the source-defined common cut of the normalized principal-root axes.
It does not identify raw weighted occurrence spans with orthogonal or physical
subsystems. The family parameter $p\in[0,1]$ used below extends the algebraic
formulas beyond these native instances. No assertion identifies that entire
interval with the image of admissible native $q$.

## 187. Full Gibbs preparation and the active/spectator correspondence

**Definition 187.1 (Full Gibbs state and aligned representation).**
Let $\beta\ge0$ be finite and $t=e^{-\beta}\in(0,1]$.
Retain the full preparation of VI §§141–142, not a sector-conditioned
replacement. Keep all eight states of $\mathcal F_-(\mathbb C^3)$, including the zero
mode, vacuum and every number sector. There is no chemical potential or
preconditioning. The preparation is

$$
\rho_{q,\beta}=\frac{e^{-\beta d\Gamma_-(H_q)}}{Z_\beta},\qquad
Z_\beta=\sum_{m_0,m_1,m_2\in\{0,1\}}t^{m_1+m_2}=2(1+t)^2.
$$

The zero-mode occupation is $1/2$, and each unit-energy mode has occupation
$t/(1+t)$. The common spectral quantities therefore include

$$
\langle\widehat H\rangle=\frac{2t}{1+t},\qquad
\langle\widehat N\rangle=\frac12+\frac{2t}{1+t},\qquad
\Pr(111)=\frac{t^2}{2(1+t)^2}.
$$

These equalities do not determine coordinate correlations or local occupations.
In covariance convention $C_{ij}=\operatorname{Tr}(\rho a_j^\dagger a_i)$,

$$
C_{q,\beta}=\frac{t}{1+t}I_3+
 \left(\frac12-\frac{t}{1+t}\right)V_qV_q^*.
$$

In the A-first CAR order $(A,r,R)$, a Bob number-preserving rotation is
generated by even bilinears. For example $a_i=Z_A\otimes b_i$ for a Bob
annihilator, so $a_i^\dagger a_j=I_A\otimes b_i^\dagger b_j$ for Bob
indices. Its lift is an ordinary Bob-local unitary; an odd annihilator
itself does not have that ordinary locality property.

Write the old Bob coordinate column as

$$
V_{B,q}=\begin{pmatrix}(V_q)_r\\(V_q)_R\end{pmatrix},
\qquad \nu_q=\|V_{B,q}\|=\sqrt{1-p_q}.
$$

For the two native instances,

$$
V_{B,a}=\frac{(10,7)^{\mathsf T}}{\sqrt{198}},\quad
\nu_a=\sqrt{\frac{149}{198}},\qquad
V_{B,b}=\frac{(1,1)^{\mathsf T}}{\sqrt3},\quad
\nu_b=\sqrt{\frac23}.
$$

The displayed matrices are **basis matrices**: their first and second
columns are the aligned active and spectator basis vectors in the old
$(r,R)$ basis,

$$
U_{B,a}=\frac1{\sqrt{149}}\begin{pmatrix}10&-7\\7&10\end{pmatrix},\qquad
U_{B,b}=\frac1{\sqrt2}\begin{pmatrix}1&-1\\1&1\end{pmatrix}.
$$

Thus the coordinate action is $x_B\mapsto U_{B,q}^*x_B$, not
$x_B\mapsto U_{B,q}x_B$. In particular,

$$
U_{B,q}^*V_{B,q}=\begin{pmatrix}\nu_q\\0\end{pmatrix}.
$$

To include Alice while retaining the original coordinate order $(r,\ell,R)$,
let the columns of

$$
J_q=
\begin{pmatrix}
0&(U_{B,q})_{11}&(U_{B,q})_{12}\\
1&0&0\\
0&(U_{B,q})_{21}&(U_{B,q})_{22}
\end{pmatrix}
$$

be the aligned ordered basis $(A,b,s)$. Then, with $p_q=|(V_q)_\ell|^2$,

$$
J_q^*V_q=(\sqrt{p_q},\sqrt{1-p_q},0)^{\mathsf T},\qquad
J_q^*H_qJ_q
=I_3-(J_q^*V_q)(J_q^*V_q)^*
=H_{\mathrm{eff}}(p_q)\oplus[1],
$$

where

$$
H_{\mathrm{eff}}=I_2-v_pv_p^*,\qquad
v_p=(\sqrt p,\sqrt{1-p})^{\mathsf T},\qquad
e^{-\beta H_{\mathrm{eff}}}=tI_2+(1-t)v_pv_p^*.
$$

The complex conjugation in these formulas is part of the convention: for a
possibly complex basis matrix the transformed one-particle operator is
$U_B^*H_BU_B$ and the transformed vector is $U_B^*V_B$; the two displayed
native matrices happen to be real, so $U_B^*=U_B^{\mathsf T}$.

The corresponding Fock operation is the even, number-preserving Bob-local
lift

$$
\mathbb U_{B,q}=\Gamma_-(I_{\mathfrak h_A}\oplus U_{B,q})
\quad\text{in A-first order }(A,r,R).
$$

Equivalently, if $b^\dagger$ and $s^\dagger$ denote creation in the two
columns of $U_{B,q}$, then
$\mathbb U_{B,q}r^\dagger\mathbb U_{B,q}^\dagger=b^\dagger$ and
$\mathbb U_{B,q}R^\dagger\mathbb U_{B,q}^\dagger=s^\dagger$.
The aligned-coordinate representative is therefore

$$
\rho^{\mathrm{al}}_{q,\beta}
=\mathbb U_{B,q}^\dagger\rho_{q,\beta}\mathbb U_{B,q}
=\frac{e^{-\beta d\Gamma_-(H_{\mathrm{eff}}(p_q)\oplus[1])}}{Z_\beta}.
$$

After the fixed coordinate reordering to creation order $(A,b,s)$, this is
the exact Bob-local factorization
$\rho^{\mathrm{al}}\simeq\sigma_\beta(p)\otimes\tau_\beta$ used below.
The reordering is only a CAR coordinate convention; its occupation-ket signs
are the passive signs displayed later and do not implement an unsigned swap or
a nonlocal replacement of the cut.

In the notation of VI (142.6) and (148.1)–(148.3), with $D=2(1+t)$,

$$
\sigma=\begin{pmatrix}a&0&0&0\\0&b&z&0\\0&\overline z&c&0\\0&0&0&d\end{pmatrix},\quad
\tau=\operatorname{diag}(r_0,r_1),\qquad
r_0=\frac1{1+t},\quad r_1=\frac t{1+t},
$$

$$
a=\frac1D,\quad b=\frac{1-(1-t)p}{D},\quad
c=\frac{t+(1-t)p}{D},\quad d=\frac tD,\quad
z=\frac{(1-t)\sqrt{p(1-p)}}D.
$$

The effective occupation order is $(|00\rangle,|01\rangle,|10\rangle,|11\rangle)$;
$z$ is real and nonnegative in this convention. The entries follow from the
vacuum weight $1$, double-occupation weight $t$, and displayed one-particle
exponential, with effective partition function $2(1+t)$.

For compact formulas set

$$
g=(1-t)^2p(1-p),\quad v=t+(1-t)p,\quad
A=ad=\frac{t}{4(1+t)^2},\quad
\mu=|z|^2=\frac{g}{4(1+t)^2},\quad
E=ac=\frac{v}{4(1+t)^2}.
$$

Here $A$ denotes the scalar $ad$; the party is Alice. Direct multiplication gives
$bc=A+\mu$, so $S=ad+bc=2A+\mu$. This identity is specific to the stated
Gibbs family, not to an arbitrary mixed X state.

## 188. Compatible preparations and coherent local-number filtering

**Assumption 188.1 (Compatible preparations and operation menu, VI §147).**
Use two independently prepared instances of the same specified $q,\beta$,
with compatible labelled CAR modes and coupling phase. This is neither cloning
nor a product of different native models. The untwirled even CAR product is
formed before imposing one common total-number SSR per party:

$$
\mathcal G_N(X)=\int_0^{2\pi}\!\int_0^{2\pi}
 e^{i\theta N_A^{\mathrm{tot}}}e^{i\phi N_B^{\mathrm{tot}}}
 X e^{-i\phi N_B^{\mathrm{tot}}}e^{-i\theta N_A^{\mathrm{tot}}}
 \frac{d\theta\,d\phi}{(2\pi)^2}.
$$

Independent, unrecorded local phase randomization of the two preparations
would remove their useful relative coherence and specifies a different input.
Allowed mathematical resources include joint handling of a party's modes,
number-preserving rotations and phases, coherent projections onto degenerate
local-number spaces, local discard, classical communication and heralding.
The instrument $X\mapsto FXF$ preserves selected rail coherence. Resolving
every individual occupation first and forgetting the outcome does not.
Availability of these preparations and instruments is an additional
physical premise, separate from the finite matrix assumptions.

**Definition 188.2 (Effective and full coherent filters).** Procedure E
aligns Bob's modes, discards each spectator and projects onto
$N_A^{\mathrm{tot}}=N_b^{\mathrm{tot}}=1$. Procedure F instead acts on the
full native normalized modes with the common projector

$$
F=\Pi_{n_{A_1}+n_{A_2}=1}
 \Pi_{n_{r_1}+n_{R_1}+n_{r_2}+n_{R_2}=1}.
$$

It counts all four Bob modes and is $q$ independent. Bob's number-preserving
alignments commute with it. Alice's selected space has dimension two; Bob's
full selected space has dimension four. Local matrices inside these spaces
have number-preserving extensions, and Hermitian rail witnesses are legal
within this resource menu. The analyzer for the active direction can depend
on $q$; a common unknown-$q$ active decoder is not supplied.

Both success projectors select fixed total number on each party. The phase
conjugations in $\mathcal G_N$ are therefore scalar on their selected
spaces, so $F\mathcal G_N(X)F=FXF$, and likewise for E's projector.
The common SSR does not remove the selected middle coherence.

All these filters and rotations also preserve local parity, but a full
total-parity twirl is a different state map from $\mathcal G_N$. The
conditional outcomes considered here do not identify those two total states.

## 189. Actual success blocks in the fixed CAR convention

**Notation 189.1 (Success blocks of VI §§149–151).**
Use the following supplier blocks with their literal CAR signs.
Regrouping the effective creation order $(A_1,b_1,A_2,b_2)$ into party
order $(A_1,A_2,b_1,b_2)$ multiplies an occupation ket by
$(-1)^{n_{b_1}n_{A_2}}$. For the full order
$(A_1,b_1,s_1,A_2,b_2,s_2)$ the sign is
$(-1)^{(n_{b_1}+n_{s_1})n_{A_2}}$. These are passive coordinate signs,
not physical nonlocal unitaries or unsigned swaps.

In the dual-rail product basis
$(|A_1b_1\rangle,|A_1b_2\rangle,|A_2b_1\rangle,|A_2b_2\rangle)$,
procedure E has the unnormalized success block of VI (149.4)–(149.6)

$$
C_-=
\begin{pmatrix}A&0&0&0\\0&bc&-\mu&0\\0&-\mu&bc&0\\0&0&0&A\end{pmatrix}
=A I_4+2\mu|\psi^-\rangle\langle\psi^-|,
\qquad
|\psi^-\rangle=\frac{|A_1b_2\rangle-|A_2b_1\rangle}{\sqrt2}.
$$

The outer populations are $ad$, from double occupation of one preparation
and vacuum of the other. Each middle population is $bc$. Their coherence
is $z\overline z$ before regrouping; the ket with $b_1,A_2$ occupied
has the negative CAR sign, yielding $-\mu$ as displayed.
The legal Alice-local phase $e^{i\pi n_{A_2}}$ reverses this sign and
preserves all quantities evaluated here.

In the aligned full proof basis define
$B_{\mathrm{act}}=\operatorname{span}\{|b_1\rangle,|b_2\rangle\}$ and
$B_{\mathrm{sp}}=\operatorname{span}\{|s_1\rangle,|s_2\rangle\}$.
Both spectators are empty on the active block. If one spectator is occupied,
the selected Bob number excludes every active Bob particle. Each of the four
remaining configurations $(A_i,s_j)$ has population $ac\,r_0r_1$.
The diagonal spectator input permits neither coherence between these flags
nor coherence linking them to the active block. Thus the full supplier block VI (151.3) is

$$
\Omega_F=r_0^2 C_-\ \oplus_B\ E r_0r_1 I_{A\otimes B_{\mathrm{sp}}}.
$$

This is a direct sum on Bob, not an additional postselection. It displays
every selected population. With

$$
Q_E=2t+g,\qquad Q_F=2t+g+2tv,
$$

the raw success probabilities VI (150.1), (151.4) become

$$
P_E=\operatorname{Tr}C_-=2S=\frac{Q_E}{2(1+t)^2},\qquad
P_F=\operatorname{Tr}\Omega_F=r_0^2P_E+4E r_0r_1
 =\frac{Q_F}{2(1+t)^4}.
$$

They lie strictly between zero and one: the finite-temperature input is
positive definite, and both the success and failure subspaces are nonempty.
No preliminary standard-form filter is performed or hidden in either value.

## 190. Conditional states, active weight and finite ranks

**Definition 190.1 (Conditional parameters and states).**
Normalize the success blocks and define

$$
\lambda=\frac{\mu}{S}=\frac{g}{Q_E},\qquad
w=\frac{r_0^2P_E}{P_F}=\frac{S}{S+2tE}=\frac{Q_E}{Q_F},\qquad
\eta=w\lambda=\frac{g}{Q_F}.
$$

Since $t>0$ and $v>0$, one has $0<w<1$ and
$0\le\eta\le\lambda<1$; $\eta<\lambda$ when $g>0$.
The states are

$$
\rho_E=W_\lambda=\frac{1-\lambda}{4}I_4+
 \lambda|\psi^-\rangle\langle\psi^-|,\qquad
\rho_F=wW_\lambda\ \oplus_B\ (1-w)\frac{I_{A\otimes B_{\mathrm{sp}}}}4.
$$

**Theorem 190.2 (Conditional marginals and finite ranks).**
The effective and full states have ranks four and eight, respectively.
Alice's marginal is $I_2/2$ in both cases. Bob's is $I_2/2$ for E, and

$$
(\rho_F)_B=\frac w2 I_{B_{\mathrm{act}}}\oplus_B
 \frac{1-w}{2}I_{B_{\mathrm{sp}}}
$$

for F. The flag alone is independent of Alice: each flag sector has Alice
marginal $I_2/2$. Nevertheless, it affects Bob's population information,
the success probability and the dilution of active correlations. The effective
state depends on $p$ through $p(1-p)$; $w$ also depends on $v=t+(1-t)p$.

Proof. Taking the partial traces of the two blocks gives the displayed
marginals and flag independence. The spectrum of $C_-$ is $A$ three times and $A+2\mu$ once. Since $A>0$
and $E r_0r_1>0$, the normalized effective and full states have ranks
four and eight, respectively, throughout this finite domain. Rank three
below refers only to the connected Pauli correlation tensor when $g>0$.

## 191. Diagnostic conventions and the two-qubit supplier boundary

**Definition 191.1 (Covariance, normalized Hilbert–Schmidt discord and negativity).**
For a normalized state on $\mathbb C^2\otimes\mathbb C^d$, define

$$
\operatorname{Cov}_\rho(X,Y)=\operatorname{Tr}\rho(X\otimes Y)
 -\operatorname{Tr}\rho(X\otimes I)\operatorname{Tr}\rho(I\otimes Y),
$$

$$
C_M(\rho)=\sup_{\substack{X\in M_2(\mathbb C),\,Y\in M_d(\mathbb C)\\
 \|X\|_{\mathrm{op}}=\|Y\|_{\mathrm{op}}=1}}
 |\operatorname{Cov}_\rho(X,Y)|,
\qquad
D_G^A(\rho)=2\inf_{\{P_+,P_-\}}
 \|\rho-\mathcal M_P(\rho)\|_{\mathrm{HS}}^2,
$$

$$
\mathcal M_P(\rho)=\sum_{\epsilon=\pm}
 (P_\epsilon\otimes I)\rho(P_\epsilon\otimes I),\qquad
\mathcal N(\rho)=\frac{\|\rho^{T_A}\|_1-1}{2}.
$$

The covariance domain includes non-Hermitian complex matrices. The discord
infimum includes every rank-one projective basis on Alice; the factor two
is the measured-qubit normalization. Write $C_j,D_j,\mathcal N_j$ for
these quantities on $\rho_j$, $j=E,F$, and $(x)_+=\max\{x,0\}$.

**Convention 191.2 (Normalization and supplier domains).**
Gwóźdź--Jakóbczyk [G], Eqs. (II.1), (II.9) and (II.15), supply these
discord and covariance conventions, but their negativity is
$\mathcal N_{\mathrm{paper}}=\|\rho^{T_A}\|_1-1=2\mathcal N$.
Their Eq. (II.23) establishes the first correlation--discord inequality
for Bell-diagonal states; its extension to arbitrary mixed two-qubit states
is presented there as a numerical expectation. It is not a general proof
supplied by that paper.

The two-qubit result [R] states
$\sqrt{D_G^A(\rho)}\le C_M(\rho)$ for positive semidefinite trace-one
two-qubit matrices, with the same full complex optimization domain. Its scope
is two qubits. The calculations below give matching upper bounds and
attainers for E and directly for this particular $2\times4$ family F.
The latter is not an instantiation of a two-qubit definition with Bob's
dimension changed, nor a generic $2\times4$ theorem.

The distinct trace-norm functional in [T] is

$$
D_1^A(\rho)=\inf_P\|\rho-\mathcal M_P(\rho)\|_1,
$$

with the unhalved trace norm. Its comparison $D_1^A\le C_M$ uses
the same all-complex covariance domain on two qubits. It is a different
functional from $D_G^A$ and supplies no $2\times4$ comparison for F.

## 192. Complete complex-operator covariance optimization

**Theorem 192.1 (Complete complex-operator covariance).**
For the states of Definition 190.1, $C_E=\lambda$ and
$C_F=\eta=w\lambda$, including $g=0$.

Proof. Let $\sigma_1,\sigma_2,\sigma_3$ be the Pauli matrices and embed them on
Bob's active sector as $S_j=\sigma_j\oplus0_{B_{\mathrm{sp}}}$. The singlet
identity gives

$$
\rho_F-(\rho_F)_A\otimes(\rho_F)_B
 =-\frac\eta4\sum_{j=1}^3\sigma_j\otimes S_j.
$$

For E replace $(\eta,S_j)$ by $(\lambda,\sigma_j)$. This also shows that
the connected $3\times3$ tensor in the displayed active coordinates is
$-\eta I_3$ for F, and $-\lambda I_3$ for E.

Take arbitrary complex $X\in M_2$ and $Y\in M_4$ of operator norm one.
Compress $Y$ to $B_{\mathrm{act}}$, obtaining a contraction $B$ even if
$Y$ mixes the flag sectors. Write

$$
X=\alpha_0I+\sum_j\alpha_j\sigma_j,\qquad
B=\gamma_0I+\sum_j\gamma_j\sigma_j.
$$

All coefficients may be complex. Pauli orthogonality and $X^\dagger X\le I$,
$B^\dagger B\le I$ imply

$$
|\alpha_0|^2+\sum_j|\alpha_j|^2=\frac12\operatorname{Tr}(X^*X)\le1,
\qquad
|\gamma_0|^2+\sum_j|\gamma_j|^2=\frac12\operatorname{Tr}(B^*B)\le1.
$$

The connected operator pairs only with this compression. Scalar and spectator
terms cancel against the product of local expectations, while off-diagonal
flag blocks have zero trace pairing. Therefore

$$
\begin{aligned}
|\operatorname{Cov}_{\rho_F}(X,Y)|
 &=\eta\left|\sum_j\alpha_j\gamma_j\right|\\
 &\le\eta\left(\sum_j|\alpha_j|^2\right)^{1/2}
              \left(\sum_j|\gamma_j|^2\right)^{1/2}\le\eta.
\end{aligned}
$$

The pairing is bilinear, not Hermitian; the absolute-value inequality follows
from complex Cauchy--Schwarz applied after conjugating one vector. The
norm-one matrices $X=\sigma_3$ and $Y=\sigma_3\oplus0$ give covariance
$-\eta$, so the bound is attained. Omitting spectators gives the same
argument for E with $X=Y=\sigma_3$. Thus

$$
\boxed{C_E=\lambda,\qquad C_F=\eta=w\lambda.}
$$

Neither non-Hermitian matrices nor flag mixing can increase these values.

## 193. All covariance maximizers and every Alice projective basis

**Theorem 193.1 (All covariance maximizers).** When $g>0$, the
maximizing pairs are precisely the phased matching Pauli directions
displayed below, with an arbitrary spectator contraction for F.
When $g=0$, every admissible norm-one pair maximizes covariance.

Proof. Suppose $g>0$. Equality in the preceding chain forces the two traceless
coefficient norms to be one, $\alpha_0=\gamma_0=0$, and both
Hilbert--Schmidt contraction bounds to be equalities. Each singular value
of $X$ and $B$ is at most one, and the sum of their squared singular values
is two. Hence both matrices are traceless unitaries. A traceless $2\times2$
unitary has opposite eigenvalues, so its spectral decomposition has form
$e^{i\alpha}\mathbf n\cdot\sigma$ for a real unit vector $\mathbf n$.
Equality in the bilinear Cauchy--Schwarz bound aligns the two real directions;
a sign can be absorbed in the phases.

Consequently all E maximizers, and only those, are

$$
X=e^{i\alpha}\mathbf n\cdot\sigma,\qquad
Y=e^{i\gamma}\mathbf n\cdot\sigma,\qquad \mathbf n\in S^2.
$$

For F, write $Y=\begin{pmatrix}B&K\\L&Z\end{pmatrix}$ in flag order.
Since $B$ is unitary, $Y^\dagger Y\le I$ gives $L=0$ and $YY^\dagger\le I$ gives
$K=0$. Thus its complete maximizing form is

$$
X=e^{i\alpha}\mathbf n\cdot\sigma,\qquad
Y=e^{i\gamma}\mathbf n\cdot\sigma\ \oplus Y_{\mathrm{sp}},\qquad
\|Y_{\mathrm{sp}}\|_{\mathrm{op}}\le1.
$$

The displayed active block already makes $\|Y\|_{\mathrm{op}}=1$.
When $g=0$, the connected operator vanishes and every permitted norm-one
pair attains the zero supremum.

**Theorem 193.2 (Every-basis disturbance and saturation).**
For all the finite parameters of Definition 187.1,
$D_E=\lambda^2$ and $D_F=\eta^2=w^2\lambda^2$. Every Alice
rank-one projective basis attains the respective infimum.

Proof. Every rank-one Alice projective basis is represented by an axis
$\mathbf n\in S^2$:

$$
P_\pm=\frac{I\pm\mathbf n\cdot\sigma}{2},\qquad
\mathcal M_{\mathbf n}(\sigma_j)=n_j(\mathbf n\cdot\sigma).
$$

Basis-vector phases and permutations do not change this channel. Alice's
maximally mixed marginal makes the product-marginal term invariant. For F,

$$
\Delta_{\mathbf n}=\rho_F-\mathcal M_{\mathbf n}(\rho_F)
 =-\frac\eta4\sum_j
  (\sigma_j-n_j\mathbf n\cdot\sigma)\otimes S_j.
$$

Since $\operatorname{Tr}(\sigma_i\sigma_j)=\operatorname{Tr}(S_iS_j)
=2\delta_{ij}$, one obtains

$$
\begin{aligned}
\|\Delta_{\mathbf n}\|_{\mathrm{HS}}^2
 &=\frac{\eta^2}{4}\|I_3-\mathbf n\mathbf n^{\mathsf T}\|_F^2\\
 &=\frac{\eta^2}{4}(3-2+1)=\frac{\eta^2}{2}.
\end{aligned}
$$

It is independent of the entire projective basis. The normalization two
therefore gives $D_F=\eta^2$. Replacing $(\eta,S_j)$ by
$(\lambda,\sigma_j)$ gives $D_E=\lambda^2$. Every Alice projective
basis attains each infimum, including the $g=0$ cases. In particular,

$$
\boxed{D_E=\lambda^2,\quad D_F=w^2\lambda^2,\quad
 C_j-\sqrt{D_j}=C_j^2-D_j=0\quad(j=E,F).}
$$

## 194. Partial transpose and the flag dilution of negativity

**Theorem 194.1 (Flag dilution of negativity).** For the actual
conditional outputs,

$$
\mathcal N_E=\frac{(3\lambda-1)_+}{4},\qquad
\mathcal N_F=\frac{(3\eta-w)_+}{4}=w\mathcal N_E.
$$

Proof. Use the active spectrum VI (150.2) and the local direct sum
VI (151.3)–(151.5). Partial transpose moves the effective middle coherence to the outer corner.
Before normalization its eigenvalues are $bc,bc,A+\mu,A-\mu$.
Equivalently,

$$
\operatorname{spec}(\rho_E^{T_A})=
 \left\{\frac{1+\lambda}{4}\ \text{three times},\quad
        \frac{1-3\lambda}{4}\right\}.
$$

The local direct sum commutes with partial transpose on Alice, so

$$
\operatorname{spec}(\rho_F^{T_A})=
 \left\{\frac{w+\eta}{4}\ \text{three times},\quad
        \frac{w-3\eta}{4},\quad
        \frac{1-w}{4}\ \text{four times}\right\}.
$$

The unnormalized full spectrum is correspondingly $r_0^2bc$ twice,
$r_0^2(A+\mu)$, $r_0^2(A-\mu)$, and $E r_0r_1$ four times.
There is at most one negative eigenvalue, yielding

$$
\begin{aligned}
\mathcal N_E&=\frac{(\mu-A)_+}{P_E}
 =\frac{(g-t)_+}{2Q_E}=\frac{(3\lambda-1)_+}{4},\\
\mathcal N_F&=\frac{r_0^2(\mu-A)_+}{P_F}
 =\frac{(g-t)_+}{2Q_F}=\frac{(3\eta-w)_+}{4}
 =w\mathcal N_E.
\end{aligned}
$$

Separability below threshold can be seen constructively. Put
$P_{j,s}=(I+s\sigma_j)/2$ for $s=\pm1$. Direct expansion gives

$$
W_{1/3}=\frac16\sum_{j=1}^3\sum_{s=\pm1}P_{j,s}\otimes P_{j,-s}.
$$

For $0\le\lambda\le1/3$,
$W_\lambda=3\lambda W_{1/3}+(1-3\lambda)I_4/4$ is thus separable.
Embedding its Bob factors in $B_{\mathrm{act}}$ and adding the product
spectator block proves full-state separability. For $\lambda>1/3$, the
displayed effective and full partial transposes both have a negative eigenvalue
because $w>0$. This agrees with the two-qubit PPT theorem [P] on the active
block and requires no PPT-sufficiency assertion in dimension $2\times4$.

## 195. The actual full-flag threshold and finite-temperature cases

**Theorem 195.1 (Flag-dependent correlation threshold and finite cases).**
For the actual conditional outputs,

$$
\begin{aligned}
\rho_F\text{ entangled}
 &\Longleftrightarrow w-3\eta<0
 \Longleftrightarrow C_F>\frac w3
 \Longleftrightarrow D_F>\frac{w^2}{9},\\
\rho_E\text{ entangled}
 &\Longleftrightarrow C_E>\frac13
 \Longleftrightarrow D_E>\frac19.
\end{aligned}
$$

Proof. Theorem 194.1 gives the full-state corner eigenvalue; its
constructive block decomposition establishes separability on the
other side. In microscopic parameters both conditions reduce to

$$
\boxed{\mu>ad\ \Longleftrightarrow\ g>t
 \ \Longleftrightarrow\ 4p(1-p)\sinh^2(\beta/2)>1.}
$$

The last equivalence uses $(1-t)^2/t=4\sinh^2(\beta/2)$ with $t>0$.
For $0<p<1$ this is exactly

$$
\beta>\beta_c(p)=2\operatorname{arsinh}\frac1{2\sqrt{p(1-p)}},\qquad
\beta_{c,a}=2\operatorname{arsinh}\frac{99}{\sqrt{7301}},\quad
\beta_{c,b}=2\operatorname{arsinh}\frac3{2\sqrt2}.
$$

Since $p_a(1-p_a)<p_b(1-p_b)$, $\beta_{c,b}<\beta_{c,a}$.
For either procedure, both native outputs are separable for
$0\le\beta\le\beta_{c,b}$; only $q_b$ is entangled for
$\beta_{c,b}<\beta\le\beta_{c,a}$; both are entangled for finite
$\beta>\beta_{c,a}$. Equality is separable at each model's boundary.
The native generators are unaffected by the quantum postselection.

The remaining finite cases are explicit. One has $g=0$ exactly when
$\beta=0$ or $p\in\{0,1\}$. Both outputs are then product states and
$C=D=\mathcal N=0$. At $\beta=0$,

$$
\rho_E=I_4/4,\quad \rho_F=I_8/8,\quad P_E=1/4,\quad P_F=1/8.
$$

At $p=0$ one has $w=1/(1+t)$; at $p=1$ one has $w=1/2$.
Bob's marginal need not be maximally mixed, although the full state remains
product. At the nonzero boundary $g=t$, negativity vanishes but
$C_E=1/3$, $C_F=w/3$ and both discords are positive. Throughout
$0<g\le t$ the states are separable with strictly positive covariance
and discord. Thus neither positive discord nor saturation of
$C_M=\sqrt{D_G^A}$ identifies entanglement.

The unchanged constants $C_F>1/3$ and $D_F>1/9$ are sufficient because
$w<1$, but are not necessary. The native example below violates their
necessity. With the paper's doubled negativity convention, the exact gap is

$$
\boxed{\sqrt{D_j}-2\mathcal N_j=\frac{\min(g,t)}{Q_j},\qquad j=E,F.}
$$

Indeed, for $g\le t$ the left side is $g/Q_j$, while for $g>t$ it is
$g/Q_j-(g-t)/Q_j=t/Q_j$. At finite $t>0$ this gap vanishes exactly when
$g=0$. No $t=0$ state, limiting attainer or zero-temperature claim is used.

## 196. Alice dephasing, surviving covariance and the fixed-source input pair

**Theorem 196.1 (Output dephasing).** Dephasing Alice along any
$\mathbf n\in S^2$ preserves $C_E=\lambda$ and $C_F=\eta$,
while both resulting states have zero Alice discord and negativity.

Proof. After Alice dephases along any $\mathbf n\in S^2$, the full connected
operator is

$$
\mathcal M_{\mathbf n}(\rho_F)-(\rho_F)_A\otimes(\rho_F)_B
 =-\frac\eta4(\mathbf n\cdot\sigma)\otimes(\mathbf n\cdot S).
$$

For arbitrary complex norm-one local matrices its covariance is
$-\eta(\alpha\cdot\mathbf n)(\gamma\cdot\mathbf n)$, whose modulus
is at most $\eta$ by the same coefficient bounds. Choosing
$X=\mathbf n\cdot\sigma$ and $Y=\mathbf n\cdot S$ attains it.
The effective argument uses $\lambda$ and Bob's Pauli matrices instead.
Hence

$$
C_M(\mathcal M_{\mathbf n}(\rho_E))=\lambda,\qquad
C_M(\mathcal M_{\mathbf n}(\rho_F))=\eta.
$$

Both dephased states have zero Alice discord, since repeating the same
projective measurement leaves them unchanged. More explicitly, their active
part is diagonal in Alice's $\mathbf n$ basis and Bob's matching active
$\mathbf n$ basis, with conditional probabilities

$$
\Pr(\epsilon,\delta\mid\mathrm{act})=
 \frac{1-\lambda\epsilon\delta}{4},\qquad \epsilon,\delta\in\{\pm1\}.
$$

In F these probabilities have weight $w$; each spectator outcome pair has
probability $(1-w)/4$ in any spectator rail basis. These are product-basis
diagonal, classical--classical states, so their negativity is zero as well.
The total covariance in the displayed matching basis is $-\eta$ for F.
The flag remains independent of Alice. Maximal covariance can therefore
survive the removal of discord and entanglement in this precise family.

**Convention 196.2 (Fixed-source input comparison, VI §154).**
For the input comparison in [N, §154], the original
single-copy state $\rho$ and its Alice occupation dephasing
$\overline\rho=\mathcal D_A(\rho)$ agree on all single-copy local
SSR product-observable statistics. On one Alice mode, allowed local-number
observables are diagonal, so removing Alice's occupation off-diagonal blocks
does not change their product expectations. In the aligned coordinates,

$$
\overline\rho=|0\rangle\langle0|\otimes\operatorname{diag}(a,b)\otimes\tau
 +|1\rangle\langle1|\otimes\operatorname{diag}(c,d)\otimes\tau.
$$

Both Bob blocks are positive and commute with Bob number; normalizing each
nonzero block gives an explicit separable mixture. The original and dephased
preparations have effective factors $\sigma$ and $\operatorname{diag}(a,b,c,d)$.
Applying F to two compatible
preparations of either input gives the same success probability and diagonal
populations. The latter input has no active middle coherence.

On the chosen source's selected space the Hermitian witness

$$
\mathsf W=|A_1b_2\rangle\langle A_2b_1|
 +|A_2b_1\rangle\langle A_1b_2|
 =\frac{X_A\otimes X_b+Y_A\otimes Y_b}{2}
$$

uses rail Pauli operators $X,Y$, with Bob's operators zero on spectators,
and preserves local total number. Its conditional
expectations are $-2r_0^2\mu/P_F=-\eta$ and $0$, respectively, in the
literal CAR convention. Their difference for $\mu>0$ does not require
entanglement. This comparison uses one fixed $q,\beta$ and joint local
access; it does not identify $\overline\rho$ with the other native model
or claim that the original single-copy observation rule was already a
tensor-compatible process equivalence.

## 197. Raw joint laws, flag conditioning and postdephasing axes

**Theorem 197.1 (Raw joint laws and postdephasing axes).**
For Alice and active-Bob rail axes $\mathbf a,\mathbf m\in S^2$,
the actual raw laws are

$$
\Pr(E\text{ succeeds},\epsilon,\delta)
 =\frac{P_E}{4}(1-\lambda\epsilon\delta\,\mathbf a\cdot\mathbf m),
$$

$$
\begin{aligned}
\Pr(F\text{ succeeds},\mathrm{act},\epsilon,\delta)
 &=\frac{r_0^2P_E}{4}(1-\lambda\epsilon\delta\,\mathbf a\cdot\mathbf m),\\
\Pr(F\text{ succeeds},\mathrm{sp},\epsilon,\delta)&=E r_0r_1.
\end{aligned}
$$

Proof. Trace against $(I+\epsilon\mathbf a\cdot\sigma)/2$ and
$(I+\delta\mathbf m\cdot\sigma)/2$. Zero local Bloch vectors
and the singlet tensor give the active formulas. The spectator formula holds in every rank-one spectator rail basis. Summing
its four terms yields $4E r_0r_1$; summing the active terms yields
$r_0^2P_E$. Their sum is $P_F$. All terms are nonnegative because
$\lambda<1$, and failure probabilities are $1-P_E$ and $1-P_F$.
Conditioned on successful F, the flag weights are $w,1-w$; conditioning
further on the active flag gives $W_\lambda$. The probability of that
joint success event is $r_0^2P_E$, not $P_E$.

If Alice first dephases the selected output along $\mathbf n$, then measures
along a subsequent axis $\mathbf a$, replace $\mathbf a\cdot\mathbf m$
in these active laws by $(\mathbf a\cdot\mathbf n)(\mathbf n\cdot\mathbf m)$.
This follows by applying $\mathcal M_{\mathbf n}$ to the Alice Pauli
factor. Setting $\mathbf a=\mathbf n$ recovers the corresponding law
with Alice measured in her dephasing basis. An arbitrary other Alice axis
does not retain the undephased law. These aligned-source formulas supply
no common unknown-$q$ analyzer.

## 198. Success weighting and the quadratic subnormalization distinction

**Theorem 198.1 (Success weighting and subnormalized disturbance).**
The probability-weighted conditional quantities are

| Quantity | Procedure E | Procedure F |
| --- | --- | --- |
| $P C_M=P\sqrt{D_G^A}$ | $2\mu$ | $2r_0^2\mu$ |
| $P D_G^A$ | $4\mu^2/P_E=2\mu^2/S$ | $4r_0^4\mu^2/P_F$ |
| $P\mathcal N$ | $(\mu-A)_+$ | $r_0^2(\mu-A)_+$ |

Proof. These follow by inserting $\lambda=2\mu/P_E$ and
$\eta=2r_0^2\mu/P_F$ into the conditional formulas. They are finite
weighted state diagnostics. In particular, $C_M$ here is defined on
normalized states: substituting $X=P\rho$ into a trace-minus-product
expression scales its first term by $P$ and its expectation-product term
by $P^2$. Thus $P C_M$ is not assigned a raw-covariance interpretation.

The quadratic measurement disturbance has a different homogeneous law.
Linearity of every dephasing map gives, for a subnormalized $X=P\rho$,

$$
\mathfrak D(X):=2\inf_{\mathcal B}\|X-\mathcal M_{\mathcal B}(X)\|_{\mathrm{HS}}^2
 =P^2D_G^A(\rho).
$$

Here $\mathcal B$ ranges over Alice's rank-one projective bases and $P$
is the success probability. Consequently

$$
\mathfrak D(C_-)=4\mu^2,\qquad
\mathfrak D(\Omega_F)=4r_0^4\mu^2.
$$

The quantities $P D_G^A$ and $P^2D_G^A$ must be kept distinct. Conditioning
on the active flag also changes the state and its joint success probability;
it cannot justify attaching E's raw probability to F's active output.

## 199. Exact native covariance and discord at inverse temperature log 7

**Proposition 199.1 (Exact native comparison).** At $\beta=\log7$, one has
$t=1/7$, $(r_0,r_1)=(7/8,1/8)$ and $A=7/256$. The common spectral
quantities from VI (141.6) are $Z=128/49$, $\langle\widehat H\rangle=1/4$,
$\langle\widehat N\rangle=3/4$ and $\Pr(111)=1/128$.
The two source parameters give the exact effective entries

$$
\begin{aligned}
q_a:\quad &(a,b,c,d,z)=
 \left(\frac7{16},\frac{91}{264},\frac{41}{264},\frac1{16},
       \frac{7\sqrt{149}}{528}\right),\\
q_b:\quad &(a,b,c,d,z)=
 \left(\frac7{16},\frac5{16},\frac3{16},\frac1{16},\frac{\sqrt2}{8}\right).
\end{aligned}
$$

Their auxiliary values are

| Parameter | $q_a$, $p=49/198$ | $q_b$, $p=1/3$ |
| --- | --- | --- |
| $\mu$ | $7301/278784$ | $1/32$ |
| $E=ac$ | $287/4224$ | $21/256$ |
| $S$ | $22547/278784$ | $11/128$ |
| $\mu-A$ | $-161/139392$ | $1/256$ |
| $\mu/A$ | $1043/1089$ | $8/7$ |
| $w$ | $22547/27959$ | $11/14$ |

Proof. Insert the entries of Definition 187.1 and the native values
$p_a=49/198$, $p_b=1/3$ into the parameter definitions.
Substitution into Theorems 192.1–195.1 gives every conditional diagnostic:

| Native instance and procedure | Raw $P$ | $C_M=\sqrt{D_G^A}$ | $D_G^A$ | $\mathcal N$ | Minimum PT eigenvalue |
| --- | --- | --- | --- | --- | --- |
| $q_a$, E | $22547/139392$ | $1043/3221$ | $1087849/10374841$ | $0$ | $23/3221$ |
| $q_a$, F | $1369991/8921088$ | $7301/27959$ | $53304601/781705681$ | $0$ | $161/27959$ |
| $q_b$, E | $11/64$ | $4/11$ | $16/121$ | $1/44$ | $-1/44$ |
| $q_b$, F | $343/2048$ | $2/7$ | $4/49$ | $1/56$ | $-1/56$ |

For $q_a$, $\mu/A=1043/1089<1$: both outputs are separable with positive
covariance and discord. For $q_b$, $\mu/A=8/7>1$: both are entangled.
The full $q_b$ output nevertheless has

$$
C_F=\frac27<\frac13,\qquad D_F=\frac4{49}<\frac19,\qquad
\mathcal N_F=\frac1{56}>0.
$$

Its actual threshold is $w/3=11/42<2/7=12/42$, and

$$
\frac{3C_F-w}{4}=\frac{3(2/7)-11/14}{4}=\frac1{56}.
$$

This exact native example shows that the effective constants fail as
necessary full-state conditions. The unnormalized full PT spectrum
is $735/16384$ three times, $-49/16384$ once and $147/16384$ four times;
its trace is $343/2048$.

The exact weighted diagnostics and subnormalized disturbances are

| Native instance and procedure | $P C_M$ | $P D_G^A$ | $P\mathcal N$ | $P^2D_G^A$ |
| --- | --- | --- | --- | --- |
| $q_a$, E | $7301/139392$ | $7614943/448981632$ | $0$ | $53304601/19430129664$ |
| $q_a$, F | $357749/8921088$ | $2611925449/249424699392$ | $0$ | $127984347001/79585811103744$ |
| $q_b$, E | $1/16$ | $1/44$ | $1/256$ | $1/256$ |
| $q_b$, F | $49/1024$ | $7/512$ | $49/16384$ | $2401/1048576$ |

For the effective total-number twirl of VI (150.5), all sectors other than $(1,1)$
have a one-dimensional local factor, so its total negativity is
$(\mu-A)_+$, equal to $1/256$ for $q_b$. This is specifically the
effective total-number value, not the full parity-twirled total or a
six-mode unfiltered total.

Equal spectral quantities do not make the native models indistinguishable:
their allowed single-copy Alice occupations are $115/528$ and $1/4$.
The indistinguishability used in the fixed-source dephasing comparison
concerns $\rho$ and $\mathcal D_A(\rho)$ at one $q$, rather than the
pair $q_a,q_b$.

## 200. Mathematical suppliers and applicability

**Convention 200.1 (Prerequisites and mature projection method).**
The native geometry, Gibbs correspondence, CAR signs, common success block,
SSR menu and original negativity threshold are reused from [N]. The mature
mixed-state two-copy projection mechanism is due to Schuch--Verstraete--Cirac
[M]. Their Eq. (18) parameters correspond to

$$
w_{\mathrm{svc}}=\sqrt{ad/bc},\qquad
v_{\mathrm{svc}}=|z|/\sqrt{bc}.
$$

Their projected standard-form matrix has diagonal
$(w_{\mathrm{svc}}^2,1,1,w_{\mathrm{svc}}^2)$ and middle coherence
$v_{\mathrm{svc}}^2$. Up to the declared legal Alice phase, it is
proportional to $C_-/(bc)$. Squaring preserves
$v_{\mathrm{svc}}>w_{\mathrm{svc}}\Longleftrightarrow\mu>ad$.
Their $w_{\mathrm{svc}}$ is not the conditional flag weight $w$ in this
appendix, and no standard-form filtering success factor is part of $P_E,P_F$.

The two-qubit supplier [R] and the direct block calculation of the full
$2\times4$ family have distinct domains. The spontaneous-emission
dynamics of [G] is not a premise of this finite native model.

**Assumption 200.2 (Applicability).** The principal-root normalization and common cut are specified model data.
The compatible preparations, coherent joint local handling, filter
instruments and aligned analyzers are the specified mathematical resources.
Their physical availability is an additional premise. A common unknown-$q$ decoder remains unsupplied. The conclusions apply to these actual $2\times2$ and block-diagonal
$2\times4$ conditional states with finite $\beta\ge0$. They are
finite state diagnostics, with no extension here to a generic
$2\times4$ discord bound, general PPT sufficiency, deterministic
extraction, asymptotic rates, arbitrary copy counts or a physical clock.

**Convention 200.3 (Mathematical references and domains).**

- **[N] Native finite quantum application.**
  [FIB ATOM recursive holographic boundary geometry, continuation VI, §§139--156](https://github.com/the-omega-institute/trureturing/blob/7b9f7a9101eb8492eba6454a034434d3b53fc79d/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md).
  §§139--142 give the source, principal-root cut and full Gibbs factorization;
  §§147--151 give the two-preparation resource, CAR convention and common
  filter; §§152--155 give the thresholds and fixed-source comparison.
- **[G] M. Gwóźdź and L. Jakóbczyk.** *Spontaneous emission can locally
  create quantum discord out of classical correlations*,
  [arXiv:1306.0130v2](https://arxiv.org/pdf/1306.0130v2),
  DOI [10.1007/s11128-013-0639-0](https://doi.org/10.1007/s11128-013-0639-0).
  Eqs. (II.1), (II.9), (II.15) and (II.23) specify the definitions and
  Bell-diagonal versus numerically expected mixed-state comparison.
- **[R] Repository two-qubit correlation--discord result.**
  [Immutable declaration source](https://github.com/the-omega-institute/trureturing/blob/62da326eca057b3195bef4099cd0c6fcccc37c3c/D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.lean)
  and [matching mathematical exposition](https://github.com/the-omega-institute/trureturing/blob/62da326eca057b3195bef4099cd0c6fcccc37c3c/Blueprint/D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.md).
  The stated result concerns all two-qubit density matrices with the
all-complex local covariance domain and the normalized Hilbert–Schmidt
discord. The E family is within that domain; the F calculation is the
direct local-block proof of §§192–194.
- **[M] N. Schuch, F. Verstraete and J. I. Cirac.** *Quantum entanglement
  theory in the presence of superselection rules*,
  [quant-ph/0404079v1](https://arxiv.org/pdf/quant-ph/0404079v1),
  DOI [10.1103/PhysRevA.70.042310](https://doi.org/10.1103/PhysRevA.70.042310).
  PDF pp. 9--10, §§IV.D.1--IV.D.2, Eqs. (17)--(18), supply the mature
  mixed-state standard form and two-copy local one-particle projection.
- **[P] M. Horodecki, P. Horodecki and R. Horodecki.** *Separability of Mixed
  States: Necessary and Sufficient Conditions*,
  [quant-ph/9605038v2](https://arxiv.org/pdf/quant-ph/9605038v2),
  Theorem 3, PDF p. 8. Its PPT sufficiency applies in $2\times2$ and
  $2\times3$; full-state separability here follows from the explicit local
  direct sum and product decomposition.

- **[T] Two-qubit trace-norm comparison.**
  [Trace-norm discord and maximal mutual correlation](https://github.com/the-omega-institute/trureturing/blob/b02b98342945a1a724a227db4fa38e376640e573/Blueprint/D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.md),
  Definitions 1.1–1.2 and Theorem 1.3, states $D_1^A\le C_M$
  on two qubits with the unhalved trace norm and all-complex covariance
  domain. It concerns the trace-norm functional of Convention 191.2.

## 200.99 追加锚（本行以下为增补区）

## 201. Fixed model, cut, and assertion

**Definition 201.1 (The fixed independent-ray family).** Use the family,
one-copy occupation convention and sector bases of (177.2) and
(178.1)–(178.3). Fix $0<t\leq 1$, $s=1-t$, and

$$
 Z=2(1+t)^2.
$$

Let $v=(\alpha,u)$ and $w=(\gamma,h)$ be unit vectors in
$\mathbb C^3=\mathbb C\oplus\mathbb C^2$. Write

$$
 x=|\alpha|^2,\qquad y=|\gamma|^2,\qquad z=|u^*h|^2.
$$

The one-copy number blocks, in the supplied bases
$(\ell,R,r)$ for $N=1$ and $(r\wedge R,\ell\wedge R,\ell\wedge r)$ for
$N=2$, are

$$
 R=1\oplus(tI_3+s vv^*)\oplus(tI_3-ts ww^*)\oplus t^2,
 \qquad \rho=R/Z.
$$

The arbitrary global-number-preserving orbit is a premise of this manuscript. It is
separate from passive one-particle $\Gamma(U_3)$, native reachability, and local
SSR operations.

**Assumption 201.2 (Compatible preparations and local operations).**
The resource consists of two disjoint, independently prepared instances
of this same untwirled $\rho(t,v,w)$, with compatible labelled modes,
creation order and coupling-phase conventions, as in VI §147. One common local-number twirl is applied across
the two copies. Bob has all four modes, and local filters may be arbitrary
coherent contractions inside a fixed total local-number space. Independent
pre-twirling of the two inputs is a different resource. No cloning, external
reference, or additional physical access is included.

The original creation order is

$$
 (\ell _1,r_1,R_1,\ell _2,r_2,R_2),
$$

and the fixed ordinary tensor cut is

$$
 (\ell _1,\ell _2)\mid(r_1,R_1,r_2,R_2).
$$

Partial transpose below is the ordinary transpose on this Alice tensor factor
once the CAR coordinate convention has been fixed; it is not fermionic
partial time reversal. An encoded $2\times2$ branch has a two-dimensional
Alice rail space and a two-dimensional Bob space, each at fixed local
total number. For a normalized output $\sigma$, write

$$
 \mathcal N(\sigma)=\frac{\|\sigma^{T_A}\|_1-1}{2},
 \qquad [r]_+=\max\{r,0\}.
$$

**Theorem 201.3 (Finite two-copy extraction equivalence).** Under
Definition 201.1 and Assumption 201.2, the normalized common-twirled
resource $\Omega$ defined in (203.2) satisfies

$$
 \boxed{
 \Omega\text{ has an allowed positive-probability encoded NPT branch}
 \iff q_0>1\ \text{or}\ q_3>1.
 }
$$

This is exactly the ordinary one-copy NPT region of Theorem 181.1,
which also identifies ordinary one-copy PPT with separability for
this exact family. The complete common-twirled
state is PPT exactly when $q_0\leq1$ and $q_3\leq1$. The sector
$(N_A,N_B)=(1,2)$ has criterion $q_0q_3>1$, and therefore supplies no
additional activation region.

Proof. The signed charge reduction in §§203–206 and the local-filter
congruence in §207 give necessity. The explicit positive-probability
outer branches in §208 give sufficiency; §210 combines them.

## 202. One-copy coordinates and the two Schur parameters

**Notation 202.1 (Reused one-copy matrix data).** Retain (178.1)–(178.6)
and the criterion of VI §170, with $d=t^2$. Put
$H=\operatorname{span}\{R,r\}\cong\mathbb C^2$,
in the ordered basis $(R,r)$, and write

$$
 |0\rangle=|b_0\rangle,\qquad |2\rangle=|b_{12}\rangle=|r\wedge R\rangle.
$$

In the Bob order $(|0\rangle,H,|2\rangle)$, define

$$
\begin{aligned}
 D&=tI_2+suu^*,& E&=tI_2-ts\,hh^*,\\
 f&=s\overline{\alpha}\,u,& g&=-ts\overline{\gamma}\,h,\\
 c&=t+sx,& b&=t(1-sy),& d&=t^2.
\end{aligned}
$$

The Alice blocks of $R$ are

$$
 A_0=1\oplus D\oplus b,\qquad A_1=c\oplus E\oplus d,\qquad
 C=|f\rangle\langle0|+|2\rangle\langle g|,
$$

so that

$$
 R=\begin{pmatrix}A_0&C\\ C^*&A_1\end{pmatrix}.
 \tag{202.1}
$$

The number-block spectra are

$$
 \operatorname{spec}(R)=\{1,1,t,t,t,t,t^2,t^2\},\qquad
 \operatorname{tr}R=Z.
 \tag{202.2}
$$

Thus $R>0$ for $t>0$, while $D\geq tI_2$ and $E\geq t^2I_2$.
The original positive blocks give the strict Schur inequalities

$$
 cD-ff^*>0,\qquad bE-gg^*>0. \tag{202.3}
$$

Define

$$
 q_0=f^*E^{-1}f,\qquad q_3={g^*D^{-1}g\over d}. \tag{202.4}
$$

The inverse rank-one formulas are

$$
 E^{-1}={1\over t}\left(I_2+{s\,hh^*\over t+sy}\right),\qquad
 D^{-1}={1\over t}\left(I_2-{s\,uu^*\over t+s(1-x)}\right),
$$

so

$$
 q_0={s^2x\over t}\left((1-x)+{sz\over t+sy}\right),\qquad
 q_3={s^2y\over t}\left((1-y)-{sz\over t+s(1-x)}\right). \tag{202.5}
$$

The published ordinary one-copy partial-transpose reduction
(178.4)–(178.5), equivalently VI (170.1)–(170.5), has positive singleton
blocks $c,b$, and nontrivial blocks

$$
 \begin{pmatrix}1&f^*\\f&E\end{pmatrix},\qquad
 \begin{pmatrix}d&g^*\\g&D\end{pmatrix}.
$$

Its Schur criterion is

$$
 \rho^{T_A}\geq0\iff q_0\leq1\text{ and }q_3\leq1. \tag{202.6}
$$

## 203. Literal CAR regrouping and the common twirl

**Proposition 203.1 (Signed 64-dimensional resource law).** For
occupations $a_i=n_{\ell_i}$ and $k_i=n_{r_i}+n_{R_i}$, moving
$\ell _2$ left across the occupied first-copy Bob modes gives exactly

$$
 J|a_1,j;a_2,k\rangle=(-1)^{k_1a_2}|a_1,a_2;j,k\rangle,\qquad
 \boxed{(-1)^{(n_{r_1}+n_{R_1})n_{\ell_2}}}. \tag{203.1}
$$

Proof. Moving $\ell_2$ to the stated Alice position crosses each
occupied first-copy Bob mode once. CAR anticommutation contributes
one minus sign per crossing. There is no further permutation within
either Bob copy. $J$ is a signed
permutation of the 64 occupation kets; it is not asserted to factor across the
Alice--Bob cut.

Let $\Pi_{a,k}$ project onto total Alice number $a$ and total Bob number
$k$. The actual normalized resource is

$$
 \Omega={1\over Z^2}
 \sum_{a=0}^2\sum_{k=0}^4
 \Pi_{a,k}J(R\otimes R)J^*\Pi_{a,k}. \tag{203.2}
$$

This is one common twirl. The opposing one-copy coherences are retained in
(203.2), subject to the CAR signs in (203.1).

For the $N_A=1$ rails write $p=|10\rangle$, $q=|01\rangle$, and

$$
 P=1\oplus(-I_H)\oplus1.
$$

Before restriction to a Bob charge, the $N_A=1$ block is

$$
 S=\begin{pmatrix}
 A_1\otimes A_0&(C^*P)\otimes C\\
 (PC)\otimes C^*&A_0\otimes A_1
 \end{pmatrix},\qquad C^*P=-|0\rangle\langle f|+|g\rangle\langle2|. \tag{203.3}
$$

On $\mathcal H_k=\bigoplus_{i+j=k}\mathcal B_i\otimes\mathcal B_j$,
where $\mathcal B_0=\mathbb C|0\rangle$, $\mathcal B_1=H$,
$\mathcal B_2=\mathbb C|2\rangle$, the off-diagonal restrictions are

$$
\begin{array}{c|c}
 k&S\text{-off-diagonal map}\\ \hline
0&0\\
1&-|0,f\rangle\langle f,0|\\
2&-|0,2\rangle\langle f,g|+|g,f\rangle\langle2,0|\\
3&|g,2\rangle\langle2,g|\\
4&0.
\end{array} \tag{203.4}
$$

Here $|a,b\rangle$ means $a\otimes b$, and all phases are those of the
same source vectors $f,g$.

The $N_A=0$ and $N_A=2$ blocks are, respectively,

$$
 M_{0,k}=(A_0\otimes A_0)|_{\mathcal H_k},\qquad
 M_{2,k}=(A_1\otimes A_1)|_{\mathcal H_k}. \tag{203.5}
$$

Each has a one-dimensional Alice factor.

## 204. All fifteen charge probabilities

**Proposition 204.1 (All charge probabilities).** Let

$$
 \delta=\operatorname{tr}D=2t+s(1-x),\qquad
 \varepsilon=\operatorname{tr}E=2t-ts(1-y).
$$

The following entries are the unnormalized numerators; every physical probability
is the displayed entry divided by $Z^2$:

$$
\begin{array}{c|ccccc}
N_A\backslash N_B & 0 & 1 & 2 & 3 & 4 \\ \hline
0 & 1 & 2\delta & \delta^2+2b & 2b\delta & b^2 \\
1 & 2c & 2(\varepsilon+c\delta) & 2(d+\delta\varepsilon+bc) & 2(d\delta+b\varepsilon) & 2bd \\
2 & c^2 & 2c\varepsilon & \varepsilon^2+2cd & 2d\varepsilon & d^2
\end{array} \tag{204.1}
$$

They include every spectator direction and all four Bob modes.

Proof. Taking traces of the blocks in (203.3)–(203.5) gives the table.
The off-diagonal maps have zero trace in the Alice rails. The row
polynomials are

$$
 (1+\delta r+br^2)^2,\quad
 2(1+\delta r+br^2)(c+\varepsilon r+dr^2),\quad
 (c+\varepsilon r+dr^2)^2.
$$

At $r=1$, their sum is
$(1+\delta+b+c+\varepsilon+d)^2/Z^2=1$, proving normalization.

## 205. Explicit source matrices by Bob charge

**Proposition 205.1 (Source matrices in every Bob charge).**
The generic formula (203.3) can be written without suppressed spectator
entries. For $N_B=0$ and $N_B=4$, in the two Alice rails, it is

$$
 S_0=cI_2,\qquad S_4=bdI_2. \tag{205.1}
$$

For $N_B=1$, use the Bob basis

$$
 L(\xi)=\xi\otimes|0\rangle,\qquad R(\xi)=|0\rangle\otimes\xi,\qquad \xi\in H.
$$

Then

$$
 S_1=
 \begin{pmatrix}
 E\oplus cD&-|R(f)\rangle\langle L(f)|\\
 -|L(f)\rangle\langle R(f)|&cD\oplus E
 \end{pmatrix}. \tag{205.2}
$$

For $N_B=2$, use $U=|2,0\rangle$, $V=H\otimes H$,
$W=|0,2\rangle$. Then

$$
 S_2=
 \begin{pmatrix}
 d\oplus(E\otimes D)\oplus bc&K_2\\
 K_2^*&bc\oplus(D\otimes E)\oplus d
 \end{pmatrix},\quad
 K_2=|g\otimes f\rangle\langle U|-|W\rangle\langle f\otimes g|. \tag{205.3}
$$

For $N_B=3$, use $L(\xi)=|2\rangle\otimes\xi$ and
$R(\xi)=\xi\otimes|2\rangle$. Then

$$
 S_3=
 \begin{pmatrix}
 dD\oplus bE&|R(g)\rangle\langle L(g)|\\
 |L(g)\rangle\langle R(g)|&bE\oplus dD
 \end{pmatrix}. \tag{205.4}
$$

All five sector matrices are unnormalized $R\otimes R$ blocks; division by $Z^2$
gives their physical contributions. Equations (205.1)--(205.4) display every
spectator direction and every phase needed below.

Proof. Restrict $A_1\otimes A_0$ and $A_0\otimes A_1$
to the displayed Bob direct sums and use the corresponding row of
(203.4) for the off-diagonal map. This gives every displayed entry.

## 206. Partial-transpose normal forms in every Bob sector

**Proposition 206.1 (Complete partial-transpose normal forms).**
Ordinary Alice partial transposition of the actual matrices (203.3)--(203.5)
gives the following complete normal forms.

Proof. Transpose the two Alice rail indices, retaining all Bob indices. The dimensions of the Bob charge
spaces $k=0,1,2,3,4$ are $1,4,6,4,1$.

For $k=0$,

$$
 M_{1,0}^{T_A}=cI_2, \tag{206.1}
$$

and for $k=4$,

$$
 M_{1,4}^{T_A}=bdI_2. \tag{206.2}
$$

Both are positive.

For $k=1$, a unitary permutation and a $2\times2$ rail rotation give

$$
 M_{1,1}^{T_A}\simeq cD\oplus cD\oplus(E-ff^*)\oplus(E+ff^*). \tag{206.3}
$$

Since $E>0$, this is positive exactly when $q_0\leq1$.

For $k=2$, put

$$
 H_-=
 \begin{pmatrix}E\otimes D&-f\otimes g\\-(f\otimes g)^*&d\end{pmatrix},\qquad
 H_+=
 \begin{pmatrix}D\otimes E&g\otimes f\\(g\otimes f)^*&d\end{pmatrix}. \tag{206.4}
$$

Then

$$
 M_{1,2}^{T_A}\simeq bc\oplus bc\oplus H_-\oplus H_+. \tag{206.5}
$$

The two $5\times5$ Schur complements are controlled by

$$
 (f\otimes g)^*(E^{-1}\otimes D^{-1})(f\otimes g)
 =d\,q_0q_3, \tag{206.6}
$$

and the analogous equality for $g\otimes f$. Hence (206.5) is positive
exactly when $q_0q_3\leq1$.

For $k=3$,

$$
 M_{1,3}^{T_A}\simeq bE\oplus bE\oplus(dD-gg^*)\oplus(dD+gg^*), \tag{206.7}
$$

Alice transposition leaves $p\otimes R(H)$ and $q\otimes L(H)$
uncoupled, each with the strictly positive block $bE$. It couples
$p\otimes L(H)$ to $q\otimes R(H)$ by $gg^*$; symmetric and
antisymmetric combinations of these components give $dD+gg^*$ and
$dD-gg^*$, respectively. Since $dD>0$, the latter is positive
semidefinite exactly when $g^*(dD)^{-1}g=q_3\leq1$. Thus (206.7)
is positive exactly when $q_3\leq1$. Equations (206.1)--(206.7),
together with the one-dimensional-Alice blocks (203.5), classify all 15
charge blocks. Therefore

$$
 \boxed{\Omega^{T_A}\geq0\iff q_0\leq1\text{ and }q_3\leq1.} \tag{206.8}
$$

No PPT inference through an assumed local ordinary regrouping is used.

## 207. Necessity for every allowed local filter

**Proof of necessity in Theorem 201.3.** If the right side of
(206.8) holds and $K_A\otimes K_B$ is any product
Kraus operator, then

$$
 \bigl[(K_A\otimes K_B)\Omega(K_A\otimes K_B)^*\bigr]^{T_A}
 =(\overline K_A\otimes K_B)\Omega^{T_A}
 (K_A^{\mathsf T}\otimes K_B^*)\geq0. \tag{207.1}
$$

An adaptive branch is still a product Kraus operator, and coarse-graining is
a positive sum of such congruences. A positive-probability normalization preserves
positivity. Charge-preserving filters are a subset. Thus $q_0\leq1,q_3\leq1$
forbids encoded NPT under the entire declared local operation class.

## 208. Inverse-direction filters and exact outer branches

**Proof of sufficiency in Theorem 201.3: the outer branches.**
Assume $q_0>1$. Define the normalized inverse direction

$$
 k_0={E^{-1}f\over\|E^{-1}f\|},\qquad
 L(\xi)=\xi\otimes|0\rangle,\qquad R(\xi)=|0\rangle\otimes\xi.
$$

Bob applies the orthogonal rank-two projector within $N_B=1$ onto
$\operatorname{span}\{L(k_0),R(k_0)\}$, and Alice projects onto
$\operatorname{span}\{p,q\}$. Set

$$
 a_0=k_0^*Ek_0,\qquad B_0=c\,k_0^*Dk_0,\qquad m_0=|k_0^*f|^2.
$$

Then $m_0/a_0=q_0$, $B_0>m_0$ by (202.3), and the actual subnormalized
encoded state in the order $(pL,pR,qL,qR)$ is

$$
 X_0={1\over Z^2}
 \begin{pmatrix}
 a_0&0&0&0\\0&B_0&-m_0&0\\0&-m_0&B_0&0\\0&0&0&a_0
 \end{pmatrix}. \tag{208.1}
$$

Its probability and partial-transpose spectrum are

$$
 P_0={2(a_0+B_0)\over Z^2}>0,\qquad
 \operatorname{spec}(X_0^{T_A})={1\over Z^2}\{B_0,B_0,a_0+m_0,a_0-m_0\}. \tag{208.2}
$$

Thus $q_0>1$ gives NPT, with

$$
 \lambda_{\min}\bigl((X_0/P_0)^{T_A}\bigr)
 ={a_0-m_0\over2(a_0+B_0)}<0,\quad
 \mathcal N(X_0/P_0)={(m_0-a_0)_+\over2(a_0+B_0)},\quad
 P_0\mathcal N={(m_0-a_0)_+\over Z^2}. \tag{208.3}
$$

The central $2\times2$ source block has eigenvalues $B_0\pm m_0$,
so the original filtered state is positive. The minus sign in (208.1) is
exactly the CAR sign and can be changed by an Alice rail phase.

Assume $q_3>1$. Define

$$
 k_3={D^{-1}g\over\|D^{-1}g\|},\qquad
 L(\xi)=|2\rangle\otimes\xi,\qquad R(\xi)=\xi\otimes|2\rangle,
$$

with the orthogonal rank-two Bob projector onto $\operatorname{span}\{L(k_3),R(k_3)\}$ in $N_B=3$.
Set

$$
 a_3=d\,k_3^*Dk_3,\qquad B_3=b\,k_3^*Ek_3,\qquad m_3=|k_3^*g|^2.
$$

Then $m_3/a_3=q_3$, $B_3>m_3$, and

$$
 X_3={1\over Z^2}
 \begin{pmatrix}
 a_3&0&0&0\\0&B_3&m_3&0\\0&m_3&B_3&0\\0&0&0&a_3
 \end{pmatrix}. \tag{208.4}
$$

Consequently

$$
 P_3={2(a_3+B_3)\over Z^2}>0,\qquad
 \operatorname{spec}(X_3^{T_A})={1\over Z^2}\{B_3,B_3,a_3+m_3,a_3-m_3\},\tag{208.5}
$$

and

$$
 \lambda_{\min}={(a_3-m_3)\over2(a_3+B_3)},\quad
 \mathcal N(X_3/P_3)={(m_3-a_3)_+\over2(a_3+B_3)},\quad
 P_3\mathcal N={(m_3-a_3)_+\over Z^2}. \tag{208.6}
$$

The plus sign in (208.4) is the corresponding literal CAR sign.

## 209. The middle sector and the product threshold

**Proposition 209.1 (Middle-sector extraction).** Under
$q_0q_3>1$, the middle branch below has positive probability and
is NPT.

Proof. Use the same $k_0,k_3$. In $N_B=2$, let

$$
 U=|2\rangle\otimes|0\rangle,\qquad \chi=k_3\otimes k_0,
$$

and project Bob onto $\operatorname{span}\{U,\chi\}$. Choose phases so that

$$
 \mu=(k_3^*g)(k_0^*f)>0.
$$

Put

$$
 A=(k_3^*Ek_3)(k_0^*Dk_0),\qquad
 B=(k_3^*Dk_3)(k_0^*Ek_0).
$$

In the order $(pU,p\chi,qU,q\chi)$, the actual subnormalized output is

$$
 X_2={1\over Z^2}
 \begin{pmatrix}
 d&0&0&0\\0&A&\mu&0\\0&\mu&bc&0\\0&0&0&B
 \end{pmatrix}. \tag{209.1}
$$

Positivity follows from (202.3):
$\mu^2\leq (b\,k_3^*Ek_3)(c\,k_0^*Dk_0)=bcA$.
Moreover,

$$
 {\mu^2\over dB}=q_0q_3. \tag{209.2}
$$

Partial transposition has spectrum

$$
 {1\over Z^2}\left\{A,bc,
 {d+B+\sqrt{(d-B)^2+4\mu^2}\over2},
 {d+B-\sqrt{(d-B)^2+4\mu^2}\over2}\right\}. \tag{209.3}
$$

With $H_2=d+A+bc+B$,

$$
 P_2={H_2\over Z^2},\qquad
 \lambda_{\min}={(d+B)-\sqrt{(d-B)^2+4\mu^2}\over2H_2},\tag{209.4}
$$

$$
 \mathcal N(X_2/P_2)={\left[\sqrt{(d-B)^2+4\mu^2}-d-B\right]_+\over2H_2},\quad
 P_2\mathcal N={\left[\sqrt{(d-B)^2+4\mu^2}-d-B\right]_+\over2Z^2}. \tag{209.5}
$$

The last eigenvalue is negative exactly when $\mu^2>dB$, namely
$q_0q_3>1$. Thus the middle sector is a valid additional witness inside
the already known union, not an activation mechanism beyond it.

## 210. Exact equivalence and a single compatible instrument

**Proof of Theorem 201.3 and its compatible flagged instrument.**
Equations (208.1)--(208.6) prove sufficiency whenever $q_0>1$ or $q_3>1$.
Equations (206.8) and (207.1) prove necessity for every allowed filter.
Therefore

$$
 \boxed{
 \Omega\text{ is PPT}\iff(q_0\leq1\ \land\ q_3\leq1),\qquad
 \Omega\text{ admits encoded NPT}\iff(q_0>1\ \lor\ q_3>1).
 }\tag{210.1}
$$

The three displayed Bob projectors occupy mutually exclusive total-number
sectors. For a fixed $t,v,w$, one instrument may measure $N_B$ and retain
flags $j\in\{0,2,3\}$ for the selected branches. Alice first
projects coherently onto $N_A=1$. Within that Alice outcome, Bob
uses the mutually orthogonal projectors from §§208–209 for a chosen
subset $J$ of defined branches and their orthogonal complement
as a failure outcome. Together with Alice’s failure outcome these
operators define one number-preserving instrument. Its accepted probability is

$$
 P_{\mathrm{acc}}=\sum_{j\in J}P_j,
$$

and its flag-retaining success-weighted negativity is

$$
 \sum_{j\in J}P_j\mathcal N_j.
$$

Only branches using the same source parameters are added. Full 64-dimensional
negativity, one selected conditional negativity, and this flagged sum are
separate quantities; no equality between them is asserted. No global
optimality or maximal-rate statement is made.

## 211. One-copy obstruction, minimum declared copy number, and preparation

**Corollary 211.1 (One-copy obstruction and the minimum in the declared menu).**
In the region $q_0>1$ or $q_3>1$, the minimum number of
compatible preparations for the declared encoded-NPT extraction is
exactly two.

Proof. For one copy, the local-number twirl is

$$
 {1\over Z}\bigl(|0\rangle\langle0|\otimes A_0
 +|1\rangle\langle1|\otimes A_1\bigr). \tag{211.1}
$$

Each Alice fixed-number sector is one-dimensional. A number-preserving local
instrument cannot turn the positive product sum (211.1) into an encoded
entangled subsystem. Thus ordinary NPT of the untwirled one-copy matrix does
not constitute one-copy SSR-accessible entanglement.

If $q_0>1$ or $q_3>1$, one copy is impossible and §§208--209 give a
positive-probability two-copy branch, so the minimum copy number in this menu is
exactly two. If $q_0,q_3\leq1$, neither one nor two copies yields encoded NPT.
No claim about three or more copies is made.

The common untwirled preparation is essential. If each input is independently
number-twirled first, its $C$ block is removed before tensoring. Every term
in (203.4) then vanishes, and a later common twirl of the product remains a
positive sum of Alice--Bob product blocks. The compatible-preparation and
common-phase assumptions are resource premises, not conclusions about physical
availability.

## 212. Finite endpoints and exact parameter cases

**Proposition 212.1 (Finite endpoint and vanishing-coupling cases).**
The sector laws and extraction criteria include all finite endpoints
and all vanishing couplings of Definition 201.1.

Proof. At $t=1$, $s=0$, $f=g=0$, $R=I_8$, and
$\Omega=I_{64}/64$. The table (204.1) reduces to the binomial charge
multiplicities; no NPT branch exists. The endpoint $t=0$ is excluded.

If $f=0$ or $g=0$, the corresponding $q$ is zero and its inverse filter
is simply unused. Formula (202.5) is regular at $x,y\in\{0,1\}$: an
endpoint component forces the associated coupling to vanish. Repeated,
collinear, orthogonal, or otherwise nonaligned unit $v,w$ require no change;
no division by $\|u\|$, $\|h\|$, or $z$ occurs. Strict activation itself
ensures the inverse direction being used is nonzero.

At $q_0=1$, $q_3=1$, or $q_0q_3=1$, the corresponding partial-transpose
block has a zero eigenvalue and is PPT, not NPT. If one outer parameter is
strictly greater than one, the other equality does not suppress that branch.

**Proposition 212.2 (Shared-source threshold equality).** An exact
shared-source equality point is

$$
 t=3-2\sqrt2,\qquad v={(1,1,0)\over\sqrt2},\qquad w={(1,0,1)\over\sqrt2}.
$$

Proof. Here $z=0$, $x=y=1/2$, and $(1-t)^2=4t$, hence
$q_0=q_3=1$ and $q_0q_3=1$. The relevant partial-transpose eigenvalues
are zero, so this point is PPT at all three threshold equalities.

**Proposition 212.3 (A rational $q_0$-only branch).** Take

$$
 t={1\over4},\qquad v={(1,1,0)\over\sqrt2},\qquad w=(0,1,0).
$$

Proof. Substitution in (202.5) and (208.1)–(208.3) gives
$q_0=9/4,q_3=0$, and $k_0=(1,0)$ gives

$$
 (a_0,B_0,m_0)=\left({1\over16},{25\over64},{9\over64}\right),\quad
 Z={25\over8},\quad P_0={58\over625},\quad
 \lambda_{\min}=-{5\over58},\quad P_0\mathcal N={1\over125}.
$$

**Proposition 212.4 (A rational $q_3$-only branch).** Take

$$
 t={1\over10},\qquad v=(0,1,0),\qquad
 w={(1,0,1)\over\sqrt2}.
$$

Proof. Substitution in (202.5) and (208.4)–(208.6) gives
$q_0=0,q_3=81/40$, and $k_3=(0,1)$ gives

$$
 (a_3,B_3,m_3)=\left({40\over40000},{121\over40000},{81\over40000}\right),\quad
 Z={121\over50},\quad P_3={161\over117128},\quad
 \lambda_{\min}=-{41\over322},\quad P_3\mathcal N={41\over234256}.
$$

**Proposition 212.5 (One complex source with three strict branches).**
A fully complex, nonaligned joint point is

$$
 t={1\over10},\qquad v={(1,2,2)\over3},\qquad
 w={(2,1,2i)\over3}.
$$

Proof. Here $x=1/9,y=4/9,z=20/81$, and direct substitution gives

$$
 q_0={6\over5},\qquad q_3={10\over9},\qquad q_0q_3={4\over3}.
$$

Thus both outer branches and the middle criterion are strict for one shared
complex source. The derivation, rather than this example, supplies the
classification.

## 213. Mathematical suppliers and finite two-copy scope

**Convention 213.1 (Source correspondence and supporting methods).**
The source and cut are those of [Continuation VI, §§139–156 and
169–176](https://github.com/the-omega-institute/trureturing/blob/d90bd2fb685cbc899f24a36bf253ad4e6d3b1886/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VI.md).
VI (140.1) and (141.1)–(141.3) supply the native finite Gibbs spectrum
and normalization. VI (142.1)–(142.2), §147 and (149.2) supply the
compatible CAR convention, common-number resource and four-mode Bob cut.
VI (169.2) and §170 supply the enlarged independent-ray orbit and
one-copy Schur criterion. Equations (177.2), (178.1)–(178.6) and
Theorem 181.1 are the corresponding one-copy prerequisites in this volume.
The pointwise ordinary PPT–separability classification is reused for
this exact family; the necessity argument in §§203–207 uses the explicit
signed two-copy law rather than treating CAR regrouping as an ordinary
local tensor permutation.

The fixed-local-number sector interpretation is the mature method of
H. M. Wiseman and J. A. Vaccaro, *The entanglement of indistinguishable
particles shared between two parties*, Phys. Rev. Lett. **91**, 097902,
[quant-ph/0210002v2](https://arxiv.org/pdf/quant-ph/0210002v2),
Eqs. (12)–(14), as cited in VI §156 [W]. Its pure-state formula is not
used as a mixed-state Gibbs formula. The mixed-state number-SSR filtering
standard form and two-copy local fixed-number projection are those of
N. Schuch, F. Verstraete and J. I. Cirac, *Quantum entanglement theory in
the presence of superselection rules*, Phys. Rev. A **70**, 042310,
[quant-ph/0404079v1](https://arxiv.org/pdf/quant-ph/0404079v1),
§IV.D.1–2, mapped to the native family in VI (148.4) and §§149–151.
Group twirling and multiple-copy reference-frame methods are treated by
S. D. Bartlett, T. Rudolph and R. W. Spekkens, *Reference frames,
superselection rules, and quantum information*, Rev. Mod. Phys. **79**,
555, [quant-ph/0610030v3](https://arxiv.org/pdf/quant-ph/0610030v3),
§III.C.2 and §III.C.4, as cited in VI §156 [R].

The ordinary partial-transpose method is applied only after fixing the
actual CAR coordinates and charge matrices; the encoded outputs are
explicit $2\times2$ matrices. Their PPT–separability criterion is the
$2\times2$ case of M. Horodecki, P. Horodecki and R. Horodecki,
*Separability of Mixed States: Necessary and Sufficient Conditions*,
[quant-ph/9605038v2](https://arxiv.org/pdf/quant-ph/9605038v2), Theorem 3,
as cited in VI §156 [P]. The signed full-orbit sector decomposition,
all fifteen probabilities, inverse-selected outer flags and middle
$q_0q_3$ branch in §§203–209 are repo-derived application synthesis
using these mature methods. No literature-priority assertion is attached
to those identities.

**Assumption 213.2 (Applicability of the finite extraction statement).**
Every assertion concerns Definition 201.1 with $0<t\le1$, two compatible
independent untwirled preparations, the stated creation convention,
one common local-number twirl and the fixed-charge coherent filters of
Assumption 201.2. The enlarged global sector orbit is a premise distinct
from passive $\Gamma(U(3))$, native reachability and the local operation
class. The physical availability of the preparations and filters is a
separate premise. Independent pre-twirling specifies a different resource.
No cloning or external phase reference is inferred. Theorem 181.1
classifies ordinary one-copy separability; Theorem 201.3 and Corollary
211.1 concern the finite two-copy encoded-NPT task. They supply no
all-copy theorem, asymptotic rate, global filter optimum, physical
implementation or resource advantage. Full-state negativity, selected
conditional negativity and the flagged success-weighted sum in §210
remain distinct quantities.

## 213.99 追加锚（本行以下为增补区）

## 214. Measure-free packing and the resolution budget

### 214.1 A metric-doubling replacement for the volume hypothesis

The Ahlfors measure in §160 is one sufficient way to turn a resolved
occurrence set into a packing bound. The measure is not essential to that
counting step. The following version uses only a uniform metric covering
property and therefore has a different scope.

**Definition 214.1 (uniform metric-doubling occurrence bridge).** Retain the
occurrence sets $V_n$, their counts and heights from (160.1). Let
$\iota_n:V_n\hookrightarrow X$ map every task-distinct occurrence into one
metric space $(X,\rho)$. Assume that, for fixed $\delta>0$ and fixed
$A,B>0$,

$$
\rho(\iota_n(x),\iota_n(y))\ge\delta\quad(x\ne y),
\qquad
\rho(o,\iota_n(x))\le A(n-1)+B.
\tag{214.1}
$$

Assume also that every closed ball at every center and radius used below is
covered by at most $K\ge2$ closed balls of half its radius, with the same
finite $K$ at every level. Put

$$
R_n=A(n-1)+B,
\qquad q=\log_2K.
\tag{214.2}
$$

No measure, Green kernel, generator, or spatial dimension is part of this
definition.

**Theorem 214.2 (metric-doubling packing obstruction).** Under Definition
214.1,

$$
\boxed{
N_n\le
K^{\left\lceil\log_2\left(1+\frac{2R_n}{\delta}\right)\right\rceil}.
}
\tag{214.3}
$$

Proof. Let

$$
k_n=\left\lceil\log_2\left(1+\frac{2R_n}{\delta}\right)\right\rceil.
$$

Iterating the half-radius covering property $k_n$ times covers the closed
ball $\overline B(o,R_n)$ by at most $K^{k_n}$ closed balls of radius
$R_n/2^{k_n}$. Since

$$
\frac{2R_n}{2^{k_n}}<\delta,
$$

each final ball has diameter strictly smaller than $\delta$ and contains at
most one point of the $\delta$-separated set $\iota_n(V_n)$. All occurrences
lie in the original ball by (214.1), so (214.3) follows. $\square$

If $\delta$ is fixed, (214.3) is polynomial in $n$:

$$
K^{\lceil\log_2(1+2R_n/\delta)\rceil}
=O(n^q).
\tag{214.4}
$$

But $N_n=2F_{n+1}-1$ has

$$
\log N_n=n\log\varphi+O(1).
\tag{214.5}
$$

Consequently no one metric-doubling carrier with fixed $K,A,B,\delta$ can
resolve every prefix. This is a measure-free obstruction; it does not say
that the source has metric dimension $q$, and it does not select $q=3$.

### 214.2 Necessary resolution budget

The same estimate gives a quantitative condition when the resolution is
allowed to vary. Since

$$
\left\lceil\log_2(1+2R_n/\delta_n)\right\rceil
<\log_2(1+2R_n/\delta_n)+1,
$$

every prefix with $N_n>K$ must satisfy

$$
\boxed{
\delta_n
<
\frac{2R_n}{(N_n/K)^{1/q}-1}
=
\frac{4R_n}{N_n^{1/q}-2}.
}
\tag{214.6}
$$

The second form uses $K^{1/q}=2$. Thus, for fixed $K,A,B$, the required
resolution is at most

$$
\delta_n=O\!\left(n\,\varphi^{-n/q}\right).
\tag{214.7}
$$

This is a necessary budget, not an embedding construction and not a
sufficient stability condition. Passing from a finite prefix to an infinite
carrier therefore requires a declared scale law; a fixed positive spatial
resolution is incompatible with the stated uniform bridge.

**Proposition 214.3 (finite exact certificate).** For

$$
K=8,\qquad A=B=\delta=1,\qquad n=26,
$$

one has $R_{26}=26$, $N_{26}=2F_{27}-1=392835$, and

$$
\left\lceil\log_2(1+2R_{26}/\delta)\right\rceil
=\lceil\log_2 53\rceil=6.
$$

The cover capacity is therefore $8^6=262144$, so (214.3) fails:

$$
\boxed{392835>262144.}
\tag{214.8}
$$

This rejects these constants at this prefix. It is not by itself an
all-prefix theorem, and it does not identify $K=8$ with a three-dimensional
covering number.

### 214.3 Why an upper measure bound alone is insufficient

Replacing the doubling condition by an upper estimate on ball masses loses
the packing conclusion unless a uniform lower mass or a direct covering
bound is also supplied. A concrete countermodel is the infinite rooted
binary occurrence tree with unit graph metric. Give a vertex at depth $h$
the mass

$$
\mu(v)=Z^{-1}4^{-h},
\qquad
Z=\sum_v4^{-\operatorname{depth}(v)}.
\tag{214.9}
$$

Since there are at most $2^h$ vertices at depth $h$, $1\le Z\le2$.
Every occurrence remains separated by one unit and the prefix of height
$n-1$ lies in a ball of radius $n$. Nevertheless, for any fixed $d>0$ and
any $t\ge1/3$,

$$
\mu(B(z,t))\le1\le 3^d t^d.
\tag{214.10}
$$

Thus the required upper $t^d$ estimate at the macroscopic radii can hold
while exponentially many occurrences still fit in radius $n$. At radius
$1/3$, the ball about a vertex contains only that vertex and its mass tends
to zero along any infinite spine. There is no uniform lower mass and no
metric-doubling packing control.

This countermodel does not assert an upper estimate at arbitrarily small
radii; it isolates exactly the missing hypothesis. Therefore §160's
measure-theoretic proof may be replaced by Theorem 214.2 only after a
metric-doubling or direct packing property has been established. Neither
route supplies the still-missing occurrence-to-physical-carrier metric,
transport, clock, observation, or dimension-sensitive invariant.

## 214.99 追加锚（本行以下为增补区）

## 215. Exponential resolution threshold

The necessary budget in (214.6) can be stated as a phase boundary. This
separates a change of resolution law from a claim about the dimension of the
carrier.

**Theorem 215.1 (subcritical resolution is impossible).** Suppose the
metric-doubling cover constant $K$, the root-radius constants $A,B$, and the
source separation constants are as in Definition 214.1, except that the
separation may vary with $n$ and is denoted by $delta_n$. Let

$$
q=\log_2K,qquad
\delta_n\ge c,n^{-s}e^{-\kappa n}
\quad(n\ge n_0),
\tag{215.1}
$$

for fixed $c>0$, $s\ge0$, and $\kappa\ge0$. If every prefix is
resolved in one common metric-doubling carrier, then necessarily

$$
\boxed{
\kappa\ge\frac{\log\varphi}{q}.
}
\tag{215.2}
$$

In particular, a fixed or polynomially shrinking resolution cannot support
all Fibonacci prefixes for any finite $K$.

Proof. From (214.3) and $\lceil x\rceil<x+1$,

$$
N_n
<K\left(1+\frac{2R_n}{\delta_n}\right)^q.
\tag{215.3}
$$

Since $R_n=A(n-1)+B=O(n)$, (215.1) gives a constant $C>0$ such that

$$
1+\frac{2R_n}{\delta_n}
\le C n^{s+1}e^{\kappa n}
\tag{215.4}
$$

for all sufficiently large $n$. Hence

$$
N_n\le C' n^{q(s+1)}e^{q\kappa n}.
\tag{215.5}
$$

On the other hand, the Binet formula used in (160.8) gives

$$
N_n\ge c'\varphi^n
\tag{215.6}
$$

for some $c'>0$ and all large $n$. If $q\kappa<\log\varphi$, the ratio of
(215.6) to (215.5) tends to infinity, a contradiction. Therefore (215.2)
is necessary. The case $\kappa=0$ includes every lower bound of polynomial
order. $\square$

**Corollary 215.2 (the critical polynomial window).** At the threshold

$$
\kappa_*:=\frac{\log\varphi}{q},
$$

the packing estimate requires

$$
\delta_n=O\!\left(n e^{-\kappa_* n}\right).
\tag{215.7}
$$

Thus a law bounded below by $c n^{1+\epsilon}e^{-\kappa_*n}$ for any
$\epsilon>0$ is impossible, while the law $n e^{-\kappa_*n}$ is only a
necessary scale and is not an existence construction.

For the stipulated $K=8$, one has $q=3$ and therefore

$$
\kappa_*=rac{\log\varphi}{3}.
\tag{215.8}
$$

This number is a resolution exponent of the declared occurrence bridge. It
is not a spatial dimension, a heat-kernel exponent, or a Fock/observation
rank. A physical three-dimensional conclusion still needs an independent
realization law and an observable correspondence.

## 215.99 追加锚（本行以下为增补区）
