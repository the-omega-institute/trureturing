# AURIC Ω: Bosonic Excursion, Return and Fixed-Frame Phase Correction

## 1. Fixed carrier, native coordinates and additional permissions

**Definition 1.1 (The five coordinates and their bosonic embedding).**
Use the ordered five-state space of [Static Compatibility–Fiber Theory,
Definition 43.1](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#19-续篇ⅳ五模式的受约束翻转与记录障碍)
and its explicitly fixed physical coordinates in Definition 68.1, equation (X.1):

$$
\begin{aligned}
(e_0,e_1,e_2,e_3,e_4)
  &=(|000\rangle,|100\rangle,|010\rangle,|001\rangle,|101\rangle),\\
V&=\operatorname{span}_{\mathbb C}\{e_0,e_1,e_2,e_3,e_4\},\\
D_3&=\operatorname{diag}(1,i,i,i,1),\\
S&=\operatorname{diag}(1,1,1,1,i).
\end{aligned}
$$

Here $S$ is the native $S_{\star,3}=S_{13}$ of that volume's
Assumption 55.2, equation (VII.4), and equation (X.26).
$D_3$ is a passive coordinate change, as in its Definitions 1.4 and 68.1;
it is not an executable phase gate.

For this model embed those five basis vectors into the normalized Fock space
of three independent modes indexed by positions $1,2,3$. Put

$$
f_+=|200\rangle,\qquad f_-=|002\rangle,\qquad
W=V\oplus\operatorname{span}_{\mathbb C}\{f_+,f_-\}.
$$

Let $P$ be the orthogonal projection onto $V$ and $Q=I-P$ on the Fock space.
On $W$, $Q$ has range $\operatorname{span}\{f_+,f_-\}$.
The ordered basis of $W$ is $(e_0,e_1,e_2,e_3,e_4,f_+,f_-)$.
The embedding identifies five orthonormal vectors; it does not identify
all operators or permitted paths of the two carriers.

**Assumption 1.2 (Normalized CCR and one fixed Hamiltonian).**
On the algebraic Fock domain assume

$$
[a_j,a_k^\dagger]=\delta_{jk}I,\qquad
[a_j,a_k]=[a_j^\dagger,a_k^\dagger]=0,\qquad n_j=a_j^\dagger a_j,
$$

with the normalized actions

$$
a_j|n\rangle=\sqrt{n_j}|n-\mathbf e_j\rangle,\qquad
a_j^\dagger|n\rangle=\sqrt{n_j+1}|n+\mathbf e_j\rangle.
$$

The negative-occupation term is zero. Fix, throughout each result and each
approximation sequence,

$$
H=g a_1^\dagger a_3+\bar g a_3^\dagger a_1+J n_1n_3,
\qquad g\in\mathbb C\setminus\{0\},\quad J\in\mathbb R,\quad\hbar>0.
$$

Both $g$ and $J$ have units of energy. Evolution means
$U(t)=\exp(-itH/\hbar)$. Each finite total-number sector is invariant and
finite dimensional; take the orthogonal direct sum of these Hermitian
restrictions to define the self-adjoint Hamiltonian and its unitary group.
All spectral assertions below concern $H|_W$ only.

The exchange/number-interaction family is classical: compare Links,
Foerster, Tonel and Santos, *The two-site Bose–Hubbard model*,
[arXiv:cond-mat/0605486v1](https://arxiv.org/abs/cond-mat/0605486v1),
§1, equation (1), [DOI 10.1007/s00023-006-0295-3](https://doi.org/10.1007/s00023-006-0295-3).
For the two outer modes, writing $M=n_1+n_3$ gives
$Jn_1n_3=J(M^2-(n_1-n_3)^2)/4$.
A scalar shift on one fixed $M$ sector is not one common scalar on $V$,
which contains different values of $M$. No such sector-dependent term is
removed in the present Hamiltonian.

The Fock modes in [Pyramid Correlation and Native Continuation,
Definition 26.7](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md#263-指定玻色模型及唯一零能射线)
are indexed by complete legal words, with a different positive Hamiltonian
in its equation defining $H_n$. Here the modes are three positions and the
Hamiltonian is the displayed $H$. Neither the indexing nor that Hamiltonian
is transported merely by using five of the same word labels.

**Assumption 1.3 (Separately stipulated endpoint corrections).**
When a result allows a real correction, assume the additional availability
of precisely

$$
G_{\mathbb R}=D_3SO(5)D_3^\dagger
$$

on $V$. Each such correction preserves $V$. One-sided correction means one
element before or after a single $H$ pulse; two-sided correction means one
element on each side. The elements and pulse times are independent of the
unknown input density. This assumption grants neither interleaving controls
within the pulse nor other preparation, reset, replication, reference,
encoding, decoding or measurement operations.

The native independent-flip closure in Static Compatibility–Fiber Theory,
Proposition 45, explains this real frame, but depends on that volume's
additional Assumption 45.1. A group closure in a different control model
does not supply an exact correction for this bosonic model. Here full
$G_{\mathbb R}$ availability is an explicit separate premise.

**Definition 1.4 (Path permission and the meaning of a channel).**
The native no-excursion requirement is preservation of the legal space for
every allowed input at every intermediate time. Its operator form here is
$QU(s)P=0$ throughout the pulse interval. This uses the support criterion
(41.1) and the throughout-pulse legality in Assumption 55.2 of
[Static Compatibility–Fiber Theory](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md).
The original fixed waiting/complete-read/Stop menu of its Definition 1.4
and Assumption 44.1 is distinct from its independently enlarged menus.
Neither $H$ nor Assumption 1.3 is inferred to belong to the original menu.

Unless a number or parity restriction is explicitly imposed, a density on
$V$ means any complex positive semidefinite trace-one matrix supported in
$V$, including coherences between different occupation sectors. Equality
of five-state channels means equality on every such density, or equivalently
on $M_5(\mathbb C)$. Projective unitary equality means equality up to one
scalar of modulus one, common to all five states. Superselection-restricted
observations are considered separately in Proposition 6.3.

**Definition 1.5 (Fixed dimensionless parameters).**
Write

$$
\begin{aligned}
r&=|g|>0,&u&=g/r,&\Delta&=\sqrt{J^2+16r^2},\\
d&=J/\Delta,&x&=2r/\Delta,&\eta&=4r/\Delta,\\
\alpha&=(1-d)/2,&
\tau(t)&=\Delta t/(2\hbar),&\chi(t)&=Jt/(2\hbar),\quad
\theta(t)=rt/\hbar.
\end{aligned}
$$

Thus $|u|=1$, $-1<d<1$, $0<x\leq1/2$, $\eta=2x>0$ and
$d^2+\eta^2=d^2+4x^2=1$. Parameters do not vary with the desired accuracy.

## 2. Exact seven-state dynamics and all-input returns

**Proposition 2.1 (The reducing space and bright/dark normalization).**
Under Assumption 1.2, $W$ is reducing, whereas $V$ is not invariant. With
columns denoting inputs, the nonzero actions are

$$
\begin{aligned}
He_1&=\bar g e_3,&He_3&=g e_1,\\
He_4&=J e_4+\sqrt2g f_++\sqrt2\bar g f_-,\\
Hf_+&=\sqrt2\bar g e_4,&Hf_-&=\sqrt2g e_4,
\end{aligned}
$$

and $He_0=He_2=0$. The orthonormal bright and dark vectors

$$
b=\frac{u f_++\bar u f_-}{\sqrt2},\qquad
z=\frac{u f_+-\bar u f_-}{\sqrt2}
$$

satisfy $Hb=2r e_4$, $Hz=0$, $He_4=J e_4+2r b$.
In the mutually orthogonal planes $(e_1,e_3)$ and $(e_4,b)$ the matrices are

$$
H_1=\begin{pmatrix}0&g\\\bar g&0\end{pmatrix},\qquad
H_2=\begin{pmatrix}J&2r\\2r&0\end{pmatrix}.
$$

The spectrum on $W$, with multiplicity, is

$$
0,0,0,r,-r,\frac{J+\Delta}{2},\frac{J-\Delta}{2}.
$$

Proof. Apply each annihilator before its creator. For example,
$a_1^\dagger a_3|101\rangle=\sqrt2|200\rangle$ and
$a_3^\dagger a_1|101\rangle=\sqrt2|002\rangle$;
the reverse actions have the displayed conjugate coefficients.
Every listed image stays in $W$, so the restriction is Hermitian and
reducing. The image of $e_4$ has nonzero component in $V^\perp$, so $V$ is
not invariant. Substitution proves the bright/dark identities and their
normalizations. Now $H_1^2=r^2I$ and

$$
(H_2-(J/2)I)^2=(\Delta^2/4)I.
$$

The remaining three vectors $e_0,e_2,z$ are fixed. Consequently
$\det(EI-H|_W)=E^3(E^2-r^2)(E^2-JE-4r^2)$, proving the spectrum.
In particular $\operatorname{tr}H|_W=J$ and
$\|H|_W\|=(\Delta+|J|)/2$. $\square$

**Theorem 2.2 (Operator leakage for every complex density).**
For every real $t$, define

$$
\begin{aligned}
B(\theta)&=
\begin{pmatrix}
\cos\theta&-iu\sin\theta\\
-i\bar u\sin\theta&\cos\theta
\end{pmatrix},\\
A(t)&=e^{-i\chi}(\cos\tau-id\sin\tau),\\
C(t)&=-i\eta e^{-i\chi}\sin\tau.
\end{aligned}
$$

The single-particle block of $U(t)$ is $B(\theta(t))$, and

$$
\begin{aligned}
U(t)e_4&=A(t)e_4+C(t)b,\\
U(t)b&=C(t)e_4+e^{-i\chi}(\cos\tau+id\sin\tau)b,\\
QU(t)P&=C(t)|b\rangle\langle e_4|.
\end{aligned}
$$

For every $\rho=P\rho P\geq0$ with $\operatorname{tr}\rho=1$, put
$\kappa=\langle e_4,\rho e_4\rangle$. Then

$$
\begin{aligned}
L_\rho(t)&=\operatorname{tr}(QU(t)\rho U(t)^\dagger)
 =\kappa\eta^2\sin^2\!\left(\frac{\Delta t}{2\hbar}\right),\\
\epsilon(t)&=\sup_{\rho\in\mathsf D(V)}L_\rho(t)
 =\|QU(t)P\|^2=\eta^2\sin^2\!\left(\frac{\Delta t}{2\hbar}\right).
\end{aligned}
$$

Proof. Exponentiating the two traceless squares in Proposition 2.1 gives
$B$ and

$$
U(t)|_{\operatorname{span}(e_4,b)}
=e^{-i\chi}\left[
\cos\tau I-i\sin\tau
\begin{pmatrix}d&\eta\\\eta&-d\end{pmatrix}\right].
$$

Only the input $e_4$ reaches $V^\perp$. Therefore

$$
PU(t)^\dagger QU(t)P
 =\eta^2\sin^2\tau\,|e_4\rangle\langle e_4|.
$$

Taking its trace pairing with an arbitrary $\rho$ proves the formula,
including all complex off-diagonal entries. The largest eigenvalue gives
the supremum, attained at $|e_4\rangle\langle e_4|$.
No diagonal-input extrapolation is needed.
If $\kappa=0$, that particular input has zero leakage at all times;
this is not a uniform return. If $\kappa>0$, its zero set is the uniform
zero set. For finite $J$,

$$
L_\rho(t)=4\kappa r^2t^2/\hbar^2+O(t^4)
\qquad(t\longrightarrow0).
$$

At $J=0$, $\Delta=4r$, $d=0$, $\eta=1$, so
$L_\rho(t)=\kappa\sin^2(2\theta)$.
As a normalization check within the same calculation, the symmetric square
of the one-particle evolution sends $e_4$ to

$$
\cos(2\theta)e_4-i\sqrt2\cos\theta\sin\theta
 (u f_++\bar u f_-),
$$

which has exactly that leakage. $\square$

**Theorem 2.3 (Uniform return lattice, determinants and compression).**
For $t\geq0$, return of every $V$ input to $V$ occurs exactly at

$$
t_m=\frac{2\pi\hbar m}{\Delta},\qquad m\in\mathbb Z_{\geq0}.
$$

At such a time write

$$
\theta_m=\pi mx,\qquad
\lambda_m=(-1)^me^{-i\pi md}=e^{2\pi im\alpha},\qquad
U_m=U(t_m)|_V.
$$

Then $U_m$ fixes $e_0,e_2$, equals $B(\theta_m)$ on $(e_1,e_3)$,
and equals $\lambda_m$ on $e_4$. On $(b,z)$ the return coefficients are
$(\lambda_m,1)$. In particular

$$
\det U_m=\lambda_m,\qquad
\det(U(t_m)|_W)=\lambda_m^2=e^{-iJt_m/\hbar}.
$$

For arbitrary $t$, the compression $K(t)=PU(t)P|_V$ defines a completely
positive trace-nonincreasing map $\Phi_t(\rho)=K(t)\rho K(t)^\dagger$,
which is trace preserving for all $V$ inputs exactly at the return times.
The projected-Hamiltonian exponential $\exp(-itPHP|_V/\hbar)$ has joint
coefficient $e^{-iJt/\hbar}$; at return it is $\lambda_m^2$ and equals the
true $U_m$, even up to a common scalar, if and only if $\lambda_m=1$.

Proof. Since $\eta>0$, Theorem 2.2 says $QU(t)P=0$ exactly when
$\sin\tau=0$. The density $|e_4\rangle\langle e_4|$ proves necessity
also when the return condition is stated by probabilities. At these times
the two-plane exponential is $(-1)^me^{-i\pi md}I$, and the asserted
blocks follow. $\det B=1$, while the bright plane contributes the phase
twice on $W$. At every time, independently,
$\det(U(t)|_W)=\exp(-it\operatorname{tr}(H|_W)/\hbar)=e^{-iJt/\hbar}$.
The seven-state determinant cannot be substituted for the five-state one.

At a general time $K$ has the same $B$ and spectators and joint entry $A$,
so

$$
K(t)^\dagger K(t)
 =I_V-\eta^2\sin^2\tau\,|e_4\rangle\langle e_4|.
$$

This proves trace nonincrease and the precise trace-preserving condition.
The single Kraus representation proves complete positivity, also with any
passive reference. Dividing $\Phi_t(\rho)$ by its nonzero trace is a
conditional transformation. At nonreturns the success probabilities on
$e_0$ and $e_4$ differ, so this normalization does not define a deterministic
linear channel on all densities.

In $PHP|_V$ the missing bright coupling leaves the entry $J$ at $e_4$.
At return $e^{-iJt_m/\hbar}=\lambda_m^2$, whereas the true entry is
$\lambda_m$. Equality requires $\lambda_m=1$.
Both operators fix $e_0$, so projective equality also requires the scalar
to be one. Their unrestricted unitary channels consequently agree exactly
under the same condition. $\square$

## 3. Exact correction in the fixed real frame

**Theorem 3.1 (One side, two sides and complete five-state channels).**
Under Assumption 1.3, a return endpoint admits a left correction, a right
correction, or two-sided corrections giving the exact matrix $S$ if and
only if

$$
\lambda_m=i,\qquad \operatorname{Re}(g)\sin\theta_m=0.
$$

For equality of the complete unrestricted five-state channel of $S$, each
of these three correction arrangements has instead the criterion

$$
\lambda_m\in\{i,-i\},\qquad \operatorname{Re}(g)\sin\theta_m=0.
$$

A nonreturn pulse cannot give an all-input deterministic $V$ unitary by
these pre/post corrections. These conclusions concern the stipulated
correction group in the original $D_3$ frame.

Proof. $D_3$ commutes with $U_m$ and $S$, since its entries on $e_1,e_3$
coincide. Thus in passive $D_3$ coordinates the two displayed endpoints
are unchanged and corrections are in $SO(5)$. Write $u=e^{i\phi}$ and
$w=-\cos\phi\sin\theta_m$. Entrywise imaginary parts satisfy

$$
\operatorname{Im}B(\theta_m)=\begin{pmatrix}0&w\\w&0\end{pmatrix}.
$$

Hence $B$ is real if and only if the asserted realness condition holds;
when real, its unitarity and determinant one make it an $SO(2)$ matrix.

For completeness, two unitaries give the same conjugation on all densities
if and only if they differ by a scalar. Their relative unitary must commute
with every rank-one projector, hence preserve every line. Basis lines make
it diagonal and lines through pairwise sums make all diagonal scalars equal.
This also shows why the full density domain matters.

For a left correction, $OU_m=\zeta S$ forces
$O=\zeta S U_m^\dagger$. Its entries on $e_0,e_2$ are $\zeta$;
reality requires $\zeta=\pm1$. The determinant condition is

$$
1=\det O=\zeta^5i/\lambda_m.
$$

The one-particle block must be real. With $\zeta=1$ this gives
$\lambda_m=i$; with $\zeta=-1$ it gives $\lambda_m=-i$.
For right corrections the same calculation applies, since $S$ commutes
with $U_m$.

To prove necessity for arbitrary two-sided mixing, suppose
$O_LU_mO_R=e^{i\gamma}S$ with $O_L,O_R\in SO(5)$.
Real orthogonal multiplication preserves the rank and singular values of
the entrywise imaginary part. Those of $\operatorname{Im}U_m$ are

$$
|w|,|w|,|\operatorname{Im}\lambda_m|,0,0.
$$

Their rank is at most three, whereas

$$
\operatorname{Im}(e^{i\gamma}S)
 =\operatorname{diag}(\sin\gamma,\sin\gamma,\sin\gamma,
                      \sin\gamma,\cos\gamma)
$$

has rank at least four if $\sin\gamma\ne0$.
Thus $e^{i\gamma}=\zeta=\pm1$. The target now has exactly one nonzero
imaginary singular value, equal to one. The doubled value $|w|$ must vanish,
and $|\operatorname{Im}\lambda_m|=1$. Finally
$\lambda_m=\zeta^5i=\zeta i$ by determinants. For literal $S$ the sign
is positive. This proves two-sided necessity without restricting the
corrections to the two-plane block.

Conversely let $O_0$ equal $B(\theta_m)^{-1}$ on $(e_1,e_3)$ and the
identity on the other three coordinates. If $B$ is real then $O_0\in SO(5)$.
For $\lambda_m=i$ it gives $O_0U_m=U_mO_0=S$.
For $\lambda_m=-i$, use also

$$
F=\operatorname{diag}(-1,-1,-1,-1,1)\in SO(5);
\qquad FO_0U_m=-S.
$$

Conjugating the corrections back by $D_3$ gives the required members of
$G_{\mathbb R}$. The one-sided constructions also establish two-sided
sufficiency. At nonreturns a right correction maps $V$ onto $V$ and
preserves $\|QUP\|$; a $V$-preserving post correction cannot remove the
outside component. Thus a unitary $V$ endpoint still requires a return.

Determinant alone is insufficient for the projective statements:
$e^{-i\pi/10}S$ has determinant one, and in odd dimension a real orthogonal
matrix of determinant $-1$ has the same channel as its negative in $SO(5)$.
The imaginary-part argument supplies the additional obstruction.
In particular no scalar multiple of $S$ is real, since its first four
entries and its last entry have relative phase $i$. $\square$

**Proposition 3.2 (All finite exact quarter phases and the obstruction).**
A positive return has joint phase $i$ or $-i$ if and only if
$d=p/q$ is rational in lowest terms with positive even denominator $q$.
More explicitly, for a specified positive $m$,

$$
\lambda_m=i
\quad\Longleftrightarrow\quad
d=1-\frac{4k+1}{2m},\qquad k=0,\ldots,m-1.
$$

The corresponding energy ratio is
$J/r=4d/\sqrt{1-d^2}$. A finite positive corrected exact $S$ matrix or
complete $S$ channel exists under Assumption 1.3 exactly when

$$
\operatorname{Re}(g)=0
\quad\hbox{and}\quad
 d\in\mathbb Q\text{ has even reduced denominator}.
$$

For every allowed $g,J$, the fixed $H$ pulse alone never gives an exact
$S$ matrix or its complete channel at positive time.

Proof. The phase equation is
$m(1-d)=1/2+2k$; $-1<d<1$ gives the indicated range of $k$.
If $\alpha$ is irrational, no nonzero integer multiple can be an integer
plus a quarter. If $\alpha=a/b$ in lowest terms, its powers form exactly
the $b$th roots of unity, containing $i$ and $-i$ precisely when $4\mid b$.
For $d=p/q$ reduced, $\alpha=(q-p)/(2q)$. If $q$ is even, $p$ and
$q-p$ are odd and $\gcd(q-p,2q)=1$, so $b=2q$ is divisible by four.
If $q$ is odd, $b$ is $q$ or $2q$ and is not divisible by four.
This treats positive, negative and zero $p$.

Suppose $\lambda_m=\pm i$ and $\sin(\pi mx)=0$ simultaneously.
The phase makes $L=2md$ an odd integer; the sine condition makes $k=mx$
an integer. Multiplying $d^2+4x^2=1$ by $4m^2$ gives

$$
4m^2=L^2+16k^2.
$$

The two sides are respectively zero and one modulo four, a contradiction.
For $\operatorname{Re}(g)\ne0$ this rules out Theorem 3.1's exact realness
condition at every quarter phase. For $\operatorname{Re}(g)=0$ that
condition is automatic, and the denominator criterion is sufficient.
A $-i$ finite phase can also be replaced by an $i$ phase using the cyclic
phase subgroup, so the existence criteria for matrix and channel coincide.

For a pulse without corrections, equality of a complete channel forces
uniform return and $U_m=\zeta S$. The fixed vacuum makes $\zeta=1$,
and the single-particle block must equal $I$. In particular its sine
vanishes, contradicting the same modulo-four equation. Repetition of only
this fixed Hamiltonian with nonnegative durations adds the durations;
it does not change the conclusion. No assertion about interleaved other
controls is made by this single-Hamiltonian statement. $\square$

**Proposition 3.3 (An exact corrected design with a nonzero excursion).**
Fix $r>0$ and prescribe, relative to the original real frame,

$$
g=ir,\qquad J=\frac{4r}{\sqrt3},\qquad
 t_* =\frac{\pi\sqrt3\hbar}{4r}.
$$

Then $t_*=t_1$, $\Delta=8r/\sqrt3$, $d=1/2$,
$x=\sqrt3/4$, $\eta=\sqrt3/2$, and $\lambda_1=i$.
There is a separately supplied real inverse rotation $R_0\in G_{\mathbb R}$
with $R_0U(t_*)|_V=S$. For every $V$ density,

$$
L_\rho(t_*/2)=3\kappa/4.
$$

Proof. Substitute in Theorems 2.2–2.3. With
$\theta_*=\pi\sqrt3/4$, the two-plane endpoint is

$$
B_* =\begin{pmatrix}\cos\theta_*&\sin\theta_*\\
                    -\sin\theta_*&\cos\theta_*\end{pmatrix}.
$$

Take $R_0=B_*^{-1}$ on $(e_1,e_3)$ and identity on $e_0,e_2,e_4$.
It is in $SO(5)$ and commutes with $D_3$, hence lies in the stipulated
group and corrects the endpoint exactly. At half time $\tau=\pi/2$
and $\chi=\pi/4$, so the leakage coefficient is $\eta^2=3/4$.
The true joint return phase is $i$ while the $PHP$ exponential gives $-1$;
the determinants on $V,W$ are $i,-1$ respectively.

The ordinary inverse *bosonic beam splitter* giving $B_*^{-1}$ in the
single-particle sector also acts by its symmetric square on two particles.
It sends $e_4$ outside $V$ with probability

$$
\sin^2(2\theta_*)=\sin^2(\pi\sqrt3/2)>0,
$$

because $\sqrt3/2$ is not an integer. It is therefore not the stipulated
selective $R_0$ that fixes $e_4$. An exact endpoint formula does not supply
that selective operation. $\square$

## 4. Fixed-parameter synchronous approximation

**Definition 4.1 (Return-orbit approximation).**
For fixed $g,J,\hbar$, approximation to $S$ means existence of positive
integers $m_j$ and, where allowed by Assumption 1.3, corrections giving
operator-norm convergence to $S$. Complete-channel approximation means
convergence of their unitary conjugation channels, for example in diamond
norm. It allows a scalar representative but retains every $V$ coherence.
One-sided and two-sided corrections may depend on $j$.
Define the two unsaturated integer-relation lattices

$$
\begin{aligned}
\mathcal L_x&=\{(h,k)\in\mathbb Z^2:h\alpha+kx\in\mathbb Z\},\\
\mathcal L_{x/2}&=\{(h,k)\in\mathbb Z^2:h\alpha+k(x/2)\in\mathbb Z\}.
\end{aligned}
$$

“Unsaturated” means that the condition is integrality of the actual
character: one does not replace a relation by a divided relation whose
value is merely rational.

**Theorem 4.2 (Complete fixed-model approximation criteria).**
For every fixed nonzero complex $g$, finite real $J$ and positive $\hbar$:

1. The joint phase orbit $\{\lambda_m:m\geq1\}$ is finite if $d$ is rational
   and dense in the circle if $d$ is irrational. Its closure contains $i$
   or $-i$ exactly when $d$ is irrational or $d$ has even reduced rational
   denominator.
2. If $\operatorname{Re}(g)=0$, one-sided or two-sided supplied real
   corrections permit arbitrary approximation to $S$, as a matrix or
   complete channel, exactly under that phase-closure condition.
3. If $\operatorname{Re}(g)\ne0$, these same corrected matrix and channel
   approximation conditions are equivalent to

$$
\boxed{\quad (h,k)\in\mathcal L_x\ \Longrightarrow\ 4\mid h.\quad}
$$

4. With no corrections, matrix and complete-channel approximation to $S$
   are equivalent, for every phase of $g$, to

$$
\boxed{\quad (h,k)\in\mathcal L_{x/2}\ \Longrightarrow\ 4\mid h.\quad}
$$

Every successful approximation can use arbitrarily large positive return
indices. None of these conclusions supplies a quantitative hitting-time
bound or permits varying the fixed parameters with accuracy.

Proof. The necessary compactness and projective arguments are first made
explicit. $SO(5)$ is compact. The endpoints belong to the compact family
$A(\theta,\lambda)$ with spectators $1,1$, block $B(\theta)$ and last
entry $\lambda$, parametrized by two circles. Any convergent corrected
sequence has a subsubsequence in which its endpoint, left correction and
right correction all converge. The limiting corrections remain in
$SO(5)$ and Theorem 3.1's imaginary-part proof applies to the limiting
endpoint. Thus matrix convergence requires

$$
\lambda_{m_j}\longrightarrow i,\qquad
|\cos\phi\sin(\pi m_jx)|\longrightarrow0.
$$

For channel convergence it requires instead distance of $\lambda_{m_j}$
from $\{i,-i\}$ tending to zero, with the same sine condition.
If either necessity failed for the whole sequence, compactness would
produce a limiting counterexample, proving these necessities for whole
sequences as well as subsequences. One may select a subsequence with a
fixed limiting sign.

For this argument on channels, equality up to scalar was proved in
Theorem 3.1. Convergence of complete channels is equivalently convergence
in operator norm up to scalar: otherwise compactness of $U(5)$ would
produce a limit with the same channel but positive distance from the
scalar orbit. Conversely expanding two products, also with an arbitrary
ancilla, gives

$$
\|\operatorname{Ad}_A-\operatorname{Ad}_B\|_\diamond
 \leq2\|A-B\|.
$$

This justifies both channel necessity and sufficiency without substituting
a restricted observation algebra for the full matrix algebra.

For the orbit step use the classical Kronecker character criterion,
attributed in the existing [Onishchik/Kronecker note](../../../Library/Fourier/onishchik2020kronecker.md)
to the [Encyclopedia of Mathematics entry](https://encyclopediaofmath.org/index.php?title=Kronecker_theorem&oldid=47528).
The following argument supplies the needed character and positive-index
steps inside this model-specific proof. They are standard torus facts,
not additional new theorems of this volume.

Let $\beta$ denote either $(\alpha)$, $(\alpha,x)$ or $(\alpha,x/2)$,
and put $C=\overline{\mathbb Z\beta}$ in the corresponding finite torus.
For any integer $Q\geq1$, pigeonhole $Q^n+1$ points $j\beta$ into $Q^n$
cubes of side $1/Q$. Subtraction gives a positive $q\leq Q^n$ with
$\operatorname{dist}(q\beta,0)\leq\sqrt n/Q$.
Either these $q$ have an unbounded subsequence tending back to zero,
or one bounded value $q_0$ recurs and satisfies $q_0\beta=0$ exactly.
In the latter case use its arbitrarily large positive multiples.
Thus in both cases there are $q_\ell\to\infty$ with $q_\ell\beta\to0$.
For each integer $a$, $(q_\ell+a)\beta\to a\beta$ through every sufficiently
late positive tail. Hence each positive-tail closure is $C$, a compact
subgroup. This replaces discrete positive powers by integer powers,
not by a continuous-time torus flow.

Every relation $v\cdot\beta\in\mathbb Z$ forces
$v\cdot y\in\mathbb Z$ on $C$. To see sufficiency, if $y\notin C$ set
$f(t)=\operatorname{dist}(t,C)$, using the translation-invariant torus
metric. It is continuous, $f(0)=0<f(y)$, and $f(t+\beta)=f(t)$.
Its Fourier coefficient $c_v$ therefore obeys

$$
c_v=e^{-2\pi i v\cdot\beta}c_v,
$$

so vanishes unless $v\cdot\beta$ is integral. For an explicit uniform
approximation, the standard Fejér kernels

$$
F_N(s)=\frac1N\left|\sum_{a=0}^{N-1}e^{2\pi ias}\right|^2
 =\sum_{|a|<N}\left(1-\frac{|a|}{N}\right)e^{2\pi ias}
$$

are nonnegative and have integral one. Away from
$\operatorname{dist}(s,\mathbb Z)<\delta$ they are at most
$1/(N\sin^2(\pi\delta))$ by the geometric sum.
Their product in $n$ coordinates has outside-box mass at most
$n/(N\sin^2(\pi\delta))$. Uniform continuity now gives
$f*\prod F_N\to f$ uniformly: use a prescribed continuity tolerance inside
the box and $2\|f\|_\infty$ times that vanishing mass outside.
Each convolution is a finite Fourier polynomial supported on the integral
relations just identified. If $y$ satisfied all the character conditions,
that polynomial would have equal values at $y$ and $0$.
Uniform convergence would imply $f(y)=f(0)$, a contradiction.
For these three model frequency vectors the needed orbit description is
therefore

$$
y\in C
\quad\Longleftrightarrow\quad
v\cdot y\in\mathbb Z\text{ whenever }v\cdot\beta\in\mathbb Z.
$$

This proof retains all torsion and disconnected components.

Apply it first to $\beta=\alpha$. If $\alpha$ is irrational, its only
integral relation is zero, giving the whole circle; if $\alpha=a/b$
is reduced, its orbit is the finite group of order $b$.
Proposition 3.2 translates quarter-phase membership into even reduced
denominator for $d$, proving assertion 1. In the aligned case
$\operatorname{Re}(g)=0$, every $B(\theta_m)$ is real. Its inverse is a
permitted endpoint correction and leaves the corrected error exactly
$|\lambda_m-i|$. Necessity, including two-sided and projective versions,
follows from the compactness argument. The two quarter targets have the
same finite-group membership and are both in the irrational closure.
This proves assertion 2.

In the nonaligned case, fixed $\cos\phi\ne0$ makes the realness limit
exactly $\operatorname{dist}(mx,\mathbb Z)\to0$.
For matrix approximation the simultaneous target for $(\alpha,x)$ is
$(1/4,0)$ modulo $\mathbb Z^2$.
Its character value is $h/4$, so the orbit criterion is precisely
$4\mid h$ for every $(h,k)\in\mathcal L_x$.
For explicit sufficiency, choose such positive indices and a nearest
integer $\ell_m$ to $mx$. Use the correction that is $(-1)^{\ell_m}$ on
both $e_1,e_3$ and identity elsewhere; its determinant is one.
Writing $\delta_m=\pi(mx-\ell_m)$ gives

$$
\|(-1)^{\ell_m}B(\theta_m)-I\|
 =2|\sin(\delta_m/2)|\leq\pi\operatorname{dist}(mx,\mathbb Z).
$$

Together with $|\lambda_m-i|\to0$ this proves convergence.
The same sign correction works on the right. For the channel branch
$\lambda\to-i$, the target is $(3/4,0)$, whose character values are
$3h/4$; integrality is again exactly $4\mid h$.
The earlier compactness proof rules out any additional two-sided limits.
This proves assertion 3.

Without corrections, $B(\theta_m)$ must approach $+I$.
The Hermitian involution

$$
T_u=\begin{pmatrix}0&u\\\bar u&0\end{pmatrix},\qquad T_u^2=I
$$

has eigenvalues $1,-1$, and $B(\theta_m)=e^{-i\pi mxT_u}$. Hence

$$
\|B(\theta_m)-I\|=2|\sin(\pi mx/2)|.
$$

It tends to zero exactly when $\operatorname{dist}(mx/2,\mathbb Z)\to0$.
The appropriate frequency pair is $(\alpha,x/2)$, with the same target
$(1/4,0)$, giving assertion 4's character criterion. Approaching $-I$
on this block has operator error two and is insufficient.
For pulse-only projective convergence choose scalars $z_j$ with
$z_jU_{m_j}\to S$. Acting on the fixed $e_0$ forces $z_j\to1$, so the
matrices themselves converge to $S$. This holds for every phase of $g$.
Every tail of each positive orbit has the same closure, as already proved,
which supplies arbitrarily large successful indices. $\square$

## 5. Exact ratios and all parameter branches

**Proposition 5.1 (The design ratio and its pulse approximation).**
If $J/r=4/\sqrt3$, then

$$
d=\tfrac12,\qquad \alpha=\tfrac14,\qquad x=\tfrac{\sqrt3}{4},\qquad
\mathcal L_x=\mathbb Z(4,0),\quad
\mathcal L_{x/2}=\mathbb Z(4,0).
$$

Thus pulse-only approximation to $S$ succeeds for every fixed phase of
$g$. Corrected approximation also succeeds for every phase; a finite
corrected exact hit exists exactly for $g=\pm ir$.
No phase of $g$ gives a finite pulse-only exact hit.

Proof. In $h/4+k\sqrt3/4\in\mathbb Z$, irrationality of $\sqrt3$ forces
$k=0$, then $4\mid h$. The same reasoning with $\sqrt3/8$ gives the
second lattice. Both criteria of Theorem 4.2 pass.
More explicitly, $m=4n+1$ has $\lambda_m=i$ and

$$
mx/2=n\sqrt3/2+\sqrt3/8.
$$

The irrational circle orbit used inside Theorem 4.2 makes this approach
zero modulo one along arbitrarily late positive indices, giving $B\to I$.
For finite $m>0$, $mx$ is irrational; the exact conclusions follow also
from Proposition 3.2, with $d=1/2$. $\square$

**Proposition 5.2 (Dense phase with an exact synchronous obstruction).**
If $J/r=4$, then

$$
\begin{aligned}
d&=1/\sqrt2,&x&=1/(2\sqrt2),&\alpha&=\tfrac12-x,\\
\mathcal L_x&=\mathbb Z(2,2),&&
\mathcal L_{x/2}=\mathbb Z(2,4).
\end{aligned}
$$

The joint phase is dense, but nonaligned real-corrected approximation and
pulse-only approximation both fail. Aligned $g=\pm ir$ does admit corrected
approximation under Assumption 1.3, without any finite exact corrected hit.

Proof. Since $x$ is irrational,

$$
h\alpha+kx=h/2+(k-h)x\in\mathbb Z
$$

forces $k=h$ and $h$ even. This gives exactly $\mathbb Z(2,2)$,
not its saturation $\mathbb Z(1,1)$.
For $x/2$ the irrational coefficient is $k/2-h$, giving
$\mathbb Z(2,4)$. Each generator has $h=2$, so each synchronous criterion
fails. Irrational $d$ nevertheless gives phase density and the aligned
corrected case by Theorem 4.2.

Directly, the exact relation $2\alpha+2x=1$ gives

$$
\lambda_m^2=e^{-4\pi imx}.
$$

If $\sin(\pi mx)\to0$, its right side tends to one; if
$\lambda_m\to\pm i$, its left side tends to minus one.
For either fixed sign $\sigma\in\{1,-1\}$ one also has

$$
2\leq4|\sin(\pi mx)|+2|\lambda_m-\sigma i|,
$$

by inserting $\lambda_m^2$ between $1$ and $-1$ and using
$|e^{-4i\theta}-1|\leq4|\sin\theta|$ and
$|\lambda_m^2+1|\leq2|\lambda_m-\sigma i|$.
This proves the obstruction without numerical sampling of the phase.
Irrationality of $d$ excludes every finite quarter-phase hit. $\square$

**Proposition 5.3 (A required sign correction at $J/r=1$).**
If $J/r=1$, then

$$
d=\frac1{\sqrt{17}},\qquad x=\frac2{\sqrt{17}},\qquad
\alpha=\frac{1-1/\sqrt{17}}2,
$$

and

$$
\mathcal L_x=\mathbb Z(4,1),\qquad
\mathcal L_{x/2}=\mathbb Z(2,1).
$$

Supplied real corrections permit approximation to $S$ for every fixed
phase of $g$, but pulse-only approximation fails for every phase.
Along every return sequence with $\lambda_m\to i$, one has
$B(\theta_m)\to-I$, which is removable by a real two-coordinate sign
correction and is not removable by a common pulse-only global phase.

Proof. In

$$
h\alpha+kx=h/2+(-h/2+2k)/\sqrt{17},
$$

integrality forces $h=4k$, giving the first lattice. For $x/2$, it forces
$h=2k$, giving the second. The corrected criterion passes whereas the
pulse-only criterion fails. The aligned case passes its phase test as well.
The exact relation $2\alpha+x/2=1$ implies
$m x/2\to1/2$ modulo one whenever $m\alpha\to1/4$ modulo one.
Thus $\theta_m=2\pi(mx/2)$ approaches $\pi$ modulo $2\pi$, proving
$B\to-I$. Minus identity on $(e_1,e_3)$ and identity on the other three
coordinates is in $SO(5)$. The fixed vacuum forbids turning that block
sign into a common phase, as in Theorem 4.2. $\square$

**Proposition 5.4 (Rational, irrational, resonant and sign branches).**
Theorem 4.2 has the following exhaustive parameter interpretation.
For aligned $g=\pm ir$, only its phase-closure test is required.
For nonaligned corrected approximation use $v=x$ below; for pulse-only
approximation, for any fixed phase of $g$, use $v=x/2$.

If $\alpha=a/b$ is rational in reduced form with $b>0$ and $v$ irrational, the relation lattice is
$\mathbb Z(b,0)$ and the test is $4\mid b$.
If $\alpha$ is irrational and $v$ rational, all relations have $h=0$,
so the test succeeds. If both are irrational, the lattice has rank zero
or one; rank zero always succeeds, and rank one succeeds exactly when
its integer generator $(h_0,k_0)$ has $4\mid h_0$.
The generator need not be primitive in $\mathbb Z^2$.
If both frequencies are rational, the orbit is finite and success means
exact quarter-target membership; for the present relation
$d^2+4x^2=1$ that simultaneous rational branch never succeeds.

In particular, rational $d=p/q$ with even reduced $q$ has irrational $x$
and passes both synchronous tests; rational $d$ with odd reduced $q$
fails even the phase test. Irrational $d$ and rational $x$ pass both
synchronous tests. Irrational $d$ and irrational $x$ require the full
rank-zero or rank-one test and cannot be decided by phase density alone.
At $J=0$ every version fails. Replacing $J$ by $-J$ leaves each success
criterion unchanged. Both signs of pure imaginary $g$ are aligned;
every other fixed complex phase is nonaligned.

Proof. For a two-frequency vector, two independent integer relations
solve for both coordinates as rational numbers. Thus the relation lattice
has rank at most one unless both coordinates are rational. In the mixed
rational/irrational cases the displayed lattices follow by comparing the
irrational coefficient; if $v=c/e$ is reduced and $\alpha$ irrational,
the lattice is $\mathbb Z(0,e)$. A rank-one subgroup of $\mathbb Z^2$
is generated by one integer vector, without a requirement that the vector
be primitive in the ambient lattice. Theorem 4.2 then gives the stated
divisibility tests. For two rational coordinates a common denominator
makes the orbit finite, so closure adds no points.

If both $\alpha$ and $x$ were rational and that finite orbit contained
the quarter target, it would give $\lambda_m=i$ and $mx\in\mathbb Z$
for some positive $m$, contrary to Proposition 3.2.
Now let $d=p/q$ have even reduced denominator. If $x$ were rational,
then both frequencies would be rational. To exclude rational $x$ directly,
put $\eta=2x=a/b$ reduced.
If $d=p/q$ and $\eta$ are rational points of $d^2+\eta^2=1$, a primitive
integer Pythagorean triple has odd hypotenuse. Consequently the reduced
denominator of $d$ is odd. To verify this last parity statement without
assuming the parametrization, clear denominators and divide the resulting
integer triple $(A,B,C)$ by its common gcd. If $C$ were even, squares
modulo four force both $A,B$ even, contradicting primitivity. Thus $C$
is odd, and the denominator of $A/C$ is odd. This contradicts even $q$.
Hence $x$ is irrational; $\alpha$ has order divisible by four, so both
mixed-frequency tests succeed. Odd $q$ fails the phase criterion already.
Irrational $d$ is equivalent to irrational $\alpha$, giving the remaining
cases above.

For $J=0$, $(d,\alpha,x)=(0,1/2,1/2)$ and
$\lambda_m=(-1)^m$; relation $(2,0)$ excludes both quarter targets.
Under $J\mapsto-J$, $d\mapsto-d$, $\alpha\mapsto1-\alpha$ and $x$
is fixed. Relations transform by $(h,k)\mapsto(-h,k)$, preserving
$4\mid h$, and the phase subgroup is inverted.
The aligned/nonaligned split depends only on $\operatorname{Re}(g)=0$.
No case uses $r=0$, $\eta=0$, infinite $J$, or varying $J/r$ in a limit.
$\square$

## 6. Near returns and the original permission boundary

**Theorem 6.1 (Uniform near-return stability with fixed supplied corrections).**
For every $t\geq0$ let $m$ be a nearest nonnegative integer to
$\Delta t/(2\pi\hbar)$. Then

$$
\begin{aligned}
|t-t_m|&\leq\frac{\pi\hbar}{4r}\sqrt{\epsilon(t)},\\
\|U(t)|_W-U(t_m)|_W\|
 &\leq\frac{\pi(\Delta+|J|)}{8r}\sqrt{\epsilon(t)}.
\end{aligned}
$$

Consequently permitting endpoint sequences with leakage tending uniformly
to zero over all $V$ densities leaves unchanged every endpoint and complete
channel limit obtainable at exact returns, with no corrections or with
one-sided or two-sided corrections from the fixed supplied $G_{\mathbb R}$.
This includes limits considered up to a common scalar. At nonreturns the
comparison is between the isometries $V\to W$ and their channels, with $V$
embedded in $W$. Their unnormalized compressed CP maps have the same limits;
no conditional normalization is used.

Proof. Put $\delta=\operatorname{dist}(\tau(t),\pi\mathbb Z)$, so
$0\leq\delta\leq\pi/2$ and
$\sin\delta\geq2\delta/\pi$ by concavity of sine. Then

$$
|t-t_m|=\frac{2\hbar\delta}{\Delta}
 \leq\frac{\pi\hbar}{\Delta}|\sin\tau|
 =\frac{\pi\hbar}{4r}\sqrt{\epsilon(t)}.
$$

Integrating the derivative of the unitary group on the finite-dimensional
reducing $W$, and using Proposition 2.1, gives

$$
\|U(t)|_W-U(s)|_W\|
 \leq\frac{\|H|_W\|}{\hbar}|t-s|
 =\frac{\Delta+|J|}{2\hbar}|t-s|.
$$

Combining these proves the second estimate. Restriction and compression
cannot increase the norm. A right correction on $V$ preserves the input
norm and the uniform leakage; extend a left correction to $W$ by identity
on $V^\perp\cap W$ to compare the isometries. This extension is a norm
comparison, not an additionally permitted physical operation.
The same correction matrices can be used for the nearby exact return.
Thus the difference tends to zero for any chosen correction sequence.
Expanding the conjugation products as in Theorem 4.2 gives convergence of
complete channels as well, including ancillas; the estimate is unaffected
by scalar representatives.

Conversely exact-return sequences already have uniformly zero leakage.
Allowing the nearest index $m=0$ adds no quarter-phase limit: at zero the
endpoint is identity, and a limit of products of supplied real corrections
remains in the compact real group, which has no projective representative
of $S$ by Theorem 3.1. Per-input zero leakage at $\kappa=0$ would not give
any estimate on $t-t_m$; the hypothesis here is uniform leakage.
These estimates compare nearby times and do not bound the waiting time
needed for a nontrivial synchronous approximation. $\square$

**Proposition 6.2 (Fixed frame, algebra choice and no native path upgrade).**
A passive Fock rephasing that changes $g$ must transport the stipulated
correction group as well. Canonical CCR, hard-core site operators and CAR
operators do not define the same dynamics on this embedding.
Under the native no-excursion permission of Definition 1.4, every positive
duration $H$ pulse is inadmissible for the full input space $V$, even if
its endpoint returns exactly or satisfies Theorem 6.1.

Proof. If $F=\exp(i\sum_j\beta_j n_j)$ is used as a passive change of
coordinates, then

$$
H'=F^\dagger HF,\qquad
 g'=e^{-i(\beta_1-\beta_3)}g,\qquad
G_{\mathbb R}'=F|_V^\dagger G_{\mathbb R}F|_V.
$$

$S$ commutes with $F|_V$, but the real group need not.
For an explicit witness take $F|_V=\operatorname{diag}(1,-i,1,1,-i)$,
which changes a positive real $g$ to $ir$. Let $O$ be the real quarter
rotation $\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$
on $(e_0,e_1)$, identity elsewhere, and let $R=D_3OD_3^\dagger$.
In the original passive $D_3$ frame, the transported $F^\dagger RF$ has
nonreal off-diagonal entries on that plane. Thus it is not in the unchanged
$G_{\mathbb R}$. Specifying $g=ir$ relative to the original group is a
design premise, not a free convention about its phase.

For hard-core two-state sites, exchange annihilates $e_4$: after removing
one outer particle it attempts to create at the other occupied outer site,
which is zero. The same vanishing holds for spinless CAR modes. In fixed
creation order $1,2,3$ their one-particle matrix is $H_1$ and $e_2$ is
fixed, while $e_4$ has energy $J$. Thus their restrictions are exactly
$PHP|_V$ and their joint phase is $e^{-iJt/\hbar}$ without leakage.
Their algebras differ from CCR, and from each other outside this restriction.
No finite occupation cutoff obeys exact CCR, since the trace of a
finite-dimensional commutator is zero and the trace of identity is not.
A hard-core limit or continual projection is therefore an extra assumption.

For the fixed canonical $H$, Proposition 2.1 gives
$QHe_4=2rb\ne0$, and Theorem 2.2 gives positive leakage from $e_4$ for
all sufficiently small positive times. Every interval of positive duration
contains such times, violating the required path condition. The halfway
leakage in Proposition 3.3 is an additional explicit witness.
Native PXP flips of Static Compatibility–Fiber Theory, Proposition 43,
change total number; this fixed exchange Hamiltonian commutes with
$N=n_1+n_2+n_3$, with parity and with $n_2$. Equality of state labels
cannot identify those generators or their permission sets.
Returning endpoints and supplied correction identities consequently do not
establish a legal native no-excursion synthesis. $\square$

**Proposition 6.3 (Number, parity and the unresolved resource premises).**
On $V$, $S$ is invisible on number-block-diagonal densities and to
number-preserving observables. This restricted equivalence does not imply
equality of its unrestricted five-state channel with identity, or equality
of the true and projected-Hamiltonian unrestricted channels.
Parity alone does not remove the target's relative phase.
None of the preceding Hamiltonian results supplies phase-sensitive
preparation or readout, an encoder/decoder, a source reset, independent
copies or a reference system.

Proof. The number sectors on $V$ are

$$
\operatorname{span}(e_0),\qquad
\operatorname{span}(e_1,e_2,e_3),\qquad
\operatorname{span}(e_4),
$$

with numbers $0,1,2$. $S$ is scalar on each. Thus $[\rho,N]=0$ implies
$S\rho S^\dagger=\rho$, and $[M,N]=0$ implies $S^\dagger MS=M$.
For the latter statement $\operatorname{tr}(MS\rho S^\dagger)
=\operatorname{tr}(M\rho)$ even if a cross-number-coherent $\rho$ is
formally specified. At return, true and projected evolutions differ only
by an $e_4$-sector scalar, so the same restricted indistinguishability
applies. The vacuum-fixed projective argument in Theorem 2.3 nevertheless
distinguishes their complete channels unless $\lambda_m=1$.

For a parity-preserving distinction, if separately supplied take

$$
\psi=\frac{e_0+e_4}{\sqrt2},\qquad
Y=-i|e_0\rangle\langle e_4|+i|e_4\rangle\langle e_0|.
$$

Both respect parity, and

$$
\langle\psi,Y\psi\rangle=0,\qquad
\langle S\psi,YS\psi\rangle=1.
$$

$Y$ is not number preserving. The fixed $H$ leaves vacuum fixed and
conserves number, so it cannot prepare $\psi$ from vacuum or by itself
supply that readout. Assumption 1.3 includes rotations across number or
parity sectors; an additional superselection restriction would require
intersecting that stipulated group with the actual allowed controls.
The selective correction of Proposition 3.3 does preserve number and parity,
but its availability remains the stated premise.

The definitions impose neither a map implementing the bosonic embedding
on an actual native source nor preparation, reference or terminal readout
instruments for it. Such additional objects and their composition laws
would be new hypotheses, not consequences of the endpoint equalities.
The results here determine the fixed model's leakage, return, correction
and approximation conditions. They make no sharp recovery-error assertion
for the original encoder/decoder problem of Static Compatibility–Fiber
Theory, Definitions 1.5 and following, and no time-cost optimum.
The physical supply and recovery bridges remain separate mathematical
obligations. $\square$

## 追加锚（本行以下为增补区）

## 7. Mode language and the leakage--return bridge

A free real scalar field in a finite periodic box gives the usual oscillator
language after a finite mode truncation. If $e_a$ are real orthonormal
Laplacian eigenmodes and $\phi=\sum_a q_a e_a$, then

$$
L=\frac12\sum_a\left(\dot q_a^2-\omega_a^2q_a^2\right),
\qquad
\omega_a^2=c^2\kappa_a^2+\omega_0^2.
$$

For one mode, $p=\dot q$ and

$$
\alpha=\frac1{\sqrt2}\left(\sqrt\omega\,q
       +i\frac p{\sqrt\omega}\right)
$$

satisfy $\dot\alpha=-i\omega\alpha$ and hence
$\alpha(t)=e^{-i\omega t}\alpha(0)$. The circle is in the $(q,p)$ phase
plane; it is not by itself a pair of spatial directions. Quantization adds
the canonical commutation relations. In particular, the five-dimensional
space $V$ above is an encoded or truncated sector: it cannot carry exact
$[a,a^\dagger]=I$ for a nonzero finite identity, since taking traces would
give $0=\dim V$. The mode construction therefore supplies an interpretation
of the oscillator terminology, not a derivation of the particular Hamiltonian
in Assumption 1.2. A standard free-field construction is given, for example,
in Tong, [*Quantum Field Theory*, §2](https://www.damtp.cam.ac.uk/user/tong/qft/qfthtml/S2.html).

**Proposition 7.1 (Retained-space defect identity).** Let $P$ be an
orthogonal projection, $Q=I-P$, and $U$ a unitary on a reducing finite
subspace. On $P\mathcal H$ put

$$
K=PUP\big|_{P\mathcal H},
\qquad
L=QUP\big|_{P\mathcal H}.
$$

Then

$$
I_{P\mathcal H}-K^\dagger K=L^\dagger L\succeq0.
\tag{7.1}
$$

Thus the norm loss of the retained compression is exactly the squared
amplitude sent into the complementary channel. For the seven-state model,
Theorem 2.2 gives

$$
L=C(t)|b\rangle\langle e_4|,
\qquad
I_V-K(t)^\dagger K(t)
=\eta^2\sin^2\!\tau(t)\,|e_4\rangle\langle e_4|.
\tag{7.2}
$$

For a density $\rho$ on $V$, the retained trace is therefore

$$
1-\operatorname{tr}\!\left(K(t)\rho K(t)^\dagger\right)
=\eta^2\sin^2\!\tau(t)\,\langle e_4,\rho e_4\rangle.
\tag{7.3}
$$

**Proof.** Insert $P+Q=I$ between the two copies of $U$ and use
$U^\dagger U=I$:

$$
K^\dagger K+L^\dagger L
=P U^\dagger(P+Q)UP\big|_{P\mathcal H}
=I_{P\mathcal H}.
$$

The displayed seven-state formulas then give (7.2), and taking the trace
pairing with $\rho$ gives (7.3). $\square$

Because the present $W$ is finite dimensional, the short-time statement can
also be made in operator norm. For $U(t)=e^{-itH/\hbar}$,

$$
Q U(t)P\big|_V
=-\frac{it}{\hbar}QHP\big|_V+O(t^2),
\qquad
\operatorname{tr}(Q U(t)\rho U(t)^\dagger)
=\frac{t^2}{\hbar^2}\operatorname{tr}\!\left(PH QH P\,\rho\right)+O(t^3).
\tag{7.4}
$$

Here $QHP=2r|b\rangle\langle e_4|$, so (7.4) has leading coefficient
$4r^2\langle e_4,\rho e_4\rangle/\hbar^2$, agreeing with the exact
formula (7.3). This identifies $QHP$ as the initial coupling interface;
it does not by itself imply irreversible decay.

**Proposition 7.2 (The first excursion can return).** With the same $P,Q$
and $K(t)$,

$$
P U(2t)P\big|_V
=K(t)^2+P U(t)Q U(t)P\big|_V.
\tag{7.5}
$$

For the fixed bosonic model,

$$
P U(t)Q U(t)P\big|_V
=C(t)^2|e_4\rangle\langle e_4|
=-\eta^2e^{-2i\chi(t)}\sin^2\!\tau(t)
  |e_4\rangle\langle e_4|.
\tag{7.6}
$$

Consequently the compression $K(t)^2$ is not, in general, the two-time
evolution restricted to $V$. The missing term is precisely the amplitude
that leaves through $b$ during the first interval and returns during the
second one. At the uniform return times of Theorem 2.3 it vanishes because
$C(t)=0$; away from those times it must be retained in any multi-step readout
calculation.

**Proof.** The group law gives
$P U(2t)P=P U(t)(P+Q)U(t)P$, which is (7.5). Theorem 2.2 gives
$Q U(t)P=C(t)|b\rangle\langle e_4|$ and, from the displayed action on $b$,
$P U(t)Q=C(t)|e_4\rangle\langle b|$. Their product is (7.6). $\square$

The operator quantities in (7.1)--(7.6) are distinct from the four-corner
seam responses in the local-clock volume. A seam kernel becomes a leakage or
decay observable only after an explicit map from the physical evolution and
the accessible output instrument to that kernel has been supplied. The
existing seam boundary therefore remains in force: nonzero seam response
establishes sensitivity of the specified readout, while a lifetime or an
irreversible decay law additionally requires a dynamical coupling, a return
analysis, an output event and a time calibration.

## 追加锚（本行以下为增补区）

## 8. Frequency domain of the mode interpretation

The oscillator coordinate in Section 7 is defined for a positive-frequency
mode, $\omega>0$. In the displayed dispersion relation this means
$c^2\kappa_a^2+\omega_0^2>0$. If that quantity is zero, the corresponding
classical mode instead has $L=\dot q^2/2$, $p=\dot q$,
$p(t)=p(0)$ and $q(t)=q(0)+tp(0)$; the formula containing
$1/\sqrt\omega$ is undefined and supplies no circular oscillator phase.
This frequency condition belongs to the free-field interpretation only.
It does not change Assumption 1.2's fixed nonzero $g$, finite real $J$,
positive $\hbar$, or any seven-state leakage, return or correction identity.

## 追加锚（本行以下为增补区）
