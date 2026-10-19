# AURIC FIB Five-Window Quantum Memory

> This volume is an appendable mathematical reference. Its statements use the
> ordinary `generic-v1` Markdown structure. Once incorporated, existing text and
> numbering remain fixed; subsequent corrections and extensions follow the final
> append anchor and identify the statements they supersede.

## 1. Scope, mathematical status, and reading contract

**Convention 1.1 (Ordinary mathematics).** This volume gives finite-dimensional
complex linear algebra, definitions, and ordinary mathematical proofs. It is
reference input rather than a Lean source and makes no kernel-verification claim.
The source interface is the fixed-activity classical law specified in §3; the
class of completely positive trace-preserving maps in §2 is an additional
mathematical modeling choice. Classical probabilities alone do not specify that
choice or an element of the class.

**Convention 1.2 (Operational contract).** A chronological step retains precisely
one five-dimensional system. One fixed channel on that system is repeated at one
fixed parameter. Each application has a fresh environment, which is discarded;
no environment, old bit, measurement outcome, or history register is retained.
An exact-code decoder acts only after the final application. A reference system
used to test entanglement breaking is external and is never incorporated into the
retained five-dimensional output. Chronological order is a mathematical index,
not a physical time calibration. The native complete-window affine operation of
[LocalClock, Definition 15.1][LC] is a different operation.

**Convention 1.3 (Dependence and attribution).** Standard Stinespring, Choi,
Knill–Laflamme, and entanglement-breaking facts are credited where they are used.
The model-specific statements are the explicit derivations in this volume.
Classical general results remain owned by [LocalClock, Propositions 15.6 and
15.8][LC] and [Pyramid, §§17–18][PY]. Section 16 specifies the literature and
interpretation boundaries. In particular, the exact-code theorem is not an
assertion about asymptotic quantum capacity or about every lift becoming
entanglement breaking.

## 2. Spaces, channels, and the all-input population law

**Definition 2.1 (Five windows and coordinate sectors).** Let

$$
\Omega=(000,100,010,001,101),\qquad H=\mathbb C^5,
$$

with the corresponding ordered orthonormal basis $|0\rangle,\ldots,|4\rangle$.
Write

$$
\begin{aligned}
P_j&=|j\rangle\langle j|,& z&=|2\rangle,\\
A&=\operatorname{span}\{|0\rangle,|1\rangle\},&
B&=\operatorname{span}\{|2\rangle\},\\
D&=\operatorname{span}\{|3\rangle,|4\rangle\},& L&=A\oplus B.
\end{aligned}
$$

The projection onto a subspace $R$ is $P_R$. The letter $B$ in this notation
is a coordinate sector, not a random bit. Inner products are conjugate-linear
in the first argument. Adjoint is denoted by $\dagger$; ordinary transpose by
$\mathsf T$. The column $\operatorname{diag}X$ lists the diagonal entries of $X$.
The full algebra of operators supported on a subspace $C$ is $\mathcal B(C)$,
viewed as a subalgebra of $M_5(\mathbb C)$.

**Definition 2.2 (Allowed lifts).** Fix $0<\eta<1$ and put $r=1-\eta$. Define the
row-stochastic matrix

$$
Q=Q_\eta=
\begin{pmatrix}
r&0&0&\eta&0\\
r&0&0&\eta&0\\
0&r&0&0&\eta\\
0&0&1&0&0\\
0&0&1&0&0
\end{pmatrix}.
\tag{2.1}
$$

An allowed lift is a complex-linear CPTP map $\Phi:M_5(\mathbb C)\to
M_5(\mathbb C)$ satisfying

$$
\operatorname{diag}\Phi(X)=Q^{\mathsf T}\operatorname{diag}X
\quad\text{for every }X\in M_5(\mathbb C).
\tag{2.2}
$$

Thus $Q_{ij}$ is the population transition from input $i$ to output $j$.
Equation (2.2) includes non-Hermitian and off-diagonal inputs. It is stronger
than prescribing only $\operatorname{diag}\Phi(P_i)$.
If $\Delta$ deletes off-diagonal entries, (2.2) implies
$\Delta\Phi=\Delta\Phi\Delta$, the detection-incoherent condition of
[Theurer et al., Definition 3 and supplemental Proposition 15][THE]. It does
not require $\Phi\Delta=\Delta\Phi\Delta$: output coherences are permitted.

**Definition 2.3 (Exact subspace memory).** For an allowed lift let $k_n(\Phi)$
be the largest complex dimension of a subspace $C\subseteq H$ for which there
is a CPTP map $\mathcal R:M_5\to M_5$ with

$$
\mathcal R\Phi^n(X)=X\qquad(X\in\mathcal B(C)).
\tag{2.3}
$$

Set $k_0(\Phi)=5$, and let $K_n(\eta)$ be the maximum of $k_n(\Phi)$ over the
allowed lifts. Codes are arbitrary complex subspaces; no coordinate, real,
stabilizer, or prescribed-encoding restriction is imposed. Recoverability of a
later iterate implies recoverability of every prefix by composing its decoder
with the remaining iterates. Such composition is a proof of a necessary
property, not an inserted intermediate operation. In particular
$k_{n+1}(\Phi)\le k_n(\Phi)$. Every one-dimensional code is recoverable by a
terminal reset to its unique pure state.

**Definition 2.4 (Entanglement breaking and its index).** A channel is
entanglement breaking (EB) if its application to one part of every bipartite
state produces a separable state. Its index is

$$
n_{\mathrm{EB}}(\Phi)=\min\{n\ge1:\Phi^n\text{ is EB}\},
$$

with value $\infty$ if this set is empty. A state is NPT if its partial
transpose on the reference has a negative eigenvalue. Separable states are
positive under this transpose: apply transpose to each positive reference
factor of a separable decomposition. Hence an NPT output witnesses failure of
EB. A composition with an EB channel is EB, so the EB iterates, if present,
form a terminal interval. Exact subspace correction and failure of EB are
different properties.

## 3. Faithful classical-source interface

**Definition 3.1 (Fixed-activity source supplied by LocalClock).** Let
$\lambda>0$ be fixed. Consider the no11 bit-word Gibbs family with weight
$\lambda^{\#\mathrm{ones}}$, compatible fixed nonnegative endpoint factors,
and positive partition function. Its two-sided body limit, with the observation
receding from both endpoints, is the stationary Perron–Markov law in
[LocalClock, Proposition 15.8][LC]. Its parameters and transition matrix are

$$
\begin{aligned}
\Lambda&=\frac{1+\sqrt{1+4\lambda}}2,&
\eta&=\frac{\Lambda-1}{\Lambda},& r&=\Lambda^{-1},&
\lambda&=\frac{\eta}{r^2},\\
P_\eta&=\begin{pmatrix}r&\eta\\1&0\end{pmatrix},&
\pi&=\frac{(1,\eta)}{1+\eta}.
\end{aligned}
\tag{3.1}
$$

Indeed, with $v=(\Lambda,1)^{\mathsf T}$ and
$H_\lambda=\left(\begin{smallmatrix}1&\lambda\\1&0\end{smallmatrix}\right)$,
the normalization is the Perron conjugation

$$
H_\lambda=\Lambda\operatorname{diag}(v)P_\eta
\operatorname{diag}(v)^{-1},
$$

rather than separate row normalization of the unnormalized guard matrix.
At $\lambda=1$ this is the unit-activity golden case of
[LocalClock, Proposition 15.6][LC], with $\eta=\phi^{-2}$.
The existence and body-limit conclusions are those owning results, not new
claims about arbitrary sources.

**Theorem 3.2 (The chosen source induces the displayed chronological kernel).**
For the stationary chain in Definition 3.1 the triple distribution in the fixed
order $\Omega$ is

$$
p=\frac1{1+\eta}
\begin{pmatrix}r^2\\\eta r\\\eta\\\eta r\\\eta^2\end{pmatrix}.
\tag{3.2}
$$

The chronological window $abc$ followed by $bcd$ has kernel (2.1), with
$Q^{\mathsf T}p=p$. For $n\ge2$ its powers satisfy

$$
(Q^n)_{abc,ijk}=(P_\eta^{\,n-2})_{c i}(P_\eta)_{ij}(P_\eta)_{jk}.
\tag{3.3}
$$

In particular $Q^4$ has every entry strictly positive.

Proof. The five probabilities are, respectively,
$\pi_0r^2$, $\pi_1r$, $\pi_0\eta$, $\pi_0r\eta$, and $\pi_1\eta$,
which give (3.2). The next bit of this specified one-step Markov source has
conditional distribution $P_{cd}$ given the entire past. Thus

$$
Q_{abc,b'c'd}=\mathbf1_{(b,c)=(b',c')}P_{cd}.
$$

For inputs $000,100$ the outputs are $000,001$ with probabilities $r,\eta$;
for $010$ they are $100,101$ with those probabilities; and for $001,101$ the
next bit is forced to zero and the output is $010$. These are precisely the
five rows of (2.1). Stationarity of the bit source gives stationarity of its
triple; alternatively direct multiplication of (3.2) gives
$Q^{\mathsf T}p=p$.
After $n\ge2$ shifts the first bit of the output is $n-2$ transitions beyond
the input's last bit, and the two remaining output bits contribute their two
internal transitions. Summing over the intermediate bits gives (3.3).
Finally

$$
P_\eta^2=\begin{pmatrix}r^2+\eta&r\eta\\r&\eta\end{pmatrix}>0.
$$

Every legal triple has positive internal transition product, so (3.3) at
$n=4$ proves $Q^4>0$. This is a statement of classical primitivity. It does
not identify the quantum peripheral spectrum. $\square$

**Definition 3.3 (General sources and chosen extensions).** A general actual
source here means a two-sided stationary binary process $(B_i)_{i\in\mathbb Z}$
with $B_iB_{i+1}=0$ almost surely. [Pyramid, Definition 17.1 and Theorem 17.3][PY]
give its triple law as

$$
p(t,\kappa)=(1-3t+\kappa,\ t-\kappa,\ t,\ t-\kappa,\ \kappa),
$$

where $t=\mathbb P(B_0=1)$ and $\kappa=\mathbb P(B_0=B_2=1)$. Full positivity
is equivalent to

$$
0<t<\tfrac12,\qquad \max(0,3t-1)<\kappa<t.
\tag{3.4}
$$

The selected second-order extension of [Pyramid, Definition 18.1][PY] has
pair-state order $(00,01,10)$ and matrix

$$
K^{(2)}=\begin{pmatrix}1-\alpha&\alpha&0\\0&0&1\\1-\beta&\beta&0\end{pmatrix},
\qquad
\alpha=\frac{t-\kappa}{1-2t},\quad\beta=\frac\kappa t.
\tag{3.5}
$$

[Pyramid, Theorems 18.2–18.3][PY] own its unique at-most-second-order
realization and its entropy-rate selection among all sources with that triple
law. Those are conditional selection results, not identifications of every
actual source. A chosen second-order extension induces a chronological window
kernel using $\alpha$ after $00$, $\beta$ after $10$, and forced zero after
$01$. It equals (2.1) for the fixed-activity parameters

$$
t=\frac\eta{1+\eta},\qquad\kappa=\frac{\eta^2}{1+\eta},\qquad
\alpha=\beta=\eta.
\tag{3.6}
$$

For a general source with the same triple marginal, even the one-step
conditional transition of the triple depends on four-bit probabilities, and
the triple process need not be Markov. Equality of five local probabilities
therefore supplies neither this $Q$ nor a homogeneous quantum lift. The
actual same-local-law sources of [Pyramid, Proposition 17.4][PY], and their
comparison with the selected extension in Theorem 18.2, furnish the inherited
counterexample; no new counterexample or reproving of that result is needed
here. Their parameters are not being identified with every fixed-activity
parameter.

**Convention 3.4 (Actual native operation).** In [LocalClock, Definition 15.1][LC]
the printed triple is low, middle, high, while native reading is high to low.
The state includes a guard and $C\in\mathbb N^2$. In the order $\Omega$, put

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
S_{\mathrm{nat}}=M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},
$$

and

$$
(d_{000},d_{100},d_{010},d_{001},d_{101})
=((0,0),(1,0),(0,1),(1,1),(2,1)).
$$

On a legal native complete-window event,
$C'=S_{\mathrm{nat}}C+d_s$; the empty window also multiplies by
$S_{\mathrm{nat}}$. This is not the chronological overlap map $abc\mapsto bcd$.
A five-state Hilbert-space label records the window but not the complete
native composition state. No equivalence of these two operation counts is
assumed.

## 4. The complete eight-edge quantum-lift class

**Theorem 4.1 (Necessary and sufficient Choi and Stinespring parameters).**
Use the unnormalized output-first Choi convention

$$
J_\Phi=\sum_{i,i'=0}^4\Phi(|i\rangle\langle i'|)
\otimes |i\rangle\langle i'|,
\tag{4.1}
$$

with indices $(\text{output }j,\text{input }i)$. The allowed lifts are exactly
the positive semidefinite matrices $J$ whose output-diagonal blocks satisfy

$$
J_{jj}=\operatorname{diag}_{i}Q_{ij}\quad(0\le j\le4).
\tag{4.2}
$$

Their only possible nonzero rows and columns are the eight edges

$$
\mathcal E=((0,0),(0,1),(1,2),(2,3),(2,4),(3,0),(3,1),(4,2)).
\tag{4.3}
$$

Equivalently every allowed lift is $\Phi(X)=\operatorname{Tr}_E(VXV^\dagger)$,
where

$$
\begin{aligned}
V|0\rangle&=\sqrt r\,|0\rangle\otimes\alpha_0+
             \sqrt\eta\,|3\rangle\otimes\beta_0,\\
V|1\rangle&=\sqrt r\,|0\rangle\otimes\alpha_1+
             \sqrt\eta\,|3\rangle\otimes\beta_1,\\
V|2\rangle&=\sqrt r\,|1\rangle\otimes\gamma_0+
             \sqrt\eta\,|4\rangle\otimes\gamma_1,\\
V|3\rangle&=|2\rangle\otimes\delta_0,\\
V|4\rangle&=|2\rangle\otimes\delta_1.
\end{aligned}
\tag{4.4}
$$

All eight environment vectors are unit vectors in one common complex Hilbert
space and the only prescribed cross inner products are

$$
\langle\alpha_0,\alpha_1\rangle=
\langle\beta_0,\beta_1\rangle=
\langle\delta_0,\delta_1\rangle=0.
\tag{4.5}
$$

Their other inner products are unrestricted except for consistency with a
positive Gram matrix. The environment need not be two-dimensional. A minimal
environment has dimension $\operatorname{rank}J\le8$, and at least two.

Proof. The Choi criterion [CHOI] says complete positivity is equivalent to
$J\ge0$. The $(i,i')$ entry of the block $J_{jj}$ is
$\langle j|\Phi(|i\rangle\langle i'|)|j\rangle$. Testing all complex matrix
units shows that (2.2) is exactly (4.2). Summing those blocks yields

$$
\operatorname{Tr}_{\mathrm{out}}J=I_5,
$$

because every row of $Q$ sums to one. Thus trace preservation follows from
(4.2), and $\operatorname{Tr}J=5$. Conversely, the Choi correspondence
constructs a CP map from every such $J$, and these two identities give TP and
the entire law (2.2).
For a positive matrix, its two-by-two principal minors give
$|J_{ab}|^2\le J_{aa}J_{bb}$. A zero diagonal entry therefore annihilates its
entire row and column. The eight positive entries of $Q$ are exactly (4.3).
Consequently the description is equivalently a PSD eight-by-eight matrix with
the constraints (4.2), padded by zeros.

For clarity about complex conjugation, write
$V|i\rangle=\sum_j|j\rangle\otimes e_{ji}$. Then

$$
J_{(j,i),(j',i')}=\langle e_{j'i'},e_{ji}\rangle.
\tag{4.6}
$$

The order is reversed relative to $\langle e_{ji},e_{j'i'}\rangle$.
Indeed the partial trace of $|e_{ji}\rangle\langle e_{j'i'}|$ is
$\langle e_{j'i'},e_{ji}\rangle$. In an environment basis, the Choi matrix is
$\sum_a v_av_a^\dagger$, with $(v_a)_{ji}=(e_{ji})_a$, which also proves
positivity with exactly this convention. Conversely a positive factorization
of $J$ supplies these coordinates. The diagonal blocks fix
$\|e_{ji}\|^2=Q_{ij}$ and make distinct predecessor vectors orthogonal at each
fixed output $j$. Removing the positive edge weights gives (4.4)–(4.5).
They imply $V^\dagger V=I$: the only possible cross terms in distinct input
columns come from the three pairs in (4.5), and each column has squared norm
one. No further orthogonality, in particular none between $\gamma_0$ and
$\gamma_1$, is required. This is the finite-dimensional Stinespring
representation [STI]. Finally $\delta_0,\delta_1$ force an environment of
dimension at least two, and the Choi factorization gives the stated upper
bound. $\square$

**Theorem 4.2 (Reset sector and dual effects).** Every allowed lift has

$$
\Phi(X)=\operatorname{Tr}(X)P_2\qquad(X\in\mathcal B(D)).
\tag{4.7}
$$

Its dual effects are

$$
\begin{aligned}
\Phi^\dagger(P_0)&=rP_A,&\Phi^\dagger(P_1)&=rP_B,&
\Phi^\dagger(P_2)&=P_D,\\
\Phi^\dagger(P_3)&=\eta P_A,&\Phi^\dagger(P_4)&=\eta P_B.
\end{aligned}
\tag{4.8}
$$

For every $t\ge0$ put $F_t=(\Phi^\dagger)^t(P_2)$. Then

$$
\begin{aligned}
F_t&=\operatorname{diag}_i(Q^t)_{i2},\\
F_1&=P_D,\qquad F_2=\eta P_L,\\
F_3&=\eta(rP_L+P_D)>0.
\end{aligned}
\tag{4.9}
$$

Moreover

$$
(Q^2)_{i,\cdot}=\begin{cases}
(r^2,0,\eta,r\eta,0),&i\in\{0,1,2\},\\
(0,r,0,0,\eta),&i\in\{3,4\}.
\end{cases}
\tag{4.10}
$$

Proof. A positive input supported on $D$ has output diagonal supported only
at coordinate 2. Positivity annihilates every row and column outside that
coordinate, leaving its trace times $P_2$. Every complex matrix is a complex
linear combination of positive matrices, proving (4.7) on the full algebra.
For arbitrary complex $X$, the equality
$\operatorname{Tr}(P_j\Phi(X))=\sum_iQ_{ij}X_{ii}$ proves (4.8).
Applying the same dual map to diagonal observables proves the first identity
in (4.9) by induction. Direct multiplication gives (4.10) and the remaining
identities. The eigenvalues of $F_3$ are $\eta r$ three times and $\eta$ twice;
all are strictly positive. These are dual effects, not forward states
$\Phi^t(P_2)$. Their trace is not constrained to be one. $\square$

## 5. Reversibility and rank accounting

**Theorem 5.1 (Supported syndrome form and rank pullback).** Suppose
$E:\mathcal B(C)\to M_5$ is the restriction of a channel and has a CPTP left
inverse, with $\dim C=k$. There are an integer $s\ge1$, a density matrix
$\tau>0$ on $G=\mathbb C^s$, and an isometry $W:C\otimes G\to H$ such that

$$
E(X)=W(X\otimes\tau)W^\dagger,
\qquad ks\le5.
\tag{5.1}
$$

Every pure input has output rank $s$. For a Stinespring representation of
$E$, the complementary output is a constant density matrix times
$\operatorname{Tr}X$, and that density matrix has rank $s$ on its support.
For any $z_0\in H$, put $y=W^\dagger z_0$. The compressed pullback of its
rank-one output effect is

$$
E^\dagger(|z_0\rangle\langle z_0|)=
\operatorname{Tr}_G\!\left[
(I\otimes\tau^{1/2})|y\rangle\langle y|
(I\otimes\tau^{1/2})\right].
\tag{5.2}
$$

Its rank equals the Schmidt rank of $y$, and is at most $s$. The zero vector
has Schmidt rank zero. Conversely (5.1) admits a terminal CPTP left inverse.

Proof. We use the complex Knill–Laflamme condition
[Knill–Laflamme, Theorems 3.2 and 3.5][KL], with the details needed here made
explicit. Let $A_\mu:C\to H$ be Kraus restrictions of $E$, and let $D_\ell$
be Kraus operators of its left inverse. The operators $D_\ell A_\mu$ realize
the identity channel on $\mathcal B(C)$. For each pure vector $u\in C$, the
sum of their positive rank-one outputs is $|u\rangle\langle u|$.
Every $D_\ell A_\mu u$ is therefore collinear with $u$. A linear map that
preserves every line of $C$ is scalar on $C$: apply it to basis vectors and
their pairwise sums. Thus $D_\ell A_\mu=c_{\ell\mu}I_C$, with the identity
understood as inclusion into the original code. Trace preservation of the
recovery gives

$$
A_\mu^\dagger A_\nu=\alpha_{\mu\nu}I_C,
\qquad
\alpha_{\mu\nu}=\sum_\ell\overline{c_{\ell\mu}}c_{\ell\nu}.
\tag{5.3}
$$

The matrix $\alpha$ is positive and has trace one. Unitary change of Kraus
coordinates diagonalizes it. Discarding its zero eigenvalues leaves
$A_a=\sqrt{\lambda_a}U_a$, where $\lambda_a>0$, $\sum_a\lambda_a=1$,
and $U_a^\dagger U_b=\delta_{ab}I_C$. The map
$W(u\otimes|a\rangle)=U_au$ is an isometry and gives (5.1) with
$\tau=\operatorname{diag}(\lambda_a)$.
It follows that the supported range has dimension $ks$ and a pure input
has rank $s$. In the original Kraus environment basis, direct tracing gives
$\widehat E(X)=\operatorname{Tr}(X)\alpha^{\mathsf T}$.
Changing to any other Stinespring representation only isometrically embeds
this support; it does not change its nonzero rank.

To obtain (5.2), pair (5.1) with $|z_0\rangle\langle z_0|$ under the trace and
move $W$ across it. The partial trace on the right is the reduced operator of
$(I\otimes\tau^{1/2})y$. Its rank is that vector's Schmidt rank. An invertible
operator on the gauge factor preserves Schmidt rank, proving the assertion,
even when $z_0$ is not in $\operatorname{ran}W$.

For the converse, set $P=WW^\dagger$ and choose a fixed state $\rho_0$ on $C$.
Then

$$
\mathcal D(Y)=\operatorname{Tr}_G(W^\dagger YW)
+\operatorname{Tr}((I-P)Y)\rho_0
\tag{5.4}
$$

is completely positive. The trace of its first term is $\operatorname{Tr}(PY)$
and the second contributes $\operatorname{Tr}((I-P)Y)$, so it is TP.
It satisfies $\mathcal D E(X)=X$. This also proves sufficiency of (5.3).
All the equalities are equalities on the full complex matrix algebra.
$\square$

## 6. Universal one- and two-step bounds

**Theorem 6.1 (One step).** Every isometric restriction of an allowed lift
has dimension at most three, and every allowed lift satisfies $k_1(\Phi)\le3$.
If $C$ is a three-dimensional correctable code, then for unit vectors
$a_0\in A$ and $d_0\in D$ it has the form

$$
C=\operatorname{span}\{a_0,z,d_0\}.
\tag{6.1}
$$

Proof. For an isometric restriction $X\mapsto UXU^\dagger$ on $C$, the
pullback of any rank-one output effect has rank at most one. By (4.8), and
$r>0$,

$$
\operatorname{rank}(P_CP_AP_C)\le1,\quad
\operatorname{rank}(P_CP_BP_C)\le1,\quad
\operatorname{rank}(P_CP_DP_C)\le1.
\tag{6.2}
$$

Their sum is $I_C$, so $\dim C\le3$. If a correctable code has dimension
$k\ge3$, (5.1) forces $s=1$ because $2k>5$. It is therefore isometric and
obeys the same bound.
For $k=3$, each of the images $P_AC,P_BC,P_DC$ has dimension at most one:
$P_CP_RP_C=(P_R|_C)^\dagger(P_R|_C)$ has the same rank as $P_R|_C$.
The code is contained in their orthogonal direct sum. That sum has dimension
at most three and contains a three-dimensional subspace, so equality holds,
and $C$ is the sum itself. The middle line is $B$, giving (6.1). $\square$

**Theorem 6.2 (Two steps).** Every allowed lift satisfies $k_2(\Phi)\le2$.

Proof. Suppose a three-dimensional code $C$ is recoverable after two steps.
Both prefix restrictions are reversible and hence, by $3s\le5$, isometric.
The first code has (6.1), and its three orthonormal input vectors have pure,
orthogonal first-step outputs $f_A,f_B,f_D$. The population law forces

$$
\begin{aligned}
f_A&\in\operatorname{span}\{|0\rangle,|3\rangle\},&
(|(f_A)_0|^2,|(f_A)_3|^2)&=(r,\eta),\\
f_B&\in\operatorname{span}\{|1\rangle,|4\rangle\},&
(|(f_B)_1|^2,|(f_B)_4|^2)&=(r,\eta),\\
f_D&\in\mathbb C z,&\|f_D\|&=1.
\end{aligned}
\tag{6.3}
$$

The first-step range $C'=\operatorname{span}\{f_A,f_B,f_D\}$ is itself an
isometric restriction for the next $\Phi$: if $U_1,U_2$ are the prefix
isometries, then for $Y=U_1XU_1^\dagger$ one has
$\Phi(Y)=U_2XU_2^\dagger$. But $P_AC'$ contains nonzero multiples of both
$|0\rangle$ and $|1\rangle$ because $r>0$. Its dimension is at least two,
contradicting (6.2) for an isometric restriction. A larger code would contain
a three-dimensional subcode. $\square$

## 7. Transfer on the entire reversible ranges

**Theorem 7.1 (Full-range transfer and its unitary consequence).** Let two
successive reversible restrictions of the same channel have a qubit logical
factor $C$ and supported forms

$$
E_t(X)=W_t(X\otimes\tau_t)W_t^\dagger,\qquad
E_{t+1}(X)=W_{t+1}(X\otimes\tau_{t+1})W_{t+1}^\dagger,
$$

where $\tau_t,\tau_{t+1}$ are strictly positive on their respective gauge
spaces $G_t,G_{t+1}$. Put $R_t=\operatorname{ran}W_t$ and
$R_{t+1}=\operatorname{ran}W_{t+1}$ and suppose $E_{t+1}=\Phi E_t$.
Then each Kraus operator of $\Phi$ maps $R_t$ into $R_{t+1}$, and in these
coordinates the complete restriction is

$$
\widetilde\Phi=\operatorname{id}_{M_2}\otimes\Gamma,
\qquad \Gamma(\tau_t)=\tau_{t+1},
\tag{7.1}
$$

on all of $\mathcal B(C\otimes G_t)$, for a CPTP $\Gamma$.
If both gauges have dimension two and

$$
(\operatorname{id}\otimes\Gamma)(|\xi\rangle\langle\xi|)
=|y\rangle\langle y|,
\tag{7.2}
$$

for unit vectors with $y$ of Schmidt rank two, then
$\Gamma(Z)=UZU^\dagger$ for a unitary $U:G_t\to G_{t+1}$.
Consequently $\Phi$ is isometric on all of $R_t$ in this case.
The conclusion is unitary conjugation, not necessarily the identity map.

Proof. The operator $E_t(I_C)$ is strictly positive on its entire range
$R_t$, because its gauge is full rank. Its image is supported on $R_{t+1}$.
For $v\perp R_{t+1}$ and Kraus operators $K_\mu$,

$$
0=\langle v,E_{t+1}(I_C)v\rangle
=\sum_\mu\|E_t(I_C)^{1/2}K_\mu^\dagger v\|^2.
$$

Each summand vanishes, so $K_\mu R_t\subseteq R_{t+1}$.
It follows that $A_\mu=W_{t+1}^\dagger K_\mu W_t$ are Kraus operators of a TP
map on the complete input tensor space: inserting $P_{R_{t+1}}$ does not
remove any $K_\mu W_t$ component, and
$\sum_\mu A_\mu^\dagger A_\mu=I_{C\otimes G_t}$.
This map obeys

$$
\sum_\mu A_\mu(X\otimes\tau_t)A_\mu^\dagger
=X\otimes\tau_{t+1}.
\tag{7.3}
$$

Diagonalize $\tau_t=\sum_a p_a|a\rangle\langle a|$ with every $p_a>0$.
For every complex logical vector $\ell$, the positive sum

$$
\sum_{\mu,a}p_a
|A_\mu(\ell\otimes a)\rangle\langle A_\mu(\ell\otimes a)|
=|\ell\rangle\langle\ell|\otimes\tau_{t+1}
$$

is supported on the logical line $\mathbb C\ell$ tensor $G_{t+1}$. Every
summand must have that logical support. Since all $p_a$ are positive and the
$|a\rangle$ span the input gauge, each $A_\mu$ preserves every logical line
on the whole tensor space. On the two basis lines it is block diagonal,
with gauge blocks $B_{\mu,0}$ and $B_{\mu,1}$. Applying the same property to
$|0\rangle+|1\rangle$ makes the blocks equal; complex linearity gives
$A_\mu=I_C\otimes B_\mu$ on every complex input. Thus
$\Gamma(Z)=\sum_\mu B_\mu ZB_\mu^\dagger$ is TP and (7.1) follows. It is not
merely an equality on the selected inputs $X\otimes\tau_t$.

For (7.2), purity implies
$(I\otimes B_\mu)\xi=c_\mu y$ for every $\mu$. At least one $c_\mu$ is
nonzero. In product bases let $X_\xi$ and $Y_y$ be their two-by-two ket
coefficient matrices. The equations read

$$
X_\xi B_\mu^{\mathsf T}=c_\mu Y_y.
\tag{7.4}
$$

The transpose is ordinary transpose, because these are coefficients of kets.
The matrix $Y_y$ is invertible. A nonzero $c_\mu$ forces $X_\xi$ invertible as
well. Equation (7.4) then makes every $B_\mu$ proportional to one fixed
matrix $B$, including $B_\mu=0$ when $c_\mu=0$. Trace preservation says
$(\sum_\mu|c_\mu|^2)B^\dagger B=I$. Normalizing $B$ therefore gives a square
unitary $U$, and the entire gauge channel is $\operatorname{Ad}_U$.
On $R_t$, the original channel is consequently conjugation by the isometry
$W_{t+1}(I\otimes U)W_t^\dagger$. No extra retained subsystem is introduced;
the tensor factors are coordinates on subspaces of $H$. $\square$

## 8. Geometry forced by a hypothetical third-step qubit

**Theorem 8.1 (Necessary syndrome pattern and one fixed phase normalization).**
If an allowed lift corrects a two-dimensional code after three steps, its
three prefix syndrome ranks must be

$$
(s_1,s_2,s_3)=(1,1,2).
\tag{8.1}
$$

After conjugating that entire channel by one fixed diagonal unitary, its
second-step code image is

$$
T=\operatorname{span}\{h,w\},\qquad
h=r|0\rangle+\sqrt\eta\,|2\rangle+\sqrt{r\eta}\,|3\rangle,
\qquad w=\sqrt r\,|1\rangle+\sqrt\eta\,|4\rangle.
\tag{8.2}
$$

The vectors $h,w$ are orthonormal, and $T$ would have to be a one-step
correctable code for that conjugated allowed lift.

Proof. Let $C$ be the hypothetical code. Every $E_t=\Phi^t|_{\mathcal B(C)}$
for $t=1,2,3$ is reversible, by terminal composition. Write (5.1) with ranks
$s_t\in\{1,2\}$. Since

$$
E_3^\dagger(P_2)=P_CF_3P_C
$$

is strictly positive on the qubit $C$, it has rank two. Formula (5.2) forces
$s_3=2$ and $W_3^\dagger z$ to have Schmidt rank two.
Suppose $s_2=2$. Both $R_2$ and $R_3$ then have dimension four, so Theorem 7.1
applies between their full ranges. As
$\dim(R_2\cap D)\ge4+2-5=1$, choose a unit $x\in R_2\cap D$.
The reset sector gives $\Phi(|x\rangle\langle x|)=P_2$. Range inclusion gives
$z\in R_3$. Thus $\xi=W_2^\dagger x$ and $y=W_3^\dagger z$ are unit vectors,
the second has Schmidt rank two, and they satisfy (7.2).
The gauge channel is unitary conjugation. Hence $\Phi$ is isometric on all
four dimensions of $R_2$, contrary to Theorem 6.1. This proves $s_2=1$.

The second prefix is therefore isometric. Its rank-one output effects $P_0$
and $P_1$, using (4.10), pull back to

$$
r^2P_CP_LP_C,\qquad rP_CP_DP_C.
\tag{8.3}
$$

Both have rank at most one. The two unscaled positive contractions sum to
$I_C$. A rank-at-most-one positive contraction on a two-dimensional space
whose complement also has rank at most one must have eigenvalues $1,0$.
Thus these are complementary rank-one projections, and

$$
C=\operatorname{span}\{x,y\},\qquad x\in L,\quad y\in D,
\quad \|x\|=\|y\|=1.
\tag{8.4}
$$

Equivalently their projected images are two orthogonal lines whose direct
sum contains and hence equals $C$. Since the first-step output of the pure
input $y$ is $P_2$, the constant pure-input rank of $E_1$ forces $s_1=1$.

The second-step isometry takes $x,y$ to two orthonormal pure vectors
$h',w'$. By (4.10) their populations are
$(r^2,0,\eta,r\eta,0)$ and $(0,r,0,0,\eta)$ respectively. Their supports are
disjoint. Choose a single diagonal unitary $D_{\mathrm{ph}}$ making all five
nonzero coordinates of these two kets positive. Then their images are
exactly (8.2); their squared norms are $r^2+\eta+r\eta=1$ and $r+\eta=1$.
Define

$$
\Phi'=\operatorname{Ad}_{D_{\mathrm{ph}}}\circ\Phi\circ
\operatorname{Ad}_{D_{\mathrm{ph}}^\dagger}.
$$

Diagonal unitary conjugation leaves every input and output population
unchanged, so (2.2) still holds. Moreover

$$
(\Phi')^n=\operatorname{Ad}_{D_{\mathrm{ph}}}\circ\Phi^n\circ
\operatorname{Ad}_{D_{\mathrm{ph}}^\dagger}
\quad\text{for every }n.
\tag{8.5}
$$

This preserves homogeneity; it is not a separate phase adjustment at each
step. The transformed initial code has second image $T$. Conjugate the final
recovery as well, and compose it with the second-prefix isometric
identification to obtain a one-step CPTP recovery onto $T$. Such a completion
is CPTP by (5.4). Thus $T$ must be correctable for $\Phi'$. $\square$

## 9. Full complex obstruction and the sharp third-step bound

**Theorem 9.1 (The forced two-plane is never correctable).** For every
$0<\eta<1$, the plane $T$ of (8.2) is not a one-step correctable subspace for
any allowed lift, including lifts with unrestricted complex Gram data and
arbitrary environment dimension.

Proof. Use the general representation (4.4), and let
$\widehat\Phi(X)=\operatorname{Tr}_H(VXV^\dagger)$ be its complement.
Correctability and (5.3) require the complete complex matrix conditions

$$
\widehat\Phi(|h\rangle\langle h|)=
\widehat\Phi(|w\rangle\langle w|)=\omega,\qquad
\widehat\Phi(|h\rangle\langle w|)=
\widehat\Phi(|w\rangle\langle h|)=0.
\tag{9.1}
$$

Here $\omega$ is a density matrix of rank $s\le2$, since $2s\le5$.
Tracing over the system coordinates in (4.4) gives

$$
\begin{aligned}
\widehat\Phi(|h\rangle\langle h|)
={}&r^3|\alpha_0\rangle\langle\alpha_0|
+r^2\eta|\beta_0\rangle\langle\beta_0|\\
&+r\eta|\delta_0\rangle\langle\delta_0|
+r\eta|\gamma_0\rangle\langle\gamma_0|
+\eta^2|\gamma_1\rangle\langle\gamma_1|,\\
\widehat\Phi(|w\rangle\langle w|)
={}&r^2|\alpha_1\rangle\langle\alpha_1|
+r\eta|\beta_1\rangle\langle\beta_1|
+\eta|\delta_1\rangle\langle\delta_1|.
\end{aligned}
\tag{9.2}
$$

In the first line of inputs the five environment vectors occur at distinct
system coordinates $0,3,2,1,4$; in the second they occur at $0,3,2$.
There are no omitted interference terms in (9.2).
All its coefficients are strictly positive. The range of a positive sum of
rank-one operators is the span of their vectors, because its kernel is the
intersection of their orthogonal complements. Therefore every one of the
eight environment vectors lies in the same space $E_0=\operatorname{ran}\omega$.
The pair $\alpha_0,\alpha_1$ is already orthonormal, so

$$
\dim E_0=2.
\tag{9.3}
$$

Each of $(\alpha_0,\alpha_1)$, $(\beta_0,\beta_1)$, and
$(\delta_0,\delta_1)$ is an ordered orthonormal basis of this same space.
This two-dimensional support is forced by correction, not assumed in the
parametrization of the class.

On $E_0$ define

$$
\begin{aligned}
S_0&=r^2|\alpha_0\rangle\langle\alpha_0|
+r\eta|\beta_0\rangle\langle\beta_0|
+\eta|\delta_0\rangle\langle\delta_0|,\\
S_1&=r^2|\alpha_1\rangle\langle\alpha_1|
+r\eta|\beta_1\rangle\langle\beta_1|
+\eta|\delta_1\rangle\langle\delta_1|,\\
\rho_g&=r|\gamma_0\rangle\langle\gamma_0|
+\eta|\gamma_1\rangle\langle\gamma_1|.
\end{aligned}
\tag{9.4}
$$

The three basis resolutions and $r^2+r\eta+\eta=1$ give
$S_0+S_1=I_{E_0}$. The equality of the two diagonal complementary outputs
in (9.2) is

$$
rS_0+\eta\rho_g=S_1.
$$

Solving these matrix equations yields

$$
S_0=\frac{I-\eta\rho_g}{1+r},\qquad
S_1=\frac{rI+\eta\rho_g}{1+r}.
\tag{9.5}
$$

Since $\rho_g$ is a density matrix, $0\le\rho_g\le I$. In particular

$$
S_0\ge\frac r{1+r}I>0,\qquad S_1\ge\frac r{1+r}I>0.
\tag{9.6}
$$

No orthogonality between the two $\gamma$ vectors was used.

The ordered cross output, with conjugates retained in the bras, is exactly

$$
\widehat\Phi(|h\rangle\langle w|)
=\sqrt r\left(
 r^2|\alpha_0\rangle\langle\alpha_1|
+r\eta|\beta_0\rangle\langle\beta_1|
+\eta|\delta_0\rangle\langle\delta_1|
\right).
\tag{9.7}
$$

For example its output-coordinate-0 coefficient is
$(r\sqrt r)\,r=r^{5/2}$, the coordinate-3 coefficient is
$(r\sqrt\eta)\sqrt{r\eta}=r^{3/2}\eta$, and the coordinate-2 coefficient is
$\sqrt{r\eta}\sqrt\eta=\sqrt r\eta$.
The other system coordinates give zero because $Vw$ has no amplitude there.
The other ordered cross output is its adjoint. By (9.1) and $r>0$, the whole
complex operator inside the parentheses must vanish. A trace condition,
a real-part condition, or selected scalar entries would be insufficient.

Let $U_\alpha,U_\beta,U_\delta:\mathbb C^2\to E_0$ send the ordered standard
basis to the corresponding three ordered orthonormal bases. Define the
auxiliary channel

$$
\mathcal M(Y)=r^2U_\alpha YU_\alpha^\dagger
+r\eta U_\beta YU_\beta^\dagger
+\eta U_\delta YU_\delta^\dagger.
\tag{9.8}
$$

It is a convex mixture of three unitary conjugations, with Kraus operators
$rU_\alpha,\sqrt{r\eta}U_\beta,\sqrt\eta U_\delta$. Its Choi matrix is a
sum of three vectorized-Kraus rank-one projectors. Thus

$$
\operatorname{rank}J_{\mathcal M}\le3.
\tag{9.9}
$$

But (9.4) and the entire complex cross equation (9.7) prescribe all four
matrix-unit images:

$$
\mathcal M(E_{00})=S_0,\quad\mathcal M(E_{11})=S_1,\quad
\mathcal M(E_{01})=\mathcal M(E_{10})=0.
$$

Consequently its input-first Choi matrix is

$$
J_{\mathcal M}^{\mathrm{in}}=
\sum_{a,b=0}^1E_{ab}\otimes\mathcal M(E_{ab})
=\begin{pmatrix}S_0&0\\0&S_1\end{pmatrix}.
\tag{9.10}
$$

It has rank four by (9.6). If $\mathsf S$ swaps the two tensor factors, the
output-first matrix is $\mathsf S J_{\mathcal M}^{\mathrm{in}}\mathsf S^\dagger$.
This is a simultaneous permutation of rows and columns, preserving rank and
spectrum; it is not a partial transpose.

There is also an explicit strict determinant contradiction. Let the
eigenvalues of $\rho_g$ be $t,1-t$, with $0\le t\le1$. The four eigenvalues
of (9.10) are

$$
\frac{1-\eta t}{1+r},\quad
\frac{1-\eta(1-t)}{1+r},\quad
\frac{r+\eta t}{1+r},\quad
\frac{r+\eta(1-t)}{1+r}.
\tag{9.11}
$$

The identities $1-\eta t=r+\eta(1-t)$ and
$1-\eta(1-t)=r+\eta t$ factor their product as

$$
\det J_{\mathcal M}^{\mathrm{in}}
=\frac{[r+\eta^2t(1-t)]^2}{(1+r)^4}>0,
\qquad
\det J_{\mathcal M}^{\mathrm{in}}
\ge\left(\frac r{1+r}\right)^4>0.
\tag{9.12}
$$

The last lower bound also follows directly from (9.6).
A three-Kraus Choi matrix must have zero determinant in dimension four,
contradicting either (9.10) or (9.12). The auxiliary map is solely a proof
object; it adds no physical operation or retained gauge to the model.
All steps allow arbitrary complex vectors and all interior parameters.
$\square$

**Theorem 9.2 (Universal third-step exact-memory obstruction).** Every
allowed lift, for every fixed $0<\eta<1$, satisfies

$$
k_n(\Phi)=1\qquad\text{for every integer }n\ge3.
\tag{9.13}
$$

Proof. A qubit code after three steps would, by Theorem 8.1, produce the
forbidden plane in Theorem 9.1 for another allowed homogeneous lift.
Thus no qubit code exists. A larger code contains a qubit subcode, and a
one-dimensional code always has a terminal reset decoder. This gives
$k_3=1$. A decoder after $n>3$ composed with $\Phi^{n-3}$ would decode the
third prefix, so $k_n=1$ thereafter. The argument proves an all-parameter,
all-lift, arbitrary-complex-subspace statement; it uses no finite grid as
its substitute. $\square$

## 10. Canonical lift, terminal decoding, and sharpness

**Definition 10.1 (Oldest-bit canonical lift).** Put

$$
u_0=\sqrt r\,|0\rangle+\sqrt\eta\,|3\rangle,\qquad
u_1=\sqrt r\,|1\rangle+\sqrt\eta\,|4\rangle.
$$

Together $u_0,u_1,z$ are orthonormal. Define

$$
\begin{aligned}
K_0&=|u_0\rangle\langle0|+|u_1\rangle\langle2|+|z\rangle\langle3|,\\
K_1&=|u_0\rangle\langle1|+|z\rangle\langle4|,\\
\Phi_{\mathrm{can}}(X)&=K_0XK_0^\dagger+K_1XK_1^\dagger.
\end{aligned}
\tag{10.1}
$$

**Theorem 10.2 (All-input law and exact terminal codes).** The canonical lift
is allowed and has

$$
(k_0,k_1,k_2,k_3,\ldots)(\Phi_{\mathrm{can}})=(5,3,2,1,1,\ldots).
\tag{10.2}
$$

Consequently the universal optima are simultaneously attained by one fixed
channel:

$$
(K_0(\eta),K_1(\eta),K_2(\eta),K_3(\eta),\ldots)
=(5,3,2,1,1,\ldots).
\tag{10.3}
$$

Here the subscripted $K_n(\eta)$ denotes code dimension, distinct from the
two Kraus operators $K_0,K_1$ in (10.1).

Proof. Orthogonality gives

$$
K_0^\dagger K_0=P_0+P_2+P_3,\qquad
K_1^\dagger K_1=P_1+P_4,
$$

so the map is TP. Its Stinespring representation is (4.4) with

$$
\alpha_0=\beta_0=\gamma_0=\gamma_1=\delta_0=|0\rangle_E,
\qquad \alpha_1=\beta_1=\delta_1=|1\rangle_E.
$$

This satisfies (4.5), proving the law for every complex input, not only for
basis populations. Equivalently it is the chronological isometry

$$
V_{\mathrm{can}}|abc\rangle
=\sum_{d=0}^1\sqrt{P_{cd}}\,|bcd\rangle\otimes|a\rangle_E.
\tag{10.4}
$$

Only legal output triples have nonzero amplitude. The first erased bit is
the fresh discarded environment label.

The one-step code

$$
C_1=\operatorname{span}\{|0\rangle,|2\rangle,|3\rangle\}
$$

is annihilated by $K_1$ and is mapped isometrically by $K_0$. This gives
$k_1\ge3$ and Theorem 6.1 gives equality. Its decoder is (5.4) with syndrome
dimension one and $W=K_0|_{C_1}$.

For two steps use
$C_2=\operatorname{span}\{|0\rangle,|3\rangle\}$, and note that
$h=\sqrt r\,u_0+\sqrt\eta\,z$ and $w=u_1$ are exactly (8.2).
All four products on the full input space are

$$
\begin{aligned}
K_0K_0&=|h\rangle\langle0|+|w\rangle\langle3|=:U_2,\\
K_0K_1&=|h\rangle\langle1|+|w\rangle\langle4|,\\
K_1K_0&=|h\rangle\langle2|,\\
K_1K_1&=0.
\end{aligned}
\tag{10.5}
$$

The last three annihilate $C_2$, while $U_2^\dagger U_2=P_{C_2}$ and
$U_2U_2^\dagger=P_T$. Thus for every complex $X\in\mathcal B(C_2)$,

$$
\Phi_{\mathrm{can}}^2(X)=U_2XU_2^\dagger.
$$

An exact decoder defined on all of $M_5$ is

$$
\mathcal R_2(Y)=U_2^\dagger YU_2+
\operatorname{Tr}((I-P_T)Y)P_0.
\tag{10.6}
$$

Its Kraus operators can be chosen as $U_2^\dagger$ together with
$|0\rangle\langle j|(I-P_T)$, $j=0,\ldots,4$. Their squared products sum to
$P_T+(I-P_T)^2=I$. Hence this is CPTP and recovers every logical matrix
unit, including both complex off-diagonal ones. It is a terminal operation.
Theorem 6.2 gives $k_2=2$, and Theorem 9.2 gives the remaining entries.
Since the universal upper bounds are attained by this same lift, (10.3)
follows. $\square$

**Theorem 10.3 (Canonical EB index and explicit witnesses before it).** The
canonical lift has $n_{\mathrm{EB}}(\Phi_{\mathrm{can}})=3$.

Proof. Iterating (10.4) with three fresh environments yields

$$
|abc\rangle\longmapsto |f_c\rangle\otimes|a,b,c\rangle_E,
\qquad
|f_c\rangle=\sum_{def\in\Omega}
\sqrt{P_{cd}P_{de}P_{ef}}\,|def\rangle.
\tag{10.7}
$$

The sum of the squared amplitudes is one by stochasticity, so each $f_c$ is
unit. The five initial triples label orthogonal environment records. Thus
on the full complex algebra

$$
\Phi_{\mathrm{can}}^3(X)=
\sum_{abc\in\Omega}X_{abc,abc}|f_c\rangle\langle f_c|.
\tag{10.8}
$$

This is a basis measurement followed by state preparation; equivalently
$|f_c\rangle\langle abc|$ are rank-one Kraus operators. The equivalence with
EB is [Horodecki–Shor–Ruskai, Theorem 4][HSR]. Later compositions remain EB.

For actual earlier witnesses, take an external reference qubit and input

$$
|\Theta\rangle=
\frac{|0\rangle_R|0\rangle+|1\rangle_R|3\rangle}{\sqrt2}.
$$

After one step the state remains pure with the orthonormal output pair
$(u_0,z)$, and after two steps it remains pure with pair $(h,w)$.
For either pair $(a,b)$ the partial transpose of
$(|0\rangle_Ra+|1\rangle_Rb)/\sqrt2$ has on
$\operatorname{span}\{|0\rangle_Rb,|1\rangle_Ra\}$ the compression
$\frac12\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$,
whose determinant is $-1/4$. Both earlier iterates are NPT for this input
and therefore fail EB. This proves the index exactly. $\square$

## 11. Same classical law and an invariant quantum two-plane

**Definition 11.1 (Equal-row unitary mixing).** Write $a=\sqrt r$ and
$b=\sqrt\eta$. Let $W$ fix $|2\rangle$ and act in each ordered block
$(|0\rangle,|1\rangle)$ and $(|3\rangle,|4\rangle)$ as

$$
\begin{pmatrix}a&b\\b&-a\end{pmatrix}.
\tag{11.1}
$$

Then $W=W^\dagger=W^{-1}$. Define

$$
\Xi=\Phi_{\mathrm{can}}\circ\operatorname{Ad}_W,
\qquad L_0=K_0W,\quad L_1=K_1W.
\tag{11.2}
$$

These are explicit fixed Kraus operators; in outer products they are

$$
\begin{aligned}
L_0={}&|u_0\rangle(a\langle0|+b\langle1|)
+|u_1\rangle\langle2|
+|z\rangle(a\langle3|+b\langle4|),\\
L_1={}&|u_0\rangle(b\langle0|-a\langle1|)
+|z\rangle(b\langle3|-a\langle4|).
\end{aligned}
\tag{11.3}
$$

**Theorem 11.2 (Full law, full two-step range, and a sharp code).** The map
$\Xi$ obeys the same all-complex-input law (2.2). It even has the same entire
output as $\Phi_{\mathrm{can}}$ on each of the five basis projectors.
Its one-step output range is supported in
$S=\operatorname{span}\{u_0,u_1,z\}$, and every two-step output is supported
in $T=\operatorname{span}\{h,w\}$. This plane is invariant.
On its ordered orthonormal basis $(h,w)$ the Kraus restrictions are

$$
A_0=\begin{pmatrix}r&\sqrt\eta\\\sqrt\eta&0\end{pmatrix},
\qquad
A_1=\begin{pmatrix}\sqrt{r\eta}&-\sqrt r\\0&0\end{pmatrix}.
\tag{11.4}
$$

Moreover $k_1(\Xi)=3$ and $k_2(\Xi)=2$.

Proof. The rows of $Q$ are equal within $\{0,1\}$ and within $\{3,4\}$.
For arbitrary complex $X$, the vector $Q^{\mathsf T}\operatorname{diag}X$
depends on these pairs only through $X_{00}+X_{11}$ and $X_{33}+X_{44}$,
as well as $X_{22}$. Block conjugation by $W$ preserves each such block trace.
Thus

$$
Q^{\mathsf T}\operatorname{diag}(WXW^\dagger)
=Q^{\mathsf T}\operatorname{diag}X.
$$

Together with the canonical law this proves the all-input assertion.
For inputs 0 and 1, the two $L$ outputs are scalar multiples of $u_0$ with
squared coefficients summing to one. Input 2 gives $u_1$, while inputs 3 and
4 give $z$. The five output density matrices therefore agree exactly with
the canonical outputs, not just in their diagonals.

The range $S$ is evident from (11.3). The three useful identities are

$$
\begin{array}{c|ccc}
&u_0&u_1&z\\\hline
L_0&a h&b h&w\\
L_1&b h&-a h&0
\end{array}
\tag{11.5}
$$

They show that all second-step outputs lie in $T$ and give (11.4) on
$h=a u_0+b z$ and $w=u_1$. More explicitly all two-step products are

$$
\begin{aligned}
L_0L_0&=\left[|h\rangle(a\langle0|+b\langle2|)
                         +|w\rangle\langle3|\right]W,\\
L_1L_0&=|h\rangle(b\langle0|-a\langle2|)W,\\
L_0L_1&=(a|h\rangle\langle1|+|w\rangle\langle4|)W,\\
L_1L_1&=b|h\rangle\langle1|W.
\end{aligned}
\tag{11.6}
$$

Thus the full-range assertion does not rely on testing selected states.

The space $WC_1$ is a three-dimensional one-step code. For two steps take

$$
C_{2,\Xi}=\operatorname{span}\{W(a|0\rangle+b|2\rangle),W|3\rangle\}.
\tag{11.7}
$$

Denote the displayed orthonormal vectors by $c_0,c_1$. The first product
in (11.6) takes them to $h,w$, and the other three annihilate them.
The resulting isometry
$U_{2,\Xi}$ has a CPTP decoder

$$
Y\longmapsto U_{2,\Xi}^\dagger YU_{2,\Xi}
+\operatorname{Tr}((I-P_T)Y)
|c_0\rangle\langle c_0|,
$$

whose reset state is the first code vector of (11.7). Its complete
positivity, trace preservation, and exact action follow by the same Kraus
completion as (10.6). The universal one- and two-step bounds give equality.
$\square$

## 12. Infinite EB index after the loss of all exact qubits

**Theorem 12.1 (Entire qubit action and exact powers).** Let
$F=\Xi|_{\mathcal B(T)}$ in the invariant coordinates of Theorem 11.2. Define

$$
\psi=\frac{h+\sqrt\eta\,w}{\sqrt{1+\eta}},\qquad
\chi=\frac{w-\sqrt\eta\,h}{\sqrt{1+\eta}},
$$

and write $R=|\psi\rangle\langle\psi|$,
$D_\chi=|\chi\rangle\langle\chi|$, and
$C_\psi=|\psi\rangle\langle\chi|$. These are an orthonormal ket basis and its
four complex matrix units. Their channel actions are

$$
\begin{aligned}
F(R)&=R,\\
F(C_\psi)&=-\eta C_\psi,\qquad
F(C_\psi^\dagger)=-\eta C_\psi^\dagger,\\
F(D_\chi)&=rR+\eta D_\chi-r\sqrt\eta(C_\psi+C_\psi^\dagger).
\end{aligned}
\tag{12.1}
$$

In particular, if $\mathcal R_\psi(X)=\operatorname{Tr}(X)R$, then on all of
$\mathcal B(T)$

$$
\begin{aligned}
F^2&=\eta^2\operatorname{id}+(1-\eta^2)\mathcal R_\psi,\\
F^{2m}&=\eta^{2m}\operatorname{id}+(1-\eta^{2m})\mathcal R_\psi,\\
F^{2m+1}&=\eta^{2m}F+(1-\eta^{2m})\mathcal R_\psi
\qquad(m\ge0).
\end{aligned}
\tag{12.2}
$$

The fixed pure state's coordinate probabilities equal the stationary source
probabilities (3.2).

Proof. From (11.4), direct multiplication gives

$$
A_0\psi=\psi,\quad A_1\psi=0,\quad
A_0\chi=-\eta\chi,\quad A_1\chi=-\sqrt{1-\eta^2}\,h.
\tag{12.3}
$$

The first three matrix-unit formulas in (12.1) follow immediately. The last
output is
$\eta^2D_\chi+(1-\eta^2)|h\rangle\langle h|$.
Since $h=(\psi-\sqrt\eta\,\chi)/\sqrt{1+\eta}$, expansion gives the stated
fourth formula. These four inputs span the entire complex algebra.
Applying $F$ twice to the fourth input gives
$rF(R)+\eta F(D_\chi)-r\sqrt\eta F(C_\psi+C_\psi^\dagger)$.
The cross terms $-r\eta\sqrt\eta$ and $+r\eta\sqrt\eta$ cancel,
while the $R$ coefficient is $r(1+\eta)=1-\eta^2$. The result is
$(1-\eta^2)R+\eta^2D_\chi$.
The other three inputs give the first identity in (12.2) as well.
As $F\mathcal R_\psi=\mathcal R_\psi F=\mathcal R_\psi$ and
$\mathcal R_\psi^2=\mathcal R_\psi$, induction gives the even powers and
composition with $F$ gives the odd ones.

In the original five coordinates,

$$
\psi=\frac1{\sqrt{1+\eta}}
(r,\sqrt{r\eta},\sqrt\eta,\sqrt{r\eta},\eta)^{\mathsf T}.
\tag{12.4}
$$

Squaring its coordinates gives (3.2). This equality is a checked interface;
it is not a derivation of the coherent state from a classical marginal.
$\square$

**Theorem 12.2 (A strict reference witness for every finite iterate).** For
every fixed $0<\eta<1$, the allowed homogeneous channel $\Xi$ satisfies

$$
n_{\mathrm{EB}}(\Xi)=\infty,
\qquad
(k_0,k_1,k_2,k_3,\ldots)(\Xi)=(5,3,2,1,1,\ldots).
\tag{12.5}
$$

Nevertheless its powers converge to the pure-state reset
$X\mapsto\operatorname{Tr}(X)R$.

Proof. Prepare only an external reference qubit and the input vector

$$
|\Upsilon\rangle=
\frac{|0\rangle_R\psi+|1\rangle_R\chi}{\sqrt2}.
\tag{12.6}
$$

From (12.1), for every integer $n\ge1$,

$$
F^n(R)=R,\quad F^n(C_\psi)=(-\eta)^nC_\psi,
\quad \langle\chi|F^n(D_\chi)|\chi\rangle=\eta^n.
\tag{12.7}
$$

For the last induction, the $\chi$ diagonal of $R,C_\psi,C_\psi^\dagger$
vanishes and the coefficient of $D_\chi$ gains exactly $\eta$ at each
application. Trace preservation then gives
$\langle\psi|F^n(D_\chi)|\psi\rangle=1-\eta^n$.
The reference partial transpose of
$(\operatorname{id}_R\otimes\Xi^n)(|\Upsilon\rangle\langle\Upsilon|)$
compressed to
$\operatorname{span}\{|0\rangle_R\chi,|1\rangle_R\psi\}$ is

$$
\frac12\begin{pmatrix}0&(-\eta)^n\\(-\eta)^n&1-\eta^n\end{pmatrix}.
\tag{12.8}
$$

Its determinant is

$$
-\frac{\eta^{2n}}4<0.
\tag{12.9}
$$

A positive operator has positive compressions, whereas this compression
has one negative eigenvalue. The full output is therefore NPT for every
finite $n$. This proves infinite EB index by an all-$n$ induction and a
strict analytic determinant, not by finitely many examples.

The first two code dimensions are Theorem 11.2, and the later ones are
Theorem 9.2. Finally (12.2) gives convergence of $F^n$ on the full qubit
algebra to $\mathcal R_\psi$. Every two-step output of $\Xi$ is in $T$ and
$\Xi$ is TP, so
$\Xi^n=F^{n-2}\Xi^2$ for $n\ge2$ converges to the reset on all $M_5$.
Its stationary state is uniquely $R$: any stationary state belongs to the
two-step range and is fixed by the limiting reset. It has rank one, so this
is not mixing to a faithful stationary state. The EB limit and the absence
of finite EB iterates are compatible because that limit lies on the
boundary relevant to separability. $\square$

**Theorem 12.3 (Classical, exact, and entanglement data separate).** Let

$$
\Psi(X)=\sum_{i,j}Q_{ij}X_{ii}P_j.
\tag{12.10}
$$

At the same fixed interior $\eta$, the three allowed channels $\Psi$,
$\Phi_{\mathrm{can}}$, and $\Xi$ have the same law (2.2), whereas their EB
indices are $1,3,\infty$ respectively. The last two have the same basis-state
outputs and the same sharp exact-code sequence.

Proof. The operators $\sqrt{Q_{ij}}|j\rangle\langle i|$ on the eight edges
are rank-one Kraus operators for $\Psi$, their squared products sum to $I$,
and its full law is immediate from (12.10). Thus it is EB and has index one.
An EB channel cannot have an exactly recoverable qubit: a maximally
entangled code-reference input would remain separable after the channel
and any terminal local decoder, contradicting exact restoration of that
entangled input. Hence $k_n(\Psi)=1$ for $n\ge1$. The other assertions were
proved in Theorems 10.2–10.3, 11.2, and 12.2. Population matching alone
proves none of the asserted entanglement behavior; the Kraus constructions
and witnesses do. $\square$

## 13. Passive logical subsystem obstruction

**Definition 13.1 (Fixed invariant tensor-sector contract).** A passive exact
logical subsystem here consists of a fixed isometry
$J:H_{\mathrm{log}}\otimes H_{\mathrm g}\to H$, a fixed unitary $U$ on
$H_{\mathrm{log}}$, and a CPTP gauge map $\Gamma$ such that for all complex
$X,Y$ on the two factors,

$$
\Phi\bigl(J(X\otimes Y)J^\dagger\bigr)
=J\bigl(UXU^\dagger\otimes\Gamma(Y)\bigr)J^\dagger.
\tag{13.1}
$$

There is no leakage from this tensor sector. The logical factor is
preserved, up to its known unitary, for every logical state and gauge input.
This is the invariant noiseless-subsystem setting of
[Kribs et al., §2][OQEC], with logical and gauge factors written in the
opposite order when necessary. It does not describe intermediate active
recovery or a changing encoding.

**Theorem 13.2 (No passive exact logical qubit in any interior lift).** Under
(13.1), every allowed interior lift has $\dim H_{\mathrm{log}}\le1$.

Proof. Choose a unit gauge vector $g$ and the initial code
$C=J(H_{\mathrm{log}}\otimes\mathbb Cg)$. Its dimension is
$\dim H_{\mathrm{log}}$. After $n$ steps its encoded input becomes

$$
J\bigl(U^n XU^{-n}\otimes\Gamma^n(|g\rangle\langle g|)\bigr)J^\dagger.
$$

A terminal decoder compresses to the sector, traces the gauge, undoes
$U^n$, and appends the original pure gauge $g$. Complete it on the
orthogonal complement by resetting to a fixed pure vector of $C$.
Explicitly, if $P=JJ^\dagger$ and $\rho_C$ is that state, it is

$$
\mathcal D_n(Y)=
J\left[
 U^{-n}\operatorname{Tr}_{\mathrm g}(J^\dagger YJ)U^n
 \otimes|g\rangle\langle g|
\right]J^\dagger
+\operatorname{Tr}((I-P)Y)\rho_C.
\tag{13.2}
$$

Each term is CP and their traces add to $\operatorname{Tr}Y$, so this is
CPTP. It recovers every complex matrix supported on $C$. If the logical
dimension were at least two, $n=3$ would contradict Theorem 9.2.
The proof is limited to the stated tensor-sector contract. $\square$

## 14. Faithful sufficient conditions for finite EB and unbounded indices

**Theorem 14.1 (Every positive mixture with the specified classical
prepare-and-measure lift has finite EB index).** Fix $0<\eta<1$, let $\Theta$
be any allowed lift, and let $0<\epsilon\le1$. Define

$$
\Phi_\epsilon=(1-\epsilon)\Theta+\epsilon\Psi,
\tag{14.1}
$$

where $\Psi$ is precisely the basis measure-and-prepare channel (12.10).
Then $\Phi_\epsilon$ is allowed, has a unique faithful stationary state
$\sigma$, converges in powers to $X\mapsto\operatorname{Tr}(X)\sigma$, and
has finite EB index. A stationary state is faithful here if it is positive
definite on all of $H$, not merely on its own support.

Proof. The common linear constraints (2.2) and the convexity of CPTP maps
give legality. Let

$$
m=\min_{i,j}(Q^4)_{ij}>0.
$$

The positivity is Theorem 3.2. Expand the fourth power of the convex mixture
as the sum of all ordered four-letter CP compositions. No commutativity is
assumed. Keeping only its all-$\Psi$ term gives the CP-order inequality

$$
\Phi_\epsilon^4\ \ge_{\mathrm{CP}}\ \epsilon^4\Psi^4.
\tag{14.2}
$$

The notation means the difference is completely positive. The output-first
Choi matrix of $\Psi^4$ is diagonal with entries $(Q^4)_{ij}\ge m$.
The completely depolarizing reset
$\mathcal R_{I/5}(X)=\operatorname{Tr}(X)I_5/5$ has Choi matrix $I_{25}/5$.
Consequently

$$
\Psi^4\ge_{\mathrm{CP}}5m\mathcal R_{I/5},\qquad
\Phi_\epsilon^4\ge_{\mathrm{CP}}\mu\mathcal R_{I/5},
\quad \mu=5\epsilon^4m\in(0,1].
\tag{14.3}
$$

The bound $5m\le1$ follows by summing one row of $Q^4$.
If $\mu<1$, the difference in (14.3) has trace
$(1-\mu)\operatorname{Tr}X$, and hence

$$
\Phi_\epsilon^4=\mu\mathcal R_{I/5}+(1-\mu)\Lambda_\epsilon
\tag{14.4}
$$

for a CPTP $\Lambda_\epsilon$. On differences of states the reset term
vanishes. A positive TP map contracts the trace norm of Hermitian inputs:
write the positive and negative parts and use the triangle inequality and
trace preservation. Thus (14.4) is a strict contraction of states with
factor at most $1-\mu$. The complete finite-dimensional state space and the
contraction principle give a unique fixed state $\sigma$ and convergence
of $(\Phi_\epsilon^4)^k$ to its reset. Moreover (14.2) gives, for every state
$\rho$,

$$
\Phi_\epsilon^4(\rho)\ge\epsilon^4\Psi^4(\rho)
\ge\epsilon^4m I_5.
\tag{14.5}
$$

Hence $\sigma\ge\epsilon^4m I_5>0$. Since $\Phi_\epsilon$ commutes with its
fourth power, $\Phi_\epsilon(\sigma)$ is another fixed state of that fourth
power and equals $\sigma$. For each residue $j=0,1,2,3$,
$\Phi_\epsilon^{4k+j}=\Phi_\epsilon^j(\Phi_\epsilon^4)^k$ has the same reset
limit. If $\mu=1$, the fourth power is already $\mathcal R_{I/5}$; commutation
gives its stationary state $I_5/5$ and the same conclusion directly.

It remains to justify why this faithful reset limit implies a finite EB
iterate. By finite-dimensional linearity, convergence on states implies
convergence on all complex matrix units and on Choi matrices. The normalized
Choi limit in our convention is

$$
J_{\Phi_\epsilon^n}/5\longrightarrow\sigma\otimes I_5/5.
\tag{14.6}
$$

A product of two full-rank states lies in the interior of the separable
states, the separable-interior mechanism used in
[Hanson–Rouzé–Stilck França, Proposition 2.6 and §3][HRS]. An elementary
finite-dimensional justification suffices here. On each local space choose
a basis $H_1,\ldots,H_{d^2-1}$ of traceless Hermitian matrices and $t>0$
small enough that $I_d/d\pm tH_a$ are positive. These local states affinely
span the trace-one Hermitian hyperplane and have average $I_d/d$ when both
signs are used equally. The finite set of all products of the states from
the two factors affinely spans the bipartite trace-one hyperplane: their
linear spans contain every local Hermitian matrix, so their tensor products
linearly span every bipartite Hermitian matrix, and all have trace one.
Their equal positive average is $I_d/d\otimes I_e/e$.
If this average lay on a supporting boundary hyperplane of their convex
hull, every vertex would have to lie on that hyperplane, contradicting the
full affine span. Thus this product is an interior point of a full-dimensional
convex hull of separable states.

An invertible local positive filter, followed by trace normalization, is a
homeomorphism of the state space that preserves separability in both
directions. Applying the filter $(5\sigma)^{1/2}$ to the first factor maps
$I_5/5\otimes I_5/5$ to $\sigma\otimes I_5/5$. Its invertibility uses
faithfulness. Therefore the limit in (14.6) has a separable neighborhood.
All sufficiently late normalized Choi states are in that neighborhood and
are separable. The Choi–EB equivalence [HSR, Theorem 4][HSR] makes these
iterates EB. This proves finite index without assuming that classical
primitivity alone gives quantum mixing.
The mixing partner in this theorem is the specified $\Psi$ with strictly
positive fourth-step Choi matrix. An arbitrary EB mixing partner without
that property is not covered. $\square$

**Theorem 14.2 (Positive definiteness on the eight-edge support).** Let
$0<\eta<1$ and let an allowed lift $\Phi$ have a Choi matrix positive definite
on the full eight-dimensional edge space (4.3), and zero on its orthogonal
complement. Then $n_{\mathrm{EB}}(\Phi)<\infty$.

Proof. The Choi matrix of $\Psi$ is diagonal and strictly positive on exactly
this edge space. Positive definiteness of $J_\Phi$ there permits some
$0<\epsilon<1$ with

$$
J_\Phi\ge\epsilon J_\Psi.
$$

For example choose $\epsilon$ smaller than the least eigenvalue of
$J_\Psi^{-1/2}J_\Phi J_\Psi^{-1/2}$ restricted to that space, and smaller
than one. All operators vanish on the complementary space, so this is a
full-matrix inequality. The residual

$$
\Theta=\frac{\Phi-\epsilon\Psi}{1-\epsilon}
$$

is CP. Its output-diagonal Choi blocks remain precisely those in (4.2),
and it is TP by the same trace constraint. Thus it is an allowed lift, and
Theorem 14.1 applies. The condition is relative positive definiteness on all
eight edges, not positive definiteness on $\mathbb C^{25}$ and not positivity
only on the possibly smaller range of $J_\Phi$. $\square$

**Theorem 14.3 (Unbounded finite EB indices at each fixed interior parameter).**
For every fixed $0<\eta<1$ and every integer $N\ge1$, there is an allowed lift
whose Choi matrix is positive definite on the full eight-edge space and whose
EB index is finite and greater than $N$.

Proof. Take

$$
\Phi_\epsilon=(1-\epsilon)\Xi+\epsilon\Psi,\qquad0<\epsilon<1.
$$

Its Choi matrix is positive definite on the edge space because it dominates
$\epsilon J_\Psi>0$ there. Theorem 14.1 gives finite EB index.
For the fixed reference input (12.6), apply $\Phi_\epsilon^N$ to the system,
partially transpose the reference, and compress to the fixed two-plane
used in (12.8). Every matrix entry is a polynomial in $\epsilon$, as a finite
iterate of a linear mixture; its determinant is continuous. At $\epsilon=0$
that determinant is exactly $-\eta^{2N}/4<0$. It therefore stays strictly
negative for every sufficiently small positive $\epsilon$. This proves
that $\Phi_\epsilon^N$ is not EB. If an earlier iterate were EB, composition
would make this one EB as well. Hence $n_{\mathrm{EB}}(\Phi_\epsilon)>N$.

This uses continuity at one prescribed finite $N$, with $\epsilon$ allowed
to depend on $N$; it makes no interchange of the limits $N\to\infty$ and
$\epsilon\to0$. It proves that no finite EB-index upper bound depending
only on this fixed $\eta$ exists, even within the full-edge-positive
finite-index subclass. The corresponding exact qubit codes are still lost
by step three, by Theorem 9.2. $\square$

## 15. The two endpoints are separate models

**Definition 15.1 (Endpoint extension).** At $\eta=0$ or $\eta=1$ define the
allowed class by the same all-complex-input law (2.2), using the endpoint
matrix $Q$. The eight-edge interior parametrization reduces to five
nonzero edges at either endpoint. Definitions of exact correction and EB
are unchanged. Endpoint statements below are direct proofs, not consequences
of dividing an interior formula by a vanishing coefficient.

**Theorem 15.2 (Zero activity: universal third-step reset).** At $\eta=0$,
every allowed lift satisfies

$$
\Phi^3(X)=\operatorname{Tr}(X)P_0\qquad(X\in M_5(\mathbb C)).
\tag{15.1}
$$

The class optima are $5,3,2,1,1,\ldots$. The canonical lift attains them and
has EB index three. The endpoint channel $\Xi$ equals the canonical channel.

Proof. Directly, every row of $Q_0^3$ is $(1,0,0,0,0)$. Iterating the
all-input law shows that every density matrix has third-step output diagonal
$(1,0,0,0,0)$. Positivity forces the whole output to be $P_0$.
Complex linearity extends this to (15.1). Thus every lift has $k_n=1$ for
$n\ge3$ and EB index at most three.

The proof of the one-step bound uses $\Phi^\dagger(P_0)=P_A$,
$\Phi^\dagger(P_1)=P_B$, and $\Phi^\dagger(P_2)=P_D$ and is valid without
$\eta>0$. The proof of the two-step bound also remains valid: the two
nonzero projections into $A$ in (6.3) have coefficient $\sqrt r=1$.
The canonical Kraus formulas, codes, and terminal decoder remain valid at
$r=1$. They attain dimensions three and two at the first two steps; the
reference witnesses of Theorem 10.3 still apply. Hence its EB index is
three and the optimum sequence follows. At this endpoint $W$ is diagonal
with entries $(1,-1,1,1,-1)$, giving $K_0W=K_0$ and $K_1W=-K_1$; these
Kraus phases leave the channel unchanged. $\square$

**Theorem 15.3 (Infinite activity: a persistent exact swap qubit).** At
$\eta=1$ the class optima are

$$
(K_0(1),K_1(1),K_2(1),K_3(1),\ldots)=(5,3,2,2,2,\ldots).
\tag{15.2}
$$

The endpoint $\Xi$ attains them and has infinite EB index. The endpoint
canonical channel instead has dimensions $5,3,2,1,1,\ldots$ and EB index
three.

Proof. Substituting $r=0$ in (11.3) gives the lawful Kraus operators

$$
L_0=|3\rangle\langle1|+|4\rangle\langle2|+|2\rangle\langle4|,
\qquad
L_1=|3\rangle\langle0|+|2\rangle\langle3|.
\tag{15.3}
$$

Their squared products sum to $I_5$, and at the output coordinates with two
predecessors the two predecessors have distinct Kraus labels. Thus their
all-complex-input population law is exactly $Q_1$.
On $C_{\mathrm{end}}=\operatorname{span}\{|2\rangle,|4\rangle\}$,
$L_1$ vanishes and $L_0$ is the swap

$$
U_{\mathrm{sw}}=|2\rangle\langle4|+|4\rangle\langle2|.
$$

Every iterate is unitary on this code. For even $n$ let
$B_n=P_{C_{\mathrm{end}}}$ and for odd $n$ let $B_n=U_{\mathrm{sw}}$.
An exact terminal decoder is

$$
Y\longmapsto B_nYB_n^\dagger+
\operatorname{Tr}((I-P_{C_{\mathrm{end}}})Y)P_2.
\tag{15.4}
$$

It is CPTP by the partial-isometry Kraus completion in (10.6). It undoes the
swap power on all complex code inputs. A reference maximally entangled with
this qubit remains entangled for every finite iterate, so the EB index is
infinite.

For the universal one-step bound at this endpoint, substitute the positive
dual effects $\Phi^\dagger(P_3)=P_A$ and $\Phi^\dagger(P_4)=P_B$, together
with $\Phi^\dagger(P_2)=P_D$, into Theorem 6.1's rank argument. The same
normal form gives $k_1\le3$. The canonical first-step code attains three,
and $WC_1$ gives the same for $\Xi$.
Directly $Q_1^2$ has no nonzero output columns outside $\{2,4\}$.
Positivity therefore confines every lift's entire two-step output to
$C_{\mathrm{end}}$. The reversible form $ks\le2$ for a code into this
output space gives $k_n\le2$ for all $n\ge2$. The swap code attains the
bound, proving (15.2).
Finally the canonical lower codes and the record-erasure formula (10.8)
remain valid at $\eta=1$. They give its separate code sequence and EB index
three, with the same explicit earlier NPT witnesses.
The interior contradiction fails here because $F_3$ and the lower bound
$r/(1+r)$ lose strict positivity. $\square$

**Convention 15.4 (Source meaning of endpoints).** The source assumption
$\lambda>0$ finite corresponds exactly to $0<\eta<1$. The endpoint $\eta=0$
is the formal $\lambda=0$ limit, with stationary source concentrated on the
all-zero word and $p=(1,0,0,0,0)$. The endpoint $\eta=1$ is the formal
$\lambda\to\infty$ limit, with the stationary no11 chain alternating between
0 and 1 and uniform random phase; its triple marginal is
$(0,0,1/2,0,1/2)$. These statements follow by substituting in $P_\eta$ and
$\pi$ and taking the corresponding limits in (3.2). The endpoint quantum
classes still allow arbitrary inputs on $H$, including coordinates absent
from the stationary source support. Neither endpoint has the full source
support or $Q^4>0$ used in §14, and no finite-EB conclusion from that section
is asserted there.

## 16. Source ownership, literature status, and mathematical boundaries

**Convention 16.1 (Owning classical references).** The classical source
passages referred to in this volume are the following passages at immutable
revision `9f316de1477daccdb5b73d05646c0c6411874668`:

| Source | Exact mathematical use |
| --- | --- |
| [LocalClock][LC], Definition 15.1 | Complete source factorization, guard, and native affine composition state; the empty complete window also applies $M^3$. |
| [LocalClock][LC], Propositions 15.6 and 15.8 | Unit-activity golden body law and fixed finite-activity Perron normalization, with fixed compatible endpoints and a two-sided body limit. |
| [Pyramid][PY], Definition 17.1 and Theorem 17.3 | General stationary no11 source, actual-source distinctions, stationary triple constraints, and full-positivity domain. |
| [Pyramid][PY], Proposition 17.4 | Inherited actual-source counterexample to determining remote law from the full five probabilities. |
| [Pyramid][PY], Definition 18.1 and Theorems 18.2–18.3 | An explicitly selected second-order extension, its uniqueness within that class, and entropy-rate selection with all-past equality conditions. |
| [Pyramid][PY], Proposition 18.4 | Memory-order and transfer-rank statements for that selected chain; they do not classify arbitrary actual sources with the same triple marginal. |

The computation in Theorem 3.2 is the finite chronological interface for the
specified Perron source. It does not reprove these general source results.
Choosing a source extension, choosing an all-input population constraint,
and choosing one CPTP lift are three different decisions.

**Convention 16.2 (Standard primary sources and hypotheses).** The following
are `literature-attested` inputs or framework references. Model-specific
identities and obstructions in this volume are ordinary `repo-derived`
derivations; these labels make no claim of exhaustive novelty search.

| Primary source and version | Precise use and conditions |
| --- | --- |
| W. F. Stinespring, *Positive Functions on C\*-Algebras*, Proc. Amer. Math. Soc. **6** (1955), 211–216, [DOI 10.1090/S0002-9939-1955-0069403-4][STI] | Dilation framework. For the finite-dimensional CPTP maps here the isometric dilation and its complex Gram convention are given explicitly in §4. No environmental dimension two is assumed for the full class. |
| M.-D. Choi, *Completely positive linear maps on complex matrices*, Linear Algebra Appl. **10** (1975), 285–290, [DOI 10.1016/0024-3795(75)90075-0][CHOI] | Complete positivity and the positive Choi matrix; the normalization and tensor order are fixed in (4.1). TP is partial output trace $I$, rather than trace-one normalization of $J$. |
| E. Knill and R. Laflamme, *A Theory of Quantum Error-Correcting Codes*, [quant-ph/9604034v1][KL], Theorems 3.2 and 3.5, equations (19)–(20) | Exact arbitrary-subspace correction iff every compressed $A_\mu^\dagger A_\nu$ is scalar, including all complex cross matrix elements. The supported syndrome representation and all rank consequences used here are derived in §5. |
| M. Horodecki, P. W. Shor, and M. B. Ruskai, *General Entanglement Breaking Channels / Entanglement Breaking Channels*, [quant-ph/0302031v2][HSR], §2, Theorem 4 | For finite-dimensional CPTP maps, EB, measure-and-prepare form, separable maximally-entangled Choi output, and rank-one Kraus form are equivalent. The measurement is a POVM and the Kraus operators satisfy completeness. |
| K. Korzekwa, S. Czachórski, Z. Puchała, and K. Życzkowski, *Coherifying quantum channels*, [1710.04228v2][COH], §II B, equations (6)–(9), and diagonal Choi-block interpretation following (13) | Their normalized Choi matrix is $J/5$ here and their classical matrix is $Q^{\mathsf T}$. Fixing basis-input populations fixes only the Choi diagonal. The stronger all-input diagonal-block constraint is proved in §4 and is not attributed to the weaker coherification criterion. |
| T. Theurer, D. Egloff, L. Zhang, and M. B. Plenio, *Quantifying Operations with an Application to Coherence*, [1806.07332v2][THE], Definition 3, equation (7), and supplemental Proposition 15, equation (35) | Detection-incoherence is $\Delta\Phi=\Delta\Phi\Delta$. Its coefficient condition matches (4.2) with $p(a\mid b)=Q_{ba}$. Creation-incoherence and DIO are different constraints. |
| L. Lami and V. Giovannetti, *Entanglement-Breaking Indices*, [1411.2517v4][LG], §III, Example 1, equations (22)–(29), paragraph after (28) | Generalized-amplitude-damping powers supply a standard precedent for decay with infinite EB index at the stated pure-stationary endpoint. No damping-index formula, endpoint extrapolation, or five-state construction is imported from it. |
| E. P. Hanson, C. Rouzé, and D. Stilck França, *Eventually entanglement breaking Markovian dynamics: structure and characteristic times*, [1902.08173v2][HRS], Proposition 2.6, §3, and Theorem 3.11 | Full-rank product separable interior and the faithful quantum-channel framework for eventual EB. A primitive quantum channel mixing to a faithful state has the interior-reset mechanism. Classical primitivity alone does not meet those quantum hypotheses. Proposition 3.1 is a density statement; its proof uses the interior-limit mechanism, rather than asserting that every classical primitive action suffices. |
| D. Kribs, R. Laflamme, D. Poulin, and M. Lesosky, *Operator quantum error correction*, [quant-ph/0504189v3][OQEC], §2, Lemma 2.3, Definition 2.4, and Theorem 2.5 | Fixed invariant tensor-sector noiseless subsystems with all logical inputs and the required Kraus algebra. The differing-range, full-input-gauge transfer of §7 is proved directly, rather than silently substituted for a fixed-sector theorem. |
| B. V. Rajarama Bhat, P. Dey, and B. Saha, *A complete characterization of eventually entanglement breaking unital quantum channels*, [2609.24168v1][BDS], introduction and Theorem 6.11 | A peripheral/nonzero-eigenvector criterion under the paper's unital CPTP hypothesis. No such criterion is applied to the present nonunital lifts or their non-TP adjoints. |

**Theorem 16.3 (Why the unital and faithful hypotheses cannot be assigned
from the classical law).** Every allowed lift in this volume is nonunital.
The same-law channel $\Xi$ has a nonfaithful stationary state. Thus neither
unital CPTP peripheral-spectrum results nor a faithful stationary-state
hypothesis follows from (2.2), even though $Q^4>0$ in the interior.

Proof. Substituting $X=I_5$ into (2.2) gives

$$
\operatorname{diag}\Phi(I_5)=(2r,r,2,2\eta,\eta)^{\mathsf T}.
$$

Its coordinate 2 is two, not one, so $\Phi(I_5)\ne I_5$.
The adjoint is unital because $\Phi$ is TP, but it is not TP because $\Phi$
is not unital. Hence neither map is a unital CPTP channel to which the
unital theorem in [Bhat–Dey–Saha][BDS] applies without additional work.
The stationary state of $\Xi$ is the rank-one $R$ by Theorem 12.2, although
its populations are the strictly positive stationary vector $p$ and its
classical action has $Q^4>0$. This also directly disproves any inference
from the classical primitive matrix to a faithful quantum stationary state.
$\square$

**Convention 16.4 (Exactly what is and is not settled).** The interior
all-lift exact-code theorem, the sharp constructions, the same-law finite
versus infinite EB distinction, the tensor-sector obstruction, and the
specified finite-EB sufficient conditions have the ordinary proofs above.
There is no remaining third-step exact-code alternative within this precise
class. These are conditional mathematical statements about that class;
they do not establish a physical source-to-CPTP realization, Hamiltonian,
quantum-field model, laboratory dynamics, or a physical meaning of one
chronological slide. No asymptotic capacity, universal relaxation theorem,
universal sharp convergence rate, all-lift finite EB theorem, priority claim,
or exhaustive novelty determination is asserted. In particular the
quantified finite-EB results are exactly those of §14, and the explicit
relaxation formula (12.2) belongs to $\Xi$ alone. Kernel formalization and
physical realization would require additional work of different kinds;
ordinary proofs and a classical source interface do not supply either one.

[LC]: AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md
[PY]: AURIC_FIB_ATOM_PYRAMID_LOCAL_FILLINGS_SOFT_TO_RIGID_AND_ODD_CYCLE_OBSTRUCTIONS.md
[STI]: https://doi.org/10.1090/S0002-9939-1955-0069403-4
[CHOI]: https://doi.org/10.1016/0024-3795(75)90075-0
[KL]: https://arxiv.org/abs/quant-ph/9604034v1
[HSR]: https://arxiv.org/abs/quant-ph/0302031v2
[COH]: https://arxiv.org/abs/1710.04228v2
[THE]: https://arxiv.org/abs/1806.07332v2
[LG]: https://arxiv.org/abs/1411.2517v4
[HRS]: https://arxiv.org/abs/1902.08173v2
[OQEC]: https://arxiv.org/abs/quant-ph/0504189v3
[BDS]: https://arxiv.org/abs/2609.24168v1

## 追加锚（本行以下为增补区）
