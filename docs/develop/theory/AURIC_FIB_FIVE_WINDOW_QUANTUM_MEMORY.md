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

## 17. A legal interior lift with hidden classical memory

**Convention 17.1 (Scope and norms of the extension).** Retain the spaces,
basis, allowed-lift definition, and homogeneous terminal-access contract of
§§1–2. This extension uses that model without changing its classical source
interpretation in §3. Sections 17–23 concern one lift at $\eta=r=1/2$ and its
specified perturbations. Section 24 gives full ordinary mathematical proofs
for one explicitly selected family at all interior parameters. Its conclusions
away from $1/2$ concern only that family. The all-lift exact-code theorem remains
Theorem 9.2; no proof of it is repeated here. Sections 27–31 separately
prove a sufficient all-lift mixing interval with complete reference bounds.

For a density matrix $\sigma$ write
$\mathcal R_\sigma(X)=\sigma\operatorname{Tr}X$. For any complex-linear map
$\Lambda$, use the unhalved diamond norm

$$
\|\Lambda\|_\diamond=
\sup_{d\ge1}\sup_{0\ne Z\in M_5\otimes M_d}
\frac{\|(\Lambda\otimes\operatorname{id}_d)(Z)\|_1}{\|Z\|_1}.
\tag{17.1}
$$

Inputs in this definition need not be positive or Hermitian. Reference systems
are arbitrary finite-dimensional external systems. All iteration statements
repeat a single chosen channel; they do not change the channel between steps.

**Definition 17.2 (The half-parameter lift).** In this section put

$$
q=\frac1{\sqrt2},\qquad
u=q(|0\rangle+|3\rangle),\qquad
v=q(|1\rangle+|4\rangle),\qquad z=|2\rangle,
\qquad R=\operatorname{span}\{u,v,z\}.
\tag{17.2}
$$

The vectors $u,v,z$ are orthonormal. Define

$$
\begin{aligned}
K^\circ_0&=|u\rangle\langle0|+q|v\rangle\langle2|
                         +|z\rangle\langle4|,\\
K^\circ_1&=|u\rangle\langle1|+q|v\rangle\langle2|
                         +|z\rangle\langle3|,\\
\Phi_\circ(X)&=K^\circ_0X(K^\circ_0)^\dagger
              +K^\circ_1X(K^\circ_1)^\dagger.
\end{aligned}
\tag{17.3}
$$

**Theorem 17.3 (Kraus, Gram, and all-complex-input legality).** The map
$\Phi_\circ$ is an allowed lift at $\eta=1/2$. Its Choi matrix has rank two,
is supported on the eight edges (4.3), and has nonzero eigenvalues $3,2$ in
the unnormalized convention (4.1). Its entire output is supported on $R$.

Proof. Orthogonality of $u,v,z$ gives

$$
\begin{aligned}
(K^\circ_0)^\dagger K^\circ_0&=P_0+\tfrac12P_2+P_4,\\
(K^\circ_1)^\dagger K^\circ_1&=P_1+\tfrac12P_2+P_3.
\end{aligned}
\tag{17.4}
$$

The sum is $I_5$, so the Kraus map is CPTP. Every Kraus image lies in $R$.
For an arbitrary complex matrix $X$, its output diagonal is

$$
\operatorname{diag}\Phi_\circ(X)=
\begin{pmatrix}
(X_{00}+X_{11})/2\\ X_{22}/2\\ X_{33}+X_{44}\\
(X_{00}+X_{11})/2\\ X_{22}/2
\end{pmatrix}
=Q_{1/2}^{\mathsf T}\operatorname{diag}X.
\tag{17.5}
$$

Indeed the coefficients of $P_u,P_v,P_z$ are respectively
$X_{00}+X_{11},X_{22},X_{33}+X_{44}$; cross operators between the three
vectors have zero computational diagonal because their supports are disjoint.
This proves the full law, including every complex coherence input.

Here is also an actual Gram realization in the conventions of §4. Take
orthonormal environment vectors $f_0,f_1$ and set $f_+=(f_0+f_1)/\sqrt2$.
In (4.4) choose

$$
\alpha_0=\beta_0=f_0,\quad
\alpha_1=\beta_1=f_1,\quad
\gamma_0=\gamma_1=f_+,\quad
\delta_0=f_1,\quad\delta_1=f_0.
\tag{17.6}
$$

These vectors obey all three orthogonality constraints (4.5); the two
$\gamma$ vectors are equal, which is permitted. In precisely the
output–input edge order (4.3), their coordinate factor is

$$
C=\begin{pmatrix}
1&0&q&0&1&1&0&q\\
0&1&q&1&0&0&1&q
\end{pmatrix}.
\tag{17.7}
$$

Thus $G=C^\dagger C$ is a rank-two PSD Gram matrix with unit diagonal.
The forced zeros are $G_{12}=G_{67}=G_{45}=0$, where the column indices in
this sentence run from $1$ to $8$. The corresponding edge weights are

$$
D_{\mathcal E}=\operatorname{diag}(q,q,q,1,1,q,q,q).
$$

All coordinates are real, so the conjugation convention (4.6) gives the
edge-supported Choi matrix $D_{\mathcal E}GD_{\mathcal E}$. Padding by zero
outside the edge space gives exactly (4.1). Alternatively its two
vectorized-Kraus columns have Gram matrix

$$
\begin{pmatrix}
\operatorname{Tr}((K^\circ_0)^\dagger K^\circ_0)&
\operatorname{Tr}((K^\circ_0)^\dagger K^\circ_1)\\
\operatorname{Tr}((K^\circ_1)^\dagger K^\circ_0)&
\operatorname{Tr}((K^\circ_1)^\dagger K^\circ_1)
\end{pmatrix}
=\begin{pmatrix}5/2&1/2\\1/2&5/2\end{pmatrix}.
\tag{17.8}
$$

Its eigenvalues are $3,2$, which are the nonzero Choi eigenvalues.
The dilation specified by
(17.6) can be applied with a fresh discarded environment at every repetition,
as required by Convention 1.2. $\square$

## 18. Orthogonal fixed states and a conserved effect invisible to populations

**Theorem 18.1 (Complete fixed-state family).** Put

$$
s=\frac{u+v+z}{\sqrt3},\qquad
P=|s\rangle\langle s|,\qquad M=\frac{P_R-P}{2}.
\tag{18.1}
$$

Then $P,M$ are orthogonally supported stationary density matrices, both with
computational diagonal

$$
p_{1/2}=\frac16(1,1,2,1,1)^{\mathsf T}.
\tag{18.2}
$$

All stationary density matrices of $\Phi_\circ$ are exactly

$$
\rho_t=tP+(1-t)M,\qquad 0\le t\le1.
\tag{18.3}
$$

In particular the nonzero operator $\Delta_\circ=P-M$ is fixed, traceless,
and has zero computational diagonal.

Proof. In the ordered basis $(u,v,z)$, the restricted Kraus matrices are
$qU_0,qU_1$, where

$$
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix}.
\tag{18.4}
$$

Both are permutation unitaries fixing $s$. Hence the restriction
$F=(\operatorname{Ad}_{U_0}+\operatorname{Ad}_{U_1})/2$ fixes $P_R,P,M$.
The projection identities $P^2=P$, $M^2=M/2$, $PM=0$ and
$\operatorname{Tr}P=\operatorname{Tr}M=1$ prove positivity, normalization,
and orthogonal supports. Directly
$\operatorname{diag}P=p_{1/2}$ and $\operatorname{diag}P_R=3p_{1/2}$,
giving (18.2) for $M$ as well.

Every full-space fixed operator is supported on $R$, by Theorem 17.3. If
$F(X)=X$ for a complex $X\in\mathcal B(R)$, set $Y_j=U_jXU_j^\dagger$.
The Hilbert–Schmidt identity

$$
\left\|\frac{Y_0+Y_1}{2}\right\|_2^2
=\frac{\|Y_0\|_2^2+\|Y_1\|_2^2}{2}
 -\frac{\|Y_0-Y_1\|_2^2}{4}
\tag{18.5}
$$

forces $Y_0=Y_1=X$, since both $Y_j$ have norm $\|X\|_2$. The transposition
$U_0$ and three-cycle $U_1$ generate the permutation group on three letters.
A matrix commuting with that group has one common diagonal entry and one
common off-diagonal entry: simultaneous permutations are transitive on each
of these two sets of positions. This commutant is
$\operatorname{span}_{\mathbb C}\{P_R,P\}=\operatorname{span}_{\mathbb C}\{P,M\}$.
A positive trace-one member has nonnegative weights on the orthogonal sectors
$\mathbb Cs$ and $T=R\cap s^\perp$, and therefore has exactly (18.3).
The assertions about $\Delta_\circ$ now follow. $\square$

**Proposition 18.2 (A permanently readable classical label).** Encode a
classical zero by $P$ and a classical one by any density supported on
$T=R\cap s^\perp$. At every iteration the terminal POVM
$\{P,I_5-P\}$ reads this label with zero error.

Proof. Each of $U_0,U_1$ fixes $s$ and preserves its orthogonal complement
in $R$. Their Kraus restrictions therefore preserve the two sectors
separately. The zero input stays $P$; the one input stays supported on $T$.
The displayed measurement distinguishes these supports. In particular the
stationary inputs $P,M$ have identical five populations at every step but
remain perfectly distinguishable by this measurement. The preserved label
is classical; this argument does not assert reversible action on
superpositions of its two sectors. $\square$

**Theorem 18.3 (Explicit conserved effect).** Define

$$
\begin{aligned}
h_0&=\frac{|0\rangle+|4\rangle}{\sqrt3}
                         +\frac{|2\rangle}{\sqrt6},\\
h_1&=\frac{|1\rangle+|3\rangle}{\sqrt3}
                         +\frac{|2\rangle}{\sqrt6},\\
E&=\Phi_\circ^\dagger(P)=|h_0\rangle\langle h_0|
                              +|h_1\rangle\langle h_1|.
\end{aligned}
\tag{18.6}
$$

Then $0\le E\le I_5$, its spectrum is $1,2/3,0,0,0$, its compression to
$R$ is $P$, and $\Phi_\circ^\dagger(E)=E$. Thus
$\operatorname{Tr}(E\Phi_\circ^n(X))=\operatorname{Tr}(EX)$ for all complex
$X$ and all $n\ge0$.

Proof. Taking $(K^\circ_j)^\dagger s$ gives exactly $h_j$. Their two-column
Gram matrix is
$\left(\begin{smallmatrix}5/6&1/6\\1/6&5/6\end{smallmatrix}\right)$,
so the stated spectrum follows. More explicitly, with

$$
d=\frac{|0\rangle-|1\rangle-|3\rangle+|4\rangle}{2},
\qquad d\perp R,
$$

one has $E=P+(2/3)|d\rangle\langle d|$. This proves both the effect
inequalities and its compression. Every $\Phi_\circ(X)$ is supported on
$R$, so
$\operatorname{Tr}(E\Phi_\circ(X))=\operatorname{Tr}(P\Phi_\circ(X))
=\operatorname{Tr}(EX)$. Nondegeneracy of the trace pairing on the complex
matrix algebra proves the adjoint identity and then its iterates.
$\square$

## 19. The full superoperator polynomial and explicit limit

**Theorem 19.1 (Full-space polynomial, including the transient).** On all
$M_5(\mathbb C)$ one has

$$
\begin{aligned}
\chi_{\Phi_\circ}(t)&=t^{20}(t-1)^2(t+1/2)^3,\\
\Phi_\circ^2(\Phi_\circ-\operatorname{id})
                    (\Phi_\circ+\tfrac12\operatorname{id})&=0.
\end{aligned}
\tag{19.1}
$$

Proof. In $\mathcal B(R)\cong M_3(\mathbb C)$ denote its matrix units by
$E_{ij}$, with indices $0,1,2$ referring only to $(u,v,z)$. The following
three complex subspaces form a direct sum of the entire algebra:

$$
\begin{aligned}
\mathcal D_R&=\operatorname{span}\{E_{00},E_{11},E_{22}\},\\
\mathcal S_R&=\operatorname{span}\{E_{01}+E_{10},E_{02}+E_{20},E_{12}+E_{21}\},\\
\mathcal A_R&=\operatorname{span}\{E_{01}-E_{10},E_{02}-E_{20},E_{12}-E_{21}\}.
\end{aligned}
\tag{19.2}
$$

Conjugating each displayed basis vector by the two permutations in (18.4)
gives the respective matrices

$$
D_\circ=\begin{pmatrix}1/2&1/2&0\\0&0&1\\1/2&1/2&0\end{pmatrix},\quad
S_\circ=\begin{pmatrix}0&1/2&1/2\\1&0&0\\0&1/2&1/2\end{pmatrix},\quad
A_\circ=\begin{pmatrix}0&1/2&1/2\\0&0&0\\0&-1/2&-1/2\end{pmatrix}.
\tag{19.3}
$$

For example $F(E_{01}+E_{10})=E_{02}+E_{20}$, whereas
$F(E_{01}-E_{10})=0$; the other columns follow by the same explicit
permutations. The characteristic polynomials of the first two matrices are
$t(t-1)(t+1/2)$, so Cayley–Hamilton annihilates them by that polynomial.
The third has characteristic polynomial $t^2(t+1/2)$ and directly satisfies
$A_\circ^2=-A_\circ/2$. Thus

$$
\chi_F(t)=t^4(t-1)^2(t+1/2)^3,\qquad
F(F-\operatorname{id})(F+\tfrac12\operatorname{id})=0.
\tag{19.4}
$$

The full map has range in the nine-dimensional $\mathcal B(R)$ and induces
the zero map on its sixteen-dimensional quotient in $M_5$. A basis extending
one of $\mathcal B(R)$ makes its matrix block triangular, proving the
characteristic polynomial in (19.1). Apply the restricted polynomial to
$\Phi_\circ(X)\in\mathcal B(R)$ to obtain the full polynomial there.
This extra factor of $\Phi_\circ$ retains the possible zero-mode transient;
the characteristic polynomial alone would not justify dropping it.
$\square$

**Theorem 19.2 (An exact recurrence and a measure-and-prepare limit).** Put

$$
\mathcal T=\frac{\Phi_\circ^2+2\Phi_\circ^3}{3}.
\tag{19.5}
$$

Then $\mathcal T$ is CPTP, idempotent, and satisfies
$\Phi_\circ\mathcal T=\mathcal T\Phi_\circ=\mathcal T$. For all $n\ge2$,

$$
\begin{aligned}
\Phi_\circ^n-\mathcal T
 &=(-1/2)^{n-2}(\Phi_\circ^2-\mathcal T),\\
\|\Phi_\circ^n-\mathcal T\|_\diamond
 &\le\frac43\,2^{-(n-2)}.
\end{aligned}
\tag{19.6}
$$

On every complex input its explicit action is

$$
\mathcal T(X)=P\operatorname{Tr}(EX)
             +M\operatorname{Tr}((I_5-E)X).
\tag{19.7}
$$

In particular the limit is EB and retains a perfectly distinguishable
classical label.

Proof. The polynomial in (19.1) is equivalently
$2\Phi_\circ^4=\Phi_\circ^3+\Phi_\circ^2$. Substitution in (19.5) gives
$\Phi_\circ\mathcal T=\mathcal T\Phi_\circ=\mathcal T$. The convex
combination in (19.5) is CPTP. Its range consists of fixed operators, and
it is the identity on such operators, so $\mathcal T^2=\mathcal T$.
Writing $C=\Phi_\circ^2-\mathcal T$, the same identities give
$\Phi_\circ C=-C/2$. Induction proves the first line of (19.6).
Furthermore
$C=(2/3)(\Phi_\circ^2-\Phi_\circ^3)$, so $\|C\|_\diamond\le4/3$:
a CPTP map has diamond norm one. The complete norm fact is also proved
in Lemma 22.1 below. This proves convergence without a diagonalizability
assumption on the full map.

The fixed space is $\operatorname{span}\{P,M\}$ by Theorem 18.1. Since
$\mathcal T$ preserves trace, its two coefficients sum to
$\operatorname{Tr}X$. On $R$, $E$ compresses to $P$, and its expectation is
conserved. Hence
$\operatorname{Tr}(P\mathcal T(X))=\operatorname{Tr}(E\mathcal T(X))
=\operatorname{Tr}(EX)$, which identifies the first coefficient; the
second is its trace complement. This proves (19.7) for all complex $X$.
The effects $E,I_5-E$ are a POVM, and $P,M$ are densities. Equation (19.7)
is therefore a measure-and-prepare representation and is EB by [Horodecki–Shor–Ruskai,
Theorem 4][HSR]. Its two stationary outputs remain distinguishable by
Proposition 18.2. $\square$

## 20. Exact reset obstruction and NPT at every finite iteration

**Theorem 20.1 (Complete-norm distance from resetting).** For every density
$\sigma$ and every $n\ge0$,

$$
\|\Phi_\circ^n-\mathcal R_\sigma\|_\diamond\ge1.
\tag{20.1}
$$

For the stationary family (18.3) the lower bound improves to
$2\max\{t,1-t\}$. The limiting channel has exactly

$$
\|\mathcal T-\mathcal R_{\rho_t}\|_\diamond
=2\max\{t,1-t\},\qquad
\inf_{\sigma\in\mathcal D(H)}
\|\mathcal T-\mathcal R_\sigma\|_\diamond=1,
\tag{20.2}
$$

and even if a new optimizing reset is chosen at every step,

$$
\lim_{n\to\infty}\inf_{\sigma\in\mathcal D(H)}
\|\Phi_\circ^n-\mathcal R_\sigma\|_\diamond=1.
\tag{20.3}
$$

Proof. Orthogonal density matrices have trace distance two. Applying the
channel difference to the stationary inputs $P,M$ therefore gives

$$
2=\|P-M\|_1\le\|P-\sigma\|_1+\|M-\sigma\|_1
\le2\|\Phi_\circ^n-\mathcal R_\sigma\|_\diamond.
$$

When $\sigma=\rho_t$, the two input distances are $2(1-t)$ and $2t$,
proving the stronger lower bound.

For the exact limiting norm, (19.7) gives

$$
(\mathcal T-\mathcal R_{\rho_t})(X)
=(P-M)\operatorname{Tr}((E-tI_5)X).
\tag{20.4}
$$

For Hermitian $B$, the completely bounded trace norm of
$X\mapsto A\operatorname{Tr}(BX)$ is
$\|A\|_1\|B\|_\infty$. To see the upper bound with arbitrary reference,
write $\ell_B(X)=\operatorname{Tr}(BX)$. The adjoint of
$\ell_B\otimes\operatorname{id}_d$ maps a reference operator $Y$ to
$B\otimes Y$, whose operator norm is $\|B\|_\infty\|Y\|_\infty$.
Trace-norm duality gives the same norm for $\ell_B\otimes\operatorname{id}_d$.
Preparing $A$ tensors its output with $A$, multiplying trace norm by
$\|A\|_1$. Equality is attained without a reference by a unit eigenvector
of $B$ with eigenvalue of maximal absolute value. Here
$\|P-M\|_1=2$ and $\|E-tI_5\|_\infty=\max\{t,1-t\}$, since $E$ has
both eigenvalues zero and one. This proves the first equality in (20.2).
The preceding stationary-input argument applies to $\mathcal T$ too, so
all resets have distance at least one; $t=1/2$ attains it.

Finally, distance to any fixed set is 1-Lipschitz in its argument under
any norm, by the triangle inequality and taking infima. Equation (19.6)
therefore transfers the infimum in (20.2) to (20.3). In particular no
vanishing reset bound depending only on the fixed $\eta=1/2$ and $n$ can
hold for all legal lifts. $\square$

**Theorem 20.2 (An all-finite-iteration NPT witness).** The channel
$\Phi_\circ$ has infinite EB index, although its limiting channel is EB.

Proof. Let

$$
w=\frac{u-2v+z}{\sqrt6}\in T,
\qquad |\Omega_\circ\rangle=
\frac{|0\rangle_{\mathrm{ref}}s+|1\rangle_{\mathrm{ref}}w}{\sqrt2}.
\tag{20.5}
$$

The vectors $s,w$ are orthonormal. From (18.4),
$(U_0+U_1)w/2=-w/2$, while $U_js=s$. Therefore

$$
\Phi_\circ(|s\rangle\langle w|)=-\tfrac12|s\rangle\langle w|.
\tag{20.6}
$$

The sectors $\mathbb Cs,T$ are invariant under each restricted Kraus
operator. Consequently $A_n=\Phi_\circ^n(|w\rangle\langle w|)$ is a
density supported on $T$ for every $n\ge0$. Applying the $n$th iterate to
the system half of (20.5) gives, in reference blocks,

$$
\frac12\begin{pmatrix}
P&c_n|s\rangle\langle w|\\
c_n|w\rangle\langle s|&A_n
\end{pmatrix},\qquad c_n=(-1/2)^n.
\tag{20.7}
$$

After reference partial transpose, compress to the ordered pair
$(|1\rangle_{\mathrm{ref}}s,|0\rangle_{\mathrm{ref}}w)$. The compression is

$$
\begin{pmatrix}0&c_n/2\\c_n/2&0\end{pmatrix},\qquad
\det=-\frac{4^{-n}}4<0.
\tag{20.8}
$$

Both diagonal entries vanish because $A_n$ is supported on $T$ and $w\perp s$.
The compression has a negative eigenvalue $-2^{-n-1}$, so the full partial
transpose is not positive. This is an NPT witness for every finite $n$,
proved from the eigenoperator and invariant-sector identities rather than
from a finite list of powers. Definition 2.4 gives infinite EB index.
The EB limit is already (19.7); failure of finite EB is compatible with
convergence to it. $\square$

## 21. Exact codes restricted to the three-dimensional image

**Definition 21.1 (Restricted code dimension).** Let $d_R(n)$ be the largest
dimension of an exactly recoverable subspace contained in $R$ for
$\Phi_\circ^n$, with a terminal CPTP decoder on the full output system.
This restricts the initial encoding, not the decoder. It differs from the
full-space $k_n$ of Definition 2.3.

**Theorem 21.2 (The restricted sequence and its actual error operators).**
The restricted dimensions are

$$
d_R(0)=3,\qquad d_R(1)=2,\qquad d_R(n)=1\quad(n\ge2).
\tag{21.1}
$$

Proof. Rotate the two restricted Kraus operators $qU_0,qU_1$ by the
Hadamard matrix. The resulting Kraus pair for the same map $F$ is

$$
B_\circ=\frac{U_0+U_1}{2}
 =\begin{pmatrix}1/2&1/2&0\\0&0&1\\1/2&1/2&0\end{pmatrix},\qquad
C_\circ=\frac{U_0-U_1}{2}
 =\begin{pmatrix}1/2&-1/2&0\\0&0&0\\-1/2&1/2&0\end{pmatrix}.
\tag{21.2}
$$

Set $a_0=(u-v)/\sqrt2$, $P_a=|a_0\rangle\langle a_0|$, and $U=U_0$.
Multiplication gives

$$
C_\circ=UP_a,\qquad B_\circ=U(I_R-P_a),\qquad
F=\operatorname{Ad}_U\circ
\bigl[X\mapsto P_aXP_a+(I_R-P_a)X(I_R-P_a)\bigr].
\tag{21.3}
$$

Thus $a_0^\perp\cap R$ is a two-dimensional one-step isometric code. The
inverse isometry on its image, completed on the orthogonal complement by
resetting to a fixed unit vector of the code, is a full CPTP decoder by
(5.4). A three-dimensional code in $R$ would be all of $R$; it violates
Knill–Laflamme since $C_\circ^\dagger C_\circ=P_a$ is not scalar on $R$.
Hence $d_R(1)=2$.

For the two-step obstruction let $E_0=B_\circ,E_1=C_\circ$. The actual
Kraus errors of $F^2$ are $E_jE_i$ for $i,j\in\{0,1\}$. Write

$$
\mathscr S_2=\operatorname{span}_{\mathbb C}
\{(E_jE_i)^\dagger(E_\ell E_k):i,j,k,\ell\in\{0,1\}\}.
\tag{21.4}
$$

Completeness $\sum_jE_j^\dagger E_j=I_R$ gives

$$
\sum_j(E_jE_i)^\dagger(E_jE_k)=E_i^\dagger E_k,
\qquad
\sum_i(C_\circ E_i)^\dagger(C_\circ E_i)=F^\dagger(P_a).
\tag{21.5}
$$

Both are sums of genuine two-step error products. Therefore
$P_a\in\mathscr S_2$ and $F^\dagger(P_a)\in\mathscr S_2$; they are not
being inferred from unrelated observable data.

Put

$$
b_0=Ua_0=\frac{u-z}{\sqrt2},\qquad
c_0=\frac{2b_0-a_0}{\sqrt3},\qquad P_c=|c_0\rangle\langle c_0|.
\tag{21.6}
$$

Here $a_0,b_0\in T$, $\langle a_0,b_0\rangle=1/2$, and $(a_0,c_0)$ is
an orthonormal basis of $T$. Since $U=U^\dagger$, equation (21.3) gives

$$
\begin{aligned}
F^\dagger(P_a)
 &=P_aP_{b_0}P_a+(I_R-P_a)P_{b_0}(I_R-P_a)\\
 &=\tfrac14P_a+\tfrac34P_c.
\end{aligned}
\tag{21.7}
$$

It follows that $P_c\in\mathscr S_2$ too. In fact the actual system is

$$
\mathscr S_2=\operatorname{span}_{\mathbb C}
\{I_R,P_a,P_c,|a_0\rangle\langle c_0|,|c_0\rangle\langle a_0|\}
=\mathbb CP\oplus\mathcal B(T).
\tag{21.8}
$$

To verify the equality, put $J_0=I_R-P_a$, $J_1=P_a$, so the two
Kraus operators are $UJ_i$. Products of genuine two-step words give
$J_iU^\dagger J_jJ_lUJ_k$; they vanish for $j\ne l$. For $j=l=1$,
use $U^\dagger P_aU=P_{b_0}$ and
$b_0=a_0/2+\sqrt3\,c_0/2$. The four $i,k$ choices give respectively
nonzero multiples of $P_a,P_c,|a_0\rangle\langle c_0|$ and its adjoint.
For $j=l=0$, replace $P_{b_0}$ by $I_R-P_{b_0}$, which gives no
direction outside their span and $I_R$. The sum of all squared words
is $I_R$ by trace preservation, so this last direction also belongs
to the actual error system. Since $(s,a_0,c_0)$ is orthonormal, its
span is exactly the five-dimensional direct sum in (21.8).

For an exact code $C\subseteq R$,
Knill–Laflamme requires $P_CYP_C$ to be scalar on $C$ for every
$Y\in\mathscr S_2$ [Knill–Laflamme, Theorem 3.2, equations (19)–(20)][KL]. If
$\dim C\ge2$, a rank-at-most-one compression of either positive rank-one
projection $P_a,P_c$ can be scalar on $C$ only if it is zero. Zero
compression of a positive rank-one projection means that its vector is
orthogonal to every vector of $C$. Hence

$$
C\subseteq a_0^\perp\cap c_0^\perp\cap R=\mathbb Cs,
$$

a contradiction. This proves $d_R(2)=1$. Prefix monotonicity from
Definition 2.3, with the same restricted initial code, proves the remaining
entries. The value at zero is its definition. $\square$

**Convention 21.3 (Comparison with full-space exact codes).**
Theorem 10.2 gives the full-space class optima
$(K_0(\eta),K_1(\eta),K_2(\eta),K_3(\eta),\ldots)=(5,3,2,1,\ldots)$,
attained by its canonical lift. These are optima over full-space input codes.
Theorem 9.2 also says that the full-space $k_n(\Phi_\circ)$ equals one
for $n\ge3$, since this is an allowed interior lift. Theorem 21.2 concerns
encoding inside $R$ and makes no new classification of full-space codes at
steps one or two. Together with Theorem 20.2 it explicitly separates loss
of restricted exact qubit correction from finite-time NPT survival.

## 22. A CP reset lemma in the complete norm

**Lemma 22.1 (Reset minorization, including arbitrary references).** Let
$\Psi$ be a finite-dimensional CPTP map, let $m\ge1$, let $\tau$ be a
density matrix, and assume

$$
\Psi^m\ge_{\mathrm{CP}} a\mathcal R_\tau,\qquad 0<a\le1.
\tag{22.1}
$$

Use (17.1) with $M_5$ replaced by the input matrix algebra of this
lemma. Then $\Psi$ has a unique stationary density $\rho$, and

$$
\|\Psi^n-\mathcal R_\rho\|_\diamond
\le2(1-a)^{\lfloor n/m\rfloor}\qquad(n\ge0).
\tag{22.2}
$$

For $a=1$, the assertion means the bound two before step $m$ and exact
resetting thereafter. Neither $\tau$ nor $\rho$ is assumed faithful.

Proof. First, a CPTP map has diamond norm one on arbitrary complex inputs.
At every amplification, its adjoint is unital CP. The Schwarz inequality
for such a map $\Theta$ gives

$$
\Theta(Y)^\dagger\Theta(Y)
\le\Theta(Y^\dagger Y)\le\|Y\|_\infty^2 I.
\tag{22.3}
$$

For completeness the first inequality follows by applying
$\operatorname{id}_2\otimes\Theta$ to the positive block matrix
$\left(\begin{smallmatrix}Y^\dagger Y&Y^\dagger\\Y&I\end{smallmatrix}\right)$
and taking its Schur complement. Thus every amplified adjoint contracts
operator norm. Trace-norm duality proves complete trace-norm contraction
of the original channel. A density input attains norm one.

A stationary density exists by compactness: for any initial density,
the Cesàro averages of its first $N$ iterates have discrepancy under
$\Psi$ of trace norm at most $2/N$, and a convergent subsequence has a
stationary limit. If $a<1$, the normalized residual

$$
G=\frac{\Psi^m-a\mathcal R_\tau}{1-a}
\tag{22.4}
$$

is CP and TP. For two stationary densities their traceless difference $X$
satisfies $X=(1-a)G(X)$, whence
$\|X\|_1\le(1-a)\|X\|_1$ and $X=0$. This proves uniqueness.

To obtain a diamond estimate, let $D=\operatorname{id}-\mathcal R_\rho$.
The map $D$ is trace annihilating, as is $\Psi^jD$ for every $j\ge0$.
For every reference dimension and every complex input $Z$, the actual
cancellation is

$$
\operatorname{Tr}_{\mathrm{sys}}
[(\Psi^jD\otimes\operatorname{id})(Z)]=0.
\tag{22.5}
$$

Indeed the left side is the amplification of the zero functional
$\operatorname{Tr}\circ\Psi^jD$. Vanishing of the scalar total trace alone
would not imply (22.5). The amplification of the reset in (22.1) acts as
$Y\mapsto\tau\otimes\operatorname{Tr}_{\mathrm{sys}}Y$, so it annihilates
these outputs, including their reference correlations.

Write $n=qm+j$ with $0\le j<m$. A TP map preserves the zero system
partial-trace condition. Successively using (22.4) and (22.5), or doing
the same computation for trace-annihilating maps before amplification,
gives the exact identity

$$
\Psi^nD=(1-a)^qG^q\Psi^jD.
\tag{22.6}
$$

No commutation of $G$ with $\Psi$ is used. Since $\Psi^nD=\Psi^n-\mathcal R_\rho$
and all CPTP factors have diamond norm one,
$\|\Psi^jD\|_\diamond\le2$. This proves (22.2) uniformly over all finite
references and complex test matrices, without a spectral or Jordan-form
assumption.

If $a=1$, (22.1) and trace preservation force the positive residual to
have zero trace on every positive input, hence the residual vanishes and
$\Psi^m=\mathcal R_\tau$. Commuting $\Psi$ with its power gives
$\mathcal R_{\Psi(\tau)}=\mathcal R_\tau$, so $\Psi(\tau)=\tau$.
Every stationary density must equal $\tau$, and all powers from $m$ onward
are this reset. This proves the stated endpoint convention. $\square$

## 23. Primitive perturbations with an exact arbitrarily slow mode

**Definition 23.1 (The specified same-law perturbations).** Let
$\mathcal D$ be precisely the basis measure-and-prepare map (12.10) at
$\eta=1/2$:

$$
\mathcal D(X)=\sum_{i,j}(Q_{1/2})_{ij}X_{ii}P_j,\qquad
\Phi_\epsilon=(1-\epsilon)\Phi_\circ+\epsilon\mathcal D,
\qquad 0<\epsilon\le1.
\tag{23.1}
$$

Each $\Phi_\epsilon$ is one fixed homogeneous allowed lift. Its classical
matrix and its all-complex-input population law do not depend on $\epsilon$.

**Theorem 23.2 (Genuine CP-word minorization and quantum primitivity).**
For every $0<\epsilon\le1$, $\Phi_\epsilon$ is quantum primitive: its fourth
power sends every nonzero positive input to a positive definite output.
It has a unique stationary density $\rho_\epsilon$, which satisfies

$$
\rho_\epsilon\ge\frac{\epsilon^4}{8}I_5>0.
\tag{23.2}
$$

With $\tau=(P_0+2P_2+P_3)/4$, one has the CP-order bound and complete-norm
rate

$$
\begin{aligned}
\Phi_\epsilon^3&\ge_{\mathrm{CP}}
                  \frac{\epsilon^3}{2}\mathcal R_\tau,\\
\|\Phi_\epsilon^n-\mathcal R_{\rho_\epsilon}\|_\diamond
 &\le2\left(1-\frac{\epsilon^3}{2}\right)^{\lfloor n/3\rfloor}.
\end{aligned}
\tag{23.3}
$$

Proof. The specified classical map is CPTP, with Kraus operators
$\sqrt{Q_{ij}}|j\rangle\langle i|$ on the eight edges. Convexity preserves
both CPTP and the full linear law (2.2). Matrix multiplication at $\eta=1/2$
gives

$$
Q_{1/2}^3=\frac18\begin{pmatrix}
1&2&2&1&2\\1&2&2&1&2\\1&2&2&1&2\\2&0&4&2&0\\2&0&4&2&0
\end{pmatrix},\qquad
Q_{1/2}^4=\frac1{16}\begin{pmatrix}
3&2&6&3&2\\3&2&6&3&2\\3&2&6&3&2\\2&4&4&2&4\\2&4&4&2&4
\end{pmatrix}.
\tag{23.4}
$$

Expand $\Phi_\epsilon^m$ distributively into the ordered compositions of
$\Phi_\circ$ and $\mathcal D$. Each coefficient is nonnegative and each
composition is CP. Keeping the all-$\mathcal D$ word therefore proves

$$
\Phi_\epsilon^m\ge_{\mathrm{CP}}\epsilon^m\mathcal D^m.
\tag{23.5}
$$

This argument does not treat the two maps as commuting. Since every entry
of $Q_{1/2}^4$ is at least $1/8$, for $X\ge0$ it gives

$$
\Phi_\epsilon^4(X)\ge\epsilon^4\mathcal D^4(X)
\ge\frac{\epsilon^4}{8}\operatorname{Tr}(X)I_5.
\tag{23.6}
$$

For a nonzero positive $X$ its trace is positive, proving quantum
primitivity directly, rather than inferring it from classical primitivity.

For the stronger three-step reset estimate, every row of $Q_{1/2}^3$
dominates $x=(1,0,2,1,0)/8$, whose sum is $1/2$. The output-first Choi
matrix of $\mathcal D^3-(1/2)\mathcal R_\tau$ is

$$
\sum_{i,j}\bigl[(Q_{1/2}^3)_{ij}-x_j\bigr]P_j\otimes P_i\ge0.
\tag{23.7}
$$

Thus this is a CP-order inequality, not merely an inequality on selected
state outputs or a lower bound for a measurement probability. Combining
it with (23.5) at $m=3$ proves the first line of (23.3). Lemma 22.1 gives
the unique stationary density and the second line. The reset density
$\tau$ is not faithful, which is allowed by that lemma. Faithfulness of
$\rho_\epsilon$ follows separately by applying (23.6) to the stationary
density itself. This also proves (23.2), including $\epsilon=1$.
$\square$

**Theorem 23.3 (Exact mode and failure of a uniform rate at fixed parameter).**
For all $0<\epsilon\le1$,

$$
\Phi_\epsilon(\Delta_\circ)=(1-\epsilon)\Delta_\circ.
\tag{23.8}
$$

For every density $\sigma$ and every $n\ge1$,

$$
\|\Phi_\epsilon^n-\mathcal R_\sigma\|_\diamond
\ge(1-\epsilon)^n.
\tag{23.9}
$$

Although every member converges to its unique faithful reset, no bound
tending to zero with $n$ holds uniformly over this displayed primitive
family, all at the same $\eta=1/2$.

Proof. Theorem 18.1 gives $\Phi_\circ(\Delta_\circ)=\Delta_\circ$ and
$\operatorname{diag}\Delta_\circ=0$. The latter implies
$\mathcal D(\Delta_\circ)=0$, proving (23.8). Also
$\operatorname{Tr}\Delta_\circ=0$ and $\|\Delta_\circ\|_1=2$, so every
reset annihilates it. Iteration of (23.8) and evaluation of the diamond
norm on this nonzero test operator give (23.9).

For every fixed $\epsilon>0$ the upper bound (23.3) tends to zero. But
for every fixed $n\ge1$,

$$
\sup_{0<\epsilon\le1}
\|\Phi_\epsilon^n-\mathcal R_{\rho_\epsilon}\|_\diamond
\ge\sup_{0<\epsilon\le1}(1-\epsilon)^n=1.
\tag{23.10}
$$

These are different quantifier orders. Even the uniform fourth-step
positivity index in (23.6) does not give a uniform positive minorization
constant: that constant vanishes as $\epsilon\downarrow0$.
The limiting channel at $\epsilon=0$ is the nonrelaxing $\Phi_\circ$.
Compactness of the full closed legal Choi class cannot yield a vanishing
rate on a primitive subclass accumulating at this member. $\square$

**Theorem 23.4 (Positive dual effects do not imply CP resetting).** For
$\Phi_\circ$, every power has zero Hermitian-replacer Doeblin coefficient

$$
\alpha_{\mathrm H}(\Phi_\circ^n)=
\sup_{X=X^\dagger}
\{\operatorname{Tr}X:\mathcal R_X\le_{\mathrm{CP}}\Phi_\circ^n\}=0
\qquad(n\ge0).
\tag{23.11}
$$

In particular no positive multiple of any density reset is CP-dominated
by any power. Nevertheless its strictly positive third-step dual effect is

$$
(\Phi_\circ^\dagger)^3(P_2)=\tfrac14P_L+\tfrac12P_D>0.
\tag{23.12}
$$

Proof. Equation (23.12) is (4.9) at $\eta=1/2$. It guarantees a positive
probability for the computational outcome $2$ from every state after
three steps. It is an effect inequality, not an inequality of channels.

If $\Phi_\circ^n\ge_{\mathrm{CP}}a\mathcal R_\omega$ for a density
$\omega$ and $a>0$, apply the positive residual to $P,M$. Their fixedness
gives $P\ge a\omega$ and $M\ge a\omega$. A positive operator dominated
by two orthogonally supported positive operators has support in the
intersection of their supports, here zero. This contradicts
$\operatorname{Tr}(a\omega)=a>0$.

The coefficient (23.11) allows an arbitrary Hermitian $X$, not just
$X\ge0$. Its feasibility still implies $X\le P$ and $X\le M$. Decompose
$H=\mathbb Cs\oplus T\oplus R^\perp$. The compression of $X$ to
$\mathbb Cs$ is nonpositive using $X\le M$; its compression to $T$ is
nonpositive using $X\le P$; the same holds on $R^\perp$ using $X\le P$.
The trace is the sum of the traces of these three diagonal blocks,
regardless of its off-diagonal blocks. Hence $\operatorname{Tr}X\le0$.
The choice $X=0$ is feasible, proving equality in (23.11).

In the output-first convention (4.1), feasibility would require the full
Choi inequality $J_{\Phi_\circ^n}\ge X\otimes I_5$. Neither classical
$Q^4>0$ nor (23.12) supplies it. For the perturbed channels the corresponding
positive-density Choi inequality was established explicitly in (23.7).
$\square$

## 24. A selected all-parameter family and its spectral continuation

**Definition 24.1 (The selected family).** For $0<\eta<1$ put $r=1-\eta$ and

$$
u_\eta=\sqrt r\,|0\rangle+\sqrt\eta\,|3\rangle,\qquad
v_\eta=\sqrt r\,|1\rangle+\sqrt\eta\,|4\rangle,\qquad
R_\eta=\operatorname{span}\{u_\eta,v_\eta,z\}.
\tag{24.1}
$$

Define the following two full five-dimensional Kraus operators:

$$
\begin{aligned}
L_{\eta,0}
 &=\frac1{\sqrt2}\bigl[
 |u_\eta\rangle(\langle0|+\langle1|)
 +|z\rangle(\langle3|+\langle4|)\bigr]
 +|v_\eta\rangle\langle2|,\\
L_{\eta,1}
 &=\frac1{\sqrt2}\bigl[
 |u_\eta\rangle(\langle0|-\langle1|)
 +|z\rangle(-\langle3|+\langle4|)\bigr],\\
\mathcal B_\eta(X)
 &=L_{\eta,0}XL_{\eta,0}^\dagger
   +L_{\eta,1}XL_{\eta,1}^\dagger.
\end{aligned}
\tag{24.2}
$$

This definition selects a channel, not an additional constraint on the
other allowed lifts of §2.

**Theorem 24.2 (Legality and exact identification at the half parameter).**
Every $\mathcal B_\eta$ is allowed at its displayed parameter, has its entire
image supported on $R_\eta$, and obeys the original eight-edge support.
On the full five-dimensional input space, the Kraus pairs satisfy exactly

$$
\begin{pmatrix}L_{1/2,0}\\L_{1/2,1}\end{pmatrix}
=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}
\begin{pmatrix}K^\circ_0\\K^\circ_1\end{pmatrix}.
\tag{24.3}
$$

Consequently $\mathcal B_{1/2}=\Phi_\circ$, not just a channel with the
same populations or the same spectrum.

Proof. The three vectors $u_\eta,v_\eta,z$ are orthonormal. On the input
$\operatorname{span}\{|0\rangle,|1\rangle\}$ the two Kraus squared
products sum to

$$
\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}
+\frac12\begin{pmatrix}1&-1\\-1&1\end{pmatrix}=I_2.
$$

On $\operatorname{span}\{|3\rangle,|4\rangle\}$ the same identity holds
with the sign-reversed second vector; on $|2\rangle$ the sum is one.
Cross terms between these three input blocks vanish by orthogonality of
their output directions. Hence $\sum_j L_{\eta,j}^\dagger L_{\eta,j}=I_5$.
For every complex $X$, expanding (24.2) gives

$$
\operatorname{diag}\mathcal B_\eta(X)=
\begin{pmatrix}
r(X_{00}+X_{11})\\rX_{22}\\X_{33}+X_{44}\\
\eta(X_{00}+X_{11})\\\eta X_{22}
\end{pmatrix}.
\tag{24.4}
$$

The $X_{01},X_{10}$ terms and the $X_{34},X_{43}$ terms cancel between
the two Kraus summands. Operators between the three disjoint output supports
have zero diagonal. Thus (24.4) is exactly (2.2) on the full complex algebra.

For a direct realization within (4.4), take orthonormal $f_0,f_1$, let
$f_\pm=(f_0\pm f_1)/\sqrt2$, and choose

$$
\alpha_0=\beta_0=f_+,\quad
\alpha_1=\beta_1=f_-,\quad
\gamma_0=\gamma_1=f_0,\quad
\delta_0=f_-,\quad\delta_1=f_+.
\tag{24.5}
$$

All three prescribed orthogonalities hold, and these actual vectors have
a PSD common Gram matrix. Every nonzero Kraus entry is one of the original
eight edges. Finally substitution of (17.3) into the right side of (24.3)
gives (24.2) entry by entry at $\eta=1/2$. The matrix performing this
rotation is unitary; expanding the sum of the two Kraus outputs cancels
its cross terms. This proves equality of the channels on every complex
input. $\square$

**Theorem 24.3 (Invariant blocks and the full characteristic
polynomial).** Put

$$
a=\sqrt{r/2},\qquad c=\sqrt{\eta/2},\qquad
b=2\sqrt{r\eta}=4ac,
\qquad
\mu_\pm=\frac{c\pm\sqrt{c^2+8rc}}2.
\tag{24.6}
$$

The characteristic polynomial on the full $M_5$ is

$$
\chi_{\mathcal B_\eta}(t)
=t^{20}(t-1)(t+\eta)(t+c)(t^2-ct-2rc).
\tag{24.7}
$$

Proof. Let $F_\eta$ be the restriction to $\mathcal B(R_\eta)$. In its
ordered orthonormal basis $(u_\eta,v_\eta,z)$ the actual Kraus matrices are

$$
B_\eta=\begin{pmatrix}a&a&0\\0&0&1\\c&c&0\end{pmatrix},\qquad
C_\eta=\begin{pmatrix}a&-a&0\\0&0&0\\-c&c&0\end{pmatrix}.
\tag{24.8}
$$

They follow, for example, by applying $L_{\eta,j}$ to each of the three
basis vectors. To derive every invariant block without assuming Hermiticity,
write $Y=(y_{ij})\in M_3(\mathbb C)$. Multiplication of these two Kraus
matrices gives

$$
F_\eta(Y)=\begin{pmatrix}
r(y_{00}+y_{11})&a(y_{02}+y_{12})&\sqrt{r\eta}(y_{01}+y_{10})\\
a(y_{20}+y_{21})&y_{22}&c(y_{20}+y_{21})\\
\sqrt{r\eta}(y_{01}+y_{10})&c(y_{02}+y_{12})&\eta(y_{00}+y_{11})
\end{pmatrix}.
\tag{24.9}
$$

Thus the three complex subspaces of (19.2), now in this parameter-dependent
basis, are invariant. Their representing matrices are

$$
D_\eta=\begin{pmatrix}r&r&0\\0&0&1\\\eta&\eta&0\end{pmatrix},\qquad
S_\eta=\begin{pmatrix}0&a&a\\b&0&0\\0&c&c\end{pmatrix},\qquad
A_\eta=\begin{pmatrix}0&a&a\\0&0&0\\0&-c&-c\end{pmatrix}.
\tag{24.10}
$$

For instance the symmetric coordinates $(x,y,w)$ on positions
$(01,02,12)$ map to $(a(y+w),bx,c(y+w))$; the antisymmetric coordinates
map to $(a(y+w),0,-c(y+w))$. These formulas also explain why splitting
only into real Hermitian inputs is unnecessary.

Expanding the three determinants gives

$$
\begin{aligned}
\det(tI-D_\eta)&=t(t^2-rt-\eta)=t(t-1)(t+\eta),\\
\det(tI-S_\eta)&=t(t^2-ct-ab)=t(t^2-ct-2rc),\\
\det(tI-A_\eta)&=t^2(t+c).
\end{aligned}
\tag{24.11}
$$

The second equality uses $ab=2rc$, not an independent parameter
assumption. The nine-dimensional restricted characteristic polynomial is
the product of these three polynomials. Every full-space output lies in
$\mathcal B(R_\eta)$, so the map induced on the sixteen-dimensional
quotient is zero. Multiplying by $t^{16}$ proves (24.7). At $\eta=1/2$,
$a=c=1/2$, $b=1$, and $\mu_+=1$, $\mu_-=-1/2$. This reduces precisely
to (19.1), in agreement with the full Kraus identification (24.3).
$\square$

**Theorem 24.4 (Unique rank-three stationary density away from the half
parameter).** For $0<\eta<1$ and $\eta\ne1/2$, the selected channel
$\mathcal B_\eta$ has the unique stationary density

$$
\rho_\eta=\frac{rP_{u_\eta}+\eta P_{v_\eta}+\eta P_z}{1+\eta},
\qquad
\mathcal B_\eta^n\longrightarrow\mathcal R_{\rho_\eta}
\quad\text{in diamond norm}.
\tag{24.12}
$$

Its computational diagonal is the classical stationary vector (3.2).
It is faithful on $R_\eta$ and has rank three on $H$, so it is not faithful
on $H$ and the channel is not quantum primitive on $M_5$.

Proof. The three positive weights in (24.12) sum to one. Its diagonal in
the $R_\eta$ basis is $(r,\eta,\eta)/(1+\eta)$, which $D_\eta$ fixes by
direct multiplication. Equation (24.9) gives no off-diagonal output from
this input. This verifies stationarity on the full system. Squaring the
coordinates of $u_\eta,v_\eta,z$ gives the five populations
$(r^2,\eta r,\eta,\eta r,\eta^2)/(1+\eta)$.

The two roots $\mu_\pm$ have opposite signs, and

$$
|\mu_-|<\mu_+,\qquad c<\mu_+.
\tag{24.13}
$$

Indeed their sum is $c>0$ and their product is $-2rc<0$; the positive
root is strictly greater than $c$. To locate this root relative to one,
put $\zeta=\sqrt{2\eta}$, so $c=\zeta/2$. Then

$$
(1-\mu_+)(1-\mu_-)
=1-c-2rc
=\frac{(\zeta-1)^2(\zeta+2)}2.
\tag{24.14}
$$

Since $\mu_-<0$, the other factor on the left is positive. Therefore
$\mu_+\le1$, with equality exactly at $\eta=1/2$. Away from that parameter,
all eigenvalues in (24.7) other than the simple eigenvalue one have
modulus strictly less than one: also $\eta<1$ and $c<1$.

The simple eigenvalue one has no nontrivial Jordan block. A
finite-dimensional Jordan decomposition therefore shows convergence of
powers to its spectral projection; every other block decays, including
any nilpotent transient. Its range is the one-dimensional fixed space
spanned by the displayed density. Trace preservation fixes the coefficient
of this projection to $\operatorname{Tr}X$, so the limit is its reset.
All norms on this finite-dimensional space of maps are equivalent,
including the diamond norm, proving the asserted convergence.
Finally every output lies in a three-dimensional proper subspace of $H$;
no power can have strictly positive outputs on all of $H$. $\square$

**Theorem 24.5 (Exact asymptotic exponent and quadratic gap closure).** For
$0<\eta<1$, $\eta\ne1/2$, set
$\varrho(\eta)=\max\{\eta,\mu_+(\eta)\}$. Then

$$
\begin{aligned}
\lim_{n\to\infty}
\|\mathcal B_\eta^n-\mathcal R_{\rho_\eta}\|_\diamond^{1/n}
 &=\varrho(\eta),\\
\lim_{n\to\infty}-\frac1n\log
\|\mathcal B_\eta^n-\mathcal R_{\rho_\eta}\|_\diamond
 &=-\log\varrho(\eta).
\end{aligned}
\tag{24.15}
$$

The selected coherence mode satisfies the exact formula

$$
1-\mu_+(\eta)=
\frac{(\sqrt{2\eta}-1)^2(\sqrt{2\eta}+2)}{2(1-\mu_-(\eta))},
\qquad
1-\mu_+(\eta)\sim(\eta-1/2)^2.
\tag{24.16}
$$

Consequently the full selected-family gap $1-\varrho(\eta)$ and its
exponential decay exponent $-\log\varrho(\eta)$ both have the same
quadratic asymptotic as $\eta\to1/2$, $\eta\ne1/2$.

Proof. Let $N=\mathcal B_\eta-\mathcal R_{\rho_\eta}$. Stationarity and
trace preservation give
$\mathcal B_\eta\mathcal R_{\rho_\eta}
=\mathcal R_{\rho_\eta}\mathcal B_\eta
=\mathcal R_{\rho_\eta}^2=\mathcal R_{\rho_\eta}$.
Thus $N^n=\mathcal B_\eta^n-\mathcal R_{\rho_\eta}$ for $n\ge1$.
On the decomposition into the stationary line and the traceless complex
operators, $N$ is zero on the former and equals $\mathcal B_\eta$ on
the latter. Its spectrum is therefore (24.7)'s nonstationary spectrum
together with zero. Equation (24.13) shows that its spectral radius is
exactly $\varrho(\eta)>0$.

A nonzero eigenoperator with eigenvalue of maximal modulus yields
$\|N^n\|_\diamond\ge\varrho(\eta)^n$ by testing its trace norm. Conversely,
a finite Jordan block of size $k$ contributes a polynomial of degree at
most $k-1$ times its eigenvalue to the $n$th power. Hence for every
$h>0$ there is a finite constant $C_h$, at this fixed parameter, such that
$\|N^n\|_\diamond\le C_h(\varrho(\eta)+h)^n$; nilpotent blocks vanish
once $n$ is large enough. Taking $n$th roots and then $h\downarrow0$
proves the first limit, and taking logarithms proves the second. This is
an asymptotic statement, not a uniform finite-$n$ prefactor estimate.

Dividing (24.14) by $1-\mu_-$ gives the exact expression in (24.16).
Writing $\delta=\eta-1/2$,

$$
\frac{\sqrt{2\eta}-1}{\delta}=
\frac2{\sqrt{2\eta}+1}\longrightarrow1,
\qquad
\mu_-\longrightarrow-1/2.
$$

The remaining factor in (24.16) tends to $3/[2(3/2)]=1$, proving the
quadratic asymptotic. At the half parameter, $\mu_+=1>\eta=1/2$;
continuity implies $\varrho=\mu_+$ throughout a neighborhood of it.
Finally $-\log x\sim1-x$ as $x\uparrow1$, proving the last assertion.
None of these selected-family conclusions decides the spectrum or
relaxation of other allowed lifts at any other fixed interior parameter.
$\square$

**Theorem 24.6 (Complete Jordan structure and the stationary-dimension
change).** For every $0<\eta<1$, the full map $\mathcal B_\eta$ has
exactly four zero Jordan blocks of size two and twelve zero blocks of
size one. Every nonzero Jordan block has size one, including at
$\eta=1/2$. Thus that parameter changes the stationary-space dimension
from one to two; it is not a defective nonzero exceptional point.

Proof. Each of $D_\eta$ and $S_\eta$ in (24.10) has three distinct
roots in the interior: respectively $0,1,-\eta$ and $0,\mu_+,\mu_-$.
They are diagonalizable. Directly
$A_\eta^2=-cA_\eta$ with $c>0$, so its two-dimensional zero eigenspace
is semisimple too. The three blocks have ranks $2,2,1$. Their invariant
direct sum therefore makes $F_\eta$ diagonalizable, even when roots in
different blocks coincide, and
$\operatorname{rank}F_\eta^l=5$ for every $l\ge1$.

To determine the full transient, let $W_\eta=(u_\eta,v_\eta,z)$ and
write $L_{\eta,j}=W_\eta T_j$, where

$$
T_0=\begin{pmatrix}
1/\sqrt2&1/\sqrt2&0&0&0\\
0&0&1&0&0\\
0&0&0&1/\sqrt2&1/\sqrt2
\end{pmatrix},\qquad
T_1=\begin{pmatrix}
1/\sqrt2&-1/\sqrt2&0&0&0\\
0&0&0&0&0\\
0&0&0&-1/\sqrt2&1/\sqrt2
\end{pmatrix}.
\tag{24.17}
$$

Define $\Theta(X)=\sum_jT_jXT_j^\dagger$ and
$\iota_\eta(Y)=W_\eta YW_\eta^\dagger$. Then
$\mathcal B_\eta=\iota_\eta\Theta$,
$F_\eta=\Theta\iota_\eta$, and $\iota_\eta$ is injective.
The map $\Theta:M_5\to M_3$ is surjective. In the order
$(00,01,02,10,11,12,20,21,22)$ of the target matrix units, explicit
preimages, written in the original five-dimensional matrix units, are

$$
E_{00},\ \sqrt2E_{02},\ E_{04},\ \sqrt2E_{20},\ E_{22},\
\sqrt2E_{23},\ E_{40},\ \sqrt2E_{32},\ E_{33}.
\tag{24.18}
$$

Substitution in (24.17) verifies each preimage. Hence

$$
\mathcal B_\eta^n=\iota_\eta F_\eta^{n-1}\Theta\quad(n\ge1),
\qquad
\operatorname{rank}\mathcal B_\eta=9,\quad
\operatorname{rank}\mathcal B_\eta^n=5\quad(n\ge2).
\tag{24.19}
$$

By (24.7), the zero algebraic multiplicity is twenty. Its geometric
multiplicity is $25-9=16$. Equality of the ranks of the square and cube
excludes zero Jordan blocks of size three or larger. If $b_1,b_2$ count
the remaining sizes, then $b_1+b_2=16$ and $b_1+2b_2=20$; thus
$b_2=4$, $b_1=12$. The zero transient vanishes after squaring.
For a nonzero eigenvalue, the full generalized eigenspace lies in the
one-step image: the map is invertible on that generalized eigenspace,
so every vector there is itself an image. That image is precisely
$\mathcal B(R_\eta)$, where $F_\eta$ is diagonalizable. This proves
semisimplicity of all nonzero modes.

In particular for $\eta\ne1/2$ the estimate in Theorem 24.5 can be
written, after the transient, as

$$
\mathcal B_\eta^n-\mathcal R_{\rho_\eta}
=\sum_{\lambda\ne0,1}\lambda^n\mathcal P_\lambda,
\qquad
\|\mathcal B_\eta^n-\mathcal R_{\rho_\eta}\|_\diamond
\le C_\eta\varrho(\eta)^n\quad(n\ge2),
\tag{24.20}
$$

where the sum runs over distinct nonzero decaying eigenvalues,
$\mathcal P_\lambda$ are their full spectral projections, and
$C_\eta=\sum_{\lambda\ne0,1}\|\mathcal P_\lambda\|_\diamond<\infty$.
This constant concerns this fixed selected channel and is not asserted
uniform over parameters or over lifts. At $1/2$, both the double
stationary eigenvalue and the triple eigenvalue $-1/2$ remain semisimple;
the limit and transient are exactly Theorem 19.2's full-input channel,
including its pulled-back effect $E$. $\square$

**Corollary 24.7 (Unit activity in the selected family).** At source
activity $\lambda=1$, the interface $\lambda=\eta/(1-\eta)^2$ gives

$$
\eta=\frac{3-\sqrt5}{2},\qquad
r=\frac{\sqrt5-1}{2},\qquad
\mu_+=\frac{r\bigl(1+\sqrt{1+8\sqrt2}\bigr)}{2\sqrt2}
\simeq0.98527216428273156.
\tag{24.21}
$$

For this selected family the exponent base in (24.15) is $\mu_+$.

Proof. The admissible root of $\eta=(1-\eta)^2$ is the displayed
$\eta=r^2$. Thus $c=r/\sqrt2$. Substitution in (24.6) gives the exact
radical in (24.21). Moreover $r>1/2$ and
$(1+\sqrt{1+8\sqrt2})/(2\sqrt2)>1$, so $\mu_+>r>r^2=\eta$.
Theorem 24.5 now identifies the exponent base. The decimal is an
approximation of that radical; the proof and the rate use its exact
value. This example specifies no rate for other lifts at unit activity.
$\square$

## 25. Universal population information and the infinite-activity cycle

**Proposition 25.1 (The classical mode is a necessary rate obstruction).**
The population matrix has

$$
\det(tI-Q_\eta)=t^3(t-1)(t+\eta).
\tag{25.1}
$$

For every allowed lift at $0<\eta<1$, every density $\sigma$, and every
$n\ge0$,

$$
\|\Phi^n-\mathcal R_\sigma\|_\diamond\ge\eta^n.
\tag{25.2}
$$

This necessary lower bound supplies no uniqueness or convergence assertion.

Proof. The image of $Q_\eta$ on column functions lies in the subspace
$f_0=f_1$, $f_3=f_4$. In coordinates $f=(a,a,b,c,c)$ its restriction is

$$
\begin{pmatrix}r&0&\eta\\r&0&\eta\\0&1&0\end{pmatrix},
$$

whose determinant polynomial is $t(t^2-rt-\eta)=t(t-1)(t+\eta)$.
The quotient has dimension two and induced map zero, giving (25.1).
The all-input law also makes the adjoint's diagonal algebra invariant,
with action $Q_\eta$, so $-\eta$ is genuinely in every lift's spectrum.
For a direct norm bound use the explicit real column

$$
a_\eta=(r^2,-r,\eta,\eta r,-\eta)^{\mathsf T}.
\tag{25.3}
$$

It satisfies $Q_\eta^{\mathsf T}a_\eta=-\eta a_\eta$,
$\sum_i(a_\eta)_i=0$, and $\|a_\eta\|_1=2$: its positive entries sum
to $r^2+\eta+\eta r=1$ and the absolute values of its negative entries
sum to $r+\eta=1$. Iterating (2.2) on $\operatorname{diag}(a_\eta)$ gives
output diagonal $(-\eta)^na_\eta$. Computational pinching is CPTP and
trace-norm contractive; every reset annihilates this traceless input.
Testing the channel difference on it and dividing by its norm two proves
(25.2). The hidden fixed direction $\Delta_\circ$ at the half parameter
has zero diagonal, so the population calculation cannot exclude it.
$\square$

**Theorem 25.2 (Every infinite-activity endpoint lift has a population
cycle).** In the endpoint class of Definition 15.1 at $\eta=1$, every
allowed lift satisfies

$$
\Phi(P_2)=P_4,\qquad\Phi(P_4)=P_2.
\tag{25.4}
$$

Thus no such lift converges to a single reset, and for every density
$\sigma$ and every $n\ge0$ its reset distance is at least one.

Proof. The endpoint all-input law prescribes the output diagonal of $P_2$
to be concentrated at $4$, and that of $P_4$ to be concentrated at $2$.
A positive trace-one matrix with a single nonzero diagonal entry must be
the corresponding basis projector: positivity gives
$|X_{ij}|^2\le X_{ii}X_{jj}$ and annihilates every other row and column.
This proves (25.4) for every lift, without assigning any particular Kraus
representation. Iteration swaps the two orthogonal projectors at odd
steps and fixes them at even steps. Their output trace distance remains
two. The triangle argument of Theorem 20.1 gives the lower bound one
for every reset, even if chosen separately at each step.

More generally, for an arbitrary initial density let
$l=\operatorname{Tr}(P_L\rho)$ and $h=\operatorname{Tr}(P_D\rho)$.
The deterministic endpoint transitions send each of $0,1,2$ to $2$
after two steps and each of $3,4$ to $4$. Thus for every endpoint lift

$$
\operatorname{diag}\Phi^n(\rho)=
\begin{cases}
l\,\operatorname{diag}P_2+h\,\operatorname{diag}P_4,
   &n\ge2\text{ even},\\
h\,\operatorname{diag}P_2+l\,\operatorname{diag}P_4,
   &n\ge3\text{ odd}.
\end{cases}
\tag{25.5}
$$

Equivalently $Q_1^4=Q_1^2$ and $Q_1^{n+2}=Q_1^n$ for $n\ge2$.
Equal weights give period one; otherwise these populations have period
two. The transient prevents $Q_1^3=Q_1$: for example the input $0$ has
first-step population at $3$ and third-step population at $4$.
These formulas do not prescribe periodicity of arbitrary quantum
coherences or an exact swap qubit for every lift. $\square$

**Convention 25.3 (Reuse of the endpoint results).** The universal
third-step reset at $\eta=0$ and the endpoint exact-code optima and swap-code
construction at $\eta=1$ remain Theorems 15.2–15.3, with their stated
source interpretation in Convention 15.4. They are not reproved or
reclassified here. The all-lift cycle (25.4) concerns populations;
it does not say that every endpoint lift preserves the swap qubit of the
particular construction in Theorem 15.3.

## 26. Primary literature, ownership, and boundaries of the extension

**Convention 26.1 (Source ownership and mathematical status).** The
classical source-to-window interface and its hypotheses remain those of
§3 and the owning references in Convention 16.1. In particular the
fixed finite-activity Perron law is owned by [LocalClock, Proposition
15.8][LC], and the distinction between a stationary local marginal and
a selected extension remains that of [Pyramid, §§17–18][PY]. The
all-complex-input CPTP class is the added quantum modeling choice of
Definition 2.2. The half-parameter counterexample corresponds to
$\lambda=\eta/(1-\eta)^2=2$ in that chosen source interface, but the
classical law does not choose its Kraus operators or its environment.

The explicit Gram realization, fixed-state family, conserved effect,
full-space polynomial, limit, complete-norm distances, NPT witness,
restricted-code calculation, and quantitative perturbation identities
above are model-specific ordinary derivations. Section 24 gives full
ordinary proofs for the displayed selected family, including its
exact identification with the half-parameter channel; it is not an
all-lift theorem away from that parameter. None of these descriptions
asserts an exhaustive literature novelty determination.

**Convention 26.2 (Primary references and exact conditions).** The standard
Choi, Stinespring, Knill–Laflamme, and EB interfaces remain the primary
sources and versions listed in Convention 16.2. In particular the
restricted code uses [Knill–Laflamme, quant-ph/9604034v1, Theorem 3.2, equations
(19)–(20)][KL], and the limit's measure-and-prepare form uses [Horodecki–Shor–Ruskai,
quant-ph/0302031v2, Theorem 4][HSR]. The following additional primary references
locate the distinctions needed for this extension.

| Primary source and version | Interface and conditions |
| --- | --- |
| D. Burgarth, G. Chiribella, V. Giovannetti, P. Perinotti, and K. Yuasa, *Ergodic and Mixing Quantum Channels in Finite Dimensions*, [arXiv:1210.5625v3][MIX17], Theorem 1, Corollary 4, and Theorem 9 | Theorem 1 characterizes a unique stationary state by the absence of two disjoint nonzero invariant subspaces, without assuming a faithful stationary state. Corollary 4 characterizes mixing by the identity, up to scalar, being the only adjoint peripheral eigenvector. Theorem 9's peripheral Kraus description assumes both ergodicity and a faithful fixed state. The sectors $\mathbb Cs,T$ and the nontrivial conserved effect $E$ explicitly obstruct the first two properties for $\Phi_\circ$; Theorem 9's hypotheses cannot be supplied by $Q^4>0$. |
| M. Sanz, D. Pérez-García, M. M. Wolf, and J. I. Cirac, *A quantum version of Wielandt's inequality*, [arXiv:0909.5347v2][WIE17], definition of primitivity, Proposition 3, and Theorem 1 | Quantum primitivity requires a power that makes every nonzero positive input positive definite. Proposition 3 relates it to eventual full Kraus rank and the unique-faithful-state peripheral criterion. Theorem 1 assumes this quantum property before bounding a length. Inequality (23.6) proves the needed property for the specified perturbations. Classical primitivity alone does not do so, and a bounded positivity index does not supply a uniform minorization constant. |
| I. George, C. Hirche, T. Nuradha, and M. M. Wilde, *Quantum Doeblin Coefficients: Interpretations and Applications*, [arXiv:2503.22823v3][DOE17], Definition 4, equations (3.1)–(3.2), and §6, Proposition 30 | The Hermitian-replacer coefficient optimizes $\operatorname{Tr}X$ subject to a CP-order inequality and permits Hermitian $X$ of either sign. In that paper's input-first convention the Choi inequality is $I_{\mathrm{in}}\otimes X\le J$; here it is $X\otimes I_{\mathrm{in}}\le J$ by the tensor swap in (4.1). The complete trace-distance contraction comparison in equations (6.15)–(6.16) uses referenced state pairs with equal reference marginals. Lemma 22.1 proves the sufficient positive-density minorization implication directly and enforces the requisite system partial-trace cancellation on arbitrary complex inputs. Theorem 23.4 separately proves that the broader Hermitian coefficient is zero for every unperturbed power. |

These references supply standard frameworks with their hypotheses. The
particular five-state matrices and all-$n$ identities are established by
the displayed calculations, not attributed to a general theorem about
all lifts of a classical primitive matrix.

**Convention 26.3 (Exact boundary of the conclusions).** The unperturbed
half-parameter lift disproves universal reset relaxation within the
stated model and preserves a terminal classical label. The specified
primitive perturbations each converge to a unique faithful reset but
admit no common vanishing rate, even at the same fixed parameter. The
selected family has exactly the spectrum, stationary density, and
asymptotic exponents of §24; no classification of all other lifts at
other interior parameters follows. Loss of an exact qubit code, NPT at
every finite step, convergence to an EB limit, and convergence to a
single reset are distinct properties with distinct conclusions above.

The all-lift positive-interval result and its separate proof follow in
§§27–31. All these statements are ordinary finite-dimensional mathematics under
Convention 1.2. They do not establish a physical realization, native
complete-window update, Hamiltonian or field theory, an asymptotic
capacity formula, a priority claim, or Lean/kernel certification. The selected-family calculation
does not classify the behavior of all lifts at the remaining interior
parameters.

[MIX17]: https://arxiv.org/abs/1210.5625v3
[WIE17]: https://arxiv.org/abs/0909.5347v2
[DOE17]: https://arxiv.org/abs/2503.22823v3

## 27. Rank-one population caps, including all mixed states

**Convention 27.1 (Dimension, norms, and the new implication).** In §§27–28,
let $d\ge2$ be finite, let $j\in\mathbb C^d$ be a unit vector, and put
$P_j=|j\rangle\langle j|$. Trace and diamond norms are unhalved, as in
(17.1). These sections prove a sufficient mixing criterion from a uniformly
heavy rank-one output population. Sections 29–30 derive that criterion from
the all-complex-input law (2.2) on an explicit interval. The stationary density
is allowed to depend on the chosen lift. All powers still mean one fixed
homogeneous channel with fresh discarded environments, under Convention 1.2.

**Lemma 27.2 (A population-preserving pure-state decomposition).** Every
density $\rho$ is a finite convex combination of pure states, each with the
same $P_j$-population $\operatorname{Tr}(P_j\rho)$ as $\rho$.

Proof. Induct on the rank $s$ of $\rho$. Rank one is immediate. For
$s\ge2$, let $S$ be its support. Hermitian operators supported on $S$ form
a real vector space of dimension $s^2$. The two real linear constraints

$$
\operatorname{Tr}H=0,\qquad \operatorname{Tr}(P_jH)=0
\tag{27.1}
$$

have a nonzero solution there, since $s^2>2$. The restriction of $\rho$ to
$S$ is positive definite, so $\rho+tH\ge0$ for all sufficiently small
positive and negative real $t$. A nonzero traceless Hermitian $H$ has both
a positive and a negative eigenvalue. Evaluating quadratic forms on their
eigenvectors bounds the feasible $t$-interval in both directions. This
closed interval therefore has finite endpoints $t_-<0<t_+$. At either
endpoint the rank drops: otherwise positive definiteness on $S$ would
permit a further small extension. Both endpoint matrices are densities
with the original population, and

$$
\rho=\frac{t_+}{t_+-t_-}(\rho+t_-H)
     +\frac{-t_-}{t_+-t_-}(\rho+t_+H).
\tag{27.2}
$$

The coefficients are positive and sum to one. Apply the induction
hypothesis to both endpoint matrices. The rank decreases along every
branch, so this yields a finite decomposition with the required exact
population. An arbitrary spectral decomposition would not by itself
ensure that property. $\square$

**Theorem 27.3 (Exact unhalved diameter of a rank-one cap).** For
$1/2<a\le1$ let

$$
\mathcal C_a=\{\rho\ge0:\operatorname{Tr}\rho=1,
                         \operatorname{Tr}(P_j\rho)\ge a\}.
$$

Then

$$
\max_{\rho,\sigma\in\mathcal C_a}\|\rho-\sigma\|_1
=4\sqrt{a(1-a)}.
\tag{27.3}
$$

Proof. First consider unit vectors $u,v$ with populations $p,q\ge a$.
Choose global phases so that their $j$-coordinates are $\sqrt p,\sqrt q$,
and write $u=\sqrt p\,j+u_\perp$, $v=\sqrt q\,j+v_\perp$. The reverse
triangle inequality and Cauchy–Schwarz give

$$
|\langle u,v\rangle|
\ge\sqrt{pq}-\sqrt{(1-p)(1-q)}
\ge a-(1-a)=2a-1.
\tag{27.4}
$$

The Hermitian difference $P_u-P_v$ is traceless, has rank at most two,
and has squared Hilbert–Schmidt norm $2(1-|\langle u,v\rangle|^2)$.
Its possible nonzero eigenvalues are therefore
$\pm\sqrt{1-|\langle u,v\rangle|^2}$. Consequently

$$
\|P_u-P_v\|_1
=2\sqrt{1-|\langle u,v\rangle|^2}
\le4\sqrt{a(1-a)}.
\tag{27.5}
$$

For arbitrary mixed $\rho,\sigma\in\mathcal C_a$, Lemma 27.2 provides
$\rho=\sum_s\lambda_sP_{u_s}$ and $\sigma=\sum_t\nu_tP_{v_t}$,
with every pure term still in the cap. Thus

$$
\rho-\sigma=\sum_{s,t}\lambda_s\nu_t(P_{u_s}-P_{v_t}),
$$

and the triangle inequality proves (27.3)'s upper bound for all mixed
states. A unit $k\perp j$ exists because $d\ge2$. The two unit vectors
$\sqrt a\,j\pm\sqrt{1-a}\,k$ have population $a$, overlap $2a-1$,
and attain equality in (27.5). At $a=1$ the cap is the singleton $\{P_j\}$,
so the same formula gives zero. $\square$

**Proposition 27.4 (Limits of the cap information).** For $0\le a\le1/2$
and $d\ge2$, the same cap has diameter two. A projection of rank at least
two permits diameter two even when its required population is one.

Proof. For the first assertion, $(j+k)/\sqrt2$ and $(j-k)/\sqrt2$ are
orthogonal unit vectors in the cap. Orthogonal pure states have unhalved
trace norm distance two, the maximum possible for densities. For the
second assertion, use two orthogonal unit vectors in the projection's
range. In dimension one the rank-one cap has diameter zero; for $a>1$
it is empty. If distance is defined as half the trace norm, the value in
(27.3) is instead $2\sqrt{a(1-a)}$. $\square$

## 28. Heavy population implies complete forgetting

**Theorem 28.1 (Lipschitz contraction and a unique stationary density).**
Let $\Psi:M_d(\mathbb C)\to M_d(\mathbb C)$ be CPTP, let $N\ge1$ be an
integer, and suppose

$$
\operatorname{Tr}(P_j\Psi^N(\rho))\ge a
\quad\text{for every density }\rho,\qquad 1/2<a<1.
\tag{28.1}
$$

Put $\kappa=2\sqrt{a(1-a)}<1$. Then $\Psi$ has a unique stationary
density $\rho_*$ and, for every traceless Hermitian $Y$ and every $n\ge0$,

$$
\|\Psi^n(Y)\|_1\le\kappa^{\lfloor n/N\rfloor}\|Y\|_1.
\tag{28.2}
$$

In particular
$\|\Psi^n(\rho)-\rho_*\|_1\le2\kappa^{\lfloor n/N\rfloor}$ for every
density $\rho$. No faithful-stationary-state hypothesis is imposed.

Proof. Set $\Gamma=\Psi^N$. For nonzero traceless Hermitian $Y$, its
positive and negative parts satisfy

$$
Y=Y_+-Y_-,\qquad
\operatorname{Tr}Y_+=\operatorname{Tr}Y_-=t=\|Y\|_1/2.
$$

The densities $\rho_\pm=Y_\pm/t$ have outputs in $\mathcal C_a$.
Theorem 27.3 gives

$$
\|\Gamma(Y)\|_1
=t\|\Gamma(\rho_+)-\Gamma(\rho_-)\|_1
\le4t\sqrt{a(1-a)}=\kappa\|Y\|_1.
\tag{28.3}
$$

The zero case is immediate. Applying this to $Y=\rho-\sigma$ proves a
Lipschitz inequality on the entire state space. This scaling argument is
needed: an absolute diameter bound between outputs alone is not a
Lipschitz estimate relative to the input distance.

The density matrices form a complete metric space in trace norm.
The Banach contraction theorem applied to $\Gamma$ gives its unique fixed
density $\rho_*$. Commutation of $\Psi$ with its power implies

$$
\Gamma(\Psi(\rho_*))=\Psi(\Gamma(\rho_*))=\Psi(\rho_*).
$$

Thus $\Psi(\rho_*)=\rho_*$ by uniqueness for $\Gamma$. Every
$\Psi$-stationary density is $\Gamma$-fixed, proving uniqueness for
$\Psi$ as well.

For a positive TP map $\Lambda$ and Hermitian $H=H_+-H_-$,

$$
\|\Lambda(H)\|_1
\le\operatorname{Tr}\Lambda(H_+)+\operatorname{Tr}\Lambda(H_-)
=\|H\|_1.
\tag{28.4}
$$

Write $n=qN+r_0$ with $0\le r_0<N$. Iterate (28.3) $q$ times and
apply (28.4) to the remaining $\Psi^{r_0}$. This proves (28.2).
Apply it to $\rho-\rho_*$, of norm at most two, to obtain the state
bound. $\square$

**Theorem 28.2 (Arbitrary complex references and the $2d$ prefactor).**
Under Theorem 28.1's hypotheses put
$\mathcal R_*(X)=\rho_*\operatorname{Tr}X$. For every finite reference
$\mathbb C^m$, every complex $Z\in M_d\otimes M_m$, and every $n\ge0$,

$$
\begin{aligned}
&\|(\Psi^n\otimes\operatorname{id}_m)(Z)
             -\rho_*\otimes\operatorname{Tr}_{\mathrm{sys}}Z\|_1\\
&\hspace{2em}\le
\min\{2,\,2d\kappa^{\lfloor n/N\rfloor}\}\,\|Z\|_1.
\end{aligned}
\tag{28.5}
$$

Consequently

$$
\|\Psi^n-\mathcal R_*\|_\diamond
\le\min\{2,\,2d\kappa^{\lfloor n/N\rfloor}\}.
\tag{28.6}
$$

Proof. Fix $n$, write $q=\lfloor n/N\rfloor$, $c_n=\kappa^q$, and
$T_n=\Psi^n-\mathcal R_*$. For a diagonal matrix unit,
$T_n(E_{ii})=\Psi^n(E_{ii}-\rho_*)$, so (28.2) bounds its norm by $2c_n$.
For $i\ne j$, write

$$
E_{ij}=A_{ij}+iB_{ij},\qquad
A_{ij}=(E_{ij}+E_{ji})/2,\qquad
B_{ij}=(E_{ij}-E_{ji})/(2i).
\tag{28.7}
$$

Both summands are traceless Hermitian of trace norm one. The reset
annihilates them, so (28.2) and the triangle inequality give
$\|T_n(E_{ij})\|_1\le2c_n$ for all $i,j$. This explicitly extends the
Hermitian traceless estimate to the full complex matrix-unit basis.

Write $Z=\sum_{i,j}E_{ij}\otimes Z_{ij}$ and take any singular value
decomposition

$$
Z=\sum_\ell s_\ell|u_\ell\rangle\langle v_\ell|,
\qquad s_\ell\ge0,\quad \|u_\ell\|_2=\|v_\ell\|_2=1.
$$

Expand $u_\ell=\sum_i|i\rangle\otimes u_{\ell i}$ and
$v_\ell=\sum_j|j\rangle\otimes v_{\ell j}$. A rank-one rectangular
operator $|u_{\ell i}\rangle\langle v_{\ell j}|$ has trace norm
$\|u_{\ell i}\|_2\|v_{\ell j}\|_2$. Thus

$$
\begin{aligned}
\sum_{i,j}\|Z_{ij}\|_1
&\le\sum_\ell s_\ell
       \left(\sum_i\|u_{\ell i}\|_2\right)
       \left(\sum_j\|v_{\ell j}\|_2\right)\\
&\le d\sum_\ell s_\ell=d\|Z\|_1.
\end{aligned}
\tag{28.8}
$$

The second inequality uses Cauchy–Schwarz and
$\sum_i\|u_{\ell i}\|_2^2=\sum_j\|v_{\ell j}\|_2^2=1$.
No factor depends on $m$. Tensor-product multiplicativity of the trace
norm now gives

$$
\begin{aligned}
\|(T_n\otimes\operatorname{id}_m)(Z)\|_1
&\le\sum_{i,j}\|T_n(E_{ij})\|_1\|Z_{ij}\|_1\\
&\le2dc_n\|Z\|_1.
\end{aligned}
\tag{28.9}
$$

Independently, Lemma 22.1's complete trace-norm argument gives diamond
norm one for both channels $\Psi^n$ and $\mathcal R_*$, hence norm at
most two for their difference. This fact holds on arbitrary complex
referenced operators: the amplified unital CP adjoint contracts operator
norm by (22.3), and Schatten infinity/one duality gives the required
primal norm. Taking the minimum proves the bound uniformly in $m$.

The usual, unnormalized partial trace satisfies

$$
(\mathcal R_*\otimes\operatorname{id}_m)(Z)
=\rho_*\otimes\operatorname{Tr}_{\mathrm{sys}}Z.
\tag{28.10}
$$

It is itself CPTP, and contracts trace norm on arbitrary complex inputs:
its adjoint is $W\mapsto I_d\otimes W$, an operator-norm isometry.
Trace preservation also gives
$\operatorname{Tr}_{\mathrm{sys}}[(\Psi^n\otimes\operatorname{id}_m)(Z)]
=\operatorname{Tr}_{\mathrm{sys}}Z$.
For a referenced density $\omega$, its marginal
$\omega_R=\operatorname{Tr}_{\mathrm{sys}}\omega$ has trace one, so the
limit is $\rho_*\otimes\omega_R$ with precisely that unchanged marginal.
No positivity, Hermiticity, or product condition on $Z$ was used in
(28.8)–(28.9). Taking the diamond supremum proves (28.6). $\square$

**Proposition 28.3 (The exact-reset endpoint and sharp limits of this
criterion).** If (28.1) holds with $a=1$, then
$\Psi^N=\mathcal R_{P_j}$ and $\Psi^n=\mathcal R_{P_j}$ for $n\ge N$.
The conclusion of automatic mixing fails in general at $a=1/2$ and for
higher-rank population projections, even with population one.

Proof. At $a=1$ positivity forces every density output of $\Psi^N$ to
be $P_j$. Densities complex-linearly span the matrix algebra, so this is
the stated reset on all complex inputs. Commutation with $\Psi$ shows
$\Psi(P_j)=P_j$, and every stationary density must equal $P_j$.
There is no need for a formula containing $\log\kappa$ at $\kappa=0$.

At $a=1/2$, dephasing a qubit in the basis
$|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$ always produces
$|0\rangle$-population $1/2$, yet fixes both orthogonal pure states
$P_+,P_-$. It also meets every smaller lower threshold. For a projection
$P$ of rank at least two, take orthogonal $e_1,e_2$ in its range. The map

$$
X\longmapsto PXP+
\operatorname{Tr}((I-P)X)|e_1\rangle\langle e_1|
\tag{28.11}
$$

is CPTP, always has population one in $P$, and fixes both pure states.
Its Kraus operators are $P$ together with $|e_1\rangle\langle f_l|$ for
an orthonormal basis $(f_l)$ of the complementary subspace; their squared
products sum to $I$. These are counterexamples to weakening the general
criterion, rather than classifications of the five-window lift class.
$\square$

**Corollary 28.4 (Direct control of all powers).** Under Theorem 28.1,
the spectral radius on the traceless complex subspace is at most
$\kappa^{1/N}$. The preceding power bounds require no normality or
diagonalizability assumption and permit a nonfaithful stationary density.

Proof. If $\operatorname{Tr}X=0$, write $X=H+iK$ with traceless Hermitian
$H,K$. Each has trace norm at most $\|X\|_1$ by the triangle inequality
and invariance under adjoint. Equation (28.2) gives
$\|\Psi^n(X)\|_1\le2\kappa^{\lfloor n/N\rfloor}\|X\|_1$.
Taking $n$th roots and using the finite-dimensional spectral radius
formula proves the claim. Possible nonnormal transients and Jordan
terms are already covered by the direct bounds for every power.
$\square$

## 29. Exact population powers and the odd-column minimum

**Theorem 29.1 (Power recurrence after the two-step transient).** Fix
$0<\eta<1$, let $r=1-\eta$, and use the row convention

$$
p=\frac{(r^2,\eta r,\eta,\eta r,\eta^2)}{1+\eta},
\qquad \Pi=\mathbf1p.
\tag{29.1}
$$

Thus $p$ is the transpose of (3.2), $\mathbf1$ is the all-ones column,
and $\Pi$ has every row $p$. For every integer $n\ge2$,

$$
Q_\eta^n=\Pi+(-\eta)^{n-2}(Q_\eta^2-\Pi).
\tag{29.2}
$$

Proof. Direct multiplication of (2.1) gives first three rows of $Q^2$
equal to $A$ and last two rows equal to $B$, where

$$
A=(r^2,0,\eta,r\eta,0),\qquad B=(0,r,0,0,\eta).
\tag{29.3}
$$

A further multiplication gives

$$
AQ=rA+\eta B,\qquad BQ=A,\qquad
p=\frac{A+\eta B}{1+\eta}.
\tag{29.4}
$$

All entries of $p$ are positive, $p\mathbf1=1$, and these equations give
$pQ=p$. Since $Q\mathbf1=\mathbf1$,
$Q\Pi=\Pi Q=\Pi$ and $\Pi^2=\Pi$.
For either $U=A$ or $U=B$, (29.4) says
$UQ=(1+\eta)p-\eta U$. Hence

$$
(Q^2-\Pi)Q=-\eta(Q^2-\Pi).
\tag{29.5}
$$

The case $n=2$ of (29.2) is its definition, and multiplication by $Q$
proves every later case by induction. This derivation keeps the initial
transient; it does not presume that $Q$ is diagonalizable. Since
$|\eta|<1$, it also proves $Q^n\to\Pi$. In particular $p$ is the unique
stationary probability row: any such row $v$ obeys
$v=vQ^n\to v\Pi=p$. $\square$

**Corollary 29.2 (The exact odd-step coordinate-zero minimum).** Put
$p_0=r^2/(1+\eta)$. For every integer $k\ge1$,

$$
(Q^{2k+1})_{i0}=
\begin{cases}
p_0(1-\eta^{2k}),&i=0,1,2,\\
p_0(1+\eta^{2k-1}),&i=3,4,
\end{cases}
\qquad
\min_i(Q^{2k+1})_{i0}=p_0(1-\eta^{2k}).
\tag{29.6}
$$

Proof. The zeroth column of $Q^2$ is $(r^2,r^2,r^2,0,0)^{\mathsf T}$,
and $r^2=(1+\eta)p_0$. Substitute these entries in (29.2) and use
$(-\eta)^{2k-1}=-\eta^{2k-1}$. The last two entries exceed the first
three by $p_0\eta^{2k-1}(1+\eta)>0$. $\square$

## 30. A positive interval of uniform mixing for every legal lift

**Theorem 30.1 (All-lift mixing and an explicit complete-norm rate).** Set

$$
\alpha=\frac{5-\sqrt{17}}4.
\tag{30.1}
$$

Fix $0<\eta<\alpha$, let $p_0=(1-\eta)^2/(1+\eta)$ and
$\delta=1-1/(2p_0)$. Choose any integer $k\ge1$ such that
$\eta^{2k}<\delta$; a strict choice, including when the logarithmic
ratio is an integer, is

$$
k=\left\lfloor\frac{\log\delta}{2\log\eta}\right\rfloor+1.
\tag{30.2}
$$

Define

$$
N=2k+1,\qquad a=p_0(1-\eta^{2k})>1/2,\qquad
\kappa=2\sqrt{a(1-a)}<1.
\tag{30.3}
$$

Every allowed lift $\Phi$ at this fixed parameter has a unique stationary
density $\rho_\Phi$. Its diagonal is $p^{\mathsf T}$ from (29.1), and

$$
\|\Phi^n-\mathcal R_{\rho_\Phi}\|_\diamond
\le\min\{2,\,10\kappa^{\lfloor n/(2k+1)\rfloor}\}
\qquad(n\ge0).
\tag{30.4}
$$

More fully, for every finite reference $\mathbb C^m$ and every complex
$Z\in M_5\otimes M_m$,

$$
\begin{aligned}
&\|(\Phi^n\otimes\operatorname{id}_m)(Z)
        -\rho_\Phi\otimes\operatorname{Tr}_{\mathrm{sys}}Z\|_1\\
&\hspace{2em}\le
\min\{2,\,10\kappa^{\lfloor n/(2k+1)\rfloor}\}\,\|Z\|_1.
\end{aligned}
\tag{30.5}
$$

The block length, rate, and prefactor are uniform over all legal lifts
at this fixed $\eta$ and chosen $k$. The stationary density can depend
on the lift; its five populations are common.

Proof. The heavy-population condition on the limiting row is exactly

$$
p_0>1/2
\iff 2(1-\eta)^2>1+\eta
\iff 2\eta^2-5\eta+1>0.
\tag{30.6}
$$

The two roots are $(5\pm\sqrt{17})/4$, with the larger root greater
than one. Thus within $0<\eta<1$ this condition holds precisely on
$(0,\alpha)$. Here $0<\delta<1$, and $\log\eta<0$. The strict inequality
$\eta^{2k}<\delta$ is equivalent to
$k>\log\delta/(2\log\eta)>0$, so (30.2) is a valid integer at least one.
It yields $1/2<a<p_0<1$, as required in Theorem 28.1.

For every complex $X$, the all-input law composes by induction:

$$
\operatorname{diag}\Phi^n(X)=(Q^{\mathsf T})^n\operatorname{diag}X.
\tag{30.7}
$$

Consequently every density $\rho$ satisfies

$$
\operatorname{Tr}(P_0\Phi^N(\rho))
=\sum_i(Q^N)_{i0}\rho_{ii}
\ge\min_i(Q^N)_{i0}=a,
\tag{30.8}
$$

where its diagonal entries are nonnegative and sum to one, and the last
equality is Corollary 29.2. This holds for every allowed lift, not just
for the selected family of §24, because (30.7) uses the full law again
on each intermediate input. Prescribing basis-input populations alone
would not justify that induction.

Apply Theorems 28.1–28.2 with $d=5$ and the rank-one $P_0$ to obtain
the unique stationary density and (30.4)–(30.5). Its stationary diagonal
obeys the classical stationary equation, whose unique probability
solution is $p$ by Theorem 29.1. All constants in these bounds depend
only on $\eta,k$. No retained environment or extra history space has
entered any of the iterates. $\square$

**Corollary 30.2 (A common per-step exponential bound).** With the same
parameters put $\beta=\kappa^{1/(2k+1)}\in(0,1)$. Then every such lift
satisfies

$$
\|\Phi^n-\mathcal R_{\rho_\Phi}\|_\diamond
\le\min\{2,\,10\kappa^{-1}\beta^n\}.
\tag{30.9}
$$

The identical coefficient also bounds (30.5) after multiplication by
$\|Z\|_1$.

Proof. Since $\lfloor n/N\rfloor\ge n/N-1$ and $0<\kappa<1$,
$\kappa^{\lfloor n/N\rfloor}\le\kappa^{-1}\beta^n$.
Substitute in (30.4)–(30.5). This is a sufficient rate and prefactor,
with no optimality assertion. $\square$

**Proposition 30.3 (The threshold is a boundary of the sufficient
criterion).** At $\eta=\alpha$, every finite-$k$ value in (30.3) is
strictly less than $1/2$. For $\alpha\le\eta<1$, no choice of time
makes $\min_i(Q^n)_{i0}>1/2$. These statements do not decide mixing of
the full lift class at or above $\alpha$.

Proof. At $\eta=\alpha$, $p_0=1/2$ and
$a_k=(1-\eta^{2k})/2<1/2$. For any $n\ge0$, stationarity gives

$$
\min_i(Q^n)_{i0}
\le\sum_i p_i(Q^n)_{i0}=p_0.
\tag{30.10}
$$

For $\eta\ge\alpha$ in the interior, (30.6) gives $p_0\le1/2$.
Thus changing the time cannot rescue this coordinate-zero criterion.
Failure of this sufficient condition is not failure of mixing. The
interval is not asserted to be sharp; other observations or mechanisms
would require their own proof. $\square$

## 31. Primary interfaces and the remaining all-parameter boundary

**Convention 31.1 (Primary sources, versions, and hypotheses).** The
population-cap and reference arguments above are given in full. The
following primary interfaces fix the standard components and their
conventions; they do not attribute the five-window interval to an
unconditional theorem about arbitrary classical lifts.

| Primary source and version | Interface and conditions |
| --- | --- |
| J. Watrous, *The Theory of Quantum Information*, author-hosted 2018 draft [TQI27], equations (1.183)–(1.186), Proposition 3.44, Theorem 3.46, and Lemma 6.31 | The pure-state trace norm formula requires unit vectors. Channel diamond norm one and complete contraction require CPTP maps on finite complex spaces. Lemma 6.31 gives a zero-diagonal orthonormal basis for a trace-zero complex operator; applied to $\sqrt\rho(P_j-pI)\sqrt\rho$, it also yields a pure decomposition of $\rho$ with population $p$. Lemma 27.2 instead proves that decomposition directly by rank reduction. The complete bound (28.5) has its own arbitrary-complex-input SVD proof, rather than being inferred from the state bound alone. |
| M. Raginsky, *Strictly contractive quantum channels and physically realizable quantum computers*, [quant-ph/0105141v3][RAG27], §II.D, equation (21), and §III.A, equations (22)–(23); Phys. Rev. A **65**, 032306 | The contraction mapping principle gives uniqueness and convergence for a fixed channel with a uniform trace-norm Lipschitz constant strictly below one on the entire density space. Equation (28.3) supplies exactly that condition for $\Gamma=\Psi^N$. No bistochastic or faithful-stationary-state premise is used, and this state-space interface is not a diamond-norm theorem. |
| O. Szehr and M. M. Wolf, *Perturbation Bounds for Quantum Markov Processes and their Fixed Points*, [arXiv:1210.1171v2][SW27], §II.B, equations (4)–(5) | The trace-norm contraction coefficient is defined on traceless Hermitian inputs and has a composition inequality for Hermiticity-preserving TP maps. Theorem 28.1 works on precisely that domain. Extension to arbitrary complex reference operators requires the additional proof of Theorem 28.2. |
| C. A. Fuchs and J. van de Graaf, *Cryptographic Distinguishability Measures for Quantum Mechanical States*, [quant-ph/9712042v2][FVG27], Theorem 1, equation (46) | For finite complex density matrices, including singular ones, the convention is $1-B(\rho,\sigma)\le\|\rho-\sigma\|_1/2\le\sqrt{1-B(\rho,\sigma)^2}$, where $B$ is root fidelity. This inequality alone does not give the needed fidelity lower bound from one population observation. The exact rank-one cap geometry in Theorem 27.3 supplies that step directly. |

**Convention 31.2 (Combined conclusions and unresolved classification).**
Theorem 30.1 is an all-lift theorem on the sufficient interval
$0<\eta<(5-\sqrt{17})/4$. It gives a common rate and prefactor at each
fixed parameter while allowing lift-dependent stationary coherences.
At $\eta=1/2$, §§17–23 give an actual nonrelaxing lift and a same-law
primitive family with no common vanishing rate. Section 24 separately
classifies the displayed selected family at every interior parameter;
its stationary-space change at $1/2$ has no defective nonzero Jordan
block. These quantifiers are compatible: the counterexample parameter
lies outside the positive interval, and selected-family convergence
cannot be transferred to the other lifts there.

No all-lift mixing classification is established here at the threshold
or on the remaining interior parameters, beyond the explicit obstruction
at $1/2$. The endpoints retain their separate conclusions in §§15 and 25.
The rates above are sufficient, with no sharp-threshold or optimal-rate
claim. Asymptotic diamond convergence to a reset is the conclusion of
§30; eventual EB and a finite EB index are not consequences asserted by
that argument. In particular the common positive stationary diagonal
alone is not a proof of a faithful stationary density.

These are ordinary finite-dimensional mathematical derivations under
the stated channel model. They do not certify physical or native
complete-window dynamics, a Hamiltonian or field theory, asymptotic
capacity, literature priority, or Lean/kernel verification. The standard
components are literature-attested within the conditions just listed;
their five-window combination and explicit formulas are model-specific
derivations, with no exhaustive novelty determination.

[TQI27]: https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf
[RAG27]: https://arxiv.org/abs/quant-ph/0105141v3
[SW27]: https://arxiv.org/abs/1210.1171v2
[FVG27]: https://arxiv.org/abs/quant-ph/9712042v2

## 追加锚（本行以下为增补区）

## 32. Full-complex interfaces and stationary-support reductions

**Convention 32.1 (Class and scope of the all-parameter extension).** Write
$\mathcal L_\eta$ for the entire allowed-lift class of Definition 2.2,
with $0<\eta<1$ and $r=1-\eta$. Retain Conventions 1.1–1.2 and the
unhalved norms of (17.1). A channel is mixing, or relaxing, if it has a
stationary density $\sigma_\Phi$ and
$\Phi^n(X)\to\sigma_\Phi\operatorname{Tr}X$ for every complex $X$.
The channel and parameter are fixed throughout each iteration. References
are arbitrary finite external systems, and each environment is fresh and
discarded. Sections 33–36 prove the full interior-parameter classification;
§37 proves a common complete-norm bound on compact parameter sets avoiding
$1/2$. These conclusions supply the all-lift classification left unresolved
in Convention 31.2, including the threshold of Proposition 30.3. The
explicit sufficient rates in Theorem 30.1 retain their stated scope.

The complete class is exactly Theorem 4.1: all eight unit environment
vectors in (4.4) live in one common complex space, obey (4.5), and have an
actual PSD Gram matrix. Every Gram rank from two through eight is allowed
when compatible with those constraints. If $G_{ab}=\langle f_a,f_b\rangle$
in the edge order (4.3), and $D_{\mathcal E}$ contains the positive edge
weights, the active Choi block is $D_{\mathcal E}\overline G D_{\mathcal E}$.
Equivalently its entries are (4.6), with the reversed inner-product order.
The output-first Choi conditions are $J\ge0$ and
$J_{jj}=\operatorname{diag}_iQ_{ij}$; they imply
$\operatorname{Tr}_{\mathrm{out}}J=I_5$. Thus the proofs concern the actual
common-environment PSD8 class, including every complex matrix-unit input.
In particular no constraint is imposed on $\langle\gamma_0,\gamma_1\rangle$
beyond that Gram positivity. The dual identities used below are precisely
(4.8):

$$
\begin{aligned}
\Phi^\dagger(P_0)&=r(P_0+P_1),&
\Phi^\dagger(P_3)&=\eta(P_0+P_1),\\
\Phi^\dagger(P_1)&=rP_2,&
\Phi^\dagger(P_4)&=\eta P_2,&
\Phi^\dagger(P_2)&=P_3+P_4.
\end{aligned}
\tag{32.1}
$$

Theorem 29.1 gives $Q^n\to\mathbf1p$, where throughout this extension
$p=(r^2,\eta r,\eta,\eta r,\eta^2)/(1+\eta)$ is a row.
Consequently every $Q^m$, $m\ge1$, has the same unique stationary
probability row: apply its powers $Q^{mk}$ and take $k\to\infty$.
By (30.7), every $\Phi^m$-fixed density therefore has diagonal
$p^{\mathsf T}$. Each of its five populations is strictly positive.
This fact does not assert that the density is faithful on all of $H$.

Here are the standard support reductions used in the proof of Theorem
36.1, with their nonfaithful cases included. A density stationary under a
CPTP map has an invariant support $S$. Indeed, for $y\perp S$ and any
Kraus representation,

$$
0=\langle y,\Phi(\rho)y\rangle
 =\sum_\ell\|\rho^{1/2}K_\ell^\dagger y\|^2
\quad\Longrightarrow\quad K_\ell S\subseteq S.
\tag{32.2}
$$

Such a subspace is called an enclosure. Restriction to it is CPTP and
has a stationary density: Cesàro averages of the iterates of any density
on it have a convergent subsequence, with discrepancy tending to zero.
These facts apply on the actual support and require no reducing-subspace
property on its full-space orthogonal complement.

If two stationary densities differ, their nonzero Hermitian difference
$D=D_+-D_-$ is fixed and $\operatorname{Tr}D_+=\operatorname{Tr}D_-$.
Trace preservation and trace-norm contraction give equality in

$$
\|D\|_1=\|\Phi(D_+)-\Phi(D_-)\|_1
\le\operatorname{Tr}\Phi(D_+)+\operatorname{Tr}\Phi(D_-)=\|D\|_1.
\tag{32.3}
$$

For positive matrices equality here means orthogonal supports. One way
to see this is to use the positive spectral projection of their difference
in the variational characterization of trace norm: equality forces that
projection to contain the first support and annihilate the second.
Uniqueness of Jordan parts then gives $\Phi(D_\pm)=D_\pm$.
Normalizing yields two orthogonally supported stationary densities.
The same argument for a fixed Hermitian operator, followed by real and
imaginary parts, shows that a unique stationary density $\sigma$ implies
$\operatorname{Fix}(\Phi)=\mathbb C\sigma$. These are the Jordan-support
facts of Burgarth et al., Lemma 1 and Corollaries 1–2 [MIX32].

For a peripheral eigenoperator $\Phi(A)=\lambda A$, $|\lambda|=1$, write
$A=UB$, $B=|A|$, extending the polar partial isometry to a unitary on
$H$. For the Hilbert–Schmidt vectors
$X_\ell=K_\ell U\sqrt B$ and $Y_\ell=UK_\ell\sqrt B$,
trace preservation gives

$$
\sum_\ell\|X_\ell\|_2^2=\sum_\ell\|Y_\ell\|_2^2=\operatorname{Tr}B,
\qquad
\sum_\ell\langle Y_\ell,X_\ell\rangle
=\operatorname{Tr}(U^\dagger\Phi(A))=\lambda\operatorname{Tr}B.
\tag{32.4}
$$

Equality in Cauchy–Schwarz implies $X_\ell=\lambda Y_\ell$ for every
$\ell$. Multiply on the right by $\sqrt B$ and sum the resulting
$K_\ell UB=\lambda UK_\ell B$ against $K_\ell^\dagger$ to obtain
$\Phi(A)=\lambda U\Phi(B)$. Comparing with $\lambda UB$ shows
$\Phi(B)=B$. Applying this also to $A^\dagger$ proves that both
$|A|$ and $|A^\dagger|$ are stationary. This reconstructs the
nonfaithful polar step in Burgarth et al., Theorem 5 [MIX32].

If $\sigma$ is unique, both moduli are the same positive scalar times
$\sigma$, their traces being equal. Thus every peripheral operator obeys
$A=P_RAP_R$, where $R=\operatorname{supp}\sigma$. The restriction to $R$
is faithful and irreducible: a proper nonzero enclosure would have its
own stationary density on a smaller support. On $R$ the polar unitary
commutes with $\sigma$ and the invertibility of $B$ permits cancellation:

$$
K_\ell U=\lambda UK_\ell\quad\hbox{on }R.
\tag{32.5}
$$

For $\lambda\ne1$, this gives the cyclic reduction explicitly. If $\mu$
is an eigenvalue of $U$, a nonzero vector in its eigenspace has at least
one nonzero Kraus image, by TP, and that image has eigenvalue
$\lambda^{-1}\mu$. The finite spectrum is closed under this rotation;
therefore $\lambda$ is a root of unity. A union of one rotation orbit is
an enclosure, so irreducibility forces exactly one orbit. Its orthogonal
spectral spaces $R_0,\ldots,R_{m-1}$, $m\ge2$, form a cycle under every
Kraus operator. Their projections commute with $\sigma$, and stationarity
gives

$$
\Phi(P_{R_a}\sigma P_{R_a})=P_{R_{a+1}}\sigma P_{R_{a+1}}.
\tag{32.6}
$$

The block traces are equal and positive. Their normalized blocks are
faithful densities $\rho_a$ on $R_a$, with
$\Phi(\rho_a)=\rho_{a+1}$, cyclic indices, and all have diagonal
$p^{\mathsf T}$ because $\Phi^m(\rho_a)=\rho_a$. This is the cyclic
structure of Carbone–Jenčová, §3.1 [CYCLE32], applied only after the
faithful irreducible restriction has been established.

## 33. A pure stationary line and its orthogonal stationary support

**Lemma 33.1 (The common-environment line obstruction).** If an allowed
lift has a pure stationary state and an orthogonally supported stationary
density, then $\eta=1/2$.

Proof. Write the pure state as $|\psi\rangle\langle\psi|$ and the other
support as $S\subseteq\psi^\perp$. A diagonal unitary conjugation of the
channel preserves (2.2). Since the five populations of $\psi$ are $p$,
choose that gauge so that

$$
\psi=\frac{(r,\sqrt{\eta r},\sqrt\eta,\sqrt{\eta r},\eta)^{\mathsf T}}
              {\sqrt{1+\eta}}.
\tag{33.1}
$$

Purity of the stationary output gives $V\psi=\psi\otimes c$ for a unit
common-environment vector $c$. Compare the five system coordinates in
(4.4). Coordinates 1 and 4 give $\gamma_0=\gamma_1=c$, and the others give

$$
\sqrt r\,\alpha_0+\sqrt\eta\,\alpha_1
=\sqrt r\,\beta_0+\sqrt\eta\,\beta_1
=\sqrt r\,\delta_0+\sqrt\eta\,\delta_1=c.
\tag{33.2}
$$

Each displayed pair is orthonormal. Hence there are unit vectors
$a,b,d\perp c$ in that same environment with

$$
\begin{aligned}
\alpha_0&=\sqrt r\,c+\sqrt\eta\,a,&
\alpha_1&=\sqrt\eta\,c-\sqrt r\,a,\\
\beta_0&=\sqrt r\,c+\sqrt\eta\,b,&
\beta_1&=\sqrt\eta\,c-\sqrt r\,b,\\
\delta_0&=\sqrt r\,c+\sqrt\eta\,d,&
\delta_1&=\sqrt\eta\,c-\sqrt r\,d.
\end{aligned}
\tag{33.3}
$$

Their mutual inner products remain arbitrary consistent complex Gram
entries. Put

$$
\begin{aligned}
u&=\sqrt r\,|0\rangle+\sqrt\eta\,|3\rangle,&
v&=\sqrt r\,|1\rangle+\sqrt\eta\,|4\rangle,& z&=|2\rangle,\\
h_A&=\sqrt r\,|0\rangle+\sqrt\eta\,|1\rangle,&
h_D&=\sqrt r\,|3\rangle+\sqrt\eta\,|4\rangle,\\
l_A&=\sqrt\eta\,|0\rangle-\sqrt r\,|1\rangle,&
l_D&=\sqrt\eta\,|3\rangle-\sqrt r\,|4\rangle,\\
K&=|u\rangle\langle h_A|+|v\rangle\langle z|
                                  +|z\rangle\langle h_D|.
\end{aligned}
\tag{33.4}
$$

For $x_A=\langle l_A,x\rangle$, $x_D=\langle l_D,x\rangle$, substitution
in the actual isometry, with no change of environment, gives

$$
\begin{aligned}
Vx&=Kx\otimes c+Wx,\\
Wx&=x_A(\sqrt r\,|0\rangle\otimes a
             +\sqrt\eta\,|3\rangle\otimes b)+x_Dz\otimes d,\\
K\psi&=K^\dagger\psi=\psi,\qquad
K^\dagger K=P_{\operatorname{span}\{h_A,z,h_D\}}.
\end{aligned}
\tag{33.5}
$$

By (32.2), $VS\subseteq S\otimes E$. The environment component along
$c$ and the component perpendicular to it separately give $KS\subseteq S$
and $WS\subseteq S\otimes E$. Projecting $Wx$ onto $\psi$ yields

$$
\sqrt r\,(ra+\eta b)x_A+\sqrt\eta\,d x_D=0\qquad(x\in S).
\tag{33.6}
$$

First suppose $x_A$ vanished on all of $S$. Then $x_D$ would also vanish,
since $d$ is unit and $\eta>0$. Thus $W$ vanishes there and the isometry
$V$ makes $K|_S$ an isometry into $S$, hence a unitary. But any
unit-modulus eigenvector of $K$ lies in
$\operatorname{span}\{h_A,z,h_D\}$ by (33.5). Write it
$x h_A+y z+q h_D$. If $x=0$, the coordinate-3 and coordinate-2 equations
force $q=y=0$. Otherwise the coordinate-0 equation forces its eigenvalue
to be one, and the remaining equations give
$y=q=\sqrt{\eta/r}\,x$. This is precisely the line $\mathbb C\psi$,
inconsistent with the nonzero space $S\perp\psi$.
The full characteristic polynomial is also
$\det(\lambda I-K)=\lambda^3(\lambda+\eta)(\lambda-1)$;
its only unit-circle root in the interior is one.

There is consequently an $x\in S$ with $x_A\ne0$. Equation (33.6)
then fixes one complex $t$, independent of $x$, such that

$$
ra+\eta b=td,\qquad x_D=-\sqrt{r/\eta}\,t x_A\quad(x\in S).
\tag{33.7}
$$

The linear functional
$L_t=\sqrt r\,t\langle l_A|+\sqrt\eta\,\langle l_D|$
annihilates $S$. Substitution in (33.5), and the chosen nonzero $x_A$,
show that

$$
F=\sqrt r\,|0\rangle\otimes a+\sqrt\eta\,|3\rangle\otimes b
                -\sqrt{r/\eta}\,t z\otimes d\ \in S\otimes E.
\tag{33.8}
$$

Applying $L_t\otimes I$ gives
$\sqrt\eta(rt a+\eta b)=0$. In particular $t=0$ is impossible.
Thus $b=\beta a$, $|\beta|=1$, and

$$
t=-\frac{\eta\beta}{r},\qquad
 d=\frac{r+\eta\beta}{t}\,a.
\tag{33.9}
$$

Only the positive $r$ and the now nonzero $t$ have been divided out.
If $r+\eta\beta=0$, (33.9) would give $d=0$, already a contradiction;
no division by that possibly zero expression is used. Substituting gives
$F=w\otimes a$, where

$$
w=\sqrt r\,|0\rangle+\sqrt\eta\,\beta|3\rangle
                   -\sqrt{r/\eta}(r+\eta\beta)z\ \in S.
\tag{33.10}
$$

Since $Kw\in S$, multiplication using (33.4), (33.9) gives the decisive
factorization

$$
0=L_tKw=r\sqrt\eta(1-\beta)(1+\eta\beta).
\tag{33.11}
$$

Here $r\sqrt\eta>0$ and $|\eta\beta|<1$, so $\beta=1$. Now
$t=-\eta/r$, $d=-(r/\eta)a$, and the unit norms force $r=\eta=1/2$.
This includes the zero-coordinate-functional case, $t=0$, every complex
phase (including $\beta=-1$), and $r+\eta\beta=0$. Invariance was used
only on $S$, without asserting reduction of the full $\psi^\perp$.
$\square$

## 34. Rank-four stationary support and full-input compression

**Lemma 34.1 (Exactly one output compression).** If a stationary density
has rank-four support $R$, then the environment-valued projection of $V$
onto $R^\perp$ vanishes on all of $H$. After diagonal phase changes,
exactly one of the following descriptions holds:

$$
\begin{aligned}
\mathrm U:\quad&R=\operatorname{span}\{u,|1\rangle,z,|4\rangle\},
 &u&=\sqrt r\,|0\rangle+\sqrt\eta\,|3\rangle,\\
\mathrm V:\quad&R=\operatorname{span}\{|0\rangle,|3\rangle,v,z\},
 &v&=\sqrt r\,|1\rangle+\sqrt\eta\,|4\rangle.
\end{aligned}
\tag{34.1}
$$

In case U, $\beta_i=\alpha_i$ in that gauge; in case V,
$\gamma_1=\gamma_0$. A simultaneous second compression is impossible.

Proof. Write $R^\perp=\mathbb C\tau$, $\|\tau\|=1$.
Since $VR\subseteq R\otimes E$, there is an environment vector $\xi$ with

$$
(\langle\tau|\otimes I)Vx=\langle\tau,x\rangle\xi\quad(x\in H).
\tag{34.2}
$$

The columns 3 and 4 of (4.4) say

$$
\overline{\tau_2}\delta_0=\overline{\tau_3}\xi,
\qquad
\overline{\tau_2}\delta_1=\overline{\tau_4}\xi.
\tag{34.3}
$$

If $\tau_2\ne0$, two nonzero orthogonal vectors would be collinear.
Hence $\tau_2=0$. If $\xi\ne0$, (34.3) forces $\tau_3=\tau_4=0$;
the column-2 equation then gives $\tau_1=0$, and the column-1 equation
becomes $\sqrt r\,\overline{\tau_0}\alpha_1=0$. This contradicts
$\|\tau\|=1$. Thus $\xi=0$, proving vanishing on the entire input space.
The remaining equations are

$$
\begin{aligned}
\sqrt r\,\overline{\tau_0}\alpha_i
       +\sqrt\eta\,\overline{\tau_3}\beta_i&=0\quad(i=0,1),\\
\sqrt r\,\overline{\tau_1}\gamma_0
       +\sqrt\eta\,\overline{\tau_4}\gamma_1&=0.
\end{aligned}
\tag{34.4}
$$

In either coordinate pair $(\tau_0,\tau_3)$ or $(\tau_1,\tau_4)$,
one nonzero coordinate forces the other to be nonzero, since the edge
weights are positive and the environment vectors are unit. The first
nonzero pair forces $\beta_i=\omega\alpha_i$ with one unit phase
$\omega$ for both $i$, compressing the coordinate plane $(0,3)$ to one
line. The second forces $\gamma_1$ to be a phase multiple of $\gamma_0$,
compressing $(1,4)$ to one line. At least one pair is nonzero.

If both were nonzero, every output of $V$ would have system support in
the sum of those two lines and $\mathbb Cz$, of dimension at most three.
A rank-four stationary output could not be supported there. The same
rank argument rules out an accidental second compression when just one
coordinate pair is nonzero. Absorb the remaining unit phase by a diagonal
unitary; the positive weights fix the displayed vectors $u$ or $v$.
Because $R$ itself has dimension four, the resulting four-dimensional
output space equals $R$. This proves exactly the alternatives in (34.1),
including coordinate-zero and phase degeneracies. It makes no general
classification assertion about rank-three stationary supports. $\square$

## 35. Complex mixed-rank stationary and swapped sectors

**Lemma 35.1 (The two mixed-sector exclusions).** Let $R_0\perp R_1$
have dimensions at least two and carry faithful densities $\rho_a$ with
diagonal $p^{\mathsf T}$. Suppose
$\Phi(\rho_a)=\rho_{\tau(a)}$, where $\tau$ is either the identity or
the swap. Dimensions $2+3$ are impossible for every interior $\eta$.
Dimensions $2+2$ force $\eta=1/2$, and their case V in Lemma 34.1 is
impossible even there. All subspaces and densities may be complex.

Proof. Put $b=\tau(a)$, $P_a=P_{R_a}$. Positivity, as in (32.2), gives
$VR_a\subseteq R_b\otimes E$. For every $j$, $P_ae_j\ne0$:
otherwise the positive population $p_j=\langle e_j,\rho_a e_j\rangle$
would vanish.

For dimensions summing to five, choose the rank-two source sector $R_a$.
The two sectors exhaust the actual five-dimensional $H$, so their
transition laws give the full intertwining
$VP_a=(P_b\otimes I)V$. In particular

$$
VP_ae_3=(P_bz)\otimes\delta_0,\qquad
VP_ae_4=(P_bz)\otimes\delta_1.
\tag{35.1}
$$

These are nonzero orthogonal equal-norm vectors. By isometry,
$P_ae_3,P_ae_4$ are a basis of $R_a$. Their whole output is supported
on the single system line $\mathbb CP_bz$, contradicting faithfulness of
$\rho_b$ in dimension at least two. This applies to both transitions.

For total dimension four, each sector has dimension two. Their mean
is a stationary density with rank-four support $R=R_0\oplus R_1$.
Lemma 34.1 applies. The restricted channel
$T_a:\mathcal B(R_a)\to\mathcal B(R_b)$ is CPTP; its adjoint is positive
and unital between the two sector identities. Write
$F_j^a=P_aP_jP_a$. Compressing (32.1) gives

$$
T_a^\dagger(F_1^b)=rF_2^a,\qquad
T_a^\dagger(F_4^b)=\eta F_2^a.
\tag{35.2}
$$

If $P_be_1,P_be_4$ were independent, $F_1^b+F_4^b$ would dominate
$\epsilon I_b$ for some $\epsilon>0$. Positivity and unitality would
make its image dominate $\epsilon I_a$, whereas (35.2) makes the image
$F_2^a$, of rank one. Thus the nonzero rank-one effects are proportional.
Applying (35.2), and using $F_2^a\ne0$, fixes the proportionality:

$$
F_1^b=(r/\eta)F_4^b.
\tag{35.3}
$$

In case U, $e_1,e_4\in R$. Sum traces of (35.3) over the two sectors:
$1=(r/\eta)1$. Hence $\eta=1/2$.

In case V, use the phase gauge $\gamma_0=\gamma_1=\gamma$, and put
$b_a=P_ae_3$, $z_a=P_az$, $v_a=P_av$. All are nonzero since the
corresponding coordinate populations are positive, and $e_3,z,v\in R$.
The intertwining on $R$, together with $Ve_3=z\otimes\delta_0$ and
$Vz=v\otimes\gamma$, gives

$$
Vb_a=z_b\otimes\delta_0,\qquad Vz_a=v_b\otimes\gamma,
\qquad
\|b_a\|^2=\|z_b\|^2,\quad \|z_a\|^2=\|v_b\|^2.
\tag{35.4}
$$

The full transition into the line $v$ gives
$\Phi^\dagger(|v\rangle\langle v|)=P_2$, so compression yields

$$
T_a^\dagger(|v_b\rangle\langle v_b|)=|z_a\rangle\langle z_a|.
\tag{35.5}
$$

The two vectors here have the same strictly positive squared norm by
(35.4). Dividing by this common value gives
$T_a^\dagger(P)=Q$ for rank-one projections on two-dimensional spaces.
This precise projection premise implies $T_a(I_a)=I_b$: the state $Q$
has output expectation one against $P$, hence output $P$; the orthogonal
state $I_a-Q$ has output expectation zero and hence output $I_b-P$.
Their sum proves unitality of $T_a$. Equal norms are essential here;
unrelated nonzero rank-one effects alone would not give that premise.

Consequently $T_a^\dagger$ is trace preserving. The identity for $P_2$
in (32.1), with $P_RP_4P_R=\eta|v\rangle\langle v|$, now gives

$$
T_a^\dagger(|z_b\rangle\langle z_b|)
=|b_a\rangle\langle b_a|+\eta|v_a\rangle\langle v_a|.
\tag{35.6}
$$

Taking traces and using (35.4) forces
$\|z_b\|^2=\|z_b\|^2+\eta\|v_a\|^2$, impossible. Thus V is
excluded. The proof uses the complete five-dimensional exhaustion for
$2+3$, and the actual four-dimensional support for $2+2$, in both the
stationary and swapped cases. $\square$

## 36. The full interior-parameter classification and transient inputs

**Theorem 36.1 (Exactly half admits a nonrelaxing lift).** In the complete
class of Definition 2.2,

$$
\forall\eta\in(0,1),\qquad
\bigl[\exists\Phi\in\mathcal L_\eta\text{ that is nonrelaxing}\bigr]
\quad\Longleftrightarrow\quad\eta=\tfrac12.
\tag{36.1}
$$

For $\eta\ne1/2$, every allowed lift has a unique stationary density
$\sigma_\Phi$, with diagonal $p^{\mathsf T}$, and has no peripheral
eigenvalue other than the simple eigenvalue one. On the whole complex
input algebra, including inputs and cross terms outside its stationary
support,

$$
\Phi^n(X)\longrightarrow\sigma_\Phi\operatorname{Tr}X.
\tag{36.2}
$$

Proof. Fix $\eta\ne1/2$. A stationary density exists by Cesàro
compactness. If there were two, (32.3) would give orthogonal stationary
densities. If one support were a line, Lemma 33.1 would force half.
Otherwise their dimensions are at least two, and, since they are
orthogonal in dimension five, the only possibilities are $2+2$ and
$2+3$. Lemma 35.1 excludes both. Thus $\sigma_\Phi$ is unique.

By the polar argument (32.4), every peripheral eigenoperator is supported
on $R=\operatorname{supp}\sigma_\Phi$. The restriction there is faithful
and irreducible. If it had an eigenvalue $\lambda\ne1$ on the unit
circle, (32.5)–(32.6) would give an orthogonal cycle of $m\ge2$ sectors
with faithful cyclic densities of diagonal $p^{\mathsf T}$.

Suppose a target sector $R_b$ is a line with unit vector $\psi_b$ and
predecessor $R_a$. On that predecessor, invariance and isometry give
$Vx=\psi_b\otimes Wx$ for an isometry $W:R_a\to E$.
The coordinate-1 equation in the actual (4.4) is

$$
\sqrt r\,x_2\gamma_0=(\psi_b)_1Wx\qquad(x\in R_a).
\tag{36.3}
$$

Its left side has rank at most one as a linear map on $R_a$, while the
right side has rank $\dim R_a$, since $|(\psi_b)_1|^2=p_1>0$.
Thus the predecessor is a line. Repeating backwards around the finite
cycle shows every sector is a line, including any initially mixed-rank
cycle containing one line.

Choose unit cyclic vectors $\psi_a$. Equation (36.3) then makes each
environment factor in $V\psi_a=\psi_{a+1}\otimes c_a$ a scalar multiple
of the same $\gamma_0$. That scalar has modulus one, since
$r p_2=p_1$. Consequently on the span of the entire cycle,
$V=U_{\mathrm{cyc}}\otimes\gamma_0$ for a unitary cyclic operator with
phases. The channel acts there by unitary conjugation. The cycle has at
least two dimensions, so an orthonormal eigenbasis of that unitary gives
at least two orthogonal stationary pure states, contradicting uniqueness.
This treats all phases using the actual common environment.

If no cyclic sector is a line, all have dimension at least two. In
$\dim R\le5$, a nontrivial cycle must therefore have exactly two
sectors, with dimensions $2+2$ or $2+3$. These are precisely the swapped
cases excluded by Lemma 35.1. Thus no nontrivial peripheral eigenvalue
exists; uniqueness and (32.3) make the eigenvalue-one space
$\mathbb C\sigma_\Phi$.

To pass to all inputs, use the full superoperator on $M_5(\mathbb C)$.
Its powers are uniformly bounded in trace norm even on complex inputs:
complete contraction of CPTP maps was proved in Lemma 22.1, (22.3), by
the amplified unital adjoint and trace-norm duality. Hence its spectral
radius is at most one and every unit-circle Jordan block is semisimple;
a larger block would give polynomially growing powers. All peripheral
eigenoperators have already been placed in $R$, and all remaining
full-algebra Jordan blocks have eigenvalues strictly inside the unit
disk. Their polynomial-times-exponential terms tend to zero. The limit
has the form $X\mapsto\sigma_\Phi f(X)$; trace preservation and
$\operatorname{Tr}\sigma_\Phi=1$ force $f(X)=\operatorname{Tr}X$.
This proves (36.2) with every transient feeding term included. It does
not require a pure stationary line to reduce the full input space.

Conversely, at half use exactly the channel $\Phi_\circ$ in Definition
17.2, with Kraus operators (17.3) and the common-environment realization
(17.6). Theorem 17.3 proves its full-complex-input legality and TP.
Theorem 18.1 supplies the orthogonal stationary densities
$P=|s\rangle\langle s|$ and $M=(P_R-P)/2$. Their two distinct fixed
outputs preclude convergence to one reset. This proves the existential
half implication in (36.1), completing the equivalence. $\square$

**Proposition 36.2 (No common vanishing bound near half).** For any
parameter set $S\subset(0,1)\setminus\{1/2\}$ having $1/2$ in its
closure, no function $b(n)\to0$ can bound
$\|\Phi^n-\mathcal R_{\sigma_\Phi}\|_\diamond$ for every
$\eta\in S$ and every $\Phi\in\mathcal L_\eta$.

Proof. Keep the exact environment vectors (17.6) and put
$u_\eta=\sqrt r\,|0\rangle+\sqrt\eta\,|3\rangle$,
$v_\eta=\sqrt r\,|1\rangle+\sqrt\eta\,|4\rangle$ in (17.3):

$$
\begin{aligned}
K_0(\eta)&=|u_\eta\rangle\langle0|
                 +|v_\eta\rangle\langle2|/\sqrt2+|z\rangle\langle4|,\\
K_1(\eta)&=|u_\eta\rangle\langle1|
                 +|v_\eta\rangle\langle2|/\sqrt2+|z\rangle\langle3|.
\end{aligned}
\tag{36.4}
$$

Theorem 4.1 makes this an actual legal continuous family at every interior
parameter; at half it is $\Phi_\circ$. For each fixed $n$, continuity
of finite powers and Theorem 18.1 give

$$
\|\Phi_\eta^n(P)-\Phi_\eta^n(M)\|_1\longrightarrow\|P-M\|_1=2
\qquad(\eta\to1/2).
\tag{36.5}
$$

Against any common reset density $\tau$, at least one of the errors on
$P,M$ is at least half this distance, by the triangle inequality.
For $\eta\in S$, take $\tau=\sigma_{\Phi_\eta}$ from Theorem 36.1.
Thus at every fixed $n$ the supremum of the complete-norm errors over
$S$ and its allowed lifts is at least one. A bound tending to zero is
impossible, even though every individual lift in that set mixes.
$\square$

## 37. A finite contraction horizon and compact uniformity

**Theorem 37.1 (Uniform complete forgetting away from half).** Let
$K\subset(0,1)\setminus\{1/2\}$ be nonempty and compact. On traceless
Hermitian inputs define

$$
\delta(T)=\sup_{A=A^\dagger,\,\operatorname{Tr}A=0,\,A\ne0}
                  \frac{\|T(A)\|_1}{\|A\|_1}.
\tag{37.1}
$$

Then the full-class extremum

$$
q_K=\max_{\eta\in K,\,\Phi\in\mathcal L_\eta}\delta(\Phi^{24})
\quad\hbox{satisfies}\quad 0\le q_K<1.
\tag{37.2}
$$

For every such $\eta,\Phi$, every $n\ge0$, every finite reference
$\mathbb C^m$, and every complex $Z\in M_5\otimes M_m$,

$$
\begin{aligned}
\|\Phi^n-\mathcal R_{\sigma_\Phi}\|_\diamond
 &\le\min\{2,10q_K^{\lfloor n/24\rfloor}\},\\
\|(\Phi^n\otimes\operatorname{id}_m)(Z)
 -\sigma_\Phi\otimes\operatorname{Tr}_{\mathrm{sys}}Z\|_1
 &\le\min\{2,10q_K^{\lfloor n/24\rfloor}\}\,\|Z\|_1.
\end{aligned}
\tag{37.3}
$$

For a fixed $\eta\ne1/2$ take $K=\{\eta\}$. The density
$\sigma_\Phi$ belongs to the chosen lift; only its diagonal is common.
Use $q^0=1$, also at $q=0$, in which case resetting is exact for
$n\ge24$. The extremum in (37.2) is implicit, with no optimal-rate
or optimal-prefactor assertion.

Proof. First establish the horizon for a mixing CPTP map on $M_d$,
without a faithful-state assumption. Gaubert–Qu [GQ32], §7, equations
(24)–(25), use a unital CP Heisenberg map
$X\mapsto\sum_iK_i^\dagger XK_i$, $\sum_iK_i^\dagger K_i=I$,
and its CPTP Schrödinger dual. Their trace-norm contraction ratio on
density differences equals (37.1): every nonzero traceless Hermitian
matrix is a positive scalar times the difference of its normalized
Jordan parts. Their Corollary 7.3 characterizes coefficient one by
orthogonal output Kraus spans. Lemma 7.6 and Theorem 7.8 give the
$d^2-1$ horizon; condition (2) of Theorem 7.8 is convergence to a unique
invariant density regardless of the initial density. Those hypotheses
are met by Theorem 36.1, with the full input dimension $d=5$. No faithful
stationary density is required by that result.

Here is an independent operator-space proof of precisely the step needed.
For Kraus operators of a CPTP map define complex subspaces

$$
\mathcal H_0=\mathbb CI,\qquad
\mathcal H_{n+1}=\operatorname{span}_{\mathbb C}
 \{K_i^\dagger XK_j:X\in\mathcal H_n,\ i,j\}.
\tag{37.4}
$$

TP gives $I=\sum_iK_i^\dagger K_i\in\mathcal H_1$; monotonicity
of the recursion then gives $\mathcal H_n\subseteq\mathcal H_{n+1}$.
If equality occurs once, it persists. Starting at dimension one in a
space of dimension $d^2$, the chain has stabilized by $d^2-1$:
if all preceding inclusions are strict it has already reached dimension
$d^2$. Explicitly, with words of length $n$,

$$
\mathcal H_n=\operatorname{span}_{\mathbb C}
               \{K_w^\dagger K_v:|w|=|v|=n\}.
\tag{37.5}
$$

For any CPTP $T$, $\delta(T)=1$ exactly when two pure inputs have
orthogonal output supports. The forward implication follows by attaining
the norm maximum on the compact unit sphere of traceless Hermitian inputs.
Its normalized Jordan parts have output distance two, hence orthogonal
supports. In spectral decompositions of those two input densities, every
positive output term lies in the corresponding output support. Select
one pure term from each; their outputs remain orthogonal. Conversely,
orthogonal output states have distance two. Trace-norm contraction forces
the corresponding pure input distance to be two as well, and their
difference attains contraction coefficient one.

For $T=\Phi^n$ this says that $\delta(\Phi^n)=1$ exactly when there
are unit vectors $x,y$ such that

$$
\langle K_wx,K_{w'}y\rangle=0
\quad\hbox{for every pair of length-}n\hbox{ words }w,w'.
\tag{37.6}
$$

Equivalently $\langle x,Xy\rangle=0$ for every $X\in\mathcal H_n$.
If this held at $n=d^2-1$, stabilization would make the very same pair
have orthogonal outputs at every later time. That contradicts convergence
of both states to one density. Thus every mixing channel on $M_d$ obeys
$\delta(\Phi^{d^2-1})<1$. For the actual full $M_5$ this is horizon 24,
including nonfaithful stationary supports and transient inputs.

Now use the Choi class in Theorem 4.1. For fixed $\eta$ it is closed
in the bounded PSD set of trace five, hence compact. More generally

$$
\{(\eta,J):\eta\in K,\ J\ge0,
                   J_{jj}=\operatorname{diag}_i(Q_\eta)_{ij}\}
\tag{37.7}
$$

is compact: all constraints are closed, $Q_\eta$ is continuous, and
$\operatorname{Tr}J=5$ bounds the positive matrices. The coefficient
$\delta$ is an operator norm on the fixed real traceless Hermitian
space, so it is continuous; $\Phi\mapsto\Phi^{24}$ is polynomial in
matrix coefficients. The continuous function in (37.2) attains its
maximum on (37.7). Every point is mixing by Theorem 36.1, so every value
is strictly below one, and the attained maximum is strictly below one.
No continuity or global faithfulness of $\sigma_\Phi$ is needed here.

For any traceless Hermitian $A$, submultiplicativity of (37.1) and
trace-norm nonexpansion of the remaining fewer than 24 steps give

$$
\|\Phi^n(A)\|_1\le q_K^{\lfloor n/24\rfloor}\|A\|_1.
\tag{37.8}
$$

Apply exactly the arbitrary-complex-input amplification in the proof of
Theorem 28.2, (28.7)–(28.10), with $d=5$ and
$c_n=q_K^{\lfloor n/24\rfloor}$ replacing $\kappa^{\lfloor n/N\rfloor}$.
Its required premise is the traceless Hermitian bound, now (37.8),
together with stationarity of $\sigma_\Phi$. Indeed diagonal matrix
units use $\Phi^n(E_{ii}-\sigma_\Phi)$, and off-diagonal units use the
two Hermitian summands in (28.7); each resulting norm is at most $2c_n$.
The already proved SVD block inequality (28.8) and tensor trace-norm
multiplicativity then give $2dc_n=10c_n$ for every complex referenced
operator. Both channels also have diamond norm one by Lemma 22.1, so
their difference is bounded by two. Formula (28.10) identifies the reset
output with precisely $\sigma_\Phi\otimes\operatorname{Tr}_{\mathrm{sys}}Z$.
This proves (37.3) by reuse of that complete amplification, without a
state-only extrapolation. For a referenced density the unchanged reference
marginal therefore factors from the limiting stationary density.
$\square$

## 38. Primary interfaces and exact boundaries of the classification

**Convention 38.1 (Standard inputs and model-specific synthesis).** The
standard support, polar, cyclic, contraction, and complete-norm tools have
the following primary versions and hypotheses. Their use is intermediate
to the full-class five-window derivations in §§33–37; the model-specific
classification and compact bound are ordinary `repo-derived` synthesis.
The standard components are `literature-attested` within the listed
conditions. No exhaustive novelty or priority conclusion is made.

| Primary source and version | Exact passage, hypotheses, and use |
| --- | --- |
| D. Burgarth, G. Chiribella, V. Giovannetti, P. Perinotti, and K. Yuasa, *Ergodic and Mixing Quantum Channels in Finite Dimensions*, [arXiv:1210.5625v3][MIX32] | Lemma 1 and Corollaries 1–2, printed pp.7–8: stationary Jordan parts and orthogonal stationary supports for CPTP maps. Lemma 2, p.9: invariant supports and stationary states on enclosures. Theorem 5 and Remark 4, p.17: stationary polar modulus of a unit-modulus eigenoperator, without global faithfulness; apply also to the adjoint operator. Theorem 9, pp.20–22, requires ergodicity and a faithful fixed state. Section 32 establishes those properties only on the actual stationary support before the cyclic argument; it does not assign them from $Q^4>0$. |
| R. Carbone and A. Jenčová, *On period, cycles and fixed points of a quantum channel*, [arXiv:1905.00857v1][CYCLE32] | §3 and §3.1, printed pp.9–11, Proposition 5, Corollary 2, Proposition 6: irreducible unital Heisenberg CP maps with a faithful normal invariant state. The applicable map is the adjoint of the faithful irreducible restriction to $R$. Equations (32.5)–(32.6) construct the actual cyclic spaces and their faithful densities. |
| S. Gaubert and Z. Qu, *Dobrushin's Ergodicity Coefficient for Markov Operators on Cones*, [arXiv:1307.4649v3][GQ32] | §7, equations (24)–(25), pp.12–13: unital CP map, CPTP dual, and the trace-norm ratio used in (37.1). Corollary 7.3, pp.13–14: coefficient one and orthogonal Kraus output spans. Lemma 7.6 and Theorems 7.7–7.8, pp.14–16: operator-space stabilization and horizon $d^2-1$. Theorem 7.8(2) uses convergence to one invariant density for every initial density, with no faithful-density premise. Theorem 6.1, p.11, supplies contraction-to-convergence. Equations (37.4)–(37.6) independently prove the needed horizon. |
| T. Theurer, D. Egloff, L. Zhang, and M. B. Plenio, *Quantifying Operations with an Application to Coherence*, [arXiv:1806.07332v2][THE] | Definition 3, equation (7), p.3, and supplemental Proposition 15, equation (35), p.8: $\Delta\Phi=\Delta\Phi\Delta$ and the fixed-output coefficient condition. Set $p(j\mid i)=Q_{ij}$. This identifies the all-input population interface and permits coherence creation; it supplies no mixing theorem by itself. |
| R. Blume-Kohout, H. K. Ng, D. Poulin, and L. Viola, *Information-preserving structures: A general framework for quantum zero-error information*, [arXiv:1006.1358v1][IPS32] | Theorem 5, p.9, concerns arbitrary CPTP maps, restricts to fixed-point support, and describes fixed states as a distortion of an algebra and fixed observables as its extension. This is structural context; the full-input asymptotic reset, including transient feeding, is proved in Theorem 36.1. |
| J. Watrous, *The Theory of Quantum Information*, author-hosted 2018 draft [TQI27] | Theorem 3.46, printed p.173: reference stabilization for arbitrary linear maps on finite complex spaces. Theorem 3.51, pp.176–177: its pure-state characterization requires Hermitian preservation, satisfied by a difference of channels. The arbitrary-complex/reference estimate used here is specifically the full SVD proof (28.7)–(28.10), applied with (37.8). |

**Convention 38.2 (Rates, half, and operational boundaries).** Theorem
30.1 remains the explicit-rate supplier on
$0<\eta<(5-\sqrt{17})/4$: its odd-step minimum is (29.6), its strict
heavy population is $a=p_0(1-\eta^{2k})>1/2$, and its coefficient is
$\kappa=2\sqrt{a(1-a)}$. Those existing cap and reference results are
reused. The general heavy-population implication at equality is false
by Proposition 28.3; Theorem 36.1 resolves the five-window threshold and
other interior parameters by its different model-specific support proof.
No closed-form worst-case $q_K$ outside that explicit interval, or
optimality of a rate or prefactor, is asserted. Proposition 36.2 rules
out a common vanishing rate on parameter sets approaching half.

At $\eta=1/2$, (36.1) asserts existence of nonmixing lifts. It does not
classify every individual Gram matrix there: the classical
measure-and-prepare lift of §14 mixes, whereas $\Phi_\circ$ does not.
The individual-half-Gram classification remains a separate open question.
The endpoints are excluded and retain their separate results in §§15 and
25. The theorems concern one homogeneous channel with fresh discarded
environments and terminal access to the retained system, not varying
channels or access to retained environments. Complete convergence to a
reset does not establish eventual entanglement breaking or a quantum
capacity claim. The stationary density need not be globally faithful.
These ordinary mathematical results supply no Lean/kernel certification,
physical or native realization, Hamiltonian, or QFT identification.

[MIX32]: https://arxiv.org/pdf/1210.5625v3
[CYCLE32]: https://arxiv.org/pdf/1905.00857v1
[GQ32]: https://arxiv.org/pdf/1307.4649v3
[IPS32]: https://arxiv.org/pdf/1006.1358v1

## 追加锚（本行以下为增补区）
