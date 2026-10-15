# Recursive relational observation: real scalar ports and boundary coordinates

## 1. Preparation, scalar ports and passive coordinates

**Assumption 1.1 (The original preparation and future menu).** Let
$\mathcal H=\mathbb C^5$ with ordered orthonormal basis
$\mathsf S=(N,2,3,5,25)$, and put $\Pi_s=e_se_s^\dagger$. Every complex
density matrix on $\mathcal H$ is an allowed input. Fix

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},\qquad U(t)=e^{-itK},\quad t\ge0.
\tag{1.1}
$$

These are precisely the hypotheses of
[QMB, Assumption 1.1](https://github.com/the-omega-institute/trureturing/blob/de4128dc7165bb668a0080dee9b94bf41f968814/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md).
The label $N$ denotes a unit vector. Quantum preparation is an independent
hypothesis: the native composition maps
[GraftAffineClosure.step, quantity and run](https://github.com/the-omega-institute/trureturing/blob/de4128dc7165bb668a0080dee9b94bf41f968814/D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean),
with $\operatorname{step}(x,y)=(y,x+y)$ and
$\operatorname{quantity}(x,y)=2x+3y$, do not supply this preparation.

An actual future protocol uses only nonnegative waits $U(t)$, the complete
five-outcome rank-one Lüders instrument
$\mathcal J_s(X)=\Pi_sX\Pi_s$, and Stop. Each protocol has finite adaptive
depth; all finite depths are included. The retained history includes
outcomes, chosen controls and stops. Initial controls and random control
resources are independent of the input, and both comparisons use the same
policy. Grouping recorded outcomes is classical postprocessing of a full
read. It does not replace that instrument by a coarse-block Lüders
instrument. There are no independent mode phases, arbitrary future
unitaries, source copies, resets, external quantum side information,
probability oracle or readable hidden Kraus record.

**Definition 1.2 (The fixed scalar-port optimization).** Let
$\mathfrak C_1$ consist of composites of fixed CPTP maps

$$
\operatorname{Enc}:M_5(\mathbb C)\longrightarrow
\bigoplus_{f\in F}M_1(\mathbb C),\qquad
\operatorname{Dec}((y_f)_f)=\sum_f\operatorname{Dec}_f(y_f),
\qquad \operatorname{Dec}_f:M_1(\mathbb C)\longrightarrow M_5(\mathbb C),
\tag{1.2}
$$

where $F$ is finite and every decoder is CPTP on its whole scalar block.
The design precedes the input and the choice of future policy. All quantum
information traverses this port, with no original-input retention,
entangled assistance or bypass. Finite classical flags are free for this
criterion, are used during decoding, and are not additionally exposed to
the later policy. All complex CPTP competitors are included.

For the full-history law $P_\rho^\pi$, define

$$
e(T)=\sup_{\rho\ge0,\ \operatorname{tr}\rho=1}
\sup_{\pi\ {\rm actual,\ finite}}
\operatorname{TV}(P_\rho^\pi,P_{T(\rho)}^\pi),
\qquad \varepsilon_1=\inf_{T\in\mathfrak C_1}e(T).
\tag{1.3}
$$

The replacement occurs once, before the common future protocol. TV is
half the $\ell^1$ distance, with its measure version for random controls.
CPTP legality includes arbitrary reference extensions; the performance
test measures only the system's actual histories. This is exactly QMB
Definitions 1.2–1.3 with $q=1$, and corresponds to ambient dimension
$D=5$, compressed dimension $d=1$, and finite classical blocks in
[Bluhm–Rauber–Wolf, Definition 4.1 and Lemmas 5.2–5.3](https://arxiv.org/html/1708.04898v4).
Their exact observable-preservation problem does not replace (1.3).

**Definition 1.3 (Real frame, effects and supplied correspondences).** Put

$$
\begin{gathered}
D=\operatorname{diag}(1,i,i,i,1),\qquad
A=-iD^\dagger KD=
\begin{pmatrix}
0&1&1&1&0\\
-1&0&0&0&-1\\
-1&0&0&0&0\\
-1&0&0&0&-1\\
0&1&0&1&0
\end{pmatrix},\\
O(t)=e^{tA}=D^\dagger U(t)D,\qquad
\Pi_J=\sum_{s\in J}\Pi_s,\qquad Q_J(t)=O(t)^T\Pi_JO(t),\\
\widehat T(X)=D^\dagger T(DXD^\dagger)D.
\end{gathered}
\tag{1.4}
$$

All channel calculations below use this frame. A transpose is taken in
this fixed frame; a dagger is the matrix adjoint, or the trace-pairing
dual of a map. Write $\operatorname{Ad}_g(X)=gXg^\dagger$. The notation
$e(S)$ for a frame channel means the transported original criterion.
The frame change is a coordinate identification, not a future control.

The credited first-read identity, QMB Theorem 2.1, is

$$
e(T)=\sup_{t\ge0}\max_{J\subseteq\mathsf S}
\|Q_J(t)-\widehat T^\dagger(Q_J(t))\|_{\rm op}.
\tag{1.5}
$$

It applies to all complex density inputs and all the histories in
Assumption 1.1. Its rank-one first read resets the conditional state to
$\Pi_s$, so a common suffix cannot increase the first-result TV.
The reverse inequality uses one full read and Stop.

QMB Theorem 5.1 identifies $\mathfrak C_1$ with finite rank-one Kraus
channels. In particular, after omitting zero terms, any competitor has

$$
\widehat T(X)=\sum_i s_i^2 a_i a_i^\dagger
\operatorname{tr}(b_i b_i^\dagger X),\qquad
\|a_i\|=\|b_i\|=1,\quad s_i>0,\quad
\sum_i s_i^2b_i b_i^\dagger=I_5.
\tag{1.6}
$$

This is the known measure-and-prepare/rank-one-Kraus equivalence of
[Horodecki–Shor–Ruskai, Theorem 4(A–D)](https://arxiv.org/html/quant-ph/0302031),
including its separate POVM condition for TP maps. The matrix marginal
in (1.6), rather than merely its trace, is retained throughout.

The channel predicate in
[FiniteStateChannel.QuantumChannel](https://github.com/the-omega-institute/trureturing/blob/de4128dc7165bb668a0080dee9b94bf41f968814/D5/S3/Quantum/Foundation/FiniteStateChannel.lean)
is complete positivity with trace preservation on all matrices. The
finite rectangular interface
[finite_kraus_quantum_channel](https://github.com/the-omega-institute/trureturing/blob/de4128dc7165bb668a0080dee9b94bf41f968814/D5/S3/Quantum/Foundation/FiniteKrausChannel.lean)
takes $K_f:\mathbb C^a\to\mathbb C^b$ and
$\sum_fK_f^\dagger K_f=I_a$. Encoder branches below have rectangular
rows $B_f:\mathbb C^5\to\mathbb C$. Equivalently embed the flag algebra
as diagonal matrices on $\mathbb C^F$ and take
$K_f=e_fB_f$, $(a,b)=(5,|F|)$; the range is diagonal and its trace is
the direct-sum trace. For each decoder take $(a,b)=(1,5)$ and the
single Kraus column $R_f$ with $R_f^\dagger R_f=1$. The branch trace
pairing is the one in
[finite_kraus_instrument_born_marginal](https://github.com/the-omega-institute/trureturing/blob/de4128dc7165bb668a0080dee9b94bf41f968814/D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean):
the sum of branch sandwich traces equals the Born weight of the sum of
$K_f^\dagger K_f$. For the decoded branches its parameters are
$n=\mathsf S$, one setting, outcomes $F$, one Kraus index per outcome,
and branch matrix $C_f=R_fB_f$. Its normalization is
$\sum_fC_f^\dagger C_f=I_5$. TP decoding makes each decoded branch
trace equal to the corresponding encoder branch trace. These are the
exact CP, TP and probability conventions used below.

## 2. A no-worse real replacement of every complex scalar port

**Definition 2.1 (Separate realification).** For a positive integer $n$,
in a fixed real frame of $\mathbb C^n$, let

$$
\mathcal R(X)=\frac{X+X^T}{2},\qquad
\mathfrak r(T)=\mathcal R\circ T\circ\mathcal R.
\tag{2.1}
$$

These are complex-linear maps. A real product channel is a finite map
$S(X)=\sum_f w_f a_fa_f^T\operatorname{tr}(b_fb_f^T X)$ with
$w_f\ge0$ and real unit vectors $a_f,b_f$. When
$\sum_fw_fb_fb_f^T=I_n$, it is a real measure-and-prepare channel.
The two unit vectors of an atom are independent.

**Theorem 2.2 (Real replacement and real finite support).** Let $T$ be
any CPTP channel on $M_n$ with a finite complex rank-one Kraus
representation. Then
$\mathfrak r(T)$ is a real measure-and-prepare CPTP channel. For every
real symmetric Hermitian effect $E$ simultaneously,

$$
\mathfrak r(T)^\dagger(E)=\mathcal R(T^\dagger(E)),\qquad
\|E-\mathfrak r(T)^\dagger(E)\|_{\rm op}
\le\|E-T^\dagger(E)\|_{\rm op}.
\tag{2.2}
$$

If $T$ commutes with conjugation by a real orthogonal matrix, then so
does $\mathfrak r(T)$. It has a real rank-one Kraus representation with
at most $[n(n+1)/2]^2$ terms. Consequently every original complex
$T\in\mathfrak C_1$ has a fixed legal scalar-port replacement with at
most $225$ flags and error no greater than $e(T)$.

Proof. Use (1.6) with $5$ replaced by $n$. Write
$a_i=u_i+iv_i$, $b_i=x_i+iy_i$ with real vectors, and set
$a_{i0}=u_i$, $a_{i1}=v_i$, $b_{i0}=x_i$, $b_{i1}=y_i$.
The explicit real matrices

$$
K_{i\alpha\beta}=s_i a_{i\alpha}b_{i\beta}^T,
\qquad \alpha,\beta\in\{0,1\},
\tag{2.3}
$$

have rank at most one and satisfy

$$
\begin{aligned}
\sum_{i,\alpha,\beta}K_{i\alpha\beta}^T K_{i\alpha\beta}
&=\sum_i s_i^2(\|u_i\|^2+\|v_i\|^2)
(x_ix_i^T+y_iy_i^T)\\
&=\mathcal R\left(\sum_i s_i^2b_ib_i^\dagger\right)=I_n.
\end{aligned}
\tag{2.4}
$$

Indeed $\|u_i\|^2+\|v_i\|^2=1$. Every sandwich by a real matrix is
completely positive on complex matrices, because on each reference
extension it is still a matrix sandwich. Thus the finite family (2.3)
is CPTP, with action

$$
\sum_i s_i^2\mathcal R(a_ia_i^\dagger)
\operatorname{tr}(\mathcal R(b_ib_i^\dagger)X)
=\mathcal R(T(\mathcal R(X))).
\tag{2.5}
$$

This also proves complete positivity of this particular composite
without requiring complete positivity of $\mathcal R$ itself.

For real symmetric $E$,
$a_i^\dagger Ea_i=u_i^TEu_i+v_i^TEv_i$ is real. Computing the dual
of (2.5) gives the first identity in (2.2). The residual
$H=E-T^\dagger(E)$ is Hermitian, so $H^T=\overline H$ and

$$
\|\mathcal R(H)\|_{\rm op}
\le\tfrac12(\|H\|_{\rm op}+\|\overline H\|_{\rm op})
=\|H\|_{\rm op}.
\tag{2.6}
$$

Complex conjugation preserves the operator norm: substitute $\bar z$
for $z$ in its unit-vector supremum. This proves the simultaneous
inequalities, which quantify over all complex input expectations of
these Hermitian residuals. Every $Q_J(t)$ is real symmetric. Equation
(1.5) therefore proves the asserted original-history error inequality.

For real orthogonal $g$, direct transposition gives
$\mathcal R\operatorname{Ad}_g=\operatorname{Ad}_g\mathcal R$.
This proves the commutation statement.

Normalize each nonzero real factor of (2.3), absorbing its squared
norms into a weight $w_f$. The normalized output-first Choi matrix is

$$
\chi_{\mathfrak r(T)}=\frac1n\sum_f w_f
(a_fa_f^T)\otimes(b_fb_f^T),\qquad
\sum_fw_f=n.
\tag{2.7}
$$

Each product projector has trace one and lies in
$\operatorname{Sym}_n(\mathbb R)\otimes\operatorname{Sym}_n(\mathbb R)$,
whose real dimension is $[n(n+1)/2]^2$. Its trace-one affine hyperplane
has dimension one less. The normalized real product projectors form a
compact set. The finite-dimensional Carathéodory theorem supplies at
most $[n(n+1)/2]^2$ terms for (2.7). Their convex hull is compact:
the indicated bounded-length convex combinations are a continuous
image of a compact product and a compact simplex. Thus the same support
bound applies to limits and averages of real product states as well.
Preserving the Choi matrix preserves the entire channel and its TP
marginal.

For $n=5$, any such representation has the exact original-coordinate
scalar realization

$$
B_f=\sqrt{w_f}\,b_f^TD^\dagger,\qquad R_f=Da_f,\qquad
\operatorname{Enc}(X)=(B_fXB_f^\dagger)_f,\qquad
\operatorname{Dec}_f(y)=R_fyR_f^\dagger.
\tag{2.8}
$$

Here $\sum_fB_f^\dagger B_f=I_5$, $R_f^\dagger R_f=1$, and the
composite Kraus matrices are $\sqrt{w_f}Da_fb_f^TD^\dagger$.
Every decoder is TP on all of $M_1$, and the sandwich argument proves
CP at every reference dimension. This realizes one finite fixed port
with flags consumed in decoding.

The positive-map compositions in Horodecki–Shor–Ruskai Theorem 4(E–F)
give a general antecedent for the CP aspect of (2.5); (2.2) supplies
the menu-specific contraction. The replacement changes the channel.
It does not identify complex separability with real product
decomposability of an unchanged real Choi matrix, the distinction in
[Caves–Fuchs–Rungta](https://arxiv.org/html/quant-ph/0009063) and
[QPC, Proposition 9.2](https://github.com/the-omega-institute/trureturing/blob/de4128dc7165bb668a0080dee9b94bf41f968814/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_PORT_COVARIANCE_AND_CERTIFIED_FRONTIER.md).
No physical application of transposition is used in (2.8). $\square$

## 3. Stationarity and the specified time reversal

**Definition 3.1 (Rotation data and reflection).** Let $r=\sqrt{17}$,
$\lambda_\pm=(5\pm r)/2$, $\omega_\pm=\sqrt{\lambda_\pm}$, and put

$$
\begin{gathered}
B=-A^2,\qquad
R_\pm=\frac{B(B-\lambda_\mp I)}
{\lambda_\pm(\lambda_\pm-\lambda_\mp)},\qquad
R_0=I-R_+-R_-,\\
d=(e_2-e_5)/\sqrt2,\qquad
u_\pm=\frac{R_\pm e_N}{\sqrt{(1\pm1/r)/2}},\qquad
v_\pm=Au_\pm/\omega_\pm,\qquad W_\pm=AR_\pm/\omega_\pm,\\
G(\theta,\phi)=R_0+\cos\theta R_++\sin\theta W_+
+\cos\phi R_-+\sin\phi W_-,\\
J=\operatorname{diag}(1,-1,-1,-1,1).
\end{gathered}
\tag{3.1}
$$

The supplied spectral result, QMB Theorem 4.1 and QPC Convention 6.1,
gives mutually orthogonal projections $R_0=dd^T,R_+,R_-$ of ranks
$1,2,2$. The vector list $(d,u_+,v_+,u_-,v_-)$ is orthonormal, and
$Au_\pm=\omega_\pm v_\pm$, $Av_\pm=-\omega_\pm u_\pm$.
In particular the normalizers in (3.1) are nonzero. The actual wait is
$O(t)=G(\omega_+t,\omega_-t)$.

A channel is stationary if it commutes with every
$\operatorname{Ad}_{O(t)}$, equivalently with $X\mapsto AX-XA$.
Let $\mathcal C_{\mathbb R,J}$ be the real measure-and-prepare TP
channels that are stationary and commute with $\operatorname{Ad}_J$.
Angles in (3.1) are mathematical coordinates for design identities.

**Theorem 3.2 (A no-worse representative in the real reflected class).**
Every original complex $T\in\mathfrak C_1$ has a representative
$S\in\mathcal C_{\mathbb R,J}$ with $e(S)\le e(T)$ and a realization
with at most $225$ fixed scalar flags. For every
$S\in\mathcal C_{\mathbb R,J}$,

$$
e(S)=\max_{J'\in\mathcal J_{15}}
\|\Pi_{J'}-S^\dagger(\Pi_{J'})\|_{\rm op},\qquad
\mathcal J_{15}=\{J'\subseteq\mathsf S:1\le|J'|\le2\}.
\tag{3.2}
$$

The maximum is attained by a pure input, wait zero, one complete mode
read, and Stop. Consequently minimizing over $\mathcal C_{\mathbb R,J}$
preserves exactly the original $\varepsilon_1$.

Proof. Use the credited no-worse stationary reduction
[QPC, Theorem 3.3](https://github.com/the-omega-institute/trureturing/blob/de4128dc7165bb668a0080dee9b94bf41f968814/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_PORT_COVARIANCE_AND_CERTIFIED_FRONTIER.md)
with $q=1$, the same $A$, all complex competitors and the same error
(1.5). It supplies a stationary $S_0\in\mathfrak C_1$ with
$e(S_0)\le e(T)$. Its averaging is legitimate for this nonnegative-wait
menu: QPC Lemma 3.1 gives recurrence and equality of every tail supremum,
and equation (3.4) there identifies a conjugated-design residual with
the original residual at $t+u$. Thus design conjugation by the actual
orbit and its compact closure preserves $e$ exactly. Convexity of $e$
and compact convexity of the rank-one-Kraus class make the mathematical
average no worse. No future negative wait or readable averaging flag
is involved in that supplier.

Apply Theorem 2.2 to $S_0$. The resulting $S_1=\mathfrak r(S_0)$ is
stationary, real measure-and-prepare, and no worse. Directly from the
displayed $A$ and $J$,

$$
JAJ=-A,\qquad J\Pi_sJ=\Pi_s,\qquad
JR_iJ=R_i\quad(i=0,+,-).
\tag{3.3}
$$

The last identities also follow because $R_i$ are polynomials in
$-A^2$. In the adapted vector basis, $J$ acts as
$(-1,1,-1,1,-1)$: $Jd=-d$, $Ju_\pm=u_\pm$, and
$Jv_\pm=-v_\pm$. Hence $JG(\theta,\phi)J=G(-\theta,-\phi)$.

Let $S_1^J=\operatorname{Ad}_J S_1\operatorname{Ad}_J$.
Conjugating its real input and output vectors by $J$ preserves their
norms, the matrix TP marginal and rank-one Kraus legality. Equation
(3.3) shows that $S_1^J$ is stationary. For any stationary channel $V$,
QPC's first-read consequence is

$$
Q_{J'}(t)-V^\dagger(Q_{J'}(t))
=O(t)^T[\Pi_{J'}-V^\dagger(\Pi_{J'})]O(t).
\tag{3.4}
$$

At zero wait the residual of $S_1^J$ is
$J[\Pi_{J'}-S_1^\dagger(\Pi_{J'})]J$. Thus (3.4) and norm invariance
prove $e(S_1^J)=e(S_1)$ for the original menu. Define
$S=(S_1+S_1^J)/2$. Concatenating scaled real Kraus families proves its
legality. It is stationary, commutes with $\operatorname{Ad}_J$, and
convexity gives $e(S)\le e(S_1)$. Theorem 2.2's real-product support
argument reduces its realization to at most $225$ flags without changing
this channel.

Equation (3.4) makes every event norm independent of the wait. Since TP
means $S^\dagger(I)=I$, complementary residuals have opposite signs;
the empty and full residuals vanish. All events are therefore represented
by the five singletons and ten pairs, proving (3.2). For a maximizing
event, take a unit eigenvector of its real symmetric residual with an
eigenvalue of largest absolute value. The corresponding physical pure
input is $Dvv^TD^\dagger$. A full read at $t=0$ and Stop gives an
event probability difference equal to that eigenvalue. Its TV is both
at least its magnitude and at most (3.2), proving attainment.

The original minimizer exists by QMB Theorem 5.1. Applying this
replacement to it, and using inclusion of the resulting channels in
the original class, proves equality of the two minima. The invariance
used here is the specified $J$ and the actual walk closure. It does not
require the full $O(5)$ menu invariance refuted by QPC Proposition 9.1.
$\square$

## 4. The faithful twelve-coordinate channel space

**Definition 4.1 (An orthonormal symmetric-matrix basis).** Use
$\langle X,Y\rangle=\operatorname{tr}(XY)$ on
$\operatorname{Sym}_5(\mathbb R)$, and for orthogonal unit vectors set
$F(a,b)=(ab^T+ba^T)/\sqrt2$. Define

$$
H_0=R_0,\qquad H_+=R_+/\sqrt2,\qquad H_-=R_-/\sqrt2,
\qquad \tau=(1,\sqrt2,\sqrt2)^T.
\tag{4.1}
$$

Thus $I=\sum_i\tau_iH_i$. The six ordered orthonormal pairs
$(F_{\nu1},F_{\nu2})$ are

$$
\begin{aligned}
\nu=+ &: \quad F(d,u_+),\quad F(d,v_+),\\
\nu=- &: \quad F(d,u_-),\quad F(d,v_-),\\
\nu=2+ &: \quad (u_+u_+^T-v_+v_+^T)/\sqrt2,\quad F(u_+,v_+),\\
\nu=2- &: \quad (u_-u_-^T-v_-v_-^T)/\sqrt2,\quad F(u_-,v_-),\\
\nu=\Delta &: \quad
\frac{F(u_+,u_-)+F(v_+,v_-)}{\sqrt2},\quad
\frac{F(v_+,u_-)-F(u_+,v_-)}{\sqrt2},\\
\nu=\Sigma &: \quad
\frac{F(u_+,u_-)-F(v_+,v_-)}{\sqrt2},\quad
\frac{F(v_+,u_-)+F(u_+,v_-)}{\sqrt2}.
\end{aligned}
\tag{4.2}
$$

Let $\mathcal N=\{+,-,2+,2-,\Delta,\Sigma\}$ and define
$P_\nu(E)=\sum_{a=1}^2\langle F_{\nu a},E\rangle F_{\nu a}$.
Together with the three $H_i$, (4.2) gives fifteen orthonormal matrices.
For arbitrary complex matrices all formulas extend complex linearly
after replacing $X$ by $(X+X^T)/2$.

**Theorem 4.2 (Exact commutant and TP coordinates).** A real-linear map
on $\operatorname{Sym}_5(\mathbb R)$ commutes with all the rotations
$\operatorname{Ad}_{G(\theta,\phi)}$ and with $\operatorname{Ad}_J$
if and only if it has the unique form

$$
S_{M,\eta}(E)=\sum_{i,j\in\{0,+,-\}}
M_{ij}\langle H_j,E\rangle H_i
+\sum_{\nu\in\mathcal N}\eta_\nu P_\nu(E),
\qquad M\in M_3(\mathbb R),\quad \eta\in\mathbb R^6.
\tag{4.3}
$$

Its complex-linear extension annihilating transpose-antisymmetric
matrices is TP exactly when

$$
M^T\tau=\tau.
\tag{4.4}
$$

These are three independent affine equations on fifteen real
coefficients. The six entries $M_{+j},M_{-j}$ and the six $\eta_\nu$
are twelve affine coordinates, with

$$
M_{0j}=\tau_j-\sqrt2(M_{+j}+M_{-j}).
\tag{4.5}
$$

Every $S\in\mathcal C_{\mathbb R,J}$ has this form on all complex
matrices. No condition $M=M^T$ or $M\tau=\tau$ is imposed.

Proof. The torus action on the vector complexification has weights
$0,e_1,-e_1,e_2,-e_2$. On its symmetric square the zero weight occurs
three times. The nonzero weights are

$$
\pm e_1,\quad\pm e_2,\quad\pm2e_1,\quad\pm2e_2,
\quad\pm(e_1-e_2),\quad\pm(e_1+e_2),
\tag{4.6}
$$

each once. Indeed these are all fifteen unordered sums, counting zero
three times. The corresponding real decomposition is the three
trivial directions (4.1) and the six rotation planes (4.2). The formulas
can also be checked by rotating $u_\pm,v_\pm$: the last two pairs
rotate through $\theta-\phi$ and $\theta+\phi$, respectively.
Each displayed matrix has unit squared norm, and matrices from
different displayed subspaces are orthogonal. In the mixed planes,
the four original $F$ matrices are orthonormal and their sum/difference
pairs are orthogonal changes of basis. These observations prove the
normalizations and exhaust the dimension $3+6\cdot2=15$.

Distinct pairs of opposite nonzero characters in (4.6) are
inequivalent. An intertwiner between different such real planes is
zero: after complexification it would map a character line to a
different character, and some torus element gives different scalars.
The same argument excludes cross terms with the trivial part. On a
single rotation plane the matrices commuting with all rotations are
$aI_2+b\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$,
as follows by commuting with a quarter turn. On the trivial part the
commutant is arbitrary $M_3(\mathbb R)$.

Conjugation by $J$ fixes every $H_i$. Its matrices on the first two
pairs in (4.2) are $\operatorname{diag}(-1,1)$ and on each other pair
are $\operatorname{diag}(1,-1)$. A reflection anticommutes with the
nonzero skew matrix in the preceding commutant. Requiring commutation
with that reflection forces $b=0$ in each plane. The surviving
coefficients are exactly (4.3), and the converse follows from the same
decomposition.

QPC Lemma 6.2 identifies the closure of the actual nonnegative orbit
with this torus. Its hypothesis is met because
$\omega_+^2/\omega_-^2=(21+5\sqrt{17})/4$ is irrational, so
$\omega_+/\omega_-$ is irrational. Continuity therefore makes actual
stationarity equivalent to commuting with all these rotations. A real
product channel annihilates $X^T=-X$, since $b^TXb=0$, and maps real
symmetric matrices to real symmetric matrices. Thus its action on
that space determines its action on every complex matrix.

Finally, every $F_{\nu a}$ is traceless. If $t_j=\langle H_j,E\rangle$,
then $\operatorname{tr}S(E)=\tau^TMt$ and
$\operatorname{tr}E=\tau^Tt$. This proves (4.4); skew inputs have zero
trace and zero output. The three column equations are independent
because each involves its own $M_{0j}$ with coefficient one.
Equation (4.5) follows. The identity $M\tau=\tau$ would instead impose
unitality, and $M=M^T$ would impose self-adjointness on the invariant
block. Neither follows from TP.

This is a decomposition of the observable-space representation, not
of individual rank-one Kraus operators. Consequently the
definite-character obstruction of QPC Proposition 9.3 does not apply
to the argument. In particular,
[unitary_kraus_mixing_invariance](https://github.com/the-omega-institute/trureturing/blob/de4128dc7165bb668a0080dee9b94bf41f968814/D5/S3/QuantumChannels/UnitaryKrausMixingInvariance.lean),
whose hypothesis is column orthogonality of a Kraus mixing matrix,
is not used to preserve individual ranks. $\square$

## 5. The exact separable atom cone and finite realization

**Definition 5.1 (Product-atom coefficients and the cone).** For real
unit $a,b\in\mathbb R^5$, define

$$
\begin{gathered}
h_i(a)=\langle H_i,aa^T\rangle
=a^TR_ia/\sqrt{d_i},\qquad (d_0,d_+,d_-)=(1,2,2),\\
z_\nu(a)=(a^TF_{\nu1}a,\ a^TF_{\nu2}a)^T,\\
k(a,b)=(M(a,b),\eta(a,b)),\qquad
M(a,b)=h(a)h(b)^T,\qquad
\eta_\nu(a,b)=\tfrac12 z_\nu(a)^Tz_\nu(b),\\
\mathcal K=\operatorname{cone}\{k(a,b):a,b\in\mathbb R^5,
\ \|a\|=\|b\|=1\}.
\end{gathered}
\tag{5.1}
$$

Here cone means finite sums with nonnegative coefficients, with no
restriction $a=b$. Define the output-first unnormalized Choi map

$$
Z(M,\eta)=\sum_{i,j}M_{ij}H_i\otimes H_j
+\sum_{\nu\in\mathcal N}\eta_\nu
(F_{\nu1}\otimes F_{\nu1}+F_{\nu2}\otimes F_{\nu2}).
\tag{5.2}
$$

For the associated channel its normalized Choi matrix is $Z(M,\eta)/5$.
No positive-semidefinite, PPT or extension relaxation is included in
the definition of $\mathcal K$.

**Theorem 5.2 (Exact cone, finite quadrature and marginal).** The maps
in $\mathcal C_{\mathbb R,J}$ correspond bijectively to

$$
\mathcal F=\{(M,\eta)\in\mathcal K:M^T\tau=\tau\}.
\tag{5.3}
$$

The cone $\mathcal K$ is closed. Every point of $\mathcal F$ yields
one legal original scalar port with at most $225$ fixed flags and
whole-block CPTP decoding. The normalized Choi marginal is exactly
$\operatorname{Tr}_{\rm out}(Z/5)=I_5/5$.

For each generator in (5.1), its full unnormalized Choi matrix has
the explicit finite expression

$$
Z(k(a,b))=\frac1{50}\sum_{\epsilon=0}^1\sum_{k,l=0}^4
(g_{\epsilon kl}aa^Tg_{\epsilon kl}^T)
\otimes(g_{\epsilon kl}bb^Tg_{\epsilon kl}^T),\qquad
g_{\epsilon kl}=J^\epsilon G(2\pi k/5,2\pi l/5).
\tag{5.4}
$$

Proof. Start with the atom
$\Gamma_{a,b}(X)=aa^T\operatorname{tr}(bb^TX)$, without imposing
TP on this single atom. Average
$\operatorname{Ad}_g\Gamma_{a,b}\operatorname{Ad}_{g^{-1}}$
over the two-angle torus and then over $I,J$. It is an average of
real product atoms with vectors $ga,gb$. It annihilates the
transpose-antisymmetric part and lies in the commutant of Theorem 4.2.

On the trivial three-dimensional part the atom's matrix is
$h(a)h(b)^T$, unchanged by the average. On a nontrivial orthonormal
pair the unaveraged block is $z_\nu(a)z_\nu(b)^T$. Its rotation
average is a scalar plus a skew matrix. The scalar is half its trace,
namely $z_\nu(a)^Tz_\nu(b)/2$. Averaging the reflection removes the
skew matrix. Cross blocks between distinct characters average to
zero. This proves exactly (5.1), including the factor $1/2$ in every
nontrivial plane. Since all the matrix bases in (5.2) are real
symmetric, vectorizing the map $P\operatorname{tr}(QX)$ gives
unnormalized Choi matrix $P\otimes Q^T=P\otimes Q$. This proves the
normalization in (5.2).

For the finite equality (5.4), each coordinate of $G(\theta,\phi)a$
or $G(\theta,\phi)b$ is a linear combination of a constant and
frequencies $\pm e_1,\pm e_2$. A product-projector entry uses four
such factors. Its Fourier support is contained in
$\{(m,n):|m|+|n|\le4\}$. The product of the two five-point circle
sums preserves exactly the zero Fourier coefficient: the only pair
in this support with both entries divisible by five is $(0,0)$.
Thus the $25$-point sum equals the full two-circle integral entry by
entry. The extra two-point sum implements the reflection average.
This proves (5.4) on all matrix coefficients and hence on every
complex matrix input. Its angle constants have exact algebraic
coefficients, for example

$$
\cos(2\pi/5)=\frac{\sqrt5-1}{4},\quad
\cos(4\pi/5)=-\frac{\sqrt5+1}{4},\quad
\sin(2\pi/5)=\frac{\sqrt{10+2\sqrt5}}4,\quad
\sin(4\pi/5)=\frac{\sqrt{10-2\sqrt5}}4.
\tag{5.5}
$$

The other values follow by reflection. No continuous flag or physical
choice of independent angles is needed in this finite identity.

For necessity in (5.3), write a real product channel in
$\mathcal C_{\mathbb R,J}$ as a finite sum
$\sum_fw_f\Gamma_{a_f,b_f}$. It is unchanged by the preceding average.
Linearity makes its coordinates $\sum_fw_fk(a_f,b_f)\in\mathcal K$.
Theorem 4.2 gives its TP equations. Conversely, a finite nonnegative
sum of the generators is, by (5.4), a finite real product CP map.
It has exactly the coefficients in that sum; imposing (4.4) makes
it TP. Theorem 4.2 supplies stationarity and reflection commutation.
This proves both directions and, by uniqueness of (4.3), bijectivity.

For clarity the matrix marginal follows directly from (5.2):

$$
\operatorname{Tr}_{\rm out} Z(M,\eta)
=\sum_j(M^T\tau)_jH_j.
\tag{5.6}
$$

There are no omitted marginal components, since every
$F_{\nu a}$ is traceless. Equation (4.4) is therefore exactly the
full marginal $I_5$, or $I_5/5$ after normalization.

Let $\ell(M,\eta)=\tau^TM\tau$. On every generator,
$\tau^Th(a)=\|a\|^2=1$ and $\tau^Th(b)=1$, so $\ell(k(a,b))=1$.
The generator set is compact, being a continuous image of two unit
spheres. Its convex hull is compact in this fifteen-dimensional
space. If a sequence in its cone converges, its total weights are
the convergent nonnegative numbers $\ell(M,\eta)$. After taking a
subsequence, the normalized convex combinations converge in that
compact hull. Multiplying by the limiting weight proves membership
of the limit in the cone, including zero limiting weight. Hence
$\mathcal K$ is closed. On the TP slice,

$$
\ell(M,\eta)=\tau^T\tau=5.
\tag{5.7}
$$

Thus $Z/5$ is in the compact convex hull of normalized real product
projectors. The real-product Carathéodory argument of Theorem 2.2
replaces the entire finite sum (5.4), across all its generators, by
at most $225$ product projectors without changing $Z/5$. Writing
their coefficients as $w_f/5$ gives
$\sum_fw_fb_fb_f^T=I_5$ from (5.6). Formula (2.8) then realizes
exactly this channel. The finite decomposition need not transform
character by character; only its summed channel has the symmetries.

The separable Choi and rank-one Kraus framework is the credited
Horodecki–Shor–Ruskai correspondence. The averaging framework also
appears in
[Nechita–Park, §2.1](https://arxiv.org/html/2403.03667v2).
Their orthogonal and diagonal-orthogonal covariance classes are
different from the present walk torus with $J$. Likewise the Cartan
symmetric-pair groups in
[Prudhoe, §§2–4](https://arxiv.org/html/2501.03959v3)
do not license enlarging this actual menu's symmetry. The cone and
the exact marginal above are retained together, rather than importing
an entanglement threshold from either of those other classes.
$\square$

## 6. All fifteen events and the unchanged original optimization

**Definition 6.1 (Exact event matrices in the coordinates).** For every
$J'\in\mathcal J_{15}$ set

$$
t_{J'}=(\langle H_i,\Pi_{J'}\rangle)_{i=0,+,-},\qquad
E_{J',\nu}=P_\nu(\Pi_{J'}),
\tag{6.1}
$$

and define the real symmetric residual

$$
\mathcal H_{J'}(M,\eta)
=\sum_i[t_{J'}-M^Tt_{J'}]_iH_i
+\sum_{\nu\in\mathcal N}(1-\eta_\nu)E_{J',\nu}.
\tag{6.2}
$$

The five singleton vectors are determined by the following exact
length table from QMB equation (4.3):

$$
\begin{array}{c|ccc}
s&r_{s0}&r_{s+}&r_{s-}\\\hline
N&0&(1+1/r)/2&(1-1/r)/2\\
2&1/2&(1+3/r)/4&(1-3/r)/4\\
3&0&(1-3/r)/2&(1+3/r)/2\\
5&1/2&(1+3/r)/4&(1-3/r)/4\\
25&0&(1-1/r)/2&(1+1/r)/2
\end{array},\qquad
t_{\{s\}}=(r_{s0},r_{s+}/\sqrt2,r_{s-}/\sqrt2)^T.
\tag{6.3}
$$

For a pair add its two singleton $t$ vectors. Every remaining
coefficient is explicitly

$$
E_{J',\nu}=\sum_{a=1}^2
\left(\sum_{s\in J'}e_s^TF_{\nu a}e_s\right)F_{\nu a}.
\tag{6.4}
$$

Thus (3.1), (4.1)–(4.2) and (6.2)–(6.4) specify every matrix entry
of all fifteen residuals by exact algebraic coefficients.

**Theorem 6.2 (An exact twelve-coordinate separable-cone minimax).**
The original unrestricted complex scalar-port value is exactly

$$
\boxed{
\varepsilon_1=
\min\left\{r_0\ge0:
\begin{array}{l}
(M,\eta)\in\mathcal K,\quad M^T\tau=\tau,\\
-r_0I_5\preceq\mathcal H_{J'}(M,\eta)\preceq r_0I_5
\quad\text{for every }J'\in\mathcal J_{15}
\end{array}\right\}.}
\tag{6.5}
$$

The threshold predicate in braces is equivalent to the existence of
an original legal complex scalar port with $e(T)\le r_0$.
Every feasible coordinate tuple has an original finite realization
with at most $225$ flags and exact error
$\max_{J'\in\mathcal J_{15}}\|\mathcal H_{J'}(M,\eta)\|_{\rm op}$.
That error is attained at actual wait zero. All fifteen event
constraints are kept.

Proof. On the invariant three-dimensional part the adjoint of (4.3)
has matrix $M^T$. On every nontrivial orthonormal pair it has scalar
$\eta_\nu$, because those blocks are scalar and real. Expanding
$\Pi_{J'}$ in the complete basis gives

$$
\Pi_{J'}-S_{M,\eta}^\dagger(\Pi_{J'})
=\mathcal H_{J'}(M,\eta).
\tag{6.6}
$$

For a real symmetric matrix the two Loewner inequalities in (6.5)
are equivalent to its operator norm being at most $r_0$.
Theorem 5.2 makes every feasible tuple a legal fixed port, and
Theorem 3.2 makes its norm maximum exactly the error for all complex
inputs and all original finite histories. The attaining input and
zero-wait full-read protocol are those in Theorem 3.2; no limiting
angle needs to be synthesized as an actual wait.

Conversely, given any original complex competitor with error at most
$r_0$, Theorem 3.2 constructs a no-worse real stationary reflected
channel. Theorems 4.2 and 5.2 give its feasible coordinates, and
(6.6) supplies every required inequality. This proves the threshold
equivalence and equality of infima. The original minimum exists;
alternatively (5.7) makes the coefficient slice compact, because it
is five times the compact generator hull intersected with closed
TP equations. The residual maximum is continuous. Thus the displayed
minimum is attained.

Explicitly, the events retained are the five singletons and
$\{N,2\},\{N,3\},\{N,5\},\{N,25\},\{2,3\},\{2,5\},\{2,25\},
\{3,5\},\{3,25\},\{5,25\}$. Pair constraints are sums of singleton
residual matrices, but their norm constraints have not been discarded.
Complementation uses TP, not unitality.

Equation (6.5) retains the exact product-atom cone. The PPT symmetric
extension tests of
[Doherty–Parrilo–Spedalieri, §§II–VI](https://arxiv.org/html/quant-ph/0308032)
give outer separability approximations and dual witnesses, not a
replacement of this cone by one finite SDP level. With TP and all
event inequalities retained, an outer feasible set can yield a
necessary lower bound when minimizing $r_0$; its feasible point does
not by itself construct a scalar port. The affine-constrained
separability formulations in
[Ohst et al., §3.3 and Appendix C](https://arxiv.org/html/2411.08110v2)
provide a related framework, but their channel-discrimination testers
have different input/output normalization and can include memory and
joint measurements. Here the exact normalization is (5.6), and the
performance tests are exactly (6.2). Similarly,
[Watrous, Theorems 1–2 and §3](https://arxiv.org/html/0901.4709v2)
supports SDP duality for the specified SDP; its completely bounded
norm objective is different from (1.3). No such alternative objective
or unevaluated relaxed optimum is used in (6.5). $\square$

## 7. The scope of affine minimality

**Theorem 7.1 (Full affine dimension of the no-worse channel class).**
The set $\mathcal F$ has nonempty relative interior in the
twelve-dimensional affine space (4.4). Therefore any faithful affine
encoding of all the channels in $\mathcal C_{\mathbb R,J}$ into
$\mathbb R^m$ requires $m\ge12$. This assertion concerns this
specified channel class, not a smallest nonlinear optimization or a
smallest number of event inequalities.

Proof. In any real orthonormal vector basis $f_1,\ldots,f_5$, take
the following $25$ trace-one projectors:

$$
P_i=f_if_i^T\quad(1\le i\le5),\qquad
P_{ij}^\pm=\frac{(f_i\pm f_j)(f_i\pm f_j)^T}{2}
\quad(i<j).
\tag{7.1}
$$

They span $\operatorname{Sym}_5(\mathbb R)$: the $P_i$ give its
diagonal basis, and
$P_{ij}^+-P_{ij}^-=f_if_j^T+f_jf_i^T$ gives every off-diagonal
basis matrix. Moreover,

$$
\sum_iP_i+\sum_{i<j}(P_{ij}^++P_{ij}^-)=5I_5.
\tag{7.2}
$$

The $625$ ordered products of these $25$ projectors span the full
$225$-dimensional real tensor space
$V=\operatorname{Sym}_5(\mathbb R)\otimes
\operatorname{Sym}_5(\mathbb R)$. They all have trace one and have
strictly positive uniform average $Z_*=I_5\otimes I_5/25$.
Their affine hull is the entire trace-one hyperplane in $V$:
any linear combination representing a trace-zero vector has total
coefficient zero, by taking its trace. Their differences therefore
span the trace-zero subspace.

This strictly positive average is an interior point of their convex
hull within that hyperplane. To see this directly, select finitely
many of the projector differences spanning the trace-zero space.
A sufficiently small vector there has a linear representation by
these differences with all coefficient changes smaller in magnitude
than $1/625$. Adding those changes to the uniform positive weights
keeps all weights nonnegative and their sum one. This produces a
whole relative neighborhood of $Z_*$. In particular the convex body
of real-separable trace-one matrices contains such a neighborhood.

Under (5.2), the torus-and-$J$ invariant subspace of $V$ has linear
dimension $15$ by Theorem 4.2. Its trace-one hyperplane has dimension
$14$, and $Z_*$ is invariant. Intersect the preceding neighborhood
with this invariant hyperplane. Every point of that intersection is
real-separable and invariant, so averaging its real product
decomposition expresses it by the generators of (5.1), as in
Theorem 5.2. Thus it is a neighborhood in the invariant
real-separable trace-one body as well.

The normalized TP condition is
$\operatorname{Tr}_{\rm out}\chi=I_5/5$. In the unnormalized
coordinates it is the three independent equations $M^T\tau=\tau$.
The trace equation $\tau^TM\tau=5$ is one consequence of these
equations. On its trace-fixed hyperplane the other two are
independent: (5.6) allows the three invariant marginal coordinates
to vary freely before fixing their trace, since each column of $M$
can be varied independently. Hence imposing the marginal removes
exactly two more dimensions, giving $14-2=12$.

The center is the completely depolarizing channel

$$
S_*(X)=\operatorname{tr}(X)I_5/5,\qquad
M_* =\tau\tau^T/5,\qquad \eta_*=0,\qquad
\chi_*=I_5\otimes I_5/25.
\tag{7.3}
$$

It satisfies the marginal. Intersecting its invariant relative
neighborhood with that affine marginal space leaves a relative
neighborhood of dimension twelve. Uniqueness of (4.3) transfers
this neighborhood to $\mathcal F$.

If an affine encoding into $\mathbb R^m$ were injective on this
neighborhood, its linear part would be injective on its
twelve-dimensional direction space: a nonzero kernel direction
would give two sufficiently close distinct feasible points with
the same encoding. Rank-nullity implies $m\ge12$.

The assertion is about distinguishing every channel in this class.
It does not assert that every original complex channel is unchanged
by the no-worse replacement, that an optimizer needs twelve free
parameters, or that fewer variables cannot describe the single
optimal value. $\square$

**Definition 7.2 (The remaining value and resource distinctions).** The
unrestricted exact-value problem is to evaluate the minimum (6.5),
with its entire cone $\mathcal K$, matrix marginal and fifteen norm
constraints, and exhibit a matching legal attaining port. The
coordinate bijection and affine-dimension statement specify that
problem but do not evaluate its minimum. The lower of QPC Theorem
6.4 and the sufficient construction of
[QFA, Theorem 5.1](https://github.com/the-omega-institute/trureturing/blob/de4128dc7165bb668a0080dee9b94bf41f968814/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_FINITE_PORT_ATTAINMENT.md)
are separate quantitative assertions; neither is a premise of
Theorems 2.2–7.1.

The boundary coordinates describe a class of fixed quantum channels.
Exact coefficient descriptions, finite flag counts and whole-block
CPTP design are distinct resources from coefficient synthesis,
finite precision, state-preparation acquisition, clocks, storage
duration and physical transport. Mutual recovery of native tree
relations, space, time, boundary and memory additionally requires
maps and hypotheses connecting those objects to Assumption 1.1.

## 追加锚（本行以下为增补区）
