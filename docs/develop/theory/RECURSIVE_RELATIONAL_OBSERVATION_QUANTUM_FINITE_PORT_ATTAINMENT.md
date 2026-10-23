# Recursive relational observation: an attained fourteen-flag quantum port

**Assumption 1.1 (The five-mode preparation).** Let $\mathcal H=\mathbb C^5$
with ordered orthonormal basis $\mathsf S=(N,2,3,5,25)$, and write
$\Pi_s=e_se_s^\dagger$. Every complex density matrix on $\mathcal H$ is an
allowed input. Fix

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},
\qquad U(t)=e^{-itK},\quad t\ge0.
\tag{1.1}
$$

These are exactly the preparation hypotheses of
[QMB, Assumption 1.1](https://github.com/the-omega-institute/trureturing/blob/65e4b82851f0d321f9211ef6cb7ef2bb343c9306/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md).
Here $N$ labels a unit vector. This preparation is an independent
hypothesis; the native composition maps
[GraftAffineClosure.step, quantity, run](https://github.com/the-omega-institute/trureturing/blob/65e4b82851f0d321f9211ef6cb7ef2bb343c9306/D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.lean)
do not supply it.

**Definition 1.2 (The original menu, port class and error).** An actual
future protocol uses only nonnegative waits $U(t)$, the complete five-outcome
rank-one Lüders instrument
$\mathcal J_s(X)=\Pi_sX\Pi_s$, and Stop. Each protocol has finite adaptive
depth, and every finite depth is included. The full history retains outcomes,
chosen controls and stops. Initial controls and random control resources
are independent of the input; both compared inputs use the same policy.
Grouping recorded outcomes is classical postprocessing of the full read,
not a coarse-block Lüders instrument. The menu has no independent mode
phases, arbitrary unitaries, source copies, resets, external quantum side
information, probability oracle or accessible hidden Kraus record.

For $1\le q\le5$, let $\mathfrak C_q$ consist of the composites of fixed
CPTP maps

$$
\operatorname{Enc}:M_5(\mathbb C)\longrightarrow
\bigoplus_{f\in F}M_q(\mathbb C),\qquad
\operatorname{Dec}((Y_f)_f)=\sum_f\operatorname{Dec}_f(Y_f),
\quad \operatorname{Dec}_f:M_q(\mathbb C)\longrightarrow M_5(\mathbb C),
\tag{1.2}
$$

where $F$ is finite and every $\operatorname{Dec}_f$ is CPTP on its whole
block. The encoder and decoders are fixed before the input and the choice
of future protocol. All quantum information traverses the stated port,
with no original-input retention, entangled assistance or bypass. Finite
classical flags are free for this $q$ criterion, are used during decoding,
and are not additionally exposed to the future policy. In particular,
$\mathfrak C_q$ includes every legal complex CPTP design, without a
reality, unitality, covariance or projection restriction.

For the retained-history law $P_\rho^\pi$, put

$$
e(T)=\sup_{\rho\in\mathcal D(\mathcal H)}
\sup_{\pi\ {\rm actual,\ finite}}
\operatorname{TV}(P_\rho^\pi,P_{T(\rho)}^\pi),
\qquad
\varepsilon_q=\inf_{T\in\mathfrak C_q}e(T).
\tag{1.3}
$$

The input is replaced once before the common future protocol. TV is half
the $\ell^1$ distance, with its usual measure version for randomized
controls. Complete positivity includes all reference extensions; the
performance criterion tests only the system histories. This is the
contract of QMB Definitions 1.2–1.3, also used in
[QPC, Definitions 1.2–1.3](https://github.com/the-omega-institute/trureturing/blob/65e4b82851f0d321f9211ef6cb7ef2bb343c9306/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_PORT_COVARIANCE_AND_CERTIFIED_FRONTIER.md).
It is measurement-relative compression with ambient dimension $D=5$ and
compressed dimension $d=q$ in
[Bluhm–Rauber–Wolf, Definition 4.1 and Lemmas 5.2–5.3](https://arxiv.org/html/1708.04898v4).
Their exact observable-preservation and finite-support results do not
identify the approximate value in (1.3).

**Definition 1.3 (Passive spectral coordinates).** Set

$$
\begin{gathered}
r=\sqrt{17},\qquad D=\operatorname{diag}(1,i,i,i,1),\qquad
A=-iD^\dagger KD,\qquad O(t)=e^{tA}=D^\dagger U(t)D,\\
B=-A^2,\qquad \lambda_\pm=(5\pm r)/2,\qquad
R_\pm=\frac{B(B-\lambda_\mp I)}
{\lambda_\pm(\lambda_\pm-\lambda_\mp)},\qquad R_0=I-R_+-R_-,\\
d=(e_2-e_5)/\sqrt2,\qquad
W_\pm=AR_\pm/\sqrt{\lambda_\pm},\qquad
u_\pm=\frac{R_\pm e_N}{\sqrt{(1\pm1/r)/2}},\\
w_\pm(\theta)=\cos\theta\,u_\pm+\sin\theta\,W_\pm u_\pm .
\end{gathered}
\tag{1.4}
$$

The spectral data are those of QMB Theorem 4.1 and QPC Convention 6.1:
$R_0=dd^T,R_+,R_-$ are mutually orthogonal projections of ranks $1,2,2$,
$W_\pm^T=-W_\pm$, $W_\pm^2=-R_\pm$, and
$u_\pm,W_\pm u_\pm$ are orthonormal bases of their planes.
For example, in the reordered splitting $(N,25)\mid(2,3,5)$,

$$
A=\begin{pmatrix}0&C\\-C^T&0\end{pmatrix},\qquad
C=\begin{pmatrix}1&1&1\\1&0&1\end{pmatrix},\qquad
CC^T=\begin{pmatrix}3&2\\2&2\end{pmatrix}.
\tag{1.5}
$$

The two eigenvalues of $CC^T$ solve $\lambda^2-5\lambda+2=0$.
Its plus projection $G_+$ is
$\frac12 I_2+\frac1{2r}\left(\begin{smallmatrix}1&4\\4&-1\end{smallmatrix}\right)$;
the right plus projection is $C^TG_+C/\lambda_+$.
These formulas give (1.4), its nonzero normalizers, and the stated
orthogonality identities directly.

A transpose refers to this fixed real frame, and $\dagger$ denotes
adjoint or the trace-pairing dual of a map. The matrices

$$
G(\theta,\phi)=R_0+\cos\theta R_++\sin\theta W_+
+\cos\phi R_-+\sin\phi W_-
\tag{1.6}
$$

are mathematical coordinates for plane rotations. The actual wait is
$O(t)=G(\sqrt{\lambda_+}t,\sqrt{\lambda_-}t)$.
Neither $D$ nor independent choices of the two angles are additional future
controls.

**Definition 2.1 (Fourteen explicit vector flags).** The following lists
give exact real coefficient pairs:

$$
\begin{array}{c|cc}
k&c_k&s_k\\ \hline
0&1&0\\
1&-1/2&\sqrt3/2\\
2&-1/2&-\sqrt3/2
\end{array}
\qquad
\begin{array}{c|cc}
k&C_k&S_k\\ \hline
0&1&0\\
1&(\sqrt5-1)/4&\sqrt{10+2\sqrt5}/4\\
2&-(\sqrt5+1)/4&\sqrt{10-2\sqrt5}/4\\
3&-(\sqrt5+1)/4&-\sqrt{10-2\sqrt5}/4\\
4&(\sqrt5-1)/4&-\sqrt{10+2\sqrt5}/4
\end{array}.
\tag{2.1}
$$

Thus $(c_k,s_k)=(\cos(2\pi k/3),\sin(2\pi k/3))$ and
$(C_k,S_k)=(\cos(2\pi k/5),\sin(2\pi k/5))$. Define the disjoint flag set

$$
F=\{(\mathrm A,k,\ell):0\le k,\ell<3\}
\sqcup\{(\mathrm B,k):0\le k<5\}
\tag{2.2}
$$

and, for every listed flag, the unit vector and positive coefficient

$$
\begin{aligned}
v_{\mathrm A,k,\ell}
&=\sqrt{\frac25}(c_ku_++s_kW_+u_+)
+\sqrt{\frac35}(c_\ell u_-+s_\ell W_-u_-),
&c_{\mathrm A,k,\ell}&=\frac{10}{27},\\
v_{\mathrm B,k}
&=\sqrt{\frac35}d+\sqrt{\frac25}(C_ku_++S_kW_+u_+),
&c_{\mathrm B,k}&=\frac13.
\end{aligned}
\tag{2.3}
$$

Here the subscripted $c_f$ is a flag weight, distinct from the circle
coefficient $c_k$ in (2.1). Write

$$
P_f=v_fv_f^T,\qquad
S(X)=\sum_{f\in F}c_fP_fXP_f,\qquad
T_*(X)=DS(D^\dagger XD)D^\dagger.
\tag{2.4}
$$

All fourteen flags, weights and vectors are fixed algebraic data.

**Lemma 2.2 (Exact finite orbit identity and normalization).** For

$$
v_{\mathrm A}(\theta,\phi)
=\sqrt{2/5}\,w_+(\theta)+\sqrt{3/5}\,w_-(\phi),\qquad
v_{\mathrm B}(\theta)=\sqrt{3/5}\,d+\sqrt{2/5}\,w_+(\theta),
\tag{2.5}
$$

let $P_{\mathrm A}=v_{\mathrm A}v_{\mathrm A}^T$ and
$P_{\mathrm B}=v_{\mathrm B}v_{\mathrm B}^T$. Normalized circle integrals
satisfy, for every complex matrix $X$,

$$
\begin{aligned}
S(X)
&=\frac{10}{3}\int P_{\mathrm A}(\theta,\phi)X
P_{\mathrm A}(\theta,\phi)\,\frac{d\theta\,d\phi}{(2\pi)^2}\\
&\quad+\frac53\int P_{\mathrm B}(\theta)X
P_{\mathrm B}(\theta)\,\frac{d\theta}{2\pi},\\
\sum_{f\in F}c_fP_f&=I_5.
\end{aligned}
\tag{2.6}
$$

Proof. The vector norms are one by the mutually orthogonal summands in
(1.4). For the A-family, every entry of $PXP$ is a linear combination
of products of four vector coordinates. Its degrees in the plus and
minus plane coordinates are
$(4,0),(3,1),(2,2),(1,3),(0,4)$.
A homogeneous trigonometric monomial of degree $a$ has frequencies among
$-a,-a+2,\ldots,a$. The three-point circle average kills every frequency
not divisible by three. At degrees zero, two and four, the only surviving
frequency is zero, exactly as in the circle integral. At bidegrees
$(3,1)$ and $(1,3)$, the degree-one factor has zero three-point average
and zero integral; both product averages therefore vanish, including
the potentially surviving frequencies of the degree-three factor.
This proves the A quartic identity. The same argument at total degree
two proves its projector-average identity.

For the B-family every entry of $PXP$ has circle frequency between $-4$
and $4$. The five-point root-of-unity sum kills all its nonzero
frequencies, so it is exactly the circle integral. The same holds for
the quadratic entries of $P$. These are identities of coefficient
tensors, hence apply to arbitrary complex $X$.
The total weights are $9(10/27)=10/3$ and $5(1/3)=5/3$, giving the
first identity of (2.6).

Circle second moments are $R_\pm/2$ on either rotation plane; the mean
plane vector is zero. Consequently the two contributions to the
projector sum are

$$
\begin{aligned}
\sum_{k,\ell}c_{\mathrm A,k,\ell}P_{\mathrm A,k,\ell}
&=\frac{10}{3}\left(\frac15R_++\frac3{10}R_-\right)
=\frac23R_++R_-,\\
\sum_kc_{\mathrm B,k}P_{\mathrm B,k}
&=\frac53\left(\frac35R_0+\frac15R_+\right)
=R_0+\frac13R_+.
\end{aligned}
\tag{2.7}
$$

Their sum is $I_5$. Thus (2.6) identifies an already finite channel;
its integrals introduce no continuous flag or future operation.
$\square$

**Theorem 2.3 (A legal fixed scalar port on every reference extension).**
For each $f\in F$, put

$$
\begin{gathered}
B_f=\sqrt{c_f}\,v_f^TD^\dagger:\mathbb C^5\longrightarrow\mathbb C,
\qquad R_f=Dv_f:\mathbb C\longrightarrow\mathbb C^5,\\
\operatorname{Enc}(X)=(B_fXB_f^\dagger)_{f\in F},\qquad
\operatorname{Dec}_f(y)=R_fyR_f^\dagger
=yDP_fD^\dagger\quad(y\in M_1).
\end{gathered}
\tag{2.8}
$$

These maps realize $T_*\in\mathfrak C_1$ with fourteen fixed flags.
Each decoder is trace preserving on its entire scalar block.

Proof. Lemma 2.2 gives

$$
\sum_fB_f^\dagger B_f
=D\left(\sum_fc_fP_f\right)D^\dagger=I_5,\qquad
R_f^\dagger R_f=1.
\tag{2.9}
$$

Each branch of the encoder and each decoder is a rectangular matrix
sandwich. For every reference dimension $n$, its extension is a
sandwich by $B_f\otimes I_n$ or $R_f\otimes I_n$, which preserves positive
semidefiniteness. Direct sums and sums preserve positivity too. Equation
(2.9) proves trace preservation on every complex matrix, and on all
reference extensions. In particular each decoder is CPTP for all
$y\in M_1$, not only on a selected encoded state.
The composite has the explicit rank-one Kraus matrices

$$
C_f=R_fB_f=\sqrt{c_f}\,DP_fD^\dagger,\qquad
\sum_fC_f^\dagger C_f=I_5.
\tag{2.10}
$$

This is exactly (2.4). It agrees with the CPTP convention of
[FiniteStateChannel.QuantumChannel](https://github.com/the-omega-institute/trureturing/blob/65e4b82851f0d321f9211ef6cb7ef2bb343c9306/D5/S3/Quantum/Foundation/FiniteStateChannel.lean)
and the finite rectangular Kraus hypothesis in
[finite_kraus_quantum_channel](https://github.com/the-omega-institute/trureturing/blob/65e4b82851f0d321f9211ef6cb7ef2bb343c9306/D5/S3/Quantum/Foundation/FiniteKrausChannel.lean).
The encoder outputs only the direct sum of scalar blocks; the decoder
outputs only their summed state. Thus the flag is consumed in decoding,
and no additional input-dependent record reaches the future policy.
All fourteen branches are specified before the input or future policy,
and no quantum path avoids the scalar block.

Equivalently, this is the finite measure-and-prepare form

$$
T_*(X)=\sum_fc_f\,\operatorname{tr}(DP_fD^\dagger X)\,DP_fD^\dagger,
\tag{2.11}
$$

with POVM effects $c_fDP_fD^\dagger$.
The rank-one Kraus/measure-and-prepare equivalence is the known
[Horodecki–Shor–Ruskai, Theorem 4(A–D)](https://arxiv.org/html/quant-ph/0302031);
the explicit normalization here is (2.7). Its branch trace/Born pairing
also has the convention of
[finite_kraus_instrument_born_marginal](https://github.com/the-omega-institute/trureturing/blob/65e4b82851f0d321f9211ef6cb7ef2bb343c9306/D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean).
$\square$

**Proposition 3.1 (The exact channel moment and stationarity).** For a
real symmetric matrix $E$, write $t_j=\operatorname{tr}(R_jE)$,
$j\in\{0,+,-\}$. The channel in (2.4) obeys

$$
\begin{aligned}
S(E)={}&\frac{3t_0+t_+}{5}R_0
+\frac{2t_0+t_++2t_-}{10}R_+
+\frac{4t_++3t_-}{20}R_-\\
&+\frac15R_+ER_++\frac3{10}R_-ER_-\\
&+\frac25(R_0ER_++R_+ER_0+R_+ER_-+R_-ER_+).
\end{aligned}
\tag{3.1}
$$

It is Hilbert–Schmidt self-adjoint and commutes with
$X\mapsto G(\theta,\phi)XG(\theta,\phi)^T$ on all complex matrices,
hence with every actual wait.

Proof. Regard (2.6) as $S(X)=5\mathbb E[PXP]$, where the two orbit types
have probabilities $2/3,1/3$. Their squared populations in the ordered
subspaces $(0,+,-)$ are

$$
p_{\mathrm A}=(0,2/5,3/5),\qquad
p_{\mathrm B}=(3/5,2/5,0).
$$

Their first and second population moments are therefore

$$
\mathbb E p=(1,2,2)/5,\qquad
M:=\mathbb E[pp^T]
=\frac1{25}\begin{pmatrix}3&2&0\\2&4&4\\0&4&6\end{pmatrix}.
\tag{3.2}
$$

For a uniform unit vector $n$ in a real two-plane, the coordinate
moments used here are

$$
\mathbb E[n_an_b]=\delta_{ab}/2,\qquad
\mathbb E[n_an_bn_cn_d]
=(\delta_{ab}\delta_{cd}+\delta_{ac}\delta_{bd}
+\delta_{ad}\delta_{bc})/8.
\tag{3.3}
$$

Indeed the nonzero fourth moments of sine and cosine are $3/8,3/8,1/8$,
and all monomials with an odd exponent have zero integral.
These fourth-moment methods are also used for accessible fidelity in
[Fuchs–Sasaki, §§4.2–4.3](https://arxiv.org/html/quant-ph/0302092v3);
their ensemble-average fidelity is a different objective from (1.3),
and their irreducible group argument does not apply directly to this
$1+2+2$ representation.

For completeness, contraction of $5\mathbb E[P\,\operatorname{tr}(PE)]$
gives a formula before inserting (3.2). On the dark line the scalar
coefficient is
$5M_{00}t_0+(5/2)M_{0+}t_++(5/2)M_{0-}t_-$.
For $j\in\{+,-\}$ and the other plane $k$, its diagonal plane block is

$$
\frac{5M_{jj}}8(t_jR_j+2R_jER_j)
+\frac{5M_{0j}}2t_0R_j+\frac{5M_{jk}}4t_kR_j.
\tag{3.4}
$$

The dark/plane off-diagonal blocks are
$5M_{0j}(R_0ER_j+R_jER_0)$; the two-plane off-diagonal blocks are
$(5/2)M_{+-}(R_+ER_-+R_-ER_+)$.
Every other term has a zero odd circle moment.
Substitution yields (3.1). The missing dark/minus interaction is exactly
$M_{0-}=0$.

Every sandwich $P_fXP_f$ is Hilbert–Schmidt self-adjoint, hence so is
$S$. The continuous orbit expression (2.6) is invariant under shifting
either angle, proving the asserted commutation on all complex matrices.
Alternatively $P_fXP_f=P_f\operatorname{tr}(P_fX)$ annihilates the
transpose-antisymmetric part of $X$, and the complex-linear extension
of (3.1) to $(X+X^T)/2$ is manifestly equivariant.
This is a property of the displayed channel, with its finite realization
already proved. It imposes no covariance or real-Kraus restriction on
competitors.
Haar covariance constructions in
[Werner, §4, equation (4.2)](https://arxiv.org/html/quant-ph/9804001)
and [Nechita–Park, §2.1](https://arxiv.org/html/2403.03667v2)
provide the relevant averaging framework. Their cloning fidelity and
random-channel orthogonal covariance classes respectively have different
objectives or symmetry hypotheses; neither evaluates (1.3).
In particular no rank-preserving character decomposition is used:
[unitary_kraus_mixing_invariance](https://github.com/the-omega-institute/trureturing/blob/65e4b82851f0d321f9211ef6cb7ef2bb343c9306/D5/S3/QuantumChannels/UnitaryKrausMixingInvariance.lean)
preserves channel sums but does not assert rank preservation.
The construction is compatible with all three counterexamples in
QPC Propositions 9.1–9.3. $\square$

**Proposition 3.2 (Explicit data for all fifteen residuals).** Put
$\Pi_J=\sum_{s\in J}\Pi_s$ and $H_J=\Pi_J-S(\Pi_J)$.
For the ordered splitting
$L=(N,25)$, $V=(2,3,5)$, define

$$
2720S(\Pi_s)
=
\begin{pmatrix}a_s&b_s\\b_s&c_s\end{pmatrix}_{L}
\oplus
\begin{pmatrix}d_s&e_s&f_s\\e_s&g_s&h_s\\f_s&h_s&k_s\end{pmatrix}_{V}.
\tag{3.5}
$$

Here scalar entries $e_s$ in the table are unrelated to basis vectors.
All entries are the following affine expressions in $r$:

| $s$ | $a_s$ | $b_s$ | $c_s$ | $d_s$ | $e_s$ | $f_s$ | $g_s$ | $h_s$ | $k_s$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $N$ | $1308-12r$ | $-72-24r$ | $256$ | $348+4r$ | $-12-4r$ | $76-12r$ | $460+4r$ | $-12-4r$ | $348+4r$ |
| $2$ | $348+4r$ | $-36+28r$ | $366-10r$ | $1107+63r$ | $-54+42r$ | $-117-9r$ | $336-24r$ | $-54-22r$ | $563-33r$ |
| $3$ | $460+4r$ | $72-8r$ | $424+8r$ | $336-24r$ | $108-12r$ | $64+24r$ | $1164+36r$ | $108-12r$ | $336-24r$ |
| $5$ | $348+4r$ | $-36+28r$ | $366-10r$ | $563-33r$ | $-54-22r$ | $-117-9r$ | $336-24r$ | $-54+42r$ | $1107+63r$ |
| $25$ | $256$ | $72-24r$ | $1308+12r$ | $366-10r$ | $12-4r$ | $94+6r$ | $424+8r$ | $12-4r$ | $366-10r$ |

For every singleton or pair $J$, its full residual is exactly

$$
H_J=\Pi_J-\frac1{2720}\sum_{s\in J}
\left[
\begin{pmatrix}a_s&b_s\\b_s&c_s\end{pmatrix}_{L}
\oplus
\begin{pmatrix}d_s&e_s&f_s\\e_s&g_s&h_s\\f_s&h_s&k_s\end{pmatrix}_{V}
\right].
\tag{3.6}
$$

Moreover

$$
e(T_*)=\max_{1\le|J|\le2}\|H_J\|_{\rm op}.
\tag{3.7}
$$

Proof. The projections needed to substitute into (3.1) have blocks

$$
\begin{aligned}
R_+|_L&=\begin{pmatrix}(r+1)/(2r)&2/r\\2/r&(r-1)/(2r)\end{pmatrix},\\
R_+|_V&=\begin{pmatrix}
(r+3)/(4r)&1/r&(r+3)/(4r)\\
1/r&(r-3)/(2r)&1/r\\
(r+3)/(4r)&1/r&(r+3)/(4r)
\end{pmatrix},\\
R_0|_L&=0,\qquad
R_0|_V=\frac12\begin{pmatrix}1&0&-1\\0&0&0\\-1&0&1\end{pmatrix},
\qquad R_-=I-R_0-R_+.
\end{aligned}
\tag{3.8}
$$

These follow from (1.5).
For each $s$ use $t_j=(R_j)_{ss}$ and
$R_i\Pi_sR_j=(R_ie_s)(R_je_s)^T$ in (3.1).
For example the $L$ block for $s=N$ becomes
$\left(\begin{smallmatrix}327-3r&-18-6r\\-18-6r&64\end{smallmatrix}\right)/680$.
The same substitutions, with $r^2=17$, give all nine entries per row
in (3.5). Thus (3.5) is a coefficient identity, and linearity gives
(3.6).

For (3.7) use the credited first-read identity of QMB Theorem 2.1:
writing $Q_J(t)=O(t)^T\Pi_JO(t)$, it gives
$e(T_*)=\sup_{t\ge0}\max_J\|Q_J(t)-S^\dagger(Q_J(t))\|_{\rm op}$.
Proposition 3.1 and self-adjointness identify this residual with
$O(t)^TH_JO(t)$, so its norm is independent of the actual nonnegative
wait. Finally $S(I)=I$ by (2.6); complementary residuals are opposites.
The empty and full events vanish, leaving precisely five singletons
and ten pairs. This is the stationary fifteen-event identity already
supplied by QPC Theorem 3.3, applied to this particular channel.
It retains all complex density inputs: the norm of a Hermitian
matrix is the supremum of its absolute expectation over complex
density matrices. The first-read identity retains every finite
adaptive depth and source-independent randomized policy. $\square$

**Lemma 4.1 (Rational endpoint bounds for eleven events).** For the eleven
events in the next table, $\|H_J\|_{\rm op}<27/50$.
In the original order $(N,2,3,5,25)$, the table gives the entire five-vector
of absolute row sums of $16320H_J(x)$ at each endpoint
$x=4$ and $x=25/6$. Here $H_J(x)$ means the affine expression (3.6)
with $r$ replaced by $x$, without reinterpreting $x$ as a new spectral
parameter.

| $J$ | Row sums at $4$ | Row sums at $25/6$ | Largest endpoint row sum |
| --- | --- | --- | --- |
| $\{25\}$ | $(1680,2688,2784,2688,8328)$ | $(1704,2688,2800,2688,8340)$ | $8340$ |
| $\{N,2\}$ | $(7128,7248,5832,6540,4044)$ | $(7132,7240,5876,6558,4030)$ | $7248$ |
| $\{N,3\}$ | $(6672,4944,6000,4944,5040)$ | $(6712,4920,5928,4920,5080)$ | $6712$ |
| $\{N,5\}$ | $(7128,6540,5832,7248,4044)$ | $(7132,6558,5876,7240,4030)$ | $7248$ |
| $\{N,25\}$ | $(8376,5208,5976,5208,7800)$ | $(8436,5204,6004,5204,7836)$ | $8436$ |
| $\{2,3\}$ | $(5736,7812,8568,4560,5388)$ | $(5764,7818,8620,4552,5406)$ | $8620$ |
| $\{2,5\}$ | $(5280,7584,3216,7584,4824)$ | $(5344,7552,3128,7552,4860)$ | $7584$ |
| $\{2,25\}$ | $(4032,7080,5712,5628,6540)$ | $(4040,7068,5760,5614,6542)$ | $7080$ |
| $\{3,5\}$ | $(5736,4560,8568,7812,5388)$ | $(5764,4552,8620,7818,5406)$ | $8620$ |
| $\{3,25\}$ | $(4488,5400,6408,5400,5544)$ | $(4460,5380,6332,5380,5492)$ | $6408$ |
| $\{5,25\}$ | $(4032,5628,5712,7080,6540)$ | $(4040,5614,5760,7068,6542)$ | $7080$ |

Proof. This is an integer certificate derived from (3.5), as follows.
Write its full numerator matrix as $M_s(r)=A_s+rB_s$ with integer
matrices $A_s,B_s$. At the two endpoints the integer matrices whose
absolute row sums are displayed are exactly

$$
\begin{aligned}
16320H_J(4)&=16320\Pi_J-\sum_{s\in J}(6A_s+24B_s),\\
16320H_J(25/6)&=16320\Pi_J-\sum_{s\in J}(6A_s+25B_s).
\end{aligned}
\tag{4.1}
$$

Taking entrywise absolute values and row sums gives every listed integer.
For example, for $J=\{2,3\}$ the row indexed by mode $3$ in the
first integer matrix has diagonal $7032$ and off-diagonal entries
$-1044,492$ in modes $2,5$, hence absolute row sum $8568$.
At the other endpoint these entries are $7020,-1074,526$, whose
absolute sum is $8620$.

Since $4^2<17<(25/6)^2$, write
$r=\xi\,4+(1-\xi)\,25/6$ with $0<\xi<1$.
Affine dependence and the triangle inequality make each absolute
row sum at $r$ no larger than the corresponding convex combination
of endpoint row sums. A real symmetric matrix has operator norm at
most its largest absolute row sum: for an eigenvector choose a
coordinate of largest modulus and apply the eigenvalue equation.
Consequently every event in the table satisfies

$$
\|H_J\|_{\rm op}\le\frac{8620}{16320}
=\frac{431}{816}<\frac{27}{50};
\qquad
27\cdot816-50\cdot431=482>0.
\tag{4.2}
$$

This proves a bound on the actual algebraic matrices, using rational
endpoint identities rather than a time or input sample. $\square$

**Lemma 4.2 (The remaining three nonextremal singletons).** The residuals
for $s=2,3,5$ satisfy $\|H_{\{s\}}\|_{\rm op}<27/50$.

Proof. Their $L$ blocks have the following complete endpoint row-sum
vectors for $16320H_{\{s\}}|_L$:

$$
\begin{array}{c|cc}
s&x=4&x=25/6\\ \hline
2&(2640,2412)&(2672,2430)\\
3&(3096,2976)&(3092,2976)\\
5&(2640,2412)&(2672,2430)
\end{array}.
\tag{4.3}
$$

The same affine argument gives norm at most $3096/16320<1/5$ on $L$.
On $V$, put $C_s=H_{\{s\}}|_V$. Formula (3.5) gives

$$
\begin{aligned}
2720C_2&=\begin{pmatrix}
1613-63r&54-42r&117+9r\\
54-42r&-336+24r&54+22r\\
117+9r&54+22r&-563+33r
\end{pmatrix},\\
2720C_3&=\begin{pmatrix}
-336+24r&-108+12r&-64-24r\\
-108+12r&1556-36r&-108+12r\\
-64-24r&-108+12r&-336+24r
\end{pmatrix}.
\end{aligned}
\tag{4.4}
$$

The $C_5$ matrix is obtained from $C_2$ by exchanging its first and
third coordinates, so it has the same norm. To bound $C_2,C_3$, let
$\Delta_{s,\sigma,k}$ be the determinant of the leading $k$ by $k$
block of $(27/50)I_3+\sigma C_s$.
The next table states exact identities
$D\Delta_{s,\sigma,k}=a+br$ and a strictly positive lower bound $n$
for that numerator. All denominators $D$ are positive.

| $s$ | $\sigma$ | $k$ | $D$ | $a$ | $b$ | $n$ |
| --- | --- | --- | --- | --- | --- | --- |
| $2$ | $-1$ | $1$ | $13600$ | $-721$ | $315$ | $539$ |
| $2$ | $-1$ | $2$ | $11560000$ | $-498219$ | $190155$ | $262401$ |
| $2$ | $-1$ | $3$ | $144500000$ | $-5314217$ | $1827285$ | $1994923$ |
| $2$ | $1$ | $1$ | $13600$ | $15409$ | $-315$ | $28193/2$ |
| $2$ | $1$ | $2$ | $11560000$ | $5363211$ | $11145$ | $5407791$ |
| $2$ | $1$ | $3$ | $144500000$ | $21973163$ | $789015$ | $25129223$ |
| $3$ | $-1$ | $1$ | $1700$ | $1128$ | $-15$ | $2131/2$ |
| $3$ | $-1$ | $2$ | $1445000$ | $-36363$ | $13605$ | $18057$ |
| $3$ | $-1$ | $3$ | $144500000$ | $-2814367$ | $971655$ | $1072253$ |
| $3$ | $1$ | $1$ | $1700$ | $708$ | $15$ | $768$ |
| $3$ | $1$ | $2$ | $361250$ | $165903$ | $1680$ | $172623$ |
| $3$ | $1$ | $3$ | $144500000$ | $27345163$ | $818445$ | $30618943$ |

These identities use only (4.4), $r^2=17$, and, for a symmetric
three by three matrix with rows $(x,u,v),(u,y,w),(v,w,z)$,

$$
\det=xyz+2uvw-xw^2-yv^2-zu^2.
\tag{4.5}
$$

Its leading determinants of orders one and two are $x$ and $xy-u^2$.
Thus (4.4)–(4.5) specify every arithmetic operation in the table.
The last column is exactly $a+4b$ when $b\ge0$, and
$a+(25/6)b$ when $b<0$.
The inequalities $4<r<25/6$ therefore prove positivity of all twelve
determinants. Successive completion of squares, with pivots
$\Delta_1,\Delta_2/\Delta_1,\Delta_3/\Delta_2$, proves positive
definiteness of both $(27/50)I_3-C_s$ and
$(27/50)I_3+C_s$. Their eigenvalues place those of $C_s$ strictly
between $-27/50$ and $27/50$.
Together with the $L$ bound and the coordinate exchange for $s=5$,
this proves the claim. $\square$

**Lemma 4.3 (The extremal singleton and its exact radical).** Define

$$
\alpha=\frac{17\sqrt{17}+3+\sqrt{10458+198\sqrt{17}}}
{80\sqrt{17}}.
\tag{4.6}
$$

Then $\|H_{\{N\}}\|_{\rm op}=\alpha$ and
$27/50<\alpha<11/20$.

Proof. The $L$ block of $H_{\{N\}}$ is

$$
F_N=\frac1{680}
\begin{pmatrix}353+3r&18+6r\\18+6r&-64\end{pmatrix}.
\tag{4.7}
$$

Its trace is $\tau=(289+3r)/680>0$, and its determinant is
$-(173+3r)/3400<0$. Its positive eigenvalue is the positive root of

$$
p(z)=z^2-\tau z-\frac{173+3r}{3400}.
\tag{4.8}
$$

The quadratic formula gives

$$
\frac{289+3r+\sqrt{177786+3366r}}{1360}=\alpha,
\tag{4.9}
$$

because $177786+3366r=17(10458+198r)$ and $r^2=17$.
The other root is negative and has smaller absolute value, since
the trace is positive.

Direct substitution gives the exact signs

$$
p(27/50)=\frac{1907-555r}{170000}<0,\qquad
p(11/20)=\frac{243-45r}{13600}>0.
\tag{4.10}
$$

Indeed $r>4$ proves the first, and $r<5$ proves the second.
The quadratic has only one positive root, so these signs place it
strictly between the two indicated rational numbers.

On $V$, $H_{\{N\}}=-S(\Pi_N)|_V$ is negative semidefinite by complete
positivity. Since $S$ is trace preserving and
$\operatorname{tr}(H_{\{N\}})=0$, this block has negative trace
$-\tau$. A positive semidefinite matrix has norm at most its trace;
hence its absolute norm is at most

$$
\tau<\frac{289+3(25/6)}{680}
=\frac{603}{1360}<\frac{27}{50}<\alpha.
\tag{4.11}
$$

The largest absolute eigenvalue of the whole residual is consequently
the positive eigenvalue $\alpha$ of (4.7). $\square$

**Theorem 5.1 (An attained strict improvement for the original menu).**
Under Assumption 1.1 and Definition 1.2, the fourteen-flag port (2.8)
has exact full-history error

$$
\boxed{e(T_*)=\alpha<\frac{11}{20}<\frac47.}
\tag{5.1}
$$

An actual attaining protocol is a zero wait, one complete five-outcome
rank-one mode read, and Stop.

Proof. Proposition 3.2 reduces this particular channel to its fifteen
event residuals. Lemma 4.1 covers all ten pairs and the singleton $25$;
Lemma 4.2 covers $2,3,5$. All fourteen norms are strictly below
$27/50$, while Lemma 4.3 gives the remaining norm exactly $\alpha$.
This proves the full-history upper and the exact maximum in (3.7).
The rational inequality $11/20<4/7$ follows from $77<80$.

To give the actual input explicitly, set

$$
b=\frac{9+3r}{340},\qquad
v=\frac{(\alpha+8/85)e_N+be_{25}}
{\sqrt{(\alpha+8/85)^2+b^2}},\qquad
\rho_*=Dvv^\dagger D^\dagger.
\tag{5.2}
$$

The vector is well defined and unit, since $b>0$.
The second row of (4.7) gives $F_Nv=\alpha v$ in that coordinate,
and the first row follows from $p(\alpha)=0$; thus the full residual
also has $H_{\{N\}}v=\alpha v$.
For the prescribed full read at wait $t=0$, the difference in
probability of the actual recorded outcome $N$ is

$$
\operatorname{tr}\bigl(\Pi_N(\rho_*-T_*(\rho_*))\bigr)
=v^\dagger H_{\{N\}}v=\alpha.
\tag{5.3}
$$

The full-history TV is at least the absolute difference on this event
and at most the proved upper $\alpha$, hence equals $\alpha$.
No limiting wait or independently selected torus angles are needed.
The first-read identity already used in Proposition 3.2 proves that
no deeper allowed adaptive protocol increases the bound.
$\square$

**Corollary 5.2 (The remaining unrestricted interval).** With the
credited QPC lower constant

$$
L=1-\frac12\left(\frac{5556+423\sqrt{17}}{13414}
+\frac{63}{125}\right),
\tag{5.4}
$$

the original unrestricted minimax problem satisfies

$$
L\le\varepsilon_1\le
\frac{17\sqrt{17}+3+\sqrt{10458+198\sqrt{17}}}{80\sqrt{17}}
<\frac{11}{20}<\frac47.
\tag{5.5}
$$

In particular the QMB Theorem 3.1 scalar real-projection channel,
whose exact error is $4/7$, is not a minimizer for this menu.

Proof. The lower bound is precisely
QPC Theorem 6.4, which covers every original complex finite-flag
competitor. Theorem 2.3 places the displayed port in that same class,
so $\varepsilon_1\le e(T_*)$. Apply Theorem 5.1.
Its strict error improvement excludes the former $4/7$ channel as a
minimizer without restricting any competitor. $\square$

**Definition 5.3 (The matching lower problem and resource boundary).**
For the attained sufficient endpoint (4.6), a matching unrestricted
lower would require
$e(T)\ge\alpha$ for every $T\in\mathfrak C_1$.
Equations (5.4)–(5.5) do not supply that inequality or an exact value
of $\varepsilon_1$.
In the output-first normalized Choi convention, the competitors
equivalently obey

$$
\chi_T=\frac15\sum_f
|\operatorname{vec}C_f\rangle\langle\operatorname{vec}C_f|,
\qquad
\operatorname{Tr}_{\rm out}\chi_T=I_5/5,\qquad
\operatorname{SN}(\chi_T)\le1.
\tag{5.6}
$$

This is the credited QMB Theorem 5.1 correspondence.
[Terhal–Horodecki, Definition 1 and Theorem 1](https://arxiv.org/html/quant-ph/9911117v4)
give the low-Schmidt-number and positive-map witness framework.
A lower certificate for (1.3) must additionally retain the TP marginal
and the actual menu objective; a maximally entangled overlap bound
alone is a different test.
QPC §§4–5 give a complete algebraic decision specification, not an
evaluated matching lower for (4.6).
Likewise, the exact primal/dual bounds in
[Watrous, §2, Theorems 1–2](https://arxiv.org/html/0901.4709v2)
apply to the stated semidefinite program; its completely bounded
trace-norm program in §3 has a different objective and does not
replace either (1.3) or the low-Schmidt-number constraint (5.6).

The algebraic vector coefficients, finite flag count, full-block CPTP
design and zero-wait attainment are separate mathematical resources
from physical coefficient synthesis, finite precision, preparation
acquisition, clocks, storage duration and transport.
No such additional resource bounds, native $\alpha/\beta$ preparation
bridge, or mutual recovery of space, time, boundary and memory are
part of (5.5).
The real projector properties in (2.3) describe only the sufficient
construction, not a reduction of the complex competitor class.

## 追加锚（本行以下为增补区）
