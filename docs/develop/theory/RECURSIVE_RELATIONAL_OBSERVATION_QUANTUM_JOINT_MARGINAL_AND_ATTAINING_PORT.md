# Recursive relational observation: joint marginal and an attaining scalar port

For the original five-mode quantum preparation, fixed scalar port and
actual finite-history criterion, this volume proves

$$
\boxed{\frac{129931}{250000}\le\varepsilon_1\le\lambda},\qquad
\frac{52417656}{10^8}<\lambda<\frac{52417658}{10^8}.
\tag{0.1}
$$

The necessary bound covers every legal complex competitor. The sufficient
bound is the exact error of one explicit fourteen-flag port and is attained
at wait zero. Both endpoints strictly improve the QWS interval. They do
not match, and the original optimum remains open.

This volume is reference mathematics: ordinary proofs and finite exact
arithmetic, without new Lean kernel evidence or a physical realization
claim. Its content is append-only; corrections and extensions belong
after the final append anchor. Definitions and proofs below distinguish
the new two-sided improvement from the credited supplier results.

## 1. Contract, suppliers and spectral conventions

**Assumption 1.1 (The unchanged preparation and actual menu).** Use exactly
QMB Assumption 1.1. The Hilbert space is $\mathbb C^5$, with ordered
orthonormal basis $\mathsf S=(N,2,3,5,25)$ and
$\Pi_s=e_se_s^\dagger$. Every complex density matrix is an allowed input.
Fix

$$
K=\begin{pmatrix}
0&1&1&1&0\\
1&0&0&0&1\\
1&0&0&0&0\\
1&0&0&0&1\\
0&1&0&1&0
\end{pmatrix},\qquad U(t)=\exp(-itK),\quad t\ge0.
\tag{1.1}
$$

The future menu consists precisely of nonnegative waits, the complete
five-outcome rank-one Lüders instrument $X\mapsto(\Pi_sX\Pi_s)_s$,
and Stop. All finite adaptive depths are included. Histories retain
outcomes, controls and stops. Initial controls and allowed random controls
are source-independent, and both comparisons use the same policy.
Classical grouping of outcomes is postprocessing of this complete read.
It is not a coarse-block Lüders instrument. Independent mode phases,
arbitrary future unitaries, probability oracles, readable hidden Kraus
records, source copies, resets and external quantum side information
are absent. This preparation is an independent hypothesis, not a
construction from the native $\alpha/\beta$ tree or a different
tensor-cut source. The label $N$ denotes a unit basis vector.

**Definition 1.2 (One fixed scalar port and its original error).** A legal
port is a composite $T=\operatorname{Dec}\circ\operatorname{Enc}$ of
fixed CPTP maps

$$
\operatorname{Enc}:M_5\longrightarrow\bigoplus_{f\in F}M_1,
\qquad \operatorname{Dec}((y_f)_f)=\sum_f\operatorname{Dec}_f(y_f),
\qquad \operatorname{Dec}_f:M_1\longrightarrow M_5,
\tag{1.2}
$$

where $F$ is finite and each decoder is CPTP on its whole scalar block.
The design precedes the input and choice of future policy. There is no
original-input retention, entangled assistance or bypass. Flags are free
for this quantum dimension criterion, are used in decoding, and are not
additionally exposed to the future policy. Let $\mathfrak C_1$ contain
all these complex CPTP composites, without a reality, covariance,
unitality or projector restriction. With replacement occurring once
before the common future protocol, put

$$
e(T)=\sup_{\rho\in\mathcal D(\mathbb C^5)}
\sup_{\pi\ {\rm actual,finite}}
\operatorname{TV}(P_\rho^\pi,P_{T(\rho)}^\pi),
\qquad \varepsilon_1=\inf_{T\in\mathfrak C_1}e(T).
\tag{1.3}
$$

TV is half the $\ell^1$ difference, or its probability-measure version
for random controls. CPTP legality includes every reference extension;
the performance criterion measures only system histories. Neither
trace distance nor diamond distance replaces (1.3).

**Convention 1.3 (Public suppliers).** The following citations refer to
the source bytes at repository pin
`cfe0f6777c3fa129e6f347d18b0893303b9a6f4a`.

| Name | Owning source and use |
| --- | --- |
| QMB | [Measurement-relative quantum boundary](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md), Assumption 1.1, Definitions 1.2–1.3 and Theorem 2.1: operational contract and first-read identity. |
| QPC | [Port covariance and certified frontier](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_PORT_COVARIANCE_AND_CERTIFIED_FRONTIER.md), Theorem 3.3 and Propositions 9.1–9.3: no-worse stationarity and the boundaries of stronger symmetry shortcuts. |
| QFA | [Finite port attainment](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_FINITE_PORT_ATTAINMENT.md), Lemma 2.2: the finite quartic circle quadrature mechanism. |
| QEC | [Classical-port exact certificates](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_CLASSICAL_PORT_EXACT_CERTIFICATES.md), Proposition 2.2 and Theorem 2.6: weighted actual-time moment and finite-wait estimates. |
| QRC | [Real-port boundary coordinates](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_REAL_PORT_BOUNDARY_COORDINATES.md), Theorems 3.2, 5.2 and 6.2: no-worse independent real-product replacement, exact atom cone, full TP marginal and joint fifteen-event formulation. |
| QWS | [Witness slack and independent decoding](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_WITNESS_SLACK_AND_INDEPENDENT_DECODING.md), §§1–2 and Proposition 4.2: spectral conventions, retained witness with complementary gap, and the orientation of the adjoint. |

These are ordinary mathematical suppliers. Merge status is not a proof,
and no formal certification of their applications is asserted here.

**Convention 1.4 (Passive real frame).** Use QWS equations (1.4)–(1.7):

$$
\begin{gathered}
r=\sqrt{17},\qquad D=\operatorname{diag}(1,i,i,i,1),\qquad
A=-iD^\dagger KD,\qquad O(t)=e^{tA}=D^\dagger U(t)D,\\
B=-A^2,\qquad \mu_\pm=(5\pm r)/2,\qquad \omega_\pm=\sqrt{\mu_\pm},\\
R_\pm=\frac{B(B-\mu_\mp I)}{\mu_\pm(\mu_\pm-\mu_\mp)},\qquad
R_0=I-R_+-R_-=dd^T,\qquad d=(e_2-e_5)/\sqrt2,\\
W_\pm=AR_\pm/\omega_\pm,\qquad
u_\pm=\frac{R_\pm e_N}{\sqrt{(1\pm1/r)/2}},\qquad
w_\pm(\alpha)=\cos\alpha\,u_\pm+\sin\alpha\,W_\pm u_\pm.
\end{gathered}
\tag{1.4}
$$

Sector order is $(0,+,-)$ with dimensions $(d_0,d_+,d_-)=(1,2,2)$.
In the reordered coordinates $L=(N,25)$ and $V=(2,3,5)$, direct
evaluation of (1.1) gives

$$
A=\begin{pmatrix}0&C\\-C^T&0\end{pmatrix},\qquad
C=\begin{pmatrix}1&1&1\\1&0&1\end{pmatrix},\qquad
CC^T=\begin{pmatrix}3&2\\2&2\end{pmatrix}.
\tag{1.5}
$$

The last matrix has characteristic polynomial $x^2-5x+2$.
Consequently (1.4) gives mutually orthogonal projections of the stated
ranks, and $u_\pm,W_\pm u_\pm$ are orthonormal plane bases. The
explicit matrices needed for every coefficient calculation are

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
\tag{1.6}
$$

All cross blocks vanish. Define

$$
\begin{gathered}
G(\alpha,\beta)=R_0+\cos\alpha R_++\sin\alpha W_+
                  +\cos\beta R_-+\sin\beta W_-,\\
\mathsf J=\operatorname{diag}(1,-1,-1,-1,1),\qquad
Q_J(t)=O(t)^T\Pi_JO(t),\qquad \Pi_J=\sum_{s\in J}\Pi_s.
\end{gathered}
\tag{1.7}
$$

Then $O(t)=G(\omega_+t,\omega_-t)$ and
$\mathsf J A\mathsf J=-A$. The two mathematical angles and passive
frame are not extra future controls. Transposes refer to this frame;
a map dagger denotes its trace-pairing adjoint.

**Convention 1.5 (The supplied exact event criterion).** For
$\widehat T(X)=D^\dagger T(DXD^\dagger)D$, QMB Theorem 2.1 states

$$
e(T)=\sup_{t\ge0}\max_{J\subseteq\mathsf S}
\|Q_J(t)-\widehat T^\dagger(Q_J(t))\|_{\rm op}.
\tag{1.8}
$$

For a frame channel $S$ commuting with every
$\operatorname{Ad}_{O(t)}$, its adjoint also commutes and hence

$$
Q_J(t)-S^\dagger(Q_J(t))
=O(t)^T[\Pi_J-S^\dagger(\Pi_J)]O(t).
\tag{1.9}
$$

TP gives $S^\dagger(I)=I$, so complementary residuals have opposite
signs. Thus the stationary error equals the maximum over
$\mathcal J_{15}=\{J:1\le|J|\le2\}$. These supplier identities
retain every complex input and every actual finite adaptive history.
The first rank-one read resets both conditional states to the same
$\Pi_s$; its common suffix cannot enlarge first-result TV.
Source-independent random controls obey the same bound. These facts
explain the applicability of (1.8), without introducing a different
measurement norm or reproving the general reduction.

## 2. A stronger necessary bound from the full TP marginal

**Convention 2.1 (Retained witness, with its exact scope).** Retain
precisely the weighted moment $\mathcal W$, multiplier $Y$, witness
$P$ and kernel projection $K_{\rm ker}$ of QWS Definition 2.1 and
Lemmas 2.2–2.3. In particular,

$$
\begin{gathered}
Y=(4025R_0+4974R_++5021R_-)/10000,
\qquad \operatorname{tr}Y/5=4803/10000,\qquad \gamma=1/25000,\\
I\otimes Y-\mathcal W=(P+P^\Gamma)/2,
\qquad P\succeq\gamma(I-K_{\rm ker}),\\
K_{\rm ker}+K_{\rm ker}^\Gamma=Q,
\qquad Q=R_+\otimes R_++R_-\otimes R_-.
\end{gathered}
\tag{2.1}
$$

Choi order is output first, input second; $\Gamma$ transposes the input
factor. The exact moment is QEC Proposition 2.2, with weights
$a=(9/4,3/4,5/4,3/4,0)$ and $w=a/5$. Its actual forward-time mean
satisfies

$$
\mathscr S(T)=\operatorname{tr}(\chi_T\mathcal W),\qquad
e(T)\ge1-\mathscr S(T),\qquad
\chi_T=(\widehat T\otimes\mathrm{id})(\Omega\Omega^\dagger),
\quad \Omega=5^{-1/2}\sum_se_s\otimes e_s.
\tag{2.2}
$$

The witness and its exact shifted-block certificate belong to QWS;
the additional consequence here uses the matrix TP marginal instead
of only $\operatorname{tr}\chi_T=1$.

**Lemma 2.2 (The marginal cap).** For every positive normalized Choi
matrix with $\operatorname{Tr}_{\rm out}\chi=I_5/5$,

$$
\operatorname{tr}(\chi Q)\le\frac45.
\tag{2.3}
$$

Proof. The exact operator difference is

$$
I\otimes(R_++R_-)-Q
=(I-R_+)\otimes R_++(I-R_-)\otimes R_-\succeq0.
\tag{2.4}
$$

Each summand is a tensor product of positive projections. Pairing
with the same positive $\chi$ and using its input marginal gives

$$
\operatorname{tr}(\chi Q)
\le\operatorname{tr}\bigl(\chi[I\otimes(R_++R_-)]\bigr)
=\frac{\operatorname{tr}(R_++R_-)}5=\frac45.
\tag{2.5}
$$

The argument is valid on the entire complex tensor space. $\square$

**Theorem 2.3 (Necessary error for every original complex scalar port).**
For every $T\in\mathfrak C_1$,

$$
e(T)\ge\frac{129931}{250000}=0.519724.
\tag{2.6}
$$

Proof. The scalar-port Choi correspondence in QWS equation (2.15)
gives $\chi_T\succeq0$, $\chi_T^\Gamma\succeq0$ and
$\operatorname{Tr}_{\rm out}\chi_T=I_5/5$. It applies to arbitrary
complex POVM effects and arbitrary complex preparation states; no
stationary or real replacement is needed for this direction.
Pair (2.1) separately with $\chi_T$ and $\chi_T^\Gamma$. The
trace self-adjointness of partial transpose and Lemma 2.2 give

$$
\begin{aligned}
\operatorname{tr}\bigl(\chi_T[I\otimes Y-\mathcal W]\bigr)
&\ge\gamma\left(1-\frac12\operatorname{tr}(\chi_T Q)\right)\\
&\ge\frac{3\gamma}{5}=\frac3{125000}.
\end{aligned}
\tag{2.7}
$$

This uses PSD pairing with $\chi_T^\Gamma$, not positivity of
$K_{\rm ker}^\Gamma$. The same TP marginal now yields

$$
\mathscr S(T)\le\frac{4803}{10000}-\frac3{125000},\qquad
e(T)\ge1-\frac{4803}{10000}+\frac3{125000}
=\frac{129931}{250000}.
\tag{2.8}
$$

This is $1/250000$ above the QWS lower bound $12993/25000$.
The proof actually bounds the entire complex PPT TP Choi slice. It
does not identify PPT with separability or construct a port from a
relaxed feasible matrix. $\square$

**Corollary 2.4 (Finite nonnegative-wait alternatives).** For every
rational $0<\delta<1$, put

$$
h=\delta/48,\qquad n=\left\lceil153600/\delta^2\right\rceil,
\qquad H=nh,\qquad \mathcal W_\delta=\{jh:0\le j\le n\}.
\tag{2.9}
$$

For each original legal complex scalar port, one of the $4(n+1)$
tests with $s\in\{N,2,3,5\}$, input $DQ_s(t)D^\dagger$ and
$t\in\mathcal W_\delta$, followed by actual wait $t$, a complete
mode read and Stop, has

$$
\operatorname{TV}>\frac{129931}{250000}-\delta,
\qquad \frac{3200}{\delta}\le H\le\frac{3200}{\delta}+\frac\delta{48}.
\tag{2.10}
$$

Proof. QEC Theorem 2.6 and QWS Corollary 2.5 supply the uniform
forward-mean error $<800/H$ and survival derivative bound $<12$.
Use the improved mean (2.8) in those estimates. Since
$H\ge3200/\delta$, some positive-weight mode has failure at least
$129931/250000-\delta/4$ in $[0,H]$. Moving to a grid point within
$h$ loses at most $12h=\delta/4$. Its TV is at least the bound minus
$\delta/2$, which proves the strict threshold. The ceiling gives
the displayed time bound. Every wait is finite and nonnegative.
These are alternative legitimate tests for a competitor, not a
single-sample probability oracle or a clock-cost theorem. $\square$

## 3. An explicit fourteen-flag port

**Definition 3.1 (Independent measurement and preparation atoms).** Let
$\alpha_k=2\pi k/3$, $\beta_k=2\pi k/5$ and

$$
F=\{(\mathrm A,k,l):0\le k,l<3\}
\sqcup\{(\mathrm B,k):0\le k<5\}.
\tag{3.1}
$$

Define real unit measurement vectors $b_f$, preparation vectors $a_f$
and positive per-flag weights $c_f$ by

$$
\begin{aligned}
b_{\mathrm A,k,l}
&=\frac{9w_+(\alpha_k)+\sqrt{119}\,w_-(\alpha_l)}{\sqrt{200}},
&c_{\mathrm A,k,l}&=\frac{400}{1071},\\
a_{\mathrm A,k,l}
&=\frac{1521w_+(\alpha_k)+166\sqrt{119}\,w_-(\alpha_l)}{\sqrt{5592605}},\\
b_{\mathrm B,k}
&=\frac{\sqrt{119}\,d+\sqrt{76}\,w_+(\beta_k)}{\sqrt{195}},
&c_{\mathrm B,k}&=\frac{39}{119},\\
a_{\mathrm B,k}
&=\frac{71\sqrt{119}\,d+94\sqrt{76}\,w_+(\beta_k)}{\sqrt{1271415}}.
\end{aligned}
\tag{3.2}
$$

These are exact algebraic data. Circle values are the same exact
three-point and five-point values as QFA equation (2.1); equivalently
they are fixed roots of unity with the displayed real angles. No angle
is selected after the input. Set

$$
S(X)=\sum_fc_fa_fa_f^T\operatorname{tr}(b_fb_f^TX),\qquad
T_\lambda(X)=DS(D^\dagger XD)D^\dagger.
\tag{3.3}
$$

**Theorem 3.2 (Fixed scalar realization and full-block TP).** The maps

$$
\begin{gathered}
B_f=\sqrt{c_f}\,b_f^TD^\dagger:\mathbb C^5\longrightarrow\mathbb C,
\qquad R_f=Da_f:\mathbb C\longrightarrow\mathbb C^5,\\
\operatorname{Enc}(X)=(B_fXB_f^\dagger)_f,\qquad
\operatorname{Dec}_f(y)=R_fyR_f^\dagger
\end{gathered}
\tag{3.4}
$$

realize $T_\lambda\in\mathfrak C_1$ with fourteen fixed nonzero
rank-one composite Kraus matrices. Every decoder is CPTP on all of
$M_1$.

Proof. Orthogonal sectors and

$$
9^2+119=200,\quad119+76=195,\quad
1521^2+166^2\cdot119=5592605,\quad
71^2\cdot119+94^2\cdot76=1271415
\tag{3.5}
$$

make all four vector families unit. Quadratic circle averages give

$$
\begin{aligned}
\sum_{k,l}c_{\mathrm A,k,l}b_{\mathrm A,k,l}b_{\mathrm A,k,l}^T
&=\frac{400}{119}\left(\frac{81}{400}R_+
                                  +\frac{119}{400}R_-\right)
=\frac{81}{119}R_++R_-,\\
\sum_kc_{\mathrm B,k}b_{\mathrm B,k}b_{\mathrm B,k}^T
&=\frac{195}{119}\left(\frac{119}{195}R_0
                                   +\frac{38}{195}R_+\right)
=R_0+\frac{38}{119}R_+.
\end{aligned}
\tag{3.6}
$$

Their sum is $I_5$. Therefore
$\sum_fB_f^\dagger B_f=I_5$ and $R_f^\dagger R_f=1$ for every
flag. Each rectangular sandwich remains positive after tensoring
with an identity of any reference dimension. Direct sums prove encoder
CP; each decoder is CP, and the normalization identities prove trace
preservation on every complex matrix of its whole domain. The composite
has Kraus matrix
$C_f=R_fB_f=\sqrt{c_f}Da_fb_f^TD^\dagger$, nonzero of rank one,
and $\sum_fC_f^\dagger C_f=I_5$.

The decoded branch trace equals its encoder trace, since
$R_f^\dagger R_f=1$. All paths pass through the stated scalar block,
and the decoder consumes the flag. The future policy receives only
the summed decoded state. $\square$

**Lemma 3.3 (Finite design identity and whole-channel stationarity).**
The channel (3.3) equals its joint continuous-orbit expression, with
normalized circle measures and total orbit weights $400/119$ and
$195/119$. It commutes with every $\operatorname{Ad}_{G(\alpha,\beta)}$
and with $\operatorname{Ad}_{\mathsf J}$ on every complex matrix.

Proof. This is the QFA quartic quadrature mechanism, also applied to
independent factors in QWS Lemma 3.3. For clarity, its hypotheses hold
for (3.2): an A coefficient of $aa^T\otimes bb^T$ has bidegree
$(4,0),(3,1),(2,2),(1,3)$ or $(0,4)$. At even degrees zero, two and
four the three-point circle rule retains only zero frequency. In
the odd bidegrees the degree-one factor has both discrete and continuous
mean zero, killing the possible degree-three alias. A B coefficient
has frequencies between $-4$ and $4$, and the five-point rule kills
every nonzero frequency. Thus these are coefficient-tensor equalities
on all complex inputs, with total weights
$9(400/1071)=400/119$ and $5(39/119)=195/119$.

Angle translation proves rotation covariance of the integrals.
Also $\mathsf Jd=-d$ and
$\mathsf Jw_\pm(\alpha)=w_\pm(-\alpha)$. For A, reflection reverses
both angles. For B, an irrelevant simultaneous sign of each vector
changes its reflected projector to the projector at angle $\pi-\alpha$.
Both integrals are invariant. Hence the already finite channel has
the asserted symmetries and is stationary for the actual walk.
The integrals are design identities, not continuous flags or added
physical controls. $\square$

## 4. Joint cone coordinates, the marginal and the adjoint

**Proposition 4.1 (Actual product membership with the full marginal).**
With output/preparation row and input/measurement column order $(0,+,-)$,
the joint population matrix is

$$
\Lambda=\begin{pmatrix}
599879/1271415&383116/1271415&0\\
671536/1271415&1280547842618/1422104377215&4626882/5592605\\
0&4464072/5592605&6558328/5592605
\end{pmatrix}.
\tag{4.1}
$$

In QRC's coordinates, with $\tau=(1,\sqrt2,\sqrt2)^T$ and its
six-plane order $(+,-,2+,2-,\Delta,\Sigma)$,

$$
M_{ij}=\frac{\Lambda_{ij}}{\sqrt{d_id_j}},\qquad
\eta=\left(\frac{507224}{1271415},0,
\frac{\Lambda_{++}}4,\frac{\Lambda_{--}}4,
\frac{2272374}{5592605},\frac{2272374}{5592605}\right).
\tag{4.2}
$$

This point belongs to the exact independent real-product cone, satisfies
$M^T\tau=\tau$, and describes the same channel as (3.3).

Proof. The sector populations of the two representative atoms are

$$
\begin{aligned}
p_{a\mathrm A}&=(0,2313441/5592605,3279164/5592605)^T,&
p_{b\mathrm A}&=(0,81/200,119/200)^T,\\
p_{a\mathrm B}&=(599879/1271415,671536/1271415,0)^T,&
p_{b\mathrm B}&=(119/195,76/195,0)^T.
\end{aligned}
\tag{4.3}
$$

Their outer products give
$\Lambda=(400/119)p_{a\mathrm A}p_{b\mathrm A}^T
 +(195/119)p_{a\mathrm B}p_{b\mathrm B}^T$.
This proves (4.1); its three column sums are exactly $(1,2,2)$.
In QRC Definition 5.1 let $k(a,b)$ be the atom with independent
real unit factors, trivial block $h(a)h(b)^T$ and plane coefficients
$z_\nu(a)^Tz_\nu(b)/2$. Lemma 3.3 identifies the point here as

$$
(M,\eta)=\frac{400}{119}
k(a_{\mathrm A}(0,0),b_{\mathrm A}(0,0))
+\frac{195}{119}k(a_{\mathrm B}(0),b_{\mathrm B}(0)).
\tag{4.4}
$$

The dark/plus coefficient is
$(195/119)(71\cdot94\cdot119\cdot76)/(1271415\cdot195)
=507224/1271415$. Each mixed-plane coefficient is
$(400/119)(1521\cdot166\cdot9\cdot119)/(2\cdot5592605\cdot200)
=2272374/5592605$. The planar traceless coefficient is
$\Lambda_{jj}/4$, and dark/minus is zero. These give (4.2) by
QRC's normalized orthonormal basis, with actual product atoms rather
than a relaxation.

The full normalized Choi state is

$$
\chi_S=\frac15\sum_fc_f(a_fa_f^T)\otimes(b_fb_f^T),\qquad
\operatorname{Tr}_{\rm out}\chi_S=I_5/5.
\tag{4.5}
$$

In particular the three TP coordinate equations represent the whole
matrix marginal, not merely its trace. The dark row sum of $\Lambda$
is $982995/1271415\ne1$, and
$\Lambda_{0+}=383116/1271415\ne671536/1271415=\Lambda_{+0}$.
Thus this channel is nonunital and not self-adjoint. These are properties
of the sufficient example, with no restriction on competitors. $\square$

**Proposition 4.2 (The effect map for this port).** For real symmetric
$E$, put $t_i=\operatorname{tr}(R_iE)$. Then $\mathcal A=S^\dagger$
is exactly

$$
\begin{aligned}
\mathcal A(E)={}&\Lambda_{00}t_0R_0
+\sum_{j=+,-}\frac{\Lambda_{jj}}8(t_jR_j+2R_jER_j)\\
&+\sum_{i\ne j}\frac{\Lambda_{ij}}{d_id_j}\,t_iR_j\\
&+\frac{507224}{1271415}(R_0ER_++R_+ER_0)
+\frac{2272374}{5592605}(R_+ER_-+R_-ER_+).
\end{aligned}
\tag{4.6}
$$

Both sides extend complex linearly after replacing a matrix by its
transpose-symmetric part. In particular $\mathcal A(I)=I$.

Proof. The branch adjoint is
$E\mapsto c_fb_fb_f^T\operatorname{tr}(a_fa_f^TE)$.
In the exact orbit expression, a plane's fourth moment is
$(t_jR_j+2R_jER_j)/8$, while different sectors use independent
second moments. Thus a transfer from input sector $j$ to output
sector $i$ contributes $\Lambda_{ij}t_iR_j/(d_id_j)$ to the
adjoint. Cross terms give the two coefficients already computed in
Proposition 4.1. This is precisely the orientation of QWS Proposition
4.2 with the new joint populations. Both the branch map and its
adjoint annihilate transpose-antisymmetric matrices, so the extension
agrees on all complex matrices.

For $E=I$, $t_i=d_i$ and cross products vanish. The coefficient of
$R_j$ is $\sum_i\Lambda_{ij}/d_j=1$. Hence
$\mathcal A(I)=I$. Using $S$ in place of $\mathcal A$ would transpose
the sector-transfer block and give incorrect residuals. $\square$

## 5. Complete coefficients and exact finite sign certificates

**Definition 5.1 (All fifteen residuals of the same port).** Set
$H_J=\Pi_J-\mathcal A(\Pi_J)$ for every $J\in\mathcal J_{15}$.
All are block diagonal in $L\oplus V$ with entries in $\mathbb Q(r)$.
For complete singleton data put $m=773624781204960$ and write

$$
m\mathcal A(\Pi_s)=
\begin{pmatrix}a&b\\b&c\end{pmatrix}_L
\oplus\begin{pmatrix}d&e&f\\e&g&h\\f&h&k\end{pmatrix}_V.
\tag{5.1}
$$

Each pair $(u,v)$ in the tables denotes the single coefficient $u+vr$.

| $s$ | $a$ | $b$ | $c$ |
| --- | --- | --- | --- |
| $N$ | $(381100912436844,-2322740857236)$ | $(-20095639492440,-4976680236312)$ | $(76811345837016,165599260920)$ |
| $2$ | $(90985226215816,1022645843792)$ | $(-10050785703132,5916526449644)$ | $(96010619067382,-1935617381030)$ |
| $3$ | $(133742070499468,443048430572)$ | $(20101571406264,-1879692426664)$ | $(123691284796336,1382894643904)$ |
| $5$ | $(90985226215816,1022645843792)$ | $(-10050785703132,5916526449644)$ | $(96010619067382,-1935617381030)$ |
| $25$ | $(76811345837016,-165599260920)$ | $(20095639492440,-4976680236312)$ | $(381100912436844,2322740857236)$ |

| $s$ | $d$ | $e$ | $f$ |
| --- | --- | --- | --- |
| $N$ | $(112922286439576,2147461890152)$ | $(-3350261901044,-939846213332)$ | $(10768998356760,-3861555055896)$ |
| $2$ | $(293746764126687,18952023512121)$ | $(-15071729619330,11261467403674)$ | $(-16994028967313,-3677678603847)$ |
| $3$ | $(109577956452356,-9261924310452)$ | $(30143459238660,-2488340118156)$ | $(7424668369540,8765126527692)$ |
| $5$ | $(139430094895199,-8280329881671)$ | $(-15071729619330,-6893434858854)$ | $(-16994028967313,-3677678603847)$ |
| $25$ | $(117947679291142,-3557231210150)$ | $(3350261901044,-939846213332)$ | $(15794391208326,2451785735898)$ |

| $s$ | $g$ | $h$ | $k$ |
| --- | --- | --- | --- |
| $N$ | $(133742070499468,1105445474252)$ | $(-3350261901044,-939846213332)$ | $(112922286439576,2147461890152)$ |
| $2$ | $(87640896228596,-4893880605852)$ | $(-15071729619330,-6893434858854)$ | $(139430094895199,-8280329881671)$ |
| $3$ | $(340909633451964,6968222571708)$ | $(30143459238660,-2488340118156)$ | $(109577956452356,-9261924310452)$ |
| $5$ | $(87640896228596,-4893880605852)$ | $(-15071729619330,11261467403674)$ | $(293746764126687,18952023512121)$ |
| $25$ | $(123691284796336,1714093165744)$ | $(3350261901044,-939846213332)$ | $(117947679291142,-3557231210150)$ |

To derive each entry, substitute $t_i=(R_i)_{ss}$ and
$R_i\Pi_sR_j=(R_ie_s)(R_je_s)^T$ into (4.6), and reduce by
$r^2=17$. The tables sum to $mI$ over $s$, as required by TP.
For every pair, add its two singleton effect matrices and subtract
from $m\Pi_J$. Thus the ten pairs are exactly
$\{N,2\},\{N,3\},\{N,5\},\{N,25\},\{2,3\},\{2,5\},
\{2,25\},\{3,5\},\{3,25\},\{5,25\}$, all for this one channel.

**Lemma 5.2 (Simultaneous minor bounds).** Let $\Delta_k$ denote a
leading $k\times k$ principal minor in the fixed block order. Every
entry in the following table is a strict lower bound, uniform over
all indicated events and signs.

| Events | Matrix | $\Delta_1(L)$ | $\Delta_2(L)$ | $\Delta_1(V)$ | $\Delta_2(V)$ | $\Delta_3(V)$ |
| --- | --- | --- | --- | --- | --- | --- |
| All ten pairs and $\{2\},\{3\},\{5\},\{25\}$ | $(52417/100000)I\pm H_J$ | $1/10$ | $1/100$ | $1/250$ | $1/2000$ | $1/1000000$ |
| $\{N\}$ | $I/2+H_N$ | $1$ | $2/5$ | $1/3$ | $1/10$ | $3/100$ |

Consequently every event other than $N$ has norm below
$52417/100000$, and $H_N\succ-I/2$.

Proof. Integer squaring gives the exact enclosure

$$
r_-:=\frac{4123105625617}{10^{12}}<r<
r_+:=\frac{4123105625618}{10^{12}}.
\tag{5.2}
$$

After reducing by $r^2=17$, define rational lower and upper evaluations

$$
\mathcal L(u+vr)=
\begin{cases}u+vr_-,&v\ge0,\\u+vr_+,&v<0,\end{cases}
\qquad
\mathcal U(u+vr)=
\begin{cases}u+vr_+,&v\ge0,\\u+vr_-,&v<0.\end{cases}
\tag{5.3}
$$

Always $\mathcal L(x)\le x\le\mathcal U(x)$. Coefficient pairs
multiply by
$(u,v)(u',v')=(uu'+17vv',uv'+vu')$. Use determinants $x$,
$xy-u^2$ and

$$
\det\begin{pmatrix}x&u&v\\u&y&w\\v&w&z\end{pmatrix}
=xyz+2uvw-xw^2-yv^2-zu^2.
\tag{5.4}
$$

The exact componentwise minima of $\mathcal L(\Delta_k)$ over the
first row's fourteen events and two signs, in the five-column order,
are

$$
\begin{aligned}
\mathbf m_1=\bigg(&
\frac{3314112062228496699144983}{32234365883540000000000000},\\
&\frac{11117047152782718364064289}{1060435740071266010000000000},\\
&\frac{74001553834953578188307}{15169113356960000000000000},\\
&\frac{8661755674367053479938143696483915327021}
{15585815158708912272643974000000000000000000},\\
&\frac{12374008581540525615548222555049850329394499}
{6234326063483564909057589600000000000000000000000}\bigg).
\end{aligned}
\tag{5.5}
$$

For the second row the five rational lower evaluations are

$$
\begin{aligned}
\mathbf m_2=\bigg(&
\frac{65742763772159683721784551}{64468731767080000000000000},\\
&\frac{146013008268942174562624110493217}
{360548151624230443400000000000000},\\
&\frac{16564743247676126577930379}{48351548825310000000000000},\\
&\frac{1028320525716796652475761983317691651249}
{9351489095225347363586384400000000000000},\\
&\frac{35189018771331516520403183322728471911}
{935148909522534736358638440000000000000}\bigg).
\end{aligned}
\tag{5.6}
$$

Equations (5.1)–(5.4), the displayed event list, and the two choices
of sign specify every identity behind (5.5)–(5.6). All denominators
are positive. Cross multiplication shows that each coordinate strictly
exceeds the corresponding simple table bound. Thus all $140+5=145$
leading principal minors are positive. Sylvester's criterion on
the two real symmetric blocks proves the asserted strict Loewner
and norm bounds. Real symmetric positivity also gives complex
positivity by splitting a vector into real and imaginary parts.
No trace-zero singleton assumption is used. $\square$

**Definition 5.3 (The exact active value).** Define

$$
\begin{gathered}
D_0=64468731767080,\qquad
a_0=32710322397343+193561738103r,\\
b_0=1674636624370+414723353026r,\qquad
c_0=-6400945486418-13799938410r,\\
C_N=\frac1{D_0}\begin{pmatrix}a_0&b_0\\b_0&c_0\end{pmatrix},\\
p(z)=z^2-\frac{a_0+c_0}{D_0}z
             +\frac{a_0c_0-b_0^2}{D_0^2},\\
\lambda=\frac{a_0+c_0+\sqrt{(a_0-c_0)^2+4b_0^2}}{2D_0}.
\end{gathered}
\tag{5.7}
$$

The square root is the nonnegative real one. This specifies every
coefficient of $p$ exactly in $\mathbb Q(\sqrt{17})$.

**Theorem 5.4 (Root isolation and the full event maximum).** The number
$\lambda$ is the unique positive root of $p$, and

$$
\frac{52417656}{10^8}<\lambda<\frac{52417658}{10^8},\qquad
\max_{J\in\mathcal J_{15}}\|H_J\|_{\rm op}=\lambda.
\tag{5.8}
$$

Only the singleton $N$ reaches this event maximum.

Proof. Subtracting the $N$ row of (5.1) from $m\Pi_N$ gives exactly
$H_N|_L=C_N$; here $m=12D_0$. One has $a_0>0$, $b_0>0$, $c_0<0$,
so $a_0c_0-b_0^2<0$. Thus $C_N$ has exactly one positive eigenvalue,
the value in (5.7), and one negative eigenvalue.

For a fully rational root certificate, let
$l=52417656/10^8$, $u=52417658/10^8$. Substitution into (5.7),
reduction by $r^2=17$, and the endpoint rule (5.3) give

$$
\begin{aligned}
p(l)&\le\mathcal U(p(l))
=-\frac{3988244642274334849666846412107}
{901370379060576108500000000000000000000}
<-\frac4{10^9},\\
p(u)&\ge\mathcal L(p(u))
=\frac{14693379189919334662338411340967}
{1802740758121152217000000000000000000000}
>\frac8{10^9}.
\end{aligned}
\tag{5.9}
$$

The unique positive root is therefore between $l$ and $u$.
The $V$ block of $H_N$ is a compression of
$-\mathcal A(\Pi_N)$, hence is nonpositive because the adjoint is
positive. Lemma 5.2 puts every negative eigenvalue of $H_N$ above
$-1/2$. Since $\lambda>l>1/2$, the positive $L$ eigenvalue is its
norm. Every other event has norm below $52417/100000<l$ by the same
lemma. This proves (5.8) for the same single channel. $\square$

## 6. Actual attainment, the narrowed interval and the unmatched dual

**Theorem 6.1 (Exact original-menu error and zero-wait attainment).**
The fixed fourteen-flag port (3.4) has $e(T_\lambda)=\lambda$ for
the full complex-input and actual finite-history suprema. Define

$$
v_0=b_0e_N+(D_0\lambda-a_0)e_{25},\qquad
v=\frac{v_0}{\sqrt{b_0^2+(D_0\lambda-a_0)^2}},\qquad
\rho_\lambda=Dvv^TD^\dagger.
\tag{6.1}
$$

This pure input, actual wait zero, one complete five-outcome read and
Stop attain the error.

Proof. Lemma 3.3 makes the channel stationary on all complex matrices.
Apply the credited identities (1.8)–(1.9), with the actual adjoint
$\mathcal A$ from (4.6). TP permits complementation, so Theorem 5.4
gives an upper $\lambda$ for every complex density input and every
actual finite protocol, including adaptive protocols and permitted
source-independent random controls.

The denominator in (6.1) is nonzero since $b_0>0$. The first row of
$C_Nv_0=\lambda v_0$ holds directly, and its second row is
$(D_0\lambda-a_0)(D_0\lambda-c_0)=b_0^2$, the equation
$p(\lambda)=0$. Thus $H_Nv=\lambda v$. At actual wait zero the
mode-$N$ probability difference for $\rho_\lambda$ and its port
replacement is $v^TH_Nv=\lambda$. The full-read TV is at least
this event difference and at most the proved upper, so is exactly
$\lambda$. The event groups an actual complete read; it does not
require another instrument, a closure angle or a limiting wait.
$\square$

**Corollary 6.2 (Strict improvements on both unrestricted endpoints).**
Under the unchanged contract,

$$
\boxed{\frac{129931}{250000}\le\varepsilon_1\le\lambda},\qquad
\frac{445256}{10^8}<\lambda-\frac{129931}{250000}
<\frac{445258}{10^8}.
\tag{6.2}
$$

Proof. Theorem 2.3 is necessary for all competitors; Theorems 3.2 and
6.1 provide a sufficient legal port. Direct rational comparisons give

$$
\frac{129931}{250000}-\frac{12993}{25000}=\frac1{250000}>0,
\qquad
\lambda<\frac{52417658}{10^8}<\frac{26209}{50000}
<\frac{52427}{100000}<\theta,
\tag{6.3}
$$

where the last inequality is QWS Theorem 5.4. Subtracting the new
necessary endpoint from (5.8) gives the gap in (6.2). The older bounds
retain their domains; the new sufficient example rules out a necessary
lower bound at the former sufficient value $\theta$. $\square$

**Convention 6.3 (The precise remaining event–atom–TP obligation).**
The minimum in QRC Theorem 6.2 still has the whole independent-product
cone and all three TP equations. The following specialization of conic
slackness records how a matching certificate would have to couple them;
it is not a new general duality theorem or an evaluated optimum.

Use QRC's orthonormal $H_i=R_i/\sqrt{d_i}$ and six pairs
$(F_{\nu1},F_{\nu2})$ from its Definition 4.1. Write
$h_i(E)=\operatorname{tr}(H_iE)$ and
$z_\nu(a)=(a^TF_{\nu1}a,a^TF_{\nu2}a)^T$, so
$k(a,b)=(h(aa^T)h(bb^T)^T,(z_\nu(a)^Tz_\nu(b)/2)_\nu)$.
Let one feasible tuple be
$x=(M,\eta)=\sum_fw_fk(a_f,b_f)$, with real unit independent factors,
$w_f\ge0$, $M^T\tau=\tau$, and
$-zI\preceq H_J(x)\preceq zI$ for every $J\in\mathcal J_{15}$.
Choose real PSD multipliers $A_J^\pm$ with
$\sum_J\operatorname{tr}(A_J^++A_J^-)=1$, and put

$$
\begin{gathered}
Z_J=A_J^+-A_J^-,\quad t_J=h(\Pi_J),\quad
\beta=\sum_J\operatorname{tr}(Z_J\Pi_J),\quad
C=\sum_J t_Jh(Z_J)^T,\\
d_\nu=\sum_J\operatorname{tr}(Z_JP_\nu(\Pi_J)),\qquad y\in\mathbb R^3,\\
B_y(a)=\sum_j[\|a\|^2y-C^Th(aa^T)]_jH_j
-\frac12\sum_\nu d_\nu\sum_{k=1}^2z_{\nu k}(a)F_{\nu k}.
\end{gathered}
\tag{6.4}
$$

Here $P_\nu$ is the orthogonal projection onto QRC's $\nu$ plane,
and $H_J(x)=\Pi_J-S_x^\dagger(\Pi_J)$ is that same tuple's residual.
There is the exact identity

$$
\begin{aligned}
z-(\beta-\tau^Ty)
={}&\sum_J\operatorname{tr}\bigl[
A_J^+(zI-H_J(x))+A_J^-(zI+H_J(x))\bigr]\\
&+\sum_fw_fb_f^TB_y(a_f)b_f.
\end{aligned}
\tag{6.5}
$$

Indeed, expanding QRC's channel coefficients gives
$L(x):=\sum_J\operatorname{tr}(Z_JS_x^\dagger(\Pi_J))
=\langle C,M\rangle+\sum_\nu d_\nu\eta_\nu$.
The first sum in (6.5) is $z-\beta+L(x)$. Unit preparation factors
and the full TP equations give $\sum_fw_fh(b_fb_f^T)=\tau$;
the second sum is therefore $\tau^Ty-L(x)$. Adding proves the
identity, with all three marginal multipliers retained.

If $B_y(a)\succeq0$ for every real $a$, every term in (6.5) is
nonnegative. The resulting lower $\beta-\tau^Ty$ on the entire
QRC class transfers to every original complex competitor by QRC's
proved no-worse replacement. That replacement may change the channel.
At equality every positive-weight atom must satisfy
$B_y(a_f)b_f=0$, and each event multiplier is supported on its
corresponding active residual eigenspace. An exposed support restriction
thus requires global atom positivity and matching event–TP equality;
the exhibited two-orbit support cannot be imposed on competitors in
advance. This is the remaining matching-certificate obligation, not a
certificate supplied by the present sufficient example.

## 7. Evidence scope, resources and unresolved bridges

**Convention 7.1 (Finite arithmetic and source correspondence).** The
finite certificates use exact rational pairs for $\mathbb Q(\sqrt{17})$,
with no time mesh or numerical optimization in their proof. Bounded
in-memory rational arithmetic verifies the spectral projections from
the original $K$, the four vector normalizations, the joint population
and plane coefficients, all three TP equations, all 45 singleton
coefficients in (5.1), all 145 minor bounds with the exact minima
(5.5)–(5.6), and both root signs (5.9). The determinant formulas agree
with independent Laplace expansion for these blocks. At the QWS
parameters the same adjoint calculation reproduces all 45 published
singleton coefficients, checking the supplier correspondence rather
than assuming it from a reported check.

For the necessary direction, the retained weighted moment is recovered
from the exact sector lengths in (1.6). The three shifted trace-block
leading minors, the three shifted cross-block determinants, and the
two antisymmetric eigenvalue bounds of QWS Lemma 2.3 are positive
by the rational enclosure (5.2). The witness kernel and complex PSD
pairings are justified by that source's tensor-block decomposition.
Lemma 2.2 then uses an exact operator identity and the full marginal;
it is not an inference from finite samples. These are ordinary finite
arithmetic checks and proofs, without Lean writing or compilation.

**Convention 7.2 (Literature status and use).** The marginal-cap
consequence and the particular attained fourteen-flag certificate are
`repo-derived`. The event–atom–TP identity (6.5) is an explicit
specialization of conic slackness. No worldwide originality follows
from these descriptions. The supplier reductions and witness are
credited in Convention 1.3 and are not new results of this volume.

| Primary source | Exact correspondence and limit |
| --- | --- |
| [Horodecki–Shor–Ruskai, quant-ph/0302031v2, Theorem 4(A–D)](https://arxiv.org/html/quant-ph/0302031v2) | `literature-attested`: measure-and-prepare, separable Choi and rank-one Kraus equivalences. Their CPTP version separately requires a POVM or $\sum_fC_f^\dagger C_f=I$. Equation (3.6) proves that normalization directly; (4.5) fixes output-first Choi order. |
| [Doherty–Parrilo–Spedalieri, quant-ph/0308032v3, §VI and §VI.1](https://arxiv.org/html/quant-ph/0308032v3) | `literature-attested`: decomposable witnesses and product-form positivity certificates. The lower uses the explicit QWS witness and PSD weak duality. Hierarchy completeness or a positive relaxed point supplies no matching endpoint or legal port here. |
| [Ohst et al., 2411.08110v2, §3.3 and Appendix C.3](https://arxiv.org/html/2411.08110v2) | `literature-attested`: constrained separability and alternating feasible-factor optimization have their specified per-factor constraints and objectives. A summed TP marginal is not a constraint on each factor separately, and a candidate from alternating optimization is not an optimality certificate for (1.3). |

The explicit atoms avoid a separability-extraction hypothesis. No
low-dimensional PPT sufficiency, flat extension, irreducible-group
fidelity optimum, diamond-norm result or general decidability theorem
is used to evaluate this $5\times5$ actual-menu problem.

**Definition 7.3 (Unmatched obligations and exposure).** The exact
original $\varepsilon_1$, a matching globally necessary certificate
and globally optimal legal port remain open. No optimality even within
the displayed orbit family is claimed. The full independent-product
cone, nonsymmetric $M$, full marginal and all fifteen events remain
part of that problem. The source obstructions in QPC §9 persist:
there is no assumed full $O(5)$ menu invariance, real rank-one
decomposition of an unchanged real Choi matrix, or rank-preserving
definite-character Kraus decomposition. QRC's real replacement does
not impose $a=b$, unitality, self-adjointness or a two-orbit support.
Neither direction replaces separability by PPT.

The $q=2,3,4$ frontiers, native all-size cofinality and memory-rate
questions, preparation from the native $\alpha/\beta$ relations,
and the general mutual-recovery bridges among space, time, boundary
and memory remain open. This result uses the independent preparation
hypothesis of Assumption 1.1 and does not settle those bridges.

Fourteen fixed finite scalar flags, rank-one composite Kraus matrices
and exact algebraic coefficients suffice for this mathematical design.
The attaining protocol uses wait zero and one complete read. Coefficient
synthesis, finite-precision robustness, physical acquisition, clocks,
storage duration and transport are separate resources with no bound
proved here. Finite lower-witness alternatives are not a
sample-complexity or channel-identification result. Evidence consists
of the cited public sources and ordinary derivations with bounded exact
arithmetic; repository and model priors do not supply proof or a claim
of statistical independence.

## 追加锚（本行以下为增补区）
