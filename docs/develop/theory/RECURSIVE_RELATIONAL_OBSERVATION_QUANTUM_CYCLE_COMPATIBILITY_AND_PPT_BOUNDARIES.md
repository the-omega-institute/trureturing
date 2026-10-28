# Recursive relational observation: cycle compatibility and PPT boundaries

## 1. The original walk, scalar ports and sector coordinates

**Assumption 1.1 (Preparation and actual histories).** Use the independent
quantum preparation hypothesis of
[QMB, Assumption 1.1](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md).
The Hilbert space is $\mathbb C^5$ with ordered orthonormal basis
$\mathsf S=(N,2,3,5,25)$, every complex density matrix is an allowed
input, and

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

An actual future protocol uses only nonnegative waits, the complete
five-outcome rank-one Lüders instrument
$X\mapsto(\Pi_sX\Pi_s)_{s\in\mathsf S}$, with
$\Pi_s=e_se_s^\dagger$, and Stop. All finite adaptive depths are
included. Histories retain outcomes, controls and stops. Initial
controls and permitted random controls are source-independent, and
both comparisons use the same policy. Grouping complete-read outcomes
is classical postprocessing, not a coarse-block Lüders instrument.
There are no independent mode phases, arbitrary future unitaries,
source copies, resets, probability oracles, readable hidden Kraus
records or external quantum side information. This source is not a
preparation derived from the native $\alpha/\beta$ relations or from
a different tensor-cut model; $N$ labels a unit vector.

**Definition 1.2 (The unchanged scalar-port problem).** Let
$\mathfrak C_1$ consist of composites of fixed CPTP maps

$$
\operatorname{Enc}:M_5\longrightarrow\bigoplus_{f\in F}M_1,
\qquad
\operatorname{Dec}((y_f)_f)=\sum_f\operatorname{Dec}_f(y_f),
\qquad \operatorname{Dec}_f:M_1\longrightarrow M_5,
\tag{1.2}
$$

where $F$ is finite and every decoder is CPTP on its whole scalar
block. The design precedes both the input and the future policy.
All quantum information traverses the port, without original-input
retention, entangled assistance or bypass. Flags are free for this
quantum-dimension criterion, are consumed in decoding, and are not
additionally exposed to the future policy. Every complex CPTP
competitor is included. With one replacement before the common
protocol, define

$$
e(T)=\sup_{\rho\in\mathcal D(\mathbb C^5)}
\sup_{\pi\ {\rm actual,finite}}
\operatorname{TV}(P_\rho^\pi,P_{T(\rho)}^\pi),\qquad
\varepsilon_1=\inf_{T\in\mathfrak C_1}e(T).
\tag{1.3}
$$

TV is half the $\ell^1$ distance, or its measure version for random
controls. CPTP legality includes every reference extension; performance
tests only the system's actual histories.

**Definition 1.3 (The actual $1+2+2$ representation).** Use the passive
real frame and spectral projections of
[QRC, Definitions 1.3 and 3.1](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_REAL_PORT_BOUNDARY_COORDINATES.md):

$$
\begin{gathered}
D=\operatorname{diag}(1,i,i,i,1),\quad A=-iD^\dagger KD,
\quad O(t)=e^{tA}=D^\dagger U(t)D,\\
B=-A^2,\quad r=\sqrt{17},\quad \mu_\pm=(5\pm r)/2,
\quad \omega_\pm=\sqrt{\mu_\pm},\\
R_\pm=\frac{B(B-\mu_\mp I)}{\mu_\pm(\mu_\pm-\mu_\mp)},
\quad R_0=I-R_+-R_-=dd^T,\quad d=(e_2-e_5)/\sqrt2,\\
u_\pm=\frac{R_\pm e_N}{\sqrt{(1\pm1/r)/2}},\quad
v_\pm=Au_\pm/\omega_\pm,\quad W_\pm=AR_\pm/\omega_\pm,\\
G(\theta,\phi)=R_0+\cos\theta R_++\sin\theta W_+
                         +\cos\phi R_-+\sin\phi W_-,\\
\mathsf J=\operatorname{diag}(1,-1,-1,-1,1).
\end{gathered}
\tag{1.4}
$$

Let $I=\{0,+,-\}$, $V_i=R_i\mathbb R^5$ and
$(n_0,n_+,n_-)=(1,2,2)$. The vector list
$(d,u_+,v_+,u_-,v_-)$ is orthonormal. The actual wait is
$O(t)=G(\omega_+t,\omega_-t)$, and in this adapted basis
$\mathsf J=\operatorname{diag}(-1,1,-1,1,-1)$.
Stationary means commuting with every $\operatorname{Ad}_{O(t)}$;
reflected means commuting with $\operatorname{Ad}_{\mathsf J}$.
The two-angle torus is the closure of the nonnegative wait orbit,
as in QPC Lemma 6.2. It is a mathematical design group, not an
additional future control. All transposes below refer to this frame.

**Definition 1.4 (The supplied complete coefficient space).** Put
$H_i=R_i/\sqrt{n_i}$ and $\tau=(1,\sqrt2,\sqrt2)^T$.
For orthogonal unit vectors set
$F(a,b)=(ab^T+ba^T)/\sqrt2$. Use the six orthonormal pairs of QRC
Definition 4.1, in the order $\mathcal N=\{+,-,2+,2-,\Delta,\Sigma\}$:

$$
\begin{aligned}
+ &: F(d,u_+),\ F(d,v_+),\\
- &: F(d,u_-),\ F(d,v_-),\\
2+ &: (u_+u_+^T-v_+v_+^T)/\sqrt2,\ F(u_+,v_+),\\
2- &: (u_-u_-^T-v_-v_-^T)/\sqrt2,\ F(u_-,v_-),\\
\Delta &: [F(u_+,u_-)+F(v_+,v_-)]/\sqrt2,\quad
          [F(v_+,u_-)-F(u_+,v_-)]/\sqrt2,\\
\Sigma &: [F(u_+,u_-)-F(v_+,v_-)]/\sqrt2,\quad
          [F(v_+,u_-)+F(u_+,v_-)]/\sqrt2.
\end{aligned}
\tag{1.5}
$$

Call these $F_{\nu1},F_{\nu2}$ and let
$P_\nu(E)=\sum_{a=1}^2\operatorname{tr}(F_{\nu a}E)F_{\nu a}$.
For $x=(M,\eta)\in M_3(\mathbb R)\times\mathbb R^6$, define

$$
\begin{aligned}
S_x(E)&=\sum_{i,j}M_{ij}\operatorname{tr}(H_jE)H_i
                       +\sum_\nu\eta_\nu P_\nu(E),\\
Z(x)&=\sum_{i,j}M_{ij}H_i\otimes H_j
       +\sum_\nu\eta_\nu\sum_{a=1}^2F_{\nu a}\otimes F_{\nu a},
\qquad \chi(x)=Z(x)/5.
\end{aligned}
\tag{1.6}
$$

Extend the map complex linearly after replacing a matrix $X$ by
$(X+X^T)/2$. Choi order is output first, input second, so
$S_x(X)=\operatorname{Tr}_{\rm in}[(I\otimes X^T)Z(x)]$.
Each $Z(x)$ is invariant under transposition of either factor.
QRC's commutant calculation makes $S_x$ stationary and reflected.
The full TP equation is

$$
\operatorname{Tr}_{\rm out}Z(x)=\sum_j(M^T\tau)_jH_j=I_5,
\qquad M^T\tau=\tau.
\tag{1.7}
$$

In particular $Z(x)\succeq0$ and (1.7) define a complex CPTP map;
they do not assert a scalar-port realization. Write
$\Lambda_{ij}=\sqrt{n_in_j}M_{ij}$. Then (1.7) is exactly
$\sum_i\Lambda_{ij}=n_j$ for each column, with no omitted
marginal component. No unitality or symmetry of $M$ is imposed.

For independent real vectors, set

$$
\begin{gathered}
h_i(a)=a^TH_ia,\quad
z_\nu(a)=(a^TF_{\nu1}a,a^TF_{\nu2}a)^T,\\
k(a,b)=\left(h(a)h(b)^T,
                (z_\nu(a)^Tz_\nu(b)/2)_{\nu\in\mathcal N}\right),\\
\mathcal K=\operatorname{cone}\{k(a,b):a,b\in\mathbb R^5,
                                         \ \|a\|=\|b\|=1\}.
\end{gathered}
\tag{1.8}
$$

Cone means finite nonnegative sums; the formula also defines the
homogeneous extension to unnormalized vectors. QRC Theorem 5.2
identifies $\mathcal K$ with the independent real-product Choi cone
in (1.6). Its TP slice is the selected scalar-port class. QRC
Theorems 2.2 and 3.2 give every original complex scalar port a
possibly different no-worse representative in this class. These
supplier reductions do not place an optimizer on any face below.

**Definition 1.5 (All events and the normalization convention).** Let
$\mathcal J_{15}=\{J\subseteq\mathsf S:1\le|J|\le2\}$ and
$\Pi_J=\sum_{s\in J}\Pi_s$. For $t_J=(\operatorname{tr}(H_i\Pi_J))_i$,
the same channel's adjoint residual is

$$
\mathcal H_J(x)=\Pi_J-S_x^\dagger(\Pi_J)
 =\sum_i[t_J-M^Tt_J]_iH_i
          +\sum_\nu(1-\eta_\nu)P_\nu(\Pi_J).
\tag{1.9}
$$

The adjoint uses $M^T$, even for nonunital, non-self-adjoint maps.
QMB Theorem 2.1 and QRC Theorem 3.2 give, for any CPTP $S_x$,

$$
e\bigl(DS_x(D^\dagger\,\cdot\,D)D^\dagger\bigr)
 =\max_{J\in\mathcal J_{15}}\|\mathcal H_J(x)\|_{\rm op}.
\tag{1.10}
$$

This identity applies also to nonseparable CPTP points of (1.6).
The scalar-port/measure-and-prepare/separable-Choi/rank-one-Kraus
equivalence is the mature result of
[Horodecki–Shor–Ruskai, quant-ph/0302031v2, Theorem 4(A–D)](https://arxiv.org/pdf/quant-ph/0302031v2).
Their CPTP version additionally requires a POVM, equivalently
$\sum_fC_f^\dagger C_f=I$. In output-first order a scalar-port
Choi state has the normalization
$\chi=\frac15\sum_f\sigma_f\otimes E_f^T$ with
$\sigma_f\succeq0$, $\operatorname{tr}\sigma_f=1$,
$E_f\succeq0$ and $\sum_fE_f=I$.

These are also the conventions of the repository interfaces
[QuantumChannel](../../../D5/S3/Quantum/Foundation/FiniteStateChannel.lean),
[finite_kraus_quantum_channel](../../../D5/S3/Quantum/Foundation/FiniteKrausChannel.lean)
and [finite_kraus_instrument_born_marginal](../../../D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean):
rectangular encoder rows have domain $\mathbb C^5$ and codomain
$\mathbb C$, decoder columns have domain $\mathbb C$ and codomain
$\mathbb C^5$, and decoded branch traces equal their Born weights.
These interface identifications do not constitute a formalization
of the statements below.

## 2. The saturated walk-sector face and its exact factors

**Definition 2.1 (The specified face coordinates).** For real
$\Lambda\in M_3(\mathbb R)$ and real symmetric
$\Gamma\in M_3(\mathbb R)$ with $\Gamma_{ii}=\Lambda_{ii}$,
let $x(\Lambda,\Gamma)$ have

$$
\begin{gathered}
M_{ij}=\Lambda_{ij}/\sqrt{n_in_j},\qquad
\eta_+=\Gamma_{0+},\quad\eta_-=\Gamma_{0-},\\
\eta_{2+}=\Lambda_{++}/4,\quad
\eta_{2-}=\Lambda_{--}/4,\qquad
\eta_\Delta=\eta_\Sigma=\Gamma_{+-}/2.
\end{gathered}
\tag{2.1}
$$

The planar saturation equations on a general tuple are
$\Lambda_{++}-4\eta_{2+}=\Lambda_{--}-4\eta_{2-}=0$.
They describe a face of $\mathcal K$, because the two functionals
are nonnegative on every product generator.

**Theorem 2.2 (Factorization on the actual saturated face).** Every
$x\in\mathcal K$ satisfying the two planar saturation equations
has $\eta_\Delta=\eta_\Sigma$ and is of the form (2.1).
For the tuple (2.1), membership in $\mathcal K$ is equivalent to
the existence of finitely many real vectors
$\alpha_f,\beta_f\in\mathbb R^3$ such that

$$
\Lambda_{ij}=\sum_f\alpha_{fi}^2\beta_{fj}^2,\qquad
\Gamma_{ij}=\sum_f(\alpha_{fi}\beta_{fi})
                         (\alpha_{fj}\beta_{fj}).
\tag{2.2}
$$

For this same $Z(x)$, complex separability is also equivalent to
(2.2). A channel additionally requires all three equations
$\sum_i\Lambda_{ij}=n_j$.

Proof. For an unnormalized real product atom put
$p_i=\|R_ia\|^2$, $q_i=\|R_ib\|^2$ and
$s_i=(R_ia)^T(R_ib)$. In a plane, direct substitution in (1.5)
gives

$$
\Lambda_{jj}=p_jq_j,\quad
4\eta_{2j}=2s_j^2-p_jq_j,\quad
\Lambda_{jj}-4\eta_{2j}
 =2(p_jq_j-s_j^2)=2\det(a_j,b_j)^2\ge0.
\tag{2.3}
$$

Here $a_j,b_j$ are the two real plane coordinates, and
$j\in\{+,-\}$. Equality in a nonnegative sum forces equality
for every positive-weight term of every generator decomposition.
Thus its preparation and measurement components are collinear in
each plane, including the possibility that one or both are zero.
Choose a common unit direction in each plane and signed amplitudes
$\alpha_j,\beta_j$ along it. Rotate both factors together so those
directions are $u_+,u_-$; the atom coordinates are unchanged.
The dark coordinates are the signed amplitudes $\alpha_0,\beta_0$.
No division by a zero component is involved.

For these radial vectors the complete coefficient identities are

$$
\begin{aligned}
\Lambda_{ij}&=\alpha_i^2\beta_j^2,&
\eta_{0j}&=(\alpha_0\beta_0)(\alpha_j\beta_j),\\
\eta_{2j}&=\alpha_j^2\beta_j^2/4,&
\eta_\Delta=\eta_\Sigma
 &= (\alpha_+\beta_+)(\alpha_-\beta_-)/2.
\end{aligned}
\tag{2.4}
$$

Here $\eta_{0+}=\eta_+$ and $\eta_{0-}=\eta_-$.
Absorb a generator's nonnegative weight into the squared norm of
its preparation factor. Summing (2.4) proves (2.2), including
the diagonal identity and both mixed planes.

Conversely, embed each pair of factors in the original real space by

$$
\widetilde a_f=\alpha_{f0}d+\alpha_{f+}u_+
                                  +\alpha_{f-}u_-,\qquad
\widetilde b_f=\beta_{f0}d+\beta_{f+}u_+
                                  +\beta_{f-}u_-.
\tag{2.5}
$$

Formula (2.4) shows that their finite sum of homogeneous atoms is
exactly (2.1). Normalize nonzero factors and absorb their squared
norms into nonnegative weights; omit a zero product. This proves
membership in $\mathcal K$ with every coefficient retained.

For the complex assertion, suppose $Z(x)$ is a finite sum of complex
positive product matrices. Apply $\mathcal R(Y)=(Y+Y^T)/2$ to
each factor of this decomposition. On a Hermitian positive matrix,
$\mathcal R(Y)$ is real symmetric positive: test real vectors,
then split a complex test vector into its real and imaginary parts.
Separate-transpose invariance of the whole $Z(x)$ makes
$(\mathcal R\otimes\mathcal R)Z(x)=Z(x)$.
Real spectral decompositions of the resulting factors therefore give
a real product decomposition of the unchanged matrix. Averaging
these finitely many products by the QRC torus/reflection formula
returns exactly its coordinates in $\mathcal K$. The forward
implication is immediate from that formula. This argument uses a
positive operation on each product factor, not a claim that
transposition or $\mathcal R$ is CP on arbitrary bipartite matrices.
Finally (1.7) proves the full-marginal assertion. $\square$

The factors in (2.2) are the real instance of the established PCP/TCP
factorizations. In the original convention of
[Johnston–MacLean, 1807.06897v1, Definition 1](https://arxiv.org/pdf/1807.06897v1),
the pair is $(X,Y)=(\Gamma,\Lambda)$. In
[Singh–Nechita, 2010.07898v2, Definitions 2.6–2.7](https://arxiv.org/pdf/2010.07898v2),
the order is $(A,B)=(\Lambda,\Gamma)$ and the real factors give
the TCP triple $(\Lambda,\Gamma,\Gamma)$. Their Theorem 2.9
concerns diagonal-sign invariant bipartite matrices. The correspondence
here is the explicit map (2.1), (2.4) and (2.5), with multiplicities
$(1,2,2)$; it is not an identification of that sign group with the
walk torus or a substitution of a $\mathbb C^3$ preparation source.

**Theorem 2.3 (The full $25$-dimensional positivity test on this face).**
For the tuple (2.1),

$$
Z(x)\succeq0\quad\Longleftrightarrow\quad
\Lambda_{ij}\ge0\ (i,j\in I),\quad\Gamma\succeq0,
\quad\Lambda_{ij}\Lambda_{ji}\ge\Gamma_{ij}^2\ (i<j).
\tag{2.6}
$$

Whenever positive, this matrix is PPT. Conditions (2.6) do not
by themselves imply (2.2).

Proof. Choose real orthonormal bases $\mathcal B_i$ of $V_i$,
and write $\Omega_i=\operatorname{vec}(R_i)/\sqrt{n_i}$.
On $\operatorname{span}(\Omega_0,\Omega_+,\Omega_-)$ the matrix
is $[\Gamma_{ij}/\sqrt{n_in_j}]_{ij}$, a congruence of $\Gamma$.
In each plane $V_j\otimes V_j$, the sum
$\sum_aF_{2j,a}\otimes F_{2j,a}$ has eigenvalues $1,0,0,-1$
on the trace, two symmetric traceless, and antisymmetric directions.
Consequently the last three directions of $Z(x)$ have eigenvalues
$\Lambda_{jj}/4,\Lambda_{jj}/4,0$.

For $i<j$ and $a\in\mathcal B_i,b\in\mathcal B_j$, the ordered
pair $(a\otimes b,b\otimes a)$ carries the block

$$
\frac1{n_in_j}
\begin{pmatrix}\Lambda_{ij}&\Gamma_{ij}\\
                \Gamma_{ij}&\Lambda_{ji}\end{pmatrix}.
\tag{2.7}
$$

There are $n_in_j$ copies for each pair of sectors. These orthogonal
blocks exhaust $3+3+3+2(2+2+4)=25$ dimensions. Their elementary
PSD conditions are precisely (2.6). Separate-transpose invariance
in (1.6) proves PPT. The analogous diagonal-sign block calculation
is mature; compare Singh–Nechita Lemma 2.12. The multiplicities
and normalizations in (2.7) are those of this walk. The example in
§4 proves the final assertion. $\square$

## 3. The three-sector cycle and a finite legal scalar port

**Theorem 3.1 (Exact cycle compatibility under explicit additional
hypotheses).** In (2.1) suppose

$$
\Gamma=tt^T,\quad t_i>0,\quad\Lambda_{ii}=t_i^2,
\quad\Lambda_{ij}>0,\quad
\Lambda_{ij}\Lambda_{ji}=t_i^2t_j^2\quad(i\ne j).
\tag{3.1}
$$

Then $x(\Lambda,\Gamma)\in\mathcal K$ if and only if

$$
\sigma:=
\frac{\Lambda_{0+}\Lambda_{+-}\Lambda_{-0}}
     {\Lambda_{+0}\Lambda_{-+}\Lambda_{0-}}=1.
\tag{3.2}
$$

With all three TP equations $\sum_i\Lambda_{ij}=n_j$, this
is equivalent to a legal complex scalar-port realization of this
specified whole channel. When it holds, a single radial generator
and its $25$ fixed quadrature flags suffice. The two face equations,
rank-one $\Gamma$, strictly positive $t_i$ and pair saturations
are hypotheses; none is asserted for an unrestricted optimizer.

Proof. In a factorization (2.2), put
$c_f=(\alpha_{fi}\beta_{fi})_i$. The rank-one equation
$\sum_fc_fc_f^T=tt^T$ forces $c_f=s_ft$ for real scalars
$s_f$, with $\sum_fs_f^2=1$. Indeed each vector orthogonal to
$t$ has a sum of squared pairings equal to zero. At least one
$s_f$ is nonzero, and that term has every $\alpha_{fi}$ and
$\beta_{fi}$ nonzero.

For $i\ne j$ form the real vectors, indexed by $f$,
$U_f=\alpha_{fi}\beta_{fj}$ and $V_f=\alpha_{fj}\beta_{fi}$.
Their squared norms are $\Lambda_{ij},\Lambda_{ji}$, and their
inner product is $\Gamma_{ij}=t_it_j>0$. Equality in
Cauchy–Schwarz, from (3.1), gives

$$
U=\kappa_{ij}V,\qquad
\kappa_{ij}=\frac{\Lambda_{ij}}{t_it_j}>0,\qquad
\kappa_{ij}\kappa_{ji}=1.
\tag{3.3}
$$

On a term of full support, multiply the three ratios in the
orientation $0\to+\to-\to0$. All factor entries cancel, giving
$\kappa_{0+}\kappa_{+-}\kappa_{-0}=1$. By the reciprocal
relations, (3.2) is the square of this product; hence it is one.

Conversely, (3.2) and positivity make that product one. Therefore
there are positive $r_i$ with $\kappa_{ij}=r_i/r_j$ for all
pairs: take $r_0=1$, $r_+=1/\kappa_{0+}$,
$r_-=1/\kappa_{0-}$, and use the cycle for the remaining pair.
Set

$$
\alpha_i=\sqrt{t_ir_i},\qquad
\beta_i=\sqrt{t_i/r_i}.
\tag{3.4}
$$

Then $\alpha_i^2\beta_j^2=\Lambda_{ij}$ and
$(\alpha_i\beta_i)(\alpha_j\beta_j)=\Gamma_{ij}$.
Theorem 2.2 gives the single homogeneous generator.
That theorem and the HSR correspondence also show that allowing
arbitrary complex scalar-port factors does not evade necessity.

For the promised port, embed (3.4) by (2.5), and put

$$
a=\widetilde a/\|\widetilde a\|,\qquad
b=\widetilde b/\|\widetilde b\|,\qquad
w=\|\widetilde a\|^2\|\widetilde b\|^2.
\tag{3.5}
$$

The TP columns give
$\|\alpha\|^2\beta_j^2=n_j$ for every $j$; in particular
$w=\sum_{i,j}\Lambda_{ij}=5$. For $0\le k,l<5$ put
$g_{kl}=G(2\pi k/5,2\pi l/5)$ and define

$$
\begin{gathered}
B_{kl}=\sqrt{w/25}\,(g_{kl}b)^TD^\dagger,
\qquad R_{kl}=Dg_{kl}a,\\
\operatorname{Enc}(X)=(B_{kl}XB_{kl}^\dagger)_{kl},\qquad
\operatorname{Dec}_{kl}(y)=R_{kl}yR_{kl}^\dagger.
\end{gathered}
\tag{3.6}
$$

Both vectors in (3.5) are radial. The group element
$G(\pi,\pi)\mathsf J$ acts as $-I$ on their radial subspace,
so their joint product projector's torus average is already reflected.
The quartic Fourier support lies in $|m|+|n|\le4$; only the zero
frequency survives both five-point sums. Thus the finite sum is
exactly $Z(x)$, by the credited quadrature in
[QAP, Theorem 2.3](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_ATOM_POSITIVITY_AND_SUPPORT.md).
No continuous flag or future choice of angles is introduced.
Its matrix marginal, or the TP column identity above, gives
$\sum_{kl}B_{kl}^\dagger B_{kl}=I_5$; and
$R_{kl}^\dagger R_{kl}=1$. Each sandwich remains positive at
every reference extension. Hence the encoder and every whole-block
decoder are CPTP, the composite matrices have rank one, and flags
are consumed in decoding. This is an actual fixed scalar port.
Its original all-history error is (1.10), not an unevaluated
relaxation used as an upper. $\square$

The equality mechanisms in this proof are mature: rank-one PSD sums,
equality in Cauchy–Schwarz, and consistency of ratios around a
cycle. Singh–Nechita Theorem 5.13, pp. 22–23, uses rank-one factors
and saturated AM–GM for PCP/TCP extreme rays. Johnston–MacLean
Example 1, p. 5, already has
$X=\mathbf1\mathbf1^T$ and
$Y=\left(\begin{smallmatrix}1&a&1/a\\1/a&1&a\\a&1/a&1\end{smallmatrix}\right)$,
which satisfy all pair inequalities but are PCP exactly when $a=1$.
Thus cyclic failure of pairwise consistency is not a new phenomenon.
The walk-space face, its full TP slice and the port (3.6) are the
specific correspondence proved here. No assertion about arbitrary
complex PCP pairs having real factors is needed.

## 4. One cyclic Choi family and its original-space TP normalizations

**Definition 4.1 (A common seed and one positive-product witness).**
Use sector bases $\mathcal B_0=(d)$,
$\mathcal B_+=(u_+,v_+)$ and $\mathcal B_-=(u_-,v_-)$. Put

$$
\begin{gathered}
\mathcal Q_{ij}=\sum_{a\in\mathcal B_i,b\in\mathcal B_j}
(ab^T+ba^T)\otimes(ab^T+ba^T),\qquad i<j,\\
\mathcal T_j=\sum_{a=1}^2F_{2j,a}\otimes F_{2j,a},
\qquad j\in\{+,-\},\\
e(\xi)=\begin{pmatrix}1&\xi&1/\xi\\
                         1/\xi&1&\xi\\
                         \xi&1/\xi&1\end{pmatrix},\qquad \xi>0,\\
Z_\xi=\sum_{i,j}e_{ij}(\xi)R_i\otimes R_j
            +\mathcal T_++\mathcal T_-+\sum_{i<j}\mathcal Q_{ij},\\
W=\sum_iR_i\otimes R_i
       +R_0\otimes R_++R_+\otimes R_-+R_-\otimes R_0
       -\tfrac12\sum_{i<j}\mathcal Q_{ij}.
\end{gathered}
\tag{4.1}
$$

All these are matrices on the original $\mathbb C^5\otimes\mathbb C^5$.
The seed $Z_\xi$ is not TP. Its input marginal is
$\sum_jm_jR_j$, where

$$
m_j=\sum_i n_ie_{ij},\qquad
m=(1+2/\xi+2\xi,\ 2+\xi+2/\xi,\ 2+2\xi+1/\xi).
\tag{4.2}
$$

Define the mathematical input congruence and paired witness by

$$
C_\xi=\sum_jm_j^{-1/2}R_j,\qquad
Z'_\xi=(I\otimes C_\xi)Z_\xi(I\otimes C_\xi),\quad
\chi'_\xi=Z'_\xi/5,\qquad
W'_\xi=(I\otimes C_\xi^{-1})W(I\otimes C_\xi^{-1}).
\tag{4.3}
$$

This is a construction of channel data, not a permitted future
filter or a diagonal similarity theorem. In particular the
diagonal invariance in
[Nechita–Singh, 2007.11219v2, Lemma B.2](https://arxiv.org/pdf/2007.11219v2)
is a congruence statement, not a diagonal similarity statement.

**Theorem 4.2 (Exact full-TP PPT channels with a nontrivial cycle).**
For every $\xi>0$, $\chi'_\xi$ is positive, has rank $13$,
is invariant under either partial transpose, and satisfies
$\operatorname{Tr}_{\rm out}\chi'_\xi=I_5/5$. Its channel

$$
T_\xi(X)=D\operatorname{Tr}_{\rm in}
 [(I\otimes(D^\dagger XD)^T)Z'_\xi]D^\dagger
\tag{4.4}
$$

is complex CPTP, stationary and reflected in the passive frame.
It admits a scalar port if and only if $\xi=1$.
The witness $W'_\xi$ is nonnegative on every complex product
vector and

$$
\operatorname{tr}(W'_\xi\chi'_\xi)=(8\xi-7)/5.
\tag{4.5}
$$

Thus for $0<\xi<7/8$ this same full-TP point is separated from
the entire complex scalar-port cone by an explicit witness.

Proof. The seed is the tuple (2.1) with
$\Lambda_{ij}=n_in_je_{ij}$ and $\Gamma_{ij}=n_in_j$.
Its trace-sector block has rank one. Each planar traceless
direction has eigenvalue one, each planar antisymmetric direction
has eigenvalue zero, and each ordered cross-sector block is
$\left(\begin{smallmatrix}e_{ij}&1\\1&e_{ji}\end{smallmatrix}\right)$.
These eight cross blocks have rank one because
$e_{ij}e_{ji}=1$. The rank is therefore $1+4+8=13$.
This proves positivity by the actual block decomposition of
Theorem 2.3, rather than by low-dimensional PPT sufficiency.

Each tensor factor in (4.1) is real symmetric, proving separate
transpose invariance. Its sums are invariant under simultaneous
orthogonal transformations within each $V_i$: the planar traceless
sum and the cross-sector sum are sums over orthonormal matrix bases.
This includes the actual walk and $\mathsf J$. Congruence by
$C_\xi$ preserves those properties and positivity. The traceless
terms have zero partial output trace, so (4.2) and (4.3) give
$\operatorname{Tr}_{\rm out}Z'_\xi=I_5$ exactly. Thus its trace
is five and its channel is CPTP on all complex matrices.

For a literal identification with the original coefficient space,
the coordinates of $Z'_\xi$ are

$$
\begin{gathered}
M'_{ij}=\sqrt{n_in_j}\,e_{ij}/m_j,\\
\eta'=\left(\frac2{\sqrt{m_0m_+}},
\frac2{\sqrt{m_0m_-}},\frac1{m_+},\frac1{m_-},
\frac2{\sqrt{m_+m_-}},\frac2{\sqrt{m_+m_-}}\right).
\end{gathered}
\tag{4.6}
$$

The three column sums of
$\Lambda'_{ij}=n_in_je_{ij}/m_j$ are $(1,2,2)$.
Furthermore (3.1) holds with $t_i=n_i/\sqrt{m_i}$, and the
cycle ratio is $\sigma=\xi^6$. Theorem 3.1 proves the exact
scalar-port assertion, including the complex case. At $\xi=1$
the port (3.6) applies; the other values are not ports.

For universal positivity of the witness, take arbitrary real
$a,b\in\mathbb R^5$, with $p_i=\|R_ia\|^2$,
$q_i=\|R_ib\|^2$ and $s_i=(R_ia)^T(R_ib)$. Its product form is

$$
\Psi(a,b)=\sum_ip_iq_i+p_0q_++p_+q_-+p_-q_0
                   -2(s_0s_++s_0s_-+s_+s_-).
\tag{4.7}
$$

Since $s_is_j\le\sqrt{p_ip_jq_iq_j}$, it is at least
$y^T\mathcal C(p)y$, for $y_i=\sqrt{q_i}$ and

$$
\mathcal C(p)=\begin{pmatrix}
p_0+p_-&-\sqrt{p_0p_+}&-\sqrt{p_0p_-}\\
-\sqrt{p_0p_+}&p_++p_0&-\sqrt{p_+p_-}\\
-\sqrt{p_0p_-}&-\sqrt{p_+p_-}&p_-+p_+
\end{pmatrix}.
\tag{4.8}
$$

Its diagonal is nonnegative. With $(x,y,z)=(p_0,p_+,p_-)$,
its three two-by-two principal minors are
$x^2+xz+yz$, $xy+yz+z^2$, and $xy+xz+y^2$.
Its determinant is

$$
x^2y+y^2z+z^2x-3xyz\ge0
\tag{4.9}
$$

by AM–GM, including zero populations. All principal minors are
nonnegative, so $\mathcal C(p)\succeq0$. This proves (4.7)
nonnegative without sign or support restrictions.

The matrix $W$ lies in
$\operatorname{Sym}_5(\mathbb R)\otimes\operatorname{Sym}_5(\mathbb R)$.
For complex $a=u+iv,b=w+iz$, its product expectation is the sum
of the four real-product expectations at $(u,w),(u,z),(v,w),(v,z)$.
Each is nonnegative by the preceding proof. Hence it is nonnegative
on all complex product vectors. The real invertible local congruence
in (4.3) preserves this property.

For the trace pairing, the diagonal terms contribute
$\sum_i n_i^2=9$, the three directed terms contribute
$(2+4+2)\xi=8\xi$, and the cross terms contribute
$-2(2+2+4)=-16$. The planar traceless terms are orthogonal
to $W$. Thus $\operatorname{tr}(WZ_\xi)=8\xi-7$.
The filters in the pairing cancel, proving (4.5).
Every complex separable matrix has nonnegative pairing with a
complex-product-positive witness, so negative pairing excludes
every complex scalar realization. In the original basis the normalized
Choi matrix and witness are, explicitly,

$$
\chi^{\rm phys}_\xi=(D\otimes\overline D)\chi'_\xi
                         (D^\dagger\otimes D^T),\qquad
W^{\rm phys}_\xi=(D\otimes\overline D)W'_\xi
                         (D^\dagger\otimes D^T).
\tag{4.9a}
$$

This local unitary change preserves PPT, the full input marginal,
complex-product positivity and every trace pairing above. The same
transport applies to the second normalization and the mixtures below.
No additional physical operation is required. $\square$

The quadratic matrix (4.8) is the classical Choi positive-map
mechanism, not a new positive map. Its three-coordinate predecessor
is displayed explicitly in Singh–Nechita Example 7.5, equation (43).
The proof above establishes its all-population lift and complex
extension in the actual sector representation. The cyclic seed
uses the same mature obstruction as Johnston–MacLean Example 1;
the sector multiplicities, normalization and original-channel
consequences are the additional correspondence.

**Proposition 4.3 (A rational joint-population normalization of the same
seed).** At $\xi=1/2$, a second full-TP normalization is

$$
L=\sqrt2R_0+R_++R_-,\qquad
Z_{\rm rat}=\frac17(L\otimes I)Z_{1/2}(L\otimes I).
\tag{4.10}
$$

It has coordinates (2.1) with

$$
\Lambda_{\rm rat}=\frac17\begin{pmatrix}2&2&8\\4&4&2\\1&8&4\end{pmatrix},
\quad
t=(\sqrt{2/7},2/\sqrt7,2/\sqrt7)^T,\quad\Gamma=tt^T,
\tag{4.11}
$$

and
$\eta=(2\sqrt2/7,2\sqrt2/7,1/7,1/7,2/7,2/7)$.
It is PPT of rank $13$, with full input marginal $I_5$ before
division by five, but has no scalar realization. In particular, if
$H=\sum_it_iR_i$ and $W_H=(I\otimes H^{-1})W(I\otimes H^{-1})$,
then $W_H$ is complex-product-positive and

$$
\operatorname{tr}(W_HZ_{\rm rat})=-3/2,\qquad
\operatorname{tr}(W_HZ_{\rm rat}/5)=-3/10.
\tag{4.12}
$$

Proof. The unfiltered joint populations of $Z_{1/2}$ are
$\left(\begin{smallmatrix}1&1&4\\4&4&2\\1&8&4\end{smallmatrix}\right)$.
The output congruence multiplies its dark row by two and its other
rows by one, then divides every entry by seven. This gives (4.11),
whose column sums are $(1,2,2)$. The cross coefficients scale
as products of the sector factors, giving the displayed $\eta$
and $\Gamma$. Positivity, rank and separate transpose invariance
are preserved by this real invertible congruence. The cycle is
$\sigma=(2\cdot2\cdot1)/(4\cdot8\cdot8)=1/64$.

The witness form is the same globally positive form (4.7), with
its input vector replaced by $H^{-1}b$. Its pairing is

$$
\sum_i\frac{\Lambda_{ii}}{t_i^2}
 +\frac{\Lambda_{0+}}{t_+^2}
 +\frac{\Lambda_{+-}}{t_-^2}
 +\frac{\Lambda_{-0}}{t_0^2}
 -2\sum_{i<j}\frac{\Gamma_{ij}}{t_it_j}
=3+\frac32-6=-\frac32.
\tag{4.13}
$$

Division by five proves the normalized value. These are two
normalizations of one cyclic mechanism; their witness scalings
and pairings are not interchangeable. $\square$

## 5. Strict positive PPT separation beyond the saturated face

**Theorem 5.1 (A full-rank family on the original TP slice).** For
$m=(6,13/2,5)$, use exactly $\chi'_{1/2}$ and $W'_{1/2}$
from (4.3), and set

$$
\chi_s=(1-s)\chi'_{1/2}+s\frac{I_{25}}{25},\qquad 0\le s\le1.
\tag{5.1}
$$

For $0\le s<15/112$, this is a PPT, full-TP, stationary and
reflected complex channel Choi state outside the scalar-port cone.
For $0<s<15/112$ it is positive definite. In particular

$$
\chi_{1/10}\succeq I_{25}/250,\qquad
\operatorname{tr}(W'_{1/2}\chi_{1/10})=-19/125.
\tag{5.2}
$$

The separation persists in a relative open neighborhood in the
affine space (1.6) with the full TP marginal. It does not depend
on maintaining the saturation or rank-one hypotheses of §3.

Proof. Both summands in (5.1) have the full marginal $I_5/5$
and the same invariances. Positivity gives
$\chi_s\succeq sI_{25}/25$. The coordinates of its unnormalized
Choi matrix are explicitly

$$
M_s=(1-s)M'_{1/2}+s\tau\tau^T/5,\qquad
\eta_s=(1-s)\eta'_{1/2}.
\tag{5.3}
$$

Thus all three marginal equations still hold. For either plane
the saturation slack is $s n_j^2/5$, which is strictly positive
for $s>0$. The rank-one/pair-saturated criterion is consequently
not invoked for these points.

At $\xi=1/2$, (4.5) is $-3/5$. The filtered witness trace is

$$
\operatorname{tr}W'_{1/2}
 =\sum_i n_i^2m_i
  +n_0n_+m_++n_+n_-m_-+n_-n_0m_0
 =52+45=97.
\tag{5.4}
$$

All cross terms are traceless. Hence

$$
\operatorname{tr}(W'_{1/2}\chi_s)
 =-\frac35(1-s)+\frac{97}{25}s
 =\frac{112s-15}{25}.
\tag{5.5}
$$

This is negative precisely on the stated interval. Theorem 4.2's
global complex-product positivity excludes complex separability
there, and HSR excludes all scalar ports. Substitution gives (5.2).

At an interior value $s>0$, sufficiently small Hermitian
perturbations in this affine space preserve strict positivity and
the strictly negative witness pairing, by their strict margins and
continuity. Separate-transpose invariance then preserves strict PPT
as well. This proves the relative-neighborhood assertion, in contrast
to a result confined to an equality face. Also the witness cannot
be decomposable as $P+Q^{\Gamma_{\rm in}}$ with $P,Q\succeq0$:
such a form pairs nonnegatively with every PPT state, contradicting
(5.5). The indecomposable mechanism is the credited Choi mechanism;
(5.1)–(5.5) give its exact walk-space robustness. $\square$

## 6. The same fifteen events and actual finite histories

**Proposition 6.1 (All-event feasibility of the nonseparable example).**
For the actual channel $T_{1/2}$ in (4.4),

$$
\frac35<e(T_{1/2})<\frac23.
\tag{6.1}
$$

The upper holds for all complex density inputs and all actual finite
adaptive histories. It is a bound on a PPT channel, not a scalar-port
upper bound for $\varepsilon_1$.

Proof. The following exact adjoint formula specifies every event
of this one channel. For real symmetric $E$ let
$r_i(E)=\operatorname{tr}(R_iE)$ and write

$$
\begin{aligned}
\mathcal A_\xi^0(E)={}&\sum_{i,j}e_{ij}(\xi)r_i(E)R_j\\
 &+\sum_{j=+,-}\left[R_jER_j-\tfrac12r_j(E)R_j\right]\\
 &+2\sum_{i<j}(R_iER_j+R_jER_i),\\
\mathcal A_\xi(E)={}&C_\xi\mathcal A_\xi^0(E)C_\xi,
\qquad H_J=\Pi_J-\mathcal A_{1/2}(\Pi_J).
\end{aligned}
\tag{6.2}
$$

The first line has output population $r_i$ multiplying input sector
$R_j$, as required for an adjoint. Formula (1.5) gives the plane
and cross terms directly; input congruence gives the last line.
All formulas extend after taking the transpose-symmetric part.
In particular $\mathcal A_\xi(I)=I$ by the same column sums.

Here is a finite rational certificate for all fifteen strict bounds
$-\frac23I\prec H_J\prec\frac23I$. Use the fixed block order
$L=(N,25)$ and $V=(2,3,5)$. The spectral projections in (1.4)
have no cross blocks and are

$$
\begin{aligned}
R_+|_L&=\begin{pmatrix}(r+1)/(2r)&2/r\\2/r&(r-1)/(2r)\end{pmatrix},\\
R_+|_V&=\begin{pmatrix}
(r+3)/(4r)&1/r&(r+3)/(4r)\\
1/r&(r-3)/(2r)&1/r\\
(r+3)/(4r)&1/r&(r+3)/(4r)
\end{pmatrix},\\
R_0|_L&=0,\quad
R_0|_V=\tfrac12\begin{pmatrix}1&0&-1\\0&0&0\\-1&0&1\end{pmatrix},
\qquad R_-=I-R_0-R_+.
\end{aligned}
\tag{6.3}
$$

Let $N_*=10^{18}$. Each positive root in the first row lies
strictly between $k/N_*$ and $(k+1)/N_*$ with the corresponding
integer in the second row:

$$
\begin{array}{c|rrrr}
\text{root}&\sqrt{17}&1/\sqrt6&\sqrt{2/13}&1/\sqrt5\\\hline
k&4123105625617660549&408248290463863016&
392232270276368063&447213595499957939
\end{array}.
\tag{6.4}
$$

Integer squaring proves these brackets. Substitute them into (6.3),
$C_{1/2}=R_0/\sqrt6+\sqrt{2/13}R_++R_-/\sqrt5$, and (6.2).
Use rational interval addition, multiplication by the minimum and
maximum of the four endpoint products, and reciprocal
$[a,b]^{-1}=[1/b,1/a]$ for a positive interval. Evaluate each
leading determinant by its permutation expansion. For every
singleton and every pair $J$, and each of the two signs, the
resulting rational lower endpoints are at least the corresponding
entry below:

| Matrix | $\Delta_1(L)$ | $\Delta_2(L)$ | $\Delta_1(V)$ | $\Delta_2(V)$ | $\Delta_3(V)$ |
| --- | --- | --- | --- | --- | --- |
| $(2/3)I\pm H_J$ | $59789/10^6$ | $13675/10^6$ | $53637/10^6$ | $16426/10^6$ | $10202/10^6$ |

The inputs to these $15\cdot2\cdot5=150$ finite rational
inequalities are completely specified by (6.2)–(6.4), the five
singletons and all ten unordered pairs of $\mathsf S$; both signs
use the same channel. Each tabulated bound is positive. Sylvester's
criterion on the two real symmetric blocks proves all thirty
strict LMIs. This is an exact finite determinant certificate, not
a sample over preparations, times or protocols.

For the lower in (6.1), take input $\Pi_3$, actual wait zero,
a complete read and Stop. Its mode-$3$ survival under $T_{1/2}$ is

$$
\operatorname{tr}(\Pi_3T_{1/2}(\Pi_3))
 =\frac{69}{340}+\frac{27}{260\sqrt{17}}
  +\frac2{17}\left(\frac{53}{130}+4\sqrt{\frac2{65}}\right)
 <\frac{6559}{17680}<\frac25.
\tag{6.5}
$$

The formula follows from (6.2) and
$\|R_+e_3\|^2=(1-3/r)/2$,
$\|R_-e_3\|^2=(1+3/r)/2$, and $R_0e_3=0$.
The strict estimate uses $\sqrt{17}>4$ and
$\sqrt{2/65}<1/5$. Hence this legitimate complete-read experiment
has TV $1-\operatorname{tr}(\Pi_3T_{1/2}(\Pi_3))>3/5$.

Finally the first-read identity explains the full quantifiers in
the upper. Before its first read a deterministic policy either stops
without an input-dependent record or accumulates a nonnegative wait.
After first outcome $s$, the two unnormalized states are
$p_s\Pi_s$ and $p'_s\Pi_s$. Their common finite suffix is a
probability kernel $L_s$ of total mass one, even when one of those
probabilities vanishes. Retaining the first result gives TV
$\frac12\sum_s|p_s-p'_s|$ for the complete histories.
Source-independent random controls preserve the upper under their
common mixing law. Stationarity gives

$$
Q_J(t)-S^\dagger(Q_J(t))=O(t)^TH_JO(t),
\quad Q_J(t)=O(t)^T\Pi_JO(t),
\tag{6.6}
$$

and TP gives opposite residuals for complementary events. Thus the
fifteen-event maximum is the full error, by (1.10), proving the
upper in (6.1). A maximizing residual eigenvector, transported by
$D$, attains that maximum with actual wait zero, a complete read
and Stop. This applies to this CPTP channel independently of its
failure to have a scalar port. $\square$

**Proposition 6.2 (Simultaneous strict event feasibility in the interior).**
Let $T_s$ be the physical channel with Choi matrix (5.1). Then

$$
\frac{31}{50}<e(T_{1/10})<\frac{17}{25}<\frac{49}{50}.
\tag{6.7}
$$

It is a full-rank, PPT, full-TP point satisfying every event
constraint at threshold $17/25$, but has no scalar-port realization.

Proof. The other summand in (5.1) is the depolarizing channel
$\Delta(X)=\operatorname{tr}(X)I_5/5$. Its adjoint residuals
have norm $4/5$ on singletons and $3/5$ on pairs. For each of the
same fifteen events, linearity gives

$$
H_J(T_s)=(1-s)H_J(T_{1/2})
                  +s(\Pi_J-|J|I_5/5).
\tag{6.8}
$$

Proposition 6.1 and norm convexity give, at $s=1/10$, strict
bounds $17/25$ on singletons and $33/50$ on pairs. All are
simultaneous bounds on this one channel. The first-read argument
therefore gives the strict upper in (6.7). The coarser $49/50$
also follows directly from the generic CPTP event bound one and
the depolarizing singleton bound, without the determinant certificate.

For the actual input and read used in (6.5), the mixed channel's
survival is less than $(9/10)(2/5)+(1/10)(1/5)=19/50$.
Its TV is consequently greater than $31/50$. Theorem 5.1 supplies
full rank, PPT, the full marginal and complex nonseparability.
Thus these event LMIs, even with strict positivity and the exact
marginal, do not extract an unperturbed scalar port. $\square$

## 7. The precise obstruction and the unmatched original goal

**Definition 7.1 (Cone separation and optimization thresholds).** Let
$\mathcal P$ consist of tuples $x$ in (1.6) with $Z(x)\succeq0$
and $M^T\tau=\tau$. They are automatically PPT. Let
$\mathcal F=\{x\in\mathcal K:M^T\tau=\tau\}$.
The supplied no-worse reduction gives

$$
\varepsilon_1=\min_{x\in\mathcal F}
\max_{J\in\mathcal J_{15}}\|\mathcal H_J(x)\|_{\rm op},
\qquad \mathcal F\subsetneq\mathcal P.
\tag{7.1}
$$

The strict inclusion follows from Theorems 4.2 and 5.1. It persists
with the same all-event inequalities at threshold $2/3$ for the
singular example and at $17/25$ for the full-rank example. In
contrast, minimizing over $\mathcal P$ gives only a necessary
relaxation value

$$
\min_{x\in\mathcal P}\max_J\|\mathcal H_J(x)\|_{\rm op}
\ \le\ \varepsilon_1.
\tag{7.2}
$$

Strict cone inclusion alone gives no strict inequality in (7.2):
the two minima could occur at a common scalar point. In particular
no example in §§4–6 is a legal scalar upper, an endpoint improvement,
or evidence of a strict optimum gap near the current interval.
The actual losses in (6.5) and (6.7) lie above that interval.

**Definition 7.2 (The missing event–atom–TP normalization).** The
witnesses above are globally complex-product-positive separating
functionals. A necessary minimax lower additionally needs the
normalization and common-marginal relation of
[QJM, Convention 6.3](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_JOINT_MARGINAL_AND_ATTAINING_PORT.md)
and QAP Theorem 5.2: positive event multipliers $A_J^\pm$ with
$\sum_J\operatorname{tr}(A_J^++A_J^-)=1$, all three TP
multipliers, and a globally positive atom form for those same data.
A matching value also needs complementary signed event eigenspaces
and positive-weight atom kernels for one legal feasible port.
No representation of $W'_\xi$ or $W_H$ by such normalized
event/TP data is supplied here. Their negative Choi pairings do
not by themselves give a numerical lower for $\varepsilon_1$.

Necessary kernel contact does not imply that positive primal mass
can be assigned to the contacted atoms. The common weights must
also satisfy all three TP equations and all fifteen event LMIs.
Theorem 3.1 gives one exact additional compatibility check when
its face/rank/pair hypotheses hold; it neither forces those
hypotheses nor classifies unrestricted optimizer support. In
particular QAP's full-sector atom requirement for its separate
boundary-cone example and
[QSD's necessary splitting-event activity](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_SPLITTING_EVENTS_AND_DECODER_DESCENT.md)
are not replaced by this face criterion.

The failure proved here is the specific shortcut from a full-TP
PPT point to an exact scalar realization. It does not invalidate
[QME's conditional marginal-preserving noisy repair](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_MARGINAL_PRESERVING_EXTENSION_REPAIR.md).
No Bose or half-PPT extension level is asserted for the examples.
Nor does it contradict QRC's no-worse real replacement, which may
change the channel. The unchanged real-Choi obstruction and the
other covariance limitations of QPC §9 retain their stated domains.

**Definition 7.3 (Mathematical attribution and remaining values).**
The HSR correspondence, Choi positive-map mechanism, PCP/TCP
factorizations, saturated equality arguments and cyclic PCP
counterexample are literature-attested ingredients, credited at
their point of use. The explicit saturated walk-face lift, cycle
consumer with full marginal and port (3.6), the normalized $5\times5$
PPT channels, and their simultaneous actual-event and interior
separations are repository-derived applications. This description
makes no worldwide novelty claim. Orthogonal or diagonal-orthogonal
covariance results, such as
[Nechita–Park, 2403.03667v2, §2.1](https://arxiv.org/pdf/2403.03667v2),
refer to their specified representations; they do not enlarge the
actual future menu here. Likewise the LOCC/separable/PPT
measurement optimizations in
[Johnston–Russo, 2604.12808v1](https://arxiv.org/pdf/2604.12808v1)
have a different observation contract and do not evaluate (1.3).

The credited original interval remains

$$
\frac{129931}{250000}\le\varepsilon_1\le e_{\rm mix},\qquad
\frac{52417598}{10^8}<e_{\rm mix}<\frac{52417600}{10^8},
\tag{7.3}
$$

with the lower from QJM Theorem 2.3 and the legal twenty-seven-flag
upper from QSD Theorem 5.2. The exact value, a globally matching
event–atom–TP certificate and a legal optimal port remain unresolved.
No new endpoint follows from the present separation. The earlier
QEC and QWS endpoints remain credited historical bounds.

The $q=2,3,4$ optima, native preparation bridge, native all-size
cofinality, memory rates and complete all-view mutual recovery
remain distinct unresolved obligations. Finite flag counts and
exact mathematical coefficients do not bound coefficient synthesis,
finite-precision implementation, acquisition, physical preparation,
clocks, transport or storage duration. The results here are ordinary
mathematical proofs, without a new Lean-verification or physical
realization assertion.

## 追加锚（本行以下为增补区）

## 8. Input-sector filters and the entire cyclic-witness zero face

**Definition 8.1 (The specified filtered family).** Retain exactly
Assumption 1.1, the scalar ports and error (1.2)–(1.3), the passive
frame (1.4), and the complete atom cone (1.8). Let $W$ be the
particular cyclic witness in (4.1). For three strictly positive real
numbers $h_0,h_+,h_-$, set

$$
\begin{gathered}
H=\sum_{i\in I}h_iR_i,\qquad
W_H=(I\otimes H^{-1})W(I\otimes H^{-1}),\\
\Psi_H(a,b)=(a\otimes b)^TW_H(a\otimes b)
                =\Psi(a,H^{-1}b),\qquad a,b\in\mathbb R^5,\\
a_*=(d+u_++u_-)/\sqrt3,\qquad
b_h=\frac{h_0d+h_+u_++h_-u_-}{\sqrt{h_0^2+h_+^2+h_-^2}},\qquad
q_i=\frac{h_i^2}{h_0^2+h_+^2+h_-^2},\\
k_h=k(a_*,b_h),\quad k_{+0}=k(u_+,d),\quad
k_{-+}=k(u_-,u_+),\quad k_{0-}=k(d,u_-),\\
\mathcal E_H=\{x\in\mathcal K:\operatorname{tr}(W_HZ(x))=0\}.
\end{gathered}
\tag{8.1}
$$

Thus $q_i>0$ and $\sum_iq_i=1$. Here $H$ filters only the input
factor of a mathematical witness; it is not an added future action.
Taking $H=I$ gives $W$. Taking $H=C_\xi$ gives precisely $W'_\xi$
of (4.3), and (4.12) is another member of this same family. No
output filter, nonscalar within-sector filter or changed coefficient
in $W$ is included in (8.1).

For an arbitrary original channel, use the output-first unnormalized
Choi matrix of its passive-frame channel,

$$
\begin{gathered}
\widehat T(X)=D^\dagger T(DXD^\dagger)D,\qquad
\Omega=5^{-1/2}\sum_{s\in\mathsf S}e_s\otimes e_s,\\
\chi_T=(\widehat T\otimes\mathrm{id})(\Omega\Omega^\dagger),
\qquad Z_T=5\chi_T.
\end{gathered}
\tag{8.2}
$$

This notation does not assume that $T$ is stationary or real.
For a selected channel $\widehat T=S_x$, it agrees with $Z(x)$.
The original-coordinate witness is transported by
$D\otimes\overline D$ as in (4.9a); all trace pairings are unchanged.
Theorem 4.2 proves global complex-product positivity of $W$.
The real invertible input congruence proves it for every $W_H$.
Consequently its pairing is nonnegative on every original scalar-port
Choi matrix, including mixed complex preparations and effects.

**Theorem 8.2 (Four generators and all three TP equations).** For every
$H$ in (8.1), the entire selected zero face is

$$
\mathcal E_H=
\operatorname{cone}\{k_h,k_{+0},k_{-+},k_{0-}\}.
\tag{8.3}
$$

These four generators are linearly independent. Its full TP slice
consists exactly of

$$
\begin{aligned}
x_H(w)={}&wk_h+(1-wq_0)k_{+0}
                  +(2-wq_+)k_{-+}+(2-wq_-)k_{0-},\\
&w\ge0,\qquad wq_0\le1,\quad wq_+\le2,\quad wq_-\le2.
\end{aligned}
\tag{8.4}
$$

Every point in (8.4) is one legal fixed scalar port, with at most
$100$ flags and whole-block CPTP decoders. This classifies this
specified witness's zero face; it imposes no support restriction
on competitors outside that face.

Proof. First classify real zero products before filtering. By
simultaneous sector rotations and an irrelevant overall sign of
the preparation, a real unit preparation can be put in the canonical
form $a(p)=\sqrt{p_0}d+\sqrt{p_+}u_++\sqrt{p_-}u_-$.
These operations leave its atom coefficients unchanged when applied
to both factors, as in QAP Theorem 2.2. For this preparation, the
actual measurement quadratic form (4.7), in the ordered radial
and tangent coordinates, has the exact block decomposition

$$
\Psi(a(p),b)=b_r^T\mathcal C(p)b_r
             +(p_0+p_+)b_{t+}^2+(p_++p_-)b_{t-}^2.
\tag{8.5}
$$

Here $b_r=(d^Tb,u_+^Tb,u_-^Tb)^T$,
$b_{t\pm}=v_\pm^Tb$, and $\mathcal C(p)$ is exactly (4.8).
Thus this calculation retains every tangent direction, as well
as the full interior radial determinant.

If all $p_i$ are positive, (4.9) and equality in AM–GM give

$$
\det\mathcal C(p)=0
\quad\Longleftrightarrow\quad
p_0^2p_+=p_+^2p_-=p_-^2p_0
\quad\Longleftrightarrow\quad
p_0=p_+=p_-=1/3.
\tag{8.6}
$$

For the last equivalence, division is only by strictly positive
populations; the three monomial equalities force their ratios to
be one. Otherwise $\mathcal C(p)$ is positive definite: its
diagonal and its three two-by-two principal minors listed after
(4.8) are positive, and its determinant is positive. Both tangent
coefficients in (8.5) are also positive. At the equal population,

$$
\mathcal C(p)=\tfrac13(3I_3-\mathbf1\mathbf1^T),\qquad
\ker\mathcal C(p)=\mathbb R(1,1,1),
\tag{8.7}
$$

while both tangent coefficients are $2/3$. Thus the only unit
measurement projectors giving zero there are $bb^T=a(p)a(p)^T$.
Undoing the simultaneous rotations gives $b=\pm a$, with each
preparation population equal to $1/3$. Equivalently, in the
Cauchy–Schwarz bounds preceding (4.8), equality forces all three
sector inner products to saturate with one common sign. There is
no independent relative-sign zero or omitted tangent zero.

If exactly two populations are positive, the determinant in (4.9)
is respectively $p_0^2p_+$, $p_+^2p_-$ or $p_-^2p_0$.
It is strictly positive in each case, all diagonal entries and
two-by-two minors of $\mathcal C(p)$ are positive, and the two
tangent coefficients in (8.5) are positive. Thus there are no edge
zero products. At a vertex, (8.5) gives exactly the following
measurement kernels in the original five-dimensional space:

$$
\begin{array}{c|c}
\text{preparation sector}&\text{whole measurement kernel}\\\hline
V_0&V_-\\
V_+&V_0\\
V_-&V_+
\end{array}.
\tag{8.8}
$$

Directions within a displayed two-plane contribute the same disjoint
sector atom: all six plane coefficients vanish and only its one
population entry remains. These are $k_{0-},k_{+0},k_{-+}$.
The interior zero products all give $k(a_*,a_*)$. This exhausts
every nonzero real product; no boundary case uses division by a
zero population.

Filtering replaces the measurement vector by $H^{-1}b$. Since
$H$ is invertible and scalar on each sector, (8.8) is unchanged.
At an interior zero, $H^{-1}b$ is proportional to $a$; normalizing
$b$ gives precisely $b_h$ after the same canonical rotations.
Thus the four zero-atom coefficients are exactly those in (8.3).
The witness is invariant under simultaneous orthogonal changes
within each sector, and hence under the torus and reflection used
in (1.8). Therefore

$$
\operatorname{tr}(W_HZ(k(a,b)))=\Psi_H(a,b).
\tag{8.9}
$$

Every point of $\mathcal K$ is a finite nonnegative sum of unit
atoms. Each summand in its witness pairing is nonnegative, so a
zero sum uses only zero atoms. The preceding exhaustive analysis
proves (8.3). The full-support generator has positive diagonal
population entries; the other three have distinct disjoint sector
entries and zero diagonal. This proves their linear independence.

The full input marginal of a unit atom, with measurement population
$q(b)$, is the supplied identity

$$
\operatorname{Tr}_{\rm out}Z(k(a,b))
                  =\sum_i\frac{q_i(b)}{n_i}R_i.
\tag{8.10}
$$

It is also immediate from (1.6), since each $F_{\nu a}$ is
traceless. Write the four coefficients in (8.3) as
$w,c_{+0},c_{-+},c_{0-}$. All three TP equations are exactly

$$
wq_0+c_{+0}=1,\qquad
wq_++c_{-+}=2,\qquad
wq_-+c_{0-}=2.
\tag{8.11}
$$

Solving them, and imposing nonnegativity of every coefficient,
gives (8.4) in both directions. Their total coefficient weight is
$5$. Equation (8.10) proves the whole matrix marginal $I_5$
before division by five, rather than just its trace.

For explicit legality, label the four unit seed pairs in (8.1)
by $r$ and their nonnegative coefficients in (8.4) by $c_r$;
omit a seed with zero coefficient. All are radial. For
$0\le k,l<5$ put $g_{kl}=G(2\pi k/5,2\pi l/5)$ and use

$$
\begin{gathered}
B_{rkl}=\sqrt{c_r/25}\,(g_{kl}b_r)^TD^\dagger,
\qquad R_{rkl}=Dg_{kl}a_r,\\
\operatorname{Enc}(X)=(B_{rkl}XB_{rkl}^\dagger)_{rkl},\qquad
\operatorname{Dec}_{rkl}(y)=R_{rkl}yR_{rkl}^\dagger.
\end{gathered}
\tag{8.12}
$$

The exact $25$-point radial quadrature of QAP Theorem 2.3,
also used in (3.6), preserves the complete Choi matrix of each
seed. Its elementary reason is Fourier support $|m|+|n|\le4$;
the two five-point sums keep only $(m,n)=(0,0)$. Reflection is
redundant for radial seeds. Thus (8.12) gives this same $S_{x_H(w)}$
on every complex matrix. Equations (8.10)–(8.11) give
$\sum_{rkl}B_{rkl}^\dagger B_{rkl}=I_5$; unit preparations give
$R_{rkl}^\dagger R_{rkl}=1$. Rectangular sandwiches prove CP at
every reference dimension. These identities prove encoder TP and
each decoder's TP on its whole scalar block. Every nonzero composite
Kraus matrix has rank one. The at-most-$100$ flags are fixed and
consumed before the future protocol. $\square$

## 9. A full-marginal event obstruction and a nonempty face

**Theorem 9.1 (Survival on the selected filtered zero face).** Let
$x=x_H(w)$ satisfy (8.4), and put

$$
n=\frac{1+1/\sqrt{17}}2,\qquad m=1-n,\qquad
t_+=wq_+,\quad t_-=wq_-.
\tag{9.1}
$$

Then $nm=4/17$, $0\le t_+,t_-\le2$, and its mode-$N$ survival
for input $\Pi_N$ at actual wait zero is

$$
\begin{aligned}
s_N(x)&:=\operatorname{tr}(\Pi_NS_x(\Pi_N))\\
&=\frac{nm}{2}
 +\left(\frac{n^2}{8}-\frac{nm}{6}\right)t_+
 +\left(\frac{m^2}{8}+\frac{nm}{12}\right)t_-
 +\frac{nm}{3}\sqrt{t_+t_-}
\ \le\ \frac{25}{68}.
\end{aligned}
\tag{9.2}
$$

Consequently the physical port in (8.12) has $e(T_x)\ge43/68$.
For $H=I$ the stronger statements are

$$
0\le w\le3,\qquad
s_N(x_I(w))=\frac2{17}+\frac w{24}\le\frac{33}{136},\qquad
e(T_x)\ge\frac{103}{136}.
\tag{9.3}
$$

Proof. By (1.4),
$e_N=\sqrt n\,u_++\sqrt m\,u_-$ and $R_0e_N=0$.
For the full-support seed in (8.1), expand its joint-rotation
survival integrand as

$$
\frac13(\sqrt n\cos\theta+\sqrt m\cos\phi)^2
       (\sqrt{nq_+}\cos\theta+\sqrt{mq_-}\cos\phi)^2.
\tag{9.4}
$$

The independent circle moments are
$\langle\cos^2\theta\rangle=1/2$,
$\langle\cos^4\theta\rangle=3/8$, and zero for the odd
powers that occur. Both the integral and the exact finite quadrature
therefore give the full-support seed survival

$$
D(q)=\frac{n^2q_+}{8}+\frac{m^2q_-}{8}
 +\frac{nm(q_++q_-)}{12}
 +\frac{nm}{3}\sqrt{q_+q_-}.
\tag{9.5}
$$

Of the other three seeds, only $k_{-+}$ survives this test.
Its value is $nm/4$, from two independent second moments.
The seed $k_{+0}$ has zero measurement overlap with $e_N$;
$k_{0-}$ has zero preparation overlap. The forced TP weights in
(8.4) give $s_N=wD(q)+(2-wq_+)nm/4$, which is exactly (9.2).
This uses common weights fixed by the whole marginal, not separate
eventwise optima.

All three variable terms in (9.2) are nondecreasing in
$(t_+,t_-)\in[0,2]^2$. The only coefficient requiring a sign
check is

$$
\frac{n^2}{8}-\frac{nm}{6}
 =\frac{n(3n-4m)}{24}>0:
\qquad n>4/7\quad\text{since }\sqrt{17}<7.
\tag{9.6}
$$

The remaining coefficients are positive. Substituting the upper
corner $(2,2)$ therefore gives

$$
s_N\le\frac{n^2+m^2}{4}+nm
      =\frac14+\frac{nm}{2}=\frac{25}{68}.
\tag{9.7}
$$

For the allowed physical input $\rho=\Pi_N$, actual wait $0$,
the complete five-outcome rank-one read and Stop, the unreplaced
law is concentrated at $N$. The replaced mode-$N$ probability is
$s_N$, since $De_N=e_N$. The TV of these full histories is
exactly $1-s_N\ge43/68$. In adjoint notation the same event
difference is

$$
\operatorname{tr}\bigl(\Pi_N[\Pi_N-S_x^\dagger(\Pi_N)]\bigr)
                       =1-s_N.
\tag{9.8}
$$

Thus no state-map substitution for a non-self-adjoint channel's
adjoint is used. This single legitimate protocol lower-bounds the
original supremum over all complex inputs and all actual finite
histories. It introduces no new instrument or reference measurement.

For $H=I$, $q_i=1/3$ and (8.4) requires $w\le3$.
Substitution in (9.2), using $n+m=1$, gives
$s_N=nm/2+w/24=2/17+w/24$. Its maximum is $33/136$,
whose complement proves (9.3). $\square$

**Theorem 9.2 (Every complex scalar port annihilating this family).**
Let $T$ be any original legal complex scalar port, with any finite
flag presentation, and suppose that for one $H$ in (8.1),

$$
\operatorname{tr}(W_HZ_T)=0.
\tag{9.9}
$$

Then $e(T)\ge43/68$. If $H=I$, then $e(T)\ge103/136$.
No reality, stationarity, reflection, unitality, self-adjointness
or pure decoding is required of the given presentation of $T$.

Proof. The credited QRC replacement can be chosen to preserve this
particular witness pairing. To see the needed additional property,
let $\mathcal R(Y)=(Y+Y^T)/2$ in the passive frame. At the Choi
level, separate realification of a scalar port applies
$\mathcal R\otimes\mathcal R$. The matrix $W_H$ is invariant
under transposition of either factor, because it lies in
$\operatorname{Sym}_5(\mathbb R)\otimes
\operatorname{Sym}_5(\mathbb R)$. Trace self-adjointness of those
transposes therefore gives

$$
\operatorname{tr}\bigl(W_H(\mathcal R\otimes\mathcal R)(Z_T)\bigr)
                    =\operatorname{tr}(W_HZ_T).
\tag{9.10}
$$

QRC Theorem 2.2 proves CP and TP of this particular replacement
by splitting actual complex rank-one factors into their real and
imaginary parts. It contracts every original real-effect residual.
It does not assert that $\mathcal R$ itself is CP. Arbitrary mixed
decoder states and POVM effects admit the finite spectral refinement
needed for those factors by the scalar-port correspondence in §1.

Furthermore $W$ is invariant under simultaneous sector orthogonal
transformations: each cross-sector sum $\mathcal Q_{ij}$ in (4.1)
is independent of its orthonormal sector bases. Since $H$ commutes
with those transformations, so is $W_H$. In particular for every
walk-torus or specified reflection matrix $g$,

$$
(g\otimes g)^TW_H(g\otimes g)=W_H.
\tag{9.11}
$$

Conjugating a channel's design by this real $g$ conjugates its
output-first Choi matrix by $g\otimes g$. Thus the stationary
average of QPC Theorem 3.3 and the reflection average of QRC
Theorem 3.2 both preserve (9.9). Continuity preserves the pairing
under their compact averages. QPC's recurrence argument proves
exact invariance of the original error under each walk-design
conjugation for nonnegative waits; convexity makes its average
no worse. QRC proves the same no-worse assertion for the reflection
of the stationary channel. These are transformations of port data,
not additional future controls or readable random flags.

Applying these operations gives one selected channel $S_x$ with
$e(T_x)\le e(T)$ and $\operatorname{tr}(W_HZ(x))=0$.
QRC's finite-product representation keeps this entire channel and
its full TP marginal. Theorem 8.2 puts $x$ in (8.4), and
Theorem 9.1 gives

$$
e(T)\ge e(T_x)\ge43/68,
\tag{9.12}
$$

with $103/136$ in the identity-filter case. The explicit wait-zero
test in Theorem 9.1 is a test of this legal no-worse representative;
the argument does not assert that the given nonstationary channel
has the same wait-zero survival. It suffices for its original error
bound. The replacement may change the channel, consistently with
the unchanged-channel obstructions in QPC §9. $\square$

**Proposition 9.3 (A full-TP face example with positive weights).** Take

$$
\begin{gathered}
H=\tfrac12R_0+R_++R_-,\qquad q=(1,4,4)/9,\qquad
w=9/2,\qquad b_h=(d+2u_++2u_-)/3,\\
x_0=\tfrac92k(a_*,b_h)+\tfrac12k(u_+,d).
\end{gathered}
\tag{9.13}
$$

Then $x_0\in\mathcal E_H$ has the full TP marginal and a fixed
legal $50$-flag scalar realization. Its actual wait-zero full-read
test on $\Pi_N$ has TV exactly $43/68$.

Proof. The two positive seed weights in (9.13) contribute input
population vectors $(1/2,2,2)$ and $(1/2,0,0)$. Their sum is
$(1,2,2)$, proving every equation in (8.11) and hence the whole
matrix marginal. Both seeds are zero atoms by Theorem 8.2, so
$\operatorname{tr}(W_HZ(x_0))=0$. Formula (8.12) with these two
seeds gives $25$ fixed flags per seed, with per-flag coefficients
$9/50$ and $1/50$, respectively. It proves CP at every reference
dimension, encoder TP, whole-scalar-block decoder TP and rank-one
nonzero composite Kraus matrices. It is a finite port for the
original source and consumes all flags before the actual protocol.

Here $t_+=t_-=2$. Equations (9.2) and (9.7) give exactly
$s_N(x_0)=25/68$, so the test in (9.8) has TV $43/68$.
This demonstrates both a nonempty full-TP zero face and sharpness
of this particular survival bound across the filter family.
It does not evaluate $e(T_{x_0})$ or supply a competitive upper
bound for $\varepsilon_1$. $\square$

## 10. Exclusion of positive augmentations from a matching certificate

**Theorem 10.1 (The defined filtered-witness route cannot match).**
Take one normalized all-fifteen-event/three-TP tuple of QJM
Convention 6.3, with real PSD $A_J^\pm$ satisfying
$\sum_J\operatorname{tr}(A_J^++A_J^-)=1$, all three
$y\in\mathbb R^3$, and its actual atom form $b^TB_y(a)b$.
Suppose that for all real $a,b$ it has the form

$$
b^TB_y(a)b=\kappa\Psi_H(a,b)+Q(a,b),\qquad
\kappa>0,\quad Q(a,b)\ge0\quad\text{for all }a,b,
\tag{10.1}
$$

where $H$ is as in (8.1) and $Q$ is a real biquadratic product
form. Then this tuple has no complementary legal port of error
less than $43/68$. In particular it cannot match the original
$\varepsilon_1$. For $H=I$, replace $43/68$ by $103/136$ in
the complementary-port assertion. The conclusion allows arbitrary
globally product-nonnegative augmentations, not only PSD matrix
augmentations.

Proof. Equation (10.1) is globally nonnegative. QJM's exact slack
identity (6.5), with the same full TP marginal and signed event
constraints, makes $c=\beta-\tau^Ty$ a lower bound on every
selected feasible channel and, by the no-worse QRC replacement,
on every original complex scalar port.

Suppose an original legal $T$ matched it with $e(T)=c$.
Its no-worse selected representative has error at most $c$ and
the same universal lower forces equality. Decompose that selected
channel into positive-weight unit atoms
$x=\sum_fw_fk(a_f,b_f)$, with $M^T\tau=\tau$.
Apply the supplied slack identity at $z=e(T_x)=c$. Each of the
thirty signed event pairings is nonnegative, and so is each
positive-weight atom slack. Their sum is zero. In particular,

$$
0=b_f^TB_y(a_f)b_f
 =\kappa\Psi_H(a_f,b_f)+Q(a_f,b_f)
\quad\Longrightarrow\quad\Psi_H(a_f,b_f)=0
\qquad(w_f>0).
\tag{10.2}
$$

Thus the same selected channel belongs to $\mathcal E_H$ and
has the full TP weights (8.4). Theorem 9.1 implies
$c=e(T_x)\ge43/68$, or $c\ge103/136$ for $H=I$.
This proves the complementary-port assertion. Equivalently,
nonnegative augmentation can only shrink the witness zero face;
it cannot supply a missing competitive TP/event solution on it.

The legal QSD Theorem 5.2 port already gives

$$
\varepsilon_1\le e_{\rm mix}
 <\frac{52417600}{10^8}<\frac{43}{68}.
\tag{10.3}
$$

Consequently no tuple satisfying (10.1) can be tight at the
original value. This does not say such a normalized tuple is
infeasible or cannot give a weaker necessary bound. All fifteen
event constraints and all three marginal multipliers remain in
the slack identity. One actual event suffices to obstruct their
joint competitive attainment; adding the other fourteen cannot
repair that obstruction. $\square$

**Definition 10.2 (Attribution, scope and the remaining joint relation).**
The positive map underlying (4.8) is the classical Choi map displayed
in [Singh–Nechita, Example 7.5, equation (43), version 2](https://arxiv.org/html/2010.07898v2).
Product zeros and their dual separable faces are mature ingredients;
see [Ha–Kye, §2, version 1](https://arxiv.org/html/1108.0130v1).
Their exposed-map results do not imply a normalized actual-event
certificate here. The scalar-port correspondence is the credited
[Horodecki–Shor–Ruskai, Theorem 4(A–D), version 2](https://arxiv.org/html/quant-ph/0302031v2),
with its separate POVM/TP condition. The zero analysis, its forced
common TP weights and the mode-$N$ test above are applications to
this exact walk-sector representation, without a novelty claim.
The QRC no-worse replacements, QAP finite quadrature and QJM slack
identity retain their supplier status.

The conditional inequality in Theorem 9.2 concerns only scalar
ports satisfying (9.9) for the precisely specified positive
input-sector-filter family. It is not a lower $43/68$ on all
scalar ports or on $\varepsilon_1$. Theorem 10.1 excludes only
the slack mechanism (10.1). Changes to the coefficients of the
cyclic witness, general output filters, nonscalar within-sector
filters, different positive forms, and corrections of indefinite
sign remain outside that exclusion. No assertion that all globally
positive witnesses or all normalized event tuples have this form
is made. The nonempty TP face in Proposition 9.3 is not an
event-preserving reduction of an optimizer, and its exact full
worst-case error is not evaluated.

The credited numerical frontier (7.3) is unchanged:
$129931/250000\le\varepsilon_1\le e_{\rm mix}$, with the
same strict QSD upper enclosure. A matching solution still requires
one normalized tuple of all fifteen signed event multipliers and
all three TP multipliers, global product-atom positivity including
the interior cubic, and one legal common-positive-weight port on
its kernel face satisfying those same TP and complementary event
equations. Theorems 8.2–10.1 rule out one defined route to that
joint solution; they do not provide the missing tuple or a new
unrestricted endpoint.

All claims use the independent $\mathbb C^5/K$ preparation of
Assumption 1.1. The event uses input $\Pi_N$, actual nonnegative
wait zero, a complete five-outcome rank-one read and Stop, with
the full history retained. Design rotations and witness congruences
add no future control, coarse-block instrument, source copy, side
information or exposed flag. The fixed scalar encoders and whole-block
CPTP decoders in (8.12) bound quantum dimension and finite flags;
they do not bound coefficient synthesis, finite-precision robustness,
acquisition, physical preparation, clock precision, transport or
storage duration. The exact original optimum and optimal port,
the $q=2,3,4$ values, native preparation and all-size cofinality,
memory rates and complete all-view mutual recovery remain unresolved.
These are ordinary mathematical proofs, without new Lean certification
or a physical implementation claim.

## 追加锚（本行以下为增补区）

## 11. Local frontier qualification

**Remark 11.1 (Scope of the unchanged frontier).** Definition 10.2's
unchanged-frontier statement concerns only the local structural results
of this volume and the supplier endpoints quoted there. The sharper
current common bracket is supplied by [Joint Event Error Bounds, Theorem 6.1](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_JOINT_EVENT_ERROR_BOUNDS.md#6-the-common-bracket-and-the-nonmatching-boundary).
The exact original optimum and a common complementary event-atom-TP
tuple matching a legal attaining port remain open.

## 追加锚（本行以下为增补区）
