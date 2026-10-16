# Recursive relational observation: witness slack and independent decoding

This volume gives two bounds for the original measurement-relative scalar
quantum port:

$$
\boxed{\frac{12993}{25000}\le\varepsilon_1\le\theta},\qquad
\frac{52427}{100000}<\theta<\frac{13107}{25000}.
\tag{0.1}
$$

The lower bound applies to every original complex competitor. The upper
bound is the exact error of one fixed fourteen-flag port with independent
measurement and preparation factors. The bounds do not match. The
derivations are ordinary mathematics, not Lean certification or a physical
realization theorem.

## 1. The original contract and the supplied reductions

**Assumption 1.1 (Five-mode preparation and actual future histories).**
Let $\mathcal H=\mathbb C^5$ with ordered orthonormal basis
$\mathsf S=(N,2,3,5,25)$, and put $\Pi_s=e_se_s^\dagger$. Every
complex density matrix on $\mathcal H$ is an allowed input. Fix

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

This is exactly QMB Assumption 1.1. It is an independent quantum
preparation hypothesis. In particular, $N$ labels a unit vector, and
preparation from the native $\alpha/\beta$ trees is not supplied.

The future menu consists of nonnegative waits $U(t)$, the complete
five-outcome rank-one Lüders read $X\mapsto(\Pi_sX\Pi_s)_s$, and Stop.
Every finite adaptive depth is included. Histories retain outcomes,
controls and stops. Initial control information and permitted random
controls are source-independent, and the two compared systems use the
same policy. Grouping the recorded outcomes of a full read is classical
postprocessing. It does not introduce a coarse-block Lüders instrument.
There are no independent mode phases, arbitrary future unitaries, source
copies, resets, probability oracles, readable hidden Kraus records or
external quantum side information.

**Definition 1.2 (Fixed ports and the unchanged objective).** For
$q\in\{1,2,3,4,5\}$, a legal port is a composite $T=\operatorname{Dec}
\circ\operatorname{Enc}$ of fixed CPTP maps

$$
\operatorname{Enc}:M_5\longrightarrow\bigoplus_{f\in F}M_q,
\qquad
\operatorname{Dec}((Y_f)_f)=\sum_f\operatorname{Dec}_f(Y_f),
\qquad \operatorname{Dec}_f:M_q\longrightarrow M_5,
\tag{1.2}
$$

with finite fixed $F$ and every decoder CPTP on its whole block.
The design precedes the unknown input and the choice of future protocol.
There is no retained original input, entangled assistance or bypass.
Flags are free for this quantum dimension criterion, are consumed in
decoding, and are not additionally exposed to the future policy. Write
$\mathfrak C_q$ for the entire complex class and set

$$
e(T)=\sup_{\rho\in\mathcal D(\mathcal H)}
\sup_{\pi\ {\rm actual,finite}}
\operatorname{TV}(P_\rho^\pi,P_{T(\rho)}^\pi),
\qquad \varepsilon_q=\inf_{T\in\mathfrak C_q}e(T).
\tag{1.3}
$$

The replacement happens once before the common future protocol. TV is
half the $\ell^1$ difference, with its measure version for random
controls. CPTP legality includes arbitrary reference extensions; this
performance criterion measures only the system histories. No trace-distance
or diamond-norm objective is substituted.

The supplier names in this volume refer to these exact sources at
repository revision `3b275991a1a78fa1468e590c3fea27abb9b4622b`:

| Name | Source and reused content |
| --- | --- |
| QMB | [Measurement-relative quantum boundary](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md), Assumption 1.1, Definitions 1.2–1.3, Theorem 2.1: the contract and first-read identity. |
| QPC | [Port covariance and certified frontier](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_PORT_COVARIANCE_AND_CERTIFIED_FRONTIER.md), Theorem 3.3 and §9: stationary reduction and its shortcut boundaries. |
| QFA | [Finite port attainment](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_FINITE_PORT_ATTAINMENT.md), Definition 2.1 and Lemma 2.2: the encoder and finite circle quadrature. |
| QEC | [Classical-port exact certificates](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_CLASSICAL_PORT_EXACT_CERTIFICATES.md), §§1–2: spectral coordinates, weighted moment and decomposable witness; Theorem 2.6: finite-wait estimates. |
| QRC | [Real-port boundary coordinates](RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_REAL_PORT_BOUNDARY_COORDINATES.md), §§4–6: independent-product cone, full TP marginal and fifteen event residuals. |

The first-read, stationarity and coordinate reductions are credited
suppliers, rather than additional results of this volume.

**Convention 1.3 (Passive frame and spectral data).** Set

$$
\begin{gathered}
r=\sqrt{17},\quad D=\operatorname{diag}(1,i,i,i,1),\quad
A=-iD^\dagger KD,\quad O(t)=e^{tA}=D^\dagger U(t)D,\\
\widehat T(X)=D^\dagger T(DXD^\dagger)D,\quad
\Pi_J=\sum_{s\in J}\Pi_s,\quad Q_J(t)=O(t)^T\Pi_JO(t),\\
B=-A^2,\quad \mu_\pm=(5\pm r)/2,\quad \omega_\pm=\sqrt{\mu_\pm},\\
R_\pm=\frac{B(B-\mu_\mp I)}{\mu_\pm(\mu_\pm-\mu_\mp)},\quad
R_0=I-R_+-R_-=dd^T,\quad d=(e_2-e_5)/\sqrt2,\\
W_\pm=AR_\pm/\omega_\pm,\quad
u_\pm=\frac{R_\pm e_N}{\sqrt{(1\pm1/r)/2}},\quad
w_\pm(\alpha)=\cos\alpha\,u_\pm+\sin\alpha\,W_\pm u_\pm.
\end{gathered}
\tag{1.4}
$$

The $R_j$ are orthogonal projections of ranks $(d_0,d_+,d_-)=(1,2,2)$;
each $u_\pm,W_\pm u_\pm$ is an orthonormal plane basis. These identities
can be checked without a spectral convention ambiguity: in the reordered
coordinates $L=(N,25)$, $V=(2,3,5)$,

$$
A=\begin{pmatrix}0&C\\-C^T&0\end{pmatrix},\quad
C=\begin{pmatrix}1&1&1\\1&0&1\end{pmatrix},\quad
CC^T=\begin{pmatrix}3&2\\2&2\end{pmatrix}.
\tag{1.5}
$$

The nonzero squared frequencies solve $x^2-5x+2=0$. Explicitly,

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

All these projections are block diagonal in $L\oplus V$.
Put

$$
G(\alpha,\beta)=R_0+\cos\alpha R_++\sin\alpha W_+
+\cos\beta R_-+\sin\beta W_-,\qquad
\mathsf J=\operatorname{diag}(1,-1,-1,-1,1).
\tag{1.7}
$$

Then $O(t)=G(\omega_+t,\omega_-t)$ and $\mathsf J A\mathsf J=-A$.
The frame and the two independent mathematical angles are not extra
physical controls. Transposes refer to this frame. A dagger on a map
denotes its trace-pairing adjoint.

**Convention 1.4 (First-read and stationary event identities).** QMB
Theorem 2.1 gives, for every original CPTP channel,

$$
e(T)=\sup_{t\ge0}\max_{J\subseteq\mathsf S}
\|Q_J(t)-\widehat T^\dagger(Q_J(t))\|_{\rm op}.
\tag{1.8}
$$

If a frame channel $S$ commutes with every $\operatorname{Ad}_{O(t)}$,
its adjoint does too, and

$$
Q_J(t)-S^\dagger(Q_J(t))
=O(t)^T[\Pi_J-S^\dagger(\Pi_J)]O(t).
\tag{1.9}
$$

TP gives $S^\dagger(I)=I$, so complementary residuals are negatives.
Thus the stationary error is exactly the maximum of the five singleton
and ten pair norms. This consequence does not assume $S(I)=I$ or
$S=S^\dagger$.

## 2. Strict slack in the full complex PPT witness

**Definition 2.1 (The retained weighted moment and witness).** Use
$a=(9/4,3/4,5/4,3/4,0)$ and $w=a/5$. For any competitor set

$$
f_s(t)=\operatorname{tr}(Q_s(t)\widehat T(Q_s(t))),\quad
g(t)=\sum_s w_s f_s(t),\quad
\chi_T=(\widehat T\otimes\mathrm{id})(\Omega\Omega^\dagger),\quad
\Omega=\frac1{\sqrt5}\sum_s e_s\otimes e_s.
\tag{2.1}
$$

The normalized Choi order is output first, input second; $\Gamma$
transposes the input factor. Write $\mathsf F$ for swap and set

$$
\begin{gathered}
\eta_j=\operatorname{vec}(R_j),\quad
I_j=R_j\otimes R_j,\quad F_j=I_j\mathsf F,\quad
E_j=\eta_j\eta_j^\dagger,\\
I_{jk}=R_j\otimes R_k+R_k\otimes R_j,\quad
F_{jk}=I_{jk}\mathsf F,\quad
E_{jk}=\eta_j\eta_k^\dagger+\eta_k\eta_j^\dagger\quad(j<k).
\end{gathered}
\tag{2.2}
$$

The exact QEC Proposition 2.2 moment, with sector order $(0,+,-)$, is

$$
\begin{gathered}
\mathcal W=\sum_j\kappa_j(I_j+F_j+E_j)
+\sum_{j<k}b_{jk}(I_{jk}+F_{jk}+E_{jk}),\\
\kappa_0=\frac18,\quad
\kappa_+=\frac{331-3r}{2176},\quad
\kappa_-=\frac{331+3r}{2176},\\
b_{0+}=\frac3{32}+\frac{9r}{544},\quad
b_{0-}=\frac3{32}-\frac{9r}{544},\quad
b_{+-}=\frac{49}{272}.
\end{gathered}
\tag{2.3}
$$

In particular $\mathcal W^\Gamma=\mathcal W$. Retain the same marginal
multiplier and the same witness coefficients:

$$
\begin{gathered}
(\ell_0,\ell_+,\ell_-)=\frac1{10000}(4025,4974,5021),\qquad
Y=\sum_j\ell_jR_j,\\
u_{0+}=-\frac{12204}{100000},\quad
u_{0-}=-\frac{5359}{100000},\quad
u_{+-}=-\frac{13938}{100000},\\
t_0=0,\qquad t_+=2\kappa_+-\ell_+,\qquad
t_-=2\kappa_--\ell_-,\\
P=I_5\otimes Y-\mathcal W
+\sum_jt_j(F_j-E_j)+\sum_{j<k}u_{jk}(F_{jk}-E_{jk}).
\end{gathered}
\tag{2.4}
$$

Every matrix in (2.2) is real. Partial transpose fixes $I_j,I_{jk}$,
interchanges $F_j,E_j$ and interchanges $F_{jk},E_{jk}$. Therefore

$$
I_5\otimes Y-\mathcal W=\frac{P+P^\Gamma}{2}.
\tag{2.5}
$$

The new lower bound uses strict slack away from the known kernel of $P$;
it does not change the weighted tests or the marginal multiplier.

**Lemma 2.2 (Kernel projections and their partial transposes).** For
$j=+,-$, define

$$
K_j=\frac{I_j+F_j-E_j}{2},\qquad
K_{\rm ker}=K_++K_-,\qquad Q=I_++I_-.
\tag{2.6}
$$

Then $K_{\rm ker}$ is the orthogonal projection onto the direct sum of
the two same-plane symmetric traceless tensor subspaces, complexified,
and

$$
K_{\rm ker}+K_{\rm ker}^\Gamma=Q,\qquad 0\preceq Q\preceq I_{25}.
\tag{2.7}
$$

Proof. In a real orthonormal basis of the two-dimensional sector,
$(I_j+F_j)/2$ projects onto symmetric tensors.
$\|\eta_j\|^2=2$, so $E_j/2$ projects onto its trace direction.
Their difference is the symmetric traceless projection, of dimension
two. The sectors are orthogonal. Partial transpose gives
$K_j^\Gamma=(I_j+E_j-F_j)/2$, proving (2.7). Finally $I_+,I_-$ are
orthogonal sector projections, so their sum is itself a projection.
This proof is on the whole complexified tensor space. $\square$

**Lemma 2.3 (An exact complementary spectral gap).** With
$\gamma=1/25000$,

$$
P\succeq\gamma(I_{25}-K_{\rm ker}).
\tag{2.8}
$$

Proof. The QEC block decomposition can be read directly from (2.2)–(2.4).
On a plane's symmetric traceless tensors, $F_j$ is the identity and
$E_j$ vanishes, giving eigenvalue $\ell_j-2\kappa_j+t_j=0$.
On its antisymmetric line, $F_j=-I$ and $E_j=0$, giving eigenvalue
$2(\ell_j-\kappa_j)$. On the trace directions
$\eta_j/\sqrt{d_j}$, the matrix is $D_dND_d$, where
$D_d=\operatorname{diag}(1,\sqrt2,\sqrt2)$ and

$$
N=\begin{pmatrix}
11/400&2829/100000-9r/544&-251/6250+9r/544\\
2829/100000-9r/544&55839/1360000+9r/2176&-8663/212500\\
-251/6250+9r/544&-8663/212500&62231/1360000-9r/2176
\end{pmatrix}.
\tag{2.9}
$$

For each $j<k$, the two ordered cross-sector tensors give $d_jd_k$
copies of

$$
D_{jk}=\begin{pmatrix}
\ell_k-b_{jk}&u_{jk}-b_{jk}\\
u_{jk}-b_{jk}&\ell_j-b_{jk}
\end{pmatrix}.
\tag{2.10}
$$

Thus the dimensions of the trace, kernel, antisymmetric and cross blocks
are $3,4,2,16$, totaling $25$. This is a decomposition of the witness,
with no restriction on a competitor's Kraus family.

Subtracting the right side of (2.8) leaves zero on the kernel. On the
trace block it leaves a matrix congruent to

$$
N_\gamma=N-\gamma\operatorname{diag}(1,1/2,1/2),
\qquad
D_dN_\gamma D_d=D_dND_d-\gamma I_3.
\tag{2.11}
$$

The next table supplies every required shifted determinant. The first
three are leading principal minors of $N_\gamma$, not of its congruent
trace block. Every displayed expression is exact in $\mathbb Q(r)$.

| Determinant | Exact value | Lower bound, denominator $10^{15}$ |
| --- | --- | --- |
| $\det(N_\gamma)_1$ | $1373/50000$ | $27460000000000/10^{15}$ |
| $\det(N_\gamma)_2$ | $-1470993437/340000000000+(114201/108800000)r$ | $>1331670138/10^{15}$ |
| $\det N_\gamma$ | $-2084432137027/231200000000000000+(161776143/73984000000000)r$ | $>24889/10^{15}$ |
| $\det(D_{0+}-\gamma I_2)$ | $78033119/1000000000-(102951/5440000)r$ | $>4102959007/10^{15}$ |
| $\det(D_{0-}-\gamma I_2)$ | $208680609/2000000000+(91053/5440000)r$ | $>173351542832592/10^{15}$ |
| $\det(D_{+-}-\gamma I_2)$ | $369953/21250000000$ | $>17409552941/10^{15}$ |

For a fully rational sign certificate, integer squaring gives

$$
\left(\frac{4123105625617}{10^{12}}\right)^2<17
<\left(\frac{4123105625618}{10^{12}}\right)^2.
\tag{2.12}
$$

Reduce each determinant using $r^2=17$. For $v\ge0$, bound $u+vr$
below by inserting the left endpoint of (2.12); for $v<0$, insert the
right endpoint. These substitutions give the last column. The identities
in the middle column follow by the two-dimensional determinant formula
and

$$
\det\begin{pmatrix}x&u&v\\u&y&w\\v&w&z\end{pmatrix}
=xyz+2uvw-xw^2-yv^2-zu^2.
\tag{2.13}
$$

Hence Sylvester's criterion gives $N_\gamma\succ0$.
Every $\ell_j>2/5$ and $0<b_{jk}<1/5$, so the leading diagonals of
$D_{jk}-\gamma I_2$ exceed $1/5-\gamma>0$. Together with their
positive determinants this proves positive definiteness. Finally
$\kappa_j<1/6$, directly from (2.3) and (2.12), so
$2(\ell_j-\kappa_j)-\gamma>2(2/5-1/6)-\gamma>0$ for the two
antisymmetric lines. This proves (2.8) on all orthogonal blocks.
The matrices are real symmetric; their positivity on real vectors implies
positivity on complex vectors by splitting a vector into real and
imaginary parts. In particular the kernel is exactly the four-dimensional
range of $K_{\rm ker}$. $\square$

**Theorem 2.4 (A necessary bound for every complex scalar port).** Every
$T\in\mathfrak C_1$ satisfies

$$
e(T)\ge\frac{12993}{25000}=0.51972.
\tag{2.14}
$$

Proof. A scalar-block encoder is a POVM: its $f$-th component has form
$X\mapsto\operatorname{tr}(M_fX)$ with $M_f\succeq0$ and
$\sum_fM_f=I_5$. A whole-block TP scalar decoder has form
$y\mapsto y\sigma_f$ with $\sigma_f\succeq0$ and
$\operatorname{tr}\sigma_f=1$. In the passive frame this gives

$$
\chi_T=\frac15\sum_f\sigma_f\otimes M_f^T\succeq0,
\quad \chi_T^\Gamma=\frac15\sum_f\sigma_f\otimes M_f\succeq0,
\quad \operatorname{Tr}_{\rm out}\chi_T=I_5/5,
\quad \operatorname{tr}\chi_T=1.
\tag{2.15}
$$

No reality, projector, covariance or unitality assumption has entered.
This also proves directly the needed direction of the usual
entanglement-breaking Choi correspondence.

For any normalized PPT matrix $\chi$, pair (2.8) separately with
$\chi$ and $\chi^\Gamma$. Both pairings are valid PSD trace pairings.
Using (2.5), the trace self-adjointness of partial transpose and (2.7)
gives

$$
\begin{aligned}
\operatorname{tr}\bigl(\chi(I\otimes Y-\mathcal W)\bigr)
&=\frac12\operatorname{tr}(P\chi)
 +\frac12\operatorname{tr}(P\chi^\Gamma)\\
&\ge\gamma\left(1-\frac12
\operatorname{tr}(\chi(K_{\rm ker}+K_{\rm ker}^\Gamma))\right)\\
&=\gamma\left(1-\frac12\operatorname{tr}(\chi Q)\right)
\ge\frac\gamma2=\frac1{50000}.
\end{aligned}
\tag{2.16}
$$

The last inequality uses $Q\preceq I$, not positivity of
$K_{\rm ker}^\Gamma$. For the same state's TP marginal,

$$
\operatorname{tr}(\chi_T\mathcal W)
\le\frac{\operatorname{tr}Y}{5}-\frac1{50000}
=\frac{4803}{10000}-\frac1{50000}
=\frac{12007}{25000}.
\tag{2.17}
$$

To connect this bound to actual protocols, the QEC moment is the actual
forward-time mean

$$
\mathcal W=\lim_{H\to\infty}\frac1H\int_0^H
\sum_s a_s Q_s(t)\otimes Q_s(t)\,dt,
\qquad
\mathscr S(T):=\lim_{H\to\infty}\frac1H\int_0^H g(t)\,dt
=\operatorname{tr}(\chi_T\mathcal W).
\tag{2.18}
$$

For completeness, $(\omega_+/\omega_-)^2=(21+5r)/4$ is irrational,
so no nonzero integer pair has $k\omega_++l\omega_-=0$.
The mean of every nonconstant Fourier term is zero, by integrating its
exponential. The finite Fourier expansion of the integrand makes its
mean equal to independent circle integration. The sector lengths from
(1.6), together with the planar moments
$\mathbb E n_an_b=\delta_{ab}/2$ and
$\mathbb E n_an_bn_cn_d=(\delta_{ab}\delta_{cd}
+\delta_{ac}\delta_{bd}+\delta_{ad}\delta_{bc})/8$, give exactly
(2.3). This is the supplied QEC weighted-moment calculation.
Choi contraction gives
$\operatorname{tr}(Q\widehat T(\rho))
=5\operatorname{tr}(\chi_T(Q\otimes\rho^T))$.
Since $Q_s(t)$ is real symmetric and $w_s=a_s/5$, this proves the
second equality in (2.18) with its normalization unchanged.

For each finite $t$ and mode $s$, prepare $DQ_s(t)D^\dagger$.
The actual wait $t$, full read and Stop give $s$ with certainty before
replacement, and with probability $f_s(t)$ after replacement.
Their TV is exactly $1-f_s(t)$. Thus $e(T)\ge1-f_s(t)$ for every
such test. Taking the weighted mean and its forward-time limit gives
$e(T)\ge1-\mathscr S(T)$. Equation (2.17) proves (2.14).
The proof even bounds the whole complex PPT TP Choi slice. It does not
identify PPT with separability, construct a port from a PPT point, mix
different marginals, or require a stationary competitor. $\square$

**Corollary 2.5 (Uniform finite-wait alternatives).** For every rational
$0<\delta<1$, put

$$
h=\frac\delta{48},\qquad
n=\left\lceil\frac{153600}{\delta^2}\right\rceil,\qquad
H=nh,\qquad \mathcal W_\delta=\{jh:0\le j\le n\}.
\tag{2.19}
$$

For every original legal complex scalar port, one of the $4(n+1)$
alternative tests with $s\in\{N,2,3,5\}$ and $t\in\mathcal W_\delta$,
input $DQ_s(t)D^\dagger$, actual wait $t$, complete read and Stop has

$$
\operatorname{TV}>\frac{12993}{25000}-\delta,
\qquad
\frac{3200}{\delta}\le H\le\frac{3200}{\delta}+\frac\delta{48}.
\tag{2.20}
$$

Proof. Retain the estimates of QEC Theorem 2.6, with the improved mean
(2.17). Here is their dependence on the original conditions.
The two-angle extension of $g$ is in $[0,1]$ for every CPTP channel,
because each conjugated rank-one projector is a state and an effect.
Its Fourier support satisfies $|k|+|l|\le4$, with at most forty
nonconstant indices and each coefficient of modulus at most one.
From (1.4), rational squaring gives
$2.13<\omega_+<2.14$ and $0.66<\omega_-<0.67$.
For all nonzero supported indices,
$|k\omega_++l\omega_-|>1/10$: equal signs are immediate; with
opposite signs, $|k|\ge2$ forces $|l|\le2$, whereas $|k|=1$
permits at most $|l|=3$ and gives
$2.13-3(0.67)=0.12>0.1$. Hence

$$
\left|H^{-1}\int_0^H g(t)\,dt-\mathscr S(T)\right|<800/H.
\tag{2.21}
$$

Since $H\ge3200/\delta$, some $t\in[0,H]$ and positive-weight mode
have failure at least $12993/25000-\delta/4$. The fourth-weight support
is precisely the displayed set of four modes.
For a rank-one projector $Q_s(t)$,
$\|Q_s'(t)\|_1\le2\|A\|$. CPTP trace-norm contraction on Hermitian
matrices, obtained from positive and negative parts, then gives
$|f_s'(t)|\le4\|A\|=4\omega_+<12$.
A grid point within $h$ loses at most $12h=\delta/4$ in failure.
Its TV is at least $12993/25000-\delta/2$, strictly greater than the
claimed threshold. The ceiling defining $n$ gives the time bounds.
All waits are finite and nonnegative. These are alternative single-input
tests, chosen for a competitor; they do not estimate an unknown channel
from one sample or supply physical preparation and clock bounds.
$\square$

## 3. A fixed fourteen-flag port with independent decoding

**Definition 3.1 (Measurement and preparation factors).** Let
$\alpha_k=2\pi k/3$ and $\beta_k=2\pi k/5$, and use the disjoint flag set

$$
F=\{(\mathrm A,k,l):0\le k,l<3\}
\sqcup\{(\mathrm B,k):0\le k<5\}.
\tag{3.1}
$$

The measurement vectors and weights are exactly the QFA encoder:

$$
\begin{aligned}
b_{\mathrm A,k,l}
&=\frac{\sqrt2\,w_+(\alpha_k)+\sqrt3\,w_-(\alpha_l)}{\sqrt5},
&c_{\mathrm A,k,l}&=\frac{10}{27},\\
b_{\mathrm B,k}
&=\frac{\sqrt3\,d+\sqrt2\,w_+(\beta_k)}{\sqrt5},
&c_{\mathrm B,k}&=\frac13.
\end{aligned}
\tag{3.2}
$$

Use independent preparation vectors

$$
\begin{aligned}
a_{\mathrm A,k,l}
&=\frac{14\sqrt6\,w_+(\alpha_k)+41w_-(\alpha_l)}{\sqrt{2857}},\\
a_{\mathrm B,k}
&=\frac{11d+5\sqrt6\,w_+(\beta_k)}{\sqrt{271}}.
\end{aligned}
\tag{3.3}
$$

Define the frame channel and original channel by

$$
S(X)=\sum_{f\in F}c_fa_fa_f^T\operatorname{tr}(b_fb_f^TX),
\qquad T_\theta(X)=DS(D^\dagger XD)D^\dagger.
\tag{3.4}
$$

These are fixed exact algebraic data. In particular, the three-point
circle values are $(1,0),(-1/2,\sqrt3/2),(-1/2,-\sqrt3/2)$.
The five-point values follow from
$\cos(2\pi/5)=(\sqrt5-1)/4$,
$\cos(4\pi/5)=-(\sqrt5+1)/4$,
$\sin(2\pi/5)=\sqrt{10+2\sqrt5}/4$ and
$\sin(4\pi/5)=\sqrt{10-2\sqrt5}/4$, with reflected signs.

**Theorem 3.2 (Whole-block CPTP legality).** The explicit maps

$$
\begin{gathered}
B_f=\sqrt{c_f}\,b_f^TD^\dagger:\mathbb C^5\longrightarrow\mathbb C,
\qquad R_f=Da_f:\mathbb C\longrightarrow\mathbb C^5,\\
\operatorname{Enc}(X)=(B_fXB_f^\dagger)_f,
\qquad \operatorname{Dec}_f(y)=R_fyR_f^\dagger
\end{gathered}
\tag{3.5}
$$

realize $T_\theta\in\mathfrak C_1$ with fourteen fixed scalar flags.
Every decoder is CPTP on all of $M_1$, and every composite Kraus matrix
$R_fB_f$ has rank one.

Proof. The orthogonal sectors make every $b_f$ unit. Every $a_f$ is
unit since $1176+1681=2857$ and $121+150=271$.
The quadratic three-point and five-point circle sums give

$$
\begin{aligned}
\sum_{k,l}c_{\mathrm A,k,l}b_{\mathrm A,k,l}b_{\mathrm A,k,l}^T
&=\frac{10}{3}\left(\frac15R_++\frac3{10}R_-\right)
=\frac23R_++R_-,\\
\sum_kc_{\mathrm B,k}b_{\mathrm B,k}b_{\mathrm B,k}^T
&=\frac53\left(\frac35R_0+\frac15R_+\right)
=R_0+\frac13R_+.
\end{aligned}
\tag{3.6}
$$

Consequently $\sum_fB_f^\dagger B_f=I_5$ and
$R_f^\dagger R_f=1$ for each flag. Matrix sandwiches remain positive
after tensoring with the identity at every reference dimension.
Direct sums prove encoder CP, and sums prove composite CP.
The normalization identities prove encoder TP and every decoder's TP
on all complex matrices in its block, rather than just on encountered
states. The decoded branch is
$c_fDa_fb_f^TD^\dagger XDb_fa_f^TD^\dagger$; its Kraus matrix is
nonzero and rank one. All paths traverse the stated scalar block;
there is no input retention or additional flag supplied to the future.

For each branch, cyclicity of the trace gives
$\operatorname{tr}(R_fB_fXB_f^\dagger R_f^\dagger)
=\operatorname{tr}(B_fXB_f^\dagger)$, since $R_f^\dagger R_f=1$.
The flag probability is therefore unchanged by decoding, and summing
the branch traces gives $\operatorname{tr}X$. $\square$

**Lemma 3.3 (Exact quadrature and whole-channel stationarity).** The finite
channel (3.4) equals its continuous orbit expression with normalized
circle measures and total orbit weights $10/3$ and $5/3$. It commutes
with every $\operatorname{Ad}_{G(\alpha,\beta)}$ and with
$\operatorname{Ad}_{\mathsf J}$ on every complex matrix.

Proof. Use (3.2)–(3.3) at continuous angles to define $a_{\mathrm A},
b_{\mathrm A},a_{\mathrm B},b_{\mathrm B}$. The coefficient tensor of
an atom is $a a^T\otimes b b^T$, still of total degree four although
the two vectors differ. For A, the planar bidegrees are
$(4,0),(3,1),(2,2),(1,3),(0,4)$.
A homogeneous circle monomial of degree $m$ has frequencies
$-m,-m+2,\ldots,m$. The three-point sum kills frequencies not divisible
by three. At even degrees zero, two and four only zero survives.
At bidegrees $(3,1),(1,3)$ the degree-one factor has both discrete and
continuous mean zero, so the degree-three alias cannot contribute.
For B, every frequency lies between $-4$ and $4$, and the five-point
sum kills all nonzero frequencies. This proves, coefficient by
coefficient on all complex inputs,

$$
S(X)=\frac{10}{3}\int a_{\mathrm A}a_{\mathrm A}^T
\operatorname{tr}(b_{\mathrm A}b_{\mathrm A}^TX)
+\frac53\int a_{\mathrm B}a_{\mathrm B}^T
\operatorname{tr}(b_{\mathrm B}b_{\mathrm B}^TX).
\tag{3.7}
$$

Shifting the common angle in both factors leaves these integrals
unchanged, proving rotation covariance. For the reflection,
$\mathsf Jd=-d$ and $\mathsf Jw_\pm(\alpha)=w_\pm(-\alpha)$.
The A integral is invariant under angle reversal. In B, after an
irrelevant simultaneous sign in each vector's projector, reflection
maps both factors to the angle $\pi-\alpha$. Its integral is invariant
too. Thus the finite channel has both asserted symmetries.
These integrals identify an already finite fixed design, not a
continuous flag, limiting wait or extra future control. This is the
QFA quartic quadrature mechanism applied to independent factors.
$\square$

## 4. Exact nonsymmetric boundary coordinates and the adjoint

**Proposition 4.1 (Joint populations, full marginal and cone membership).**
Let $\Lambda$ have preparation/output row index and measurement/input
column index, both ordered $(0,+,-)$. Its exact value for (3.4) is

$$
\Lambda=\begin{pmatrix}
121/271&242/813&0\\
150/271&710628/774247&2352/2857\\
0&6724/8571&3362/2857
\end{pmatrix}.
\tag{4.1}
$$

In QRC coordinates, with $\tau=(1,\sqrt2,\sqrt2)^T$,

$$
M_{ij}=\frac{\Lambda_{ij}}{\sqrt{d_id_j}},\qquad
\eta=\left(\frac{110}{271},0,
\frac{\Lambda_{++}}4,\frac{\Lambda_{--}}4,
\frac{1148}{2857},\frac{1148}{2857}\right),
\tag{4.2}
$$

in order $(+,-,2+,2-,\Delta,\Sigma)$. These exact coordinates belong
to the actual independent real-product atom cone and satisfy the full
TP marginal $M^T\tau=\tau$. The channel is nonunital and not
self-adjoint.

Proof. The four sector-population vectors are

$$
\begin{aligned}
p_{a\mathrm A}&=(0,1176/2857,1681/2857)^T,&
p_{b\mathrm A}&=(0,2/5,3/5)^T,\\
p_{a\mathrm B}&=(121/271,150/271,0)^T,&
p_{b\mathrm B}&=(3/5,2/5,0)^T.
\end{aligned}
\tag{4.3}
$$

Then $\Lambda=(10/3)p_{a\mathrm A}p_{b\mathrm A}^T
+(5/3)p_{a\mathrm B}p_{b\mathrm B}^T$, giving (4.1).
Its three column sums are exactly $(1,2,2)$, so (4.2) gives
$M^T\tau=\tau$. In particular, the normalized Choi matrix is

$$
\chi_S=\frac15\sum_fc_f(a_fa_f^T)\otimes(b_fb_f^T),\qquad
\operatorname{Tr}_{\rm out}\chi_S=I_5/5.
\tag{4.4}
$$

To specify the cone membership fully, use QRC's orthonormal invariant
matrices $H_i=R_i/\sqrt{d_i}$ and its six orthonormal pairs
$(F_{\nu1},F_{\nu2})$. Define
$h_i(a)=a^TR_ia/\sqrt{d_i}$,
$z_\nu(a)=(a^TF_{\nu1}a,a^TF_{\nu2}a)^T$, and
$k(a,b)=(h(a)h(b)^T,(z_\nu(a)^Tz_\nu(b)/2)_\nu)$.
The point here is exactly

$$
(M,\eta)=\frac{10}{3}k(a_{\mathrm A}(0,0),b_{\mathrm A}(0,0))
+\frac53 k(a_{\mathrm B}(0),b_{\mathrm B}(0)).
\tag{4.5}
$$

The symmetries proved in Lemma 3.3 identify its orbit coordinates with
these QRC generators. Their trivial block is (4.1) divided by
$\sqrt{d_id_j}$. The planar traceless coefficient is
$\Lambda_{jj}/4$. The dark/plus coefficient is
$(5/3)(55\sqrt6/271)(\sqrt6/5)=110/271$; the mixed-plane coefficients
are both $(10/3)(574\sqrt6/2857)(\sqrt6/5)/2=1148/2857$.
The dark/minus coefficient vanishes. This proves all of (4.2) and
(4.5), using actual product atoms rather than PPT feasibility.

The dark coefficient of $S(I)$ is the first row sum of $\Lambda$,
$605/813\ne1$. Also
$M_{0+}=242/(813\sqrt2)\ne150/(271\sqrt2)=M_{+0}$.
Thus $S(I)\ne I$ and $S\ne S^\dagger$.
TP concerns column sums; unitality would concern row sums.
Independent decoder factors are essential to the specification of this
channel. No restriction on other competitors follows. $\square$

**Proposition 4.2 (The effect map, with its orientation fixed).** For a
real symmetric $E$, put $t_i=\operatorname{tr}(R_iE)$ and define

$$
\begin{aligned}
\mathcal A(E)={}&\Lambda_{00}t_0R_0
+\sum_{j=+,-}\frac{\Lambda_{jj}}8(t_jR_j+2R_jER_j)\\
&+\sum_{i\ne j}\frac{\Lambda_{ij}}{d_id_j}\,t_iR_j\\
&+\frac{110}{271}(R_0ER_++R_+ER_0)
+\frac{1148}{2857}(R_+ER_-+R_-ER_+).
\end{aligned}
\tag{4.6}
$$

Then $\mathcal A=S^\dagger$. Both sides extend complex linearly after
replacing $X$ by $(X+X^T)/2$. The formula for $S(E)$ has instead
$t_jR_i$ in the sum over $i\ne j$; the other displayed terms agree.

Proof. For one flag, the adjoint is
$E\mapsto c_fb_fb_f^T\operatorname{tr}(a_fa_f^TE)$.
Take the exact continuous averages (3.7). In a plane, the fourth
moment is $(t_jR_j+2R_jER_j)/8$. Distinct planes have independent
second moments, so diagonal output/input sectors contribute
$\Lambda_{ij}t_iR_j/(d_id_j)$ to the adjoint. Two dark/plane cross
terms give the coefficient $110/271$ in (4.6), and two planar cross
terms give $1148/2857$, as computed in Proposition 4.1. These terms
are self-adjoint as linear maps on symmetric matrices, while the
sector-transfer block is transposed on taking the adjoint.
Both real-product maps annihilate transpose-antisymmetric inputs,
proving the complex-linear extension assertion.

As a direct check, for $E=I$ one has $t_i=d_i$. The $R_j$
coefficient in (4.6) is $\sum_i\Lambda_{ij}/d_j=1$; cross terms
vanish. Hence $\mathcal A(I)=I$ exactly. In contrast the row sums in
Proposition 4.1 show why substituting $S$ for $\mathcal A$ would be
incorrect. $\square$

## 5. A complete exact certificate for all fifteen events

**Definition 5.1 (Residuals and coefficient data).** For every singleton
or pair $J\subseteq\mathsf S$, define

$$
H_J=\Pi_J-\mathcal A(\Pi_J).
\tag{5.1}
$$

Use $L=(N,25)$ and $V=(2,3,5)$. All these matrices are block diagonal
in $L\oplus V$ by (1.6) and (4.6), and have entries in $\mathbb Q(r)$.
Here is complete singleton data, making the finite certificate independent
of numerical evaluation. Set $m=1263571104$, and write

$$
m\mathcal A(\Pi_s)=
\begin{pmatrix}a&b\\b&c\end{pmatrix}_L
\oplus\begin{pmatrix}d&e&f\\e&g&h\\f&h&k\end{pmatrix}_V.
\tag{5.2}
$$

Each pair $(u,v)$ below denotes $u+vr$, not two matrix entries.

| $s$ | $a$ | $b$ | $c$ |
| --- | --- | --- | --- |
| $N$ | $(621151364,-3608532)$ | $(-31225496,-7936840)$ | $(129035856,359888)$ |
| $2$ | $(147948012,1742676)$ | $(-15621420,9499572)$ | $(155758722,-3007110)$ |
| $3$ | $(217487860,483068)$ | $(31242840,-3125464)$ | $(201866440,2045800)$ |
| $5$ | $(147948012,1742676)$ | $(-15621420,9499572)$ | $(155758722,-3007110)$ |
| $25$ | $(129035856,-359888)$ | $(31225496,-7936840)$ | $(621151364,3608532)$ |

| $s$ | $d$ | $e$ | $f$ |
| --- | --- | --- | --- |
| $N$ | $(188357420,3759812)$ | $(-5207140,-1562732)$ | $(13509020,-6525388)$ |
| $2$ | $(476161125,31783305)$ | $(-23419122,18631902)$ | $(-21573987,-6271935)$ |
| $3$ | $(183167624,-15967632)$ | $(46838244,-3968420)$ | $(8319224,14887968)$ |
| $5$ | $(219716805,-13471575)$ | $(-23419122,-11538018)$ | $(-21573987,-6271935)$ |
| $25$ | $(196168130,-6103910)$ | $(5207140,-1562732)$ | $(21319730,4181290)$ |

| $s$ | $g$ | $h$ | $k$ |
| --- | --- | --- | --- |
| $N$ | $(217487860,1922620)$ | $(-5207140,-1562732)$ | $(188357420,3759812)$ |
| $2$ | $(142758216,-7756896)$ | $(-23419122,-11538018)$ | $(219716805,-13471575)$ |
| $3$ | $(558700372,10825596)$ | $(46838244,-3968420)$ | $(183167624,-15967632)$ |
| $5$ | $(142758216,-7756896)$ | $(-23419122,18631902)$ | $(476161125,31783305)$ |
| $25$ | $(201866440,2765576)$ | $(5207140,-1562732)$ | $(196168130,-6103910)$ |

These entries follow by substituting $t_i=(R_i)_{ss}$ and
$R_i\Pi_sR_j=(R_ie_s)(R_je_s)^T$ into (4.6), followed by
$r^2=17$. They sum to $mI$ over $s$, also checking
$\mathcal A(I)=I$. For every pair, add its two singleton matrices
and subtract from $m\Pi_J$. In particular, the same channel supplies
all fifteen event tests.

**Lemma 5.2 (Simultaneous strict minor bounds).** For a matrix block in
the fixed order $L$ or $V$, let $\Delta_k$ be the determinant of its
leading $k\times k$ principal submatrix. Every entry in the next table
is a strict lower bound, uniform over the indicated events and signs.

| Events | Matrix | $\Delta_1(L)$ | $\Delta_2(L)$ | $\Delta_1(V)$ | $\Delta_2(V)$ | $\Delta_3(V)$ |
| --- | --- | --- | --- | --- | --- | --- |
| All ten pairs and $\{25\}$ | $I/2\pm H_J$ | $2/25$ | $1/500$ | $7/100$ | $3/10000$ | $1/10000$ |
| $\{2\},\{3\},\{5\}$ | $(26213/50000)I\pm H_J$ | $7/20$ | $1/8$ | $1/250$ | $1/2500$ | $1/200000$ |
| $\{N\}$ | $I/2+H_N$ | $1$ | $2/5$ | $1/3$ | $1/10$ | $9/250$ |

Consequently the eleven events in the first row have norm below $1/2$,
the three in the second row have norm below $26213/50000$, and
$H_N\succ-I/2$.

Proof. Here is a rational certificate for all $110+30+5=145$
inequalities. Integer squaring gives

$$
r_-:=\frac{4123105}{1000000}<r<
r_+:=\frac{2061553}{500000}.
\tag{5.3}
$$

For $x=u+vr\in\mathbb Q(r)$, after reducing by $r^2=17$, put

$$
\mathcal L(x)=
\begin{cases}u+vr_-,&v\ge0,\\u+vr_+,&v<0.\end{cases}
\tag{5.4}
$$

This is a rational lower bound for $x$. Reduction precedes endpoint
substitution; determinants at a fictitious physical source are not
being used. Apply (2.13) and its two-dimensional version to (5.2).
The exact minima of $\mathcal L(\Delta_k)$ over each row's events
and signs, in the five-column order of the displayed minor table, are

$$
\begin{aligned}
\mathbf m_1=\bigg(&
\frac{2550986292187}{31589277600000},
\frac{145634780064979}{72200452882560000},
\frac{18550575484933}{252714220800000},\\[-2pt]
&\frac{500320088596678933}{1330509945719815680000},
\frac{134457340051112983}{1330509945719815680000}\bigg),\\
\mathbf m_2=\bigg(&
\frac{55370023301729}{157946388000000},
\frac{2825499825261754314539}{22562641525800000000000},
\frac{405047449671}{84238073600000},\\[-2pt]
&\frac{20570908698283648019381}{41578435803744240000000000},
\frac{2161305730306518257799809}{415784358037442400000000000000}\bigg),\\
\mathbf m_3=\bigg(&
\frac{64454182416593}{63178555200000},
\frac{145178533822590539}{361002264412800000},
\frac{17830251190997}{52648796000000},\\[-2pt]
&\frac{452502063300490155889}{4157843580374424000000},
\frac{17998076394403593139}{489158068279344000000}\bigg).
\end{aligned}
\tag{5.5}
$$

For clarity, the finite comparisons specified by (5.5) use all pairs
$\{N,2\},\{N,3\},\{N,5\},\{N,25\},\{2,3\},\{2,5\},
\{2,25\},\{3,5\},\{3,25\},\{5,25\}$; the first two rows
include both signs. Matrix entries add and multiply as pairs by
$(u,v)(u',v')=(uu'+17vv',uv'+vu')$.
Together with (5.2), (2.13) and (5.4), this specifies every rational
identity in (5.5). Each coordinate of $\mathbf m_i$ strictly exceeds
its corresponding simple bound in the minor table, by cross multiplication
of positive denominators. Thus all leading principal minors are positive.
Sylvester's criterion on the real symmetric $2\times2$ and $3\times3$
blocks gives the asserted strict Loewner inequalities, hence the norm
bounds. This proof does not use the trace-zero singleton criterion:
for this nonunital channel, $\operatorname{tr}\mathcal A(\Pi_s)$ need
not equal one. $\square$

**Definition 5.3 (The exact active value).** Put

$$
\begin{gathered}
D_0=315892776,\qquad
a_0=160604935+902133r,\\
b_0=7806374+1984210r,\qquad
c_0=-32258964-89972r,\\
C_N=\frac1{D_0}\begin{pmatrix}a_0&b_0\\b_0&c_0\end{pmatrix},\\
p_N(z)=\det(zI_2-C_N)
=z^2-\frac{a_0+c_0}{D_0}z
+\frac{a_0c_0-b_0^2}{D_0^2},\\
\theta=\frac{a_0+c_0+
\sqrt{(a_0-c_0)^2+4b_0^2}}{2D_0}.
\end{gathered}
\tag{5.6}
$$

The radical is the nonnegative real square root.

**Theorem 5.4 (Exact event maximum and root isolation).** The number
$\theta$ is the unique positive root of $p_N$, and

$$
\frac{52427}{100000}<\theta<\frac{13107}{25000},\qquad
\max_{1\le|J|\le2}\|H_J\|_{\rm op}=\theta.
\tag{5.7}
$$

Only the singleton $N$ reaches this maximum.

Proof. The $L$ block of $H_N$, obtained from (5.2), is exactly $C_N$.
One has $a_0>0$, $c_0<0$, and $b_0>0$. Thus
$a_0c_0-b_0^2<0$, giving exactly one positive eigenvalue and one
negative eigenvalue in $C_N$. The positive one is (5.6).
The $V$ block is a compression of $-\mathcal A(\Pi_N)$ and is
nonpositive, since $\mathcal A=S^\dagger$ is positive.

For an exact root sign certificate, reduce $p_N(z)$ in $\mathbb Q(r)$
and use the same interval (5.3). The appropriate affine endpoint values
give

$$
\begin{aligned}
p_N(52427/100000)
&<\frac{-8876548390036701}{6016704406880000000000}
<-\frac1{1000000},\\
p_N(13107/25000)
&>\frac{54591695728667293}{11281320762900000000000}
>\frac1{250000}.
\end{aligned}
\tag{5.8}
$$

These substitutions use only (5.6), $r^2=17$, and rational arithmetic.
There is only one positive root, so the signs prove its isolation.
Lemma 5.2 bounds all negative eigenvalues of $H_N$ in magnitude by
$1/2$, which is below $\theta$. Its positive eigenvalue is therefore
its norm. The other fourteen events have norms below either $1/2$ or
$26213/50000$, and

$$
\frac12<\frac{26213}{50000}
<\frac{52427}{100000}<\theta.
\tag{5.9}
$$

This proves the event maximum. No self-adjointness of the channel or
trace-zero property of $H_N$ was assumed. $\square$

## 6. Actual-history error, attaining input and remaining boundary

**Theorem 6.1 (Exact original error of the independent-decoder port).**
The fixed port (3.5) has, for all original complex inputs and all actual
finite adaptive histories,

$$
e(T_\theta)=\theta
=0.524272337746606724475420251080046976\ldots .
\tag{6.1}
$$

Its error is attained by an explicit algebraic pure input, actual wait
zero, one complete five-outcome rank-one read, and Stop.

Proof. The channel is stationary on all complex matrices by Lemma 3.3.
Apply the supplied first-read identity (1.8) and its stationary
consequence (1.9), always with $S^\dagger=\mathcal A$. TP gives
$\mathcal A(I)=I$, so complements reduce the full event family to
the fifteen tests certified in Theorem 5.4. This proves the upper
bound for the entire history and input suprema in (1.3).

To recall why the first-read identity covers these suprema, before the
first read there are no source-dependent results. A deterministic policy
therefore has a common prefix of waits totaling a nonnegative $t$, or
stops without a read. In the latter case its histories agree. In the
former case, after first outcome $s$, each compared conditional state
is $\Pi_s$. The common finite suffix is a probability kernel depending
on that outcome and the common controls, not on the original input.
With the first outcome retained, summing the absolute probability
differences over the suffix gives exactly the first-outcome TV.
Forgetting records cannot increase it. Source-independent random
controls mix these inequalities under the same mixing law, even if
the control record is retained. Conversely one wait, full read and
Stop realizes each first-read comparison. Finally maximizing a
Hermitian event expectation over all complex density inputs gives
its operator norm. This preserves every quantifier of the original
contract, rather than testing only real states or a bounded depth.

For explicit attainment, define the nonzero real vector

$$
v_0=b_0e_N+(D_0\theta-a_0)e_{25},\qquad
v=\frac{v_0}{\sqrt{b_0^2+(D_0\theta-a_0)^2}},\qquad
\rho_\theta=Dvv^TD^\dagger.
\tag{6.2}
$$

The denominator is positive because $b_0>0$. The first row of
$C_Nv_0=\theta v_0$ holds immediately; the second is the identity
$(D_0\theta-a_0)(D_0\theta-c_0)=b_0^2$ from $p_N(\theta)=0$.
Thus $H_Nv=\theta v$. Since $D$ is the identity on $L$, the frame
identification introduces no phase in this example. For input
$\rho_\theta$, wait zero and a full mode read, the mode-$N$ probability
difference is
$\operatorname{tr}(\Pi_N(\rho_\theta-T_\theta(\rho_\theta)))
=v^TH_Nv=\theta$.
The full outcome TV is at least this difference and at most the proved
upper $\theta$, so equality holds. The singleton event is a grouping
of the full read, not a new instrument. No closure angle, inaccessible
wait, hidden record or limiting input is used. $\square$

**Corollary 6.2 (A strictly narrower unrestricted interval).** Under
Assumption 1.1 and the original fixed-port contract,

$$
\boxed{\frac{12993}{25000}\le\varepsilon_1\le\theta},\qquad
\theta-\frac{12993}{25000}
=0.004552337746606724475420251080046976\ldots .
\tag{6.3}
$$

Proof. Theorem 2.4 covers every original legal competitor; Theorems 3.2
and 6.1 provide one original legal attaining upper construction.
Relative to QEC's endpoints,

$$
\frac{12993}{25000}-\frac{5197}{10000}=\frac1{50000}>0,
\qquad
\theta<\frac{13107}{25000}<\frac{37}{70}<\xi.
\tag{6.4}
$$

The last inequality is QEC Theorem 4.4 for its exact cubic root
$\xi$; the preceding rational comparison is direct cross multiplication.
The older endpoints retain their stated domains as weaker bounds.
$\square$

**Definition 6.3 (Unresolved obligations and separate resources).** A
matching lower bound at $\theta$, an evaluated minimum of the full QRC
cone with its three TP equations and all fifteen event inequalities,
and a globally optimal original port remain open. This volume proves
neither an optimum within an orbit ansatz nor that an unrestricted
optimizer belongs to the displayed fourteen-flag family. It also gives
no further no-loss restriction to $a=b$, real Kraus for an unchanged
channel, unital channels, symmetric $M$, or definite-character Kraus
operators. QRC's no-worse real replacement changes a channel and keeps
independent factors; QPC §9's obstructions remain in force.

The lower slack $\gamma$ is a sufficient exact spectral shift, not a
maximal shift or an optimum of a PPT relaxation. Zero pair multipliers
in its inherited weighted-test dual do not remove any pair constraint
from the primal. The upper satisfies every pair and singleton inequality
for one common normalized channel. Neither certificate replaces real
product separability by PPT.

The original $q=2,3,4$ optima and their credited bounds are unchanged.
The native all-length verifier, native memory-rate theorem, a preparation
map from the $\alpha/\beta$ trees to Assumption 1.1, and the general
mutual-recovery bridges between relations, space, time, boundary and
memory remain open programme obligations. The native definitions
`GraftAffineClosure.step`, `quantity`, and `run` specify a classical
composition dynamics; they do not constitute a quantum preparation map.

Fourteen finite scalar flags, rank-one composite Kraus matrices and
exact algebraic coefficient descriptions suffice for this mathematical
port. These resources are separate from coefficient synthesis,
finite-precision robustness, state acquisition, clocks, physical
transport and storage duration. No bounds for those physical resources
are inferred. The finite-wait alternatives in Corollary 2.5 also do
not provide a sample-complexity or channel-identification theorem.

## 7. Sources and evidence scope

**Convention 7.1 (Literature status).** The witness-slack consequence
and the particular independent-decoder certificate are `repo-derived`
results, with their complete data and derivations above. The first-read,
compactness, no-worse stationary and real-coordinate results belong to
the credited supplier sources. No worldwide originality claim follows
from this classification.

| Primary source | Exact use and boundary |
| --- | --- |
| [Horodecki–Shor–Ruskai, quant-ph/0302031v2, Theorem 4(A–D)](https://arxiv.org/html/quant-ph/0302031v2) | `literature-attested`: measure-and-prepare, rank-one Kraus and separable Choi correspondence, with the separate POVM/TP condition. Equations (2.15) and (3.6) establish the normalization needed here directly. |
| [Doherty–Parrilo–Spedalieri, quant-ph/0308032, §§IV, VI](https://arxiv.org/html/quant-ph/0308032) | `literature-attested`: PSD/PPT weak duality and decomposable witnesses. The explicit shifted certificate is (2.8); PPT sufficiency is not used. |
| [Fuchs–Sasaki, quant-ph/0302092v3, §4.2.2, pp. 16–18, Eqs. (97)–(98)](https://arxiv.org/html/quant-ph/0302092v3) | `literature-attested`: the finite-group irreducibility and rank-one orbit-POVM argument has those hypotheses and that location. Section 4.3 concerns the uniform all-pure-state ensemble. Neither evaluates this reducible $1+2+2$ actual-menu minimax. Only elementary circle moments are used here. |
| [Nechita–Park, 2403.03667v2, §2.1](https://arxiv.org/html/2403.03667v2) | `literature-attested`: representation-dependent averaging. Scalar twirl formulas require their multiplicity hypotheses; group-specific PPT/entanglement-breaking equivalences are not general DOC or present-cone equivalences. The needed invariant multiplicity-three block remains arbitrary in QRC. |
| [Ohst et al., 2411.08110v2, §3.3 and Appendix C](https://arxiv.org/html/2411.08110v2) | `literature-attested`: constrained separability includes specified constraints on individual decomposition factors. A summed TP marginal and joint walk symmetry do not establish that correspondence. No optimum is imported. |
| [Koßmann–Zeiss, 2607.23689v1, §§4–5, 7.1](https://arxiv.org/html/2607.23689v1) | `literature-attested`: fixed-point extension results have their own per-factor constraints. No bridge from this joint covariance and common TP marginal to those constraints is supplied. |
| [Hildebrand, math/0701571v1, Theorems 3.8, 3.9, 8.1](https://arxiv.org/html/math/0701571v1) | Their specified low-dimensional real/complex separability spaces do not identify the whole $5\times5$ QRC cone with PPT. No such identification is assumed. |
| [Leditzky et al., 1709.01111v3, Lemma III.8](https://arxiv.org/html/1709.01111v3) | The dimension-product restriction and diamond-norm objective are different from (1.3); the result supplies no minimax value here. |
| [Milazzo–Braun–Giraud, 2006.15003v1, Theorem 4](https://arxiv.org/html/2006.15003v1) | Flat-extension extraction is conditional on its moment/localizing and flatness hypotheses. No such extension for the present minimum is supplied or used. |

**Convention 7.2 (What the finite certificates establish).** The shifted
determinants, integer singleton data, rational minor certificates and
root signs are exact finite arithmetic in $\mathbb Q(\sqrt{17})$.
Their role is to certify the two displayed mathematical constructions;
no numerical mesh, finite time window, relaxed feasible point or ensemble
average is an optimum certificate. The all-complex and all-finite-history
consequences follow from the ordinary operational proofs, not from
sampling. These checks and source correspondences do not replace
independent mathematical review, required repository checks or Lean
kernel verification.

## 追加锚（本行以下为增补区）
