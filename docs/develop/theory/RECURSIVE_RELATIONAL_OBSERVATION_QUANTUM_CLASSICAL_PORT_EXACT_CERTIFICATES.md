# Recursive relational observation: exact certificates for a classical quantum port

## 1. Preparation, actual histories and spectral coordinates

**Assumption 1.1 (The original five-mode source).** Let $\mathcal H=\mathbb C^5$
with ordered orthonormal basis $\mathsf S=(N,2,3,5,25)$ and
$\Pi_s=e_se_s^\dagger$. Every complex density matrix on $\mathcal H$ is
an allowed input. Set

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

This is precisely
[QMB Assumption 1.1](https://github.com/the-omega-institute/trureturing/blob/720d8d9671ab19dbd8be12bc17d238eb4201fa5d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md).
It is an independent quantum preparation hypothesis; $N$ denotes a unit
basis vector. No preparation map from the native $\alpha/\beta$ tree or
from a tensor-cut source is part of this assumption.

**Definition 1.2 (The fixed port and its actual-menu error).** A future
protocol consists of nonnegative waits $U(t)$, complete five-outcome
rank-one Lüders reads $X\mapsto(\Pi_sX\Pi_s)_{s\in\mathsf S}$, and Stop.
All finite adaptive depths are included. Histories retain outcomes,
controls and stops. Initial controls and any random control resources
are independent of the input, and both comparisons use the same policy.
Grouping a full read's outcomes is classical postprocessing. Independent
mode phases, arbitrary future unitaries, source copies, resets, probability
oracles, external quantum side information, readable hidden Kraus records
and coarse-block Lüders instruments are absent.

A scalar port is one fixed CPTP encoder and fixed whole-block CPTP decoders

$$
\operatorname{Enc}:M_5\longrightarrow\bigoplus_{f\in F}M_1,
\qquad \operatorname{Dec}((y_f)_f)=\sum_f\operatorname{Dec}_f(y_f),
\qquad \operatorname{Dec}_f:M_1\longrightarrow M_5,
\tag{1.2}
$$

where $F$ is finite and the design precedes the input and future policy.
There is no retained source, entangled assistance or quantum bypass.
The finite classical flag is free for this dimension criterion, is used
in decoding, and is not additionally exposed to the later policy.
Let $\mathfrak C_1$ contain every such complex CPTP composite, and define

$$
e(T)=\sup_{\rho\in\mathcal D(\mathcal H)}
\sup_{\pi\text{ actual, finite}}
\operatorname{TV}(P_\rho^\pi,P_{T(\rho)}^\pi),
\qquad \varepsilon_1=\inf_{T\in\mathfrak C_1}e(T).
\tag{1.3}
$$

The input is replaced once before the common protocol. TV is half the
$\ell^1$ difference, with its measure version for random controls.
CPTP legality includes arbitrary reference extensions; the performance
criterion uses system histories only. These are exactly QMB Definitions
1.2–1.3. In
[Bluhm–Rauber–Wolf, *Quantum compression relative to a set of measurements*, Definition 4.1 and Lemmas 5.2–5.3](https://arxiv.org/html/1708.04898v4),
the ambient and compressed dimensions correspond to $D=5,d=1$ and the
classical algebra to $\mathbb C^{|F|}$. Their exact operator-system
preservation criterion is distinct from the particular approximate norm
in (1.3).

**Definition 1.3 (Passive coordinates and the three sectors).** Put

$$
\begin{gathered}
r=\sqrt{17},\quad D=\operatorname{diag}(1,i,i,i,1),\quad
A=-iD^\dagger KD,\quad O(t)=e^{tA}=D^\dagger U(t)D,\\
\widehat T(X)=D^\dagger T(DXD^\dagger)D,\quad
Q_J(t)=O(t)^T\Pi_JO(t),\quad \Pi_J=\sum_{s\in J}\Pi_s,\\
B=-A^2,\quad \mu_\pm=(5\pm r)/2,\quad \omega_\pm=\sqrt{\mu_\pm},\\
R_\pm=\frac{B(B-\mu_\mp I)}{\mu_\pm(\mu_\pm-\mu_\mp)},\quad
R_0=I-R_+-R_-=dd^T,\quad d=(e_2-e_5)/\sqrt2,\\
W_\pm=AR_\pm/\omega_\pm,\quad
u_\pm=\frac{R_\pm e_N}{\sqrt{(1\pm1/r)/2}},\quad
w_\pm(\theta)=\cos\theta\,u_\pm+\sin\theta\,W_\pm u_\pm.
\end{gathered}
\tag{1.4}
$$

Transposition always refers to this real frame; a dagger denotes an
adjoint, or the trace-pairing dual for maps. Write $\mathcal H_j$ for the
complexification of $\operatorname{ran}_{\mathbb R}R_j$, with dimensions
$(d_0,d_+,d_-)=(1,2,2)$. These are the spectral coordinates of QMB
Theorem 4.1,
[QPC Convention 6.1](https://github.com/the-omega-institute/trureturing/blob/720d8d9671ab19dbd8be12bc17d238eb4201fa5d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_PORT_COVARIANCE_AND_CERTIFIED_FRONTIER.md)
and
[QFA Definition 1.3](https://github.com/the-omega-institute/trureturing/blob/720d8d9671ab19dbd8be12bc17d238eb4201fa5d/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_QUANTUM_FINITE_PORT_ATTAINMENT.md).
Their identities follow directly by ordering coordinates as
$L=(N,25)$, $V=(2,3,5)$:

$$
A=\begin{pmatrix}0&C\\-C^T&0\end{pmatrix},\qquad
C=\begin{pmatrix}1&1&1\\1&0&1\end{pmatrix},\qquad
CC^T=\begin{pmatrix}3&2\\2&2\end{pmatrix}.
\tag{1.5}
$$

The nonzero squared frequencies solve $x^2-5x+2=0$.
Consequently the $R_j$ are mutually orthogonal projections,
$W_j^T=-W_j$, $W_j^2=-R_j$, and $u_j,W_ju_j$ are orthonormal plane
bases. Explicitly,

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

Thus the squared sector lengths $r_{sj}=(R_j)_{ss}$ are

$$
\begin{array}{c|ccc}
s&r_{s0}&r_{s+}&r_{s-}\\\hline
N&0&(1+1/r)/2&(1-1/r)/2\\
2&1/2&(1+3/r)/4&(1-3/r)/4\\
3&0&(1-3/r)/2&(1+3/r)/2\\
5&1/2&(1+3/r)/4&(1-3/r)/4\\
25&0&(1-1/r)/2&(1+1/r)/2
\end{array}.
\tag{1.7}
$$

The matrices
$G(\theta,\phi)=R_0+\cos\theta R_++\sin\theta W_+
+\cos\phi R_-+\sin\phi W_-$ are mathematical coordinates;
the actual wait has angles $(\omega_+t,\omega_-t)$. The frame $D$ and
independent angles are not extra future controls.

## 2. A complex PPT certificate coupled to the TP marginal

**Definition 2.1 (Weighted actual tests and tensor notation).** Use mode
weights

$$
a=(9/4,3/4,5/4,3/4,0),\qquad
w=a/5=(9/20,3/20,1/4,3/20,0).
\tag{2.1}
$$

For any CPTP $\widehat T$, put
$f_s(t)=\operatorname{tr}(Q_s(t)\widehat T(Q_s(t)))$ and
$g(t)=\sum_sw_sf_s(t)$.
Use output-first normalized Choi matrices

$$
\Omega=5^{-1/2}\sum_se_s\otimes e_s,\qquad
\chi_T=(\widehat T\otimes\mathrm{id})(\Omega\Omega^\dagger),
\qquad \operatorname{Tr}_{\rm out}\chi_T=I_5/5.
\tag{2.2}
$$

Let $\Gamma$ transpose the input tensor factor. Let $\mathsf F$ be swap,
$\eta_j=\operatorname{vec}(R_j)=\sum_{a,b}(R_j)_{ab}e_a\otimes e_b$,
and define

$$
\begin{gathered}
I_j=R_j\otimes R_j,\quad F_j=I_j\mathsf F,\quad
E_j=\eta_j\eta_j^\dagger,\\
I_{jk}=R_j\otimes R_k+R_k\otimes R_j,\quad F_{jk}=I_{jk}\mathsf F,\quad
E_{jk}=\eta_j\eta_k^\dagger+\eta_k\eta_j^\dagger\quad(j<k).
\end{gathered}
\tag{2.3}
$$

Order the sector labels as $(0,+,-)$. Choi matrices are mathematical
representations of the system channel; (2.2) introduces no reference
performance test. The rank-one Kraus, measure-and-prepare and complex
separable-Choi equivalences are
[Horodecki–Shor–Ruskai, *Entanglement Breaking Channels*, Theorem 4(A–D)](https://arxiv.org/html/quant-ph/0302031)
and QMB Theorem 5.1. In particular a legal scalar port has
$\chi_T\ge0$, $\chi_T^\Gamma\ge0$ and the displayed TP marginal.
The marginal is an additional constraint, not a consequence of separability.

**Proposition 2.2 (The exact weighted moment).** The forward-time mean

$$
\mathcal W=\lim_{H\to\infty}\frac1H\int_0^H
\sum_sa_sQ_s(t)\otimes Q_s(t)\,dt
\tag{2.4}
$$

exists and obeys $\mathcal W^\Gamma=\mathcal W$ and

$$
\begin{gathered}
\mathcal W=\sum_j\kappa_j(I_j+F_j+E_j)
+\sum_{j<k}b_{jk}(I_{jk}+F_{jk}+E_{jk}),\\
S_{jk}:=\sum_sa_sr_{sj}r_{sk},\qquad
S=\begin{pmatrix}
3/8&3/16+9r/272&3/16-9r/272\\
3/16+9r/272&(331-3r)/272&49/68\\
3/16-9r/272&49/68&(331+3r)/272
\end{pmatrix},\\
\kappa_j=\frac{S_{jj}}{d_j(d_j+2)},\qquad
b_{jk}=\frac{S_{jk}}{d_jd_k},\\
h_j:=3\kappa_j,\quad
h=\left(\frac38,\frac{993-9r}{2176},\frac{993+9r}{2176}\right),\\
b_{0+}=\frac3{32}+\frac{9r}{544},\quad
b_{0-}=\frac3{32}-\frac{9r}{544},\quad b_{+-}=\frac{49}{272}.
\end{gathered}
\tag{2.5}
$$

For every CPTP channel, its mean survival satisfies

$$
\mathscr S(T):=\lim_{H\to\infty}\frac1H\int_0^Hg(t)\,dt
=\operatorname{tr}(\chi_T\mathcal W),\qquad e(T)\ge1-\mathscr S(T).
\tag{2.6}
$$

Proof. The squared frequency ratio is $(21+5r)/4$, which is irrational;
therefore $\omega_+/\omega_-$ is irrational. For every nonzero integer
pair $(k,l)$,

$$
\frac1H\int_0^He^{i(k\omega_++l\omega_-)t}\,dt
=\frac{e^{i(k\omega_++l\omega_-)H}-1}
{iH(k\omega_++l\omega_-)}\longrightarrow0.
\tag{2.7}
$$

All entries of (2.4) are finite trigonometric polynomials, so their actual
forward-time means equal independent circle integrals. This is the
finite-Fourier argument of QPC Lemma 6.2 applied to the new weights.
On a real $d$-sphere, for $d=1,2$, the needed moments are

$$
\mathbb E[n_an_b]=\delta_{ab}/d,\qquad
\mathbb E[n_an_bn_cn_e]
=\frac{\delta_{ab}\delta_{ce}+\delta_{ac}\delta_{be}
+\delta_{ae}\delta_{bc}}{d(d+2)}.
\tag{2.8}
$$

For $d=2$ these follow from sine/cosine fourth moments $3/8,3/8,1/8$;
for $d=1$ the fourth power is one. Although the actual dark component
has fixed sign, every term with an odd plane degree vanishes, so the same
fourth-moment formula applies. Within one sector the three pairings in
(2.8) give $I_j,F_j,E_j$. Between two sectors the second moments give
$I_{jk},F_{jk},E_{jk}$ with coefficient $S_{jk}/(d_jd_k)$.
Substitution of (1.7) gives every entry of $S$ in (2.5).
Partial transpose interchanges $F_j,E_j$ and $F_{jk},E_{jk}$ and fixes
the $I$ terms, proving the asserted invariance.

For any matrices $Q,\rho$, Choi contraction gives
$\operatorname{tr}(Q\widehat T(\rho))
=5\operatorname{tr}(\chi_T(Q\otimes\rho^T))$.
Since $Q_s(t)$ is real symmetric and $w_s=a_s/5$, the factor five
cancels exactly and proves the equality in (2.6).
For physical input $DQ_s(t)D^\dagger$, the actual wait $t$ and full
read originally give $s$ with certainty. After replacement, the survival
probability is $f_s(t)$, so that read followed by Stop has TV exactly
$1-f_s(t)$. Thus $e(T)\ge1-f_s(t)$ for every finite $t,s$.
Average with the nonnegative normalized weights and then take the mean
to prove (2.6). No isotropic mean-input condition is used.
This weighted survival functional is an accessible-fidelity comparison
as in
[Fuchs–Sasaki, *Squeezing Quantum Information through a Classical Channel*, §3](https://arxiv.org/html/quant-ph/0302092v3);
the comparison is an inequality with (1.3), not an equality of objectives.
$\square$

**Definition 2.3 (Exact marginal multiplier and decomposable witness).** Set

$$
\begin{gathered}
(\ell_0,\ell_+,\ell_-)=\frac1{10000}(4025,4974,5021),\qquad
Y=\ell_0R_0+\ell_+R_++\ell_-R_-,\\
u_{0+}=-\frac{12204}{100000},\quad
u_{0-}=-\frac{5359}{100000},\quad
u_{+-}=-\frac{13938}{100000},\\
t_0=0,\quad t_+=2\kappa_+-\ell_+,\quad t_-=2\kappa_--\ell_-,\\
P=I_5\otimes Y-\mathcal W
+\sum_jt_j(F_j-E_j)+\sum_{j<k}u_{jk}(F_{jk}-E_{jk}).
\end{gathered}
\tag{2.9}
$$

Here $u_{jk}$ are scalar coefficients, distinct from the plane vectors
$u_\pm$ of (1.4).

**Lemma 2.4 (Full complex positivity certificate).** The matrix $P$ in
(2.9) is positive semidefinite on $\mathbb C^5\otimes\mathbb C^5$, and

$$
I_5\otimes Y-\mathcal W=\frac{P+P^\Gamma}{2}.
\tag{2.10}
$$

Proof. Equation (2.10) follows immediately from Proposition 2.2 and the
partial-transpose oddness of every added difference in (2.9).
For positivity, first decompose the tensor space using the real orthogonal
sectors $\mathcal H_j$. In each plane's same-sector tensor square the
symmetric traceless subspace has eigenvalue
$\ell_j-2\kappa_j+t_j=0$. The antisymmetric line has eigenvalue
$\ell_j-t_j=2(\ell_j-\kappa_j)$.
The remaining three trace directions are $\eta_j/\sqrt{d_j}$.
Their matrix is $\operatorname{diag}(\sqrt d)\,N\,
\operatorname{diag}(\sqrt d)$, where

$$
\begin{aligned}
N_{jj}&=\ell_j-h_j,&N_{jk}&=-(b_{jk}+u_{jk}),\\
N&=\begin{pmatrix}
11/400&2829/100000-9r/544&-251/6250+9r/544\\
2829/100000-9r/544&55839/1360000+9r/2176&-8663/212500\\
-251/6250+9r/544&-8663/212500&62231/1360000-9r/2176
\end{pmatrix}.
\end{aligned}
\tag{2.11}
$$

For each $j<k$, the cross-sector spaces give $d_jd_k$ copies of

$$
D_{jk}=\begin{pmatrix}
\ell_k-b_{jk}&u_{jk}-b_{jk}\\
u_{jk}-b_{jk}&\ell_j-b_{jk}
\end{pmatrix}.
\tag{2.12}
$$

The following table gives exact determinants $(a+br)/D$ and a positive
rational lower bound. For $N$ use its leading principal submatrices.

| Determinant | $a$ | $b$ | $D$ | Lower bound |
| --- | --- | --- | --- | --- |
| $N_1$ | $11$ | $0$ | $400$ | $11/400$ |
| $N_2$ | $-1470248319$ | $356934375$ | $340000000000$ | $22844841/5440000000000$ |
| $N_3$ | $-10641427272359$ | $2581015359375$ | $1156000000000000000$ | $5714494081/18496000000000000000$ |
| $D_{0+}$ | $6635237139$ | $-1608721875$ | $85000000000$ | $73596447/2720000000000$ |
| $D_{0-}$ | $17742727773$ | $2845631250$ | $170000000000$ | $235804399839/1360000000000$ |
| $D_{+-}$ | $228311$ | $0$ | $5312500000$ | $228311/5312500000$ |

Every denominator is positive. Squaring integers gives

$$
\left(\frac{41231}{10000}\right)^2<17
<\left(\frac{412311}{100000}\right)^2.
\tag{2.13}
$$

For $b>0$ insert the left endpoint into $(a+br)/D$, and for $b<0$
insert the right endpoint. For $b=0$ the last column is the exact value.
This gives exactly the displayed lower bounds, strictly when $b\ne0$.
The determinant identities follow from $r^2=17$ and

$$
\det\begin{pmatrix}x&u&v\\u&y&w\\v&w&z\end{pmatrix}
=xyz+2uvw-xw^2-yv^2-zu^2.
\tag{2.14}
$$

The first and second leading determinants are $x$ and $xy-u^2$.
Thus (2.11)–(2.14) specify the arithmetic of all six rows.
Positive leading pivots show $N>0$, hence $\ell_j>h_j=3\kappa_j$.
The antisymmetric eigenvalues are consequently positive.
All $\ell_j>2/5$ and $0<b_{jk}<1/5$, so both diagonals in (2.12)
are positive. Their determinants are positive, giving $D_{jk}>0$.
The trace block, symmetric traceless blocks, antisymmetric blocks and
cross-sector blocks have dimensions $3,4,2,16$, respectively, totaling
25. This proves $P\ge0$ on the real tensor space and hence on its complexification:
for real symmetric $P$ and $z=x+iy$,
$z^\dagger Pz=x^TPx+y^TPy\ge0$.
This is an orthogonal decomposition of a witness, not a decomposition
restriction on any competing channel. $\square$

**Theorem 2.5 (Unrestricted necessary error).** Every original legal
complex scalar port satisfies

$$
e(T)\ge\frac{5197}{10000},\qquad
\varepsilon_1\ge\frac{5197}{10000}.
\tag{2.15}
$$

Proof. For any $\chi\ge0$ with $\chi^\Gamma\ge0$, Lemma 2.4 gives

$$
\operatorname{tr}\bigl(\chi(I\otimes Y-\mathcal W)\bigr)
=\frac12\operatorname{tr}(P\chi)
+\frac12\operatorname{tr}(P\chi^\Gamma)\ge0.
\tag{2.16}
$$

Only weak duality and PSD trace pairing are used. In particular the
inequality holds on every complex product vector: partial transpose
replaces its input factor by its complex conjugate in the quadratic form
of $P$. A scalar-port rank-one Kraus term $C_i=s_i a_i b_i^\dagger$
contributes Choi vector $s_i a_i\otimes\overline{b_i}$.
This covers independent arbitrary complex measurement and preparation
vectors, whether or not the Choi coefficients are real.
The use of PSD and partial-transposed PSD matrices is the decomposable
witness framework of
[Doherty–Parrilo–Spedalieri, *A complete family of separability criteria*, §§IV, VI](https://arxiv.org/html/quant-ph/0308032).
Here the explicit witness is (2.9), not a numerical relaxation value.

Apply (2.16) to the separable TP Choi state of any legal $T$:

$$
\mathscr S(T)\le\operatorname{tr}(\chi_T(I\otimes Y))
=\frac{\operatorname{tr}Y}{5}
=\frac{4025+2(4974)+2(5021)}{50000}
=\frac{4803}{10000}.
\tag{2.17}
$$

The equality uses the same channel's full TP marginal. In Kraus coordinates
it is exactly $\sum_i s_i^2b_ib_i^\dagger=I_5$, so independent atom
maxima have not been combined without their common normalization.
Proposition 2.2 now gives (2.15). The argument already holds before
stationarity is imposed. It even bounds every PPT Choi matrix with this
TP marginal, which is an outer class; feasibility in that outer class
would not construct a scalar port. $\square$

**Theorem 2.6 (A finite family of faithful nonnegative waits).** For any
rational $0<\delta<1$, put

$$
h=\frac\delta{48},\qquad
n=\left\lceil\frac{153600}{\delta^2}\right\rceil,\qquad
\mathcal W_\delta=\{jh:0\le j\le n\},\qquad H=nh.
\tag{2.18}
$$

For every legal complex scalar port there is a test with
$s\in\{N,2,3,5\}$ and $t\in\mathcal W_\delta$, input
$DQ_s(t)D^\dagger$, and protocol wait $t$, full mode read, Stop, whose
TV exceeds $5197/10000-\delta$. There are $4(n+1)$ alternatives, and

$$
\frac{3200}{\delta}\le H\le\frac{3200}{\delta}+\frac\delta{48}.
\tag{2.19}
$$

Proof. The two-angle extension of $g$ in Definition 2.1 is in $[0,1]$
for every CPTP competitor. Its Fourier support satisfies $|k|+|l|\le4$,
so there are at most 40 nonconstant indices and every normalized Fourier
coefficient has modulus at most one. Squaring rational endpoints in
(1.4) gives

$$
2.13<\omega_+<2.14,\qquad 0.66<\omega_-<0.67.
\tag{2.20}
$$

For every nonzero supported index, $|k\omega_++l\omega_-|>1/10$.
For same-sign indices this is immediate. With opposite signs, $|k|\ge2$
forces $|l|\le2$ and gives a lower bound
$2(2.13)-2(0.67)>1/10$; $|k|=1$ permits $|l|\le3$ and gives
$2.13-3(0.67)=0.12>1/10$.
Integrating the exponentials as in (2.7) therefore gives

$$
\left|H^{-1}\int_0^Hg(t)\,dt-\mathscr S(T)\right|<800/H.
\tag{2.21}
$$

By (2.17)–(2.19), some $t\in[0,H]$ and a positive-weight mode have
failure at least $5197/10000-\delta/4$.
For discretization, $Q_s'=-AQ_s+Q_sA$ and
$\|Q_s'\|_1\le2\|A\|$. Positive and negative parts show that CPTP
maps contract the trace norm on Hermitian matrices. Differentiating $f_s$
thus gives $|f_s'|\le4\|A\|=4\omega_+<12$.
A grid point within $h$ decreases failure by at most $12h=\delta/4$.
Its TV is at least $5197/10000-\delta/2$, strictly greater than the
claimed threshold. The ceiling gives (2.19).
These are alternative legitimate single-input experiments for each channel;
the statement does not infer probabilities from one sample or assert a
physical preparation or clock cost. The time-average argument has produced
finite nonnegative waits with a uniform termination and error bound.
$\square$

## 3. An explicit fourteen-flag sufficient channel

**Definition 3.1 (Fixed algebraic design).** Let
$(c_k,s_k)=(\cos(2\pi k/3),\sin(2\pi k/3))$ and
$(C_k,S_k)=(\cos(2\pi k/5),\sin(2\pi k/5))$, with exact entries

$$
\begin{array}{c|cc}
k&c_k&s_k\\\hline
0&1&0\\1&-1/2&\sqrt3/2\\2&-1/2&-\sqrt3/2
\end{array}
\qquad
\begin{array}{c|cc}
k&C_k&S_k\\\hline
0&1&0\\
1&(\sqrt5-1)/4&\sqrt{10+2\sqrt5}/4\\
2&-(\sqrt5+1)/4&\sqrt{10-2\sqrt5}/4\\
3&-(\sqrt5+1)/4&-\sqrt{10-2\sqrt5}/4\\
4&(\sqrt5-1)/4&-\sqrt{10+2\sqrt5}/4
\end{array}.
\tag{3.1}
$$

Use the disjoint flags
$F=\{(\mathrm A,k,l):0\le k,l<3\}\sqcup
\{(\mathrm B,k):0\le k<5\}$ and set

$$
\begin{aligned}
v_{\mathrm A,k,l}
&=\sqrt{3/7}(c_ku_++s_kW_+u_+)
+\sqrt{4/7}(c_lu_-+s_lW_-u_-),&c_{\mathrm A,k,l}&=7/18,\\
v_{\mathrm B,k}
&=\sqrt{2/3}d+\sqrt{1/3}(C_ku_++S_kW_+u_+),&c_{\mathrm B,k}&=3/10,\\
P_f&=v_fv_f^T,\qquad
S(X)=\sum_fc_fP_fXP_f,&T_\xi(X)&=DS(D^\dagger XD)D^\dagger.
\end{aligned}
\tag{3.2}
$$

The flag coefficient $c_f$ is distinct from $c_k$ in (3.1).
The support pattern and finite quadrature geometry are those of QFA
Definition 2.1 and Lemma 2.2; (3.2) uses populations
$(0,3/7,4/7)$ and $(2/3,1/3,0)$ in place of QFA's
$(0,2/5,3/5)$ and $(3/5,2/5,0)$.

**Theorem 3.2 (Exact finite CPTP scalar realization).** Define

$$
\begin{gathered}
B_f=\sqrt{c_f}\,v_f^TD^\dagger:\mathbb C^5\longrightarrow\mathbb C,
\qquad R_f=Dv_f:\mathbb C\longrightarrow\mathbb C^5,\\
\operatorname{Enc}(X)=(B_fXB_f^\dagger)_f,\qquad
\operatorname{Dec}_f(y)=R_fyR_f^\dagger.
\end{gathered}
\tag{3.3}
$$

They realize $T_\xi\in\mathfrak C_1$ with fourteen fixed flags and
whole-block TP decoding. The channel $S$ is TP, unital, Hilbert–Schmidt
self-adjoint and stationary on all complex matrices.

Proof. Orthogonal summands in (1.4) make every $v_f$ unit.
Put $v_{\mathrm A}(\theta,\phi)=\sqrt{3/7}w_+(\theta)
+\sqrt{4/7}w_-(\phi)$ and
$v_{\mathrm B}(\theta)=\sqrt{2/3}d+\sqrt{1/3}w_+(\theta)$.
Write $P_{\mathrm A},P_{\mathrm B}$ for their projectors.
The nine-point A average integrates $PXP$ exactly: every coefficient has
planar bidegree $(4,0),(3,1),(2,2),(1,3)$ or $(0,4)$.
At even degrees zero, two and four, the three-point circle rule leaves
only zero frequency. At bidegrees $(3,1),(1,3)$ the degree-one factor
has zero discrete and continuous mean, killing any degree-three alias.
The B rule has five points and every frequency lies between $-4$ and
$4$, so all its nonzero frequencies vanish. The quadratic projector
averages are exact by the same argument. These are coefficient-tensor
identities, valid for arbitrary complex $X$. With normalized circle
measures,

$$
S(X)=\frac72\int P_{\mathrm A}XP_{\mathrm A}
+\frac32\int P_{\mathrm B}XP_{\mathrm B}.
\tag{3.4}
$$

The two projector-sum contributions are exactly

$$
\frac72\left(\frac3{14}R_++\frac27R_-\right)
=\frac34R_++R_-,\qquad
\frac32\left(\frac23R_0+\frac16R_+\right)
=R_0+\frac14R_+.
\tag{3.5}
$$

Hence $\sum_fc_fP_f=I$,
$\sum_fB_f^\dagger B_f=I_5$ and $R_f^\dagger R_f=1$.
Every rectangular sandwich remains positive after arbitrary reference
amplification. These normalization identities give encoder TP and each
decoder's TP on all of $M_1$. The composite Kraus matrices are
$\sqrt{c_f}DP_fD^\dagger$, all rank one. Every quantum path factors
through its declared scalar; flags are consumed in decoding.
This matches
[FiniteStateChannel.QuantumChannel](https://github.com/the-omega-institute/trureturing/blob/720d8d9671ab19dbd8be12bc17d238eb4201fa5d/D5/S3/Quantum/Foundation/FiniteStateChannel.lean)
with input/output index set $\mathrm{Fin}\,5$, and
[finite_kraus_quantum_channel](https://github.com/the-omega-institute/trureturing/blob/720d8d9671ab19dbd8be12bc17d238eb4201fa5d/D5/S3/Quantum/Foundation/FiniteKrausChannel.lean)
with Kraus index $F$, matrices $\sqrt{c_f}DP_fD^\dagger$, and its
hypothesis $\sum_fC_f^\dagger C_f=I_5$. For a scalar decoder the
input index is $\mathrm{Fin}\,1$, the output index is $\mathrm{Fin}\,5$,
and the single Kraus matrix is $R_f$.
The branch probability identity agrees with
[finite_kraus_instrument_born_marginal](https://github.com/the-omega-institute/trureturing/blob/720d8d9671ab19dbd8be12bc17d238eb4201fa5d/D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.lean):
for a complete mode read its outcome index is $\mathsf S$, its Kraus
index is a singleton, and its Kraus matrix at outcome $s$ is $\Pi_s$.

Each sandwich $P_fXP_f$ is self-adjoint as a superoperator; normalization
gives both $S(I)=I$ and TP. Shifting either angle in (3.4) proves
commutation with $\operatorname{Ad}_{G(\theta,\phi)}$ on all complex
matrices, hence with the actual waits. The integrals identify an already
finite fixed channel, not a continuous flag or independent physical
phase control. These properties describe this construction only; they
impose no projector, unitality or reality condition on competitors.
$\square$

**Proposition 3.3 (The changed population moment).** For real symmetric
$E$, set $t_j=\operatorname{tr}(R_jE)$. Then

$$
\begin{aligned}
S(E)={}&(2t_0/3+t_+/6)R_0
+(t_0/6+17t_+/168+3t_-/14)R_+\\
&+(3t_+/14+t_-/7)R_-
+\frac{17}{84}R_+ER_++\frac27R_-ER_-\\
&+\frac13(R_0ER_++R_+ER_0)
+\frac37(R_+ER_-+R_-ER_+).
\end{aligned}
\tag{3.6}
$$

Proof. Equation (3.4) is $5\mathbb E[PXP]$ with orbit probabilities
$7/10,3/10$, populations $p_{\mathrm A}=(0,3/7,4/7)$,
$p_{\mathrm B}=(2/3,1/3,0)$ and moments

$$
\mathbb E p=(1,2,2)/5,\qquad
M=\mathbb E[pp^T]
=\frac1{105}\begin{pmatrix}14&7&0\\7&17&18\\0&18&24\end{pmatrix}.
\tag{3.7}
$$

Contract the circle moments (2.8). The dark coefficient is
$5M_{00}t_0+(5/2)\sum_{j=+,-}M_{0j}t_j$.
A plane's diagonal block, for the other plane $k$, is

$$
\frac{5M_{jj}}8(t_jR_j+2R_jER_j)
+\frac{5M_{0j}}2t_0R_j+\frac{5M_{jk}}4t_kR_j.
\tag{3.8}
$$

Dark/plane cross blocks have coefficient $5M_{0j}$ and the two-plane
cross block has coefficient $5M_{+-}/2$. Substitution of (3.7)
gives (3.6). This is the fourth-moment contraction used in QFA
Proposition 3.1, evaluated at the different joint populations (3.7).
The corresponding moment techniques in Fuchs–Sasaki §§4.2–4.3 concern
ensemble fidelity; their irreducible symmetry hypotheses do not assert
optimality for the present reducible $1+2+2$ representation. $\square$

## 4. Exact simultaneous certificates for the fifteen events

**Proposition 4.1 (Complete singleton coefficient data).** In the ordered
splitting $L=(N,25)$, $V=(2,3,5)$, define coefficients by

$$
22848S(\Pi_s)=
\begin{pmatrix}a_s&b_s\\b_s&c_s\end{pmatrix}_L
\oplus
\begin{pmatrix}d_s&e_s&f_s\\e_s&g_s&h_s\\f_s&h_s&k_s\end{pmatrix}_V.
\tag{4.1}
$$

Their exact values are as follows; every cross-block entry is zero.

| $s$ | $a_s$ | $b_s$ | $c_s$ | $d_s$ | $e_s$ | $f_s$ | $g_s$ | $h_s$ | $k_s$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $N$ | $11340-84r$ | $-744-168r$ | $1920$ | $2780+28r$ | $-124-28r$ | $876-84r$ | $4028+28r$ | $-124-28r$ | $2780+28r$ |
| $2$ | $2780+28r$ | $-372+196r$ | $2966-70r$ | $9127+441r$ | $-558+294r$ | $-1345-63r$ | $2656-168r$ | $-558-154r$ | $5319-231r$ |
| $3$ | $4028+28r$ | $744-56r$ | $3656+56r$ | $2656-168r$ | $1116-84r$ | $752+168r$ | $9852+252r$ | $1116-84r$ | $2656-168r$ |
| $5$ | $2780+28r$ | $-372+196r$ | $2966-70r$ | $5319-231r$ | $-558-154r$ | $-1345-63r$ | $2656-168r$ | $-558+294r$ | $9127+441r$ |
| $25$ | $1920$ | $744-168r$ | $11340+84r$ | $2966-70r$ | $124-28r$ | $1062+42r$ | $3656+56r$ | $124-28r$ | $2966-70r$ |

For every singleton or pair $J$, the full residual is
$H_J=\Pi_J-\sum_{s\in J}S(\Pi_s)$.

Proof. In (3.6), substitute $t_j=(R_j)_{ss}$ and
$R_i\Pi_sR_j=(R_ie_s)(R_je_s)^T$, using the explicit matrices
(1.6). Reducing by $r^2=17$ gives the nine entries in each row.
For example the active block of $H_{\{N\}}$ is
$\left(\begin{smallmatrix}959+7r&62+14r\\62+14r&-160\end{smallmatrix}\right)/1904$.
All these substitutions are identities in $\mathbb Q(r)$;
linearity gives every pair from the same channel. $\square$

**Lemma 4.2 (Ten pairs and the singleton $25$).** Every event $J$ in the
next table satisfies $\|H_J\|_{\rm op}<37/70$.
The entries are the exact maximum absolute row sums of the full affine
matrix $H_J(x)$ from (4.1), where $x$ replaces $r$ only in that table.

| $J$ | At $x=4$ | At $x=25/6$ |
| --- | --- | --- |
| $\{25\}$ | $937/1904$ | $1867/3808$ |
| $\{N,2\}$ | $1313/2856$ | $463/1008$ |
| $\{N,3\}$ | $1117/2856$ | $2213/5712$ |
| $\{N,5\}$ | $1313/2856$ | $463/1008$ |
| $\{N,25\}$ | $939/1904$ | $5669/11424$ |
| $\{2,3\}$ | $983/1904$ | $17785/34272$ |
| $\{2,5\}$ | $101/204$ | $151/306$ |
| $\{2,25\}$ | $151/336$ | $1709/3808$ |
| $\{3,5\}$ | $983/1904$ | $17785/34272$ |
| $\{3,25\}$ | $2423/5712$ | $14405/34272$ |
| $\{5,25\}$ | $151/336$ | $1709/3808$ |

Proof. To obtain each entry, sum the chosen numerator rows of (4.1),
subtract from $22848\Pi_J$, substitute the indicated rational endpoint,
take entrywise absolute values and maximize the five row sums after
scaling by $22848$. This specifies all 22 rational identities.
For example the mode-$3$ row of $H_{\{2,3\}}$ at $x=25/6$ has
entries $-1433/22848$, $1665/3808$, $1301/68544$ in columns $(2,3,5)$.
Their absolute sum is $17785/34272$.
Since $4<r<25/6$, each absolute row sum at $r$ is at most its convex
interpolation between the endpoint row sums. Symmetry bounds operator
norm by maximum absolute row sum. Every endpoint entry is at most
$17785/34272$, and

$$
\frac{17785}{34272}<\frac{37}{70},\qquad
37\cdot34272-70\cdot17785=23114>0.
\tag{4.2}
$$

Thus all eleven events obey the claimed strict bound. $\square$

**Lemma 4.3 (The singleton positive-index criterion).** For any singleton
$s$, $H_{\{s\}}$ has trace zero and at most one positive eigenvalue.
If nonzero, its norm is its unique positive eigenvalue. The block
containing $e_s$ has that eigenvalue; the other block is nonpositive.
In the nonzero case, for $c>0$ the determinant of $cI$ minus the
containing block is positive exactly when that positive eigenvalue is
less than $c$.

Proof. $S(\Pi_s)\ge0$ and has trace one by Theorem 3.2.
The quadratic form of $H_{\{s\}}=\Pi_s-S(\Pi_s)$ is nonpositive
on $e_s^\perp$. Hence a two-dimensional positive eigenspace is impossible.
A nonzero trace-zero Hermitian matrix has a positive eigenvalue; the sum
of all absolute negative eigenvalues equals it. Each individual negative
eigenvalue therefore has smaller or equal absolute value. The other
coordinate block is a compression of $-S(\Pi_s)$ and is nonpositive.
All factors $c-\lambda$ associated with nonpositive eigenvalues of the
containing block are positive, so its determinant has the sign of
$c-\lambda_{\rm positive}$. The zero residual case has norm zero and
positive determinant for every $c>0$. $\square$

**Theorem 4.4 (The active cubic and the exact event maximum).** Define

$$
p(z)=z^3+\frac{-2873+21r}{11424}z^2
+\frac{-13393+981r}{68544}z
+\frac{-171581+24645r}{9321984}.
\tag{4.3}
$$

There is exactly one positive root $\xi$, with

$$
\frac{37}{70}<\xi<\frac{529}{1000},\qquad
\max_{1\le|J|\le2}\|H_J\|_{\rm op}=\xi.
\tag{4.4}
$$

The maximum is attained by the singletons $2$ and $5$.

Proof. The remaining containing blocks from Proposition 4.1 are

$$
\begin{aligned}
C_N&=\frac1{1904}\begin{pmatrix}959+7r&62+14r\\62+14r&-160\end{pmatrix},\\
C_3&=\frac1{22848}\begin{pmatrix}
-2656+168r&-1116+84r&-752-168r\\
-1116+84r&12996-252r&-1116+84r\\
-752-168r&-1116+84r&-2656+168r
\end{pmatrix},\\
C_2&=\frac1{22848}\begin{pmatrix}
13721-441r&558-294r&1345+63r\\
558-294r&-2656+168r&558+154r\\
1345+63r&558+154r&-5319+231r
\end{pmatrix}.
\end{aligned}
\tag{4.5}
$$

Here $C_N$ is on $L$; $C_2,C_3$ are on $V$.
The next table states exact identities
$\det(cI-C_s)=(a+br)/D$ and sign bounds.

| $s$ | $c$ | $a$ | $b$ | $D$ | Bound on determinant |
| --- | --- | --- | --- | --- | --- |
| $N$ | $37/70$ | $2211$ | $-455$ | $166600$ | $>2673/1332800>0$ |
| $3$ | $37/70$ | $-26090291$ | $6532155$ | $1189524000$ | $>2055469/2973810000>0$ |
| $2$ | $37/70$ | $-120370013$ | $29152805$ | $2718912000$ | $<-131077/3107328000<0$ |
| $2$ | $529/1000$ | $-1070804918761$ | $260462029625$ | $24276000000000$ | $>1149321647/12138000000000>0$ |

Expand using (2.14), its two-dimensional version and $r^2=17$.
For signs, rational squaring gives $103/25<r<33/8$;
substituting the appropriate endpoint into the affine numerator gives
exactly the last column. Lemma 4.3 proves
$\|H_{\{N\}}\|,\|H_{\{3\}}\|<37/70$.
It also proves that $C_2$ has a unique positive eigenvalue between
$37/70$ and $529/1000$. Direct determinant expansion gives
$\det(zI-C_2)=p(z)$, including all three nonleading coefficients in
(4.3). Therefore this eigenvalue is $\xi$ and is the only positive root.
By Lemma 4.3 the full singleton-$2$ norm is $\xi$, including its
negative eigenvalues and its other coordinate block.
Exchanging modes $2$ and $5$ leaves $R_\pm$ invariant and sends
$d$ to $-d$. Formula (3.6), or the full table (4.1), therefore conjugates
$H_{\{2\}}$ to $H_{\{5\}}$ by this permutation.
Lemma 4.2 covers all remaining events. This proves (4.4) for the same
single channel simultaneously, without a restricted-family optimum claim.
$\square$

## 5. The original-history interval and actual attainment

**Theorem 5.1 (Exact all-input, all-history error of the finite port).**
The port (3.3) satisfies

$$
e(T_\xi)=\xi=0.52871214445486778799\ldots .
\tag{5.1}
$$

Its error is attained by one algebraic pure input, wait zero, one complete
five-outcome rank-one mode read, and Stop.

Proof. QMB Theorem 2.1 gives the exact first-read identity

$$
e(T_\xi)=\sup_{t\ge0}\max_{J\subseteq\mathsf S}
\|Q_J(t)-S^\dagger(Q_J(t))\|_{\rm op}.
\tag{5.2}
$$

The reset in this identity is decisive: after first outcome $s$, both
conditional states equal $\Pi_s$, so the common suffix of every finite
adaptive policy is a probability kernel. Retaining the first outcome
preserves its TV; further common processing cannot enlarge it.
Source-independent random controls are mixtures of these comparisons.
Conversely wait $t$, a complete read, and Stop realize each first-read
comparison. Maximizing a Hermitian event expectation over every complex
density input gives its operator norm. Thus (5.2) retains the full input
and history quantifiers of Definition 1.2.

By Theorem 3.2, self-adjointness and stationarity yield

$$
Q_J(t)-S^\dagger(Q_J(t))=O(t)^TH_JO(t).
\tag{5.3}
$$

Its norm is independent of actual nonnegative waiting time.
Since $S(I)=I$, complementary residuals are negatives; empty and full
events vanish. The fifteen singleton/pair representatives cover every
event. Theorem 4.4 now proves (5.1), with the decimal only illustrating
the exact root (4.3)–(4.4).

For an explicit attaining state, write
$C_2=\left(\begin{smallmatrix}a&b&c\\b&d&e\\c&e&f\end{smallmatrix}\right)$
in the ordered $V$ basis and set

$$
B_2=\begin{pmatrix}d&e\\e&f\end{pmatrix},\quad
h=\begin{pmatrix}b\\c\end{pmatrix},\quad
v=\frac{(1,\ ((\xi I_2-B_2)^{-1}h)^T)^T}
{\|(1,\ ((\xi I_2-B_2)^{-1}h)^T)^T\|}.
\tag{5.4}
$$

The matrix $B_2$ is a compression of $-S(\Pi_2)$, hence is nonpositive.
Since $\xi>0$, the inverse in (5.4) exists.
The Schur complement of $\xi I_2-B_2$ in $\xi I_3-C_2$, together
with $p(\xi)=0$, proves $C_2v=\xi v$.
Embed $v$ with zero $L$ coordinates and prepare
$\rho_\xi=Dvv^\dagger D^\dagger$. Its mode-$2$ probability difference
at actual wait zero is $v^\dagger H_{\{2\}}v=\xi$.
The full read's TV is at least that difference and at most the proved
upper $\xi$, so equality holds. All coefficients of this input are
algebraic. No limiting torus point, inaccessible event instrument or
negative physical wait is involved. $\square$

**Corollary 5.2 (A strictly narrower unrestricted interval).** For the
original complex scalar-port problem,

$$
\boxed{\frac{5197}{10000}\le\varepsilon_1\le\xi},\qquad
\xi-\frac{5197}{10000}=0.00901214445486778799\ldots .
\tag{5.5}
$$

The necessary endpoint strictly exceeds the credited QPC lower
$L=1-((5556+423r)/13414+63/125)/2$.
The sufficient endpoint strictly improves the QFA construction's displayed
error

$$
a_\star=\frac{17r+3+\sqrt{10458+198r}}{80r},\qquad
\xi<\frac{529}{1000}<\frac{27}{50}<a_\star.
\tag{5.6}
$$

Proof. Apply Theorem 2.5 to all competitors and Theorems 3.2 and 5.1
to the exhibited port. For the lower comparison,
$m=(5556+423r)/13414>1/2$ since $r>4$; hence
$L<249/500<5197/10000$.
For the upper comparison, direct algebra makes $a_\star$ the positive
root of

$$
z^2-\frac{289+3r}{680}z-\frac{173+3r}{3400}.
\tag{5.7}
$$

Its constant term is negative and its value at $27/50$ is
$(1907-555r)/170000<0$. Therefore its unique positive root exceeds
$27/50$. This verifies the comparison using QFA's exact algebraic
endpoint; the new upper's feasibility and all-event certificate have
been established independently in §§3–5. $\square$

## 6. The joint event–marginal–separability relation

**Proposition 6.1 (Placement of the lower witness in the full dual).**
In the stationary fifteen-event formulation of QPC Theorem 3.3,
the certificate in §2 has singleton multipliers
$A_{\{s\}}^+=w_s\Pi_s$, all negative multipliers zero, and all pair
multipliers zero. It is a feasible decomposable dual certificate for the
full original objective with value $5197/10000$.

Proof. A single common normalized separable Choi state must obey
$\operatorname{Tr}_{\rm out}\chi=I/5$ and all inequalities

$$
-zI\le H_J\le zI,\qquad
H_J=\Pi_J-5\left[\operatorname{Tr}_{\rm out}
((\Pi_J\otimes I)\chi)\right]^T,
\quad 1\le|J|\le2.
\tag{6.1}
$$

For PSD multipliers with
$\sum_J\operatorname{tr}(A_J^++A_J^-)=1$, put
$Z_J=A_J^+-A_J^-$,
$\beta=\sum_J\operatorname{tr}(Z_J\Pi_J)$ and
$\mathcal W_Z=5\sum_J\Pi_J\otimes Z_J^T$.
Pairing (6.1) with those multipliers gives

$$
z\ge\beta-\operatorname{tr}(\chi\mathcal W_Z).
\tag{6.2}
$$

For stationary $\chi$, joint rotation averaging replaces $\mathcal W_Z$
by its twirl without changing that pairing. With the stated multipliers,
$\beta=1$ and this twirl is exactly $\mathcal W$ in (2.4).
Equation (2.10) is the decomposable representation $P_0+P_1^\Gamma$
with $P_0=P_1=P/2\ge0$.
Pair with the same PPT TP state and apply (2.17) to obtain
$z\ge1-4803/10000$.
Zero pair multipliers do not drop the pair constraints from the primal
problem or assert equality with a singleton subproblem.

The supplier stationary reduction preserves the whole complex class:
conjugating a rank-one Kraus family by actual-walk matrices preserves
rank and TP; recurrence makes time-shifted tail suprema equal to the
original error; convex averaging cannot increase this supremum.
Compactness of the TP separable Choi slice keeps the average admissible,
and the supplied finite support representation replaces it by at most
625 fixed flags. Stationarity then makes every event residual a conjugate
of its zero-wait residual. These are precisely the hypotheses and
conclusion of QPC Theorem 3.3, not independent local twirls or
rank-preserving character decompositions. The lower proof in Theorem 2.5
also avoids this reduction entirely.

Replacing separability in (6.1) by PPT or an outer extension condition
can only lower the minimum over $z$. Thus a verified dual point gives a
necessary bound, whereas a feasible relaxed state need not be a legal
scalar port. The extension and complex polynomial-witness frameworks of
[Doherty–Parrilo–Spedalieri](https://arxiv.org/html/quant-ph/0308032)
and
[Derksen–Johnston–Lovitz, *X-arability of mixed quantum states*, §§1.1–1.2, 4](https://arxiv.org/html/2409.18948)
apply with the product-vector Segre variety when the marginal and event
constraints are retained. The fixed-point and fixed-marginal setting of
[Koßmann–Zeiss, *Fixed points in de Finetti hierarchies*, §§4–5, 7.1](https://arxiv.org/html/2607.23689)
requires its own constraint correspondence: joint diagonal walk symmetry
here is not independent local fixed-point symmetry.
Exact-algebraic SDP methods such as
[Henrion–Naldi–Safey El Din, *Exact algorithms for semidefinite programs with degenerate feasible set*](https://arxiv.org/html/1802.02834)
concern spectrahedral optimization; the explicit determinant identities
in §§2 and 4 certify these particular points without asserting an optimum
of an SDP or of the separable problem. $\square$

**Definition 6.2 (Remaining exact-value and recovery questions).** The
unresolved scalar-port problem is to identify the minimum in (6.1) over
stationary separable TP Choi states, or equivalently the original
$\varepsilon_1$, and a matching legal port. The explicit feasible upper
and decomposable lower in (5.5) are different endpoints. Neither a
projector-orbit optimum, a PPT optimum, nor equality at $\xi$ is part
of (5.5). A stronger lower must bound all admissible independent complex
product factors jointly with their TP marginal and actual event residuals;
a sufficient improvement must be another single fixed legal port satisfying
all event inequalities at once. The scalar multiplier certificate and
changed joint moment (3.7) provide the two concrete relations used here.

Finite classical flags, algebraic coefficient descriptions and quantum
block dimension are separate from coefficient synthesis, finite precision,
preparation acquisition, clocks, storage duration and physical transport.
Those resources require additional hypotheses and bounds. The original
values for $q=2,3,4$, a native memory-rate theorem, a preparation bridge
from the native tree, and mutual recovery of space, time, boundary and
memory remain separate mathematical questions.

## 追加锚（本行以下为增补区）
