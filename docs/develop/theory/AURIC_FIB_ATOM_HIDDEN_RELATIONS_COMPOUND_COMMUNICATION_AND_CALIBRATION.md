# Auric FIB-ATOM: compound communication and calibration

This is the same-theme continuation of
[Mixed-state capacity and certification, §§108–115](AURIC_FIB_ATOM_HIDDEN_RELATIONS_MIXED_STATE_CAPACITY_AND_CERTIFICATION.md#115-原不可见-schur-族的无辅助量子容量与等谱全像).
It retains the original sources, coordinates and cut. The mathematical increment
is the placement of supplied calibration information and persistence of a source
label across uses. All proofs here are ordinary finite-dimensional mathematics
consuming the cited coding theorems. They have no exact Lean application or
kernel certification.

## 116. Original sources and three fixed-label communication tasks

**Definition C-116.1 (Coordinates, channel and source).**
Let $B=(0,1,2,3,13)$, $f=(0\ 13)(1\ 3)$ with $f(2)=2$.
In the original cut $A\mid B$, retain the fixed identifications
$Ve_j=|B_j\rangle_A$, $We_j=|f(B_j)\rangle_B$ and
$Je_j=|B_j,f(B_j)\rangle$, $0\le j\le4$.
These maps identify original labels; they are not a choice of a new observation
basis. Matrix units $E_{jk}$ below use these coefficient positions.
Retain precisely C-114.1's compact set

$$
\mathcal K=\{X=iR:R\in M_5(\mathbb R),\ R^T=-R,\ \|X\|_{\rm op}\le1\}.
$$

For known $0\le t,\eta\le1$, define, on the whole complex matrix algebra,

$$
\begin{aligned}
A_{t,X}&=I_5+tX,\qquad C_{t,X}=A_{t,X}/5,\\
\Phi_{t,\eta,X}(Y)&=(1-\eta)A_{t,X}\circ Y
                     +\eta\operatorname{tr}(Y)I_5/5,\qquad Y\in M_5(\mathbb C),\\
\rho_{t,\eta}(X)&=(1-\eta)JC_{t,X}J^\dagger+\eta I_{25}/25.
\end{aligned}
\tag{C116.1}
$$

Since $A_{t,X}\succeq0$ with diagonal one, the Schur term is CPTP.
The replacement term is CPTP, hence so is their convex mixture, including all
endpoints. No inverse or strict positivity is required.
With output first, the normalized Choi operator is

$$
\chi(\Phi)=\frac15\sum_{j,k=0}^4\Phi(E_{jk})\otimes E_{jk},\qquad
(V\otimes W)\chi(\Phi_{t,\eta,X})(V\otimes W)^\dagger
=\rho_{t,\eta}(X).
\tag{C116.2}
$$

Indeed the Schur contribution is $JC_{t,X}J^\dagger$, and the replacement
contribution is $I_5/5\otimes I_5/5$ on these original local supports.
The Choi trace is one and its partial trace over output is $I_5/5$.
Equation (C116.2) is a correspondence between an explicitly defined channel
and an original source. It supplies no common simulator programmed by one
unknown source state.

**Definition C-116.2 (A label fixed throughout a block).**
For a nonempty compact $U\subseteq\mathcal K$, one $X\in U$ is selected and
kept fixed throughout the entire block. Conditional on this same $X$, successive
environments are fresh, independent of each other and initially independent of
the input/reference. Thus the block map is $\Phi_{t,\eta,X}^{\otimes n}$,
including on correlated complex inputs. A distribution on $X$ is not assumed.
The known data $t,\eta,U$ may enter the code.

Let $k_n\ge1$, $L_n\cong R_n\cong\mathbb C^{k_n}$ and
$\beta_{k_n}=|\beta_{k_n}\rangle\langle\beta_{k_n}|$, where
$|\beta_k\rangle=k^{-1/2}\sum_{a=1}^k|a,a\rangle$.
Encoders and decoders are arbitrary complex CPTP maps

$$
\mathcal E_{n,X}:M_{k_n}\longrightarrow M_{5^n},\qquad
\mathcal D_{n,X}:M_{5^n}\longrightarrow M_{k_n}.
\tag{C116.3}
$$

There are three distinct tasks. In the common task neither map depends on $X$.
In the receiver-informed task only $\mathcal D_{n,X}$ may depend on the supplied
label. In the sender-informed task only $\mathcal E_{n,X}$ may depend on it;
the decoder is one common CPTP map. In each case reliability means

$$
\epsilon_n=\sup_{X\in U}
\left\| (\mathrm{id}_{R_n}\otimes
 \mathcal D_{n,X}\Phi_{t,\eta,X}^{\otimes n}\mathcal E_{n,X})
 (\beta_{k_n})-\beta_{k_n}\right\|_1\longrightarrow0,
\tag{C116.4}
$$

with the dependencies just specified. The norm is not divided by two.
Define $Q_{\rm com}(t,\eta;U)$, $Q_{\rm rec}(t,\eta;U)$ and
$Q_{\rm send}(t,\eta;U)$ as the suprema of achievable
$\liminf_n n^{-1}\log_2 k_n$ in these three tasks.
For a singleton use $Q(t,\eta;X)$.

Local blank ancillas and discarding are allowed. There is no preshared
entanglement or other initial correlation across sender and receiver, no quantum
bypass, free classical forward/feedback channel, hidden environment output,
postselection exception, or uncounted transmission. The reference is never acted
on. Supplying the label at one end is the additional information service being
compared. It is not a proof that the native menu can acquire that label, nor does
it itself communicate the label to the other end.
The channel uses and all block coding operations are additional mathematical
services, with the same resource exclusions as C-115.1.

**Literature input C-116.3 (Corrected compound coding supplier).**
We consume Bjelaković–Boche–Nötzel,
[*Entanglement transmission and generation under channel uncertainty: Universal
quantum channel coding*, arXiv:0811.4588v3](https://arxiv.org/html/0811.4588v3),
§§1.3, 2.1–2.4, Theorem 1, together with their
[erratum, DOI 10.1007/s00220-012-1609-6](https://doi.org/10.1007/s00220-012-1609-6),
Commun. Math. Phys. 317, 99–102.
For a set $\mathfrak I$ of CPTP maps between fixed finite-dimensional complex
input/output spaces, that theorem gives

$$
\begin{aligned}
Q_{\rm com}(\mathfrak I)=Q_{\rm rec}(\mathfrak I)
 &=\lim_{n\to\infty}\frac1n
   \max_{\sigma\in\mathcal S(\mathcal H^{\otimes n})}
   \inf_{N\in\mathfrak I} I_c(\sigma,N^{\otimes n}),\\
Q_{\rm send}(\mathfrak I)
 &=\lim_{n\to\infty}\frac1n
   \inf_{N\in\mathfrak I}
   \max_{\sigma\in\mathcal S(\mathcal H^{\otimes n})}
   I_c(\sigma,N^{\otimes n}).
\end{aligned}
\tag{C116.5}
$$

Here $I_c(\sigma,N)=S_2(N(\sigma))-S_2((\mathrm{id}\otimes N)(\psi_\sigma))$
for any purification, equivalently output entropy minus complementary entropy.
These are operational coding theorems, not definitions of capacity by entropy.
Their maxima range over every complex density matrix, not a real or product
subdomain. No generic coding framework is reproved here.

The erratum corrects the missing square root in its Lemma 3 and the subsequent
finite-channel/net error estimates on printed pp.70–86. It also replaces Lemma 14
by an Alicki–Fannes conditional-entropy bound independent of the decoder output
dimension, and adjusts the converse estimates on pp.87–89 and 93. These are
corrections of the proofs and estimates; the listed corrections do not replace
Theorem 1's capacity formulas. Only the corrected asymptotic theorem is consumed;
no original projection/error constant is used.

All its hypotheses hold here: input and output are both $\mathbb C^5$; (C116.1)
is CPTP on the whole algebra; conditional uses are tensor powers of one channel;
and encoders/decoders and information dependencies agree with §§2.1–2.3.
The supplier permits the logical output space to be enlarged, $L_n\subseteq L_n'$.
This does not enlarge our rates. Compress to $L_n$ by the CPTP map

$$
Z\longmapsto PZP+\operatorname{tr}((I-P)Z)\tau,
\tag{C116.6}
$$

where $P$ projects onto $L_n$ and $\tau$ is a fixed state there. It fixes the
embedded target; its adjoint sends that target test to the target plus a positive
operator. Consequently target fidelity cannot decrease. Conversely our output
space is already an allowed special case.
For the pure normalized target, with $F=\langle\beta_k,\omega\beta_k\rangle$,

$$
2(1-F)\le\|\omega-\beta_k\|_1\le2\sqrt{1-F}.
\tag{C116.7}
$$

The first inequality is the two-outcome target measurement; the second is the
pure-target fidelity/trace inequality. Both are independent of $k$, so taking
suprema/infima proves exactly the uniform convergence equivalence needed in
(C116.4), including enlarged-output codes followed by (C116.6).

## 117. Common populations and a strict calibration-placement gap

**Theorem C-117.1 (Source-specific compact-set reduction at zero noise).**
For every nonempty compact $U\subseteq\mathcal K$ and $0\le t\le1$, retain the
closed simplex $\Delta_5=\{p_j\ge0:\sum_jp_j=1\}$ and C-115.2's function

$$
F_{t,X}(p)=H_2(p)-S_2\bigl(\sqrt{D_p}(I_5+tX)\sqrt{D_p}\bigr).
$$

Then

$$
\begin{aligned}
Q_{\rm com}(t,0;U)=Q_{\rm rec}(t,0;U)
 &=\max_{p\in\Delta_5}\min_{X\in U}F_{t,X}(p),\\
Q_{\rm send}(t,0;U)
 &=\min_{X\in U}\max_{p\in\Delta_5}F_{t,X}(p).
\end{aligned}
\tag{C117.1}
$$

In particular the first line requires one common population vector before the
unknown label is selected. No interchange of max and min is asserted.
All extrema exist. Zero populations, $t=0,1$, singular $I_5+tX$, and arbitrary
complex correlations across all channel uses are included.

Proof. Consume C-115.2, including its actual Stinespring extension
$U_Xe_j=e_j\otimes\sqrt{\overline{I_5+tX}}e_j$ and its CPTP degrading map
$\mathcal L_X(Z)=\sum_j Z_{jj}|v_{X,j}\rangle\langle v_{X,j}|$.
For any block density matrix $\sigma$, let $p^{(r)}$ be its $r$th marginal
population and $\bar p=n^{-1}\sum_rp^{(r)}$. The total-correlation data-processing
step in (C115.7), followed by concavity of $F_{t,X}$, gives for every same $X$

$$
I_c(\sigma,\Phi_{t,0,X}^{\otimes n})
 \le\sum_{r=1}^nF_{t,X}(p^{(r)})
 \le nF_{t,X}(\bar p).
\tag{C117.2}
$$

The vector $\bar p$ depends only on $\sigma$, not on $X$. Hence taking the
infimum in this inequality gives an upper bound by
$n\max_p\min_XF_{t,X}(p)$. Conversely, a product of the same diagonal input
$D_p$ has coherent information exactly $nF_{t,X}(p)$ simultaneously for all $X$.
Maximizing the common $p$ proves equality of the regularized common expression
in (C116.5) with the first line of (C117.1), for every block length already.
For the sender-informed expression, C-115.2 gives
$\max_\sigma I_c(\sigma,\Phi_{t,0,X}^{\otimes n})=n\max_pF_{t,X}(p)$
for each $X$ before taking the infimum. This gives the second line.
The operational conclusions now follow from the corrected supplier, not from
an entropy definition or a numerical optimizer.

C-115.2 gives joint continuity on the compact domain and concavity in $p$.
Uniform continuity implies continuity of $p\mapsto\min_XF_{t,X}(p)$ and
$X\mapsto\max_pF_{t,X}(p)$, which proves attainment. No division by a population
or inverse of a Gram matrix occurs, so the same argument includes the boundary.
The extensions and data processing act on whole complex matrix algebras; no
restriction to diagonal block inputs was made in the upper bound. QED.

**Definition C-117.2 (The same four actual sources).**
Take the following particular subset, without changing $B,f,J$ or the cut:

$$
\begin{aligned}
X_{a,+}&=i(E_{04}-E_{40}),&X_{a,-}&=-X_{a,+},\\
X_{b,+}&=i(E_{13}-E_{31}),&X_{b,-}&=-X_{b,+},\\
U_4&=\{X_{a,+},X_{a,-},X_{b,+},X_{b,-}\}\subset\mathcal K.
\end{aligned}
\tag{C117.3}
$$

They have operator norm one, spectrum $\{1,0,0,0,-1\}$ and coefficient
populations $1/5$. The pairs are positions $(0,4)$ and $(1,3)$, namely original
labels $(0,13)$ and $(1,3)$. Signs change the imaginary coherence on the actual
pair. Each source belongs to C-108.3's same complete native-history fiber.
For any fixed $t,\eta$, all four source/Choi spectra, with multiplicities, are

$$
\left\{a+b,\ a-b,\ a^{[3]},\ c^{[20]}\right\},\qquad
 a=(1-\eta)/5+\eta/25,\quad b=(1-\eta)t/5,\quad c=\eta/25.
\tag{C117.4}
$$

Coincident eigenvalues and zeros are counted with their stated multiplicities.
Native-history equality follows from the inherited observation theorem and
linearity under the same white-noise mixing, not from isospectrality alone.

**Theorem C-117.3 (Placement, rather than individual capacity or spectrum).**
Put $g(t)=1-h_2((1+t)/2)$, with base-two binary entropy and $0\log_20=0$.
For all $0\le t\le1$,

$$
\begin{aligned}
Q(t,0;X)&=g(t) &&(X\in U_4),\\
Q_{\rm com}(t,0;U_4)=Q_{\rm rec}(t,0;U_4)&=g(t)/2,\\
Q_{\rm send}(t,0;U_4)&=g(t).
\end{aligned}
\tag{C117.5}
$$

Moreover the individual exact whole-input one-use port dimension in C-114.1's
finite-flag CPTP contract is

$$
q_{\rm exact}(\Phi_{t,0,X})=
\begin{cases}1,&t=0,\\2,&0<t\le1,\end{cases}\qquad X\in U_4.
\tag{C117.6}
$$

Thus the positive placement gap is compatible with equal individual capacities,
equal native histories, equal source spectra and equal individual exact ports.
Equation (C117.6) asserts no common unknown-source simulator.

Proof. If the active pair is $(j,k)$, put $s=p_j+p_k$. At $s>0$ put $r=p_j/s$.
The only nondiagonal block of the Gram state in $F$ has eigenvalues

$$
\frac{s}{2}(1\pm d),\qquad
 d=\sqrt{(2r-1)^2+4t^2r(1-r)}.
$$

The three other eigenvalues are the other populations, including their zeros.
Splitting the entropy by the pair and its complement cancels every other
population and the pair mass term, leaving

$$
F_{t,X}(p)=s\left[h_2(r)-h_2((1+d)/2)\right].
\tag{C117.7}
$$

At $s=0$ the value is zero, its continuous limit. Sign does not affect this
spectrum. For fixed $s$, the expression is concave in $r$ by C-115.2 and invariant
under $r\mapsto1-r$ (exchange the two populations). Averaging these two points
bounds it by its value at $r=1/2$, namely $s g(t)$, with equality at balance.
Therefore the individual maximum is $g(t)$, obtained by putting mass $1/2$ on
each endpoint of the active pair. This consumes C-115.2's calibrated capacity
result; it does not reprove its coding theorem.

For a single common vector write $s_a=p_0+p_4$, $s_b=p_1+p_3$.
Their sum is $1-p_2\le1$. Consequently

$$
\min_{X\in U_4}F_{t,X}(p)
 \le g(t)\min(s_a,s_b)\le g(t)/2.
$$

The actual vector $p_*=(1/4,1/4,0,1/4,1/4)$ attains $g(t)/2$ for all four
labels at once, including $t=0,1$. The first line of (C117.1) yields the two
uninformed-encoder capacities. The second line yields $g(t)$ for the
sender-informed task, since each individual maximum is $g(t)$.
At $t=0$ all channels are the original-basis complete dephasing map and all
rates vanish. At $t=1$ the individual and common values are respectively one
and one half. No strict-positivity assumption was used.

For ports, the normalized Choi state at zero noise is maximally correlated.
Its active $2\times2$ block has eigenvectors supported on only $|j,j\rangle$ and
$|k,k\rangle$; the other three contributions are product projectors. Its spectral
decomposition therefore has Schmidt ranks at most two, including a vanished
active eigenvalue at $t=1$. When $t>0$, partial transpose has on
$\operatorname{span}\{|j,k\rangle,|k,j\rangle\}$ the eigenvalues $\pm t/5$.
It is entangled, so Schmidt number is at least two. C-113.3/C-114.1's exact
whole-algebra finite-flag Choi/Schmidt-number equivalence gives (C117.6).
At $t=0$ the Choi state is the sum of five product projectors, giving one.
This port argument uses the source itself, independently of coding capacity. QED.

**Remark C-117.4 (Information is supplied, and any header is paid for).**
The sender-informed encoder may choose a different population for each active
pair because its label is supplied before encoding. Receiver information cannot
change the common encoder population. That is the operational distinction in
(C117.5); a native history does not perform this calibration.
For the finite set there is also an explicit way to make a single receiver
implementation from four individually calibrated codes. For $\eta<1$, encode
each of the two label bits by $m$ repetitions of $E_{00}$ or $E_{11}$ on the same
channel. The probability of the measured output label zero is respectively
$1-\eta+\eta/5$ or $\eta/5$, independent of $t$ and $X$.
A midpoint threshold on that empirical frequency has bit error at most
$\exp[-m(1-\eta)^2/2]$ by the Bernoulli Hoeffding bound.
Take $m\to\infty$ with $m/n\to0$, then apply the label-selected data decoder.
The header costs $2m$ actual uses and carries no message/reference correlation.
Its measurement and controlled decoding form one common CPTP decoder; the
extra trace error is at most twice the header failure probability. Conditional
independence of fresh environments permits the header and data errors to be
combined. At $\eta=0$ the two bits can instead be sent exactly in two uses.
This description illustrates the resource accounting in the supplier; no free
sender-to-receiver communication is being introduced.

## 118. Original positive white noise: rates with complete reference spectra

**Theorem C-118.1 (Useful bounds without a noisy degradability claim).**
For all $0\le t,\eta\le1$ and the same $U_4$, define entropy of a probability
list by $H(v)=-\sum_i v_i\log_2v_i$, with all multiplicities retained, and set

$$
\begin{aligned}
u_\pm&=(1-\eta)(1\pm t)/2+\eta/10,\\
v_\pm&=(1-\eta)(1\pm t)/4+\eta/20,\qquad
v_0=(1-\eta)/4+\eta/20,\\
L_s(t,\eta)&=H\left(((1-\eta)/2+\eta/5)^{[2]},(\eta/5)^{[3]}\right)
             -H\left(u_+,u_-,(\eta/10)^{[8]}\right),\\
L_c(t,\eta)&=H\left(((1-\eta)/4+\eta/5)^{[4]},\eta/5\right)
             -H\left(v_+,v_-,v_0^{[2]},(\eta/20)^{[16]}\right).
\end{aligned}
\tag{C118.1}
$$

The resulting rate bounds are

$$
\begin{aligned}
\max\{0,L_c(t,\eta)\}&\le Q_{\rm com}(t,\eta;U_4)
 =Q_{\rm rec}(t,\eta;U_4)\le g(t)/2,\\
\max\{0,L_s(t,\eta)\}&\le Q_{\rm send}(t,\eta;U_4)\le g(t),\\
\max\{0,L_s(t,\eta)\}&\le Q(t,\eta;X)\le g(t)\qquad(X\in U_4).
\end{aligned}
\tag{C118.2}
$$

In particular $L_s(t,0)=g(t)$ and $L_c(t,0)=g(t)/2$.
At $t=0$ or $\eta=1$ all three capacities and individual capacities are zero.
For $\eta>0$ the displayed entropy differences are achievable bounds, not
assertions of exact capacity or degradability.

Proof. Use the balanced rank-two input on a label's active pair and its actual
purification in $\mathbb C^2_R\otimes\mathbb C^5$.
The five output eigenvalues are the first list in $L_s$.
On the full ten-dimensional reference/output space the ideal output has the two
eigenvalues $(1\pm t)/2$ and eight zeros. The noisy output is

$$
(1-\eta)\omega_0+\eta(I_2/2\otimes I_5/5),
\tag{C118.3}
$$

so its full spectrum is exactly the second list in $L_s$.
Imaginary off-diagonal entries are retained: the active coherence is
$\pm it/2$, not its real part. Its sign disappears only after computing the
Hermitian eigenvalues. No projection onto a successful output pair is made;
the other three output labels are retained in the first entropy.

For the same common input $D_{p_*}$ use a purification with four-dimensional
reference. In the original matching subspace the ideal reference/output
operator has one active pair with eigenvalues $(1\pm t)/4$ and two singleton
eigenvalues $1/4$. Its full dimension is twenty, with sixteen additional zeros.
The replacement branch is $I_4/4\otimes I_5/5$; adding it gives precisely
$v_+,v_-,v_0^{[2]},(\eta/20)^{[16]}$.
The output is the full five-dimensional probability list in $L_c$.
All four labels have these same two entropy values, and the common input is
identical for them. Using a five-dimensional reference would add exactly five
zero eigenvalues; it would not change either entropy or discard any state.
These calculations are purified coherent information, not an entropy of the
source state substituted for channel coherent information.

The $n$th tensor power of this common input has coherent information $nL_c$
for every same fixed label. Inserting it into the common expression of (C116.5)
yields the first lower bound. For the informed-encoder expression, each label
has its own balanced active-pair input with value $nL_s$ before the infimum is
taken. This gives the sender lower bound. The singleton coding theorem reused
in C-115.2 gives the individual lower bound. Rate zero is always achievable.
None of these lower bounds assumes single-letterization of the noisy channels.

For upper bounds write the actual noisy map as output postprocessing of the
zero-noise map:

$$
\Phi_{t,\eta,X}=\mathcal R_\eta\Phi_{t,0,X},\qquad
\mathcal R_\eta(Z)=(1-\eta)Z+\eta\operatorname{tr}(Z)I_5/5.
\tag{C118.4}
$$

Every noisy code can be run on the ideal channels by putting
$\mathcal R_\eta^{\otimes n}$ into its decoder. This is the same postprocessing
for all labels and respects each information-placement restriction. Therefore
each capacity is no greater than its corresponding value in (C117.5).
If $t=0$, the map measures the original basis and prepares a noisy basis state;
it is entanglement breaking. At $\eta=1$ it is replacement. Tensor powers and
local CPTP encoding/decoding preserve separability across the unchanged
reference, giving zero capacity (also by the target test in C-119.1 below).
Every entropy list remains normalized at these endpoints, including its zero
and repeated eigenvalues. QED.

**Corollary C-118.2 (An actual positive-noise calibration advantage).**
Put $g=g(t)$. For $t>0$, the following explicitly specified parameter set is
nonempty and contains an interval $(0,\eta_t)$ at each fixed $t$:

$$
0<\eta<1,\qquad h_2(\eta)+\eta(2+g/2)<g/2.
\tag{C118.5}
$$

Throughout it,

$$
0<Q_{\rm com}=Q_{\rm rec}\le g/2
 <Q_{\rm send},\qquad Q(t,\eta;X)>g/2\quad(X\in U_4).
\tag{C118.6}
$$

In particular, a concrete closed range of positive noise is

$$
t=1,\qquad 0<\eta\le1/64:
\quad Q_{\rm com}>1/4,\quad
 Q_{\rm com}=Q_{\rm rec}\le1/2<3/4<Q_{\rm send}.
\tag{C118.7}
$$

Proof. The standard entropy-of-mixture bounds
$\sum_iw_iS(\omega_i)\le S(\sum_iw_i\omega_i)
\le H(w)+\sum_iw_iS(\omega_i)$ applied separately to output and full
reference/output state give, for the balanced rank-$r$ input,

$$
I_c(\sigma,\Phi_{t,\eta,X})
 \ge(1-\eta)I_c(\sigma,\Phi_{t,0,X})-\eta\log_2r-h_2(\eta).
\tag{C118.8}
$$

Indeed the noise-only output entropy is $\log_25$ and its reference/output
entropy is $\log_2r+\log_25$. Use the lower mixture inequality on the first
entropy and the upper one on the second. Thus

$$
L_s\ge(1-\eta)g-\eta-h_2(\eta),\qquad
L_c\ge(1-\eta)g/2-2\eta-h_2(\eta).
\tag{C118.9}
$$

Condition (C118.5) makes the second quantity positive. It also makes the first
strictly greater than $g/2$, since $g+1\le2+g/2$ for $0\le g\le1$.
The capacities therefore satisfy (C118.6) by (C118.2).
For each $t>0$, $g(t)>0$ while the left side of (C118.5) tends to zero as
$\eta\downarrow0$, proving the claimed nonempty interval with the original
noise, not a flagged-erasure replacement model.

For a purely analytic concrete bound, $h_2$ is increasing on $[0,1/2]$ and
$-(1-x)\log_2(1-x)\le x\log_2 e$. Hence
$h_2(\eta)\le h_2(1/64)\le(6+\log_2e)/64<8/64$ for $0<\eta\le1/64$.
At $g(1)=1$, (C118.9) yields
$L_s>1-10/64>3/4$ and
$L_c>1/2-(5/2+8)/64=43/128>1/4$.
This proves the whole range (C118.7) without a numerical capacity estimate. QED.

No individual noisy exact-port value is inferred from these rates. In
particular, neither the ideal rank-two argument nor positivity of a rate is a
proof of a positive-noise Schmidt-number threshold.

## 119. Varying labels on the same source set and a finite obstruction

**Theorem C-119.1 (Per-use label variation has zero uniform rate).**
Define a separate task on exactly $U_4$: for each $n$, any sequence
$(X_1,\ldots,X_n)\in U_4^n$ is permitted and the channel is
$\Phi_{t,\eta,X_1}\otimes\cdots\otimes\Phi_{t,\eta,X_n}$, with fresh independent
environments conditional on that sequence. Neither party receives the sequence.
One common encoder and one common decoder must satisfy (C116.4) with the
supremum now over $U_4^n$. All other complex CPTP block/reference/resource
contracts stay exactly the same. For every $n$, every logical dimension $k$,
and every such pair of CPTP maps,

$$
\sup_{(X_1,\ldots,X_n)\in U_4^n}
\left\|(\mathrm{id}_{R}\otimes\mathcal D
 [\bigotimes_{r=1}^n\Phi_{t,\eta,X_r}]\mathcal E)(\beta_k)
 -\beta_k\right\|_1
\ge2(1-1/k).
\tag{C119.1}
$$

This holds for all $0\le t,\eta\le1$. In particular its uniformly reliable
capacity is zero, and even logical dimension two has an error floor of one.

Proof. Averaging the four actual single-use maps cancels their opposite
imaginary coherences, giving on the whole complex algebra

$$
\overline\Phi(Y)=\frac14\sum_{X\in U_4}\Phi_{t,\eta,X}(Y)
 =(1-\eta)\sum_jY_{jj}E_{jj}+\eta\operatorname{tr}(Y)I_5/5.
\tag{C119.2}
$$

It is a measure-and-prepare channel, hence entanglement breaking.
The uniform independent average over the $4^n$ permitted sequences is exactly
$\overline\Phi^{\otimes n}$. This is entanglement breaking even on an arbitrary
complex input entangled across all uses and with $R$: it measures a full basis
string and prepares a product output conditioned on that string. Applying an
arbitrary CPTP encoder first cannot prevent this reference/output separability;
applying the local decoder afterwards preserves it. Denote the resulting
separable $R\mid L$ state by $\bar\omega$.

For normalized product vectors $u,v\in\mathbb C^k$,
$|\langle\beta_k|u\otimes v\rangle|^2
 =|\sum_a u_av_a|^2/k\le1/k$ by Cauchy–Schwarz.
Convexity gives $\langle\beta_k|\bar\omega|\beta_k\rangle\le1/k$ for every
separable mixed state. The two-outcome test $\{\beta_k,I-\beta_k\}$ gives
$\|\bar\omega-\beta_k\|_1\ge2(1-1/k)$.
Linearity of the tensor channel and of the fixed encoder/decoder makes
$\bar\omega$ the arithmetic mean of the actual sequence outputs. The norm of
a mean is at most the largest norm, proving (C119.1). This is a finite
reference-error obstruction for the entire code class, not a product-code or
real-state converse. If errors tend to zero, $k_n\ge2$ cannot occur infinitely
often, so the rate is zero. QED.

**Proposition C-119.2 (Fixed-label and per-use averages differ).**
The common fixed-label task in C-116.2 cannot be replaced by the convexified
single-use family. At $\eta=0$, $t>0$, already at two uses

$$
\begin{aligned}
\frac14\sum_{X\in U_4}\Phi_{t,0,X}^{\otimes2}(E_{04}\otimes E_{04})
 &=-\frac{t^2}{2}E_{04}\otimes E_{04},\\
\overline\Phi^{\otimes2}(E_{04}\otimes E_{04})&=0.
\end{aligned}
\tag{C119.3}
$$

Proof. The two $a$ labels multiply $E_{04}$ by $\pm it$; the two $b$ labels
annihilate it. Squaring before averaging gives $(-t^2-t^2)/4$.
Averaging before tensoring instead gives zero. The block-fixed mixture at zero
noise is itself a Schur channel on dimension 25. The displayed nonzero
coherence produces a negative eigenvalue in its maximally correlated Choi
partial transpose, so this block mixture is not entanglement breaking.
Thus even its entanglement-breaking status differs from that of the per-use
average. The first task keeps the same unknown label, the second permits every
sequence. Opposite-label cancellation is a valid converse for the second;
convexifying the first would contradict (C117.5). QED.

## 120. Consumed relations, native boundaries and evidence ceiling

**Scope C-120.1 (What is and is not transferred from current mathematics).**
The original-source relation proved here is an operational one: two disjoint
coherence locations compete for the same input population before an unknown
persistent label is revealed. Sender information changes the available
population choice; receiver information does not. Permitting the label to vary
at every use removes that persistence and admits the finite obstruction above.
These conclusions use (C116.1)–(C116.4), not an assumed ability to access quantum
phases through the native observation interface.

The actual carriers of the related results have different domains:

- [Acquisition Resources XVI, Definitions 273.1–273.3](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md#273-complete-allocations-original-objects-and-signed-coordinates)
  uses Boolean prime-divisibility replies, one finite conic allocation and signed
  event-score coordinates. Its $M=1$ kernels are classical probability laws.
  It supplies no original $M_5(\mathbb C)$ quantum preparation or phase label.
- `InterleavedWordRecovery.interleaved_word_recovery` in
  `D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/InterleavedWordRecovery.lean`
  recovers a promised original Boolean vector encoded into a `Source` tree,
  using address/depth hypotheses and a native serial program. A decoded Boolean
  word is not a calibration of the four density operators in (C117.3).
- [Native critical-cutoff spectral limits, Definition 31.1 and Theorem 32.1](FIB_NATIVE_CRITICAL_CUTOFF_SPECTRAL_LIMITS.md#31-the-original-critical-families-and-scalar-comparison)
  uses Dirichlet scalar operators, raw measures and native diffusion clocks.
  Its $L^2$ eigenfunctions/heat kernels are not the normalized output-first Choi
  states or coding operations here. No finite-dimensional CPTP or resource
  bridge from that carrier is assumed.

The common-allocation theme is a useful comparison, but no theorem from these
carriers is used to infer a quantum calibration service. A bridge would have to
supply actual states, permissible controls and the same uniform reference-error
contract; matching names, spectra or budget inequalities do not provide it.

For the full $\mathcal K$, $X_0=0$ gives complete dephasing at $\eta=0$ and a
measure-and-prepare mixture at every $\eta$. Its individual capacity is zero.
Consequently all three fixed-label guaranteed rates over the full $\mathcal K$
are zero. This is only a scope boundary; it does not replace the nontrivial
four-source calculation by a larger family containing a zero-capacity member.

**Literature status C-120.2 (Suppliers and new synthesis).**
The mature coding ingredients are `literature-attested`: C-116.3's corrected
compound theorem and the Devetak–Shor supplier already consumed in C-115.2,
[*The capacity of a quantum channel for simultaneous transmission of classical
and quantum information*, quant-ph/0311131v3](https://arxiv.org/html/quant-ph/0311131v3),
§§1–2 and Appendix B, especially its generalized-dephasing discussion and
single-letter formula (18). C-115.2's exact source-specific Gram function,
concavity, degradation and complex block bound are reused rather than reproved.
The entropy-of-mixture inequalities and the pure-target fidelity/trace
inequalities are standard finite-dimensional tools; the Hoeffding bound only
illustrates the optional paid header and is not needed for (C117.5).

The compact-$U$ common-population reduction, evaluation on the actual four
original matrices, complete noisy reference spectra and rate separation, and
same-set varying-label obstruction are `repo-derived` synthesis in this volume.
They are not claims of literature novelty or new generic coding theorems.
The ordinary proofs above consume the explicitly cited mathematical suppliers;
no formal-grade conclusion or exact Lean capacity certificate is asserted.

The noisy capacity values outside the bounds (C118.2) remain undetermined here;
no noisy degradability or exact-port threshold is concluded. Native acquisition,
a physical implementation of the extra channel/coding services, and a common
unknown-source simulator also remain outside these results.

## 追加锚（本行以下为增补区）
