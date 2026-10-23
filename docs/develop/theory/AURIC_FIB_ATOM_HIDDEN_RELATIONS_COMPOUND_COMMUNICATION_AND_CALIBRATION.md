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

## 121. Actual original-source copies as programs on the whole complex algebra

**Definition C-121.1 (Prescribed programs and access services).**
Retain (C116.1)–(C116.2), in particular $B=(0,1,2,3,13)$,
$f=(0\ 13)(1\ 3)$, $f(2)=2$, $Je_j=|B_j,f(B_j)\rangle$, the original
$A\mid B$ cut and the normalized output-first Choi operator. Put

$$
X_a=i(E_{04}-E_{40}),\quad X_b=i(E_{13}-E_{31}),\quad
U_4=\{X_a,-X_a,X_b,-X_b\}.
\tag{C121.1}
$$

One unknown $X\in U_4$ is fixed. The known parameters are $t,\eta\in[0,1]$.
A batch of size $m\in\mathbb N_0$ consists of the actual state
$\rho_{t,\eta}(X)^{\otimes m}$ on $P_m=(\mathbb C^5\otimes\mathbb C^5)^{\otimes m}$,
conditionally independent across copies and initially independent of every data
system and external reference. For $m=0$ the program space is $\mathbb C$.
No classical source name, selected eigenstate or freely chosen program replaces
this batch. There is no distributional assumption on $X$.

A processor is one complex CPTP map
$\mathcal P_m:M_{5\cdot25^m}\to M_5$, with data first, independent of $X$.
It must be defined on the entire joint matrix algebra, including program inputs
outside the promised family and inputs correlated with the data. Its induced
channel on the promised batch is

$$
N_X(Y)=\mathcal P_m\bigl(Y\otimes\rho_{t,\eta}(X)^{\otimes m}\bigr),\qquad
 e_m(t,\eta)=\inf_{\mathcal P_m\ {\rm CPTP}}\max_{X\in U_4}
 \|N_X-\Phi_{t,\eta,X}\|_\diamond.
\tag{C121.2}
$$

Diamond error is unhalved and stabilizes over all finite complex references.
The reference is untouched. Only the stated product program/data inputs are
used to evaluate (C121.2); whole-algebra validity of the processor is a stronger
requirement on its definition.

The batch supply, joint measurement below, calibrated local channel controls,
blank ancillas, discarding and any spatial routing are additional mathematical
services. Their counts are given in C-124. They are not consequences of the
native local menu in C-108.1. Mathematical access to a density operator,
physical preparation of it, and native acquisition are distinct assertions.
In particular, exact known real control amplitudes and a phase reference for
$i$ must be supplied; a finite classical code naming them is not their exact
physical preparation or calibration.

**Proposition C-121.2 (The exact commuting experiment supplied by those copies).**
Set

$$
\begin{aligned}
 c&=(1-\eta)t,& w&=(1-\eta)/5+\eta/25=(5-4\eta)/25,\\
 u&=c/5,& s&=5w=1-4\eta/5,&
 \gamma&=s-c=(1-\eta)(1-t)+\eta/5.
\end{aligned}
\tag{C121.3}
$$

The symbols $c,w,u$ in this increment have the meanings (C121.3); they do not
redefine C-114.1's local symbols. Define five orthonormal vectors on the original
matching subspace and one complementary projection by

$$
|a_\epsilon\rangle=J(e_0-i\epsilon e_4)/\sqrt2,\qquad
|b_\epsilon\rangle=J(e_1-i\epsilon e_3)/\sqrt2\quad(\epsilon=\pm1),\qquad
|o\rangle=Je_2,\qquad Q=I_{25}-JJ^\dagger.
\tag{C121.4}
$$

Measure the six projections onto these five vectors and $Q$, denoting the
outcomes by $a_+,a_-,b_+,b_-,o,*$. For $X=\sigma X_a$, $\sigma=\pm1$,
the law in this order is

$$
p_{a,\sigma}=(w+\sigma u,w-\sigma u,w,w,w,20\eta/25);
\tag{C121.5}
$$

$p_{b,\sigma}$ interchanges the two $a$ entries with the two $b$ entries.
The measurement is fixed and label independent. All four source states commute.
For their tensor powers, this classical experiment loses no trace distance.
In particular, define

$$
\begin{aligned}
D_m(t,\eta)&=\tfrac12\|
 \rho_{t,\eta}(X_a)^{\otimes m}-\rho_{t,\eta}(-X_a)^{\otimes m}\|_1\\
&=\frac12\sum_{r+q+k=m}\frac{m!}{r!q!k!}(1-2w)^k
 \left|(w+u)^r(w-u)^q-(w-u)^r(w+u)^q\right|.
\end{aligned}
\tag{C121.6}
$$

The sum is finite, includes $m=0$, and uses $0^0=1$. The opposite-$b$ quantity
is the same. Thus (C121.6) is an explicit source-copy resource quantity, with no
optimization over hypothetical programs.

Proof. $X_a(e_0-i\epsilon e_4)=\epsilon(e_0-i\epsilon e_4)$,
and similarly for $b$. The two matrices act on disjoint pairs, so the five
vectors diagonalize every matching contribution at once. The complementary
contribution is the same scalar $\eta/25$ on all twenty orthogonal modes.
This proves (C121.5) and simultaneous diagonalization. The trace norm of a
Hermitian diagonal matrix is the sum of the absolute values of its entries;
tensoring preserves this common eigenbasis. Within the $*$ outcome all twenty
conditional probabilities coincide for all labels, so grouping them changes
no trace distance. For the opposite-$a$ comparison every outcome other than
$a_+,a_-$ has the same probability under both hypotheses. Group those outcomes
into total mass $1-2w$, and count the two distinguished outcomes as $r,q$.
The multinomial expansion gives (C121.6), including all zero probabilities.
The empty products at $m=0$ agree, so $D_0=0$. QED.

**Proposition C-121.3 (Admissible response channels, exact norm and one processor).**
For any real $v_a,v_b$ with $|v_a|,|v_b|\le s$, define on all $M_5(\mathbb C)$

$$
T_\eta(v_a,v_b)(Y)=(1-\eta)\sum_jY_{jj}E_{jj}
 +\eta\operatorname{tr}(Y)I_5/5
 +v_a(X_a\circ Y)+v_b(X_b\circ Y).
\tag{C121.7}
$$

These maps are CPTP, with the same diagonal action as the target. Moreover

$$
\|T_\eta(v_a,v_b)-T_\eta(v'_a,v'_b)\|_\diamond
 =\max\{|v_a-v'_a|,|v_b-v'_b|\}.
\tag{C121.8}
$$

For a length-$m$ outcome string $z$, let
$h_a(z)=\operatorname{sgn}(n_{a_+}(z)-n_{a_-}(z))$ and define $h_b$ similarly,
with $\operatorname{sgn}(0)=0$. Put $D=D_m(t,\eta)$ and

$$
 r_m=\begin{cases}\min\{s,c/D\},&D>0,\\0,&D=0.\end{cases}
\qquad T_z=T_\eta(r_mh_a(z),r_mh_b(z)).
\tag{C121.9}
$$

Let $M_z$ be the product of the six-outcome projections in (C121.4). The formula

$$
\mathcal P_m(\Omega)=\sum_z T_z\left(
 \operatorname{tr}_{P_m}\bigl[(I_5\otimes M_z)\Omega(I_5\otimes M_z)\bigr]
 \right)
\tag{C121.10}
$$

defines one label-independent CPTP processor on the whole joint algebra.
It has, for every label, the exact error

$$
\max_{X\in U_4}\|N_X-\Phi_{t,\eta,X}\|_\diamond
 =[c-sD_m(t,\eta)]_+,
\qquad [x]_+=\max\{0,x\}.
\tag{C121.11}
$$

Proof. The normalized output-first Choi matrix of $T_\eta(v_a,v_b)$ has, on the
matching subspace, diagonal $w=s/5$ and the two imaginary off-diagonal pairs
$v_aX_a/5$, $v_bX_b/5$. Its two block eigenvalue pairs are
$(s\pm v_a)/5$, $(s\pm v_b)/5$; the singleton eigenvalue is $s/5$.
On the twenty unmatched modes it is $\eta/25$. They are nonnegative and sum
to one. Tracing over output gives $I_5/5$: every off-diagonal pair has different
input and output indices, and each input's diagonal sum is
$s/5+4\eta/25=1/5$. Choi's CP criterion and this marginal give CPTP.
This is the original output-first normalization, not an input transpose.

For (C121.8), pinch the data into the orthogonal sectors $\{0,4\}$,
$\{1,3\}$ and $\{2\}$. The difference vanishes on cross-sector entries and
on sector diagonals. On a two-dimensional sector, the off-diagonal extraction
is $(Y-ZYZ)/2$, where $Z=\operatorname{diag}(1,-1)$; hence it is a contraction
in trace norm even after tensoring with any identity. Multiplication of its
$jk,kj$ entries by $i,-i$ is unitary conjugation on that off-diagonal space.
For any reference/data state the two pinched sector blocks are positive, with
traces summing to at most one. Their contributions therefore have total trace
norm at most $\max(|v_a-v'_a|,|v_b-v'_b|)$. A balanced pure input on the pair
with the larger coefficient gives an off-diagonal Hermitian output with
trace norm equal to that coefficient. This proves the equality with every
finite complex reference included.

The instrument in (C121.10), partial trace and each response channel are CP;
$\sum_zM_z=I$ and trace preservation of the responses give TP on every input.
At $m=0$ there is one empty string, $h_a=h_b=0$ and $T_z=T_\eta(0,0)$.
No assumption about an unpromised program is required for this validity.

For $u>0$, the sign of
$p_{a,+}^{\otimes m}(z)-p_{a,-}^{\otimes m}(z)$, wherever it is nonzero,
is $h_a(z)$. This follows by comparing the powers of $w+u$ and $w-u$;
if $w-u=0$, the same conclusion holds on either nonzero support and the other
strings contribute zero. Swapping $a_+,a_-$ exchanges these two laws and
negates $h_a$. Therefore

$$
\mathbb E_{a,\sigma}h_a=\sigma D,\quad
\mathbb E_{a,\sigma}h_b=0,\quad
\mathbb E_{b,\sigma}h_b=\sigma D,\quad
\mathbb E_{b,\sigma}h_a=0.
\tag{C121.12}
$$

The zero expectations use the swap of the inactive pair, which leaves the
actual source law fixed. If $u=0$, all laws coincide and each sign has zero
expectation by the same symmetry. Since (C121.7) is affine in its coefficients,
$N_{\sigma X_a}=T_\eta(\sigma r_mD,0)$ and
$N_{\sigma X_b}=T_\eta(0,\sigma r_mD)$.
The respective target coefficients are $(\sigma c,0)$ and $(0,\sigma c)$.
Equation (C121.8), $r_mD=\min(c,sD)$, and the $D=0$ case prove (C121.11).
The two signs are read together from the same fixed commuting experiment;
there is no choice of measurement depending on the unknown active pair. QED.

## 122. Sharp zero-white-noise minimax over every common CPTP processor

**Theorem C-122.1 (Attained full-four-source value).**
For every $m\in\mathbb N_0$ and $t\in[0,1]$, the infimum over all processors
in (C121.2), with no Schur, measurement or covariance restriction on competitors,
is attained and equals

$$
 e_m(t,0)=[t-D_m(t,0)]_+.
\tag{C122.1}
$$

In particular, with all endpoints included,

$$
 e_0(t,0)=t,\qquad e_1(t,0)=3t/5,\qquad
 e_m(1,0)=(3/5)^m,\qquad e_m(0,0)=0.
\tag{C122.2}
$$

For $0<t<1$, a sufficient and directly decidable finite-copy exactness
criterion is $D_m(t,0)\ge t$. Within the explicit processor (C121.10) it is
also necessary. At $t=1$ no finite $m$ gives exactness, even for an arbitrary
common whole-algebra CPTP processor.

Proof. The two opposite-$a$ target channels have diamond distance $2t$ by
(C121.8). Fix any admissible processor. For any reference/data input state,
feeding in either actual program defines a CPTP map from the program to the
reference/output, with this fixed input appended. Trace-distance contraction
bounds the two resulting outputs' trace-norm difference by $2D_m(t,0)$.
Taking the supremum over all finite reference/data states yields
$\|N_{X_a}-N_{-X_a}\|_\diamond\le2D_m(t,0)$.
The triangle inequality consequently gives

$$
2t\le\|\Phi_{t,0,X_a}-N_{X_a}\|_\diamond
 +2D_m(t,0)+\|N_{-X_a}-\Phi_{t,0,-X_a}\|_\diamond.
\tag{C122.3}
$$

Thus every common processor has worst error at least $[t-D_m(t,0)]_+$.
This uses actual opposite-source tensor powers and permits arbitrary complex
reference entanglement. Since $s=1$ at zero white noise, (C121.10) attains this
lower bound simultaneously for all four labels, proving (C122.1) and attainment
on the whole program algebra. A binary converse alone would not establish
this four-label simultaneous attainment.

At $m=0$ the trace distance is zero. At $m=1$ the two differing probabilities
are $(1+t)/5,(1-t)/5$, interchanged, so $D_1=2t/5$.
At $t=0$ the programs and channels coincide. At $t=1$, the two laws assign
$a_+$ probabilities $2/5,0$ and $a_-$ probabilities $0,2/5$.
Their only common support consists of strings with neither outcome. On it the
laws agree, with total mass $(3/5)^m$ under either source. The classical
identity $\tfrac12\sum|p-q|=1-\sum\min(p,q)$ gives
$D_m(1,0)=1-(3/5)^m$, also for $m=0$.
These computations prove (C122.2) and the finite-copy obstruction.
For $0<t<1$ the finite-copy existence assertion follows also from the explicit
budget in C-123.1 with $\eta=0$; it requires no perfect finite-copy source
identification. QED.

## 123. The same positive white noise permits exact noisy channels from finite copies

**Theorem C-123.1 (All-parameter bounds and a sufficient exactness budget).**
For the actual original noisy family, all $m\ge0$ and $t,\eta\in[0,1]$ satisfy

$$
 [c-D_m(t,\eta)]_+\ \le\ e_m(t,\eta)\ \le\
 [c-sD_m(t,\eta)]_+\ \le c.
\tag{C123.1}
$$

Here $c,s,\gamma$ are exactly (C121.3), and $D_m$ is the finite sum (C121.6).
At $t=0$ or $\eta=1$, $e_0=e_m=0$ and no program is needed.
If $c>0$ and the target margin $\gamma=s-c$ is strictly positive, then a finite
$m$ suffices for exact simultaneous programming of all four target channels.
One sufficient integer budget is

$$
 m\ \ge\ \left\lceil\frac{25}{2c^2}
              \log\frac{2s}{\gamma}\right\rceil.
\tag{C123.2}
$$

The logarithm here is natural. A smaller sufficient budget is any integer for
which (C121.6) gives $D_m\ge c/s$. Neither budget is asserted optimal for
$\eta>0$. The sole parameter point with $\gamma=0$ is $(t,\eta)=(1,0)$,
whose finite-copy obstruction is (C122.2).

Proof. Repeat (C122.3) with target distance $2c$, which is still exact by
(C121.8), and the actual noisy-program distance $2D_m(t,\eta)$. This proves
the lower bound over all CPTP competitors. C-121.3 gives the upper bound.
At $c=0$ every target is $T_\eta(0,0)$, directly implementable with $m=0$.

For $c>0$, on one measured copy let $H_a$ be $1$ at $a_+$, $-1$ at $a_-$,
and $0$ otherwise. Under the two opposite-$a$ laws its means are $2u$ and
$-2u$. The variables for $m$ copies are independent and lie in $[-1,1]$.
The bounded-variable estimate used here is the standard Hoeffding bound.
Its needed form follows directly: for a variable $V\in[-1,1]$, put
$F(\lambda)=\log\mathbb E e^{\lambda(V-\mathbb EV)}$. Its second derivative
is the variance under the exponentially tilted law, at most one;
$F(0)=F'(0)=0$ therefore implies $F(\lambda)\le\lambda^2/2$.
Independence, the exponential Markov inequality and minimization at
$\lambda=\alpha$ give the one-sided sample-mean bound
$\exp(-m\alpha^2/2)$, with a factor two for the two tails.
Applying it at $\alpha=2u$ gives
$\Pr_{a,+}(\sum H_a\le0)\le\exp(-2mu^2)$ and the opposite inequality under
$a,-$ with the same bound. The test given by the sign of the sum, with a fair
random tie, thus has average error at most $\exp(-2mu^2)$.
For commuting states the optimal equal-prior binary error is $(1-D_m)/2$,
as follows directly by assigning each outcome to its larger probability.
Consequently

$$
D_m(t,\eta)\ge1-2\exp(-2mc^2/25).
\tag{C123.3}
$$

This bound may be negative for small $m$; the exact value remains nonnegative.
Condition (C123.2) makes its right side at least $c/s=1-\gamma/s$.
Then $r_m=c/D_m\le s$ in (C121.9), and the average response is precisely the
target on every input matrix, hence with every complex reference.
Finally $\gamma=(1-\eta)(1-t)+\eta/5$ is a sum of nonnegative terms; its zero
set on the specified square is exactly the coherent corner. QED.

**Proposition C-123.2 (Exact channels do not require exact label identification).**
For $\eta>0$ and $c>0$, all four actual program states are positive definite.
No finite number of them permits perfect identification of $X$, whereas
C-123.1 gives exact channel programming with sufficiently many copies.
At $\eta=0$, $0<t<1$, the same statement holds on their common five-dimensional
support. In both cases the exact construction uses response channels whose
allowed coherence magnitude $s$ exceeds the target magnitude $c$.

Proof. In the noisy case the smallest program eigenvalue is at least
$\eta/25>0$. On the matching support at zero white noise and $t<1$, the
smallest eigenvalue is $(1-t)/5>0$. Tensor powers have the same common support
with strictly positive eigenvalues there. An effect with zero probability on
one such state must vanish on this support, and therefore has zero probability
on every state in the family. No POVM can give four disjoint perfectly
identifying outcomes. Nevertheless, (C121.12) has nonzero signed expectations.
Choosing $r_m=c/D_m$ reproduces the required coefficients exactly, while each
response remains CP because $r_m\le s$. The individual outcomes need not name
the true label; they may select more coherent channels than the averaged
target. This is exact synthesis by averaging actual controls, not postselection
or finite-copy perfect tomography. QED.

## 124. Fresh batches, shared calibration and paid whole-block communication

**Theorem C-124.1 (Fresh batches preserve the tensor channel contract).**
Use $n$ independent batches of $m$ copies each, all with the same fixed $X$,
independent of the entire complex block input and reference. Apply (C121.10)
once per data factor, with fresh local environments. The resulting map is
$N_X^{\otimes n}$, including for arbitrary inputs entangled across all $n$
factors and an arbitrary finite reference. Put
$\varepsilon_m=[c-sD_m(t,\eta)]_+$. Then

$$
 \sup_{X\in U_4}\|N_X^{\otimes n}-\Phi_{t,\eta,X}^{\otimes n}\|_\diamond
 \le\min\{2,n\varepsilon_m\}.
\tag{C124.1}
$$

Any common whole-block CPTP encoder and decoder as in (C116.3) can be composed
with these maps; the trace-norm error on every reference/logical input increases
by at most the same bound. In particular an ideal code with (C116.4) error
$\epsilon_n$ has implemented error at most $\epsilon_n+\min(2,n\varepsilon_m)$.
In the finite-copy exactness regime this is an exact replacement of the supplied
channel-use service, at cost $nm$ actual source copies, not $m$ copies total.
At $(t,\eta)=(1,0)$, a sufficient budget for added block error at most $\delta>0$
is $n(3/5)^m\le\delta$; for $\delta<n$ one may take
$m\ge\lceil\log(n/\delta)/\log(5/3)\rceil$.

Proof. Conditional on $X$, the initial batch state is
$\rho_{t,\eta}(X)^{\otimes mn}$, regrouped into $n$ independent batches. The
joint processor is the tensor product of the specified CPTP maps. Linearity
on the full input algebra gives exactly $N_X^{\otimes n}$, without a product
assumption on data or reference. Telescope the difference of tensor powers,
replacing one factor at a time. CPTP pre- and postcomposition and untouched
ancillas do not increase diamond distance, so the $n$ terms sum to at most
$n\varepsilon_m$. Two channels have unhalved diamond distance at most two.
Further whole-block CPTP composition preserves this estimate. C-122.1 gives
the coherent-corner budget. No asymptotic rate per source copy follows. QED.

**Proposition C-124.2 (A reused exact one-use record can fail already at two uses).**
Measuring one batch and reusing its record $z$ on every factor instead gives

$$
\Psi_X^{(n)}=\sum_z p_X^{\otimes m}(z)\,T_z^{\otimes n},
\quad\hbox{rather than}\quad
N_X^{\otimes n}=\left(\sum_zp_X^{\otimes m}(z)T_z\right)^{\otimes n}.
\tag{C124.2}
$$

This distinction persists even when the one-use map is exact. For an explicit
zero-white-noise example take $t=1/2$, $m=5$, $X=X_a$ and (C121.10). Then

$$
 D_5(1/2,0)=13043/25000>1/2,\qquad r_5=12500/13043<1,
\tag{C124.3}
$$

so $N_X=\Phi_{1/2,0,X}$ for all four labels. Nevertheless, on the actual
complex two-use input
$|\zeta\rangle=(|1,3\rangle+|3,1\rangle)/\sqrt2$, the reused-record output
has trace-norm distance at least

$$
 r_5^2\,\mathbb E_{a,+}h_b^2>0
\tag{C124.4}
$$

from the desired tensor output. Thus exact one-use programming is not a license
to reuse a finite calibration record as independent channel environments.

Proof. For $\eta=0,t=1/2$, $w=1/5,u=1/10$; the opposite-$a$ probabilities are
$3/10,1/10$ and $1/10,3/10$, with remaining mass $3/5$. Substituting them in
the finite trinomial sum (C121.6) yields $13043/25000$.
The inactive-$b$ sign has mean zero, but not zero second moment: the event that
all five outcomes are $b_+$ alone has probability $(1/5)^5>0$.
On $E_{13}\otimes E_{31}$, a conditional response has coefficient
$(ir_5h_b)(-ir_5h_b)=r_5^2h_b^2$. Its average is strictly positive; the target
tensor channel and $N_X^{\otimes2}$ both annihilate this matrix unit because
$X_a$ has no $13$ coherence. At zero white noise all sector populations are
preserved. On the stated balanced input the difference is a Hermitian
$2\times2$ off-diagonal block of trace norm $r_5^2\mathbb E h_b^2$.
This proves the claim using a normalized state, not only a non-Hermitian matrix
unit. Its meaning is classical common-record correlation conditional on the
same actual source, not label variation between uses. QED.

**Theorem C-124.3 (A useful uniform block bound from one shared calibration batch).**
There is also a different common processor using just one batch of $m$ copies
for an entire $n$-use block. For $c>0$ and $m\ge1$, measure (C121.4), and choose the nearest,
in the maximum norm, of the four mean vectors
$(2u,0),(-2u,0),(0,2u),(0,-2u)$ to the empirical vector
$(\bar H_a,\bar H_b)$. Fix ties independently of $X$.
Call the resulting four-valued record $\widehat X$. Conditioned on it, implement
$\Phi_{t,\eta,\widehat X}^{\otimes n}$ using fresh local environments.
The resulting whole-algebra CPTP block processor obeys, uniformly in $n$,

$$
 \sup_{X\in U_4}\|\widetilde\Psi_X^{(n)}-
            \Phi_{t,\eta,X}^{\otimes n}\|_\diamond
 \le2\delta_m,\qquad
 \delta_m=\min\{1,4\exp(-mc^2/50)\}.
\tag{C124.5}
$$

For $m=0$ choose a fixed label and use its tensor channel; the bound is then
the trivial two. The same bound holds after any common CPTP block encoder and
decoder and for every finite complex reference. Hence a sufficient batch size for added block
error at most $0<\delta<2$ is
$m\ge\lceil50c^{-2}\log(8/\delta)\rceil$, independent of $n$.
At $c=0$ use no batch and implement the common target directly.
This shared-record construction has no finite-copy exactness claim for $c>0$.

Proof. Distinct mean vectors are at maximum-norm distance at least $2u$.
If both empirical coordinates differ from their true means by less than $u$,
the nearest vector is uniquely correct. Each variable is in $[-1,1]$;
the two-sided Hoeffding bound and a union bound give
$\Pr_X(\widehat X\ne X)\le4\exp(-mu^2/2)=4\exp(-mc^2/50)$.
This probability is independent of the data/reference. On the correct event
the entire conditional block channel equals the desired tensor channel;
on the other events its diamond distance is at most two. Convexity gives
(C124.5), with no factor $n$. Measurement followed by a controlled product of
CPTP maps defines a CPTP map on every program/block input, by the same
instrument formula as (C121.10). This proves the whole-block statement rather
than incorrectly tensoring the averaged one-use map. QED.

**Proposition C-124.4 (Explicit control, transport and decoder costs).**
Every response in (C121.10) and every conditional target in C-124.3 has a finite
rank-at-most-two Kraus implementation. There is a lawful separated-party route
with the following sufficient resources, in addition to the actual programs:

- Each measured copy needs one fixed six-outcome joint projective measurement
  on its original $25$-dimensional $A\mid B$ carrier. For a one-use fresh batch,
  the two count differences determine two trits $h_a,h_b$; at most nine
  calibrated response settings are required. A six-dimensional pointer ancilla
  suffices for each projective measurement and can be reset between copies.
  One may retain the raw $m$
  six-valued outcomes ($3m$ classical bits suffice), or update just the two
  counts (at most $(2m+1)^2$ states) and discard them after choosing the response.
  C-124.3 instead retains one four-valued calibration record (two bits).
- Local controls supply the fixed complex phases in (C121.4), the known numbers
  $r_m,s,\eta$ or $c$, their required square roots, finite ancillas and the
  conditional Kraus instrument. Exact real-valued controls are a separate
  supply obligation. A response needs at most $25$ Kraus branches and an
  environment of dimension at most $25$ before it is discarded or measured.
- If the source halves initially reside at separated laboratories $A,B$, put
  the processor at $A$ and transport the $B$ half of each program copy to $A$
  through a declared noiseless five-dimensional quantum wire. This costs one
  such transfer per consumed source copy: $nm$ for fresh batches, $m$ for the
  shared batch. Joint measurement is then local at $A$. No native local-history
  measurement or free classical phase revelation substitutes for this transport.
- For each simulated data use from $A$ to $B$, the route below transmits a
  two-dimensional quantum port and one flag from an alphabet of at most $25$
  ($5$ classical bits suffice). For $n$ uses its aggregate port dimension is
  $2^n$ and flag alphabet is at most $25^n$ ($5n$ bits suffice). These forward
  quantum and classical links are charged communication resources, with no
  additional preshared entanglement, return data wire or free forward/feedback
  side channel.
  The calibration record need not be sent to $B$ in this implementation.

All decoders are CPTP on their entire port spaces. Composing with a supplied
C-116 whole-block encoder/decoder is legitimate, but its local block operations
are additional services. The resulting physical resource bundle is not the
unassisted channel-use contract used to define the capacities in C-116.

Proof. Write the unnormalized matching matrix for a response as

$$
 M(v)=sI_5+v_aX_a+v_bX_b.
\tag{C124.6}
$$

Its orthonormal eigenvectors are the coefficient-space versions of (C121.4),
with eigenvalues $s\pm v_a,s\pm v_b,s$. For each of these five vectors $q_\ell$
and its eigenvalue $\lambda_\ell\ge0$, take the diagonal Kraus matrix
$K_\ell=\sqrt{\lambda_\ell}\operatorname{diag}(q_\ell)$.
Their Schur sum is $M(v)\circ Y$. Add the twenty Kraus matrices
$\sqrt{\eta/5}E_{jk}$ for $j\ne k$. Their sum gives
$\frac\eta5\sum_{j\ne k}Y_{kk}E_{jj}$.
Together these are exactly (C121.7); their completeness follows also directly
from $s+4\eta/5=1$. The five diagonal matrices have rank at most two and the
other twenty rank one, including vanishing branches at endpoints.

For each branch choose a fixed isometry $V_\ell:\mathbb C^2\to\mathbb C^5$
whose image contains the range of $K_\ell$. For the four pair branches use the
corresponding original coordinate pair; for a rank-one branch complete its
one coordinate with any different fixed original coordinate. These choices do
not depend on $v$, $z$ or $X$. Put $B_\ell=V_\ell^\dagger K_\ell$.
Then $\sum_\ell B_\ell^\dagger B_\ell=I_5$, so the sender instrument
$Y\mapsto B_\ell YB_\ell^\dagger$ with flag $\ell$ is trace preserving when
all branches are retained. Send its qubit output and flag. The receiver applies
$Z\mapsto V_\ell ZV_\ell^\dagger$, an isometric CPTP decoder on every qubit
input. The composite branch is exactly $K_\ell YK_\ell^\dagger$.
The decoder is common because $V_\ell$ is fixed; all parameter-dependent
amplitudes reside in the sender instrument. No successful flag is postselected.

For blocks, retain the entire flag string and use the controlled tensor product
of these isometries, followed by the supplied arbitrary whole-block CPTP decoder.
This is one whole-block CPTP decoder, including on correlated inputs across
ports and the reference. The branchwise equality proves the exact channel
factorization on the full algebra; C-124.1 or C-124.3 then controls simulation
error. Transporting the program halves is an explicitly paid way to make the
joint measurement available. Alternatively co-located actual programs can be
supplied directly, but that is a different declared preparation service. QED.

## 125. Consumed suppliers and the remaining acquisition boundary

**Scope C-125.1 (What the construction closes).**
The source-copy-to-channel service in C-121–C-124 is a conditional mathematical
implementation of precisely the original four sources and their associated
channels, with known $t,\eta$, one unknown persistent label, actual independent
tensor copies and uniform complex-reference error. It quantifies part of the
unknown-source access gap left in C-115.6 and C-120.2. It does not produce the
copies from native histories, synthesize exact amplitudes from code names or
make separated-party transport free. A declared joint CPTP processor by itself
is not a separated-party communication protocol; C-124.4 supplies one paid route.
No minimal physical acquisition cost, optimal positive-noise copy budget,
asymptotic coding rate per source copy or improved channel capacity is asserted.
The exact noisy one-use construction uses fresh independent program batches
when invoked as independent channel uses. The shared-record block construction
has the different law and bound (C124.5).

The comparison with
[Contextual spacetime arithmetic quantum, §§187 and 200](CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md#187-一枚非交换程序消去固定经典设计的统一额外成本)
is at the level of a fixed processor with an initially independent program.
Section 187.1 permits a chosen program curve; its displayed optimal qubit
curve is noncommuting, and §187.2 treats arbitrary commuting curves by their
fixed-basis classical components. Section 200 concerns chosen two-dimensional
program curves for a three-level Schur family and SLD equality/continuation,
including a nonzero Bloch transverse coordinate. Those program carriers and
optimization criteria are not the prescribed $\rho_{t,\eta}(X)^{\otimes m}$.
Their chosen-program synthesis is therefore not an acquisition or tensor-copy
supplier for this increment. Here commutativity is proved directly from the
original matrices in (C121.4), and the copy distributions are fixed by them.

Likewise
[Acquisition Resources XVI, §§289–296](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVI.md#289-a-four-address-payer-with-a-signed-residual-and-one-input-budget)
uses original Boolean replies, finite decision trees, nonnegative allocations
and signed residuals. Its actual four-address payers, finite-reader synthesis
and restricted common-budget results retain those classical carriers. They
supply neither this six-outcome quantum measurement nor its phase controls,
quantum program copies or transmission links. The native heat-trace crossover
uses scalar spectral measures and native clocks; it does not change this
carrier boundary. These are explicit missing implementation bridges, not
objections to the conditional mathematical channel construction.

**Literature input C-125.2 (Primary ingredients and limits of their transfer).**
The finite-dimensional CP/Kraus/Choi and distance ingredients are reused,
including the actual declarations and private supporting closure of
`D5/S3/Quantum/Foundation/FiniteKrausRepresentation.lean`,
`FiniteKrausChannel.lean`, `FiniteTraceDistance.lean` and
`FiniteDiamondDistance.lean`. In the actual `MatrixMap.choi_matrix` definition
the index order is output/input and the Choi matrix is unnormalized; dividing
by five gives the convention (C116.2). No displayed narrative convention is
used to reverse these indices. `FiniteDiamondDistance.diamondDistance`
uses the unhalved stabilized reference-state distance; its pure-input/reference
reduction does not assert the new minimax computation here. The existing
`QuantumChannels/CovariantPureProgramDimensionRefutation.lean` and
`PureProgramQubitObstruction.lean` distinguish chosen mixed and pure programs;
their four-target obstruction does not give a source-copy error formula.
No new generic Kraus, CP criterion, norm theorem or decorative Lean application
is needed for the ordinary source-specific proofs above.

The mature comparison/programming ingredients are `literature-attested`:

- Francesco Buscemi, [*Comparison of quantum statistical models: equivalent
  conditions for sufficiency*, arXiv:1004.3794v4](https://arxiv.org/html/1004.3794v4),
  §§4–8, especially the distinction between statistical morphisms and CPTP
  extension and the abelian-output extension in Proposition 3. Merely matching
  classical native tests does not establish a full-algebra quantum processor.
  Here (C121.10) explicitly supplies that processor, and the converse uses
  trace-distance contraction, rather than claiming a restricted-test criterion
  gives the required quantum simulation.
- Anna Jenčová, [*A general theory of comparison of quantum channels (and
  beyond)*, arXiv:2002.04240v2](https://arxiv.org/html/2002.04240v2),
  §3.1.5 and §3.2: diamond-norm comparison and admissible channel transformations
  retain the ancillary-system quantifiers. We use that operational distinction;
  no generic comparison theorem alone evaluates this prescribed four-program task.
- Martina Gschwendtner, Andreas Bluhm and Andreas Winter,
  [*Programmability of covariant quantum channels*, arXiv:2012.00717v2](https://arxiv.org/html/2012.00717v2),
  §3.3, Proposition 24: its exact Choi-program teleportation construction assumes
  an irreducible input representation $U$ of a compact group, with the stated
  covariance. The original-basis phase symmetry here is reducible; no qualifying
  irreducible common covariance is supplied. That proposition is not invoked
  to turn one unknown original Choi state into its channel.
- Stefano Pirandola, Riccardo Laurenza, Cosmo Lupo and Jason L. Pereira,
  [*Fundamental limits to quantum channel discrimination*, arXiv:1803.02834v4](https://arxiv.org/html/1803.02834v4),
  §II.2, Lemma 1 and §II.3: deterministic port-based teleportation gives a
  generic common simulation from tensor powers of normalized channel Choi
  states, with its own measurement and routing services and diamond-error
  bound. This is a generic benchmark, not new content or an assertion of
  exact finite-copy simulation at the coherent corner. C-122 evaluates the
  unrestricted minimax for the original zero-noise subfamily more specifically.
- Wassily Hoeffding, *Probability inequalities for sums of bounded random
  variables*, Journal of the American Statistical Association 58, 13–30,
  [DOI 10.1080/01621459.1963.10500830](https://doi.org/10.1080/01621459.1963.10500830),
  Theorem 2 (bibliographic attribution; the primary article text was not
  obtained here): for variables in $[-1,1]$, the one-sided sample-mean
  deviation bound is $\exp(-m\alpha^2/2)$, with the two-sided factor two. The
  needed estimate and its constants are supplied directly by the bounded-mgf
  derivation in the proof of (C123.1), rather than by an unverified quotation.

The simultaneous original-source response construction, attained zero-noise
minimax, noisy interior exactness budget and their fresh/shared-record resource
connection are `repo-derived` synthesis. The bounded comparison above does not
assert exhaustive absence of an equivalent result in the literature or global
originality. These are complete ordinary proofs; there is no exact scoped Lean
application, accepted axiom-closure evidence or kernel claim for this increment.
Physical/native preparation, exact calibration supply and cheaper lawful routes
remain outside the proved acquisition result.

## 126. Operation-control supplier and its exactness boundary

**Correspondence C-125.3 (Independent controls are an added service).**
The operation-control result in `AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md`,
§§19 and 21–22 of pinned source snapshot `2c22f027c10d658fbf32942a70f717537c61b2d0`,
uses the single five-dimensional carrier $\mathcal H_F$ of Definition 43.1.
Assumption 45.1 supplies three independently adjustable gates on that carrier
in addition to the passive coordinate matrix $D$; the second contract also
supplies an independently adjustable $e^{i\phi E_{00}}$. After restriction to
that five-dimensional space, Proposition 45 gives

$$
\operatorname{Lie}_{\mathbb R}(A_1,A_2,A_3)=\mathfrak{so}(5),\qquad
\operatorname{Lie}_{\mathbb R}(A_1,A_2,A_3,iE_{00})=\mathfrak u(5).
$$

In the original coordinates the closures are $D\,SO(5)\,D^\dagger$ and $U(5)$,
respectively, on that single carrier. They do not supply control on
$\mathbb C^5\otimes\mathbb C^5$. The six-outcome PVM in (C121.4) acts on this
$25$-dimensional carrier, with projections onto the five matching vectors in
(C121.4), including the entangled pairs, and the rank-$20$ complementary
projection $Q$. The mathematical isometry $J$ supplies neither
encoded joint operations nor a readout separating $JJ^\dagger$ from $Q$.
For $\eta>0$, that complement has probability $20\eta/25$ and cannot be discarded.
No approximation to this joint PVM is supplied by Proposition 45.

This is a control correspondence, not a source correspondence: $D$ remains
passive, and the independent gates are new permissions. The source result also
records that nonnegative parameters can realize each individual inverse because
the displayed generators have periodic spectra; this does not make a fixed-sum
control parameter invertible.

Within its single-carrier contract, the proposition proves approximation:
every target and every positive tolerance has a finite product. It does not
provide an exact finite pulse sequence for an arbitrary target, a uniform pulse
count, total time or energy, or an exact calibrated amplitude. Any use as an
approximate control supplier requires its tolerance to be included in the
relevant diamond-error budget; no joint-PVM approximation or corresponding error
bound is supplied by this result. It does not by itself supply the states $\rho_{t,\eta}(X)$,
the exact phase reference, the exact response maps in (C121.10), or the finite
physical resource bundle in (C124.4). The exact controls and joint measurement
in C-121–C-124 therefore remain explicit services unless stronger contracts
separately supply those operations, readout and exact calibration.

## 127. Independent sources and single-copy certification

**Correspondence C-125.4 (Certification does not manufacture the program).**
The four-corner source result `AURIC_FIB_ATOM_FOUR_CORNER_COHERENCE_AND_SINGLE_COPY_CERTIFICATION.md`,
§§116 and 120–122 of the pinned source snapshot, uses the same five-mode
carrier and a different source family. In C-116.1,
$\rho_\pm$ and $\bar\rho$ are five-mode states; in C-116.2 the exchangeable
source $\Gamma_N=\tfrac12\rho_+^{\otimes N}+\tfrac12\rho_-^{\otimes N}$ is fully
separable across copies and has the same one-copy marginal and all bottom
indicator product probabilities as $\bar\rho^{\otimes N}$, while the actual
two-copy projection distinguishes them. Equal marginals and indicator laws
therefore do not certify iid copies or erase source correlations. This family
uses separability on the bottom $\mathbb C_A^2\mid\mathbb C_B^2$ cut, while
multi-copy separability uses $\mathcal H_5^{(1)}\mid\cdots\mid\mathcal H_5^{(N)}$;
neither cut is the two five-dimensional halves of the C-121 program carrier.
C-120.1's fixed-diagonal coherent family has the linear readouts
$a(\sigma_\gamma)=\gamma$, $b(\sigma_\gamma)=1$ and concurrence $\gamma$; it is
a certification family, not the U4 program family $\rho_{t,\eta}(X)$ on
$(\mathbb C^5\otimes\mathbb C^5)^{\otimes m}$.

C-121.1 makes the operational distinction explicit: one actual five-mode source
copy is consumed in each round, the setting is independent of the current
source conditional on the observed history, and iid is not assumed. Its actual
effects are $E_{j,+}=(P_{\mathrm b}+K_j)/2$,
$E_{j,-}=(P_{\mathrm b}-K_j)/2$ and
$E_{j,0}=I_5-P_{\mathrm b}$, with a fresh setting $J_n\in\{1,2\}$ chosen
independently conditional on that history. The
nonnegative-supermartingale result C-121.3 then gives the anytime bound only
under its history-conditional separability contract and its actual PVM. C-122.1
and C-122.2 add a different supplier assumption—iid copies of the specified
coherent family with a calibrated phase—and derive an expected stopping-cost
bound. “Single-copy” means one consumed source per round; it does not mean that
one observed sample certifies an entire experiment. These results provide
certification and source-model diagnostics when their contracts are met. They
do not produce the U4 tensor copies, the joint 25-dimensional measurement, or
the channel controls required by C-121–C-124.

## 128. Native bounded preparers and the quantum boundary

**Correspondence C-125.5 (Finite native synthesis is a separate carrier).**
`FIB_BOUNDED_NATIVE_PREPARER_SYNTHESIS.md`, §§8–12 of the pinned source
snapshot, defines an attained relation on finite trees and installed reader states. Its
Theorem 8.3 preserves that relation under literal-only normalization, and
Theorem 10.2 gives a terminating exact finite decision/synthesis procedure for
the SOME-preparer question, with actual finite origins for both attained bits
when the native budgets pass. The counted quantities are installed native
states, literal reads, serving calls and finite-tree witnesses; the reader,
original Boolean replies and serving table are part of that contract.

This is a lawful supplier for a bounded classical/native preparer only when its
finite-tree and serving-table premises and actual witnesses are supplied. It
does not prepare a density operator, a phase reference, a complex amplitude,
the six-outcome PVM, a CPTP response map, or a quantum wire. Its $N,P,L$ and
six-capacity bounds cannot be renamed as the quantum copy count $m$, Hilbert
space dimension, diamond error or communication cost. Acquired finite code
terms in that volume likewise do not become native quantum source copies.
The native result therefore sharpens the classical acquisition boundary while
leaving the quantum tensor-copy supply open.

**Supplier ledger C-125.6.** The three new correspondences have the following
scopes:

| Required service for C-121–C-124 | Fresh result that bears on it | Status in this volume |
| --- | --- | --- |
| Native/physical preparation of $\rho_{t,\eta}(X)^{\otimes m}$ | C-116/C-122 source contracts; native §§8–12 | Not supplied; premises remain external |
| Exact phase and amplitude calibration | Assumption 45.1 and Proposition 45 with the added phase gate | Approximate controllability only; exact calibration remains open |
| Approximate controllability | Proposition 45 Lie closures on $\mathcal H_F$ | Single-carrier mathematical approximation only; no uniform resource bound |
| Source certification | C-121.1–C-122.2 histories, PVM and iid contracts | Available only under those stated source and measurement assumptions |
| Actual tensor-copy supply and paid transport | C-124.4 | Not supplied by any of the three results |

No row converts a reachable closure, a classical controller state, or a
certification record into an exact finite operation or resource budget. In
particular, these suppliers do not close the remaining quantum preparation gap
unless their stronger physical conditions are separately established.

**Literature access boundary C-125.7.** The DOI landing page for the cited
Hoeffding article returned HTTP 403, so its primary text was not verified. The
attribution above is consequently limited to bibliographic identification; the
bound used in this manuscript is established by the self-contained mgf,
exponential-Markov and independence derivation in (C123.1), including the
constants in (C123.3) and (C124.5). No primary-source verification is claimed.

## 追加锚（本行以下为增补区）

## 129. Actual quantum hits supply phase coherence under fixed real joint controls

**Definition C-129.1 (Same source, restricted operations and comparison class).**
Retain exactly C-116.1 and C-121.1–C-121.3: the ordered original labels
$B=(0,1,2,3,13)$, $f=(0\ 13)(1\ 3)$ with $f(2)=2$, the real isometry
$Je_j=|B_j,f(B_j)\rangle$, the original $A\mid B$ cut, $U_4$, and
$\rho_X=\rho_{t,\eta}(X)$ with known $t,\eta\in[0,1]$. In particular,

$$
\begin{aligned}
\rho_X&=(1-\eta)J(I_5+tX)J^\dagger/5+\eta I_{25}/25,\\
\Phi_X(Y)&=(1-\eta)(I_5+tX)\circ Y+\eta\operatorname{tr}(Y)I_5/5,\\
c&=(1-\eta)t,\quad s=1-4\eta/5,\quad w=s/5,\quad u=c/5.
\end{aligned}
\tag{C129.1}
$$

There is one fixed unknown $X\in U_4$, no prior on it, and $m$ actual
conditionally iid copies, initially independent of the data and every complex
reference. Thus $1/5\le s\le1$ and $0\le c\le s$.
All maps act complex linearly on the whole indicated complex matrix algebras.
The fixed real structure is entrywise conjugation in these original product
bases; it is not a change of cut or a restriction to real input states.

A real processor has a complete finite Kraus family of real rectangular
matrices in this fixed structure. Write $e_m^{\mathbb R}(t,\eta)$ for the
infimum in (C121.2) restricted to these processors, retaining the unhalved
diamond norm and arbitrary complex references. In particular
$e_m\le e_m^{\mathbb R}$. Real operations, in this established sense, are
the operations of [Wu et al.](../../../Library/Quantum/wu2021imaginarity.md).
The finite realization menu used here consists of real blank ancillas,
computational basis permutations and sign reflections, specified two-level
real rotations on joint registers, computational projective measurement,
classical feedforward, and discarding. A two-level rotation on basis vectors
$p,q$ has matrix $\left(\begin{smallmatrix}\cos\theta&-\sin\theta\\
\sin\theta&\cos\theta\end{smallmatrix}\right)$ there and identity elsewhere.
Exact known angles and the corresponding joint controls are supplied services.
The menu includes real quantum wires when the original laboratories are
separated, charged in C-133.1. It contains no conjugation or transpose gate
on an unknown state, no externally supplied imbit, and no revealed label.

**Theorem C-129.2 (First-hit real processor and its exact error).**
For every $m\in\mathbb N_0$ and every $t,\eta\in[0,1]$, one common real
whole-algebra CPTP processor has, simultaneously for all four labels, error

$$
E_m(t,\eta)=\frac cs\big[(1-2s/5)^m-(1-s)\big]_+.
\tag{C129.2}
$$

More precisely, put

$$
p=2s/5,\qquad q_m=1-(1-p)^m,\qquad h=\min\{q_m,s\},\qquad b=c/s.
\tag{C129.3}
$$

Its promised induced channels, on every $Y\in M_5(\mathbb C)$, are

$$
N_{\sigma X_a}=T_\eta(\sigma bh,0),\qquad
N_{\sigma X_b}=T_\eta(0,\sigma bh),\qquad \sigma\in\{1,-1\},
\tag{C129.4}
$$

with $T_\eta$ as in (C121.7). These identities extend after tensoring with
the identity on every finite complex reference. Whole-algebra validity of
the processor also includes unpromised programs and correlated data/program
inputs; the promised identity (C129.4) uses the specified independent batch.

Proof. Set $d_a=(0,4)$ and $d_b=(1,3)$. For $d=(j,k)$ let

$$
P_d=|Je_j\rangle\langle Je_j|+|Je_k\rangle\langle Je_k|,\qquad
F_d=I_{25}-P_d,\qquad
T_d=|0\rangle\langle Je_j|+|1\rangle\langle Je_k|.
\tag{C129.5}
$$

These are real matrices, $T_d^\dagger T_d=P_d$, and $P_d$ is diagonal in
the original product basis. Direct compression of the actual source gives
$\operatorname{tr}(P_d\rho_X)=2w=p$ for every $X$. With
$H=i(|0\rangle\langle1|-|1\rangle\langle0|)$,

$$
\frac{T_d\rho_XT_d^\dagger}{p}
 =\begin{cases}(I_2+\sigma bH)/2,&X=\sigma X_d,\\
 I_2/2,&X\text{ is on the other pair}.
 \end{cases}
\tag{C129.6}
$$

In particular this is a mixed extracted subsystem, with its actual bias
$b=c/s$. It is not a supplied eigenvector or a chosen maximally imaginary
state. The $20$ unmatched white-noise coordinates, the singleton, and the
other pair all belong to the measured complement $F_d$.

First pinch the data with the three real projections onto
$\operatorname{span}\{e_0,e_4\}$, $\operatorname{span}\{e_1,e_3\}$ and
$\operatorname{span}\{e_2\}$. On a pair sector $d$, measure
$\{P_d,F_d\}$ on the program copies in their fixed order until the first
hit. On a hit extract by $T_d$, retaining its qubit, and discard the other
program registers. If all $m$ tests fail, retain the no-hit outcome. On the
singleton sector discard every program register immediately.

For completeness, the unnormalized CP success map $\mathcal H_{d,m}$ from
programs to a qubit is the sum over first-hit positions $\ell=1,\ldots,m$:
project preceding factors with $F_d$, extract factor $\ell$ with $T_d$,
and trace out every other factor. Each summand has real Kraus operators.
On a product-basis vector $|z_1\cdots z_m\rangle$, its effect is the
indicator that the first factor belonging to the two matching coordinates
of $d$ occurs at $\ell$. Thus

$$
\mathcal H_{d,m}^*(I_2)=I-F_d^{\otimes m},\qquad
\mathcal H_{d,m}(\rho_X^{\otimes m})
 =\sum_{\ell=1}^m(1-p)^{\ell-1}T_d\rho_XT_d^\dagger
 =q_m\omega_{d,X},
\tag{C129.7}
$$

where $\omega_{d,X}$ is (C129.6). The effect identity is on the full program
space, not just on the promised states. The empty sum is zero and
$F_d^{\otimes0}=1$ at $m=0$.

If $q_m>0$, accept a hit with probability $a=h/q_m$ using a real coin;
otherwise put $a=0$. Rejection and no hit are both failure outcomes and
are retained. The accepted quantum map is $a\mathcal H_{d,m}$; the failure
effect is
$I-a(I-F_d^{\otimes m})\succeq0$. The instrument is complete on every
program input. Its promised acceptance probability is $h$, independent of
the unknown label, and the accepted qubit is still $\omega_{d,X}$.

On acceptance apply, to the data pair and that actual qubit, the real
orthogonal controlled matrix

$$
R=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
G_d=|j\rangle\langle j|\otimes I_2
       +|k\rangle\langle k|\otimes R,
\tag{C129.8}
$$

then discard the qubit. On the selected pair $G_d^\dagger G_d=I_4$.
For a gate on the entire data/qubit register, extend it by identity on the
other three data coordinates.
This is the restricted controlled-imbit mechanism of
[Wu et al., Appendix A, (22)–(23)](../../../Library/QuantumChannels/wu2024distributedimaginarity.md),
used here with the actual mixed state (C129.6). Directly, for
$\omega=(I_2+zH)/2$ and every complex pair matrix,

$$
\operatorname{tr}_2[G_d(E_{jk}\otimes\omega)G_d^{\mathsf T}]
 =E_{jk}\operatorname{tr}(\omega R^{\mathsf T})=izE_{jk};
\tag{C129.9}
$$

the $kj$ multiplier is $-iz$ and both diagonal multipliers are one.
Indeed $R^{\mathsf T}=-R$, $R^2=-I_2$ and $H=iR$. Equation (C129.9)
also holds at $z=0,\pm1$; no sign measurement or phase calibration depending
on $X$ is performed. Inactive-pair hits supply $z=0$ and hence no coherence.

On failure measure the data coordinate $r\in d$ and use the real classical
channel with transition probabilities

$$
v_{l|r}=\begin{cases}(s-h)/(1-h),&l=r,\\
\eta/[5(1-h)],&l\ne r.
\end{cases}
\tag{C129.10}
$$

For finite $m$, $p\le2/5$ gives $q_m<1$, hence $h<1$. Thus this formula
has no vanishing denominator, including at $\eta=0$. It is nonnegative,
and its column sum is $(s-h+4\eta/5)/(1-h)=1$.
The Kraus matrices are $\sqrt{v_{l|r}}|l\rangle\langle r|$.
On the singleton $r=2$, instead use probabilities $s$ for $l=2$ and
$\eta/5$ for each $l\ne2$, again a complete real measure-and-prepare map.

Each branch is a composition of real CP instruments, a real orthogonal
matrix and partial traces. The first-hit instrument, coin, failure
transitions and singleton map each retain every outcome. Their completeness
proves TP for the full data/program algebra, without independence or any
promise on that input. Tensoring the same real Kraus matrices with $I_R$
proves CP and TP with every complex reference.

For the promised inputs, a pair-sector diagonal $E_{rr}$ has output weight
$h+(1-h)v_{r|r}=s$ at $r$, and $(1-h)v_{l|r}=\eta/5$ at every $l\ne r$.
The singleton has exactly the same target populations. Every cross-sector
matrix unit vanishes, as it does under $\Phi_X$. Within a pair, the failure
branch kills its off-diagonals; (C129.6)–(C129.9) give coefficients
$\sigma bh$ on the active pair and zero on the inactive pair. This checks
all $25$ complex matrix units and proves (C129.4) and its reference extension
by complex linearity. Finally $bh\le c\le s$; (C121.8) gives exact error
$c-bh=(c/s)[s-q_m]_+$, which is (C129.2). QED.

## 130. Relative-sign quantum retention realizes the supplied unrestricted optimum

**Proposition C-130.1 (An explicit real instrument for conjugate program words).**
Use the same $H=iR$ as in (C129.8)–(C129.9), and write
$P_\epsilon=(I_2+\epsilon H)/2$. For every finite $m$, a finite real
program-only instrument has a classical record and at most one retained
qubit with the following promised action. The six-outcome words $z$ of
(C121.4), with probabilities $\lambda_X(z)=p_X^{\otimes m}(z)$, are
partitioned into conjugate pairs $\{z,\bar z\}$ by simultaneously swapping
$a_+,a_-$ and $b_+,b_-$. A word containing no pair outcome is fixed.
For each two-word orbit choose the representative whose first pair sign is
$+$. The record identifies this orbit, and its unnormalized retained qubit is

$$
\tau_{X,z}=\lambda_X(z)P_++\lambda_X(\bar z)P_-,\qquad
\operatorname{tr}\tau_{X,z}=\lambda_X(z)+\lambda_X(\bar z),\quad
\operatorname{tr}(H\tau_{X,z})=\lambda_X(z)-\lambda_X(\bar z).
\tag{C130.1}
$$

For a fixed word the outcome is its scalar weight $\lambda_X(z)$ with no
retained qubit. The $*$ symbol includes all $20$ unmatched modes. Zero
weights, all-neutral words, $m=0$ and every failure/no-pair branch are
included. In particular, the qubit is not a supplied $H$ eigenstate, and its
unknown sign is not measured into the record.

Proof. On each actual copy use the four real sector effects
$P_{d_a},P_{d_b},|Je_2\rangle\langle Je_2|,I_{25}-JJ^\dagger$.
On the first two outcomes use the extraction $T_d$ in (C129.5), retaining
a qubit. On the singleton discard its fixed coordinate; on $*$ discard the
full unmatched sector. The latter map has the twenty real Kraus rows
$\langle v|$, one for each unmatched original computational vector $v$.
Together with $T_{d_a},T_{d_b},\langle Je_2|$, these rows have completeness
operator $I_{25}$. Thus this is a complete instrument on every complex
program, including correlated multiple-copy inputs, not a postselection.

Fix its sector record and order the $k$ extracted qubits by original copy
position. If $k=0$, nothing further is done. If $k\ge1$, retain qubit $1$
and for $j=2,\ldots,k$ apply the following real orthogonal gate on qubits
$1,j$, then measure and discard qubit $j$ in the computational basis:

$$
\begin{aligned}
A&=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\quad
Z=\operatorname{diag}(1,-1),\\
V_{1j}&=(I_2\otimes A)
 \big(I_2\otimes|0\rangle\langle0|
       +R^{\mathsf T}\otimes|1\rangle\langle1|\big),\\
V(H\otimes I_2)V^{\mathsf T}&=H\otimes I_2,\qquad
V(I_2\otimes H)V^{\mathsf T}=H\otimes Z.
\end{aligned}
\tag{C130.2}
$$

The controlled matrix in parentheses and $A$ are individually real
orthogonal. Multiplying the two $4\times4$ matrices gives the displayed
identities. They imply, for the rank-one projectors and $e=\epsilon_1
\epsilon_j$, the exact density-matrix identity

$$
V(P_{\epsilon_1}\otimes P_{\epsilon_j})V^{\mathsf T}
 =P_{\epsilon_1}\otimes |b(e)\rangle\langle b(e)|,
\qquad b(+1)=0,\quad b(-1)=1.
\tag{C130.3}
$$

Indeed the left side is the joint eigenspace of $H\otimes I$ and
$H\otimes Z$ with eigenvalues $\epsilon_1,\epsilon_j$; that space is
one dimensional. Subsequent gates preserve $H$ on qubit $1$ and do not
act on earlier measured bits. Hence the recorded bits give every relative
sign $\epsilon_1\epsilon_j$ while the retained qubit keeps $P_{\epsilon_1}$.
These bits, the sector record and the convention $\epsilon_1=+$ identify
exactly $\{z,\bar z\}$. The original sources are diagonal in the complete
commuting basis (C121.4). Their actual product weights, including the trace
of every unmatched sector, are precisely $\lambda_X$. Summing the two
possible global signs proves (C130.1), without assuming their values or
preparing either eigenstate. For $m=0$ the empty word has unit scalar
weight. Composition of the complete sector instruments, orthogonal gates,
complete measurements and discards gives finite real Kraus operators and
TP on the entire complex program algebra. QED.

**Theorem C-130.2 (Fixed-basis real attainment of the supplied optimum).**
For every finite $m\in\mathbb N_0$ and known $t,\eta\in[0,1]$, one common
processor from the real menu in C-129.1 attains, simultaneously for all four
original labels and arbitrary finite complex references,

$$
\boxed{e_m^{\mathbb R}(t,\eta)=e_m(t,\eta)=[c-D_m(t,\eta)]_+.}
\tag{C130.4}
$$

The unrestricted value and converse are reused from
[FIB noisy source programming minimax, Theorem 4.1](FIB_NOISY_SOURCE_PROGRAMMING_MINIMAX.md).
Its Definitions 1.1–1.3 use exactly the same $B,f,J,U_4$, original cut,
actual noisy copies, initial independence, target channel, unhalved norm
and full complex reference domain as C-129.1. There is no relabelled source
or pure-state replacement. The additional assertion here is its attainment
by the explicit real relative-sign instrument and real conditional responses
below, with whole-algebra CP/TP and the finite services of C-133.1.

Proof. Reuse the supplier's Proposition 2.2 signed expectations,
Proposition 2.3 presence probabilities and first-occurrence inequality,
and (4.2)–(4.5) feasible pair-specific diagonal budgets. In full notation,
put $D=D_m$, $Z_m=(1-2s/5)^m>0$, $T_m=1-Z_m$, and

$$
\begin{aligned}
r&=\begin{cases}0,&D=0,\\ \min\{1,c/D\},&D>0,\end{cases}
&Q&=\max\{s,r\},&q_{\emptyset}&=(s-QT_m)/Z_m,\\
q_d(z)&=\begin{cases}Q,&\mathsf H_d(z)=1,\\
q_{\emptyset},&\mathsf H_d(z)=0,\end{cases}
&h_d(z)&=\operatorname{sgn}(n_{d_+}(z)-n_{d_-}(z)).
\end{aligned}
\tag{C130.5}
$$

Here $\mathsf H_d$ indicates at least one outcome of pair $d$, not just a
nonzero signed count; a present tie still uses $Q$. The cited supplier
proves $0\le q_{\emptyset}\le s\le Q\le1$,
$0\le r|h_d(z)|\le q_d(z)$ and $\mathbb E_Xq_d=s$ under every label.
Both $q_d$ and presence are unchanged by $z\mapsto\bar z$, whereas
$h_d(\bar z)=-h_d(z)$. These are supplied quantitative budgets, not a
second optimization or a new claim about the already known unrestricted
value.

Pinch the data into $d_a,d_b,\{2\}$ with real projections. Apply
C-130.1 to the entire program batch. Conditional on a two-word orbit record
$z$ and data pair $d=(j,k)$, set $a_d=r|h_d(z)|$ and use a three-outcome
real coin of probabilities

$$
(a_d,\ q_d(z)-a_d,\ 1-q_d(z)).
\tag{C130.6}
$$

In the first branch, if $h_d=+1$ use $G_d$ from (C129.8), and if $h_d=-1$
replace its $R$ by $R^{\mathsf T}=R^{-1}$; then discard the retained qubit.
When $h_d=0$ this branch has zero weight. In the second branch measure the
data coordinate and leave it unchanged. In the third branch measure the
data coordinate $l$ and prepare each of the other four coordinates with
probability $1/4$. Discard the retained qubit in both latter branches.
For a fixed no-pair word use just the latter two branches with probabilities
$q_{\emptyset},1-q_{\emptyset}$. On data singleton $2$ discard all programs
and use the real classical channel with stay probability $s$ and each
wrong-output probability $(1-s)/4=\eta/5$.

Every coin probability is nonnegative and their sum is one. Each branch
is a real orthogonal gate and partial trace, or a real data-basis
measure-and-prepare channel. All zero-probability branches are retained.
Together with the complete instruments in C-130.1 and the complete data
pinching, this proves CP and TP on the entire joint complex algebra,
including unpromised programs, arbitrary data/program correlations and
arbitrary complex references. No conjugation or transpose is applied to
an unknown state.

To compute the action, let $\tau$ be any unnormalized complex qubit
operator. In the accepted branch the $jk$ multiplier before its coin
weight is
$\operatorname{tr}(\tau(R^{h_d})^{\mathsf T})
 =ih_d\operatorname{tr}(H\tau)$; its reverse multiplier is the negative.
Each diagonal multiplier is $\operatorname{tr}\tau$. The other branches
kill pair off-diagonals. Therefore the complete conditional response obeys

$$
\begin{aligned}
E_{ll}\otimes\tau&\longmapsto
 (\operatorname{tr}\tau)\left(q_dE_{ll}
 +\frac{1-q_d}{4}\sum_{v\ne l}E_{vv}\right),\quad l\in d,\\
E_{jk}\otimes\tau&\longmapsto
 irh_d(z)\operatorname{tr}(H\tau)E_{jk},\\
E_{kj}\otimes\tau&\longmapsto
 -irh_d(z)\operatorname{tr}(H\tau)E_{kj}.
\end{aligned}
\tag{C130.7}
$$

At $h_d=0$ the last two expressions are zero without using $R^0$ in a
nonzero branch. Insert (C130.1) and sum the orbits. For the diagonal the
sum is $\sum_z\lambda_X(z)q_d(z)=s$. For the coherence it is
$r\sum_{\{z,\bar z\}}h_d(z)(\lambda_X(z)-\lambda_X(\bar z))
 =r\sum_z\lambda_X(z)h_d(z)$. The supplier's signed expectations then give
on all $25$ complex data matrix units

$$
N_{\sigma X_a}=T_\eta(\sigma rD,0),\qquad
N_{\sigma X_b}=T_\eta(0,\sigma rD),\qquad rD=\min\{c,D\}.
\tag{C130.8}
$$

Every cross-sector matrix unit is killed by the data pinching, every
wrong-coordinate population is $(1-s)/4=\eta/5$, and the singleton has
the target populations. Thus (C130.8) is equality of full complex linear
maps, so it remains equality after tensoring every finite reference.
The existing exact norm (C121.8), equivalently the supplier's Proposition
3.2, gives error $c-rD=[c-D]_+$ on each label. The supplier's unrestricted
optimum and $e_m\le e_m^{\mathbb R}$ give (C130.4).

At $m=0$, $D=T_m=r=0$, $Z_m=1$ and $Q=q_{\emptyset}=s$; the circuit is
$T_\eta(0,0)$. At $c=0$ the same common target is exact without copies;
using the displayed circuit is also lawful. At $\eta=0$, $s=1$ and
$Q=q_{\emptyset}=1$, including $t=0,1$. At $\eta=1$ or $t=0$ one has
$c=D=r=0$. Every denominator in (C130.5) is either explicitly branched
at zero or strictly positive for finite $m$. Zero source probabilities,
$r=1$, $q_{\emptyset}=0$ and all singular endpoints require no limit.
The gate calibration depends only on the known parameters, never on the
unknown label or retained sign. QED.

## 131. Reused sharp values, first-hit comparison and a noise-only sufficient budget

**Proposition C-131.1 (Real attainment of the reused endpoints and exact threshold).**
The unrestricted values below are the supplier's Theorem 4.1,
Corollary 4.2, Proposition 7.4 and Proposition 11.1; C-130.2 attains them
within the explicit real menu:

$$
\begin{aligned}
e_0^{\mathbb R}=e_0&=c,\qquad
 e_1^{\mathbb R}=e_1=3c/5,\\
e_2^{\mathbb R}=e_2&=c(5+4s)/25,\\
e_m^{\mathbb R}=0&\ \Longleftrightarrow\ D_m\ge c.
\end{aligned}
\tag{C131.1}
$$

The real minimum prescribed-copy threshold is therefore exactly the
supplier's $\min\{m\ge0:D_m\ge c\}$, with $\min\varnothing=\infty$.
These are reused quantitative values, not additional uncovered minimax
results. The first-hit circuit remains an alternative explicit realization,
with error $E_m\ge[c-D_m]_+$ for every parameter; it is optimal at
$m=0,1,2$ and at every point where its error vanishes.

Proof. Apply C-130.2 directly to the cited supplier values and threshold.
For the first-hit comparison reuse its Proposition 2.3,
$D_m\ge(c/s)q_m$. If $q_m\le s$, then
$\min(c,D_m)\ge(c/s)q_m$; if $q_m\ge s$, then $D_m\ge c$.
Together with (C129.2) this gives the stated inequality and exact-regime
agreement. At $m=0$ the first-hit error is $c$; at $m=1$ it is $3c/5$.
At $m=2$, $q_2=4s/5-4s^2/25<s$ and hence
$E_2=c-(c/s)q_2=c(5+4s)/25$. These comparisons do not replace the
supplier's unrestricted optimization proof. The elementary first-hit
circuit uses neither the multi-qubit relative-sign stage nor calibration
of $D_m$; its larger error at some other copy counts is a stated
performance tradeoff, not a resource-minimality claim. QED.

**Theorem C-131.2 (An $\eta$-only sufficient exactness budget).**
If $\eta>0$ and $c>0$, all four original noisy channels are simultaneously
exactly programmed by the real construction C-129.2 whenever

$$
m\ge M_\eta:=\left\lceil
 \frac{\log(1-s)}{\log(1-2s/5)}\right\rceil,
\qquad s=1-4\eta/5.
\tag{C131.2}
$$

This is a sufficient first-hit budget independent of $t$. The exact
minimum prescribed-copy threshold is already the supplier's criterion
$D_m\ge c$, now attained by C-130.2 with real controls. Neither threshold
is a minimum physical acquisition, control or communication cost.
At $t=0$ or $\eta=1$ no program is needed. At $\eta=0$, the sharper statement remains exactly
C-122.1, including finite exactness for $0<t<1$ and the coherent-corner
obstruction $e_m(1,0)=(3/5)^m>0$ for every finite $m$.

Proof. The hypotheses imply $0<\eta<1$, hence $1/5<s<1$;
$\log(1-s)$ and $\log(1-2s/5)$ are finite negative numbers.
Condition (C131.2) is precisely $(1-2s/5)^m\le1-s$, or $q_m\ge s$.
In C-129.2 the accepted hit mass is then $h=s$, so its active coefficient
is $bh=(c/s)s=c$; directly (C129.4) equals
the target. Equivalently (C129.2) vanishes. At $c=0$ the target is the
single real channel $T_\eta(0,0)$, including both stated zero-copy cases.
At $\eta=0$ the relative-sign processor of C-130.2 attains the entire
reused exact minimax result C-122.1, whereas the first-hit error alone is
$E_m(t,0)=t(3/5)^m$. At $t=1$ this agrees with the strict finite-copy
obstruction and is not a finite exact imbit factory. Positive-definite
programs for $\eta>0$ still cannot reveal the label perfectly, as in
C-123.2; the exact noisy channel identity does not require doing so. QED.

## 132. What real classical records retain, and what quantum retention supplies

**Definition C-132.1 (Program-first real records with no quantum memory).**
A comparator first acts only on the $m$ program copies, using a real
instrument, real blank ancillas and no initial non-real resource. Its output
is a classical record and, if desired, real prepared states conditioned on
that record; it retains no quantum subsystem or correlation with the original
program for a later interaction with the data. Equivalently its record has
real positive effects $F_z$, $\sum_zF_z=I$, and every retained quantum
state is prepared from the record alone. It then chooses a label-independent
data channel from that record and the known parameters. Allowing arbitrary
complex later data channels only enlarges this comparison class. This is a
program-first restriction; it is not imposed on C-129 or C-130, nor on the
complex PVM record of C-121.4.

**Theorem C-132.2 (Sharp comparator error and exact real-record axis distance).**
For all $m,t,\eta$, the minimax unhalved diamond error of C-132.1 is exactly
$c$. Every such record has identical laws under $X_a,-X_a$, and identical
laws under $X_b,-X_b$, including adaptive real program-only instruments.
For one copy its law is identical for all four labels. For two copies,
the largest total variation between its laws for axis $a$ and axis $b$ is
exactly

$$
\delta_{\mathrm{axis},2}^{\mathbb R}=4c^2/25.
\tag{C132.1}
$$

This distinguishability is attained by a real-producing instrument with a
projective measurement on the two actual original copies. In particular, a retained
real statistic $Z_a\in\{-1,0,1\}$ has expectation $4c^2/25$ on axis $a$
and zero on axis $b$, for either sign. Neither this statistic nor any other
real classical record reveals the opposite sign for any finite $m$.
Compared with this comparator, C-130.2 reduces the worst-label channel error
by exactly $c-[c-D_m]_+=\min\{c,D_m\}$, strictly positive when $m\ge1$
and $c>0$.

Proof. Let

$$
D=(1-\eta)JJ^\dagger/5+\eta I_{25}/25,\qquad
A_a=JX_aJ^\dagger,\quad A_b=JX_bJ^\dagger.
\tag{C132.2}
$$

Here $D$ is real diagonal, $A_d$ is Hermitian and purely imaginary,
$A_d^{\mathsf T}=-A_d$, and $\rho_{\sigma X_d}=D+\sigma uA_d$.
Every real instrument effect $F_z$ is real symmetric, so

$$
\operatorname{tr}(F_z\rho_{X_d}^{\otimes m})
 =\operatorname{tr}(F_z(\rho_{X_d}^{\otimes m})^{\mathsf T})
 =\operatorname{tr}(F_z\rho_{-X_d}^{\otimes m}).
\tag{C132.3}
$$

Adaptive real Kraus products also have real symmetric effects and obey the
same identity. This equality of numbers uses transposition algebraically;
it does not implement transposition on the unknown quantum state. Any
later data channel selected by the record is consequently the same averaged
channel $N_d$ for the two opposite signs. Since their target distance is
$2c$ by (C121.8), the triangle inequality forces worst error at least $c$.
The real zero-program channel $T_\eta(0,0)$ attains $c$ simultaneously
for every label. Real output states depending only on the record cannot
alter this equality of induced channels. At one copy the term
$\operatorname{tr}(F_zA_d)$ vanishes, so the entire record law depends only
on $D$ and is also axis independent. Subtracting (C130.4) from the
attained comparator error $c$ gives the stated gap. It is positive for
$m\ge1,c>0$ because the reused $D_m\ge D_1=2c/5>0$.

More generally any real effect sees only the global-conjugation average

$$
\Omega_{d,m}=\tfrac12\left[
 (D+uA_d)^{\otimes m}+(D-uA_d)^{\otimes m}\right].
\tag{C132.4}
$$

At two copies
$\Omega_{a,2}-\Omega_{b,2}
 =u^2(A_a\otimes A_a-A_b\otimes A_b)$.
The two tensor terms have disjoint four-dimensional supports. Each has
eigenvalues $+1,+1,-1,-1$ on its support, because $A_d$ has eigenvalues
$+1,-1$ on its matching pair. Hence the half trace norm of this difference
is $4u^2$. Any POVM's classical total variation is bounded by this half
trace norm: for the set of positive probability differences use its sum
effect $0\le F\le I$, and bound $\operatorname{tr}(F\Delta)$ by the trace
of the positive part of the trace-zero Hermitian $\Delta$.

The bound is attained by the positive/negative spectral projections of
$A_a\otimes A_a-A_b\otimes A_b$, which are real matrices. Explicitly,
within the $d\otimes d$ matching sector identify $Je_j,Je_k$ with
$|0\rangle,|1\rangle$. The $+1$ vectors of $H\otimes H$ are
$(|00\rangle-|11\rangle)/\sqrt2$ and
$(|01\rangle+|10\rangle)/\sqrt2$; its $-1$ vectors are
$(|00\rangle+|11\rangle)/\sqrt2$ and
$(|01\rangle-|10\rangle)/\sqrt2$.
They are a real Bell basis, measurable using a real Hadamard and controlled
bit flip after the real matching-sector test. Assign positive axis-test
outcome to the $+1$ subspace for $a$ and the $-1$ subspace for $b$;
assign negative outcome to the other two subspaces, and retain the full
orthogonal complement as a third outcome. Its effect is the positive
spectral projector just described, and its probability difference between
axes is $4u^2=4c^2/25$. Recording the outcome and preparing a real blank
gives the required real-producing instrument with no quantum memory.
More explicitly, complete these eight real Bell vectors by the $617$
original computational vectors outside the two pair-product sectors.
For each vector $v$ take the Kraus matrix $|z(v),0\rangle\langle v|$,
where $z(v)$ is its assigned classical outcome and the second factor is
a fixed real blank. These real matrices have completeness operator $I_{625}$,
so the instrument is CP and TP on the entire two-program algebra, including
unpromised complex inputs and arbitrary references.

For the separate statistic $Z_a$, measure the three real projections

$$
\Pi_{a,\pm}=\tfrac12(P_{d_a}\otimes P_{d_a}
                    \pm A_a\otimes A_a),\qquad
\Pi_{a,0}=I-P_{d_a}\otimes P_{d_a},
\tag{C132.5}
$$

and record $\pm1,0$. On axis $a$ its probabilities are
$2w^2+2u^2,2w^2-2u^2,1-4w^2$; on axis $b$ they are
$2w^2,2w^2,1-4w^2$. These follow directly from
$\operatorname{tr}(P_{d_a}\rho_X)=2w$ and
$\operatorname{tr}(A_a\rho_{\sigma X_a})=2\sigma u$,
$\operatorname{tr}(A_a\rho_{\sigma X_b})=0$.
They are nonnegative even at $c=s$, sum to one, and give the stated
expectation. The single statistic's total variation is $2u^2$; the optimal
axis-test record using both sectors has the larger value $4u^2$ in
(C132.1). This distinguishes a statistic's signed expectation from optimal
classical distinguishability. Equation (C132.3) still excludes sign
information from either record. QED.

## 133. Finite real controls, fresh-block resources and applicability boundaries

**Proposition C-133.1 (Sufficient finite circuits and charged original-cut route).**
The processors of C-129.2 and C-130.2 admit finite realizations by the
real menu of C-129.1, with no externally supplied non-real ancilla.
A sufficient local ancillary supply for the relative-sign processor is
$m$ real blank qubits for extraction, $m$ four-valued sector pointers,
at most $m-1$ binary relative-sign pointers, a three-valued data-sector
pointer, a three-valued real response coin, and a five-valued data
preparation register. Unused blank qubits are discarded. For a branch with
$k\ge1$ matching-pair outcomes it uses exactly $k-1$ gates $V$ from
(C130.2); each consists of one controlled $R^{\mathsf T}$ and one real
Hadamard. Only one qubit is retained after that stage, and it is discarded
after the response. A classical record of the four-valued sectors and
relative bits uses at most $2m+\max\{m-1,0\}$ bits, besides the known
parameters and finite control computation. No minimum ancillary or
classical-memory cost is asserted.

For $n$ simulated data uses with a fresh size-$m$ batch per use, a
sufficient separated-laboratory contract places the processor at original
laboratory $A$, supplied with the data and the original $A$ program halves.
Each program's original $B$ half is transported to $A$ by one paid
noiseless five-dimensional wire. Each resulting entire five-dimensional
data output is then sent to $B$ by another paid noiseless wire, with the
fixed coefficient identifications. Thus the contract consumes $nm$ actual
original copies, $nm$ backward five-dimensional program-half wires and
$n$ forward five-dimensional data wires. Real local support embeddings
and their full-space extensions are supplied. This is a sufficient route;
it does not assert minimal transport, a qubit factorization for the new
joint instrument, LOCC implementability without those links, free phases,
a revealed source label or preshared ancillary entanglement.

Proof. A computational sector predicate is recorded by a real controlled
permutation into a blank pointer. The data pinching has three sectors.
The four program sectors are those of C-130.1; their projectors are
diagonal in the original basis, including the full $20$-dimensional
complement. On matching sector $d=(j,k)$ there is a concrete permutation
extension of extraction with a blank qubit: swap the two product basis
vectors $(Je_k,0)$ and $(Je_j,1)$ and leave all other basis vectors fixed.
It sends $Je_j\otimes|0\rangle$ and $Je_k\otimes|0\rangle$ to
$Je_j\otimes|0\rangle$ and $Je_j\otimes|1\rangle$. The remaining program
register is fixed on that sector and can be discarded. The choices of
$a$ or $b$ extraction are conditioned on the real sector record. Neutral
sectors are discarded without omitting their outcomes. These operations
have full real permutation/projective extensions, so they are not defined
only on promised matching vectors.

On the extracted qubits use exactly (C130.2). The controlled
$R^{\mathsf T}$ is a real two-level $\pi/2$ rotation in its enabled
subspace; the Hadamard is a real rotation and a sign reflection.
Measurements of the discarded qubits are computational. The remaining
relative bits determine the representative word by setting its first
pair sign to $+$; computing counts, presence, $h_d$ and the response
choice is finite classical feedforward, independent of $X$. An absent
pair and a present tie remain distinct records. At $k=0$ there is no
relative gate or retained qubit.

For any probabilities $p_1,p_2,p_3\ge0$ summing to one, two real two-level
rotations prepare a blank three-level register with amplitudes
$(\sqrt{p_1},\sqrt{p_2},\sqrt{p_3})$. First rotate amplitudes to
$(\sqrt{p_1},\sqrt{1-p_1},0)$, then split the second amplitude in the
ratio $p_2:p_3$, skipping this split when $p_1=1$. A computational
measurement gives exactly the response coin (C130.6). Its probabilities
are the known $r|h_d|$, $q_d-r|h_d|$ and $1-q_d$. The first branch uses
one controlled $R$ or $R^{\mathsf T}$ on the data pair and the retained
qubit, with identity on other data coordinates, then discards that qubit.
The second branch is data-basis measurement and retention of its coordinate.
The third branch uses data-basis measurement followed by a uniform real
preparation on the four other coordinates. The singleton and the fixed
no-pair record use the stated real measure-and-prepare probabilities.
Successive two-level rotations on a five-level blank prepare the required
nonnegative amplitudes; measuring that blank supplies the probabilities.
All outcomes, including zero-weight branches, are included. Reset means
discard and a fresh real blank, a declared dissipative service.

Thus every stage of C-130.2 is a specified finite real instrument or gate,
not solely a real Choi representation or an existence-only dilation.
Its exact calibrated constants are $1/\sqrt2$, the fixed orientations of
$R,R^{\mathsf T}$, the known $s,D_m,r,Q,q_{\emptyset}$ and the real square
roots in its coins. Exact knowledge of a formula does not physically
supply its amplitudes. The joint real gates, computational measurements,
blank registers, classical controls, discard/reset and these calibrations
remain supplied services. The real-operation definition does not make
such joint hardware native or free. If services are only approximate,
their errors must be separately bounded and included; an exact channel
identity requires the aggregate implementation error to vanish.

For the first-hit alternative, sufficient ancillas are a three-valued
data-sector pointer, at most $m$ binary program-test pointers, one blank
extraction qubit, a real acceptance coin and a five-valued preparation
register. Its program tests are the computational predicates $P_d,F_d$.
The same extraction permutation and controlled $R$ above implement each
accepted hit. The coin uses the known amplitude $\sqrt{h/q_m}$ when
$q_m>0$, and is deterministically rejected otherwise. Its failure and
singleton preparations are exactly (C129.10). This circuit requires the
known $s,q_m,h$ but not $D_m$ or relative-sign gates. Its CP/TP on every
unpromised joint input was proved in C-129.2.

The two-copy record instrument of C-132.2 is likewise realizable at $A$
after two paid five-dimensional transfers of the original $B$ halves.
A three-valued pointer records the $a\otimes a$, $b\otimes b$ or
complement sector. On either pair-product sector two blank qubits and
the extraction permutations extract the matching coordinates; a real
controlled bit flip and Hadamard measure the displayed real Bell basis
with a four-valued pointer. Coarse-grain to its three-valued axis outcome,
discard both qubits and prepare a real blank. The complement outcome is
retained. It consumes two actual copies, these joint controls and fixed
real calibration, with no non-real preparation or quantum program memory.

Transporting the original $B$ halves makes all specified joint operations
local at $A$ while retaining the original source and cut. The outgoing
identity wire and real embeddings are CPTP on their full spaces; all
records may remain at $A$. This proves the paid route. The supplier's
qubit/flag factorization concerns its own conditional complex response
instrument. No such factorization for these new joint real instruments is
inferred merely from equality of their promised effective channels.

For independent fresh batches conditional on the same fixed $X$, C-130.2
induces the tensor channel $N_X^{\otimes n}$ even on data entangled across
uses and with an arbitrary complex reference. Put
$\epsilon_m=[c-D_m]_+$. The channel telescoping identity and diamond norm
one of CPTP maps give block error at most $\min\{2,n\epsilon_m\}$,
and zero in an exact one-use regime. This reuses the supplier's
Theorem 10.1 tensor argument with the present real circuit. The first-hit
alternative separately has $\epsilon_m=E_m$. The same real calibration
settings may be reused classically. Reusing one retained qubit or
correlated quantum program memory across data uses does not establish
this tensor law or these fresh-batch costs; it requires its own complete
joint-channel proof. The old complex-PVM record and shared-calibration
services of C-124 keep their different hypotheses and paid operations.
No real-record conclusion of C-132 is imposed on those complex records.
At $m=0$ the backward wires and program ancillas vanish. At $c=0$ the
common target needs no copies; its controls and any forward transport
still belong to the declared contract. QED.

**Proposition C-133.2 (Correspondence, suppliers and mathematical ceiling).**
C-129–C-133 give conditional mathematical relations for the original
five-mode mixed source, original cut and full-complex programming task.
C-130 supplies a source-specific real relative-sign circuit attaining the
already known unrestricted value, not a new noisy minimax optimization.
C-129 supplies the simpler first-hit performance/budget tradeoff and
C-132 gives a sharp program-first real-record/quantum-memory separation.
These reduce the required external non-real phase resource by retaining
coherence from the actual quantum copies under the stated real joint
controls. They retain preparation of the actual batches, initial
independence, joint controls, calibration, ancillary reset and paid quantum
links as assumptions. No native operation claim or universal phase-reference
factory follows.

Proof. Every compression is a real restriction of the fixed original $J$.
Every retained state is calculated from $\rho_X$: (C129.6) for a first
hit and (C130.1) for an actual-word orbit. The proof uses the full source
law including its twenty unmatched modes, without a selected pure state,
a changed cut or an unknown-label-dependent service. C-130.2 applies the
retained imaginary sign through a real joint interaction with the data.
C-132 instead removes all such quantum retention and thereby loses the
opposite sign, although its two-copy record retains a quadratic axis
correlation. The complex eigenbasis PVM of C-121 has non-real effects and
sign-dependent laws, so its classical records are outside C-132.1.
The relative-sign instrument retains a quantum qubit as well as its real
record, and therefore is also outside that memory-discarding comparator.

The real-operation definitions and imaginarity framework are
`literature-attested` in
[Wu et al. (2021)](../../../Library/Quantum/wu2021imaginarity.md).
The supplied-imbit real implementation is `literature-attested` in
[Wu et al. (2024), Eq. (11) and its real-Kraus completeness argument](../../../Library/QuantumChannels/wu2024distributedimaginarity.md),
also arXiv:2301.04782v1, Appendix A, (22)–(23). It assumes the imbit
already supplied; it does not itself distill the unknown mixed source or
supply native joint gates. The complete-Kraus/all-complex-algebra framework
is the existing
[channel representation supplier](../../../Library/Quantum/watrous2018theory.md),
also represented by the repository's finite Kraus, Choi and stabilized
diamond interfaces. These mature ingredients and conjugation symmetry are
reused, not claimed as new generic resource theory.

The all-parameter value $[c-D_m]_+$, necessary-and-sufficient copy threshold,
$e_1=3c/5$, pair-specific diagonal budgets and actual-word first-occurrence
inequality are reused from
[FIB noisy source programming minimax, Sections 2–4, 7 and 11](FIB_NOISY_SOURCE_PROGRAMMING_MINIMAX.md).
The source-specific real extraction, relative-sign gates, finite real
conditional response, first-hit realization and real-record comparison
here are `repo-derived` ordinary consequences with the complete proofs
above. No literature-priority or originality clearance is claimed.

A pure two-qubit four-copy concentration theorem with a real Bell output
has a different source and output task. At $c>0$ the present source has
rank at least four at zero white noise and full rank $25$ at positive
white noise. Its coherent-corner rank is four and the reused finite-copy
obstruction is $e_m^{\mathbb R}(1,0)=(3/5)^m>0$. Pure-source concentration
cannot override this obstruction. A result about exact simulation of a
non-real unitary likewise does not by itself apply to these noisy
nonunitary channels. Single-carrier controllability and bounded classical
preparation from C-126–C-128 do not establish the present joint quantum
services. These are ordinary finite-dimensional proofs with an uncompiled
ceiling; no Lean/kernel certificate, minimum hardware or physical-cost
claim follows. QED.

## 追加锚（本行以下为增补区）
## 134. Two original copies: the attained BOTH-REAL spatial value

**Definition C-134.1 (The original-cut two-copy problem).**
Use the original source and target of
[FIB noisy source programming minimax, Definitions 1.1–1.3](FIB_NOISY_SOURCE_PROGRAMMING_MINIMAX.md)
without changing their coordinate identification. Thus
$B=(0,1,2,3,13)$, $f=(0\ 13)(1\ 3)$, $f(2)=2$,
$Je_j=|B_j,f(B_j)\rangle$, and the two active coefficient pairs are
$d_a=(0,4)$ and $d_b=(1,3)$. Put

$$
\begin{aligned}
X_a&=i(E_{04}-E_{40}),& X_b&=i(E_{13}-E_{31}),\\
c&=(1-\eta)t,&u&=c/5,\\
s&=1-4\eta/5,&w&=s/5,&n&=\eta/25.
\end{aligned}
\tag{C134.1}
$$

Here $t,\eta\in[0,1]$ are known. The one unknown label
$X\in\{X_a,-X_a,X_b,-X_b\}$ is fixed throughout the batch. The
actual two programs are conditionally iid copies of

$$
\rho_X=(1-\eta)J(I_5+tX)J^\dagger/5+\eta I_{25}/25,
\tag{C134.2}
$$

initially independent of the entire data/reference state. All twenty
unmatched white-noise modes remain present. The target on the entire
complex algebra is

$$
\Phi_X(Y)=(1-\eta)(I_5+tX)\circ Y
                  +\eta\operatorname{tr}(Y)I_5/5.
\tag{C134.3}
$$

Alice holds the complex five-dimensional data and $A_1,A_2$; Bob holds
$B_1,B_2$ and the output under the prescribed fixed identification.
A BOTH-REAL competitor is one label-independent finite-round two-way
LOCC processor, with every local Kraus matrix real in the original
bases. Arbitrary finite real local computational ancillas, the supplied
calibrated real local controls, discard/reset, shared classical randomness
and classical messages are allowed. The processor must be CP and TP on
the entire joint algebra, including off-promise and correlated inputs.
Evaluation uses the stipulated independent programs. Data and every
untouched finite reference remain complex. Write

$$
E_{2,\mathrm{RLOCC}}
 =\inf_{\mathcal P}\ \max_{X\in U_4}
 \|\mathcal P(\,\cdot\,\otimes\rho_X^{\otimes2})-\Phi_X\|_\diamond,
\tag{C134.4}
$$

with the unhalved diamond convention of the supplier. There is no quantum
wire, additional entanglement, supplied imbit, revealed label, physical
conjugation/transpose gate or postselection in this menu.

**Theorem C-134.2 (Exact attained spatial optimum).**
For every $t,\eta\in[0,1]$,

$$
\boxed{E_{2,\mathrm{RLOCC}}=\frac{c(45-12\eta)}{125}.}
\tag{C134.5}
$$

One common finite-round real local protocol attains this error for each
of the four labels. The converse covers every competitor in C-134.1,
without a program-first, Schur, record-only, first-hit, fixed-round-count
or ancillary-dimension restriction. The same infimum holds for the
closure of this class in the induced channel norm, since the bound is
continuous and the displayed value is already attained at finite rounds.
This does not identify a general complex separable or PPT optimum.

The unrestricted supplier's Proposition 11.1 gives
$e_2=c(45-16\eta)/125$. Consequently the spatial real restriction has the
exact excess

$$
E_{2,\mathrm{RLOCC}}-e_2=4c\eta/125.
\tag{C134.6}
$$

At $\eta=0$ the value is $9t/25$; at $c=0$ it is zero. At
$t=1,\eta=1/2$ the restricted and unrestricted values are respectively
$39/250$ and $37/250$. These are channel errors, not label-identification
probabilities or halved trace distances.

Proof. C-135.1 supplies a finite matrix certificate for the universal
converse in C-136.1. C-137.1 supplies an actual finite-round real local
instrument with the matching full-complex channel action. Both statements
include the parameter endpoints. Their combination proves (C134.5);
subtracting the credited unrestricted value gives (C134.6). Continuity
extends the lower bound to limits of induced four-channel tuples, while
the same finite protocol remains an admissible upper bound. QED.

## 135. A locally transposed Choi certificate for the noise term

**Lemma C-135.1 (Two-pair real local certificate).**
For this lemma only, identify each selected local pair with the real
computational basis $|0\rangle,|1\rangle$. This is a local basis
identification within the original support, not a new spatial cut. On one
such bipartite pair put

$$
\begin{aligned}
A&=i(|00\rangle\langle11|-|11\rangle\langle00|),\\
P&=|00\rangle\langle00|+|11\rangle\langle11|,\\
Q&=|01\rangle\langle01|+|10\rangle\langle10|,\\
C&=A^{T_A}
  =i(|10\rangle\langle01|-|01\rangle\langle10|),\\
R_n&=A\otimes Q+Q\otimes A.
\end{aligned}
\tag{C135.1}
$$

Let $\mathcal F$ be any CPTP map admitting a product Kraus decomposition
with every local factor real, from these two bipartite pairs to one output
qubit $r$ at Alice and one output qubit $o$ at Bob.
In particular it may be any finite-round real LOCC map with arbitrary
finite real local ancillas. For the Hermitian output test

$$
W=i(|00\rangle\langle11|-|11\rangle\langle00|)_{ro},
\qquad \|W\|_\infty=1,
\tag{C135.2}
$$

one has

$$
\operatorname{tr}\bigl(W\mathcal F(R_n)\bigr)\le4.
\tag{C135.3}
$$

The assertion also holds for every CPTP map whose Choi matrix is
invariant under transposition of Alice's entire input/output block.
That larger class is used only for the converse. Neither $R_n$ nor the
dual operator below is asserted to be a state.

Proof. Order the six Choi bits as $(r,a_1,a_2,b_1,b_2,o)$; write
$a=(a_1,a_2)$ and $b=(b_1,b_2)$. The unnormalized Choi matrix is

$$
M_{rabo,\,sa'b'p}
  =\bigl[\mathcal F(|ab\rangle\langle a'b'|)\bigr]_{ro,sp}.
\tag{C135.4}
$$

It is positive, and $\operatorname{tr}_{r,o}M=I_{ab}$. Denote by
$\Gamma$ transposition of the first three bits $(r,a_1,a_2)$, keeping
the Bob block $(b_1,b_2,o)$ fixed. A real product Kraus matrix has a real
vectorized factor on each side, whose rank-one projector is symmetric.
Its Choi contribution is therefore invariant under $\Gamma$. Sums of
such contributions give $M^\Gamma=M$ for real separable maps. For a
finite adaptive real LOCC protocol, refine the local Kraus records and
final discards. Each complete history has a product of real local Kraus
matrices, so the same conclusion holds. Real blank ancillas and real
mixed ancillary preparations can be absorbed into these local Kraus
matrices; real spectral decompositions suffice for the mixed case.
Classical randomization preserves the linear identity. If an instrument
uses an integral of histories, the finite-dimensional Choi identity is
preserved under that integral as well. No bound on the history count,
round count or finite ancillary dimensions has been imposed.

On the program bits, in the order $(a_1,a_2,b_1,b_2)$, define

$$
Z=Q\otimes Q+\tfrac12(A\otimes A+C\otimes C),
\tag{C135.5}
$$

where tensor factors on the right first refer to copies
$(a_1b_1),(a_2b_2)$ and are then reordered as stated. Thus
$Z^{T_{a_1a_2}}=Z$ and $\operatorname{tr}Z=4$. Let $\widehat Z$ act as
$Z$ on the four program bits and as identity on $r,o$. Define $H$ by

$$
H_{rabo,\,sa'b'p}
 =W_{ro,sp}(R_n)_{a'b',ab}.
\tag{C135.6}
$$

It is a real symmetric matrix and
$\operatorname{tr}(MH)=\operatorname{tr}(W\mathcal F(R_n))$.
The following six real vectors, with binary strings in the six-bit order
above, give a positive certificate:

$$
\begin{aligned}
v_1&=|000110\rangle-|011000\rangle,\\
v_2&=|000111\rangle-|011001\rangle-|101100\rangle-|110010\rangle,\\
v_3&=|001101\rangle+|010011\rangle+|100110\rangle-|111000\rangle,\\
v_4&=|001100\rangle+|010010\rangle,\\
v_5&=|101101\rangle+|110011\rangle,\\
v_6&=|100111\rangle-|111001\rangle,\\
S&=\sum_{h=1}^6|v_h\rangle\langle v_h|\ \ge0.
\end{aligned}
\tag{C135.7}
$$

Their exact identity is

$$
\frac{S+S^\Gamma}{2}
   =\widehat Z-\frac{H+H^\Gamma}{2}.
\tag{C135.8}
$$

For an entrywise verification, the only nonzero entries needed in the
one-copy matrices are
$A_{00,11}=i$, $A_{11,00}=-i$,
$C_{10,01}=i$, $C_{01,10}=-i$ and
$Q_{01,01}=Q_{10,10}=1$. Insert these entries in (C135.5)–(C135.6),
expand the six rank-one matrices in (C135.7), and swap the first three
row bits with the first three column bits for $\Gamma$.
Equivalently, with $A=iT$, $C=iT_c$ and $W=iU$, all of
$T,T_c,U$ real antisymmetric, the entries to check are

$$
\begin{aligned}
(2Z)&=2Q\otimes Q-T\otimes T-T_c\otimes T_c,\\
H_{rabo,sa'b'p}
 &=U_{ro,sp}(T\otimes Q+Q\otimes T)_{ab,a'b'},\\
2(S+S^\Gamma)
 &=2\widehat Z+2\widehat Z^\Gamma-2(H+H^\Gamma).
\end{aligned}
\tag{C135.9}
$$

All entries in the last equality are integers. These expansions establish
(C135.8); the vectors' disjoint supports also give
$v_h^T v_k=0$ for $h\ne k$ and squared norms $2,4,4,2,2,2$.
The certificate uses no eigenvalue approximation or optimizing premise.

Partial transpose is self-adjoint for the trace pairing. Pairing
(C135.8) with $M=M^\Gamma$ and using trace preservation gives

$$
\begin{aligned}
\operatorname{tr}(W\mathcal F(R_n))
 &=\operatorname{tr}(M\widehat Z)-\operatorname{tr}(MS)\\
 &=\operatorname{tr}Z-\operatorname{tr}(MS)\le4.
\end{aligned}
\tag{C135.10}
$$

The last inequality follows from positivity of $M$ and $S$. All
transpositions here are algebraic operations in a converse certificate;
none is an allowed gate on an unknown state. QED.

## 136. Universal converse on the full noisy source

**Theorem C-136.1 (Converse without a processor subclass restriction).**
Every processor allowed in C-134.1 has worst-label unhalved diamond error
at least $c(45-12\eta)/125$.

Proof. Fix either original pair $d=(j,k)$ and its opposite labels
$X=\pm X_d$. In the full $25$-dimensional program space write

$$
\rho_\pm=D\pm u A_d,\qquad
D=(1-\eta)JJ^\dagger/5+\eta I_{25}/25,
\tag{C136.1}
$$

where $A_d=i(|jj\rangle\langle kk|-|kk\rangle\langle jj|)$ in the
fixed coefficient identifications. Its notation $|jj\rangle$ means the
original vector $|B_j,f(B_j)\rangle$. On the four-dimensional local
pair product, identify $A_d,P_d,Q_d$ with $A,P,Q$ of C-135.1 and put

$$
D=wP+nQ+D_{\rm out},\qquad
r=\operatorname{tr}D_{\rm out}=1-2w-2n.
\tag{C136.2}
$$

Here $D_{\rm out}\ge0$ is diagonal and supported outside that entire
local pair product. It retains three other matching modes and eighteen
unmatched modes. The other two unmatched modes are exactly $Q$; thus
none of the twenty white-noise modes has been removed.

Prepare the fixed real data/reference state

$$
|\Omega_d\rangle
  =(|0\rangle_R|e_j\rangle_D+|1\rangle_R|e_k\rangle_D)/\sqrt2
\tag{C136.3}
$$

at Alice and feed the data to the given processor. Keep $R$ untouched.
This defines a CPTP real local map $\mathcal F$ from the entire two-copy
program algebra to $R$ and Bob's output. This deduction uses the
processor's full-algebra CP/TP requirement, not merely its behavior on
promised independent inputs. Give the output the Hermitian test

$$
W_d=i(|0,j\rangle\langle1,k|-|1,k\rangle\langle0,j|),
\qquad\|W_d\|_\infty=1.
\tag{C136.4}
$$

This test belongs to the mathematical norm evaluation; it is not a
processor measurement or an additional non-real resource. The target
expectations on (C136.3) are $+c,-c$. If the two respective
diamond errors are $\epsilon_+,\epsilon_-$ and

$$
g=\operatorname{tr}\left[
 W_d\mathcal F\!\left(\frac{\rho_+^{\otimes2}-\rho_-^{\otimes2}}2\right)
 \right],
\tag{C136.5}
$$

then testing these particular complex-output reference states gives
$(\epsilon_++\epsilon_-)/2\ge c-g$. This uses the unhalved trace-norm
duality with an operator of norm one; no extra factor $1/2$ is introduced
in either diamond error.

The iid expansion with the same fixed sign cancels the quadratic term:

$$
\frac{\rho_+^{\otimes2}-\rho_-^{\otimes2}}2
 =u(A\otimes D+D\otimes A)
 =uwR_w+unR_n+uR_{\rm out},
\tag{C136.6}
$$

where
$R_w=A\otimes P+P\otimes A$ and
$R_{\rm out}=A\otimes D_{\rm out}+D_{\rm out}\otimes A$.
These are Hermitian operators used in a linear calculation, not
alternative selectable program states.

On $P\otimes P$, $A$ has eigenvalues $1,-1$ and $P$ is the identity;
therefore $R_w$ has eigenvalues $2,0,0,-2$ and trace norm $4$.
The two terms in $R_{\rm out}$ have orthogonal supports and each has
trace norm $2r$, so $\|R_{\rm out}\|_1=4r$. Trace-norm contraction of
the full CPTP map $\mathcal F$ bounds their contributions to $g$ by
$4uw$ and $4ur$.

For the remaining term restrict each local input to its selected real
pair. This is a local isometric restriction of the domain of
$\mathcal F$, still a CPTP real local map. Compress Bob's output to the
selected pair, sending every other output coordinate to a fixed real
qubit blank and discarding the corresponding coherences. Explicit
Kraus matrices are the pair identification and one
$|0\rangle\langle e_\ell|$ for each $\ell\notin\{j,k\}$.
This real CPTP compression leaves the $W_d$ expectation unchanged.
The resulting map has exactly the interface of C-135.1, so the noise
contribution is at most $4un$. The restriction of the interface has
not restricted any internal ancilla, adaptive control or round count.
Consequently

$$
\begin{aligned}
g&\le4u(r+w+n)=4u(1-w-n)\\
 &=\frac{c(80+12\eta)}{125},\\
\max_{X\in U_4}\epsilon_X
 &\ge\frac{\epsilon_++\epsilon_-}{2}
 \ge c-g\ge\frac{c(45-12\eta)}{125}.
\end{aligned}
\tag{C136.7}
$$

The construction of the test and the certificate is identical under the
real local relabeling for $d_a$ or $d_b$. The proof bounds every original
competitor, even when it interacts with the data before any program
measurement and retains both quantum programs adaptively. For $u=0$
the same inequalities give the required zero lower bound without a
division or limiting argument. QED.

## 137. A common attained finite-round real local instrument

**Theorem C-137.1 (Whole-algebra original-cut attainment).**
The following single protocol, independent of $X$, is finite-round
BOTH-REAL LOCC, is CP/TP on its entire complex joint input algebra,
and induces the error in (C134.5) for all four labels and every finite
untouched complex reference.

Proof. Alice first measures the three data sectors $d_a,d_b,\{2\}$
using their real computational projectors. This removes only
cross-sector coherences, which every target (C134.3) already sends to
zero. Alice communicates the sector to Bob. In singleton sector $2$,
Bob prepares the diagonal distribution with probability $s$ on $2$ and
$\eta/5$ on each other coordinate. Both programs are discarded.

In pair sector $d=(j,k)$, both parties locally test each copy, in order,
for membership in their respective two-dimensional supports for $d$.
The Alice support is $\{|B_j\rangle,|B_k\rangle\}$ and the Bob support
is $\{|f(B_j)\rangle,|f(B_k)\rangle\}$. They communicate their binary
membership results. A copy is accepted precisely when both tests say
inside. This is the local pair-product test, retaining all four product
modes; it is not a nondestructive test for matching coordinates.
On the first accepted copy they use the Bell instrument below. Earlier
failed copies and the unused copy are discarded. If neither copy is
accepted they use the real fallback below. Every failure outcome is
retained in this channel.

On either copy the acceptance probability, the same for all four labels,
is

$$
q=2(w+n)=\frac{10-6\eta}{25},\qquad
\frac4{25}\le q\le\frac25.
\tag{C137.1}
$$

The unnormalized accepted state, in order $00,01,10,11$, is

$$
\tau_{X,d}=\operatorname{diag}(w,n,n,w)
        +iv_{X,d}(|00\rangle\langle11|-|11\rangle\langle00|),
\tag{C137.2}
$$

where $v_{\sigma X_d,d}=\sigma u$, while $v_{X,d}=0$ when $X$ belongs
to the other pair. These are descriptions of the actual state branches;
no control is conditioned on $v_{X,d}$ or on an inferred label.

Identify the retained local pairs with bits. Let

$$
Z_2=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
X_2=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
R_2=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\tag{C137.3}
$$

Alice measures data and her accepted half in the four real Bell vectors
$|\beta_V\rangle=(I\otimes V)(|00\rangle+|11\rangle)/\sqrt2$.
She sends the outcome to Bob, who applies the correction in this table:

| $V$ defining Alice's Bell vector | Bob's real correction $C_V$ |
| --- | --- |
| $I_2$ | $I_2$ |
| $Z_2$ | $Z_2$ |
| $X_2$ | $R_2$ |
| $R_2$ | $X_2$ |

All four matrices are real orthogonal. The corrections are independent
of the unknown sign, axis and $t$. A direct contraction of each Bell
vector with $Y\otimes\tau_{X,d}$, followed by $C_V$, gives one fourth
of the following unnormalized channel, for every $Y\in M_2(\mathbb C)$:

$$
\mathcal T_{\tau}(Y)=
\begin{pmatrix}
2wY_{00}+2nY_{11}&2iv_{X,d}Y_{01}\\
-2iv_{X,d}Y_{10}&2nY_{00}+2wY_{11}
\end{pmatrix}.
\tag{C137.4}
$$

For example the $I_2$ Bell outcome contracts the $(a,b),(a',b')$
entry of $\tau$ with $Y_{aa'}/2$. The $Z_2$ outcome changes both
off-diagonal signs, canceled by $C_V=Z_2$. The $X_2$ outcome interchanges
the data coordinates; $R_2 E_{10}R_2^T=-E_{01}$ cancels its additional
imaginary sign. The $R_2$ outcome has that additional minus in the Bell
vector already and is corrected by $X_2$. Their diagonal swaps are the
same in the last two cases. This proves (C137.4) on all four matrix units,
including the two independent complex off-diagonal units. Its trace is
$q\operatorname{tr}Y$. The Bell basis is complete, so its four outcomes
are all included.

Conditional iid programs imply that the first-copy acceptance contributes
$\mathcal T_\tau$ and the second-copy acceptance after first failure
contributes $(1-q)\mathcal T_\tau$. Define the paid hit populations and
the total failure probability by

$$
\alpha=2w(2-q),\qquad
\beta=2n(2-q),\qquad
z=(1-q)^2=1-\alpha-\beta.
\tag{C137.5}
$$

For a measured input coordinate $\ell\in\{j,k\}$ in the total-failure
branch, Bob prepares output $r$ with probabilities

$$
p_{r\mid\ell}=
\begin{cases}
(s-\alpha)/z,&r=\ell,\\
(\eta/5-\beta)/z,&r\in\{j,k\}\setminus\{\ell\},\\
(\eta/5)/z,&r\notin\{j,k\}.
\end{cases}
\tag{C137.6}
$$

These are lawful at every endpoint. Indeed $z\ge9/25>0$,
$\alpha\le4s/5\le s$, and
$\beta\le4\eta/25\le\eta/5$. Their sum is
$[s-\alpha+\eta/5-\beta+3\eta/5]/z=1$.
This fallback measures the data coordinate at Alice, sends that classical
coordinate, and prepares a real diagonal state at Bob. Its Kraus matrices
on the pair are $\sqrt{p_{r\mid\ell}}|r\rangle\langle\ell|$ with the
measurement and preparation spatially separated by that classical message.
No data phase or quantum carrier is supplied by this branch.

The hit branches and (C137.6) give exactly the target diagonal for every
input coordinate: the correct coordinate has population
$\alpha+(s-\alpha)=s$, its pair partner has
$\beta+(\eta/5-\beta)=\eta/5$, and each other output has $\eta/5$.
For either active label the only nonzero off-diagonal coefficient is

$$
g_2=2u(2-q)=4u(1-w-n)=\frac{c(80+12\eta)}{125},
\tag{C137.7}
$$

with the source's sign; the other pair coefficient is zero. The singleton
and cross-sector actions were already specified. Thus the induced map is
exactly the supplier's response $T_\eta(\sigma g_2,0)$ or
$T_\eta(0,\sigma g_2)$, on every complex matrix unit.
The exact reference-norm identity in the supplier's Proposition 3.2
therefore gives, without a new norm calculation,

$$
\|N_X-\Phi_X\|_\diamond=c-g_2
               =\frac{c(45-12\eta)}{125}
\quad\text{for each }X\in U_4.
\tag{C137.8}
$$

Equality of these complex-linear maps remains equality after tensoring
any finite untouched reference. In particular imaginary data coherences
have not been replaced by their real parts.

For completeness, every operation used above has a full-space real Kraus
implementation. The data sector projectors sum to $I_5$. Each local
membership instrument consists of a real projector and its complement.
Failure records can be coarsened only after their subsequent actions
have been specified identically; their probabilities are never dropped.
Alice's four Bell projectors on the selected pair product can be completed
by the twenty-one computational projectors outside it. The corrections
extend as identity on the three complementary Bob coordinates. Discard
has computational-bra Kraus matrices. Fallback measurement and preparation
have the real Kraus matrices just displayed, whose squared weights sum
to one. The singleton preparation is the same kind of instrument.
Real computational pointers and controlled classical feedforward implement
these branches with their complete complements. A finite composition of
these specified instruments is CP and TP on all complex joint inputs,
including arbitrary correlations among data and both programs. This
argument does not infer implementability from Choi positivity, and it
does not use the independent-input promise to establish CP/TP.
The promise is used only to evaluate the induced channel and its
$(1-q)$ factor. QED.

## 138. Resources, reuse and the ordinary-proof boundary

**Proposition C-138.1 (Sufficient original-cut resource contract).**
C-137.1 consumes or discards exactly the two supplied actual source
copies and sends only classical messages across the original cut.
A sufficient finite ancillary supply consists of a three-valued data
sector pointer, two binary membership pointers at each party, a
four-valued Bell pointer at Alice, and a five-valued real preparation
register and five-dimensional output blank at Bob. Pointers may instead
be reset and reused. There is at most one Bell measurement, after the
accepted copy is selected. All used or unused program registers are
discarded at the end. No imbit, extra entangled pair or transmitted
quantum system is required by this mathematical protocol.

One explicit message schedule is: Alice sends her three-valued sector;
for each examined copy she sends her membership bit and Bob replies with
the acceptance bit; on acceptance Alice sends her four-valued Bell
outcome, and on total failure she sends her binary data coordinate.
The singleton sector needs only the sector message. Thus at most six
one-way messages, representable using at most eight binary bits in the
longest branch, suffice; there is no imposed message-budget constraint
or optimality claim about these counts.

Proof. Sector and membership predicates are local computational
projections. A Bell measurement is a real controlled bit flip and real
Hadamard followed by computational measurement on the selected local
pairs. The displayed $X_2,Z_2,R_2$ corrections and their full-space
extensions are calibrated real local controls. The fallback probabilities
are known functions of $\eta$ alone, so neither its controls nor the Bell
corrections require $X$ or a measured sign. A real five-level rotation
can prepare amplitudes $\sqrt{p_{r\mid\ell}}$ from a blank; computational
measurement and conditional basis preparation give (C137.6).
The singleton uses the analogous known probabilities. This is a
specified finite local circuit using the supplied menu. Counting its
pointers and messages gives the bounds above. Discard/reset and exact
preparation of real blanks remain supplied dissipative services. QED.

The source preparation, delivery of each original $A$ and $B$ half,
conditional iid law, initial independence from all data/reference,
fixed original basis identifications, exact known calibration, local
joint access to Alice's data and either of her halves, local computational
measurements, classical links and output acquisition remain explicit
services. The result does not construct native hardware or prepare the
unknown source from a classical description. The abstract finite circuit
attains a mathematical menu optimum; no experimental physical realization,
minimum acquisition cost or free all-copy law is asserted. Approximate
controls or an imperfect source require additional error estimates.
Fresh independent blocks can reuse the real classical settings; reusing
these same two quantum copies does not establish independent channel uses.

**Statement C-138.2 (Suppliers and claim ceiling).**
The original source, target, full-complex reference convention,
unrestricted value and exact response-channel norm are reused from
[FIB noisy source programming minimax, Sections 1, 3 and 11](FIB_NOISY_SOURCE_PROGRAMMING_MINIMAX.md).
C-129–C-133 supply the earlier real joint-processing and real-record
boundaries. Their paid transfer of Bob's halves to Alice is not used in
C-137.1, and their joint matching extraction is not assumed local here.
The present converse is a channel/reference test with an explicit
transpose-invariant Choi certificate, not a record-discrimination bound.
The upper bound is an explicit local Bell instrument and its complete
noise/failure accounting, not a Choi-only implementation assertion.

[Wu et al., Communications Physics 7, 171](https://doi.org/10.1038/s42005-024-01649-y),
Methods, “Properties of LRCC operations,” Eqs. (37)–(39), supply the
mature local-transpose Choi condition and distinguish LRCC (both sides
real) from LQRCC (Alice unrestricted). Their supplied-imbit real
implementation, already cited in
[the existing literature note](../../../Library/QuantumChannels/wu2024distributedimaginarity.md),
is a different resource contract and is not an extra input here. The
necessary Choi condition is re-established in C-135.1 for this map
interface; it is not treated as sufficient for LOCC implementation.
The six-vector certificate, its original-source decomposition and its
matching simultaneous local channel construction are `repo-derived`
ordinary mathematical synthesis. No literature-priority or global
novelty clearance is claimed.

[Pirandola, arXiv:1711.09909v3, Criterion 4](https://arxiv.org/abs/1711.09909v3)
states teleportation simulation under the required covariance/correction
hypotheses. The actual Bell contraction and sign-independent real
corrections in C-137.1 provide the source-specific bridge used here.
The bare identity of the full five-mode source with a channel Choi
state would not provide that bridge.
[arXiv:2603.12130v1](https://arxiv.org/abs/2603.12130v1) concerns
entanglement-assisted bipartite channel discrimination and PPT tester
relaxations; [arXiv:2604.06412v1](https://arxiv.org/abs/2604.06412v1)
concerns local discrimination of five three-qubit pure states.
Neither supplies the mixed-source programmable-channel optimum proved
here. A separable/PPT relaxation may give a converse; an explicit legal
protocol is still needed for attainment.

The repository's finite Kraus/Choi and five-mode real-response suppliers,
including the private real-pairing arguments in
`D5/S3/Quantum/Fibers/FiveModeRealResponse.lean`, concern the mature
interfaces and observation fibers. Its finite-sector channel-optimality
modules concern a different sector encoding/target problem. The selected pinned
mathlib positive-matrix and physlib Kraus/Choi interfaces are mature
algebraic ingredients; no current compiled application of them to
C-134–C-137 is claimed.
These sections are complete ordinary finite-dimensional proofs with an
explicit uncompiled ceiling. They make no Lean/kernel, formal-freeze,
empirical hardware or exhaustive-search claim. They settle this precise
two-copy spatial question and do not complete the continuing
quantum-focused AURIC FIB ATOM research objective.

## 追加锚（本行以下为增补区）
