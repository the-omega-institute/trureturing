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
