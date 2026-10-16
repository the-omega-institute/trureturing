# Native complete-continuation joint record and quantum payload

## 29. The fixed channel and its original winding phase

**Convention 29.1 (source and conditional scope).** This is a same-topic
continuation of [Complete Continuation Distinguishability Gap][CG],
§§13–28; its numbering continues that volume. The premises are its
isolated point $u_*$, strict coefficient enclosures and the particular
complete channel $\widehat\Phi_*$ of (CG.135)–(CG.142). These are credited
ordinary mathematical premises. The constructions and bounds below are
ordinary source-conditional mathematics, without new kernel evidence.
Neither the complete-channel uniqueness of an optimizer nor a native
implementation of this particular channel is a premise or conclusion.

Use the calibrated isometry $E:\mathbb C^3\to\mathbb C^5$ with columns
$(|+\rangle,|-\rangle,|2\rangle)$ and let $P=EE^\dagger$. The twelve
inputs remain the ACTUAL normalized reached-old-live-cut specimens

$$
\begin{aligned}
\rho_{y,e,n}&=U_{e,n}a_ya_y^TU_{e,n}^\dagger,
&U_{e,n}&=\operatorname{diag}(e,n,1),\\
p_y&=\left(\frac y{128},\frac{64-y}{128},\frac12\right),
&(a_y)_i&=\sqrt{p_{yi}},\\
y&\in\{5,16,27\},& e,n&\in\{1,-1\}.
\end{aligned}
\tag{JR.1}
$$

Their original parameters are $x=y/256$, $e=(-1)^{\beta/\pi}$ and
$n=e(-1)^m$. In particular $en=(-1)^m$: the phase read below is the
original winding parity, not a newly installed label. The ideal live
block remains $U_{e,n}B_yU_{e,n}^\dagger$, with $B_y$ of (CG.111).
Its five ideal failure measures remain $w_\ell f_y(t)dt\,P_f$, where
$w=(0,1/4,1/2,1/4,0)$ and $f_y(t)=6y/(y+6t)^2$ on $[0,1]$.
All comparisons retain HALF the full cq trace norm, with every live
coherence and every singular, abort, wrong-support and zero-ideal sector.
There is no acceptance normalization, height prior or reach-mass prior.

Abbreviate the REAL coefficients of (CG.134) by

$$
\begin{aligned}
D&=K_0=\operatorname{diag}(h_0,h_1,h_2),\\
T&=K_{01}=a|0\rangle\langle1|+b|1\rangle\langle0|,\\
S&=K_{02}=c|0\rangle\langle2|+d|2\rangle\langle0|,\\
M&=\operatorname{diag}(0,m_1,m_2),
&\kappa&=h_0a+h_1b,\qquad q_y=\sqrt{p_{y0}p_{y1}}.
\end{aligned}
\tag{JR.2}
$$

The scalar $h_0$ in $D$ is a Kraus amplitude. To avoid conflating it
with the time density called $h_0(t)$ in [CG], write that density here as
$g(t)=2/(1+t)^2$. Thus the fixed qutrit-input channel has live map
$A\mapsto DAD^\dagger+TAT^\dagger+SAS^\dagger$ and failure CP measures
$w_\ell g(t)dt\,\operatorname{tr}(MA)P_f$. Its five-mode completion adds
$g(t)dt\,\operatorname{tr}((I_5-P)A)P_f$ at original failure label $2$,
compresses all supported branches by $E^\dagger$, and kills cross-support
entries. These descriptions specify the same map on all complex matrices.

**Proposition 29.2 (coefficient signs and nonsingular phase mixtures).**
The amplitudes $h_i,a,b,c$ in (JR.2) are positive, and $d\ne0$. Moreover

$$
0<\kappa<\frac14,\qquad
h_0h_1-s^2ab>\frac{677}{1000}\quad(0\leq s\leq1).
\tag{JR.3}
$$

Proof. The positive first pivots in (CG.117) give $h_0,a,c>0$.
Theorem 22.1's enclosures $H_{01}>695/1000$ and $H_{02}>796/1000$
give $h_1,h_2>0$, since $H=hh^T$. The off-diagonal entries of
$Q^{01}$ and $Q^{02}$ are respectively $\eta_1N_{01}$ and $\eta_2N_{02}$.
For $N_{01}$ both terms in (CG.112) are strictly positive: its two
rank-one vectors have positive coordinates $0,1$. Hence $b>0$.
The other transfer satisfies $d^2=(Q_*^{02})_{11}>0$ by
(CG.166); its sign is immaterial to every conclusion below.

Only $h_i,a,b>0$ enter the conclusions. Rank one gives
$h_0h_1=H_{01}$ and $ab=Q^{01}_{01}$. Positivity gives
$0<ab\leq\operatorname{tr}Q^{01}/2<18/1000$. Consequently
$h_0h_1-s^2ab>695/1000-18/1000$. Finally Cauchy–Schwarz and the
credited enclosures give

$$
\kappa^2\leq(H_{00}+H_{11})\operatorname{tr}Q^{01}
 <\frac{1470\cdot36}{10^6}<\frac1{16}.
\tag{JR.4}
$$

Together with positivity this proves (JR.3). $\square$

## 30. A finite acquired phase record preserving every channel sector

**Definition 30.1 (actually enacted family).** Fix $s\in[0,1]$ before
receiving the specimen. The following finite instrument and its controlled
decoders are additional supplied operations. A native realization must
actually enact these maps and retain the stated classical record; the
definition does not infer them from a Kraus representation. The only
input-dependent quantum system accessible after this acquisition is its
declared joint fibre, including every retained ancillary or entangled
share. All other dilation systems are permanently inaccessible. There is
no specimen callback, helper specimen, retry, later returned environment
or quantum bypass. A passive reference is not accessible to execution.

The actual classical acquisition label is $\alpha=(r,j)$, with
$r\in\{+1,-1\}$ and $j\in\{L,T,S,f_1,f_2,\perp\}$.
The binary phase record is the component $r$; $j$ is also counted as
classical information. Let $V_T,V_S:\mathbb C^2\to\mathbb C^3$ be the
isometries with columns $(|1\rangle,|0\rangle)$ and
$(|2\rangle,|0\rangle)$ respectively. On qutrit inputs the encoder
Kraus matrices and quantum fibre dimensions are

$$
\begin{array}{c|c|c}
j&C_{r,j}&d_{r,j}\\ \hline
L&(D+rsT)/\sqrt2&3\\
T&\sqrt{(1-s^2)/2}\,V_T^\dagger T&2\\
S&V_S^\dagger S/\sqrt2&2\\
f_k&\sqrt{m_k/2}\,\langle k|\quad(k=1,2)&1.
\end{array}
\tag{JR.5}
$$

Each encoder branch is $\mathcal E_{r,j}(A)=C_{r,j}AC_{r,j}^\dagger$.
The $L$ decoder embeds its entire fibre into the live output by $E$.
The $T,S$ decoders embed by $EV_T,EV_S$. Each scalar $f_k$ decoder
sends $z$ to the WHOLE failure measure
$z\,w_\ell g(t)dt\,P_f$, separately for all five labels. It is TP since
$\sum_\ell w_\ell=\int_0^1g(t)dt=1$.

For the five-mode encoder replace every displayed Kraus matrix by
$C_{r,j}E^\dagger$. Add the scalar branch
$\mathcal E_{r,\perp}(A)=\operatorname{tr}((I_5-P)A)/2$, whose decoder
sends $z$ to $z\,g(t)dt\,P_f$ only at original label $2$.
This branch has several Kraus rows when $\dim V^\perp=2$, but its
retained quantum fibre is one-dimensional; the discarded multiplicity
index is not an accessible port. Zero $T$ branches at $s=1$ may be
removed before receiving any input. No output is conditioned upon $r$.

**Theorem 30.2 (one common complete channel, all complex inputs).**
The maps of Definition 30.1 form one finite acquisition/execution
factorization with full TP decoders. Forgetting $(r,j)$ gives exactly
$\widehat\Phi_*$, for every complex five-mode input and at every passive
reference amplification. This equality includes each exact-time failure
CP measure, all five labels, all cross-support entries and all zero
additional sectors. Its canonical twelve-history error is therefore the
credited $E_*$ for every $s$.

Proof. Write $L_r=(D+rsT)/\sqrt2$. The elementary Kraus mixing identity
already supplied by `UnitaryKrausMixingInvariance` gives

$$
\sum_rL_rAL_r^\dagger
 =DAD^\dagger+s^2TAT^\dagger.
\tag{JR.6}
$$

The $T$ branches sum to $(1-s^2)TAT^\dagger$, because
$V_TV_T^\dagger T=T$; the $S$ branches sum to $SAS^\dagger$.
Their live sum is precisely the fixed live map, without any reality
restriction on $A$. The $f_k$ branches sum to
$w_\ell g(t)dt\,\sum_km_kA_{kk}P_f$ in each original sector.
Each equality is an equality of CP maps, not just traces on twelve inputs.

Likewise, summing encoder effects gives

$$
\begin{aligned}
\sum_rL_r^\dagger L_r
 +(1-s^2)T^\dagger T+S^\dagger S+M
 &=D^\dagger D+T^\dagger T+S^\dagger S+M\\
 &=I_3
\end{aligned}
\tag{JR.7}
$$

by (CG.141). Every individual effect is positive and at most this sum,
so every finite encoder branch is TNI. All live decoders are isometric
channels and the scalar decoders are TP by their exact integrals.
On five modes the supported effects sum to $P$; the two scalar
$\perp$ effects sum to $I_5-P$. Their decoded measure is exactly the
extra term in (CG.142). The compression and trace branches annihilate
all $V$–$V^\perp$ coherences, as does that fixed completion.

For a joint matrix $X$ with reference $R$, a scalar row $C$ acts by
$(C\otimes I_R)X(C^\dagger\otimes I_R)$, not by replacing the
reference by its unconditional marginal. The $\perp$ branch gives
$\operatorname{Tr}_5[((I_5-P)\otimes I_R)X]/2$. Multiplying these
reference operators by the respective output measures proves the same
identity at every amplification. The identities hold on every Borel
time set: there is no time binning or marginal substitution. Both
zero-weight labels stay zero, $g$ is finite at both endpoints and has
no endpoint atoms, and no singular or additional output sector is
introduced. The last claim now reuses Theorem 16.1 on identical complete
outputs; it asserts no error bound for a new task exposing $(r,j)$.
$\square$

## 31. Actual record laws and every-input quantum accounting

**Theorem 31.1 (original-history information, without certain readout).**
For a normalized qutrit density $\rho$, put
$A(\rho)=\operatorname{tr}(D^\dagger D\rho)$,
$B(\rho)=\operatorname{tr}(T^\dagger T\rho)$ and
$C(\rho)=\operatorname{tr}(S^\dagger S\rho)$.
The ACTUAL unnormalized acquisition probabilities are

$$
\begin{aligned}
p_{r,L}(\rho)&=\tfrac12[A(\rho)+s^2B(\rho)]
                    +rs\kappa\operatorname{Re}\rho_{01},\\
p_{r,T}(\rho)&=\tfrac12(1-s^2)B(\rho),
&p_{r,S}(\rho)&=\tfrac12 C(\rho),\\
p_{r,f_k}(\rho)&=\tfrac12m_k\rho_{kk},
&\Pr_\rho(r)&=\tfrac12+rs\kappa\operatorname{Re}\rho_{01}.
\end{aligned}
\tag{JR.8}
$$

On the twelve specimens the binary law is

$$
\Pr_{y,e,n}(r)=\frac12+rs\kappa en\,q_y
 =\frac12+rs\kappa(-1)^m\frac{\sqrt{y(64-y)}}{128}.
\tag{JR.9}
$$

If $s>0$, the full finite record laws have exactly six distinct classes,
indexed by $(y,m)$; the two values of $\beta$ at fixed $(y,m)$ have
identical classical laws. Each of the twelve laws gives positive
probability to the same label $(+1,L)$, so these distinct laws do not
give certain single-specimen identification, even of those six classes.
The binary laws for opposite winding parities at the same $y$ have
total variation distance $2s\kappa q_y<1/8$.

Proof. The Born trace identity, already supplied by
`FiniteKrausInstrumentBornMarginal`, reduces the branch laws to effects.
Here

$$
D^\dagger T+T^\dagger D
 =\kappa(|0\rangle\langle1|+|1\rangle\langle0|).
\tag{JR.10}
$$

Expanding $L_r^\dagger L_r$ proves (JR.8); summing all its unnormalized
branches uses (JR.7) and proves the binary formula. On (JR.1),
$\operatorname{Re}\rho_{01}=enq_y$, giving (JR.9).
Every other branch effect is diagonal, so no record law depends
separately on $e$ or $n$. Distinct heights have distinct probabilities
$p_{+,f_1}=m_1(64-y)/256$, since $m_1>0$. At a fixed height the two
parities have different $p_{+,L}$ for $s>0$.

The determinant calculation

$$
\det L_r=\frac{h_2}{2\sqrt2}(h_0h_1-s^2ab)>0
\tag{JR.11}
$$

uses (JR.3), so $L_r^\dagger L_r$ is strictly positive. Thus
$p_{+,L}>0$ on every actual input. The variation formula follows
from the two binary probabilities; $q_y\leq1/4$ and $\kappa<1/4$
give its strict bound. This is a comparison of conditional laws, without
placing a probability distribution on the unknown histories. $\square$

**Theorem 31.2 (fully counted payload and its exact family tradeoff).**
At the cut in Definition 30.1 the joint quantum fibre dimensions are
$3,2,2,1,1,1$ for each value of $r$. The probability of a fibre of
dimension at least three, on EVERY normalized complex qutrit input, is

$$
\begin{aligned}
p_{\geq3}^{(s)}(\rho)
 &=A(\rho)+s^2B(\rho)\\
 &=\sum_{i=0}^2 H_{ii,*}\rho_{ii}
     +s^2\bigl(b^2\rho_{00}+a^2\rho_{11}\bigr),\\
p_{\geq3}^{(s)}(\rho)-p_{\geq3}^{(0)}(\rho)
 &=s^2\bigl(b^2\rho_{00}+a^2\rho_{11}\bigr).
\end{aligned}
\tag{JR.12}
$$

In particular $p_{\geq3}^{(s)}(\rho)>498/1000$ for every such input.
On the actual histories this equals

$$
\sum_iH_{ii,*}p_{yi}
  +s^2\left((Q_*^{01})_{11}\frac y{128}
             +(Q_*^{01})_{00}\frac{64-y}{128}\right).
\tag{JR.13}
$$

It is independent of both signs. If $\gamma=s\kappa$ denotes the
phase-record coefficient in (JR.9), the additional qutrit probability
is exactly $(\gamma/\kappa)^2B(\rho)$ in this family. It is strictly
positive for $s>0$ whenever $\rho_{00}+\rho_{11}>0$, and is zero
on $|2\rangle\langle2|$. This is an attained family tradeoff, not a
universal lower envelope over all implementations.

Proof. Equation (JR.11) makes each $L$ branch rank three, including
$s=0$ and $s=1$. The nonzero $T,S$ branches have rank two, and the
failure branches retain only scalars. Thus the only high-dimensional
branches are the two $L$ branches. Summing their probabilities cancels
the phase term in (JR.8) and proves (JR.12). The lower bound follows
from the three strict diagonal enclosures in Theorem 22.1 and
$\operatorname{tr}\rho=1$. Substitution gives (JR.13).

On an arbitrary normalized five-mode input $\sigma$, the same accounting
uses the unnormalized compression $\rho=E^\dagger\sigma E$ in (JR.12),
and $p_{r,\perp}=\operatorname{tr}((I_5-P)\sigma)/2$.
There is no asserted positive qutrit mass on an input supported entirely
in $V^\perp$. Passive-reference inputs use their reduced input density
for these probabilities, while their full conditional reference states
are those in Theorem 30.2.

The acquisition instrument outputs only its actual classical label and
the indicated fibre. A coherent dilation used to enact it must discard
its other systems permanently before this cut; retaining any such system
that execution can use changes the dimension being counted. Independent
blank systems introduced later require no input memory, but a later
accessible entanglement share is not a blank and cannot be omitted.
Under the stated no-bypass premise, the displayed decoders use only
the indicated fibre and generated label. Hence the count contains every
future-accessible input-dependent quantum system. It is not a count of
just the transmitted subsystem or the nominal output span. $\square$

## 32. A sharp binary winding-record ceiling for this fixed channel

**Definition 32.1 (compatible finite binary record).** Consider ANY
actually enacted finite acquisition/execution factorization in the
sense of [CG, Definition 21.2], with full TP decoders and jointly counted
quantum fibres, whose forgotten complete output is exactly
$\widehat\Phi_*$. A binary record can be any classical postprocessing
of its acquired finite label, including an additional input-independent
coin. Absorb that coin into the finite label. Write its full-output CP
branches as $\Psi_+,\Psi_-$, so
$\Psi_++\Psi_-=\widehat\Phi_*$ on the whole complex algebra and
all output measures. The input effect on the supported qutrit is
$F=\Psi_+^\dagger(I)$, compressed by $E$, so that
$\Pr_\rho(+)=\operatorname{tr}(F\rho)$ and $0\preceq F\preceq I_3$.
No separate access to an original environment is presumed.

For a fixed actual height define the algebraic phase contrast and
worst-case correct-parity probability by

$$
\begin{aligned}
\Gamma_y(F)&=\frac14\sum_{e,n=\pm1}en\,
                   \Pr_{y,e,n}(+),\\
\mathsf S_y&=\min_{e,n=\pm1}\Pr_{y,e,n}(r=en).
\end{aligned}
\tag{JR.14}
$$

The finite sum defining $\Gamma_y$ is a Fourier coefficient of four
conditional laws, not a source prior or a prepared mixed specimen.
The decision $r=en$ means $r=+1$ reports even winding and $r=-1$
reports odd winding; relabeling these two reports is allowed.

**Theorem 32.2 (sharp fixed-channel phase compatibility).** Every
factorization and binary record of Definition 32.1 satisfies

$$
\begin{aligned}
|\operatorname{Re}F_{01}|&\leq\frac\kappa2,
&|\Gamma_y(F)|&\leq\kappa q_y,\\
\mathsf S_y&\leq\frac12+\kappa q_y,
&\min_{y,e,n}\Pr_{y,e,n}(r=en)
 &\leq\frac12+\kappa\frac{\sqrt{295}}{128}.
\end{aligned}
\tag{JR.15}
$$

The family of Definition 30.1 at $s=1$ attains all these ceilings
simultaneously, at all three heights, with one history-independent
instrument and the same complete channel. More generally every
$\gamma\in[-\kappa,\kappa]$ is attained by that family, after a
possible binary relabeling, with
$\Pr_{y,e,n}(+)=1/2+\gamma enq_y$. No larger absolute common
coefficient is compatible with the fixed channel, even if imaginary
effect entries or arbitrary finite quantum fibres are permitted.

Proof. Take the live branch Choi matrix $J_+$ of $\Psi_+$ restricted
to $V$. Complete CP compatibility gives

$$
0\preceq J_+\preceq J_*
 =\sum_{K\in\{D,T,S\}}|K\rangle\!\rangle\langle\!\langle K|.
\tag{JR.16}
$$

This uses the actual full-channel identity; agreement of effects alone
would not imply it. The three Choi vectors are nonzero and mutually
orthogonal, because their matrix supports are diagonal, $01/10$ and
$02/20$. Let $V$ be the matrix with these three columns, ordered
$(D,T,S)$, and $G=V^\dagger V\succ0$. Positivity first implies
$J_+$ vanishes on $\ker J_*$: on that kernel its nonnegative quadratic
form is bounded above by zero, and a positive matrix with zero quadratic
form kills the vector. The range of $J_+$ is therefore in
$\operatorname{ran}V$. Consequently

$$
J_+=VZV^\dagger,\qquad
Z=G^{-1}V^\dagger J_+VG^{-1},\qquad 0\preceq Z\preceq I_3.
\tag{JR.17}
$$

For the last inequality, for any $u$ apply (JR.16) to $VG^{-1}u$.
This is the finite Choi-support form of the standard CP domination
argument, with the actual Gram matrix retained; the Kraus vectors
have not been incorrectly declared orthonormal. Write $z=Z_{DT}$.
Since $2Z-I$ is a Hermitian contraction, $|z|\leq1/2$.
The live effect is
$F^L=\sum_{i,j}Z_{ij}K_j^\dagger K_i$. Its $01$ entry receives
contributions only from the $D,T$ pair, giving

$$
F^L_{01}=z\,bh_1+\overline z\,h_0a,
\qquad \operatorname{Re}F^L_{01}=\kappa\operatorname{Re}z.
\tag{JR.18}
$$

The COMPLETE failure contribution to the $+$ record has effect $F^f$
satisfying $0\preceq F^f\preceq M$. To see this without replacing
the task by a time marginal, apply both positive branch measures to
the event consisting of every original failure label and time, and
use their exact sum from Definition 32.1. The total event effect is
$M$. Since $M|0\rangle=0$, positivity implies
$F^f|0\rangle=0$, hence $F^f_{01}=0$. Additional zero-ideal sectors
have zero branch maps by positivity; the fixed five-mode completion
restricts to this same statement on $V$. Thus (JR.18) also controls
the full effect $F$, proving the first inequality in (JR.15).
The exact-time law is essential to the stipulated common channel;
its integration here is merely a necessary consequence used in a bound.

Expanding (JR.1) against a general Hermitian $F$, the four signs
cancel every term of $\Gamma_y$ except the real $01$ coherence:

$$
\Gamma_y(F)=2q_y\operatorname{Re}F_{01}.
\tag{JR.19}
$$

This proves the contrast bound. The minimum of the four correct-parity
probabilities is no larger than their arithmetic mean, which is
$1/2+\Gamma_y(F)\leq1/2+\kappa q_y$. This use of an arithmetic
mean is a deterministic inequality, without an equal-prior premise.
The function $y(64-y)$ is increasing at the three heights below $32$,
so its minimum is $295$ at $y=5$. This proves the final ceiling.

Equation (JR.9) shows that $s=1$ makes every correct-parity probability
at a fixed $y$ exactly $1/2+\kappa q_y$; (JR.10) gives
$\operatorname{Re}F_{01}=\kappa/2$. Theorem 30.2 supplies the same
complete-channel identity for this actual finite factorization, including
all exact-time measures. Varying $s$ and relabeling gives the full
claimed coefficient interval. This proves mathematical attainment, not
merely separately attained finite-test optima. $\square$

## 33. Correspondence, attribution and the remaining native bridge

**Convention 33.1 (mathematical inputs and new content).** The channel,
its original five-mode completion, strict coefficient enclosures and
complete-output minimax value are reused from [CG, §§13–17]. Its
Schmidt-number and every-input necessity statements in §§22–24, its
unmixed sufficient factorization in §25 and its near-optimal stability
in §§26–28 are also credited. The additional `repo-derived` statements
here are the original-winding laws (JR.8)–(JR.9), their simultaneous
complete-channel realization, the exact every-input family accounting
(JR.12)–(JR.13), and the sharp fixed-channel compatibility and
worst-case parity ceilings (JR.15). None is a new minimax certificate.

The general mechanisms used inside these source-specific deductions
are `literature-attested`. Muñoz-Moller, Leppäjärvi and Heinosaari,
[*Adversarial Information Gain in Non-ideal Quantum Measurements*,
arXiv:2602.20941v1](https://arxiv.org/html/2602.20941v1), Definition 1
and Proposition 1, characterize meter/instrument compatibility by a
joint instrument and meters on a conjugate instrument. Leppäjärvi and
Sedlák, [*Incompatibility of quantum instruments*,
arXiv:2212.11225v2](https://arxiv.org/html/2212.11225v2), Definition 8,
Remark 3 and Proposition 7, give dilation and complementary-instrument
postprocessing descriptions. These finite-dimensional results substantiate
the joint-operation requirement and the finite Choi domination mechanism.
Their qubit tradeoff formulas, numerical examples and implied environment
access are not premises here. The proof of Theorem 32.2 applies its
domination argument only to the finite live Choi matrix and treats the
continuous failure measure directly; it assumes no unproved
continuous-outcome extension of their finite-outcome statements.

The repository's `UnitaryKrausMixingInvariance` and
`FiniteKrausInstrumentBornMarginal` supply the generic unchanged-channel
and branch-effect trace identities. `FiniteKrausRepresentation`, with
its selected Physlib declarations at
`6a09b2d1761a0d4430083045a247eb121d8da260`, supplies finite Choi/Kraus
correspondence. `AntidistinguishabilityGram.psd_summand_projection`
and its private kernel lemma express the positive-support mechanism
used in (JR.17); its antidistinguishing POVM is a different conclusion.
Pinned mathlib's matrix positivity, Gram and trace identities provide
the underlying finite linear algebra. These are source references, not
newly compiled applications. The examined compatible Lean sources and
these primary articles do not provide this channel's coefficient
$\kappa$, original-winding law or resource accounting as stated here.
That bounded comparison makes no worldwide novelty assertion.

**Convention 33.2 (actual operations and native obligations).** All maps
are common: $u_*,s,E,V_T,V_S$ and the output measure are fixed before
the sole unknown specimen is received. Neither encoder nor decoder
uses $y,e,n,\beta,m$ as an input. The acquired record is generated
by (JR.5), and execution is controlled only by that actual record.
The parameter $s$ selects an actually supplied acquisition instrument;
it is not an unknown-source-dependent calibration or a cost-free
permission inferred from an abstract dilation. No prior, reset,
survival conditioning, added specimen or readable old history occurs.
The full-complex and passive-reference identities, five original labels
and exact-time CP measures are those proved in Theorem 30.2.

`OriginalControlComposition.OriginalControl` specifies continuity,
strict-domain, variation and regularity conditions on real paths. Its
private absolute-continuity and integral helpers, and its chronological
concatenation theorem, construct no encoder or controlled qutrit decoder.
[Probability/Phase Transport][PPT], Definition 10.1, includes
$P=\partial_\kappa$ and $Q=\sum_aw_a(\kappa)\partial_{h_a}$;
its probability-changing noncommuting fields prevent treating diagonal
filters as an exhaustive native menu. The acquisition instrument
(JR.5), coherent storage, actual classical flags, calibrated isometric
decoding and their permissions remain additional services to be supplied
under that original operation contract. Geometric reachability alone
does not enact them. No sensor priors, action, symmetry or angle are
identified with the actual source, and no spectral weak-binding carrier
is substituted for it.

The law $g(t)dt$ is an exact mathematical output measure. A physical
implementation still needs the absorbing failure to occur at that
elapsed time, no later positive-carrier operation after failure, live
output at time one, and all original archives, aligned clocks,
permissions and controller updates. The cut must fit that same clock;
Definition 30.1 grants no extra acquisition time. An internal label
destined for later failure or a timestamp drawn from $g$ supplies
neither an absorbing event nor its timing. These obligations remain
unresolved. The sharp ceiling concerns the PARTICULAR complete channel
$\widehat\Phi_*$ and actual finite factorizations of it; the
sign-averaged-live conclusions about other optimizers do not extend
the ceiling to their full channels. The resource curve is exact for
the displayed family and is not claimed globally sharp. The native
acquisition/control programme therefore remains open.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[PPT]: AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md

## 追加锚（本行以下为增补区）

## 34. Original contrast and the joint acquisition cost

**Definition 34.1 (joint optimization at the credited error).** Retain
the sole normalized reached-cut experiment (JR.1), all four real signs
at each of the three heights, and the full complex common-processor
contract of [CG, Definitions 3.1 and 21.2]. The calibrated five-mode
input, fixed common metadata, ideal coherent live block, five ORIGINAL
exact-time failure measures, and HALF full cq norm are unchanged.
The isolated point, coefficient enclosures and optimum $E_*$ of
[CG, §§13–17] are ordinary source-conditional premises throughout.

Allow any optimal common full-output processor $\Phi$, not just
$\widehat\Phi_*$. Its acquisition is an ACTUAL factorization
$\Phi=\sum_\alpha\mathcal R_\alpha\mathcal E_\alpha$ with CP encoders,
$\sum_\alpha\mathcal E_\alpha^\dagger(I)=I$, full-output TP decoders,
and jointly counted future-accessible quantum fibres of dimension
$d_\alpha$. Countable and explicitly supplied integral factorizations
have exactly [CG, Convention 21.3]'s measurability and integrability
hypotheses. A binary record $r\in\{+1,-1\}$ is classical processing
of the acquired label, with independent coins absorbed into that label.
It is acquired before execution; it is not a measurement retrospectively
chosen on a discarded environment. Write $F$ for its plus effect on
the supported qutrit. Define

$$
\begin{aligned}
\mathsf V(F)&=\frac{|\Gamma_y(F)|}{\kappa q_y}
             =\frac{2|\operatorname{Re}F_{01}|}{\kappa},\\
Q_H&=\sum_{\alpha:d_\alpha\geq3}
                     \mathcal E_\alpha^\dagger(I),
&p_H(\rho)&=\operatorname{tr}(Q_H\rho),\\
\overline p_{H,y}&=\frac14\sum_{e,n}p_H(\rho_{y,e,n}),
&\mathsf W&=\max_{y,e,n}p_H(\rho_{y,e,n}),\\
\mathsf C(s)&=\inf\{\mathsf W:E(\Phi)=E_*,\ \mathsf V(F)\geq s,
                  \text{with such an actual factorization and record}\}.
\end{aligned}
\tag{JR.20}
$$

Here $\Gamma_y$ is the ORIGINAL winding Fourier coefficient (JR.14),
and (JR.19) proves that its normalized value is independent of $y$.
The denominator is positive. The four-term sums are mathematical tests
of four conditional laws, with no source prior. Every quantum system
available to execution is included in $d_\alpha$, including retained
specimen, controller, environment and entanglement shares. There is no
helper, readable history, callback, retry, bypass or normalization.
The cost concerns acquisition, including branches later destined for
failure; it is not conditioned on live output. Extra acquired classical
labels are allowed and are not presumed to be unknown source labels.

**Proposition 34.2 (the source-specific determinant parameters).** In
addition to the signs already established in Proposition 29.2, $d>0$.
Set

$$
\theta=\frac{ab}{h_0h_1},\qquad
\omega=\frac{cd}{h_0h_2},\qquad
\delta=\theta+\omega,\qquad k=1-\theta-\omega,\qquad
v_0=\frac{\omega}{1-\theta},\qquad s_0=\sqrt\delta.
\tag{JR.21}
$$

Then $\theta,\omega>0$, $\delta<18/695<1$, and $0<v_0<1$.
For arbitrary COMPLEX coefficients $x,z,w$,

$$
\det(xD+zT+wS)
 =h_0h_1h_2\,x\bigl(x^2-\theta z^2-\omega w^2\bigr).
\tag{JR.22}
$$

For each original height write

$$
\begin{aligned}
A_y&=\sum_i h_i^2p_{yi},\\
B_y&=b^2p_{y0}+a^2p_{y1},\\
C_y&=d^2p_{y0}+c^2p_{y2}.
\end{aligned}
\tag{JR.23}
$$

All three are positive and strictly increase as $y$ runs from $5$
through $16$ to $27$.

Proof. Only the sign of $d$ requires information beyond Proposition
29.2. In the exact root box of [CG, Proposition 13.2], the coordinates
of (CG.112) obey
$\lambda<1/2$, $7/5<\alpha_1<3/2$, $\alpha_2>11/10$,
$2/5<\beta_1<1/2$, and $0<\beta_2<5/6$.
Consequently $\|v_5\|^2>4$ and $\|v_{27}\|^2<2$.
The two contributions to $N_{02}$ in (CG.112) have opposite signs,
and $\sqrt{p_{50}p_{52}}=\sqrt5/16$,
$\sqrt{p_{27,0}p_{27,2}}=\sqrt{27}/16$. Using
$\sqrt5<9/4$ and $\sqrt{27}>5$ gives

$$
N_{02}=-\frac{\lambda\alpha_1\sqrt5}{16\|v_5\|^2}
       +\frac{(1-\lambda)\beta_1\sqrt{27}}{16\|v_{27}\|^2}
 >-\frac{27}{1024}+\frac1{32}>0.
$$

Since $Q^{02}_{01}=\eta_2N_{02}=cd$, with $\eta_2,c>0$, this proves
$d>0$. These rational comparisons use the credited box and do not
recertify its root. By rank one and [CG, Theorem 22.1],
$h_0h_1>695/1000$, $h_0h_2>796/1000$, and
$\operatorname{tr}Q^{01}+\operatorname{tr}Q^{02}<36/1000$.
The inequalities $2ab\leq a^2+b^2$ and $2cd\leq c^2+d^2$
therefore give $\delta<18/695$. Expansion of the displayed three by
three matrix proves (JR.22), without taking complex moduli or replacing
squares by absolute squares.

Finally, $A_y$ has slope $(H_{00}-H_{11})/128>0$ by the credited
enclosures. The box has $\eta_1>19/100$, and (CG.115) has
$(S_{01})_{00}>1/10$, so $b^2=(Q^{01})_{11}>19/1000$.
The trace bound gives $a^2<17/1000$, hence $B_y$ has positive
slope $(b^2-a^2)/128$. The slope of $C_y$ is $d^2/128>0$.
Positivity of their coefficients proves their positivity. $\square$

## 35. Averaging an actual record together with its acquisition cost

**Theorem 35.1 (record-preserving reduction for EVERY optimizer).**
Given any implementation in Definition 34.1, there is a mathematical
sign-averaged implementation with the SAME normalized winding contrast,
the SAME four-sign averaged acquisition cost at each height, and live
Choi matrix $J_*$ of (JR.16). Its entire full channel need not be
$\widehat\Phi_*$. Its total canonical-failure effect on the qutrit
is $M$, with no other output mass on that input space. This reduction
does not assert that its sign operations are natively supplied.

Proof. Put $g=(e,n)$, $U_g=\operatorname{diag}(e,n,1)$ and
$\chi(g)=en$. On the whole five-mode live output use the fixed unitary
$\widetilde U_g=EU_gE^\dagger+(I_5-P)$; on all failure and extra
sectors use identity. Denote that output action by $\mathcal U_g$.
Append an independent uniform classical coin $g$ to the acquired label
and use encoder $\mathcal E_\alpha\circ\operatorname{Ad}_{U_g}/4$
on the supported qutrit, decoder
$\mathcal U_g^\dagger\circ\mathcal R_\alpha$, and report

$$
\widetilde\Phi=\frac14\sum_g
 \mathcal U_g^\dagger\circ\Phi\circ\operatorname{Ad}_{U_g},
\qquad \widetilde r=\chi(g)r,\qquad d_{g,\alpha}=d_\alpha.
\tag{JR.24}
$$

The encoders have total effect $I$ and all decoders remain full TP.
The five-mode input version uses $\widetilde U_g$ as well. This is
one common instrument with a generated independent coin, not a random
choice of the unknown history. The signs permute the original four
input/target pairs at each height, including their unchanged full
failure measures. Convexity and unitary invariance of the complete
norm give $E(\widetilde\Phi)\leq E_*$. The credited full-class lower
bound gives equality. Applying the finite contraction of [CG,
Convention 17.1] and then its Theorem 17.2 fixes precisely the averaged
live Choi $J_*$. That theorem also gives $G_o=0$ and $G_f|0\rangle=0$
before averaging. After averaging the live effect is
$D^\dagger D+T^\dagger T+S^\dagger S=I-M$, so the total failure
effect is $M$. No individual failure measure or unaveraged full channel
has been identified by this argument.

The binary relabelling is essential. Its plus effect and its high-fibre
effect are

$$
\begin{aligned}
\widetilde F
 &=\frac12 I+\frac14\sum_g\chi(g)U_g^\dagger F U_g
  =\frac12I+F_{01}|0\rangle\langle1|
                   +F_{10}|1\rangle\langle0|,\\
\widetilde Q_H&=\frac14\sum_gU_g^\dagger Q_HU_g
                  =\operatorname{diag}((Q_H)_{00},(Q_H)_{11},(Q_H)_{22}),\\
\widetilde p_H(\rho_{y,e,n})&=\overline p_{H,y}
                                      \leq\mathsf W.
\end{aligned}
\tag{JR.25}
$$

For the first identity, the plus effect conditional on $g$ is
$U_g^\dagger[I/2+\chi(g)(F-I/2)]U_g$.
Character orthogonality retains exactly the $01,10$ entries in its
signed average. This preserves the ACTUAL record's Fourier coordinate;
averaging while discarding or keeping its old sign unchanged would not.
The second identity follows because the same coin neither changes
dimension nor deletes any branch. Summing the four actual input
probabilities gives the last identity, without a source prior.

In particular an individual coherent-input cost was not diagonalized
inside the original implementation. For its original Hermitian $Q_H$,
the exact cost is

$$
\begin{aligned}
p_H(\rho_{y,e,n})={}&\sum_i p_{yi}(Q_H)_{ii}
 +2enq_y\operatorname{Re}(Q_H)_{01}\\
 &+2e\sqrt{p_{y0}p_{y2}}\operatorname{Re}(Q_H)_{02}
 +2n\sqrt{p_{y1}p_{y2}}\operatorname{Re}(Q_H)_{12}.
\end{aligned}
\tag{JR.26}
$$

Those off-diagonal terms vanish in the FOUR-SIGN average, not in an
individual history. The argument preserves low/high fibre membership
throughout; it replaces neither the actual cut by a virtual Choi
ensemble nor worst-history cost by an average-case objective.
The finite coin also preserves the hypotheses for countable and
specified integral factorizations. $\square$

## 36. The simultaneous rank and record constraint on the live face

**Theorem 36.1 (one joint coefficient constraint).** For the averaged
implementation of Theorem 35.1 there are numbers $u,v,w\in[0,1]$
such that

$$
\begin{aligned}
u&\leq\theta v+\omega w,\\
\mathsf V(F)&\leq\sqrt{uv}+\sqrt{(1-u)(1-v)}\leq1,\\
\overline p_{H,y}&\geq
 A_y(1-u)+B_y(1-v)+C_y(1-w)
                       \quad(y=5,16,27).
\end{aligned}
\tag{JR.27}
$$

The SAME $u,v,w$ occur in all three inequalities and at all heights.
The cost inequality uses the original implementation's averaged
ACQUISITION probability, including any high fibre that later fails.

Proof. Refine the actual label by its binary coin, so $r$ is determined
by it. Choose encoder Kraus matrices $C_{\alpha j}$ and compressed
live-decoder Kraus matrices $R_{\alpha i}^L$. Their products
$L_{\alpha ij}=R_{\alpha i}^LC_{\alpha j}$ give the live Choi matrix.
Their rank is at most $d_\alpha$, and the live decoder is TNI.
These are analytic Kraus refinements of the same branches, not newly
observable records. In the integral case use its stipulated measurable
Kraus fields. Integrable positive Choi matrices make the following
finite-dimensional moments well defined.

Every such Kraus vector lies in the span of $|D\rangle\!\rangle$,
$|T\rangle\!\rangle$, $|S\rangle\!\rangle$: a vector orthogonal to
this support has zero quadratic form against their total $J_*$,
so positivity kills each summand, or almost every integrand. This is
the positive-summand support mechanism already used in (JR.17).
Write each product uniquely as $L_j=x_jD+z_jT+w_jS$.
The three Kraus vectors are linearly independent with disjoint matrix
supports. Applying their Gram left inverse to the Choi equality gives

$$
\sum_j
 \begin{pmatrix}x_j\\z_j\\w_j\end{pmatrix}
 \begin{pmatrix}\overline x_j&\overline z_j&\overline w_j\end{pmatrix}
 =I_3.
\tag{JR.28}
$$

In particular each total squared coefficient mass is $1$, and the total
$D,T$ cross moment is zero. Partition these SAME products by their
actual fibre dimension. Let $u,v,w$ be the low-fibre sums of
$|x_j|^2,|z_j|^2,|w_j|^2$, respectively; high means $d_\alpha\geq3$.
Each low product has rank at most two. By (JR.22), either $x_j=0$
or $x_j^2=\theta z_j^2+\omega w_j^2$. The complex triangle inequality
therefore gives $|x_j|^2\leq\theta|z_j|^2+\omega|w_j|^2$ in both
cases. Sum to get the first line of (JR.27).

The plus branch's failure effect is dominated by $M$. Positivity and
$M|0\rangle=0$ imply that its $01$ entry is zero, even when the
full failure measures differ from those of $\widehat\Phi_*$.
There is no other mass on the qutrit input space. Computing the live
effect as in (JR.18), and using (JR.28), consequently gives the exact
signed-record identity

$$
\frac{2\operatorname{Re}\widetilde F_{01}}\kappa
 =\sum_j r_j\operatorname{Re}(\overline x_jz_j).
\tag{JR.29}
$$

Taking an absolute value and applying Cauchy–Schwarz separately on
the low and high sets bounds this by
$\sqrt{uv}+\sqrt{(1-u)(1-v)}$. Cauchy–Schwarz on the two real unit
vectors $(\sqrt u,\sqrt{1-u})$, $(\sqrt v,\sqrt{1-v})$ gives the
ceiling $1$. This proof retains arbitrary complex phases and the
actual acquired binary record.

For the cost, the aggregate low and high live maps separately commute
with the sign action, because membership in those sets was preserved
in (JR.24). Their coefficient Gram matrices are therefore diagonal:
$D,T,S$ have the distinct characters $1,en,e$.
Equivalently, average their effects over those same signs before
testing $\rho_y$. The high live-output probability is exactly
$A_y(1-u)+B_y(1-v)+C_y(1-w)$. Full TP of each decoder makes its
supported live trace at most its encoder trace. Summing over the same
high branches gives the last line of (JR.27). Countable sums and the
specified integrals obey the same support, triangle and Cauchy–Schwarz
arguments. No decoder has been treated as TP on just its live part.
$\square$

## 37. The sharp cost function for every required contrast

**Definition 37.1 (explicit frontier parameter).** On $[v_0,1]$ put

$$
\mathfrak f(v)=\sqrt{v(\theta v+\omega)}
              +\sqrt{(1-v)(1-\theta v-\omega)}.
\tag{JR.30}
$$

For $0\leq s\leq s_0$ set $v_s=1$. For $s_0<s\leq1$ let $v_s$
be the unique point in $[v_0,1)$ with $\mathfrak f(v_s)=s$.
An expression requiring no optimization or implicit root choice is

$$
v_s=
\frac{(1+\theta)(1-s^2-\omega)+2\omega s^2
 +2s\sqrt{1-s^2}\sqrt{\theta(1-s^2)+\omega k}}
 {(1+\theta)^2-4\theta s^2}
 \qquad(s_0\leq s\leq1).
\tag{JR.31}
$$

The formula agrees with the first case at $s=s_0$.

**Theorem 37.2 (complete sharp original record/resource frontier).**
For EVERY optimal original common processor and compatible actual
factorization and binary record, $0\leq\mathsf V(F)\leq1$.
Every value in this interval is feasible. For a required $s\in[0,1]$,
every such implementation with $\mathsf V(F)\geq s$ satisfies

$$
\begin{aligned}
\overline p_{H,y}&\geq P_y(s)
 :=A_y(1-\omega-\theta v_s)+B_y(1-v_s),\\
\mathsf W&\geq\mathsf C(s)=P_{27}(s).
\end{aligned}
\tag{JR.32}
$$

A single common finite factorization for each prescribed $s$, supplied
in §38, attains the three averaged bounds and the worst-history bound
SIMULTANEOUSLY, has contrast exactly $s$, and forgets to the PARTICULAR
complete channel $\widehat\Phi_*$. Thus the infimum in (JR.20) is a
minimum, also when the comparison permits the countable and specified
integral factorizations. Requirements $s>1$ are infeasible.

All endpoints and the constant-cost interval are

$$
\begin{aligned}
P_y(s)&=(1-\delta)A_y &&(0\leq s\leq s_0),\\
P_y(1)&=\frac{k}{1-\theta}(A_y+B_y),
&v_1&=v_0.
\end{aligned}
\tag{JR.33}
$$

The functions $P_y$ are continuous, constant precisely on $[0,s_0]$,
and strictly increasing on $[s_0,1]$. In particular zero required
contrast does not permit zero dimension-three mass. These per-height
necessary bounds are FOUR-SIGN averages. They are not individual-input
Loewner inequalities for an unaveraged implementation.

Proof. For well-definedness, set $u(v)=\theta v+\omega$.
On $[v_0,1]$, $0<u(v)\leq v$, with equality only at $v_0$.
Write
$\mathfrak f(v)=\cos(\arcsin\sqrt v-\arcsin\sqrt{u(v)})$.
The angle difference is zero at $v_0$ and increases strictly to
$\arccos\sqrt\delta$ at $1$. Indeed its derivative in the interior
is positive because
$u(v)>\theta v$ and $1-u(v)>\theta(1-v)$ imply
$\sqrt{u(v)(1-u(v))}>\theta\sqrt{v(1-v)}$.
Thus $\mathfrak f$ decreases continuously and strictly from $1$ to
$s_0$. This proves existence, uniqueness and the stated inverse
continuity and monotonicity. To verify (JR.31), the equality
$\mathfrak f(v)=s$ with $u\leq v$ gives

$$
\sqrt u=s\sqrt v-\sqrt{1-s^2}\sqrt{1-v},\qquad
(2s^2-1-\theta)v+1-s^2-\omega
 =2s\sqrt{1-s^2}\sqrt{v(1-v)}.
$$

Squaring the second equality gives a quadratic with positive leading
coefficient $(1+\theta)^2-4\theta s^2\geq(1-\theta)^2$.
The larger root is (JR.31); its inner discriminant simplifies to
$\theta(1-s^2)+\omega k$. It is the desired root: at $s_0$ it
is $1$, it continues without a double root for $s_0<s<1$, and
the unique solution just proved in $[v_0,1]$ cannot switch roots
there. At $s=1$ both roots equal $v_0$. This also verifies both
endpoint substitutions without an extraneous squared-equation branch.

Now take $u,v,w$ from Theorem 36.1. They satisfy
$u\leq\theta v+\omega w\leq\theta v+\omega$.
For $s\leq s_0$, the bounds $u\leq\delta$, $v,w\leq1$ immediately
give $\overline p_{H,y}\geq(1-\delta)A_y$.
For $s>s_0$, necessarily $v\leq v_s$. Otherwise
$v>v_s\geq v_0$, so $u\leq\theta v+\omega<v$. For fixed $v$,
$\sqrt{uv}+\sqrt{(1-u)(1-v)}$ increases on $0\leq u\leq v$.
Consequently (JR.27) would imply

$$
s\leq\mathsf V(F)\leq\sqrt{uv}+\sqrt{(1-u)(1-v)}
 \leq\mathfrak f(v)<\mathfrak f(v_s)=s,
$$

a contradiction. Hence $u\leq\theta v_s+\omega$, $v\leq v_s$,
$w\leq1$. Substitution in (JR.27), whose weights are positive, proves
the first line of (JR.32). It uses one joint constraint on cost and
record, not independently optimized endpoints.

The original maximum is at least each four-sign average. In the
displayed bound, $1-\omega-\theta v_s\geq k>0$ and $1-v_s\geq0$.
Since $A_y,B_y$ strictly increase, $P_5(s)<P_{16}(s)<P_{27}(s)$.
Thus $\mathsf W\geq P_{27}(s)$; no averaging over heights is used.
The construction in Theorem 38.2 supplies the reverse inequality with
one channel and record, proving the equality defining $\mathsf C$.
The contrast ceiling is already (JR.27); that same construction gives
every value. Finally $P_y$ is affine decreasing in $v_s$ with strictly
positive coefficient $\theta A_y+B_y$. This proves the remaining
monotonicity and endpoint claims. $\square$

## 38. One finite joint attainer with the full original complete output

**Definition 38.1 (supplied encoder and full TP decoders).** Fix
$s\in[0,1]$, $v=v_s$ and $u=\theta v+\omega$ before the specimen
arrives. For $\sigma,\tau\in\{+1,-1\}$ define qutrit live matrices

$$
H_\sigma=\frac{\sqrt{1-u}D+\sigma\sqrt{1-v}T}{\sqrt2},\qquad
L_{\sigma,\tau}=\frac{\sqrt uD+\sigma\sqrt vT+\tau S}{2}.
\tag{JR.34}
$$

For each $L_{\sigma,\tau}$ choose once a fixed isometry
$V_{\sigma,\tau}:\mathbb C^2\to\mathbb C^3$ onto its image.
Its columns can be fixed by Gram–Schmidt on the first two independent
columns in their lexicographic order. This rule uses known matrices,
not the received state. The acquisition has the following branches:

| Acquired branch | Encoder Kraus matrix | Joint fibre | Full-output decoder |
| --- | --- | --- | --- |
| $(H,\sigma)$ | $H_\sigma$ | $3$ | $X\mapsto EXE^\dagger$ in live |
| $(L,\sigma,\tau)$ | $V_{\sigma,\tau}^\dagger L_{\sigma,\tau}$ | $2$ | $X\mapsto EV_{\sigma,\tau}XV_{\sigma,\tau}^\dagger E^\dagger$ in live |
| $(f,j,\sigma)$, $j=1,2$ | $\sqrt{m_j/2}\langle j|$ | $1$ | $z\mapsto z w_\ell g(t)dt\,P_f$ in EACH original label $\ell$ |

For five-mode inputs multiply each encoder matrix on the right by
$E^\dagger$. Add branches $(\perp,\sigma)$ with scalar encoder
$A\mapsto\operatorname{tr}((I_5-P)A)/2$, decoded to
$z g(t)dt\,P_f$ only at original label $2$. Their two orthogonal
complementary Kraus rows are a discarded multiplicity, not extra
accessible quantum systems. The live and scalar decoders have no
other output sectors. Every displayed decoder is TP on its WHOLE fibre.

On a live branch retain $\sigma$ as a generated classical label, and
on failure branches $\sigma$ is the fair coin already in their rows.
For the designated binary record, use the fixed classical kernel

$$
\Pr(r\mid\sigma)=\frac{1+r\sigma\eta_s}{2},\qquad
\eta_s=\begin{cases}s/s_0,&0\leq s\leq s_0,\\1,&s_0<s\leq1.
\end{cases}
\tag{JR.35}
$$

Absorb its coin into the actual acquisition label. All labels needed
for decoding are retained classically, including $\sigma,\tau$ when
present. Only the declared fibre is quantum. These are additional
actually supplied operations, rather than permission inferred from
a change of channel representation.

**Theorem 38.2 (simultaneous rank, law, reference and cost equality).**
The acquisition of Definition 38.1 has exactly the stated fully counted
fibre dimensions, a finite label alphabet, full TP decoders and total
encoder effect $I_5$. Forgetting its acquired labels gives exactly
$\widehat\Phi_*$ on EVERY complex five-mode matrix and after tensoring
identity on every passive reference. This includes each of the five
original exact-time failure CP measures on every Borel set, all
cross-support entries and all zero additional sectors. Its original
complete-output error is the credited $E_*$. Its contrast is exactly
$s$ and its high-fibre probability on every normalized supported
complex input is

$$
p_H^{[s]}(\rho)=(1-u)\sum_i h_i^2\rho_{ii}
                      +(1-v)(b^2\rho_{00}+a^2\rho_{11}).
\tag{JR.36}
$$

Thus on EACH original sign history it equals $P_y(s)$ and its worst
history cost is $P_{27}(s)$. Both the full-class necessary curve and
all three per-height averages are attained by this ONE factorization.

Proof. From (JR.22) and $u=\theta v+\omega>0$,
$\det L_{\sigma,\tau}=0$. Its rows and columns indexed by $1,2$
have diagonal minor $u h_1h_2/4>0$, so its rank is exactly two.
Also

$$
\det H_\sigma
 =\frac{h_0h_1h_2}{2\sqrt2}\sqrt{1-u}
       [(1-u)-\theta(1-v)]
 =\frac{h_0h_1h_2}{2\sqrt2}\sqrt{1-u}\,k>0.
\tag{JR.37}
$$

Thus every $H$ branch has rank three, including $v=1$ and $s=1$.
There is no rank convention jump at either endpoint. The image
isometries exist for the rank-two branches and satisfy
$V_{\sigma,\tau}V_{\sigma,\tau}^\dagger L_{\sigma,\tau}
=L_{\sigma,\tau}$. Compression and its isometric TP decoder therefore
have product exactly $L_{\sigma,\tau}$ on all complex matrix units.

The coefficient columns in (JR.34) are orthonormal when summed over
the two $H$ rows and four $L$ rows: their squared masses are
$(1-u)+u=1$, $(1-v)+v=1$, $0+1=1$, and every cross moment is zero.
The existing Kraus-mixing identity used in (JR.6) therefore gives,
for every complex $A$,

$$
\begin{aligned}
\sum_\sigma H_\sigma A H_\sigma^\dagger
 +\sum_{\sigma,\tau}L_{\sigma,\tau}A L_{\sigma,\tau}^\dagger
 &=DAD^\dagger+TAT^\dagger+SAS^\dagger,\\
\sum_\sigma H_\sigma^\dagger H_\sigma
 +\sum_{\sigma,\tau}L_{\sigma,\tau}^\dagger L_{\sigma,\tau}+M
 &=I_3.
\end{aligned}
\tag{JR.38}
$$

The last identity is exactly the credited (CG.141). The compressed
encoders have the same effects as the uncompressed $L$ matrices.
Every scalar failure decoder is TP because $\sum_\ell w_\ell=1$
and $\int_0^1g(t)dt=1$. Summing their encoder-decoder products yields
$w_\ell g(t)dt\,\operatorname{tr}(MA)P_f$ separately for each original
$\ell$, with both zero-weight labels retained. For five modes the
complementary encoder effect is $I_5-P$; hence the total encoder
effect is $P+(I_5-P)=I_5$. The forgotten maps are exactly

$$
\begin{aligned}
\Phi_{\mathrm{live}}(A)&=
 E[D(E^\dagger AE)D^\dagger+T(E^\dagger AE)T^\dagger
                                  +S(E^\dagger AE)S^\dagger]E^\dagger,\\
\Phi_\ell(A)(dt)&=g(t)\left[
 w_\ell\operatorname{tr}(EME^\dagger A)
 +\mathbf1_{\ell=2}\operatorname{tr}((I_5-P)A)\right]dt\,P_f.
\end{aligned}
\tag{JR.39}
$$

These are equalities of maps and measures, not only their values on
twelve densities. In particular cross operators between $P$ and
$I_5-P$ have zero image, and every extra output sector is zero.
Every identity holds on matrix units and thus after arbitrary passive
reference amplification. More explicitly, the failure reference
factor on a joint operator $X$ is
$\operatorname{Tr}_5[(EME^\dagger\otimes I)X]$ in the first term,
and $\operatorname{Tr}_5[((I_5-P)\otimes I)X]$ in the second.
Multiplying these by the stated density and $P_f$ proves equality
on every Borel time set, including the absence of singular mass.
The maps leave common metadata in the same fixed state. Performance
therefore reuses the original full-output theorem, with no new
acceptance event or changed metric.

Only the $H$ branches have dimension at least three. Their effects sum
to $(1-u)D^\dagger D+(1-v)T^\dagger T$, proving (JR.36) even on
complex inputs. At the original inputs this is $P_y(s)$, independent
of both signs. The binary law is computed in §39; it gives contrast
$s$. This finishes the simultaneous attainment claimed in Theorem
37.2.

For completeness, a dilation of this specified acquisition can use
$|\alpha\rangle_C\otimes C_{\alpha j}|\psi\rangle$
with an orthogonal environment copy $|\alpha,j\rangle_Z$ for every
Kraus row. Their sum is an isometry by the encoder-effect identity.
Trace out $Z$ to produce the actual classical label $\alpha$ and
its declared fibre. The complementary-support multiplicity and all
coin/dilation systems other than the retained classical label are in
$Z$ and are permanently inaccessible BEFORE the cut. No retained
specimen, quantum controller, environment or entanglement share is
available outside the fibre. Later independent blank ancillas can be
used by the TP decoders; later accessible correlated shares cannot.
If an implementation retains $Z$, it is a different acquisition cost
and is not the attaining implementation specified here. $\square$

## 39. Actual laws, plateau cases and the inverse budget curve

**Proposition 39.1 (height and sign correspondence in the attainer).**
Put $q_{02,y}=\sqrt{p_{y0}p_{y2}}$, $q_{12,y}=\sqrt{p_{y1}p_{y2}}$
and $\kappa_{02}=h_0c+h_2d>0$. Before the optional binary coin,
the entire finite acquisition law on the original specimen is

$$
\begin{aligned}
\Pr(H,\sigma\mid y,e,n)
 &=\frac{P_y(s)}2
    +\sigma\sqrt{(1-u)(1-v)}\,\kappa enq_y,\\
\Pr(L,\sigma,\tau\mid y,e,n)
 &=\frac14\bigl[uA_y+vB_y+C_y
     +2\sigma\sqrt{uv}\,\kappa enq_y\\
 &\hspace{22mm}+2\tau\sqrt u\,\kappa_{02}e q_{02,y}
     +2\sigma\tau\sqrt v\,acn q_{12,y}\bigr],\\
\Pr(f,j,\sigma\mid y,e,n)&=m_jp_{yj}/2,\qquad
\Pr(\perp,\sigma\mid y,e,n)=0.
\end{aligned}
\tag{JR.40}
$$

After (JR.35), the designated binary law and effect are

$$
\Pr(r\mid y,e,n)=\frac12+r\kappa s\,enq_y,
\qquad F=\frac12I+\frac{\kappa s}{2}
                (|0\rangle\langle1|+|1\rangle\langle0|).
\tag{JR.41}
$$

Thus $en=(-1)^m$ is the original winding parity and $x=y/256$ is
the original height. The binary correct-parity probability is
$1/2+\kappa s q_y$ at every sign; its worst original height is $5$.
The high-fibre cost is largest at height $27$. Height $16$ remains
one of the required complete-output constraints and has its own
attained intermediate resource bound. No one of these heights is a
probabilistic source weight.

Proof. The cross effects are
$D^\dagger T+T^\dagger D=\kappa X_{01}$,
$D^\dagger S+S^\dagger D=\kappa_{02}X_{02}$, and
$T^\dagger S+S^\dagger T=acX_{12}$, where
$X_{ij}=|i\rangle\langle j|+|j\rangle\langle i|$.
Expanding (JR.34)'s effects and applying the Born trace identity gives
(JR.40). Sum over $\tau$ and the branch types. The unsigned masses
sum to $1/2$ for each $\sigma$, while its signed term is
$\sigma\kappa enq_y\mathfrak f(v)$. The independent record coin
multiplies that term by $\eta_s$, with
$\eta_s\mathfrak f(v)=s$ in both parameter regimes. This proves
(JR.41) and the effect identity on the whole complex algebra.

At $s=0$ the designated binary record is a fair coin and the cost is
$(1-\delta)A_y$. Up to $s=s_0$ the SAME quantum instrument attains
the constant minimum; only its fixed classical record kernel changes.
At $s=s_0$ it can report $\sigma$ directly. For $s_0<s<1$ both high
Kraus coefficients in (JR.34) are nonzero. At $s=1$, $u=v=v_0$,
the low matrices are
$(\sqrt{v_0}D+\sigma\sqrt{v_0}T+\tau S)/2$, and the high matrices
are $\sqrt{1-v_0}(D+\sigma T)/\sqrt2$.
The rank arguments in (JR.37) still apply. Binary relabelling supplies
either sign of the contrast, so the signed normalized Fourier
coordinate has precisely the feasible range $[-1,1]$.

The extra labels in (JR.40) can depend separately on $e,n$ through the
two other coherences; the binary marginal in (JR.41) depends only on
$(y,m)$. No claim that the entire acquired law has only six classes
is made for this different instrument. Since every $H_+$ is invertible,
all twelve histories assign positive probability to that same branch;
the full classical law does not identify the unknown history with
certainty from one specimen. All these are unconditional laws at the
already normalized old cut. $\square$

**Corollary 39.2 (complete inverse resource budget).** Let
$c_0=(1-\delta)A_{27}$ and
$c_1=k(A_{27}+B_{27})/(1-\theta)$. Among original optimal processors
with an actual factorization and worst-history cost at most $c$, none
exists if $c<c_0$. For $c_0\leq c\leq c_1$ the largest feasible
normalized binary contrast is

$$
\mathsf V_{\max}(c)=\mathfrak f\!\left(
 \frac{A_{27}(1-\omega)+B_{27}-c}{\theta A_{27}+B_{27}}
                         \right).
\tag{JR.42}
$$

For $c\geq c_1$ it is $1$. In particular at the minimum resource
budget $c_0$ the entire interval $[0,s_0]$ is attainable.

Proof. Theorem 37.2 gives the constant minimum and strict increase
thereafter, as well as the maximal contrast $1$. On its increasing
part its cost is affine in $v_s$ with slope
$-(\theta A_{27}+B_{27})<0$; solving that affine equation gives
(JR.42). The finite instruments in §38 attain each case, including
both budget endpoints. $\square$

## 40. Mathematical reuse and the residual native obligation

**Convention 40.1 (covered mathematics and the uncovered relation).**
The exact original benchmark, isolated root, coefficient bounds and
particular complete channel are credited to [CG, §§13–16]. Its
Theorem 17.2 fixes only the sign-averaged live Choi of every optimizer;
its entire full channel and individual failure-time laws are not unique
by that theorem. The Schmidt-three and every-input nonsharp lower
bounds in [CG, §§22–24], near-optimal results in §§26–28, and the
attained family and particular-channel ceiling in §§29–33 above remain
credited results. They are not the sharp optimization in (JR.20).

The additional `repo-derived` relation is the joint actual-record/cost
reduction (JR.24)–(JR.29), the determinant allocation and complete
frontier (JR.30)–(JR.33), and its single finite complete-channel
attainer with laws (JR.34)–(JR.42). In particular the constant-cost
interval uses singular mixtures of $D,T,S$, instead of simply
interpolating the previously attained $D+sT$ family. These results
are ordinary conditional proofs, without fresh Lean/kernel evidence
or a new certificate for $E_*$. The per-height necessity is explicitly
an average; (JR.26)'s coherent-input terms remain in the actual cost.

The mature mechanisms are `literature-attested`. Sekatski,
[*The bottleneck dimension of quantum operations*,
arXiv:2608.25010v1](https://arxiv.org/html/2608.25010v1), §II.A,
equation (2) and Definition 1, gives the classical-assisted
encoder/TP-decoder compression and its Kraus-rank/Schmidt-number
correspondence. Its singular-value factorization explains the
rank-two image compression used here; it does not supply a cost for
this original twelve-history task or an actually acquired record.
Leppäjärvi–Sedlák, [*Incompatibility of quantum instruments*,
arXiv:2212.11225v2](https://arxiv.org/html/2212.11225v2), Definition 8,
Remark 3 and Proposition 7, gives finite-dimensional instrument
dilation and complementary-instrument postprocessing compatibility.
Its joint-instrument requirement is retained here, but no accessible
native environment or continuous-outcome theorem is inferred from it.
Our failure-measure equalities instead follow directly from (JR.39).
Complex triangle inequalities, Cauchy–Schwarz, character averaging and
finite positive-support arguments are standard tools inside the proofs.

The exact generic Kraus-mixing and branch-effect identities are reused
from `UnitaryKrausMixingInvariance.unitary_kraus_mixing_invariance` and
`FiniteKrausInstrumentBornMarginal.finite_kraus_instrument_born_marginal`.
`FiniteKrausRepresentation`, including `choi_of_kraus`,
`choi_PSD_iff_CP_map` and its Kraus representation, supplies the finite
CP machinery, selected from Physlib at
`6a09b2d1761a0d4430083045a247eb121d8da260`.
`AntidistinguishabilityGram.psd_summand_projection` and its private
`psd_summand_kills_kernel` express the support argument; their specific
antidistinguishability conclusions are not premises of this frontier.
Pinned mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` supplies the
matrix positivity, Gram and trace framework. These are source reuse,
not newly compiled applications or additional Lean declarations.

The source snapshot
`648765d8c61a33ec941bbfc16416ca49c4c8c36c` also contains
[Joint Transfer–Coherence Interface Geometry](https://github.com/the-omega-institute/trureturing/blob/648765d8c61a33ec941bbfc16416ca49c4c8c36c/docs/develop/theory/FIB_NATIVE_JOINT_TRANSFER_COHERENCE_INTERFACE_GEOMETRY.md),
whose Theorem 2.2 characterizes a simultaneous ZERO-TRANSFER and
Schmidt-two live restriction by a comparison matrix. The present live
face has the nonzero transfers of $T,S$; that Schur-supported criterion
is not a replacement for (JR.22) or an exhaustive native class.
`SchurChannelMixedUnitaryDistance` concerns diamond distance of TP
Schur channels to mixed-unitary sets. `ThreePointPositivityGate`
concerns an entrywise nonnegative real three-point matrix under its
one-versus-many hypothesis. `ChenDeyNaiveEquationsFive` refutes a
five-dimensional orthostochastic lifting criterion. Their conclusions
do not optimize this acquisition cost. The pure-state entropy identity
in `InputInformationBalance.input_information_balance` and the
specific coherent-copy identity in
`CoherentCopyCorrelationTax.coherent_copy_correlation_tax` concern
their own joint states and entropy functionals. No conversion from
those entropies, the designated-subspace EOF refutation, or the
classical $137/512$ allocation score to (JR.20) is established or used.
The later weak-binding extension and structural atlas are not premises.
These bounded source and primary-literature comparisons assert no
worldwide priority or literature-absence result.

**Definition 40.2 (remaining actual acquisition and time bridge).**
The supplied-operation class in §38 must actually enact its common
encoder, classical flags, calibrated support decomposition, rank-two
image encodings, coherent retention and controlled TP decoders under
the ORIGINAL permissions. The maps, the parameter $s$, the isometries
and all classical kernels are fixed before receiving the sample.
Native access to an unknown specimen, controlled decoding and permanent
inaccessibility of the discarded dilation systems remain obligations.
A mathematical change of candidate channel or instrument grants no
actuator, rotation, swap, measurement or new permission.

`OriginalControlComposition.OriginalControl` requires nonnegative finite
duration, continuity, strict height domain, bounded phase variation,
and its absolute-continuity or finite-piecewise-$C^1$ alternative.
Its concatenation and private analytic helpers are statements about
those paths, not constructors of the operations in §38.
[Probability/Phase Transport][PPT], Definition 10.1, has the actual
fields $P=\partial_\kappa$ and
$Q=\sum_a w_a(\kappa)\partial_{h_a}$. On the double wall their
commutator is $-(\partial_u+\partial_v)/r\ne0$ as in its Theorem
8.7. Probability-changing noncommuting controls prevent identifying
all original native operations with a diagonal/Schur menu. These
geometric facts alone provide neither the acquisition map nor a
global native impossibility theorem.

The acquisition duration and placement must fit the SAME aligned
original clock with no extra time. The five original label measures
in (JR.39) are mathematical output measures; a physical realization
must make the FIRST absorbing failure occur at that elapsed time,
perform no later positive-carrier operation on a failed branch, and
produce live output at time $1$. It must preserve the old stopped
archives, source/epoch identity, permissions and controller updates.
An internal failure-destined label or a timestamp sampled using
$t=z/(2-z)$ for an independent uniform $z\in[0,1]$ does not provide
that physical event, finite exact-time storage or extra execution
time. These obligations remain unresolved. The sharp joint frontier
settles the stated finite mathematical optimization; it neither
realizes it natively nor completes the through-2027 programme.

## 追加锚（本行以下为增补区）
