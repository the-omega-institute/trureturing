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
