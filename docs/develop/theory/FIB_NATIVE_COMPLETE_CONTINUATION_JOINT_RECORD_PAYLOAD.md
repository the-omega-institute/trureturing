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

## 41. Height records at the original sharp cost

**Definition 41.1 (the unchanged full-output problem).** Retain Definition
34.1 and the complete comparison class of (JR.20). In particular the
sole input is one of the twelve normalized states (JR.1), embedded by
$E$ in the original five modes. The processor is one common all-complex
CPTP map, with an actual acquisition factorization, full TP conditional
decoders and the same jointly counted acquisition cut. The ideal targets
are still the coherent live blocks $EU_{e,n}B_yU_{e,n}^\dagger E^\dagger$
of (CG.111), together with all five separately labelled measures
$w_j f_y(t)dt\,P_f$. Here $B_y$ in the ideal target denotes the matrix
of (CG.111); the scalar $B_y$ in resource expressions below always
means (JR.23). The error remains

$$
E(\Phi)=\max_{y\in\{5,16,27\},\ e,n=\pm1}
 \frac12\|\Phi(E\rho_{y,e,n}E^\dagger)-\Omega_{y,e,n}\|_{1,\mathrm{cq}}.
$$

Thus every live coherence, singular-time component, abort, wrong support
and zero-target sector is counted. There is no source prior, helper,
acceptance division, copy, reset, retry, readable old history or quantum
bypass. The isolated CG point, its ranks, normalization, strict source
enclosures, endpoint witnesses and minimax certificate in CG §§13–17
are named ordinary conditional premises. The deductions here reuse that
certificate; they do not authenticate the original algebraic/minimax
certificate anew and carry no Lean/kernel certification.

Let $R$ be an actually generated classical record available at the
acquisition cut, and $F$ the plus effect of a binary record obtained
from that same acquisition. A common classical kernel for $R,F$ may
be included in the actual label $\alpha$. It suffices for maximization
to retain the entire generated label as $R$: classical processing
contracts total variation. Define, on the supported qutrit,

$$
\begin{aligned}
\Delta&=\rho_{27,+,+}-\rho_{5,+,+},\\
\mathcal T(s)&=\sup\left\{
 \operatorname{TV}(P^R_{5,+,+},P^R_{27,+,+}):
 E(\Phi)=E_*,\quad \mathsf V(F)\geq s,\quad
 \mathsf W=\mathsf C(s)\right\},\qquad 0\leq s\leq1.
\end{aligned}
\tag{JR.43}
$$

Here $\operatorname{TV}(P,Q)=\tfrac12\int|dP-dQ|$ on the actual
classical record space; no inaccessible Kraus index is added to it.
The law $P^R_{y,e,n}$ is induced by the actual encoder masses
$\operatorname{tr}\mathcal E_\alpha(E\rho_{y,e,n}E^\dagger)$
and its common classical kernel. Encoder traces on general positive
inputs are unnormalized masses; they are probabilities only when the
actual input is normalized.
The constraint is exactly the original contrast inequality
$\mathsf V(F)=2|\operatorname{Re}F_{01}|/\kappa\geq s$.
It prescribes neither the other entries of $F$ nor the forgotten
channel. In particular (JR.43) does not impose the full binary effects
(CA.11) of [CA, Definition 2.2] or fix $\widehat\Phi_*$ in advance.

The cost is still the maximum over all twelve histories of the
probability that the joint future-accessible input-dependent quantum
fibre has dimension at least three. Retained specimen, memory,
controller, accessible environment and entanglement shares are counted
together. Blank ancillas introduced later are independent; a later
accessible correlated share is not a blank. All other dilation systems
are permanently inaccessible before this same cut.

The necessary statements use the finite class, its countable version
with convergent CP instruments, and only the explicitly stipulated
integrals of CG Convention 21.3: measurable finite fibre dimensions,
measurable encoder/live-decoder Kraus fields, integrable effects and
live Choi matrices, and full-output TP decoders almost everywhere.
Integral encoder densities are CP, without an individual TNI requirement
relative to the reference measure; their integrated effect is $I$.
No arbitrary continuous-outcome disintegration or infinite-dimensional
coding extension is asserted. All attainments below have finite actual
alphabets, which does not enlarge these necessity scopes.

**Convention 41.2 (reused source dictionary).** Keep $D,T,S,M,\kappa$
from (JR.2), the positive $\theta,\omega,\delta,k,v_0,s_0$ of (JR.21),
and $A_y,B_y,C_y$ of (JR.23). For the prescribed $s$ write
$v=v_s$, $u=\theta v+\omega$ and $P_y(s)$ as in (JR.30)–(JR.33).
The sharp law $\mathsf C(s)=P_{27}(s)$, its inverse (JR.42), the
constant interval $[0,s_0]$, and the complete H/L attainer (JR.34)–(JR.41)
are reused from §§34–40. In CA notation
$(\alpha,\beta,\ell)=(\theta,\omega,\delta)$ and
$(p_s,q_s)=(1-u,1-v)$; CA's $B_0$ is the matrix called $Q_0$ below.

## 42. Supported rigidity from the original error and cost equalities

**Theorem 42.1 (every sharp-cost error optimizer).** Every actual
implementation in (JR.43), for every $0\leq s\leq1$, has on the
supported qutrit algebra the following equalities. Here $\Lambda_\Phi$
is its supported live compression and $G_f,G_o$ are its total canonical
failure and other effects, as in (CG.155):

$$
\begin{aligned}
\Lambda_\Phi&=\Lambda_*:=D(\cdot)D^\dagger+
 T(\cdot)T^\dagger+S(\cdot)S^\dagger,\\
G_f&=M,\qquad G_o=0,\\
Q_H&=(1-u)D^\dagger D+(1-v)T^\dagger T.
\end{aligned}
\tag{JR.44}
$$

Each high-fibre branch has zero later nonlive mass on supported inputs,
or this holds almost everywhere in the stipulated integral case.
These are supported live/effect equalities. They assert neither full
five-mode channel uniqueness nor uniqueness of the individual
labelled failure-time CP measures.

Proof. Apply CG Theorem 17.2 and Corollary 17.3 to the original full
optimizer, with the finite compression only as a necessary test. Before
averaging, the live Choi support lies in
$\operatorname{span}\{|D\rangle\!\rangle,|T\rangle\!\rangle,
|S\rangle\!\rangle\}$, $G_o=0$, $G_f|0\rangle=0$, and every
positive-weight endpoint witness individually saturates (CG.157).
The averaged Choi equality fixes the diagonal of the unaveraged
coefficient Gram to $(1,1,1)$. These are the credited CG consequences,
not a premise that the unaveraged live map is already $\Lambda_*$.

Choose the actual encoder/live-decoder products and write them uniquely
as $K_j=x_jD+z_jT+w_jS$. Kraus refinements here are analytic devices;
$j$ is not declared observable. Define the low-fibre squared masses
$(u_L,v_L,w_L)$ from these same products. The proof of (JR.27) applies
to their masses without altering the original instrument: sign averaging
only reads diagonal moments and four-sign cost means. In particular

$$
\begin{aligned}
u_L&\leq\theta v_L+\omega w_L,\\
s\leq\mathsf V(F)&\leq
 \sqrt{u_Lv_L}+\sqrt{(1-u_L)(1-v_L)},\\
\mathsf W\geq\overline p_{H,27}&\geq
 A_{27}(1-u_L)+B_{27}(1-v_L)+C_{27}(1-w_L).
\end{aligned}
\tag{JR.45}
$$

For the middle line, TP and $G_f|0\rangle=0$ give zero real total
$DT$ moment. The failure plus effect is dominated by $G_f$, so its
$01$ entry vanishes. Therefore the signed winding identity is
$2\operatorname{Re}F_{01}/\kappa
=\sum_j r_j\operatorname{Re}(\overline x_jz_j)$, after absorbing
actual binary coins. This uses no height-TV average. Let $G_H^L$ denote the sum of the
supported high-live effects
$(\mathcal R_\alpha^L\mathcal E_\alpha)^\dagger(I_3)$ over
$d_\alpha\geq3$. The cost line uses full TP of each decoder, whose
live restriction alone is TNI, so $Q_H-G_H^L\succeq0$.

For $s\leq s_0$, $u_L\leq\delta$ and $v_L,w_L\leq1$.
For $s>s_0$, the monotonicity argument of Theorem 37.2 gives
$v_L\leq v_s$, $u_L\leq\theta v_s+\omega$, $w_L\leq1$.
Since $A_{27},B_{27},C_{27}$ are strictly positive and
$\mathsf W=P_{27}(s)$, equality forces
$(u_L,v_L,w_L)=(u,v,1)$ in both regimes. Also
$Q_H-G_H^L\succeq0$ has zero trace against
$\operatorname{diag}(p_{27})\succ0$. It is zero. Each nonnegative
branch slack consequently vanishes, or vanishes almost everywhere.
This excludes hidden high-fibre failure mass.

The low singular products saturate the determinant/triangle budget:

$$
x_j^2=\theta z_j^2+\omega w_j^2,\qquad
|x_j|^2=\theta|z_j|^2+\omega|w_j|^2.
\tag{JR.46}
$$

Indeed the summed nonnegative slack is zero; a product with $x_j=0$
then has $z_j=w_j=0$. Every nonzero product is on the quadratic
component of the complex singular locus. CA Theorem 5.1, equation
(CA.21), supplies precisely this exposed real equality face: after a
common phase is removed, its coefficients are real. In its pointwise
proof, divide (JR.46) by $x_j^2$ and use equality in the complex triangle
inequality; both squared ratios are nonnegative real. This also handles
one zero ratio. The complex singular plane and relative complex phases
are excluded by equality, not by an imposed real implementation class.

High products have $w_j=0$. On $s\leq s_0$ they also have $z_j=0$,
and hence are phase multiples of $D$. On $s\geq s_0$, the signed
Cauchy–Schwarz inequalities in (JR.45) all saturate, after one global
binary reversal if necessary. Thus

$$
z_j=r_j\sqrt{v/u}\,x_j\quad\text{on low products},\qquad
z_j=r_j\sqrt{(1-v)/(1-u)}\,x_j\quad\text{on high products}.
\tag{JR.47}
$$

Here $u,1-u>0$; the second ratio is zero at $s=s_0$, and at $s=1$
one has $u=v=v_0>0$. Equality with the positive low/high sums forces
a high product with $x_j=0$ to be zero. Consequently high coefficient
projectors are real too. No phases were assumed real before equality.

Let $Z$ be the total real coefficient Gram. Its diagonal is one.
The $01$ and $02$ entries of TP, together with $G_f|0\rangle=0$,
give $\kappa Z_{DT}=\kappa_{02}Z_{DS}=0$, where
$\kappa_{02}=h_0c+h_2d>0$. The only possible remaining perturbation is

$$
\Lambda_\Phi=\Lambda_*+
 t\{T(\cdot)S^\dagger+S(\cdot)T^\dagger\},\qquad t\in\mathbb R.
\tag{JR.48}
$$

At height $27$ the credited endpoint effect is $U_{e,n}R_{27}U_{e,n}^\dagger$
on live and zero on every nonlive sector. Write
$R_{27}=\zeta_{27}\zeta_{27}^T$ with the positive unit vector
$\zeta_{27}=(\beta_{1,*},\beta_{2,*},1)^T/
\|(\beta_{1,*},\beta_{2,*},1)\|$ from (CG.112).
The perturbation changes its live pairing by
$nt\,C_{TS}$, where
$C_{TS}=2(\zeta_{27}^TTa_{27})(\zeta_{27}^TSa_{27})>0$.
Every one of the four endpoint payoffs equals $E_*$, as does the
credited channel's payoff. Both signs of $n$ therefore force $t=0$.
A change of failure measures cannot compensate a witness that vanishes
on those sectors. Thus $Z=I$, $\Lambda_\Phi=\Lambda_*$, and TP gives
$G_f=M$.

Only a real $DT$ cross moment can now remain in the high coefficient
Gram, since it has diagonal $(1-u,1-v,0)$. Its four height-$27$
acquisition probabilities have mean $P_{27}(s)$ and are each at most
$\mathsf W=P_{27}(s)$. All four equal their mean; $q_{27},\kappa>0$
kill that cross moment. This proves the final operator identity in
(JR.44). Nonnegative sum/integral equalities propagate pointwise or
almost everywhere under exactly Definition 41.1's hypotheses. $\square$

## 43. The evaluated strong-regime height-TV law

**Definition 43.1 (unnormalized height differences).** Set

$$
\begin{gathered}
\Delta A=A_{27}-A_5,\quad \Delta B=B_{27}-B_5,\quad
\Delta C=C_{27}-C_5,\\
\xi=\kappa(q_{27}-q_5)>0,\quad
\eta=\kappa_{02}(q_{02,27}-q_{02,5})>0,\quad
\zeta=ac(q_{12,27}-q_{12,5})<0,\\
q_y=\sqrt{y(64-y)}/128,\quad q_{02,y}=\sqrt y/16,\quad
q_{12,y}=\sqrt{64-y}/16,\\
\Xi=M^{1/2}\Delta M^{1/2}\big|_{\operatorname{span}\{|1\rangle,|2\rangle\}}
 =\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},\\
d_f=11m_1/64,\quad
z_f=\frac{\sqrt{m_1m_2}}{16}(\sqrt{37}-\sqrt{59}),\quad
L_f=\|\Xi\|_1=\sqrt{d_f^2+4z_f^2}.
\end{gathered}
\tag{JR.49}
$$

These are unnormalized differences, including the failure part.
In particular $L_f$ is not a conditional-on-failure distance. Put

$$
\begin{aligned}
h_\sigma(s)&=\frac{(1-u)\Delta A+(1-v)\Delta B}{2}
 +\sigma\sqrt{(1-u)(1-v)}\,\xi,\\
\ell_{\sigma,\tau}(s)&=\frac14\left[
 u\Delta A+v\Delta B+\Delta C+2\sigma\sqrt{uv}\,\xi
 +2\tau\sqrt u\,\eta+2\sigma\tau\sqrt v\,\zeta\right],\\
\mathfrak a&=\theta\Delta A+\Delta B,\qquad
\mathfrak b=\omega\Delta A+\Delta C,\\
\mathsf b(v)&=\frac14\left[
 \mathfrak av+\mathfrak b-2\xi\sqrt{v(\theta v+\omega)}
 -2\eta\sqrt{\theta v+\omega}+2\zeta\sqrt v\right],\\
T_{\rm flat}&=(d_f+L_f)/2.
\end{aligned}
\tag{JR.50}
$$

Thus $\mathsf b(v_s)=\ell_{-,-}(s)$; it is a function, distinct from
the transfer amplitude $b$ in $T$.

**Theorem 43.2 (sharp strong-regime height distinguishability).** For
$s_0\leq s\leq1$, the supremum over every optimizer in (JR.43) is

$$
\boxed{\displaystyle
\mathcal T(s)=\frac12\left[
 \sum_{\sigma=\pm1}|h_\sigma(s)|+
 \sum_{\sigma,\tau=\pm1}|\ell_{\sigma,\tau}(s)|+L_f\right]
 =T_{\rm flat}+[-\mathsf b(v_s)]_+.}
\tag{JR.51}
$$

One common finite actual instrument for each prescribed $s$ attains
this value with the original complete output and the sharp acquisition
cost. There is a unique $v_c\in(v_0,1)$ with $\mathsf b(v_c)=0$.
For $s_c=\mathfrak f(v_c)$, $\mathcal T$ strictly decreases from
$T_{\rm flat}-\mathsf b(1)$ on $[s_0,s_c]$, then is constant at
$T_{\rm flat}$ on $[s_c,1]$. In particular
$\mathcal T(s_0)=T_{\rm flat}-\mathsf b(1)$ and
$\mathcal T(1)=T_{\rm flat}$. No feasible contrast exceeds $1$ by
Theorem 37.2.

Proof of the upper bound. Theorem 42.1 fixes the low/high coefficient
Grams to $\operatorname{diag}(u,v,1)$ and
$\operatorname{diag}(1-u,1-v,0)$. Equation (JR.47) and the real null
condition leave only the four low rays
$(\sqrt u,\sigma\sqrt v,\tau)$ and two high rays
$(\sqrt{1-u},\sigma\sqrt{1-v},0)$. The three zero low cross moments
force total weights $1/4$ on each of the four rays: their three signed
moments and total mass determine the four weights. The high weights
are $1/2$ when $v<1$. At $v=1$ the high rays coincide; arbitrary
proportional splitting leaves the same absolute-difference sum.
The resulting product differences are exactly (JR.50)'s $h,\ell$.

For an actual acquisition label $\alpha$, separate its live Kraus
products and total later failure effect $B_\alpha\succeq0$ only to
bound its absolute height-probability difference. By (JR.44),
$\sum_\alpha B_\alpha=M$. On $\operatorname{ran}M$ write
$B_\alpha=M^{1/2}E_\alpha M^{1/2}$; the positive $E_\alpha$ sum to
identity. Then

$$
\sum_\alpha|\operatorname{tr}(B_\alpha\Delta)|
 =\sum_\alpha|\operatorname{tr}(E_\alpha\Xi)|
 \leq\sum_\alpha\operatorname{tr}(E_\alpha|\Xi|)=L_f.
$$

For integrals the same inequality is integrated. Splitting a label
and analytically refining its products can only increase this upper
bound. It creates no readable record. Combining it with the six live
rays proves the first bound in (JR.51), without averaging height TV or
assuming an optimizer's individual failure measures. Section 44 supplies
actual common attainment of all its terms.

For the evaluation, the exact coefficient formulas (CG.112)–(CG.116),
(CG.134), with the rational-centre radius-$10^{-24}$ box of CG
Proposition 13.2, give the following strict rational enclosures and
inequalities:

$$
\begin{gathered}
10^6(h_0,h_1,h_2,a,b,c,d)\in
 \prod_{j=1}^7(N_j,N_j+1),\quad
N=(984341,706284,809497,65664,145993,15496,98783),\\
\mathfrak a,\mathfrak b>0,\quad
\Delta A/2>\xi,\quad \mathfrak a<2\sqrt\theta\,\xi,\quad
\mathfrak a+\mathfrak b>2\sqrt\delta\,\xi,\\
\mathfrak a+2\sqrt\theta\,\xi>\theta\eta/\sqrt\omega,\quad
\xi\sqrt\omega>|\zeta|,\\
\ell_{\sigma,\tau}(u=v=v_0)>1/25000
 \quad(\sigma,\tau=\pm1),\qquad
-9/10000<\mathsf b(1)<-8/10000.
\end{gathered}
\tag{JR.52}
$$

These comparisons concern the given box, not a fitted new root.
They can be obtained directly by interval substitution in the source
adjugates: $H=1000\eta_0\operatorname{adj}S_0$,
$Q^{01}=\eta_1\operatorname{adj}S_{01}$,
$Q^{02}=\eta_2\operatorname{adj}S_{02}$, followed by the positive-pivot
amplitude formulas (CG.134). Every denominator is strictly positive
on that box. Rational arithmetic with outward square-root bounds
therefore supplies (JR.52) without an inference from sampled signs.

Here is the interval-wide sign argument from those finite comparisons.
Since $u\leq v$, $1-u\geq1-v$ and $\Delta A/2>\xi$, both
$h_\sigma$ are positive. The quadratic

$$
q(v)=(\mathfrak av+\mathfrak b)^2
      -4\xi^2v(\theta v+\omega)
$$

is strictly concave by $\mathfrak a<2\sqrt\theta\xi$.
Its endpoint values on $[0,1]$ are positive by (JR.52). Thus
$\mathfrak av+\mathfrak b>2\xi\sqrt{v(\theta v+\omega)}$.
It follows that $\ell_{-,+}>0$, since its remaining terms
$2\eta\sqrt u-2\zeta\sqrt v$ are positive.
Also $\ell_{+,+}>\ell_{-,+}$ because
$\xi\sqrt u>|\zeta|$. For $\ell_{+,-}$ the derivative with respect
to $v$, multiplied by four, is bounded below by
$\mathfrak a+2\sqrt\theta\xi-\theta\eta/\sqrt\omega>0$;
its value at $v_0$ is positive. Only $\ell_{-,-}=\mathsf b$ can
change sign. Indeed

$$
4\mathsf b'(v)=\mathfrak a
 -\xi\frac{2\theta v+\omega}{\sqrt{v(\theta v+\omega)}}
 -\frac{\theta\eta}{\sqrt{\theta v+\omega}}
 +\frac{\zeta}{\sqrt v}<0
\tag{JR.53}
$$

on $[v_0,1]$, since the displayed fraction exceeds $2\sqrt\theta$.
The endpoint signs in (JR.52) give exactly one root. The inverse
$v_s$ strictly decreases with $s$ by Theorem 37.2. Finally TP gives
$\operatorname{tr}(\Lambda_*(\Delta))=-\operatorname{tr}(M\Delta)=d_f$.
Replacing a sole possibly negative live difference by its absolute
value proves the positive-part expression and all asserted segments.
For orientation, conditional on the same source box,

$$
\frac{18047653179}{10^{12}}<v_c<\frac{18047653180}{10^{12}},\qquad
0.9961174281164<s_c<0.9961174281172.
$$

The first enclosure follows from opposite signs of $\mathsf b$ at
those rational endpoints; uniqueness follows from (JR.53), not from
floating root finding. $\square$

## 44. A common finite actual attainer on the full complex output

**Definition 44.1 (spectral failure readout with the existing live
attainer).** For $s_0\leq s\leq1$, use exactly the high $H_\sigma$ and
image-compressed low $L_{\sigma,\tau}$ branches of Definition 38.1.
Their rank-three/rank-two statements and full TP isometric decoders
are (JR.37)–(JR.38), also the range realization of IR Lemma 4.2.
Let $v_\epsilon$ be a fixed real unit eigenvector of $\Xi$ for its
positive or negative eigenvalue, $\epsilon=\pm1$. The projections are

$$
\Pi_\epsilon=\frac12\left[I_2+
 \epsilon\frac{2\Xi+d_fI_2}{L_f}\right],\qquad
C_{f,\epsilon,r}=\frac1{\sqrt2}\langle v_\epsilon|M^{1/2},
 \qquad \epsilon,r=\pm1.
\tag{JR.54}
$$

The row is zero on coordinate $0$ and its fibre is one-dimensional.
Its full TP decoder sends a scalar $z$ to the whole measure
$z w_jg(t)dt\,P_f$ in each of the five original labels, where
$g(t)=2/(1+t)^2$. This is the spectral scalar realization of IR
Theorem 5.2, applied to the height difference. Set the designated binary
record to $r=\sigma$ on live branches, and to the row label $r$ on
failure branches. Retain the entire generated branch label as $R$.

On five modes precompose supported encoders with $E^\dagger$ and add
the two scalar complement branches with effect $(I_5-P)/2$, one for
each $r$. Each is decoded to $z g(t)dt\,P_f$ only at original
label $2$. Its Kraus multiplicity is discarded, as in Definition 38.1.
All matrices, spectral vectors and classical choices are fixed before
the sole specimen arrives. The spectral outcome is actually generated
by this new encoder; it is not an index read from an old discarded
environment. Only its declared fibre and dephased classical label
remain accessible after the cut.

**Proposition 44.2 (joint attainment and the full-output identity).**
Definition 44.1 has full TP decoders, total encoder effect $I_5$ and
$\mathsf V(F)=s$, $\mathsf W=P_{27}(s)$. On each normalized original
input its acquired law is

$$
\begin{aligned}
p(H,\sigma\mid y,e,n)&=P_y(s)/2+
 \sigma\sqrt{(1-u)(1-v)}\,\kappa enq_y,\\
p(L,\sigma,\tau\mid y,e,n)&=\frac14\left[
 uA_y+vB_y+C_y+2\sigma\sqrt{uv}\,\kappa enq_y
 +2\tau\sqrt u\,\kappa_{02}e q_{02,y}
 +2\sigma\tau\sqrt v\,acn q_{12,y}\right],\\
p(f,\epsilon,r\mid y,e,n)&=\frac12\left|
 \left\langle v_\epsilon,
 (\sqrt{m_1}n\sqrt{p_{y1}},\sqrt{m_2}\sqrt{p_{y2}})^T
 \right\rangle\right|^2,\\
p(\perp,r\mid y,e,n)&=0,\qquad
p(F=r\mid y,e,n)=1/2+r\kappa s\,enq_y.
\end{aligned}
\tag{JR.55}
$$

For every complex five-mode input $A$, forgetting all acquisition labels
gives the complete channel

$$
\begin{aligned}
\Phi^L(A)&=E\Lambda_*(E^\dagger AE)E^\dagger,\\
\Phi_j^f(A)(B)&=\left(\int_Bg(t)dt\right)
 \left[w_j\operatorname{tr}(EME^\dagger A)
  +\mathbf1_{j=2}\operatorname{tr}((I_5-P)A)\right]P_f,
 \quad j=0,\ldots,4,
\end{aligned}
\tag{JR.56}
$$

for every labelled Borel time set $B\subseteq[0,1]$. All cross-support
operators and extra-sector outputs vanish. The same identity holds
at every passive-reference amplification, with the exact conditional
reference operators. Hence all twelve original full-cq errors are those
of $\widehat\Phi_*$, and $E(\Phi)=E_*$. This common instrument attains
(JR.51), including at its endpoints.

Proof. The live laws and ranks reuse (JR.37), (JR.38) and (JR.40).
The spectral rows have total effect $M$, and each binary value receives
$M/2$. The live coefficient Gram sums to $I_3$, so the live encoder effect
is $D^\dagger D+T^\dagger T+S^\dagger S=I_3-M$. Adding the
spectral rows gives supported encoder effect $I_3$; the complement
gives $I_5-P$.
All individual positive effects are bounded by this sum and are TNI.
The live decoders are isometries on their entire fibres. The scalar
decoders are TP because $\sum_jw_j=1$ and $\int_0^1g(t)dt=1$.
Thus no live-only normalization is used. The binary effect is (JR.41)
on the supported algebra, and is
$(I_5+r\kappa sEX_{01}E^\dagger)/2$ on five modes.
This particular attainer satisfies (CA.11); that is a consequence of
the construction, not an assumption about every optimizer.

The spectral row effects sum to $M$, so their decoded maps sum to
$w_jg(t)dt\,\operatorname{tr}(MA_V)P_f$, with
$A_V=E^\dagger AE$. The complement supplies the second term of
(JR.56), exactly as in (JR.39). These are equalities of Kraus
conjugations and trace functionals on all complex matrix units.
For a joint operator $X$ with passive reference $\mathcal H_R$, the
live term is obtained by $(EK E^\dagger\otimes I_R)X
(EK^\dagger E^\dagger\otimes I_R)$, summed over $K=D,T,S$.
The two failure reference factors are, respectively,

$$
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X],\qquad
\operatorname{Tr}_5[((I_5-P)\otimes I_R)X].
$$

They multiply $P_f$, the original weights and $\int_Bg(t)dt$ as
in (JR.56); they are not replaced by an unconditional reference state.
This proves the entire complex/reference/labelled-Borel-time identity.
The two zero-weight original labels stay zero, the others stay separate,
no singular part is added and common fixed metadata are preserved.
The actual density $g$ is not asserted to equal an ideal $f_y$.
Equality to the same complete approximate channel is precisely what
allows reuse of the original HALF full-cq error certificate.

Only the high H fibres have dimension at least three, so their effect
and each history's cost are (JR.36). The row law in (JR.55) is its
ordinary Born probability on a normalized input; it has no division by
failure mass. Its two spectral outcomes give absolute height-difference
sum $L_f$. The live differences give $h,\ell$, so all terms of the
upper bound in Theorem 43.2 are attained by this one instrument.
A dilation must discard every other system permanently before the cut;
retaining a correlated share changes the stated cost. $\square$

**Corollary 44.3 (strict actual failure-record gain).** For each
$s\in[s_0,1]$, compare Definition 44.1 with the H/L instrument of
Definition 38.1, keeping every label of both instruments. At the same
contrast, worst-history cost and forgotten complete channel, the former
has full acquired height TV larger by

$$
\frac{L_f-d_f}{2}>0.
\tag{JR.57}
$$

Proof. In the coordinate failure readout of (JR.40), the $j=1$ height
difference is $-d_f$ in total and the $j=2$ difference is zero.
The spectral readout instead gives $L_f$, and $z_f\ne0$ implies
$L_f>d_f$. The live labels agree. This comparison enacts a different
measurement and does not recover a discarded label. $\square$

## 45. Exact finite optimization on the weak cost plateau

**Theorem 45.1 (four real PSD matrices and actual attainment).** Put
$K_0=D,K_1=T,K_2=S$ and

$$
L_0=\operatorname{diag}(\delta,1,1),\qquad
Q_0=\operatorname{diag}(1,-\theta,-\omega),\qquad
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger)\in\mathbb R.
$$

For $0\leq s\leq s_0$, define

$$
\begin{aligned}
J_s=\max\quad &\sum_{r,\epsilon=\pm1}\epsilon\operatorname{tr}(NZ_{r,\epsilon})\\
\text{subject to}\quad
&Z_{r,\epsilon}\in\operatorname{Sym}_3(\mathbb R),\quad
 Z_{r,\epsilon}\succeq0,\quad
 \operatorname{tr}(Q_0Z_{r,\epsilon})=0,\\
&\sum_{r,\epsilon}Z_{r,\epsilon}=L_0,\qquad
 \sum_{r,\epsilon}r(Z_{r,\epsilon})_{01}\geq s.
\end{aligned}
\tag{JR.58}
$$

Then the exact original height-record optimum is

$$
\boxed{\displaystyle
\mathcal T(s)=\frac12[(1-\delta)\Delta A+L_f+J_s],
 \qquad 0\leq s\leq s_0.}
\tag{JR.59}
$$

The feasible set is nonempty compact, the maximum exists, and an optimal
tuple gives one finite actual five-mode instrument with at most twenty
branches. It has full TP decoders, original error $E_*$, cost
$\mathsf C(s)$, contrast at least $s$, and the full complex/reference/
labelled-Borel-time identity (JR.56). Formula (JR.58) is an exact
optimization with attainment; its value for $s<s_0$ is not evaluated
here. It does not replace the unrestricted complex cone (IR.68), the
set $\mathcal K_s$ of (IR.69), or CA's prescribed-effect problem.

Proof. For necessity use Theorem 42.1. The high products are proportional
to $D$ and have positive total height difference $(1-\delta)\Delta A$.
Every low product is a real null vector after removal of a phase;
write it $c=(x,z,w)^T$. Group its coefficient projector by its actual
binary label $r$ and by $\epsilon=\operatorname{sign}(c^TNc)$,
assigning zero values either sign. The four sums or integrals are real
PSD, have zero $Q_0$ trace and total $L_0$. The high products give zero
$DT$ moment; all failure subeffects kill coordinate $0$.
After a global binary reversal, the winding identity is exactly
$\mathsf V(F)=\sum_{r,\epsilon}r(Z_{r,\epsilon})_{01}$.
This proves the final constraint, with no factor-of-two change and no
condition on any other entry of $F$. The grouped signed objective is
the sum of absolute low-product height differences. Refinement and
live/failure separation only upper-bound the TV of the original actual
label; the failure contribution is at most $L_f$ as in §43.
This proves the upper direction of (JR.59).

For sufficiency reuse IR Lemma 10.1 and CA Theorem 5.1 on each
$Z=Z_{r,\epsilon}$. The useful rank count is

$$
Z=\sum_{j=1}^{\operatorname{rank}Z}c_jc_j^T,\qquad
c_j^TQ_0c_j=0,
\tag{JR.60}
$$

with no vectors for $Z=0$. To see the support count, restrict
$Z^{1/2}Q_0Z^{1/2}$ to $\operatorname{ran}Z$. It is real symmetric
with trace zero. The zero-Rayleigh-basis induction in (IR.58), equivalently
(CA.22), operates on this support: choose a zero Rayleigh vector between
a positive and a negative eigenvector, remove it, and repeat on its
orthogonal complement. A zero compression permits any basis.
Multiplying that basis by $Z^{1/2}$ gives (JR.60). The induction on
all of $\mathbb R^3$ alone gives at most three, whereas the support
restriction gives the asserted rank count, including singular $Z$.
Every nonzero $c_j$ has $x_j\ne0$, and IR Lemma 4.2 makes $K(c_j)$
rank exactly two.

For each actual low label $(r,\epsilon,j)$, supply encoder
$V_{c_j}^\dagger K(c_j)$ into its fixed two-dimensional image and
full TP decoder $X\mapsto EV_{c_j}XV_{c_j}^\dagger E^\dagger$,
using the fixed isometries (IR.22). Add the two high branches with
live products $\sqrt{(1-\delta)/2}\,D$, tagged by fair $r$,
and full TP decoder $X\mapsto EXE^\dagger$ on each high fibre.
Add all four spectral scalar failure rows (JR.54), and the two scalar
complement branches of Definition 44.1. Precompose supported encoders
with $E^\dagger$ on five modes. These are at most $12+2+4+2=20$
actual branches. The true acquired record retains $(r,\epsilon,j)$
and the full high/failure/complement labels, with probabilities

$$
p(r,\epsilon,j\mid y,e,n)
 =\|K(c_{r,\epsilon,j})U_{e,n}a_y\|^2
\tag{JR.61}
$$

on low branches, fair high probabilities $(1-\delta)A_y/2$, and the
failure law of (JR.55). All nondeclared dilation systems are permanently
inaccessible before the cut.

The total live coefficient Gram is
$L_0+\operatorname{diag}(1-\delta,0,0)=I_3$. Thus the live encoder
effect is $D^\dagger D+T^\dagger T+S^\dagger S=I_3-M$. Adding
the spectral failure effect gives $I_3$; the complement gives $I_5$.
Individual effects are positive and bounded by this total. The live
decoders are TP isometries and scalar decoders have exactly the TP
integrals in §44. Hence the construction gives (JR.56) on every complex
input and, with its conditional partial traces, at every reference and
Borel time set. Cross-support and extra-sector maps vanish. Thus every
original error constraint, including height $16$, is retained. Its only
high-fibre effect is $(1-\delta)D^\dagger D$, so its worst-history
cost is $(1-\delta)A_{27}=\mathsf C(s)$. Its contrast is the last
sum in (JR.58), at least $s$; its other binary-effect entries are free.

The actual refined low-label TV is at least the grouped signed
objective. The high and failure terms attain their respective bounds.
The feasible set of (JR.58) is closed and bounded since
$0\preceq Z_{r,\epsilon}\preceq L_0$; it is nonempty using the
H/L instrument at $s_0$ with the classical kernel (JR.35), retaining
all labels. Thus a maximizing tuple exists. Realizing it as above gives
actual TV at least the right side of (JR.59). The already proved
universal upper bound forbids strict excess. This is actual common
finite attainment, using the same compact-moment realization mechanism
as IR §11 and CA §6, without compactness of the full time-output space.
At $s=s_0$, signed Cauchy–Schwarz equality gives the four H/L low rays,
so (JR.59) agrees with (JR.51). At $s=0$ the cost is still the strictly
positive original plateau cost. $\square$

## 46. A strict interior comparator retaining every generated label

**Proposition 46.1 (same contrast, cost and complete channel).** Let

$$
s_{\rm int}=2s_0/3,\qquad
c_*=(\sqrt\delta,-1,-1)^T/\sqrt3,\qquad
Z_{\rm rem}=L_0-c_*c_*^T.
\tag{JR.62}
$$

There is an actual finite instrument with three rank-two low live
products, fair binary high and failure branches, contrast exactly
$s_{\rm int}$, cost $\mathsf C(s_{\rm int})$, and forgotten complete
channel (JR.56), such that

$$
\operatorname{TV}(P^R_{5,+,+},P^R_{27,+,+})
 \geq T_{\rm flat}-\frac43\mathsf b(1)
 >\mathcal T(s_0),\qquad
\text{gap}\geq-\mathsf b(1)/3>2/7500.
\tag{JR.63}
$$

It strictly exceeds a comparator at the same required contrast and cost,
with the same complete channel and every original comparator label kept.
No optimality of these three low branches is asserted.

Proof. One has $c_*^TQ_0c_*=0$ and
$Z_{\rm rem}=L_0^{1/2}(I-aa^T)L_0^{1/2}$ with
$a=(1,-1,-1)^T/\sqrt3$. It is PSD of rank two and has zero
$Q_0$ trace. The supported version (JR.60) of IR Lemma 10.1 gives
$Z_{\rm rem}=c_1c_1^T+c_2c_2^T$ with real null $c_1,c_2$.
Supply the three image encoders for
$K_*=K(c_*)=(\sqrt\delta D-T-S)/\sqrt3$, $K(c_1)$, $K(c_2)$.
Report $r=-1$ on $K_*$ and $r=+1$ on the other two, while retaining
the three distinct acquired labels. Use the two fair high branches and
all spectral failure/complement branches from the proof of Theorem 45.1.
This is one eleven-branch five-mode instrument, with the same full TP
decoders and the full complex/reference/labelled-Borel identity (JR.56).
Its effect normalization and full-output error follow from that proof.

Its signed contrast is $-2(c_*c_*^T)_{01}=2s_0/3$, and only the high
branches cost dimension three. The complete supported plus effect is

$$
F_+=\frac{I_3}{2}+\frac12\left[
 \delta D^\dagger D+T^\dagger T+S^\dagger S-2K_*^\dagger K_*\right].
\tag{JR.64}
$$

On five modes it is $EF_+E^\dagger+(I_5-P)/2$.
This effect satisfies the original contrast constraint, not the
prescribed full binary-effect identity (CA.11). For example its $02$
entry is $s_0\kappa_{02}/3>0$, whereas (CA.11) has zero $02$ entry.
This distinction prevents using the example as a counterexample to CA's
narrower class or its resource classification.

The $K_*$ height difference is $4\mathsf b(1)/3<0$. The total live
difference is $d_f$, and the high difference is
$(1-\delta)\Delta A>0$. The other two low differences have sum
$\delta\Delta A+\Delta B+\Delta C-4\mathsf b(1)/3>0$.
Their absolute sum is at least that sum. Adding the actual spectral
failure contribution $L_f$ proves the first inequality in (JR.63).
The strong endpoint is $T_{\rm flat}-\mathsf b(1)$, so its difference
is at least $-\mathsf b(1)/3>2/7500$ by (JR.52).

For the comparator, take Definition 44.1 at $s_0$ and apply the kernel
(JR.35) with parameter $s_{\rm int}/s_0=2/3$ to report the lower
binary contrast. Keep the old $\sigma$, every $\tau$ and spectral
failure label, the branch type, and the new reported binary value.
Write $\sigma(\alpha)$ for the old designated binary value, including
the old $r$ on scalar rows. For each old label $\alpha$, its two new
probabilities are $p_y(\alpha)k(r\mid\sigma(\alpha))$ with the same nonnegative
input-independent kernel. Their absolute height differences sum to
$|p_{27}(\alpha)-p_5(\alpha)|$. Consequently the comparator's full
actual-record TV remains exactly $\mathcal T(s_0)$, while its binary
contrast is $s_{\rm int}$, cost is the same plateau value and forgotten
full channel is unchanged. Reporting $\sigma$ directly below $s_0$
would have contrast $s_0$, so this kernel is required for the claimed
exact lower contrast. No comparator label is discarded. $\square$

## 47. Correspondence, mathematical credit and residual obligations

**Convention 47.1 (the original-objective delta and its antecedents).**
The additional `repo-derived` content is the supported all-error-optimizer
sharp-cost bridge (JR.44), the evaluated strong height-TV objective
(JR.51), its common actual height-attaining measurement, and the exact
weak-plateau height optimization (JR.58)–(JR.59) with strict same-cost,
same-complete-channel, all-record comparison (JR.63). This is a bounded
original-objective delta relative to the cited sources, not a worldwide
novelty claim. The three-low-branch comparison is a lower bound;
Sections 48–49 give its exact symmetric-point TV and a strict local
improvement by another three-low-branch instrument. Evaluating $J_s$
and its analytic plateau segments remains unresolved.

The sharp cost, its inverse and plateau, and the H/L complete attainer
are entirely reused from JR §§34–40. CG Theorem 17.2 and Corollary
17.3 supply support and individual endpoint saturation. The exposed
real equality face is CA Theorem 5.1, not a new cone theorem here.
The finite real null decomposition is IR Lemma 10.1, with its induction
restricted to $\operatorname{ran}Z$ for the rank count used above.
IR Lemma 4.2 and Theorem 5.2 supply fixed-image compression and spectral
scalar failure realization. IR §11 and CA §6 supply the finite compact
moment/actual-realization mechanism. CA Theorem 4.3's full complex cone
and six atoms, Theorem 6.3's at-most-twenty-four-branch resource
realization, and Theorems 8.1–8.3's singleton/exceptional-segment resource
classification are existing results. Neither a second proof of those
results nor a broader resource classification is claimed. CA fixes the
complete channel and the exact effects (CA.11); the present original
contrast inequality permits other effect coordinates, as (JR.64) shows.

[Real coefficient Grams and a small-record resource law](https://github.com/the-omega-institute/trureturing/blob/605dc535dd6054581ecd337dac446d76a6c23fbb/docs/develop/theory/FIB_NATIVE_REAL_GRAM_SMALL_RECORD_RESOURCE_LAW.md),
Sections 4–9, evaluates fixed-channel, exact-binary-effect finite-class
selected per-input acquisition minima on real positive-definite
coefficient Grams and sufficient small-strength caps. Its at-most-fourteen
branches and selected-coordinate Pareto points are credited results.
Those Pareto vectors raise all three original sharp sign means on their
stated interval, rather than obeying the sharp worst-history equality
in (JR.43). That supplier does not evaluate the present all-record-TV
objective and is not a new premise of the local comparison below.

The generic compatibility mechanisms are `literature-attested` as in
Conventions 33.1 and 40.1: Leppäjärvi–Sedlák, Definition 8, Remark 3 and
Proposition 7, and Muñoz-Moller–Leppäjärvi–Heinosaari, Proposition 1,
require a common finite-dimensional compatible realization. They do not
supply an accessible discarded environment or allow separately optimal
records to be combined. Sekatski's rank/image factorization supplies the
compression mechanism, not this state-dependent acquisition cost.
Uhlmann, [*Roofs and Convexity*, Proposition 2.2](https://arxiv.org/pdf/1108.3218),
is a related affine-flat decomposition antecedent; the real null argument
used here is already in IR and CA. Generic spectral, trace-norm and
Born-effect identities are likewise reused, rather than counted as new
height-TV mathematics. No recovery error, diamond distance or cb-norm
objective replaces the original twelve-state HALF complete-cq error.

Universal quantifiers in these conditional ordinary proofs rest on the
support, nonnegative equality, signed Cauchy–Schwarz, trace-norm and
finite realization arguments. A finite set of numerical instruments,
time sets or references can check their formulas but cannot prove those
quantifiers. The root isolation, exact ranks and original minimax
certificate remain the named CG premises; derived strict scalar signs
such as (JR.52) do not reauthenticate that certificate. The rigidity
identifies only supported live and aggregate effects, leaving full
five-mode optimizer and individual failure CP-measure classification
unresolved.

**Definition 47.2 (retained native acquisition and time obligations).**
All attaining encoders, generated classical flags, calibrated support
and image isometries, coherent storage, spectral measurement and full
TP conditional decoders are explicitly supplied operations. Their
lawful enactment on the unknown specimen under the original permissions
remains an implementation obligation. The joint cut must include every
future-accessible input-dependent quantum share; its duration and
placement must fit the same aligned clock without extra time. Fixed
matrices, an abstract dilation and permanent environmental discard in a
mathematical model grant no actuator, native rotation, measurement or
permission.

`OriginalControlComposition.OriginalControl` is the finite-duration,
continuity, strict-height-domain, bounded-phase-variation and
absolute-continuity/finite-piecewise-$C^1$ path predicate described in
Definition 40.2. It is not a constructor of the operations above.
The probability-changing noncommuting fields of [Probability/Phase
Transport][PPT], Definition 10.1 and Theorem 8.7, also remain: their
double-wall commutator is nonzero. They prevent treating a diagonal or
Schur menu as exhaustive, but furnish neither arbitrary acquisition
access nor a global native impossibility theorem.

For every full output (JR.56), a native realization must make the first
absorbing failure actually occur at elapsed time $t$, with no later
positive-carrier action after failure, and terminal live output at time
$1$. All five original labels, stopped archives, source/epoch identity,
permissions and controller updates must retain their original semantics.
A failure-destined acquired label or a subsequently sampled timestamp
does not supply that absorbing event or its same-clock timing. These
native bridges, together with the unevaluated weak-plateau optimum,
remain unresolved; the finite mathematical increment does not complete
the through-2027 programme.

[CA]: FIB_NATIVE_COMPLEX_ATOMIC_CONE_AND_OPTIMAL_RESOURCE_FACES.md
[IR]: FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md

## 追加锚（本行以下为增补区）

## 48. A feasible local improvement of the symmetric three-low-branch point

**Definition 48.1 (the local curve in the unchanged original class).**
Keep the sole specimen, all twelve histories, HALF complete-cq error,
actual record $R$, binary effect $F$, joint cost and necessity scope of
Definition 41.1. All source-root, normalization, rank and minimax
premises remain those of that definition. In coefficient coordinates
$(D,T,S)$, the matrix $N$ of Theorem 45.1 is explicitly

$$
N=\begin{pmatrix}
\Delta A&\xi&\eta\\
\xi&\Delta B&\zeta\\
\eta&\zeta&\Delta C
\end{pmatrix},\qquad
L_0=\operatorname{diag}(\delta,1,1),\quad
Q_0=\operatorname{diag}(1,-\theta,-\omega).
\tag{JR.65}
$$

These entries follow by expanding
$\operatorname{tr}(K_i\Delta K_j^\dagger)$ with (JR.2) and (JR.49).
They concern the two actual positive-sign heights, without replacing
any acquisition law by its sign average. Set

$$
\begin{gathered}
\tau_0=\frac13,\qquad \tau_1=\frac{1003}{3000}
 =\tau_0+\frac1{1000},\qquad
\chi=\frac{\theta+2\omega}{\theta-\omega},\\
Y_\tau=\frac13+\chi(\tau-\tau_0),\qquad
Z_\tau=\frac13-(1+\chi)(\tau-\tau_0),\\
c_\tau=(\sqrt{\delta\tau},-\sqrt{Y_\tau},-\sqrt{Z_\tau})^T,
\qquad R_\tau=L_0-c_\tau c_\tau^T,
\qquad \tau\in[\tau_0,\tau_1].
\end{gathered}
\tag{JR.66}
$$

Here $Z_\tau$ is a scalar, distinct from the four matrices
$Z_{r,\epsilon}$ in (JR.58); $R_\tau$ is a coefficient matrix,
not the classical record. Let

$$
\begin{aligned}
\phi(\tau)&=c_\tau^TNc_\tau\\
 &=\delta\tau\Delta A+Y_\tau\Delta B+Z_\tau\Delta C
 -2s_0\xi\sqrt{\tau Y_\tau}-2s_0\eta\sqrt{\tau Z_\tau}
 +2\zeta\sqrt{Y_\tau Z_\tau}.
\end{aligned}
\tag{JR.67}
$$

**Proposition 48.2 (feasibility and a strictly decreasing atom).**
Throughout this closed interval, $Y_\tau,Z_\tau>0$,
$c_\tau^TQ_0c_\tau=0$, and $R_\tau$ is PSD of rank two with
$\operatorname{tr}(Q_0R_\tau)=0$. Moreover

$$
-\frac{1095}{10^6}<\phi'(\tau)<-\frac{998}{10^6}
 <-\frac1{2000},\qquad
\frac{1046}{10^9}<\phi(\tau_0)-\phi(\tau_1)
 <\frac{1048}{10^9}.
\tag{JR.68}
$$

Proof. The positive coefficient bounds used here are consequences of
the exact rational box in CG Proposition 13.2 and its formulas
(CG.112), (CG.113), (CG.116), (CG.134), not additional fitted
parameters. They give $\theta-\omega>0$ and the following strict
rational enclosures; terminating decimals in this table are exact
rationals.

| Quantity | Lower bound | Upper bound |
| --- | --- | --- |
| $\delta$ | $0.0156$ | $0.0159$ |
| $s_0$ | $0.124$ | $0.127$ |
| $\chi$ | $1.475$ | $1.52$ |
| $\Delta A$ | $0.0807$ | $0.0809$ |
| $\Delta B$ | $0.00291$ | $0.00294$ |
| $\Delta C$ | $0.00167$ | $0.00169$ |
| $\xi$ | $0.0188$ | $0.0191$ |
| $\eta$ | $0.0175$ | $0.0178$ |
| $-\zeta$ | $0.000100$ | $0.000104$ |

In particular $Y_\tau\geq1/3$ and
$Z_\tau\geq1/3-2.52/1000>0$. The definitions give exactly

$$
\tau+Y_\tau+Z_\tau=1,\qquad
\delta\tau=\theta Y_\tau+\omega Z_\tau,\qquad
c_\tau^TL_0^{-1}c_\tau=1.
\tag{JR.69}
$$

For $a_\tau=(\sqrt\tau,-\sqrt{Y_\tau},-\sqrt{Z_\tau})^T$,
therefore,
$R_\tau=L_0^{1/2}(I-a_\tau a_\tau^T)L_0^{1/2}$.
This proves its positivity, rank and trace claim. No new general
null-decomposition assertion is needed; the residual decomposition is
the rank-two case of IR Lemma 10.1 and CA Theorem 5.1.

Differentiating the displayed radicals, whose arguments are positive,
gives

$$
\begin{aligned}
\phi'(\tau)={}&\delta\Delta A+\chi\Delta B-(1+\chi)\Delta C\\
 &-s_0\xi\frac{Y_\tau+\chi\tau}{\sqrt{\tau Y_\tau}}
 -s_0\eta\frac{Z_\tau-(1+\chi)\tau}{\sqrt{\tau Z_\tau}}\\
 &+\zeta\frac{\chi Z_\tau-(1+\chi)Y_\tau}
                   {\sqrt{Y_\tau Z_\tau}}.
\end{aligned}
\tag{JR.70}
$$

For example, at $\tau_0$ this simplifies to
$\delta\Delta A+\chi\Delta B-(1+\chi)\Delta C
-s_0(1+\chi)\xi+s_0\chi\eta-\zeta$.
The table gives the entirely rational upper bound

$$
\begin{aligned}
\phi'(\tau_0)<{}&
0.0159(0.0809)+1.52(0.00294)-2.475(0.00167)\\
&-0.124(2.475)(0.0188)+0.127(1.52)(0.0178)+0.000104\\
={}&-\frac{151937}{250000000}<-\frac1{2000}.
\end{aligned}
\tag{JR.71}
$$

The stronger whole-segment and endpoint bounds in (JR.68) use the
original rational coefficient box, rather than just this coarse table.
Their directed evaluation can be specified entirely by rational
operations: use mesh $2^{-224}$, enclose each exact input interval
outwards, and round each lower/upper endpoint after every sum, product
or quotient respectively down/up to that mesh. For a nonnegative
endpoint $k/2^{224}$, bound its square root by
$\lfloor\sqrt{k2^{224}}\rfloor/2^{224}$ and
$\lceil\sqrt{k2^{224}}\rceil/2^{224}$. Division is used only for
intervals separated from zero. Reconstruct $H,Q^{01},Q^{02}$ from
the CG adjugate formulas, and their positive-pivot factors from
(CG.134); all nine box radii are exactly $10^{-24}$.
Inserting $[1/3,1003/3000]$ into (JR.70), with $Y,Z$ expressed
relative to $1/3$ as in (JR.66), yields the first two bounds below.
Inserting the two exact rational endpoints separately into (JR.67)
yields the last two:

$$
\begin{gathered}
\inf\phi'([\tau_0,\tau_1])>-0.001095,\qquad
\sup\phi'([\tau_0,\tau_1])<-0.000998,\\
\inf\bigl(\phi(\tau_0)-\phi(\tau_1)\bigr)>0.000001046,\qquad
\sup\bigl(\phi(\tau_0)-\phi(\tau_1)\bigr)<0.000001048.
\end{gathered}
\tag{JR.72}
$$

Here infimum and supremum refer to the outward arithmetic enclosures;
these contain every value on the inherited box. Thus the comparisons
are strict rational inequalities. Integrating just the derivative
bound would give $1/2000000$; the direct endpoint calculation supplies
the larger $1/1000000$ margin needed below. None of these operations
isolates the original root or proves its minimax identification.
$\square$

**Theorem 48.3 (strict local nonoptimality of the specified symmetric
point).** Let $\mathfrak I_{\rm sym}$ be the three-low-branch instrument
of Proposition 46.1, retaining every low, fair high, spectral failure
and complement label. Its two residual null atoms may be chosen by any
decomposition (JR.60) of $Z_{\rm rem}$. Its actual height-record TV is
exactly $T_{\rm flat}-\phi(\tau_0)$. There is a common finite
instrument $\mathfrak I_1$ with three low live branches and

$$
\begin{gathered}
\operatorname{TV}_{\mathfrak I_1}
 -\operatorname{TV}_{\mathfrak I_{\rm sym}}
 \geq\phi(\tau_0)-\phi(\tau_1)
 >\frac1{1000000},\\
E(\mathfrak I_1)=E_*,\qquad
\mathsf W(\mathfrak I_1)=\mathsf C(s_{\rm int}),\qquad
\mathsf V(F_1)=2s_0\sqrt{\tau_1Y_{\tau_1}}>s_{\rm int}.
\end{gathered}
\tag{JR.73}
$$

Both instruments have the same entire forgotten channel (JR.56), all
original failure labels and exact-time measures, the same acquisition
cut, and $s_{\rm int}=2s_0/3$. Optional classical attenuation retaining
all labels makes the new contrast exactly $s_{\rm int}$ with the same
TV, cost and complete channel. This refutes optimality of this
specified symmetric point for the original inequality constraint.
The improving witness itself still has three low branches; no
nonoptimality of every three-low-branch construction is implied.

Proof of the strict TV comparison. At $\tau_0$ the residual coefficient
support consists of vectors $L_0^{1/2}(u+v,u,v)^T$. The restriction
of its $N$ quadratic form is

$$
\begin{aligned}
A_{\rm res}u^2+2C_{\rm res}uv+B_{\rm res}v^2,\qquad
A_{\rm res}&=\delta\Delta A+\Delta B+2s_0\xi>\frac8{1000},\\
B_{\rm res}&=\delta\Delta A+\Delta C+2s_0\eta>\frac7{1000},\\
0<C_{\rm res}&=\delta\Delta A+s_0(\xi+\eta)+\zeta
 <\frac6{1000}.
\end{aligned}
\tag{JR.74}
$$

The rational box gives these strict comparisons by the same directed
operations as above. Hence
$A_{\rm res}B_{\rm res}-C_{\rm res}^2>20/10^6$.
Every nonzero residual atom therefore has positive height difference,
independently of its chosen null decomposition. The distinguished
atom has

$$
-\frac{12}{10000}<\phi(\tau_0)=\frac43\mathsf b(1)
 <-\frac{32}{30000}<0.
\tag{JR.75}
$$

The high differences are positive, the total live signed difference
is $d_f$, and the retained spectral failure labels contribute absolute
sum $L_f$. Thus the symmetric actual TV, with no label discarded,
is $\tfrac12[d_f-2\phi(\tau_0)+L_f]$.
For the new instrument the distinguished low difference is
$\phi(\tau_1)<\phi(\tau_0)<0$. Whatever the signs of its two
residual differences, their absolute sum is at least their signed sum.
Its high contribution is unchanged and its total live signed difference
is still $d_f$. Its actual TV is consequently at least
$T_{\rm flat}-\phi(\tau_1)$. Equation (JR.68) proves (JR.73).
This compares an established old actual value with a new lower bound,
not two unrelated lower bounds. The common realization and original
contrast/cost claims are proved next. $\square$

## 49. One common finite instrument for the local curve

**Definition 49.1 (explicit residual atoms and actual branches).**
All choices below depend only on public constants and $\tau$ before
the unknown specimen arrives. Put
$p=\sqrt\tau$, $q=\sqrt{Y_\tau}$, $r=\sqrt{Z_\tau}$,
$n_0=\sqrt{\tau+Y_\tau}$ and

$$
\begin{gathered}
U_\tau=\left(
 \frac{(q,p,0)^T}{n_0},\,
 \frac{(pr,-qr,n_0^2)^T}{n_0}\right),\qquad
B_\tau=L_0^{1/2}U_\tau,\\
B_\tau^TQ_0B_\tau=\begin{pmatrix}u&v\\v&-u\end{pmatrix},\qquad
u=\frac{\delta Y_\tau-\theta\tau}{\tau+Y_\tau},\quad
v=\frac{(\delta+\theta)\sqrt{\tau Y_\tau Z_\tau}}
 {\tau+Y_\tau}>0,\\
k_\tau=-\frac{u}{v+\sqrt{u^2+v^2}},\qquad
O_\tau=\frac1{\sqrt{1+k_\tau^2}}
 \begin{pmatrix}1&-k_\tau\\k_\tau&1\end{pmatrix},\\
c_0=c_\tau,\qquad (c_1,c_2)=B_\tau O_\tau.
\end{gathered}
\tag{JR.76}
$$

The letter $u$ here is only a residual $2\times2$ matrix entry, not
the strength-dependent $u$ of Convention 41.2.
One has $U_\tau^TU_\tau=I_2$ and
$U_\tau U_\tau^T=I-a_\tau a_\tau^T$.
The identity $u(1-k_\tau^2)+2vk_\tau=0$ makes both diagonal
entries of $O_\tau^TB_\tau^TQ_0B_\tau O_\tau$ zero. Consequently

$$
\sum_{j=0}^2c_jc_j^T=L_0,\qquad
c_j^TQ_0c_j=0,\qquad c_j\ne0.
\tag{JR.77}
$$

For $c_j=(x_j,z_j,w_j)^T$ write $K_j=x_jD+z_jT+w_jS$.
Nullity and $\theta,\omega>0$ imply $x_j\ne0$.
The determinant formula (JR.22) gives $\det K_j=0$, whereas the
rows/columns $1,2$ minor is $x_j^2h_1h_2\ne0$. Thus $K_j$ has
rank exactly two. Fix an isometry $V_j:\mathbb C^2\to\mathbb C^3$
onto its image by Gram–Schmidt on columns $1,2$; their independence
makes every denominator positive. This specializes the credited image
factorization of IR Lemma 4.2.

Use these three actual low encoders and whole-fibre live decoders:

$$
C_j=V_j^\dagger K_jE^\dagger,\qquad
\mathcal R_j(X)=EV_jXV_j^\dagger E^\dagger,
\quad j=0,1,2.
\tag{JR.78}
$$

Their declared fibres have dimension two. Report $r(0)=-1$ and
$r(1)=r(2)=+1$, retaining $j$ in $R$. Add the two high encoders
$\sqrt{(1-\delta)/2}\,DE^\dagger$, with actual fair labels
$r=\pm1$, dimension-three fibres and decoder $X\mapsto EXE^\dagger$.
Add all four scalar spectral failure rows $C_{f,\epsilon,r}E^\dagger$
of (JR.54), retaining both $\epsilon$ and $r$; their whole-fibre
decoders send scalar mass $z$ to $zw_\ell g(t)dt\,P_f$ at each
original label $\ell=0,\ldots,4$. Finally retain the two complement
labels $r=\pm1$, encoder $A\mapsto\operatorname{tr}((I_5-P)A)/2$
into a scalar fibre, decoded to $zg(t)dt\,P_f$ only at original
label $2$. Their two Kraus rows are discarded multiplicity as in
Definition 44.1, not an additional accessible payload.

These are eleven actual acquisition labels with joint quantum fibre
dimensions $(2,2,2,3,3,1,1,1,1,1,1)$. Define $R$ to retain the full
label $\alpha$, and $F$ to report its designated $r(\alpha)$.
An instrument dilation dephases this label by copying its branch and
Kraus multiplicity to a discarded orthogonal environment; that
environment is permanently inaccessible before the counted cut.
Only the stated classical label and its entire declared quantum fibre
remain accessible. Every other future-accessible input-bearing share,
including any retained specimen, controller, memory, environment or
entanglement share, would have to be counted jointly at this same cut.
The specification supplies a mathematical CP operation, not access to
a label or port of a previously discarded environment.

**Proposition 49.2 (normalization, full output, every history and
contrast).** Definition 49.1 is a single finite actual instrument,
with full TP decoders, preserving (JR.56) on every complex input,
every passive reference and every separately labelled Borel time set.
For every one of the twelve actual original histories its low law is

$$
\begin{aligned}
p(j\mid y,e,n)={}&x_j^2A_y+z_j^2B_y+w_j^2C_y
 +2x_jz_j\kappa enq_y\\
 &+2x_jw_j\kappa_{02}e q_{02,y}
 +2z_jw_jacnq_{12,y}.
\end{aligned}
\tag{JR.79}
$$

The high probabilities are $(1-\delta)A_y/2$ each; all four spectral
failure probabilities are exactly (JR.55), and complement probabilities
are zero. Its cost and supported binary effect are

$$
\begin{aligned}
\mathsf W&=(1-\delta)A_{27}=\mathsf C(s_{\rm int}),\\
F_+(\tau)&=\frac{I_3}{2}+\frac12[
 \delta D^\dagger D+T^\dagger T+S^\dagger S-2K_0^\dagger K_0],\\
\mathsf V(F(\tau))&=2s_0\sqrt{\tau Y_\tau}.
\end{aligned}
\tag{JR.80}
$$

Here $K_0=K(c_\tau)$, not the original coefficient-basis matrix $D$.
On five modes the plus effect is
$EF_+(\tau)E^\dagger+(I_5-P)/2$.

Proof. From (JR.77) the total live coefficient Gram is
$L_0+\operatorname{diag}(1-\delta,0,0)=I_3$. The supported live
effect is therefore $D^\dagger D+T^\dagger T+S^\dagger S=I_3-M$.
The spectral rows add $M$, and the complement adds $I_5-P$ on five
modes, so the total encoder effect is $I_5$. Each positive encoder
effect is bounded by that sum, making every encoder TNI. The live
decoders are TP on their entire declared fibres because $EV_j$ and
$E$ are isometries. The scalar decoders are TP because
$\sum_\ell w_\ell=1$ and $\int_0^1 2/(1+t)^2dt=1$.
Their normalization does not condition on survival or on an acquired
branch. All branch masses are unnormalized linear functions of the
input and become probabilities only on normalized specimens.

For every complex $A\in M_5$, image reconstruction gives the sum of
live products $E\Lambda_*(E^\dagger AE)E^\dagger$.
The failure rows sum to $M$ and the complement rows sum to $I_5-P$.
Thus each original failure measure is exactly

$$
g(t)\left[w_\ell\operatorname{tr}(ME^\dagger AE)
 +\mathbf1_{\ell=2}\operatorname{tr}((I_5-P)A)\right]dt\,P_f.
\tag{JR.81}
$$

There are no cross-support outputs, singular additions or extra-sector
maps. The original two side labels remain distinct and the two
zero-weight labels remain zero. For a joint operator $X$ with passive
reference, each encoder and live isometry is tensored with $I_R$.
The two reference operators multiplying $P_f$ in (JR.81) are precisely
$\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X]$ and
$\operatorname{Tr}_5[((I_5-P)\otimes I_R)X]$, as in Proposition
44.2. Integrating their common density over any Borel set proves the
full labelled-time reference identity, including its conditional
reference operators. Finite Kraus identities give the same assertion
at every passive-reference amplification. No time sampling or
unconditional-reference substitution is used in this implication.
Hence every original HALF full-cq error is unchanged and $E=E_*$,
conditional on the inherited CG certificate. The ideal comparison
still uses $f_y(t)=6y/(y+6t)^2$, never $g$ in its place.

Expanding the low encoder norms gives (JR.79) for each actual
$(y,e,n)$, and encoder normalization makes the complete actual law
sum to one. Only the two high fibres have dimension at least three,
so their total acquired probability on each history is
$(1-\delta)A_y$, independent of its two signs. Its maximum is the
stated original sharp cost at height $27$. This is a worst-history
statement about the common instrument, not an individual-input or
sign-averaged replacement objective.

The high and scalar labels are fair for $F$. On low branches the
positive reports have total coefficient Gram $L_0-c_\tau c_\tau^T$.
Their plus effect is therefore (JR.80). In particular
$(F_+(\tau))_{01}=\kappa s_0\sqrt{\tau Y_\tau}$ and
$(F_+(\tau))_{02}=\kappa_{02}s_0\sqrt{\tau Z_\tau}>0$.
The latter shows explicitly why this is not CA's prescribed full
binary effect. Since
$(\tau Y_\tau)'=Y_\tau+\chi\tau>0$, the contrast starts at
$s_{\rm int}$ and increases strictly. This proves the remaining
claims of Theorem 48.3 for the original constraint
$\mathsf V(F)\geq s_{\rm int}$.

For exact contrast, set $\beta=s_{\rm int}/\mathsf V(F(\tau_1))$
and refine each actual label by the input-independent kernel

$$
k(r'\mid\alpha)=\frac{1+r'r(\alpha)\beta}{2},\qquad
r'=\pm1,\quad 0<\beta<1,
\qquad R'=(\alpha,r'),\quad F'=r'.
\tag{JR.82}
$$

Multiply each encoder CP map by this classical probability and keep its
full decoder and fibre. This gives at most twenty-two actual labels,
the same full output and cost, and $\mathsf V(F')=s_{\rm int}$.
For every retained $\alpha$, summing absolute differences over $r'$
gives
$\sum_{r'}k(r'\mid\alpha)|p_{27}(\alpha)-p_5(\alpha)|
=|p_{27}(\alpha)-p_5(\alpha)|$, so actual TV is exactly unchanged.
All old labels are retained. Including the decoder-generated failure
label and time likewise preserves this TV, since its conditional
scalar law is common to the two heights on each such branch.
$\square$

**Convention 49.3 (extent of the local conclusion).** Proposition
46.1's strict improvement over its all-label comparator survives;
Theorem 48.3 improves that symmetric instrument further. The
all-optimizer supported rigidity, strong-regime evaluation and weak
four-PSD reduction retain their stated hypotheses and conclusions.
Only the specified symmetric point is shown nonoptimal here; the
new three-low-branch witness is not asserted optimal. Evaluation of
$J_s$, the full weak-plateau law, and optimality or nonoptimality of
all three-low-branch constructions remain unresolved. In particular,
this local comparison supplies no full-plateau evaluation.

The construction retains one unknown specimen, no prior, no
postselection or acceptance division, no readable history, no helper,
copy, retry, reset or bypass, the entire joint quantum cut, all original
labels and coherent live entries. Its existence is ordinary conditional
mathematics. Native lawful unknown-specimen acquisition, calibrated
operations and coherent storage, the same aligned clock, actual first
absorbing failure with no later positive-carrier action, terminal live
output, archives, controller and permissions remain the obligations of
Definition 47.2. The original noncommuting probability–phase controls
remain available in their stated scope; neither an exhaustive Schur
restriction nor a native actuation theorem follows. The original CG
root/minimax premises are not reauthenticated, and no Lean/kernel,
native-execution or programme-completion claim is made.

## 追加锚（本行以下为增补区）
## 50. The normalized real-null problem and its global spectral certificate

**Convention 50.1 (the original weak-plateau problem).** Retain the original
full twelve-history, all-complex, common-processor problem of Definition
41.1. The source-root, complete-channel, sharp-cost and minimax statements
from CG §§13--17 and JR §§41--49 are conditional premises here. The
inequality on the binary effect remains the original inequality; no other
binary-effect coordinate, complete-channel representative, or input phase
is fixed. In particular, the reduction below does not replace the original
problem by CA's prescribed complete binary effect.

Put

$$
L_0=\operatorname{diag}(\delta,1,1),\qquad
L=L_0^{1/2}=\operatorname{diag}(\sqrt\delta,1,1),\qquad
\chi=\frac{\omega}{\delta},
$$

and

$$
Q_0=\operatorname{diag}(1,-\theta,-\omega),\qquad
Q=\operatorname{diag}(1,-(1-\chi),-\chi).
$$

Then $LQ_0L=\delta Q$ and $\operatorname{tr}Q=0$. For the four real
PSD matrices in JR.58 write

$$
Z_{r,\epsilon}=LX_{r,\epsilon}L,\qquad
G=LNL=
\begin{pmatrix}g_0&x&y\\x&g_1&z\\y&z&g_2\end{pmatrix},
$$

where

$$
\begin{gathered}
N=\begin{pmatrix}\Delta A&\xi&\eta\\\xi&\Delta B&\zeta\\\eta&\zeta&\Delta C\end{pmatrix},
\quad(g_0,g_1,g_2,x,y,z)=(\delta\Delta A,\Delta B,\Delta C,s_0\xi,s_0\eta,\zeta),\\
\tau=s/s_0.
\end{gathered}
\tag{JR.83}
$$

Thus the exact normalized primal is

$$
\begin{aligned}
J_s=\max\quad&\sum_{r,\epsilon=\pm1}\epsilon\operatorname{tr}(GX_{r,\epsilon})\\
\text{subject to}\quad
&X_{r,\epsilon}\succeq0,\qquad
\operatorname{tr}(QX_{r,\epsilon})=0,\\
&\sum_{r,\epsilon}X_{r,\epsilon}=I,\qquad
\sum_{r,\epsilon}r(X_{r,\epsilon})_{01}\geq\tau.
\end{aligned}
\tag{JR.84}
$$

Every coordinate of the original effect not displayed in (JR.84) remains
free. The height record is still

$$
\mathcal T(s)=\frac12\bigl[(1-\delta)\Delta A+L_f+J_s\bigr].
\tag{JR.85}
$$

For numerical enclosures in §§50–51, use the full inherited box
$\mathcal B_{\rm CG}=\prod_{i=0}^8[c_i-10^{-24},c_i+10^{-24}]$,
where $c$ is the exact rational centre table in [CG, Proposition 13.2],
in the order $(\lambda,\alpha_1,\alpha_2,\beta_1,\beta_2,z,\eta_0,\eta_1,\eta_2)$. Reconstruct the coefficients by (CG.112),
(CG.113), (CG.116), (CG.134), then (JR.21), (JR.49) and (JR.83).
The CG coordinate $z$ in that table is distinct from $z=G_{12}$ here.
Every narrow directed enclosure below uses this entire box, with outward
rational arithmetic and square-root bounds as specified in §48;
terminating decimal endpoints are exact rationals. This only evaluates
derived quantities on the inherited box; it does not reauthenticate
its isolated root, exact ranks, normalization or minimax certificate.

A coarse consequence of this full premise, with rational endpoints, is

$$
\begin{gathered}
\frac{12227}{100000}<\chi<\frac{12230}{100000},\qquad
\frac{1269}{10^6}<g_0<\frac{1270}{10^6},\qquad
\frac{29222}{10^7}<g_1<\frac{29224}{10^7},\\
\frac{16771}{10^7}<g_2<\frac{16773}{10^7},\qquad
\frac{2370}{10^6}<x<\frac{2372}{10^6},\qquad
\frac{2207}{10^6}<y<\frac{2209}{10^6},\\
-\frac{1017}{10^7}<z<-\frac{1016}{10^7}.
\end{gathered}
\tag{JR.86}
$$

The coarse bounds (JR.86) support strict sign and positive-pivot
comparisons. The narrow numerical enclosures below use $\mathcal B_{\rm CG}$,
not (JR.86) alone.

**Definition 50.2 (the real-null curve).** Set

$$
q(t)=\sqrt{1-\chi+\chi t^2},\qquad d=2-\chi,\qquad e=1+\chi,\qquad
D_t=d+et^2,
$$

and

$$
v(t)=\frac{(q(t),-1,-t)^T}{\sqrt{D_t}}.
\tag{JR.87}
$$

Then $\|v(t)\|=1$ and $v(t)^TQv(t)=0$. Let

$$
\begin{gathered}
p=(1-\chi)g_0+g_1,\qquad h=\chi g_0+g_2,\\
F_t=p+ht^2-2q(t)(x+yt)+2zt,\qquad
\psi(t)=\frac{F_t}{D_t}.
\end{gathered}
\tag{JR.88}
$$

The tuple

$$
X_{-,-}=v(t)v(t)^T,\qquad X_{+,+}=I-v(t)v(t)^T,\qquad
X_{+,-}=X_{-,+}=0
\tag{JR.89}
$$

is feasible for (JR.84) at $s=s(t)$, with trial objective

$$
\sum_{r,\epsilon}r(X_{r,\epsilon})_{01}=\frac{2q(t)}{D_t},\qquad
J_{\rm trial}(t):=\operatorname{tr}G-2\psi(t)\leq J_{s(t)},\qquad
s(t)=\frac{2s_0q(t)}{D_t}.
\tag{JR.90}
$$

Here $J_{\rm trial}(t)$ is the linear objective of (JR.89), whereas
$J_s$ retains its optimized meaning in (JR.84). Feasibility gives the
displayed inequality; it does not assert equality.

At $t=1$, the restriction of $G$ to $v(1)^\perp$ is represented in
coordinates $u_0=u_1+u_2$ by

$$
\begin{pmatrix}
g_0+g_1+2x&g_0+x+y+z\\
g_0+x+y+z&g_0+g_2+2y
\end{pmatrix}\succ0.
\tag{JR.91}
$$

Evaluation on $\mathcal B_{\rm CG}$ places the determinant of (JR.91)
in the rational interval

$$
\frac{32748113870346}{10^{18}}<\det\!\begin{pmatrix}
 g_0+g_1+2x&g_0+x+y+z\\
 g_0+x+y+z&g_0+g_2+2y
\end{pmatrix}<\frac{32748113870347}{10^{18}}.
\tag{JR.92}
$$

Consequently the former three-low-ray construction has actual value
$T_{\rm flat}-\psi(1)$, with $\psi(1)=4\mathsf b(1)/3$. At $t=9/10$,
exact rational radical bounds on $\mathcal B_{\rm CG}$ give

$$
3q(9/10)-D_{9/10}>
\frac{178177939744504162}{10^{18}}>0,
\tag{JR.93}
$$

and

$$
-\frac{97686672107194}{10^{18}}<
3F_{9/10}-D_{9/10}F_1<-
\frac{97686672107193}{10^{18}}.
\tag{JR.94}
$$

Indeed, the second expression is the exact combination

$$
3F_t-D_tF_1=-(1-t^2)(dh-ep)+2x(D_t-3q(t))
 +2y(D_t-3tq(t))+2z(3t-D_t).
\tag{JR.95}
$$

Equations (JR.93)--(JR.95) prove $s(9/10)>2s_0/3$ and
$\psi(9/10)<\psi(1)-10^{-5}$. Thus the original three-low point is
strictly suboptimal at $s=2s_0/3$, while the comparison is with its
actual TV and not with a lower bound.

**Lemma 50.3 (stationary isolation).** Put $K=dh-ep$ and define

$$
\begin{aligned}
\mathscr E(t):={q(t)D_t^2\over2}\psi'(t)
={}&q(t)[Kt+z(d-et^2)]\\
&+xt[2-2\chi-\chi^2+\chi et^2]\\
&-y[(1-\chi)d+(4\chi-\chi^2-1)t^2].
\end{aligned}
\tag{JR.96}
$$

**Proof.** Directed rational interval evaluation of (JR.96) on the full
box $\mathcal B_{\rm CG}$, with outward square-root bounds, gives

$$
-\frac{1100}{10^7}<\mathscr E(17/20)<-\frac{1099}{10^7},\qquad
\frac{1857}{10^7}<\mathscr E(9/10)<\frac{1858}{10^7},
\tag{JR.97}
$$

and, after differentiating the displayed expression and subdividing only
by rational endpoints,

$$
\mathscr E'(t)>\frac1{200}\qquad(17/20\leq t\leq9/10).
\tag{JR.98}
$$

Therefore there is a unique $`t_*\in(17/20,9/10)`$ with
$`\mathscr E(t_*)=0`$. Evaluating (JR.96) on $\mathcal B_{\rm CG}$ at
the two rational endpoints below gives respectively a strictly negative and a strictly positive value,
yielding the isolating interval

$$
\frac{4890850417337583}{5629499534213120}<t_*<
\frac{19563401669350333}{22517998136852480}.
\tag{JR.99}
$$

The decimal $`t_*=0.8687895589321185\ldots`$ is only an illustration of
this exact isolation.

**Theorem 50.4 (global spectral optimum and its four slacks).** Define

$$
\mu_*=\psi(t_*),\qquad v_*=v(t_*),\qquad P_*=v_*v_*^T,
$$

and distinguish the spectral multiplier from the contrast multiplier by

$$
\lambda_{\rm sp}=\mu_*-g_0+\frac{x+yt_*}{q(t_*)},\qquad
H_*=G+\lambda_{\rm sp}Q.
\tag{JR.100}
$$

**Proof.** The stationarity equation is $`H_*v_*=\mu_*v_*`$. Directed bounds on the
full box $\mathcal B_{\rm CG}$ and the bracket (JR.99) give

$$
-\frac{129}{10^5}<\mu_*<-\frac{107}{10^5},\qquad
\frac{17}{10^4}<\lambda_{\rm sp}<\frac{22}{10^4},
\tag{JR.101}
$$

and

$$
(H_*)_{11}>\frac9{10^4},\qquad (H_*)_{22}>\frac{14}{10^4},\qquad
|(H_*)_{12}|<\frac{102}{10^6},\qquad
\det(H_*[1,2])>0.
\tag{JR.102}
$$

Thus the $1,2$ principal block is positive definite. Interlacing and
$`H_*v_*=\mu_*v_*`$ show that $`H_*`$ has exactly one negative eigenvalue,
namely $`\mu_*`$, and two strictly positive eigenvalues.

Set

$$
Y_*=H_*-2\mu_*P_*=|H_*|.
\tag{JR.103}
$$

The four PSD slacks of the real SDP dual are

$$
\begin{aligned}
Y_*-G-\lambda_{\rm sp}Q&=-2\mu_*P_*\succeq0,\\
Y_*+G+\lambda_{\rm sp}Q&=2(H_*-\mu_*P_*)\succeq0.
\end{aligned}
\tag{JR.104}
$$

The first line is the positive-report ($\epsilon=+1$) slack and the
second is the negative-report ($\epsilon=-1$) slack. Explicitly, for each
$r=\pm1$, $`S_{r,+}:=Y_*-G-\lambda_{\rm sp}Q\succeq0`$ and
$`S_{r,-}:=Y_*+G+\lambda_{\rm sp}Q\succeq0`$. These are the four slacks of
(JR.126) with $\lambda=0$ and $\nu_{r,\epsilon}=-\epsilon\lambda_{\rm sp}$;
they satisfy $`S_{r,+}(I-P_*)=0`$ and $`S_{r,-}P_*=0`$.
For any feasible tuple put $X_-:=X_{+,-}+X_{-,-}$. Then
$0\preceq X_-\preceq I$, $\operatorname{tr}(QX_-)=0$, and
$`\operatorname{tr}(GX_-)=\operatorname{tr}(H_*X_-)`$, because
$\operatorname{tr}(QX_-)=0$. In an eigenbasis of $`H_*`$, the unique
negative coordinate of $X_-$ is at most one and all positive
coordinates contribute nonnegatively. Consequently

$$
\operatorname{tr}(GX_-)=\operatorname{tr}(H_*X_-)\geq\mu_*.
\tag{JR.105}
$$

It follows that

$$
J_s\leq\operatorname{tr}G-2\mu_*\qquad(0\leq s\leq s_0).
\tag{JR.106}
$$

Equality in (JR.105) holds exactly when $`X_-=P_*`$. This is the global
upper bound, and it uses no fixed complete binary effect.

**Definition 50.5 (the orthonormal null frame and exact endpoint).** Put

$$
\begin{gathered}
a_0=1-\chi,\qquad q_*=q(t_*),\qquad B_*=a_0t_*^2+\chi,\\
z_*={a_0q_*t_*-\sqrt{B_*-a_0\chi q_*^2}\over B_*},\qquad
b_*=q_*-t_*z_*,\\
u_*={ (1,b_*,z_*)^T\over\sqrt{1+b_*^2+z_*^2}},\qquad
w_*=v_*\times u_*.
\end{gathered}
\tag{JR.107}
$$

**Proof.** The defining quadratic identity for $`z_*`$ gives $`u_*^TQu_*=0`$;
orthogonality to $`v_*`$ is immediate, and hence $`w_*`$ is orthogonal to
both and is also $Q$-null because the compression of $Q$ to
$`v_*^\perp`$ is a nonzero traceless $2\times2$ form. Thus
$`(v_*,u_*,w_*)`$ is an orthonormal real $Q$-null frame. Evaluation on
$\mathcal B_{\rm CG}$ with (JR.99) gives

$$
-\frac1{10}<z_*<0,\qquad {49\over50}<b_*<{27\over25}.
\tag{JR.108}
$$

The normalized $01$ products have signs

$$
(v_*)_0(v_*)_1<0,\qquad (u_*)_0(u_*)_1>0,\qquad
(w_*)_0(w_*)_1<0.
\tag{JR.109}
$$

Define

$$
\bar s=2s_0(u_*)_0(u_*)_1
=s_0\left(|(v_*)_0(v_*)_1|+(u_*)_0(u_*)_1+|(w_*)_0(w_*)_1|\right).
\tag{JR.110}
$$

The tuple

$$
Z_{+,+}=Lu_*u_*^TL,\quad Z_{-,+}=Lw_*w_*^TL,\quad
Z_{-,-}=Lv_*v_*^TL,\quad Z_{+,-}=0
\tag{JR.111}
$$

attains (JR.106), has contrast $\bar s$, and has $`X_-=P_*`$.
Moreover,

$$
\frac{\bar s}{s_0}={2b_*\over1+b_*^2+z_*^2}
=1-{(b_*-1)^2+z_*^2\over1+b_*^2+z_*^2}
>1-{41\over4901}>{99\over100}.
\tag{JR.112}
$$

Since $`t_*<1`$, $`q_*<1`$; equality in the two-coordinate
Cauchy--Schwarz bound would require $`|(v_*)_0|=|(v_*)_1|`$, which is
false. Hence $\bar s<s_0$. Evaluation on $\mathcal B_{\rm CG}$ with
(JR.99) gives the illustrations

$$
0.993780002195346659<\frac{\bar s}{s_0}<0.993780002195346879,\qquad
0.103298204128059321<T_{\rm flat}-\mu_*<0.103298204128059323.
$$

**Theorem 50.6 (optimal value and real-atom classification).** The exact
weak-plateau value is

$$
\boxed{J_s=\operatorname{tr}G-2\mu_*,\qquad
\mathcal T(s)=T_{\rm flat}-\mu_*,\qquad0\leq s\leq\bar s.}
\tag{JR.113}
$$

**Proof.** In particular the equality includes $s=0$ and $s=2s_0/3$. Equality in
(JR.105) forces the aggregate negative part to be $`P_*`$, and the aggregate
positive part to be $`I-P_*`$. The real $Q$-null cone inside $`v_*^\perp`$
has exactly the two lines spanned by $`u_*`$ and $`w_*`$: a two-dimensional
totally null plane would make the nonzero traceless compression vanish.
The rank-by-rank real null decomposition therefore classifies every
nonzero optimal real atom, up to proportional splitting, a sign phase,
and the report assignment, as one of $`v_*,u_*,w_*`$. The aggregate
weights in this frame are fixed by (JR.111). This classification concerns
the finite real SDP and its aggregate supports only; it asserts no
uniqueness of a whole channel, a time law, a native implementation, or
an inaccessible instrument refinement.

No value above (JR.113) is possible for $s>\bar s$. Compactness of the
feasible set and the equality classification give

$$
J_s<\operatorname{tr}G-2\mu_*,\qquad \bar s<s\leq s_0.
\tag{JR.114}
$$

## 51. One common finite instrument and the residual interval

**Definition 51.1 (the common frame instrument).** For
$`f\in\{v_*,u_*,w_*\}`$, set $c_f=Lf$ and

$$
K_f=(c_f)_0D+(c_f)_1T+(c_f)_2S.
\tag{JR.115}
$$

Each $K_f$ has rank two. Choose an isometry $V_f:\mathbb C^2\to\mathbb C^3$ onto its image and use encoder $V_f^\dagger K_fE^\dagger$
with the full TP decoder

$$
A\longmapsto EV_fAV_f^\dagger E^\dagger.
\tag{JR.116}
$$

The low reports are $`r(v_*)=-1`$, $`r(u_*)=+1`$, and $`r(w_*)=-1`$.
The high-dimensional pair uses

$$
K_{H,\sigma}=\sqrt{(1-\delta)/2}\,D,\qquad \sigma=\pm1,
\tag{JR.117}
$$

with the full live decoder $A\mapsto EAE^\dagger$, and both high labels
are fair. Let $\Xi$ be the $2\times2$ failure difference matrix of
JR.49 and choose real unit eigenvectors $f_+,f_-$. For
$\epsilon,r=\pm1$, use the scalar row

$$
C_{\epsilon,r}={1\over\sqrt2}\langle f_\epsilon|M^{1/2}E^\dagger.
\tag{JR.118}
$$

Its decoder sends $z$ to $z\,w_\ell g(t)dt\,P_f$ in every original
label $\ell=0,\ldots,4$. Finally use two complement labels, with each
complement CP map having effect $(I_5-P)/2$, scalar retained fibre,
and decoder $z\mapsto z\,g(t)dt\,P_f$ at original label $2$ only; the
Kraus multiplicity inside $V^\perp$ is permanently inaccessible.

There are $3+2+4+2=11$ base branches. Every input, all twelve histories,
and every passive reference use this one fixed instrument. The jointly
counted accessible fibre includes every retained specimen, memory,
controller, environment, or entanglement share at the cut.

**Proposition 51.2 (normalization, complete channel and all labelled
measures).**

**Proof.** The frame identity gives

$$
\sum_{f\in\{v_*,u_*,w_*\}}c_fc_f^T=L_0,\qquad
\sum_fK_f^\dagger K_f=\delta D^\dagger D+T^\dagger T+S^\dagger S.
\tag{JR.119}
$$

Adding (JR.117) and the failure rows gives $I_3$, by the inherited
identity $D^\dagger D+T^\dagger T+S^\dagger S+M=I_3$.
On five modes the complement effects add $I_5-P$, so the encoder effects
sum to $I_5$. The range isometries and the scalar decoders are TP on
their complete declared fibres, since

$$
\int_0^1{2\over(1+t)^2}\,dt=1,\qquad
\sum_{\ell=0}^4w_\ell=1.
\tag{JR.120}
$$

For every $A\in M_5(\mathbb C)$, write $A_V=E^\dagger AE$. Forgetting
all acquisition labels gives

$$
\Phi^L(A)=E\bigl(DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger\bigr)E^\dagger,
\tag{JR.121}
$$

and for every Borel $B\subseteq[0,1]$,

$$
\Phi^f_\ell(A)(B)=\left(\int_Bg(t)\,dt\right)
\left[w_\ell\operatorname{tr}(EME^\dagger A)
+\mathbf1_{\ell=2}\operatorname{tr}((I_5-P)A)\right]P_f.
\tag{JR.122}
$$

These are equalities on every complex matrix unit, hence on every complex
input. Tensoring each encoder and decoder by a passive reference identity
proves the same identity with the two conditional reference operators
$\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X]$ and
$\operatorname{Tr}_5[((I_5-P)\otimes I_R)X]$. Equation (JR.122) is therefore
valid separately for all five original labels and all Borel time sets.
It preserves the original $`E_*`$, including every live coherence and every
full HALF complete-cq norm term, conditional on the inherited CG
certificate. The density $g$ is the actual common output density; it is
not substituted for the ideal $f_y$.

Only the two high labels have fibre dimension at least three, so their
maximum twelve-history mass is $(1-\delta)A_{27}=\mathsf C(s)$ throughout
the weak plateau. No prior, postselection, acceptance division, helper,
copy, reset, retry, readable history or free bypass is introduced.

For $0\le s\le\bar s$, the base raw report has contrast $\bar s$. An
input-independent report kernel

$$
\Pr(F=f\mid r)={1+fr\,s/\bar s\over2},\qquad f,r=\pm1,
\tag{JR.123}
$$

retains the original branch label and raw report and adds $F$. It gives
$\mathsf V(F)=s$; summing over $F$ on each retained branch leaves its
height absolute difference unchanged. Thus the exact lower-contrast
instrument has 22 retained branches (each of the 11 base branches split
by $F$); at $s=\bar s$ it has 11. If only the inequality
$\mathsf V(F)\ge s$ is requested, the 11-branch raw instrument already
suffices.

**Proposition 51.3 (the residual chord and strict decrease).** Let
$b(1)$ be the inherited endpoint residual in JR.50 and put

$$
a_s={s_0-s\over s_0-\bar s},\qquad \bar s\le s\le s_0.
$$

**Proof.** Mix the instrument of Proposition 51.2 at $\bar s$ with the inherited
finite $s_0$ instrument, using an input-independent retained choice
with weights $a_s$ and $1-a_s$. Both choices have the same complete
channel and the same sharp cost. The resulting common instrument has

$$
\boxed{\mathcal T(s)\geq
T_{\rm flat}-a_s\mu_*-(1-a_s)b(1).}
\tag{JR.124}
$$

The inequality is a feasible retained-choice lower bound. It is not an
evaluation of the residual optimum. Its interior branch count is 23
(11 plus 12); the endpoint counts are 11 at $\bar s$ and 12 at $s_0$.

The compact feasible sets make $J_s$ concave by retained input-independent
choice and nonincreasing by constraint inclusion. Together with (JR.114),
concavity forces strict decrease on $(\bar s,s_0]$: if two points in
that interval had equal values, the slope from the preceding point
$\bar s$, where the value is larger, would violate the monotonicity of
secant slopes for a concave function. Hence

$$
\mathcal T(s)<T_{\rm flat}-\mu_*\quad(\bar s<s\le s_0),
\tag{JR.125}
$$

while the exact endpoint is attained by the inherited finite instrument,
$\mathcal T(s_0)=T_{\rm flat}-b(1)$. The residual curve, contact rays and
branch transitions remain unevaluated.

**Theorem 51.4 (the four-slack dual and the singular endpoint).** Put

$$
C={|0\rangle\langle1|+|1\rangle\langle0|\over2},\qquad \tau=s/s_0.
$$

For $s<s_0$, the normalized dual is

$$
\boxed{
J_s=\min_{\substack{\lambda\ge0,\ Y=Y^T\\
\nu_{r,\epsilon}\in\mathbb R}}
\left\{\operatorname{tr}Y-\lambda\tau:
Y-\epsilon G-\lambda rC+\nu_{r,\epsilon}Q\succeq0
\right\}.}
\tag{JR.126}
$$

**Proof.** Here $\lambda$ is the nonnegative contrast multiplier and is distinct
from $\lambda_{\rm sp}$ in (JR.100). To prove finite dual attainment,
let $X^{(1)}$ be any endpoint feasible tuple with contrast one and let
$X^{(0)}_{r,\epsilon}=I/4$. For $0<\eta<1$,
$X^{(\eta)}=(1-\eta)X^{(0)}+\eta X^{(1)}$ is positive definite in
all four slots and has contrast $\eta$. Given $\tau<1$, choose
$\eta\in(\tau,1)$. This is a genuinely strict feasible tuple for the
primal SDP, so finite-dimensional Slater duality gives equality in
(JR.126) and a finite dual minimizer.

On $\bar s<s<s_0$, every finite optimal contrast multiplier satisfies
$\lambda>0$. If $\lambda=0$, (JR.126) is the unconstrained spectral
problem and its value is the plateau value in (JR.113), contradicting
(JR.125). Complementary slackness therefore forces
$\sum_{r,\epsilon}r(X_{r,\epsilon})_{01}=\tau$, so the original contrast
inequality is saturated throughout the residual interval. On the constant
interval, the certificate (JR.103)--(JR.104) is the branch
$\lambda=0$, $`Y=Y_*`$, $\nu_{r,\epsilon}=-\epsilon\lambda_{\rm sp}$.

At $s=s_0$, the endpoint primal is finitely attained, but the dual has
an infimum and no finite minimizer. For the four endpoint null atoms
$d_{\sigma,t}=(1,\sigma,t)^T/2$, $\sigma,t=\pm1$, complementary
slackness for a putative finite dual minimizer first gives

$$
\begin{gathered}
A_{+,+}=\alpha(1,-1,0)^T(1,-1,0),\qquad
\alpha=\lambda/2,\\
\nu_{-,+}=\nu_{+,+},\qquad
Y_{01}=x,\quad Y_{02}=y,\quad Y_{12}=z,\\
Y_{00}=g_0-\nu_{+,+}+\lambda/2,\\
Y_{11}=g_1+(1-\chi)\nu_{+,+}+\lambda/2,\qquad
Y_{22}=g_2+\chi\nu_{+,+}.
\end{gathered}
\tag{JR.127}
$$

The negative atom $d_{-,-}$ then requires
$\nu_{-,-}-\nu_{+,+}=2(x+y-g_0)$. Substitution into the two remaining
complementary diagonal equations requires both residues

$$
R_1=x-g_1-z+(1-\chi)(x+y-g_0)=0,\qquad
R_2=y-z-g_2+\chi(x+y-g_0)=0.
\tag{JR.128}
$$

Evaluation of (JR.128) on $\mathcal B_{\rm CG}$ gives the directed intervals

$$
\frac{2454521998719936}{10^{18}}<R_1<
\frac{2454521998719937}{10^{18}},\qquad
\frac{1037144557584923}{10^{18}}<R_2<
\frac{1037144557584924}{10^{18}}.
\tag{JR.129}
$$

Both are strictly positive, contradicting (JR.128). Thus no finite dual
minimum exists at $s_0$. The endpoint dual infimum nevertheless equals
$J_{s_0}$: compactness and nested feasible sets give
$J_s\to J_{s_0}$ as $s\uparrow s_0$, while every dual feasible point
for an interior $\tau$ remains feasible at $\tau=1$ with objective
lowered by $\lambda(1-\tau)$. Weak duality at the endpoint sandwiches
its dual infimum between $J_{s_0}$ and this convergent sequence. No
multiplier-divergence rate or other endpoint asymptotic is asserted.

## 52. Source conditions, literature scope and remaining boundaries

**Convention 52.1 (credit and hypotheses).** CG supplies the isolated
source root, conditional channel, normalization, sharp worst-history
cost and original minimax certificate. JR §§41--49 supplies the original
height-record formulation, supported equality consequences, failure
spectral readout, labelled-time identities and the strong-regime endpoint
instrument. CA supplies the real exposed/null-decomposition mechanism,
rank compression and finite realization facts. IR supplies the compatible
finite CP-map and reference/Borel-measure identities. These mechanisms are
reused with the frame substitutions (JR.107) and (JR.115); no generic
S-lemma, flat-roof theorem or whole-channel uniqueness claim is counted as
new mathematics here.

The equality S-lemma of Xia--Wang--Sheu supports only the relation between
an equality quadratic constraint and a scalar PSD certificate when its
sign-changing hypothesis holds; (JR.103)--(JR.106) provide the concrete
certificate here. Uhlmann's common flat decomposition for affine
functionals is an antecedent for convex decompositions, not a proof of
this real-null height-TV optimum. Leppäjärvi--Sedlák and
Muñoz-Moller--Leppäjärvi--Heinosaari supply finite compatibility and
conditional-measure mechanisms within their stated hypotheses. Sekatski's
rank/image compression is used from subsection II.1, with its stated
finite-dimensional scope; it supplies no original state-dependent
acquisition-cost theorem. The latest nonreal-input plateau source has a
selected-input resource objective and a different exact-effect model; its
values are not transferred to (JR.84)--(JR.126). Calibration XXIV's
proper-restriction obstruction supplies no quantum CP or resource
correspondence and is not used here.

**Convention 52.2 (scope boundary).** The conditional mathematics retains
one unknown specimen, no prior, postselection, acceptance division,
helper, copy, reset, retry, readable history or free bypass. It counts all
future-accessible specimen, memory, controller, environment and
entanglement shares at one acquisition cut. The construction does not
supply native acquisition, calibrated native D/T/S operations, coherent
storage, an aligned-clock execution, an actual first absorbing failure
with no later positive-carrier action, terminal live output, archives,
controller or permission bridge. OriginalControl remains geometric rather
than an actuator, and the noncommuting controls do not admit an exhaustive
Schur restriction. The exact residual curve on $(\bar s,s_0)$, its contact
transitions and the native realization therefore remain open. The statements
above are ordinary source-conditional mathematics and do not assert
Lean/kernel certification, native execution, or completion of the wider
programme.

## 追加锚（本行以下为增补区）

## 53. The original residual problem, signs and actual finite records

**Convention 53.1 (premises and normalization).** Retain Definition 41.1,
including its finite/countable scope and only its stipulated measurable
finite-fibre, integrable-Kraus extension. The isolated source root in CG
Proposition 13.2, its exact ranks, normalization and original minimax
identification remain conditional premises. All channel identities below
are evaluated at that root. Enclosures on its surrounding box certify
inequalities of derived expressions; they do not make off-root points TP.
The sharp worst-history acquisition law is the result of JR §§34–40.
This corrects the allocation of that cost result in Convention 52.1:
CG supplies the source root, channel and minimax premises, while JR
§§34–40 supplies the sharp jointly counted resource cost.

Write

$$
\alpha=1-\chi,\quad\beta=\chi,\quad A=1+\alpha,\quad
Q=\operatorname{diag}(1,-\alpha,-\beta),\quad
C=(e_0e_1^T+e_1e_0^T)/2,\quad j(\tau)=J_{s_0\tau}.
$$

Here $\chi=\omega/\delta$, as in §50, not the different local-curve
parameter of §48. With $G=LNL$ from (JR.83), the exact original problem is
(JR.84), its dual is (JR.126), and

$$
\mathcal T(s_0\tau)=\frac{(1-\delta)\Delta A+L_f+j(\tau)}2,
\qquad T_{\rm flat}=\frac{(1-\delta)\Delta A+L_f+\operatorname{tr}G}2.
\tag{JR.130}
$$

The original binary contrast is an inequality; other effect entries and
the forgotten complete channel are not prescribed. The supported
real-null equality face comes from the all-complex error/cost equalities
of Theorem 42.1 and CA's exposed-face argument, not a restriction to real
physical processors. Theorem 45.1 supplies the two directions between
this finite problem and the original optimization. In particular,
analytic refinement gives only an upper bound on the TV of an arbitrary
actual record. A new instrument which actually generates the refined
labels can attain the bound. No discarded environment index is readable.

**Lemma 53.2 (signs of every residual optimum).** Put
$\bar\tau=\bar s/s_0$. For $\bar\tau<\tau\leq1$, every optimal tuple has
saturated signed contrast, every finite real-null decomposition of it
has report aligned with the sign of its $01$ product, and

$$
X_{+,-}=0.
\tag{JR.131}
$$

Consequently its optimizing tuples correspond exactly to the minimizers
of $\operatorname{tr}(GC_0)$ subject to

$$
A_0,B_0,C_0\succeq0,\quad A_0+B_0+C_0=I,\quad
\operatorname{tr}(QA_0)=\operatorname{tr}(QB_0)=\operatorname{tr}(QC_0)=0,
\quad 2(A_0)_{01}\geq\tau,
\tag{JR.132}
$$

by $A_0=X_{+,+},B_0=X_{-,+},C_0=X_{-,-}$, with value
$j(\tau)=\operatorname{tr}G-2\operatorname{tr}(GC_0)$ and equality in the
last constraint at every optimum.

**Proof.** First, for the entire source box (JR.86),

$$
\alpha u^2+\beta v^2=1,\quad u\geq0
\quad\Longrightarrow\quad f_G(u,v):=(1,u,v)G(1,u,v)^T>0.
\tag{JR.133}
$$

For $v\geq0$, the quadratic part is at least
$(g_1-|z|)u^2+(g_2-|z|)v^2\geq0$ and the remaining terms are positive.
For $v<0$, drop $2zuv\geq0$ and use
$\sqrt{1-\alpha u^2}\leq1-\alpha u^2/2$. This bounds $f_G$ below by
$c_0+2xu+c_2u^2$ on $[0,1/\sqrt\alpha]$, where

$$
c_0=g_0+g_2/\beta-2y/\sqrt\beta,\qquad
c_2=g_1-\alpha g_2/\beta+\alpha y/\sqrt\beta.
$$

Outward rational substitution of (JR.86), with the square-root rules
in §56, gives

$$
c_0>.00234727>.0023,\qquad
c_0+2x/\sqrt\alpha+c_2/\alpha
=g_0+g_1/\alpha+2x/\sqrt\alpha-y/\sqrt\beta>.00334029>.0033.
$$

If $c_2\leq0$, the minimum is at an endpoint; otherwise the quadratic
is increasing for $u\geq0$. This proves (JR.133), including the axes.

Reuse the rank-supported zero-Rayleigh decomposition (JR.60): a PSD
matrix with zero $Q$ trace is a sum of exactly its rank in real null
outer products. A nonzero null vector has nonzero coordinate $0$, so
reverse its global sign and write it $\sqrt\pi(1,u,v)$, $\pi>0$.
Normalization of the whole tuple gives $\sum h_0^2=\sum h_1^2=1$;
hence every reassignment of reports has contrast at most
$\sum|h_0h_1|\leq1$. The strict decrease in Proposition 51.3 implies
that an optimum cannot have contrast larger than $\tau$; at $\tau=1$
the same statement follows directly from this ceiling. Moving a
misaligned atom to the other report keeps objective and all matrix
constraints, but strictly raises contrast, contradicting strict decrease
or the ceiling. In $X_{+,-}$ all remaining atoms therefore have $u\geq0$.
By (JR.133), changing their objective sign to $+$ strictly improves the
objective without changing any constraint. Thus that entire block is
zero. An objective-sign mismatch in any other atom is excluded by the
same sign flip. With $X_{+,-}=0$, the normalization identity makes signed
contrast $2(A_0)_{01}$. Conversely every feasible triple in (JR.132)
embeds as $(A_0,0,B_0,C_0)$ in (JR.84). Compactness and elimination
establish the claimed correspondence of optimizers. This is not equality
of the two full feasible sets. Atom reassignments here are mathematical
modifications of a tuple; Theorem 45.1 constructs a new actual instrument
for the modified tuple, without revealing a flag of an old instrument.
$\square$

**Definition 53.3 (the common finite correspondence).** For any finite
real null family $h_j=\sqrt{\pi_j}(1,u_j,v_j)^T$ with
$\sum_jh_jh_j^T=I$, set

$$
c_j=Lh_j,\qquad K_j=\sqrt{\pi_j}(s_0D+u_jT+v_jS).
\tag{JR.134}
$$

Use a fixed image isometry $V_j:\mathbb C^2\to\operatorname{ran}K_j$,
encoder $V_j^\dagger K_jE^\dagger$, and decoder
$X\mapsto EV_jXV_j^\dagger E^\dagger$ on all $M_2$.
Retain the actual label $j$ and its specified raw report $r_j$.
Add the two fair high branches
$\sqrt{(1-\delta)/2}\,DE^\dagger$ with full $M_3$ isometric decoders,
the four fair-report scalar spectral rows (JR.118), and the two scalar
complement branches of Definition 51.1. On a spectral row the decoder
sends $z$ to $zw_\ell g(t)dt\,P_f$ for each $\ell=0,\ldots,4$;
on a complement branch it sends $z$ to $zg(t)dt\,P_f$ at label $2$ only.
Their nonretained internal Kraus multiplicities are discarded.

**Proposition 53.4 (full output, actual laws and the TV direction).**
This is one finite common instrument with $m+8$ generated labels for
$m$ low atoms. At the conditional source root it has full TP decoders
and total encoder effect $I_5$. On each of the twelve actual histories,

$$
p(j\mid y,e,n)=\pi_j\|(s_0D+u_jT+v_jS)U_{e,n}a_y\|^2,
\quad p_H(y,e,n)=(1-\delta)A_y,
\quad\mathsf W=(1-\delta)A_{27}=\mathsf C(s).
\tag{JR.135}
$$

The coefficient weights $\pi_j$ are not these acquisition probabilities
and are not a source prior. Reports outside the low part are fair and

$$
\mathsf V(F)=s_0\sum_jr_j\pi_ju_j.
\tag{JR.136}
$$

**Proof.** Nullity gives $\det K_j=0$, whereas its $1,2$ minor is
$\pi_js_0^2h_1h_2\ne0$; its rank is exactly two. The image isometry
therefore exists and its decoder is TP on the entire declared fibre.
This reuses the finite image factorization of IR Lemma 4.2, not a new
compression theorem. The coefficient Gram is

$$
\sum_jc_jc_j^T=\operatorname{diag}(\delta,1,1),\qquad
\operatorname{diag}(\delta,1,1)+(1-\delta)e_0e_0^T=I.
\tag{JR.137}
$$

Thus low plus high effect is $I_3-M$. The spectral rows add $M$ and the
complement adds $I_5-P$. Every finite branch is CP/TNI. Scalar decoders
are TP because $\int_0^1g(t)dt=1$ and $\sum_\ell w_\ell=1$.
For every complex $A\in M_5$, $A_V=E^\dagger AE$, forgetting the labels
gives exactly

$$
\begin{aligned}
\Phi^L(A)&=E(DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger)E^\dagger,\\
\Phi^f_\ell(A)(B)&=\left(\int_B\frac{2\,dt}{(1+t)^2}\right)
\left[w_\ell\operatorname{tr}(MA_V)
+\mathbf1_{\ell=2}\operatorname{tr}((I_5-P)A)\right]P_f
\quad(\ell=0,\ldots,4).
\end{aligned}
\tag{JR.138}
$$

This holds for every Borel $B\subseteq[0,1]$, separately for all five
labels including the two zero-weight ones; there are no extra or singular
measures. Cross-support terms vanish. Tensor the finite Kraus identities
with $I_R$ for any passive reference. In the failure identity the scalar
traces become the exact conditional reference operators
$\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X]$ and
$\operatorname{Tr}_5[((I_5-P)\otimes I_R)X]$, not the unconditional
reference marginal. These algebraic identities establish the full complex,
reference and Borel scope, not only twelve probability identities.
They preserve the original HALF complete-cq error $E_*$ conditionally
on CG; the ideal densities remain $f_y(t)=6y/(y+6t)^2$, not $g(t)$.

Only the high pair has jointly counted dimension at least three; its
effect is $(1-\delta)ED^\dagger DE^\dagger$. This proves (JR.135),
including the worst height $27$, using JR §§34–40. The low $DT$ moment
gives (JR.136); no other effect coordinate is fixed. The actual retained
TV of this spectral realization is

$$
T_{\rm can}=\frac{(1-\delta)\Delta A+L_f+
\sum_j\pi_j|f_G(u_j,v_j)|}2.
\tag{JR.139}
$$

For an arbitrary original realization, separating live/failure products
and resolving their null atoms can increase TV. Its actual TV is at most
the corresponding right side, not equal to it in general. The equality
in (JR.139) belongs to the construction which generates these atom labels
and uses the optimal spectral failure readout. All choices precede the
sole unknown input. Precisely the declared dephased labels and full
quantum fibres remain accessible; any retained input-bearing specimen,
memory, controller, environment or entanglement share must be jointly
counted at the same cut. Other dilation systems are permanently discarded.
No prior, readable history, helper, postselection, acceptance division,
copy, reset, retry or bypass is supplied. $\square$

## 54. The exact initial residual branch through its first certificate zero

**Definition 54.1 (a specified algebraic frame).** Keep $t_*,\psi$ of
§50 and write

$$
\begin{gathered}
q(t)=\sqrt{\alpha+\beta t^2},\quad D(t)=A+(1+\beta)t^2,
\quad t_3=\sqrt{A/\alpha},\\
\mathcal A(t)=\alpha[\beta-(1+\beta)t^2],\qquad
\mathcal B(t)=\beta(\alpha t^2-A),\\
k(t)=\frac{\mathcal B(t)}{t+\sqrt{t^2-\mathcal A(t)\mathcal B(t)}},
\qquad p(t)=\sqrt{\alpha+\beta k(t)^2},\\
f_0=\frac{(q(t),-1,-t)^T}{\sqrt{D(t)}},\qquad
f_1=\frac{(p(t),1,k(t))^T}{\sqrt{D(k(t))}},\qquad f_2=f_0\times f_1.
\end{gathered}
\tag{JR.140}
$$

On $[t_*,t_3]$ these vectors form $F=(f_0,f_1,f_2)\in SO(3)$ and are
$Q$-null, with positive first coordinates and $01$ product signs $(-,+,-)$.
Their maximal signed contrast is

$$
h(t)=2(f_1)_0(f_1)_1=\frac{2p(t)}{D(k(t))},\quad
h(t_*)=\bar\tau,\quad h(t_3)=\tau_3:=\frac{2\sqrt\alpha}{A}<1.
\tag{JR.141}
$$

**Proof.** Orthogonality is the unsquared identity $qp=1+tk$.
Squaring gives $\mathcal A k^2-2tk+\mathcal B=0$; the rationalized root
in (JR.140) selects $k<0$ before $t_3$ and $k(t_3)=0$. Its discriminant is

$$
t^2-\mathcal A\mathcal B=
\alpha\beta^2A+(1-2\alpha\beta-2\alpha^2\beta^2)t^2
+\alpha^2\beta(1+\beta)t^4>0.
$$

The three coefficients are positive on (JR.86). Throughout
$[.85,t_3]$, one has $|k|<.271$, $t_3<1.464$, and hence
$1+tk>1-1.464\cdot.271>0$; this verifies the unsquared branch.
For completeness, the bound on $k$ follows from its increasing root:

$$
k'=(k-q'p)/(q\beta k/p-t)>0,
$$

whose numerator and denominator are negative, and direct outward
substitution at $t=.85$ gives $k>-.271$. This differentiation is
legitimate on the selected smooth root, where both denominators are
nonzero. The norms and nullity of $f_0,f_1$ follow by substitution.
Their unit cross product is null since $\operatorname{tr}Q=0$.
Its numerator is $(t-k,-tp-qk,q+p)$; the bounds above give
$tp+qk>.85\sqrt{.87770}-.271\sqrt{.87773+.12230(1.464)^2}>.506$.
This proves the coordinate and product signs. At $t_*$ this is exactly
the two-null-line completion of $v_*$ in §50. Finally

$$
\frac{dh}{dk}=
\frac{2k[\beta^2+2\beta-2-\beta(1+\beta)k^2]}
{\sqrt{\alpha+\beta k^2}\,D(k)^2}>0\quad(k<0).
$$

Thus $h'>0$ on $[t_*,t_3)$, while $h'(t_3)=0$ and
$k'(t_3)=\alpha\beta>0$. All radicals and root denominators remain
positive on the closed frame interval. $\square$

**Definition 54.2 (three discriminants).** In this moving frame put

$$
B=F^TGF,\quad c=F^TCF,\quad q_{ij}=(F^TQF)_{ij},\quad
\lambda(t)=2\psi'(t)/h'(t),\qquad \psi=B_{00}.
$$

The contrast multiplier $\lambda$ is distinct from $\lambda_{\rm sp}$.
It extends to $\lambda(t_*)=0$ and is defined by this ratio only for
$t<t_3$. Define

$$
\begin{aligned}
k_-&=c_{01}-q_{01}c_{12}/q_{12},&
k_+&=q_{02}c_{12}/q_{12}-c_{02},&
m&=B_{12}-q_{12}B_{02}/q_{02},\\
d_-&=-B_{00}c_{11}-\lambda k_-^2,\\
d_+&=B_{00}c_{22}+\lambda(c_{00}c_{22}-k_+^2),\\
d_N&=(B_{11}+\lambda c_{11})B_{22}-m^2.
\end{aligned}
\tag{JR.142}
$$

Since $q_{ii}=0$ and $2q_{01}q_{02}q_{12}=\det Q=\alpha\beta>0$,
every displayed $q_{ij}$ denominator is nonzero. Set

$$
t_\dagger=\min\{t\in(t_*,t_3):d_-(t)d_+(t)d_N(t)=0\},\qquad
\tau_\dagger=h(t_\dagger).
\tag{JR.143}
$$

**Theorem 54.3 (exact original branch and bounded uniqueness).** The
minimum in (JR.143) exists, with
$t_*<t_\dagger<t_3$ and $\bar\tau<\tau_\dagger<\tau_3$.
For every $t_*<t\leq t_\dagger$,

$$
\boxed{j(h(t))=\operatorname{tr}G-2\psi(t),\qquad
\mathcal T(s_0h(t))=T_{\rm flat}-\psi(t).}
\tag{JR.144}
$$

A matching original primal tuple is

$$
X_{-,-}=f_0f_0^T,\quad X_{+,+}=f_1f_1^T,\quad
X_{-,+}=f_2f_2^T,\quad X_{+,-}=0.
\tag{JR.145}
$$

On $t_*<t<t_\dagger$ this SDP tuple is unique. The three active original
dual slacks have rank two and the fourth can be strictly positive
definite. At $t_\dagger$ at least one active slack has rank one; the
fourth can still be strictly positive definite. These are statements
about aggregate matrices and certificates, not uniqueness of a complete
channel, a physical realization, or a minimum physical-label count.

**Proof.** Define

$$
\nu_0=0,\quad \nu_1=2(B_{01}+\lambda c_{01})/q_{01},\quad
\nu_2=2B_{02}/q_{02},
$$

and the full symmetric matrix

$$
\widetilde Y=\begin{pmatrix}
-B_{00}-\lambda c_{00}&-B_{01}-\lambda c_{01}&-B_{02}-\lambda c_{02}\\
-B_{01}-\lambda c_{01}&B_{11}+\lambda c_{11}&B_{12}+\lambda c_{12}-\nu_1q_{12}\\
-B_{02}-\lambda c_{02}&B_{12}+\lambda c_{12}-\nu_1q_{12}&B_{22}-\lambda c_{22}
\end{pmatrix},\qquad Y=F\widetilde YF^T.
\tag{JR.146}
$$

For $F'=F\Omega$, $\Omega^T=-\Omega$, differentiation of the three null
equations gives
$w=q_{01}\Omega_{01}=-q_{02}\Omega_{02}=q_{12}\Omega_{12}$.
Differentiation of $B_{00}$ and $h=2c_{11}$ gives

$$
\psi'=-2w(B_{01}/q_{01}-B_{02}/q_{02}),\qquad
h'=4w(c_{01}/q_{01}-c_{12}/q_{12}).
$$

As $h'>0$, $w\ne0$, and $\lambda h'=2\psi'$ is exactly
$(\nu_1-\nu_2)q_{12}=2\lambda c_{12}$. Consequently the original slacks

$$
S_{-,-}=Y+G+\lambda C,\quad
S_{+,+}=Y-G-\lambda C+\nu_1Q,\quad
S_{-,+}=Y-G+\lambda C+\nu_2Q
\tag{JR.147}
$$

annihilate respectively $f_0,f_1,f_2$. On their respective orthogonal
complements their matrices are

$$
\begin{aligned}
S_{-,+}|_{\langle f_0,f_1\rangle}
&=2\begin{pmatrix}-B_{00}&\lambda k_-\\\lambda k_-&\lambda c_{11}\end{pmatrix},\\
S_{+,+}|_{\langle f_0,f_2\rangle}
&=2\begin{pmatrix}-B_{00}-\lambda c_{00}&\lambda k_+\\
\lambda k_+&-\lambda c_{22}\end{pmatrix},\\
S_{-,-}|_{\langle f_1,f_2\rangle}
&=2\begin{pmatrix}B_{11}+\lambda c_{11}&m\\m&B_{22}\end{pmatrix}.
\end{aligned}
\tag{JR.148}
$$

Their determinants are $4\lambda d_-,4\lambda d_+,4d_N$.
Moreover $c_{11}>0$, $c_{00},c_{22}<0$, and $B_{11}>0$ by (JR.133).
Thus when $\lambda>0$ and all three discriminants are positive,
$d_->0$ implies $B_{00}<0$, and $d_N>0$ implies $B_{22}>0$.
Every matrix in (JR.148) is then positive definite.

There is also a fourth ORIGINAL slack. Put $R=Y+G-\lambda C$.
For any nonzero real $Q$-null $z$, if $z^TCz\geq0$, (JR.133) implies
$z^TGz>0$, and

$$
z^TRz=z^TS_{+,+}z+2z^TGz>0.
$$

If $z^TCz<0$, then
$z^TRz=z^TS_{-,-}z-2\lambda z^TCz>0$.
Compactness of the unit null set yields a positive minimum $a$.
Apply the equality S-lemma to $z^T(R-eI)z$, $0<e<a$, with constraint
$z^TQz=0$. Specifically, Xia–Wang–Sheu,
[S-Lemma with Equality and Its Applications, arXiv:1403.2816v3,
Theorem 3](https://arxiv.org/pdf/1403.2816v3), under its Assumption 1,
requires the constraint to take both signs. Here $Q$ is indefinite.
Its only exceptional case requires zero quadratic constraint matrix
and a nonzero linear constraint term; our matrix is the nonzero $Q$.
The theorem therefore supplies a finite real $\nu_3$ with

$$
S_{+,-}=Y+G-\lambda C+\nu_3Q\succeq eI\succ0.
\tag{JR.149}
$$

Only this certificate-completion mechanism is borrowed, not a value or
contact choice. One can choose $\nu_3$ algebraically: sort the distinct
real roots of $\det(R+\nu Q)$ and test Sylvester minors at their adjacent
midpoints. The PD set is one nonempty open interval by convexity and is
bounded because $Q$ is indefinite. Its endpoints are adjacent determinant
roots; their midpoint is an admissible choice. The leading coefficient
is $\det Q\ne0$, so there is no identically zero determinant exception.
This is a pointwise finite choice, not a uniform strict margin at $t_*$.

The primal (JR.145) is feasible with contrast $h(t)$. Since
$\operatorname{tr}c=0$ and $h=2c_{11}$,

$$
\operatorname{tr}Y-\lambda h(t)=\operatorname{tr}G-2B_{00}.
\tag{JR.150}
$$

This equals the primal objective, so the original primal and all four
original dual blocks match whenever the stated signs hold.

It remains to prove the whole nonempty interval, not just local signs.
At $t_*$, $\lambda=0$, $B_{00}=\mu_*<0$, and
$d_-=-\mu_*c_{11}>0$, $d_+=\mu_*c_{22}>0$.
The third discriminant is the determinant of the compression of
$H_*=G+\lambda_{\rm sp}Q$ to $f_0^\perp$, positive by Theorem 50.4.
Its positive spectrum also follows directly from (JR.86) and
$\lambda_{\rm sp}<.0032$: the $1,2$ principal block has positive
entries on the diagonal and determinant $>1.35\cdot10^{-7}$.
Constrained differentiation gives

$$
\psi''(t_*)=2f_0'(t_*)^T(H_*-\mu_*I)f_0'(t_*)>0,
\tag{JR.151}
$$

because $f_0'\ne0$ is perpendicular to $f_0$. Thus $\lambda>0$ just
to the right of $t_*$. Existence of a later discriminant zero is proved
below independently of this positivity continuation. The zero set is
closed away from the two endpoints, with no zeros in an initial
neighborhood; minimizing it on a compact interval ending at any later
zero proves that (JR.143) is a genuine least zero.

On $(t_*,t_\dagger)$ all discriminants stay positive. If $\lambda$
first returned to zero at $t_0\leq t_\dagger$, continuity and (JR.148)
would leave the first two compressions PSD, equal to
$2\operatorname{diag}(-B_{00},0)$. The third is PSD since $B_{11}>0$
and $d_N\geq0$. At that return choose the fourth slack equal to
$S_{-,-}$, with $\nu_3=0$. Equation (JR.150) still matches a zero-contrast-
multiplier dual at $h(t_0)>\bar\tau$. Such a dual bounds even $j(0)$
by $j(h(t_0))$, contradicting (JR.114). Hence $\lambda$ remains strictly
positive, including at $t_\dagger$. The three compressions are PD before
that endpoint and PSD at it. Each has a positive diagonal entry there,
namely $\lambda c_{11}$, $-\lambda c_{22}$, or $B_{11}+\lambda c_{11}$.
A vanishing determinant therefore gives rank exactly one. Since
$h'(t_\dagger)>0$, every multiplier already displayed is finite; construct
(JR.149) anew at the endpoint, without assuming the earlier choices of
$\nu_3$ remain bounded. This proves (JR.144) through the endpoint.

In the open interval, complementary slackness puts any optimal tuple
in the three one-dimensional kernels of (JR.147), and forces
$X_{+,-}=0$ by (JR.149). Thus its other blocks are $a_if_if_i^T$;
normalization in the orthonormal frame gives $a_0=a_1=a_2=1$.
This proves precisely the bounded uniqueness statement. Differentiating
(JR.144) gives

$$
j'(h(t))=-\lambda(t)<0,\qquad
\mathcal T'(s_0h(t))=-\lambda(t)/(2s_0)
\quad(t_*<t<t_\dagger).
\tag{JR.152}
$$

No endpoint uniqueness or true support transition is inferred. $\square$

**Proposition 54.4 (a later zero and the three-atom cap).** The three-atom
contrast ceiling is exactly $\tau_3$ in (JR.141). No optimal representation
by at most three real rank-one null atoms exists at $\tau_3$, or throughout
some interval $(\tau_3-\eta,1]$, $\eta>0$. The candidate discriminant
$d_+$ tends to $-\infty$ as $t\uparrow t_3$, so the least zero in
Theorem 54.3 occurs strictly before $t_3$.

**Proof.** Three nonzero rank-one atoms summing to $I_3$ must be the
columns of an orthogonal matrix; fewer cannot span $I_3$. Their $01$
products sum to zero, so their absolute sum is twice the largest absolute
product. For a unit null vector, writing $Y=f_1^2$ gives

$$
f_0^2=\frac{\beta+(1-2\beta)Y}{1+\beta},\quad
f_2^2=\frac{1-AY}{1+\beta},\quad 0\leq Y\leq1/A.
$$

Since $0<\beta<1/2$, $4f_0^2Y$ is strictly increasing and its maximum
is $4\alpha/A^2$. The bound $\tau_3=2\sqrt\alpha/A$ is attained.
At equality the distinguished vector has third coordinate zero.
Up to column signs and permutations the only cap frames are

$$
\begin{aligned}
\mathcal F_+&=\{p,n_-,n_+\},&
p&=(\sqrt\alpha,1,0)/\sqrt A,&
n_\pm&=(1,-\sqrt\alpha,\pm\sqrt A)/\sqrt{2A},\\
\mathcal F_-&=\{q,m_-,m_+\},&
q&=(\sqrt\alpha,-1,0)/\sqrt A,&
m_\pm&=(1,\sqrt\alpha,\pm\sqrt A)/\sqrt{2A}.
\end{aligned}
\tag{JR.153}
$$

The remaining two null lines in each orthogonal plane give exactly
these completions. Source-box substitution shows only $n_-$ is negative
in $\mathcal F_+$, only $q$ is negative in $\mathcal F_-$, and
$n_-^TGn_-<-.0009$, $-.0003<q^TGq<-.0001$; all other heights are positive.
Along $p(k)=(\sqrt{\alpha+\beta k^2},1,k)/\sqrt{D(k)}$ choose the smooth
null completion near $k=0$. The nonzero traceless compression of $Q$ has
two simple null lines, so this is a two-sided smooth choice. Differentiating
orthogonality, norm and nullity gives

$$
n_-'(0)=p/\sqrt{2A}-\sqrt\alpha\,n_+/(2\beta\sqrt A),\qquad
(n_-^TGn_-)'(0)=\mathcal R/(A\sqrt A),
$$

where

$$
\mathcal R=\sqrt\alpha(g_0-g_1)+\beta x-\sqrt A(\sqrt\alpha y+z)
-\frac{\sqrt\alpha}{2\beta}(g_0+\alpha g_1-2\sqrt\alpha x-Ag_2).
\tag{JR.154}
$$

Outward substitution of (JR.86) gives
$\mathcal R/(A\sqrt A)>.00405167>.003$.
For example, the final parenthesis is $<-.0037$, the first three terms
are $>-.0041$, $\sqrt\alpha/(2\beta)>3.8$, and $A\sqrt A<2.6$;
these coarser rational inequalities alone imply $>.003$.
For the second frame vary
$q(k)=(\sqrt{\alpha+\beta k^2},-1,k)/\sqrt{D(k)}$; then
$(q^TGq)'(0)=2(\sqrt\alpha y-z)/A>0$.
Both cap contrasts have derivative zero. If a cap frame optimized the
original problem, finite dual attainment at the interior $\tau_3<1$
would make it maximize $J+\lambda h$ over the unconstrained normalized
null tuples. A two-sided smooth variation would then have zero
Lagrangian derivative. Here $J'=-2$ times the nonzero negative-height
derivative, while $h'=0$, a contradiction. The variations need not
satisfy a fixed contrast lower bound; they satisfy all constraints of
this unconstrained Lagrangian maximization.

The set of null orthonormal frames with finitely many report/sign
assignments is compact. If optimal three-atom frames occurred arbitrarily
close on the left of $\tau_3$, a convergent subsequence and continuity of
the finite concave $j$ at this interior point would give an optimal cap
frame. Combining this contradiction with infeasibility above $\tau_3$
proves the stated left-extended obstruction.

At $t_3$ the frame (JR.140) is $(n_-,p,n_+)$, and
$\psi'(t_3)>0$ by (JR.154) and $k'(t_3)=\alpha\beta>0$.
Thus the continued candidate $\lambda=2\psi'/h'$ tends to $+\infty$.
At the same endpoint

$$
c_{00}=c_{22}=-\sqrt\alpha/(2A),\quad
k_+=(\alpha+\beta^2)/(2A\sqrt\alpha),\quad
c_{00}c_{22}-k_+^2=-\frac{\beta^2(2\alpha+\beta^2)}{4A^2\alpha}<0.
$$

Therefore $d_+\to-\infty$, whereas $d_+(t_*)>0$, proving the later zero
needed above. The functions are algebraic on their specified analytic
branch; their zero sets before $t_3$ are semialgebraic and have no
accumulation at $t_*$. At the conditional algebraic source point the
least zero is an exactly specified algebraic number. This identifies no
first vanishing factor. The divergence describes a continued trial
frame beyond its certified interval, not the optimal multiplier at the
interior contrast $\tau_3$. $\square$

**Corollary 54.5 (an original finite attainer).** Substituting the three
columns of (JR.140), with reports $(-,+,-)$, into Definition 53.3 gives
an eleven-label instrument attaining (JR.144). Its fibre dimensions are
$(2,2,2,3,3,1,1,1,1,1,1)$. The matching upper bound covers the full
original class in Convention 53.1. These labels are a construction count,
not a lower bound on arbitrary multi-Kraus acquisition labels.

**Proof.** Equations (JR.145) and (JR.150) match; the objective signs and
reports are aligned by Lemma 53.2. Apply (JR.134)–(JR.139). $\square$

## 55. Matching endpoint bounds with full remainders and multiplier scope

**Definition 55.1 (the endpoint coefficient).** Put
$\varepsilon=1-s/s_0$, $\gamma=\alpha/\beta$, and

$$
\begin{aligned}
R_1&=x-g_1-z+\alpha(x+y-g_0),&
R_2&=y-z-g_2+\beta(x+y-g_0),\\
b_{++}&=R_1-\gamma R_2,&b_{+-}&=-(1+\gamma)R_2,\\
b_{-+}&=(1+\gamma)R_1,&
b_{--}&=-(\gamma+2)R_1+(2\gamma+1)R_2,\\
\Gamma&=\sqrt{\tfrac18\sum_{\sigma,\eta=\pm1}b_{\sigma\eta}^2},&
T_0&=\mathcal T(s_0)=T_{\rm flat}-b(1).
\end{aligned}
\tag{JR.155}
$$

The scalar $b(1)$ in $T_0$ is the inherited endpoint residual, not an
entry of the four-number list $b_{\sigma\eta}$. We have $\sum b_{\sigma\eta}=0$,
$.008<\Gamma<.009$, and $|b_{\sigma\eta}/\Gamma|<3$.
These follow directly from the source formulas and directed enclosures
specified in §56; for example
$.00824076104752150020<\Gamma<.00824076104752150022$.

**Theorem 55.2 (quantitative endpoint law).** Under Convention 53.1,
for every $0<\varepsilon\leq10^{-8}$,

$$
\boxed{T_0+\Gamma\sqrt\varepsilon-15\varepsilon
\leq\mathcal T(s_0(1-\varepsilon))
\leq T_0+\Gamma\sqrt\varepsilon+11\varepsilon.}
\tag{JR.156}
$$

The lower bound is attained as a lower value by one twelve-label finite
common instrument. It is asymptotically optimal and is not asserted to
be a pointwise optimizer at any nonzero $\varepsilon$.

**Proof.** Decompose the real-null matrices as in (JR.60) and write the
atoms as $\sqrt\pi(1,u,v)$. Their exact moment conditions are

$$
\alpha u^2+\beta v^2=1,\quad
\mathbb E1=1,\quad\mathbb Eu=\mathbb Ev=\mathbb Euv=0,\quad
\mathbb Eu^2=\mathbb Ev^2=1.
\tag{JR.157}
$$

These expectations are coefficient sums, not averages over unknown
histories. For arbitrary feasible reports, let
$e=1-\mathbb E|u|$. The original inequality gives $0\leq e\leq\varepsilon$.
With $d=|u|-1$ there are exact identities

$$
\mathbb Ed=-e,\qquad \mathbb Ed^2=2e.
\tag{JR.158}
$$

At $e=0$ they force $|u|=|v|=1$, and the three zero mixed moments
force weight $1/4$ at each of the four corners.

Put $B=f_G(-1,-1)=-(R_1+R_2)=4b(1)<0$ and
$m=2(\gamma R_2-R_1)$. Define

$$
P(u,v)=\frac B4(1-u)(1-v)+\frac m8(u^2-1),\qquad
\mathfrak r(u,v)=\min\{f_G(u,v),0\}-P(u,v).
\tag{JR.159}
$$

By (JR.157), $\mathbb EP=B/4$. Equations (JR.130), (JR.139) and
$|f_G|=f_G-2\min(f_G,0)$ therefore give the universal necessity direction

$$
\boxed{T_{\rm instr}-T_0\leq-\mathbb E\mathfrak r.}
\tag{JR.160}
$$

Equality holds for Definition 53.3 with its actually generated atom
labels and optimal spectral failure readout. It does not hold for an
arbitrary original realization. For instance coordinate failure rows
preserve the forgotten complete channel but contribute $d_f$ instead of
$L_f$, losing $(L_f-d_f)/2>0$ when the off-diagonal failure difference
$z_f\ne0$. An analytic refinement used for this upper bound is not free
physical information.

We prove a remainder over the ENTIRE null ellipse. Assign signs
$\sigma,\eta\in\{\pm1\}$ to $u,v$, choosing either sign at a zero, and write

$$
u=\sigma(1+d),\quad v=\eta\varphi(d),\quad
\varphi(d)=\sqrt{1-2\gamma d-\gamma d^2},\quad
-1\leq d\leq\sqrt{1+1/\gamma}-1.
\tag{JR.161}
$$

Direct differentiation at $d=0$ gives
$\mathfrak r=0$ and derivative $\ell_{\sigma\eta}=b_{\sigma\eta}/2$.
The following bound includes the axes, the extreme $d$ values, and the
zeros of $f_G$:

$$
|\mathfrak r(\sigma(1+d),\eta\varphi(d))-
\ell_{\sigma\eta}d|\leq3d^2.
\tag{JR.162}
$$

To see this with explicit constants, the exact radical identity is

$$
\varphi(d)-(1-\gamma d)=
-\frac{\gamma(\gamma+1)d^2}{\varphi(d)+1-\gamma d}.
\tag{JR.163}
$$

Its denominator is minimized at the upper endpoint: its derivative
is $-\gamma(1+d)/\varphi-\gamma<0$ in the interior, so it is at least
$\gamma+1-\sqrt{\gamma(\gamma+1)}>1/2$.
The coarse source bounds give
$1<\gamma<8$, $|u|<2$, $|d|\leq1$,
$|g_1|<.003$, $|g_2|<.002$, $|x|,|y|<.003$, $|z|<1/8000$.
Consequently $|\varphi-(1-\gamma d)|\leq144d^2$.
The remainder of $f_G$ from its corner tangent is at most

$$
[.003+8(.002)+2(.003)(144)+2(1/8000)(8+2\cdot144)]d^2
=.957d^2.
$$

Its corner tangent coefficient has absolute value at most
$.006+.032+.006+.048+.00175=.09375<.1$.
All four corner $|f_G|$ exceed $.003$, and only the negative-negative
corner has negative height. For $a\ne0$, the elementary kink estimate

$$
|\min(a+Ad,0)-\min(a,0)-\mathbf1_{a<0}Ad|
\leq A^2d^2/(4|a|)
$$

follows by maximizing $(|A||d|-|a|)/d^2$ in the crossing case;
otherwise the left side is zero. Since the minimum function is
1-Lipschitz, the remainder of $\min(f_G,0)$ is at most
$(.957+5/6)d^2<2d^2$. Also $|B|<.004$, $|m|<1/40$.
Expanding $(1-u)(1-v)$ using (JR.163), its remainder coefficient
is at most $8+3\cdot144=440$. Hence the remainder of $P$ is at most
$(.004\cdot440/4+1/320)d^2=.443125d^2<d^2/2$.
The two remainder bounds prove (JR.162).

Let $\pi_{\sigma\eta}$ be total coefficient weight in a sign sector.
Writing $S=\operatorname{sgn}u$, $H=\operatorname{sgn}v$, (JR.157),
(JR.158) and (JR.163) give

$$
\begin{aligned}
|\mathbb ES|&\leq\sqrt{2e},\\
|\mathbb EH|&\leq\gamma\sqrt{2e}+288e,\\
|\mathbb ESH|&\leq(\gamma-1)\sqrt{2e}+(2\gamma+576)e.
\end{aligned}
$$

Fourier inversion on the four signs therefore yields

$$
|\pi_{\sigma\eta}-1/4|\leq\gamma\sqrt{2e}/2+220e,
\tag{JR.164}
$$

because $(864+2\gamma)/4<220$. Since
$\sum\ell_{\sigma\eta}^2=2\Gamma^2$, Cauchy–Schwarz, (JR.160) and
(JR.162) imply, for arbitrary actual records,

$$
\begin{aligned}
T_{\rm instr}-T_0
&\leq-\mathbb E(\ell d)+6e\\
&\leq\Gamma\sqrt e+(6+\gamma\sqrt2\,\Gamma)e+440\Gamma e^{3/2}\\
&\leq\Gamma\sqrt e+11e\leq\Gamma\sqrt\varepsilon+11\varepsilon.
\end{aligned}
\tag{JR.165}
$$

Here $\sqrt{1+a}\leq1+a/2$ bounds the sector-weight factor in
$\mathbb E\ell^2$, and $e\leq10^{-8}$ makes the coefficient strictly
less than $11$ using $\Gamma<.009$, $\gamma<8$. This proves the upper
bound with the universal inequality, without an ungenerated readout.

For the matching lower coefficient put $d_j^\circ=-b_j/\Gamma$, in corner
order $(++),(+-),(-+),(--)$. Then
$\sum d_j^\circ=0$, $\sum(d_j^\circ)^2=8$, $|d_j^\circ|<3$.
For $0<h\leq10^{-4}$ and $|c|\leq2048h^2$, set

$$
\begin{gathered}
d_j=hd_j^\circ+c,\quad u_j=\sigma_j(1+d_j),\quad
v_j=\eta_j\varphi(d_j),\\
\mathscr M(h,c)=\begin{pmatrix}
1&1&1&1\\u_{++}&u_{+-}&u_{-+}&u_{--}\\
v_{++}&v_{+-}&v_{-+}&v_{--}\\
u_{++}v_{++}&u_{+-}v_{+-}&u_{-+}v_{-+}&u_{--}v_{--}
\end{pmatrix},\qquad
\pi(h,c)=\mathscr M(h,c)^{-1}(1,0,0,0)^T.
\end{gathered}
\tag{JR.166}
$$

All entries in the fourth row are $u_jv_j$. Let $c$ be the least root
in this closed interval of

$$
F(h,c):=\sum_j\pi_j(h,c)u_j(h,c)^2-1=0.
\tag{JR.167}
$$

We establish existence and exact moments, not just formal expansions.
Let $r=\max|d_j|<4h\leq1/2500$. The radicals stay positive and
$|\varphi-1|<9r$, $|uv-\sigma\eta|<19r$.
At $h=c=0$, $\mathscr M=H_4$ is a Hadamard matrix with
$\|H_4^{-1}\|_\infty=1$. Throughout the entire rectangle,
$\|\mathscr M-H_4\|_\infty\leq76r<1$; the Neumann estimate gives

$$
\|\pi-\tfrac14\mathbf1\|_\infty
\leq\frac{19r}{1-76r}<22r\leq.0088<1/4.
\tag{JR.168}
$$

Thus all weights are positive and the inverse is continuous throughout.
The first row makes their sum one. Since
$\sum_j|d_j^\circ|<12$ and $\sum d_j^\circ=0$,

$$
|F(h,c)-2c|\leq2h(22r)12+r^2\leq2128h^2.
$$

At $c=\pm2048h^2$, $2c=\pm4096h^2$, so the signs differ.
The intermediate value theorem gives a nonempty compact root set;
its least element exists. No uniqueness or continuous selection of
roots is required. Rows $1,u,v,uv$ and (JR.167) give all moments in
(JR.157), with $\mathbb Ev^2=1$ following from the null equation.

Write $\varepsilon_h=1-\sum_j\pi_j|u_j|$.
Expanding the second moment and using (JR.168) gives

$$
\left|\sum_j\pi_jd_j^2-2h^2\right|
\leq704h^3+8519680h^4<1600h^3,\qquad
|\varepsilon_h-h^2|\leq800h^3.
\tag{JR.169}
$$

Indeed the first coefficient is $22\cdot4\cdot8$, and the fourth-order
coefficient is $2\cdot2048\cdot22\cdot4\cdot12+2048^2$.
The uniform-weight linear term in $-\mathbb E\ell d$ is $\Gamma h$.
The weight perturbation contributes at most $352\Gamma h^2$;
the common shift contributes at most
$2\sqrt2\cdot2048\cdot88\Gamma h^3<54.0672\Gamma h^2$.
The remainder in (JR.162) contributes at most
$6\varepsilon_h\leq6.48h^2<13h^2/2$.
For the actual spectral construction, where (JR.160) is equality,

$$
T_{\rm can}(h)\geq T_0+\Gamma h-(407\Gamma+13/2)h^2
\geq T_0+\Gamma h-11h^2.
\tag{JR.170}
$$

For a prescribed $0<\varepsilon\leq10^{-8}$ choose

$$
h=\frac{\sqrt\varepsilon}{1+400\sqrt\varepsilon}.
\tag{JR.171}
$$

Then $\varepsilon_h\leq h^2(1+800h)\leq\varepsilon$ and
$h\geq\sqrt\varepsilon-400\varepsilon$.
Definition 53.3 on these four atoms, with reports $r_j=\sigma_j$, has
$\mathsf V=s_0(1-\varepsilon_h)\geq s_0(1-\varepsilon)$,
all twelve original error constraints and the sharp common cost.
Thus $T_{\rm can}\geq T_0+\Gamma\sqrt\varepsilon-15\varepsilon$ since
$400\Gamma+11<15$. Its twelve generated labels comprise four two-dimensional,
two three-dimensional and six scalar fibres. If exact rather than lower-
bounded contrast is desired, the fixed kernel

$$
\Pr(F=f\mid r)=\tfrac12\left[1+fr\frac{1-\varepsilon}{1-\varepsilon_h}\right]
$$

retains the old label and report, adds $F$, and preserves TV. Its ratio
is in $[0,1]$; at most twenty-four labels suffice. The original inequality
needs only twelve. This completes both bounds with the full original
instrument correspondence. $\square$

**Theorem 55.3 (every optimal normalized multiplier and first-order
contacts).** Let $\lambda_s$ be any optimal multiplier of the normalized
contrast in (JR.126), $s<s_0$. Then

$$
\lim_{s\uparrow s_0}\lambda_s\sqrt{1-s/s_0}=\Gamma,
\qquad
\lambda_s=\Gamma/\sqrt\varepsilon+O(\varepsilon^{-1/4}).
\tag{JR.172}
$$

For every optimal real-null decomposition near the endpoint, its sector
weights tend to $1/4$ and

$$
\mathbb E\left[
\left(\frac{|u|-1}{\sqrt\varepsilon}+\frac{b_{\sigma\eta}}\Gamma\right)^2
\right]\longrightarrow0.
\tag{JR.173}
$$

**Proof.** Let $F(\varepsilon)=j(1-\varepsilon)$.
Theorem 55.2 gives
$F(\varepsilon)=F(0)+2\Gamma\sqrt\varepsilon+R(\varepsilon)$,
$-30\varepsilon\leq R(\varepsilon)\leq22\varepsilon$.
An optimal normalized contrast multiplier is a supergradient of this
concave function; every such supergradient obeys

$$
\frac{F(\varepsilon+\Delta)-F(\varepsilon)}\Delta
\leq\lambda_s\leq
\frac{F(\varepsilon)-F(\varepsilon-\Delta)}\Delta.
\tag{JR.174}
$$

For $0<\varepsilon\leq5\cdot10^{-9}$ take $\Delta=\varepsilon^{5/4}$.
Both comparison points lie in $(0,10^{-8}]$.
The $R$ contribution in either secant is at most
$(60+30\varepsilon^{1/4})\varepsilon^{-1/4}$ in absolute value;
the square-root secant differs from $\Gamma/\sqrt\varepsilon$ by at most
$\Gamma\varepsilon^{-1/4}/[4(1-\varepsilon^{1/4})^{3/2}]$.
Their sum is $<61\varepsilon^{-1/4}$, proving (JR.172) without a
smoothness or multiplier-uniqueness hypothesis. This is the multiplier
for $j(\tau)$, not the physical-$s$ derivative and not $\lambda_{\rm sp}$.
A finite endpoint dual minimum would force
$j(1-\varepsilon)-j(1)\leq\lambda\varepsilon$, contradicting (JR.156).
Endpoint primal attainment and equal dual infimum from Theorem 51.4
are retained, with no finite original dual minimum.

By Lemma 53.2 any optimal decomposition has aligned saturated contrast;
hence $e=\varepsilon$ in (JR.158). Equation (JR.164) gives its sector
weight limits. Asymptotic equality in the upper/lower estimates forces
$\mathbb E[b_{\sigma\eta}d/(\Gamma\sqrt\varepsilon)]\to-2$.
Also $\mathbb Ed^2/\varepsilon=2$ and
$\mathbb Eb_{\sigma\eta}^2/\Gamma^2\to2$.
Expanding the square gives (JR.173), including arbitrary proportional
splitting. This is first-order contact rigidity, not a proof that four
rays optimize each interior point, nor a physical-label minimum. $\square$

## 56. A uniform pre-cap obstruction with exhaustive candidates

**Theorem 56.1 (uniform exclusion below the feasibility cap).** Put

$$
I=[996999/1000000,997001/1000000].
\tag{JR.175}
$$

For every $\tau\in I$, no optimum of the original problem can have an
associated optimal representation by at most three real rank-one
$Q$-null atoms. Equivalently every optimal reduced triple (JR.132)
has aggregate rank sum at least four. There is an explicit feasible
four-atom instrument whose TV exceeds the upper value of every
saturated aligned three-atom candidate by more than $17/5000000$,
uniformly on $I$. The witness is not asserted to optimize the original
problem. Aggregate rank, real-null atom count and physical-label count
are distinct quantities.

**Proof.** If an optimum admitted at most three atoms, normalization
would make them an orthonormal null frame, as in Proposition 54.4.
By Lemma 53.2 its reports and objective signs align and its contrast
is saturated. The three $01$ products sum to zero, so some column
$h$ has $|h_0h_1|=\tau/2$. Write $Y=h_1^2$, $X=h_0^2$, $Z=h_2^2$.
The unique possible nonnegative root is

$$
\begin{gathered}
Y=\frac{-\beta+\sqrt{\beta^2+(1-2\beta)(1+\beta)\tau^2}}{2(1-2\beta)},\\
X=\frac{\beta+(1-2\beta)Y}{1+\beta},\qquad
Z=\frac{1-AY}{1+\beta}.
\end{gathered}
\tag{JR.176}
$$

Indeed $4[\beta Y+(1-2\beta)Y^2]/(1+\beta)=\tau^2$ is strictly
increasing for $Y\geq0$; its other quadratic root is negative.
All $X,Y,Z$ are strictly positive on $I$. Up to a global column sign,
$h=(\sqrt X,\sigma\sqrt Y,\eta\sqrt Z)$ for four sign pairs.
For each pair define

$$
\begin{gathered}
e=(h_1,-h_0,0)/\sqrt{X+Y},\quad k=h\times e,\quad
m=e^TQe,\quad n=e^TQk,\\
t=(n+\sqrt{n^2+m^2})/m,\quad
f=(e+tk)/\sqrt{1+t^2},\quad g=h\times f,\\
J_{\sigma\eta}(\tau)=|h^TGh|+|f^TGf|+|g^TGg|.
\end{gathered}
\tag{JR.177}
$$

The $Q$ compression to $h^\perp$ is
$\left(\begin{smallmatrix}m&n\\n&-m\end{smallmatrix}\right)$.
It is nonzero: a two-dimensional totally null plane would intersect
$e_0^\perp$, on which $Q$ is strictly negative. On $I$, in fact
$m>1/10$. Its two distinct null slopes are
$(n\pm\sqrt{n^2+m^2})/m$, with product $-1$.
Thus $f,g$ are exactly the two remaining null lines. Choosing the other
root merely interchanges them up to sign. Column permutations, global
signs, zero blocks, rank-two aggregates and proportional splittings are
all covered by selecting a distinguished maximal-product column and
using these four pairs. Overinclusion of a frame would only strengthen
the upper bound. No arbitrary trial family is assumed exhaustive.

For a better feasible tuple set, with a different notation from $h$,

$$
\begin{gathered}
u=-6/7,\quad v=\sqrt{(1-\alpha u^2)/\beta},\quad
b=(1,u,v)^T,\quad c=(1,-1,-1)^T,\\
N=b^Tb,\quad K=3N-(b^Tc)^2>0,\quad r=7/6,\\
a_q=-rK,\quad b_q=rN-3+r\tau K/2,\quad c_q=1-r\tau N/2,\\
\mathcal D=b_q^2-4a_qc_q,\quad
q=\frac{-b_q-\sqrt{\mathcal D}}{2a_q},\quad p=r(\tau/2-q),\\
B_0=pbb^T,\quad C_0=qcc^T,\quad A_0=I-B_0-C_0,\quad
\rho=2-pN-3q.
\end{gathered}
\tag{JR.178}
$$

The selected $q$ is the larger root because $a_q<0$.
Both $b,c$ are exactly null. The determinant lemma gives

$$
\det A_0=1-pN-3q+pqK=a_qq^2+b_qq+c_q=0,
\qquad (A_0)_{01}=6p/7+q=\tau/2.
\tag{JR.179}
$$

The rank-two matrix $B_0+C_0$ leaves an eigenvalue one in $A_0$;
the remaining eigenvalues have product zero and sum $\rho$.
The directed bounds below show $p,q>0$, $\mathcal D>0$, $0<\rho<1$.
Therefore $A_0$ is PSD of rank two with eigenvalues $(0,\rho,1)$,
and $B_0,C_0$ are positive rank one. Their $Q$ traces vanish, so this
is feasible for the unchanged reduced problem at the same $\tau$.

To establish its actual refined signs, let $d=1-pN$ and

$$
w=c+\frac{p(b^Tc)}d\,b.
\tag{JR.180}
$$

The exact identity $A_0w=(\det A_0/d)c=0$ and rank two show
$\operatorname{ran}A_0=w^\perp$. The bounds below give $d>0$, $w_1<0$,
$w_0-|w_2|/\sqrt\beta>1.2300$. If a nonzero null vector of this range
is normalized as $(1,u,v)$ with $u\leq0$, its inner product with $w$
is at least $w_0-|w_2|/\sqrt\beta>0$, a contradiction. Thus every range
null atom has $u>0$, so positive height by (JR.133).
Also $b^TGb>.012046$ and $c^TGc<-.0034916$.
The rank-supported decomposition splits $A_0$ into exactly two null
atoms; give these report $+$ and the atoms $\sqrt p\,b,\sqrt q\,c$
report $-$. Their height signs are $(+,+,+,-)$ and the actual low
absolute sum and TV are exactly

$$
J_w=\operatorname{tr}G-2q\,c^TGc,\qquad
T_w=T_{\rm flat}-q\,c^TGc.
\tag{JR.181}
$$

Definition 53.3 gives twelve actual labels, all complex/reference/
separately labelled Borel identities and the original jointly counted
cost and $E_*$. In particular this is an attained feasible lower value,
not an upper certificate for the unrestricted optimum.

Here is a directed-domain arithmetic specification for all strict
comparisons, including the narrow margin. Use the complete CG box
$\mathcal B_{\rm CG}$ in Convention 50.1, with every one of its nine
independent coordinates. Reconstruct $N_{\rm src},S_0,S_{01},S_{02}$ by
(CG.112)–(CG.113), their adjugates by (CG.116), and their positive-pivot
factors by (CG.134). Then, without imposing a root identity on the box,

$$
\begin{gathered}
\theta=ab/(h_0h_1),\quad\omega=cd/(h_0h_2),\quad
\delta=\theta+\omega,\quad\chi=\omega/\delta,\\
g_0=\delta\,22(h_0^2-h_1^2)/128,\quad
g_1=22(b^2-a^2)/128,\quad g_2=22d^2/128,\\
x=s_0(h_0a+h_1b)(\sqrt{999}-\sqrt{295})/128,\\
y=s_0(h_0c+h_2d)(\sqrt{27}-\sqrt5)/16,\quad
z=ac(\sqrt{37}-\sqrt{59})/16.
\end{gathered}
\tag{JR.182}
$$

The source amplitudes $a,b,c,d$ in this display are distinct from the
witness vectors $b,c$ in (JR.178). The resulting outward rational bounds
are

| Quantity | Lower endpoint | Upper endpoint |
| --- | --- | --- |
| $\chi$ | $.122286669157798516$ | $.122286669157798517$ |
| $g_0$ | $.001269341241543639$ | $.001269341241543640$ |
| $g_1$ | $.002922245046832447$ | $.002922245046832448$ |
| $g_2$ | $.001677196665043113$ | $.001677196665043114$ |
| $x$ | $.002370558001558581$ | $.002370558001558582$ |
| $y$ | $.002208011237702434$ | $.002208011237702435$ |
| $z$ | $-.000101655515601015$ | $-.000101655515601014$ |

For an explicit rational implementation of directed evaluation, use
$D=2^{224}$ and enclose a rational $a$ by
$[\lfloor Da\rfloor/D,\lceil Da\rceil/D]$.
Addition and negation use their exact endpoint formulas. Products and
quotients use the minimum and maximum of the four endpoint products or
quotients, rounded outwards to multiples of $1/D$; every divided interval
excludes zero. For $[a/D,b/D]\geq0$, use square-root endpoints
$\lfloor\sqrt{aD}\rfloor/D$ and $\lceil\sqrt{bD}\rceil/D$.
For a square use lower endpoint zero when the interval crosses zero;
otherwise use the smaller endpoint square, and always the larger for
the upper endpoint. Absolute values are enclosed in the same way.
An adjugate entry is its signed transposed minor, with each two-dimensional
determinant evaluated as $ad-bc$. These rules also give the source signs,
the cap derivative in (JR.154), and the endpoint coefficient bounds.

For the whole contrast domain, use the 400 closed rational cells

$$
I_i=\left[\frac{996999}{10^6}+\frac{i}{200\cdot10^6},
\frac{996999}{10^6}+\frac{i+1}{200\cdot10^6}\right],
\qquad i=0,\ldots,399.
\tag{JR.183}
$$

On each cell evaluate (JR.176)–(JR.180) in their displayed order, using
the full reconstructed source intervals, retaining all four sign pairs.
Taking lower minima and upper maxima over these cells gives the following
strict rational comparisons; all terminating decimals are exact rationals.

| Quantity over the entire $I$ | Strict lower bound | Strict upper bound |
| --- | --- | --- |
| $J_{-,-}$ | $0$ | $.006486135$ |
| $J_{-,+}$ | $0$ | $.006109040$ |
| $J_{+,-}$ | $0$ | $.008128902$ |
| $J_{+,+}$ | $0$ | $.007486052$ |
| $J_w$ | $.008135718$ | $.009$ |
| $q$ | $.3246208$ | $.3246265$ |
| $p$ | $.2028518$ | $.2028597$ |
| $\rho$ | $.0850833$ | $.0851075$ |
| $\mathcal D$ | $.0009779$ | $.0009905$ |
| $d=1-pN$ | $.0589484$ | $.0589844$ |
| $w_1$ | $-1.451188$ | $-1.450895$ |
| $w_0-|w_2|/\sqrt\beta$ | $1.2300$ | $1.2321$ |
| $b^TGb$ | $.012046$ | $.012047$ |
| $c^TGc$ | $-.003492$ | $-.0034916$ |

All radicals, $X,Y,Z$, $X+Y$, $m$, $n^2+m^2$, $1+t^2$,
$\mathcal D$, and $d$ have positive lower endpoints in this evaluation;
$m>1/10$ in all four branches. These are evaluations over complete
closed cells and the entire source box, not midpoint values or a grid
of samples. The four-frame upper bound and witness lower bound give

$$
\frac{J_w-\max_{\sigma,\eta}J_{\sigma\eta}}2
>\frac{.008135718-.008128902}2
=.000003408>\frac{17}{5000000}.
\tag{JR.184}
$$

Since every hypothetical optimal three-atom representation at this
same saturated $\tau$ occurs in the four-frame list, it has strictly
smaller possible TV than the feasible actual witness. This contradicts
optimality. Conversely a reduced triple of rank sum at most three
admits at most three null atoms by (JR.60), so the rank-sum conclusion
follows as well. Finally (JR.99)–(JR.112) and the cap formula give
$\bar\tau<.993781<\inf I<\sup I<.997877<\tau_3$.
Thus three atoms remain feasible on $I$ but cannot optimize there;
feasibility and optimality have different boundaries. $\square$

## 57. Mathematical attribution and the remaining original continuation

**Convention 57.1 (scope of the new conclusions).** The exact initial
branch (JR.144), the matching endpoint estimates (JR.156) with every-
multiplier asymptotic (JR.172), and the uniform pre-cap comparison
(JR.184) are source-specific repository derivations. The spectral
plateau, original reduction, sharp cost and finite image/null mechanisms
are reused at their stated hypotheses; they are not new results of these
sections. The equality S-lemma is used only in the exact version and
hypotheses specified after (JR.148). The explicit moment, determinant,
remainder and secant arguments supply the additional conclusions; generic
quadrature, POVM extremality or singular-SDP error bounds are not used to
supply their source-specific values. No worldwide novelty claim is made.

The least active discriminant zero is a certificate boundary, not a
proved first support transition. Which factor first vanishes, the
contact/rank geometry beyond it, a matching solution throughout the
remaining residual interval, and lawful native realization remain
unresolved. The four-atom endpoint family is asymptotically optimal;
the pre-cap four-atom family is a strict trial witness. Neither is a
proved global four-atom optimizer. Real atom counts and aggregate ranks
impose no unproved minimum on physical labels with multi-Kraus encoders.
The separate selected-nonreal-input fixed-channel/full-effect QO law
supplies no value, optimizer or exponent transfer to this original
contrast-inequality problem. Scattering-delay clocks likewise supply
no common-instrument clock correspondence.

These are ordinary conditional mathematical results, without Lean/kernel
certification or native execution. The unknown specimen's lawful access,
D/T/S calibration, coherent storage of all jointly accessible shares,
controlled decoding, one aligned clock, actual FIRST absorbing failure
with no subsequent positive-carrier action, and terminal/archive/controller/
permission semantics remain required native bridges. OriginalControl is
geometric, not an actuator; noncommuting probability-phase controls do
not justify an exhaustive Schur assumption. The full residual curve, all contact/rank transitions and a lawful
native realization remain unresolved beyond these bounded results.

## 追加锚（本行以下为增补区）

## 58. The joint height-record and decoder-clock continuation

**Convention 58.1 (same owner and unchanged original problem).**
The [height/clock continuation](FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD_HEIGHT_CLOCK.md),
§§59–68, continues this volume's original joint-record/payload problem.
It relates the actual-label height optimum to entire-fibre positive
decoders, full-output exact-time domination and conditional finite-activity
first-failure synthesis. It retains Definitions 34.1 and 41.1, the
inherited CG premises, the remaining residual/contact/rank problem and
all native acquisition and clock obligations of Definitions 40.2 and 47.2.

## 追加锚（本行以下为增补区）
