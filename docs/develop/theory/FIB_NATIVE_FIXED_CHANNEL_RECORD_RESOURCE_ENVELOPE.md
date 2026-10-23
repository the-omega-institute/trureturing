# Native fixed-channel record and resource envelope

## 1. Conditional premises, the original task and native limits

**Convention 1.1 (mathematical status and the fixed object).** This volume
studies the particular complete channel $\widehat\Phi_*$ of
[Complete Continuation Distinguishability Gap][CG], (CG.135)–(CG.142),
and [Joint Record and Quantum Payload][JR], (JR.2). It does not range over
all channels attaining the same minimax value. The isolated algebraic
point, arithmetic enclosures, exact normalization and minimax statements
of CG §§13–17 are conditional ordinary mathematical premises here. Their
nested preparation, control and calibrated-instrument suppliers retain
the conditions stated in CG. The new proofs below use those premises;
file identity, an approval, or a small residual is not a proof of them.
No arithmetic enclosure or isolated root is newly certified in this volume.

The original objective is unchanged: from one normalized specimen at an
already reached unresolved live cut, use a common history-independent
processor to approximate twelve prescribed complete continuation outputs,
with error one half of the full classical–quantum trace norm. The entire
five-mode complex algebra, every passive reference amplification, every
original failure label and exact elapsed-time measure remain part of the
contract. The resource question fixes the complete forgotten channel
$\widehat\Phi_*$ and the binary acquired law on every input. It allows
additional genuinely acquired finite labels, whose laws need not equal
JR's finer label laws.

The original native acquisition, coherent storage, controlled decoding,
permissions and clock placement are not supplied by a mathematical
factorization. Physical execution must make the first absorbing failure
occur at its recorded elapsed time, perform no later positive-carrier
operation on that branch, and deliver live output at terminal time one.
An exact random timestamp or an internal label destined for failure does
not supply that timing service. All original archives, aligned clocks,
source/epoch metadata and declared controller updates must also match.
These remain implementation obligations, including for every attainer
constructed here. No extra acquisition time is granted.

**Definition 1.2 (source parameters and the twelve actual histories).**
The original five modes have orthonormal basis
$e_0,e_1,e_2,e_3,e_4$, with index $4$ naming mode $13$. Set

$$
\begin{gathered}
c_{\rm src}=\frac14,\quad Z=\frac12,\quad
\mathfrak a=\frac{16}{256},\quad \mathfrak h=\frac{11}{256},\quad
\delta_{\rm ramp}=\frac6{256},\quad L=1,\\
|+\rangle=(e_0+e_4)/\sqrt2,\quad
|-\rangle=(e_1+e_3)/\sqrt2,\quad |2\rangle=e_2,\\
E:\mathbb C^3\longrightarrow\mathbb C^5,
\quad E=(|+\rangle,|-\rangle,|2\rangle),\quad
P=EE^\dagger,\quad Q=I_5-P,\quad V=\operatorname{ran}E.
\end{gathered}
\tag{RE.1}
$$

The supported coordinate indices $0,1,2$ henceforth mean $(+,-,2)$;
they must not be confused with the five failure-mode labels. For
$y\in\{5,16,27\}$ put

$$
\begin{aligned}
p_y&=\left(\frac y{128},\frac{64-y}{128},\frac12\right),
&a_y&=(\sqrt{p_{y0}},\sqrt{p_{y1}},\sqrt{p_{y2}})^T,\\
U_{e,n}&=\operatorname{diag}(e,n,1),
&\rho_{y,e,n}&=U_{e,n}a_ya_y^TU_{e,n}^\dagger,
\qquad e,n\in\{1,-1\}.
\end{aligned}
\tag{RE.2}
$$

These are the actual reached-cut states, embedded by $E$. Their original
parameters are

$$
x=y/256\in\{\mathfrak a-\mathfrak h,\mathfrak a,
\mathfrak a+\mathfrak h\},\qquad
e=(-1)^{\beta/\pi},\quad n=e(-1)^m,
\quad \beta\in\{0,\pi\},\quad m\in\{0,1\}.
\tag{RE.3}
$$

Thus $en=(-1)^m$. Changing $\beta$ while keeping $y,m$ fixed changes
$(e,n)$ to $(-e,-n)$. It is an original history pair, not a new ensemble.

For clarity about the credited realization, the double-wall population
path is $(k,c_{\rm src}-k,Z,c_{\rm src}-k,k)$ with
$0<k<c_{\rm src}$. Its real phase lift uses

$$
w(k)=\left(\frac{c_{\rm src}-k}{2c_{\rm src}},
-\frac{k}{2c_{\rm src}},0,-\frac{k}{2c_{\rm src}},
\frac{c_{\rm src}-k}{2c_{\rm src}}\right),\qquad
H_i(t)=\int_0^t w_i(k(u))\chi'(u)\,du.
\tag{RE.4}
$$

CG Proposition 2.2 supplies the common-preparation six-leg histories
with preparation height $1/8$, rectangle height $1/16$, real rectangle
phase $8\beta-4\pi m$, final height $x$, and residual
$(\beta,\beta-\pi m,0,\beta-\pi m,\beta)$. Original finite durations,
continuous strict-domain coordinates, finite phase variation, the
absolute-continuity or finite-piecewise-$C^1$ regularity alternative,
and the literal signed real lift are retained. The old reach masses are
$32/177,2/9,32/111$ at the three heights. They are positive earlier
branch masses, not priors or weights in this normalized-cut experiment.

The requested continuation is $k(t)=x+\delta_{\rm ramp}t$ with phase
held fixed, $0\leq t\leq1$, in the common legal relative-command domain
$(0,58/256)$. Zero duration permits only the matching zero-displacement
identity. Original denial, rejection and controller-update conventions
remain; naming a partial command grants no unknown-height sensor or new
actuator. None of the constructions below reads the old waveform,
height, winding, parity or generator word.

**Definition 1.3 (the original complete targets and error).** Define

$$
\begin{aligned}
\varsigma_y&=\frac y{y+6},& f_y(t)&=\frac{6y}{(y+6t)^2},\\
(B_y)_{ij}&=\sqrt{d_{yi}d_{yj}},&
d_y&=\left(\frac y{128},
\frac{y(58-y)}{128(y+6)},\frac{y}{2(y+6)}\right),\\
w&=(0,1/4,1/2,1/4,0),&P_f&=|f\rangle\langle f|.
\end{aligned}
\tag{RE.5}
$$

The target for $(y,e,n)$ has live block
$EU_{e,n}B_yU_{e,n}^\dagger E^\dagger$ and, separately at each
original label $\ell=0,1,2,3,4$, measure
$w_\ell f_y(t)dt\,P_f$. Time is exact $t\in[0,1]$, equivalently
absolute time $6+t$. Labels $1,3$ remain separate even though their
densities agree; labels $0,13$ remain named with zero density.
The target is normalized since $\operatorname{tr}B_y=\varsigma_y$ and
$\int_0^1f_y=1-\varsigma_y$.

A common CPTP processor has only the specimen and fixed common metadata,
blanks and independent ancillas. No history index, source callback,
helper specimen, returned uncounted environment or source-dependent
installed programme is available. All outcomes, including acquisition
abort, unexecuted rejection, wrong support and other zero-target sectors,
enter the norm. If $\Omega_h$ denotes the entire target, the original
quantity is

$$
\mathcal E(\Phi)=\max_{h=(y,e,n)}
\frac12\|\Phi(E\rho_hE^\dagger)-\Omega_h\|_{1,\mathrm{cq}},
\qquad \mathcal E_* =\inf_{\Phi\ \mathrm{common\ CPTP}}\mathcal E(\Phi).
\tag{RE.6}
$$

The cq norm is the live trace norm plus the sum of the variation trace
norms of all separately labelled output measures. A common dominating
scalar measure handles atoms and singular continuous parts. It is not
merely the distance between survival probabilities. No new acquisition
outcome is conditioned upon or divided by its probability.

## 2. Exact coefficient dictionary and inherited results

**Definition 2.1 (the credited algebraic point).** The following gives
an exact specification of the source constants, rather than replacing
them by decimal fits. In this definition only, let
$\mathbf x=(\lambda,\alpha_1,\alpha_2,\beta_1,\beta_2,z)$ and
$\eta=(\eta_0,\eta_1,\eta_2)$. The coordinates $\beta_1,\beta_2$
are algebraic variables, not the history phase $\beta$. Put

$$
\begin{aligned}
v_5&=(\alpha_1,\alpha_2,-1)^T,&
v_{27}&=(\beta_1,\beta_2,1)^T,\\
R_y^{\rm src}&=v_yv_y^T/(v_y^Tv_y),&
A_5^{\rm src}&=\lambda R_5^{\rm src},\quad
A_{27}^{\rm src}=(1-\lambda)R_{27}^{\rm src},\\
\zeta&=(z,59\lambda/128,\lambda/2),&
N&=A_5^{\rm src}\odot(a_5a_5^T)
 +A_{27}^{\rm src}\odot(a_{27}a_{27}^T),\\
S_0^{\rm src}&=\operatorname{diag}\zeta-N,&
S_{ij}^{\rm src}&=
\begin{pmatrix}
\zeta_j-\sum_{y=5,27}(A_y^{\rm src})_{ii}p_{yj}&-N_{ij}\\
-N_{ij}&\zeta_i-\sum_{y=5,27}(A_y^{\rm src})_{jj}p_{yi}
\end{pmatrix}\quad(i<j),\\
F^{\rm src}(\mathbf x)&=\sum_{y=5,27}\operatorname{tr}(A_y^{\rm src}B_y)
-\sum_i\zeta_i+6\lambda/11,&
\mathbf g&=(1000\det S_0^{\rm src},\det S_{01}^{\rm src},
\det S_{02}^{\rm src}),\\
\mathcal L^{\rm src}(\mathbf x,\eta)&=F^{\rm src}(\mathbf x)
+\eta\cdot\mathbf g(\mathbf x),&
\Psi&=(\nabla_{\mathbf x}\mathcal L^{\rm src},\mathbf g).
\end{aligned}
\tag{RE.7}
$$

Here $\odot$ is entrywise product and the radicals in (RE.2), (RE.5)
are positive. The source premise is that $\Psi$ has a unique zero
$u_*=(\mathbf x_*,\eta_*)$ in the product of radius-$10^{-24}$ closed
intervals centred at these exact rational numbers:

| Coordinate | Rational centre |
| --- | --- |
| $\lambda$ | $0.479508042205945691075728241615$ |
| $\alpha_1$ | $1.412018697539825943102823246594$ |
| $\alpha_2$ | $1.185897402486986028204155873343$ |
| $\beta_1$ | $0.413330945620125544606320492846$ |
| $\beta_2$ | $0.809647491041060318009094562763$ |
| $z$ | $0.066998926272600209516864472757$ |
| $\eta_0$ | $0.279795267654829218213193898783$ |
| $\eta_1$ | $0.199570407911600478528148253443$ |
| $\eta_2$ | $0.091392615490799158339482855657$ |

All following source matrices are evaluated at that point. Define

$$
\begin{aligned}
H&=1000\eta_0\operatorname{adj}S_0^{\rm src},&
Q^{01}&=\eta_1\operatorname{adj}S_{01}^{\rm src},&
Q^{02}&=\eta_2\operatorname{adj}S_{02}^{\rm src},\\
h&=He_0/\sqrt{H_{00}},&
(a,b)^T&=Q^{01}e_0/\sqrt{Q^{01}_{00}},&
(c,d)^T&=Q^{02}e_0/\sqrt{Q^{02}_{00}},\\
r_1^{\rm src}&=H_{11}+Q^{01}_{00},&
r_2^{\rm src}&=H_{22}+Q^{02}_{00},&
m_k&=1-r_k^{\rm src}\quad(k=1,2),\\
D&=\operatorname{diag}(h_0,h_1,h_2),&
T&=a|0\rangle\langle1|+b|1\rangle\langle0|,&
S&=c|0\rangle\langle2|+d|2\rangle\langle0|,\\
M&=\operatorname{diag}(0,m_1,m_2),&
\kappa&=h_0a+h_1b,&g(t)&=2/(1+t)^2.
\end{aligned}
\tag{RE.8}
$$

The $e_0$ in the first two lines is the first standard coordinate of
the relevant matrix size. The amplitude $h_0$, the dimension
$d_\alpha$, the coefficient $d$, and the ramp displacement
$\delta_{\rm ramp}$ are different quantities.

**Convention 2.2 (specific conditional premises used below).** CG
Proposition 13.2, Corollary 13.3, Theorem 15.1 and JR Proposition 29.2
supply the following facts:

$$
\begin{gathered}
H=hh^T,\quad Q^{01}=(a,b)^T(a,b),\quad Q^{02}=(c,d)^T(c,d),\\
h_0,h_1,h_2,a,b,c>0,\quad d\ne0,\quad m_1,m_2,\eta_2>0,\\
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\qquad
0<\kappa<1/4,\\
H_{01}>695/1000,\quad H_{11}<500/1000,\quad H_{22}>655/1000,\quad
\operatorname{tr}Q^{01}+\operatorname{tr}Q^{02}<36/1000,\\
h_0h_1-s^2ab>677/1000\qquad(0\leq s\leq1).
\end{gathered}
\tag{RE.9}
$$

The box also gives
$\lambda<49/100$, $\alpha_1>0$, $\alpha_2>1$,
$2/5<\beta_1<1/2$ and $0<\beta_2<5/6$. These are credited enclosure
consequences, not arithmetic newly executed here. In particular the
normalization in (RE.9) is an exact source identity, not a tolerance.

**Definition 2.3 (the fixed whole-complex channel).** On any complex
$A\in M_5(\mathbb C)$, with $A_V=E^\dagger AE$, set

$$
\begin{aligned}
\widehat\Phi_*^L(A)
 &=E(DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger)E^\dagger,\\
\widehat\Phi_{*,\ell}^f(A)(dt)
 &=g(t)\left[w_\ell\operatorname{tr}(MA_V)
 +\mathbf1_{\ell=2}\operatorname{tr}(QA)\right]dt\,P_f.
\end{aligned}
\tag{RE.10}
$$

Every additional output-sector map is zero. Both compressing to $V$
and the $Q$ trace kill all $V$–$V^\perp$ cross operators. The five-mode
completion, including this cross-support action, is part of the fixed
channel. Since $g\geq0$, $\int_0^1g=1$ and $\sum_\ell w_\ell=1$,
Kraus conjugations and positive trace functionals together with (RE.9)
prove CP and total TP for (RE.10), at every reference amplification.
The conditional reference operators of the trace branches must be kept;
they are not replaced by unconditional reference marginals. Fixed common
metadata are carried identically in every output sector.

**Convention 2.4 (what is already credited).** CG §§1–7 give the
coherent lower witness and its strict improvement over $1/22$; §§8–12
give common-channel attainment, a strict gap above that witness and
explicit scalar-live and fixed-filter feasible channels. CG §§13–16
conditionally identify the exact complete-output minimax value and the
particular channel (RE.10):

$$
\mathcal E(\widehat\Phi_*)=\mathcal E_*=F^{\rm src}(\mathbf x_*),
\qquad
0.14817810291080132013<\mathcal E_*<0.14817810291080132014.
\tag{RE.11}
$$

This does not assert whole-channel uniqueness. CG §17 identifies the
sign-averaged live Choi matrix of every optimizer; §§18–20 give the
strict zero-transfer subclass gap, same-effects/different-successor pair
and conditional native synthesis interface. They do not identify the
native operation menu with a Schur subclass.

CG §§21–25 already give the joint acquisition model, the Schmidt-number
three obstruction, a nonsharp positive acquired-high mass on every
supported input, and an unmixed sufficient factorization. In the
unnormalized output-input Choi convention, let

$$
J_*=|D\rangle\!\rangle\langle\!\langle D|
 +|T\rangle\!\rangle\langle\!\langle T|
 +|S\rangle\!\rangle\langle\!\langle S|,\quad
W_3=|\Omega\rangle\langle\Omega|-2I_9,\quad
|\Omega\rangle=\sum_{i=0}^2|ii\rangle,
\quad \delta_*=\operatorname{tr}(W_3J_*)>19/10.
\tag{RE.12}
$$

CG §§26–28 further supply a finite positive source constant
$C_{\rm CG}$, exactly defined in (CG.204), such that for
$0\leq\epsilon\leq1$,

$$
\begin{aligned}
\mathcal E(\Phi)\leq\mathcal E_*+\epsilon
&\Longrightarrow
\|\overline J_\Phi-J_*\|_1\leq C_{\rm CG}\sqrt\epsilon,\\
p_H^{\rm acq}(\rho)\geq p_H^L(\rho)
&\geq\frac{[\max\{\delta_*-2C_{\rm CG}\sqrt\epsilon,0\}]^2}{24}
\quad(\operatorname{tr}\rho=1).
\end{aligned}
\tag{RE.13}
$$

Under the same near-optimal hypothesis, the second line requires an
actual fully counted factorization;
$\overline J$ is the mathematical four-sign average. CG (CG.225)
also supplies the penalties $\delta_*^2/(4C_{\rm CG}^2)$ for live
Schmidt number at most two, $\tau_{ij}^2/C_{\rm CG}^2$ for a missing
one of its four positive transfers, and
$[\max\{\delta_*-\sqrt{24p_H^L(\rho)},0\}]^2/(4C_{\rm CG}^2)$
for a given resource probability, also with acquired mass substituted.
Here $\tau_{ij}=\langle ij|J_*|ij\rangle$ for
$ij\in\{01,10,02,20\}$.
Those are inherited nonsharp bounds, with their stated source premises;
no constant in them is improved here.

JR §§29–31 construct a finite family with binary coefficient $s\kappa$
and high-acquisition effect $D^\dagger D+s^2T^\dagger T$. JR §32
proves the sharp fixed-channel ceiling $|\gamma|\leq\kappa$, including
its original-winding correct-report bounds. JR §33 expressly leaves
universal resource sharpness and native supply unresolved. Its exact
family curve is not stated there to minimize over every factorization.
The results below address that additional universal question, while
preserving all of these credited results and their conditional scope.

## 3. The observed record and the fully counted factorization class

**Definition 3.1 (finite acquisition and full decoding).** A design
$\mathfrak F$ consists of an actually supplied finite classical output
alphabet $A$, common CP encoders
$\mathcal C_\alpha:M_5\to M_{d_\alpha}$, and common full-output TP
CP decoders $\mathcal R_\alpha$, with

$$
\sum_{\alpha\in A}\mathcal C_\alpha^\dagger(I_{d_\alpha})=I_5,
\qquad
\sum_{\alpha\in A}\mathcal R_\alpha\mathcal C_\alpha
=\widehat\Phi_*.
\tag{RE.14}
$$

Equality means equality on all complex matrices and each Borel time
set in every output sector. Each $d_\alpha$ is a positive finite integer.
The label $\alpha$ is generated by the acquisition instrument, not
furnished as a source label. The binary observed component is
$r(\alpha)\in\{+1,-1\}$. A finite classical postprocessing coin may
be absorbed into $\alpha$. All finer labels are counted and may control
the decoder. Only their binary component has a prescribed law.

The quantum block $M_{d_\alpha}$ counts jointly every system accessible
to later execution that can influence output: the retained specimen,
memory, controller, environment, returned system and any accessible
entanglement share. There is no other quantum bypass or later callback.
Independent later blank ancillas are free; a receiver share of earlier
entanglement is not a blank. A permanently inaccessible reference may be
arbitrary and entangled, but neither map may use it. All identities tensor
with its identity. An instrument's other dilation systems must be
permanently inaccessible before this cut if not included in the block.
A coherent branch sum without an actual classical record remains one
quantum payload. No algebraic Kraus label alone licenses a hardware flag.

Only the total encoder is TP. Each branch is CP/TNI by its positive
effect and (RE.14). Each decoder is TP on its entire fibre, including
failure and other outcomes; its supported live compression is merely
TNI. Branch states and probabilities remain unnormalized. This volume's
new universal statements concern exactly this finite model, not a new
countable, integral or unrestricted infinite-dimensional extension.

**Definition 3.2 (same binary law and resource).** Fix a public
$s\in[0,1]$ before the specimen arrives. With
$X_{01}=|0\rangle\langle1|+|1\rangle\langle0|$, the required effects
on the complete five-mode input are

$$
F_r(s)=\frac{I_5+r s\kappa E X_{01}E^\dagger}{2}.
\tag{RE.15}
$$

Thus the scalar record functional on a general complex matrix is

$$
\operatorname{tr}(F_r(s)A)=\frac{\operatorname{tr}A}{2}
+\frac{r s\kappa}{2}\bigl((A_V)_{01}+(A_V)_{10}\bigr).
\tag{RE.16}
$$

For positive $A$ its second term is
$r s\kappa\operatorname{Re}(A_V)_{01}$. On the normalized original
states it is the probability

$$
\Pr_{y,e,n}(r)=\frac12+r s\kappa en\,q_y,
\qquad q_y=\frac{\sqrt{y(64-y)}}{128}.
\tag{RE.17}
$$

There is no history prior in this formula. Binary relabeling realizes
$\gamma=-s\kappa$; in particular the two ceilings $\gamma=\pm\kappa$
are equivalent. JR Theorem 32.2 rules out $|\gamma|>\kappa$ for this
fixed channel. This is a compatibility ceiling, not certain winding
readout: the opposite-parity binary laws at a height have variation
$2s\kappa q_y<1/8$.

For any positive input $\sigma$, define

$$
\begin{aligned}
p_H^{\rm acq}(\sigma;\mathfrak F)
 &=\sum_{d_\alpha\geq3}\operatorname{tr}\mathcal C_\alpha(\sigma),\\
p_H^L(\sigma;\mathfrak F)
 &=\sum_{d_\alpha\geq3}
\operatorname{tr}\bigl(\mathcal R_\alpha^L\mathcal C_\alpha(\sigma)\bigr).
\end{aligned}
\tag{RE.18}
$$

They are probabilities for normalized inputs and homogeneous masses
otherwise. TP of the full decoder and TNI of its supported live part give

$$
p_H^{\rm acq}(\sigma;\mathfrak F)\geq
p_H^L(\sigma;\mathfrak F)\geq0.
\tag{RE.19}
$$

For a supported $\rho\in M_3$, the notation $p_H(\rho)$ means
$p_H(E\rho E^\dagger)$; equivalently, use the encoders restricted by $E$.
Inequality (RE.19) is also an inequality of input effects. No acceptance
denominator appears. The displayed constructions will have equality between these
two quantities, but arbitrary factorizations need not.

## 4. Positive coefficients and all complex low-rank directions

**Lemma 4.1 (the sign of the second transfer).** The premises imply
$d>0$. For $0\leq s\leq1$ define

$$
\Delta_s=h_0h_1-s^2ab,\qquad
R_s=\frac{h_2\Delta_s}{h_1cd}.
\tag{RE.20}
$$

Then $\Delta_s>677/1000$ and $R_s>677/18>1$.

Proof. From (RE.7),

$$
N_{02}=-\frac{\lambda\alpha_1}{1+\alpha_1^2+\alpha_2^2}
\frac{\sqrt5}{16}
+\frac{(1-\lambda)\beta_1}{1+\beta_1^2+\beta_2^2}
\frac{\sqrt{27}}{16}.
\tag{RE.21}
$$

Since $\alpha_2>1$ and $\alpha_1>0$, the elementary inequality
$\alpha_1^2+2\geq2\sqrt2\alpha_1$ gives

$$
\frac{\alpha_1}{1+\alpha_1^2+\alpha_2^2}
<\frac1{2\sqrt2}<\frac38.
\tag{RE.22}
$$

The positive box bounds give

$$
\frac{\beta_1}{1+\beta_1^2+\beta_2^2}
>\frac{2/5}{1+1/4+25/36}=\frac{36}{175}>\frac15.
\tag{RE.23}
$$

Positive squaring shows $\sqrt5/16<3/20$ and
$\sqrt{27}/16>3/10$. The negative term in (RE.21) has magnitude
less than $441/16000$; its positive term exceeds $153/5000$.
Consequently $N_{02}>243/80000>0$. The two-dimensional adjugate in
(RE.8) has off-diagonal entry $\eta_2N_{02}$, so
$cd=Q^{02}_{01}=\eta_2N_{02}>0$. Since $c>0$, this proves $d>0$.
This is a symbolic consequence of the credited box, not a new numerical
calculation of that box.

The strict bounds on $H_{22}=h_2^2$ and $H_{11}=h_1^2$ imply
$h_2>h_1>0$. Also
$0<2cd\leq c^2+d^2=\operatorname{tr}Q^{02}<36/1000$.
Combine these inequalities with (RE.9) in (RE.20) to obtain the stated
strict lower bound on $R_s$. $\square$

**Lemma 4.2 (determinant, exact ranks and fixed range maps).** Let
$K_{r,s}=D+rsT$, where $r=\pm1$ and $0\leq s\leq1$. For arbitrary
complex $u,v$,

$$
\det(uK_{r,s}+vS)=u h_1cd\,(R_su^2-v^2).
\tag{RE.24}
$$

The matrix $K_{r,s}$ is invertible. Each of $S$ and
$K_{r,s}\pm\sqrt{R_s}S$ has rank exactly two. The complete set of
nonzero rank-at-most-two matrices in the complex span of $K_{r,s},S$
is the union of the three complex lines generated by these matrices.

Proof. In the fixed supported coordinates the matrix is

$$
u K_{r,s}+vS=
\begin{pmatrix}
u h_0&u rs a&v c\\
u rs b&u h_1&0\\
v d&0&u h_2
\end{pmatrix}.
\tag{RE.25}
$$

First-row expansion gives
$u^3h_2(h_0h_1-s^2ab)-uv^2h_1cd$, which is (RE.24).
For $u=1,v=0$ the determinant is positive. For $u=0,v\ne0$,
the two nonzero entries of $S$ occupy independent rows and columns,
so its rank is two. For $u\ne0$, a vanishing determinant is equivalent
over $\mathbb C$ to $v/u=\pm\sqrt{R_s}$. The upper-left two-dimensional
minor of $K_{r,s}\pm\sqrt{R_s}S$ is $\Delta_s>0$, so its rank is
exactly two. These arguments exclude rank-one directions as well as
any additional complex low-rank line.

Here is a common explicit range isometry for each mixed line. For
$\epsilon=\pm1$ let

$$
z_1=(h_0,rsb,\epsilon\sqrt{R_s}d)^T,\qquad
z_2=(rsa,h_1,0)^T,
\quad u_1=z_1/\|z_1\|,
\quad u_2=\frac{z_2-u_1(u_1^\dagger z_2)}
{\|z_2-u_1(u_1^\dagger z_2)\|},
\quad U_{r,\epsilon}^{(s)}=(u_1,u_2).
\tag{RE.26}
$$

Their first two coordinates have determinant $\Delta_s>0$, so both
normalizing denominators are nonzero. They are the first two columns
of $K_{r,s}+\epsilon\sqrt{R_s}S$ and span its rank-two range.
Thus $U^\dagger U=I_2$ and $UU^\dagger$ acts identically on that
matrix's range. All these isometries are fixed by the public design,
independently of any input. For $T$ use the range isometry
$V_T=(|1\rangle,|0\rangle)$. $\square$

## 5. A strict replacement of the entire JR family

**Definition 5.1 (the finite common instrument).** Fix $s\in[0,1]$
and write $R_s$ as in (RE.20). Define

$$
B_{r,\epsilon}^{(s)}
=\frac{K_{r,s}+\epsilon\sqrt{R_s}S}{2\sqrt{R_s}}.
\tag{RE.27}
$$

On supported inputs prescribe the following actual encoder branches;
each displayed matrix acts by $A\mapsto CAC^\dagger$:

| Acquired label | Joint fibre dimension | Encoder Kraus matrix |
| --- | --- | --- |
| $(r,H)$ | $3$ | $\sqrt{(R_s-1)/(2R_s)}K_{r,s}$ |
| $(r,R_\epsilon)$ | $2$ | $(U_{r,\epsilon}^{(s)})^\dagger B_{r,\epsilon}^{(s)}$ |
| $(r,T)$ | $2$ | $\sqrt{(1-s^2)/2}\,V_T^\dagger T$ |
| $(r,f_k)$, $k=1,2$ | $1$ | $\sqrt{m_k/2}\langle k|$ |

There are two $R_\epsilon$ branches for each $r$. The zero $T$ branch
is removed when $s=1$. Decode the $H$ fibre into live output by $E$;
decode $R_\epsilon$ by $EU_{r,\epsilon}^{(s)}$ and $T$ by $EV_T$.
Each live decoder is the isometric CP map $X\mapsto VXV^\dagger$
on its entire fibre. Each $f_k$ decoder sends scalar $z$ to
$z w_\ell g(t)dt\,P_f$ in all five original failure sectors.
It has no live output.

For five-mode inputs replace every supported encoder matrix $C$ by
$CE^\dagger$. For each $r$ add a scalar branch

$$
\mathcal C_{r,\perp}(A)=\frac12\operatorname{tr}(QA),
\tag{RE.28}
$$

decoded to $z g(t)dt\,P_f$ solely at original failure label $2$.
For example, the CP trace in (RE.28) has rows
$\langle(e_0-e_4)/\sqrt2|/\sqrt2$ and
$\langle(e_1-e_3)/\sqrt2|/\sqrt2$.
Their Kraus multiplicity is discarded, not a retained quantum system.
The branch's joint quantum fibre is scalar.

The acquisition output is the actual classical tag in this table and
only its stated fibre. The prescription includes permanently discarding
all other input-dependent dilation systems before the cut. A native
claim would additionally have to supply the lawful operations enacting
this instrument; no such claim is made by specifying its CP maps.

**Theorem 5.2 (complete channel, effects and references).** Definition
5.1 is a finite factorization with jointly normalized encoders and full
TP decoders. It has exactly (RE.15) and, more strongly, the same
unnormalized binary-labelled complete CP output maps as the JR family:

$$
\begin{aligned}
\Psi_{r,s}^L(A)
 &=\frac12E\left[K_{r,s}A_VK_{r,s}^\dagger
 +(1-s^2)TA_VT^\dagger+SA_VS^\dagger\right]E^\dagger,\\
\Psi_{r,s,\ell}^f(A)(dt)
 &=\frac12g(t)\left[w_\ell\operatorname{tr}(MA_V)
 +\mathbf1_{\ell=2}\operatorname{tr}(QA)\right]dt\,P_f.
\end{aligned}
\tag{RE.29}
$$

Their sum is $\widehat\Phi_*$. These identities hold on all complex
matrices, at every passive reference amplification, for each original
label and each Borel time set, with zero additional sectors and the
same zero cross-support action.

Proof. On any complex supported $A$, cancellation of the two opposite
cross terms gives

$$
\sum_{\epsilon=\pm1}B_{r,\epsilon}^{(s)}A
(B_{r,\epsilon}^{(s)})^\dagger
=\frac1{2R_s}K_{r,s}AK_{r,s}^\dagger+\frac12SAS^\dagger.
\tag{RE.30}
$$

Compression into the range and its isometric decoding multiply to
$B_{r,\epsilon}^{(s)}$ itself, by (RE.26). Adding the $H$ branch to
(RE.30) yields $K_{r,s}AK_{r,s}^\dagger/2+SAS^\dagger/2$.
Adding the residual $T$ branch proves the supported live line of
(RE.29). The scalar rows give its failure line directly. All are
matrix identities; no assumption $A_{ij}=A_{ji}$ has been used.

The exact supported encoder effects, before summing labels, are

$$
\begin{aligned}
G_{r,H}&=\frac{R_s-1}{2R_s}K_{r,s}^\dagger K_{r,s},\\
G_{r,R_\epsilon}&=\frac{K_{r,s}^\dagger K_{r,s}}{4R_s}
 +\frac{S^\dagger S}{4}
 +\frac{\epsilon}{4\sqrt{R_s}}
 (K_{r,s}^\dagger S+S^\dagger K_{r,s}),\\
G_{r,T}&=(1-s^2)T^\dagger T/2,
\qquad G_{r,f_k}=m_k|k\rangle\langle k|/2.
\end{aligned}
\tag{RE.31}
$$

Each is positive because it is $C^\dagger C$. Since
$D^\dagger T+T^\dagger D=\kappa X_{01}$, their sum at fixed $r$ is
$(I_3+rs\kappa X_{01})/2$. Summing $r$ gives $I_3$ by (RE.9).
After compression their total is $P$, and the two (RE.28) effects
add to $Q$. Thus the entire effect is $I_5$; in particular every
individual encoder is TNI. Each live decoder is TP since its isometry
has $V^\dagger V=I$ on the entire fibre. Each scalar decoder is TP
since $\sum_\ell w_\ell=\int_0^1g=1$. The complement decoder uses
the same normalized time law at just one existing label. This proves
both full-decoder normalization and the binary effect (RE.15).

Summing (RE.29) over $r$ cancels $D$–$T$ cross terms and gives exactly
(RE.10). On $V$–$V^\perp$ cross matrix units, all $CE^\dagger$
conjugations and the $Q$ trace are zero, as required. There is no
complement live contribution.

For completeness, on a joint complex input $X$ with arbitrary passive
reference $R$, every Kraus matrix in these calculations is replaced by
$C\otimes I_R$, and every live isometry by $V\otimes I_R$.
The cancellation (RE.30) is unchanged. A scalar row outputs the reference
operator $(C\otimes I_R)X(C^\dagger\otimes I_R)$; a complement
branch outputs $\operatorname{Tr}_5[(Q\otimes I_R)X]/2$.
The failure decoder tensors this operator with $P_f$ and the stated
labelled measure. Its sum over scalar rows gives the conditional
reference operator associated with $M/2$ or $Q/2$. It never substitutes
an unconditional reference state. Therefore the same identities hold
at every reference size and for entangled, singular or subnormalized
positive inputs, as well as complex matrix units by linearity.

Integrating $g(t)dt$ over any Borel set proves equality of the entire
CP measure, with each label retained. The constructed law has no
endpoint atoms or singular addition; $g$ is finite at both endpoints.
Both zero-weight modes and every extra sector have zero maps, rather
than uncounted events. Consequently its canonical error on all twelve
original histories is the inherited (RE.11). This is not an error
claim for a different task that reveals the extra internal labels.
$\square$

**Theorem 5.3 (exact high mass and strict all-$s$ improvement).** The only
high branches of Definition 5.1 are $(r,H)$. Its acquired and supported
live high effects agree and equal, on $V$,

$$
G_s=\left(1-\frac1{R_s}\right)
(D^\dagger D+s^2T^\dagger T).
\tag{RE.32}
$$

On five modes the effect is $EG_sE^\dagger$, and
$p_H^{\rm acq}(\sigma)=\operatorname{tr}(G_sE^\dagger\sigma E)$.
For every $s\in[0,1]$ it is strictly smaller than JR's acquired high
mass on every positive input with nonzero supported compression.

Proof. Lemma 4.2 and $R_s>1$ make each $H$ encoder invertible into
its three-dimensional fibre. Every nonzero mixed branch has rank two
and uses precisely its two-dimensional range; the residual $T$ branch
has rank two when present. Failure and complement fibres are scalar.
Per $r$ the joint dimensions are therefore $3,2,2,2,1,1,1$ in the
five-mode construction, with the residual $T$ omitted at $s=1$.
There is no additional retained specimen or controller share.
All high decoders output their entire input live, so acquisition and
supported live mass agree on those branches. Summing the first line of
(RE.31) over $r$ gives (RE.32).

JR's effect is $G_s^{\rm JR}=D^\dagger D+s^2T^\dagger T$.
The difference $G_s^{\rm JR}-G_s=G_s^{\rm JR}/R_s$ is positive
definite on $V$, since $D$ is invertible. Its trace against any nonzero
positive supported compression is strictly positive. On an original
history the new value is exactly

$$
\left(1-\frac1{R_s}\right)
\left[\sum_iH_{ii}p_{yi}
+s^2\left(b^2\frac y{128}+a^2\frac{64-y}{128}\right)\right].
\tag{RE.33}
$$

It is independent of both signs, and the difference from JR's value
is the bracket divided by $R_s$. On $V^\perp$ both high effects
vanish. For arbitrary positive five-mode inputs the compression is used
without normalizing its trace. The same scalar probabilities for a
joint input use its reduced specimen density, while Theorem 5.2 retains
the full conditional reference states. Relabeling $r$ proves the same
statement for all $\gamma\in[-\kappa,0]$ as for
$\gamma\in[0,\kappa]$. $\square$

## 6. Universal structure at either binary-record ceiling

**Theorem 6.1 (saturation forces the binary live maps).** Set
$s=1$, $R=R_1$ and $K_r=D+rT$. For every finite factorization of
Definition 3.1 satisfying (RE.15), its two supported live Choi matrices
are necessarily

$$
J_r=\frac12\left(|K_r\rangle\!\rangle\langle\!\langle K_r|
+|S\rangle\!\rangle\langle\!\langle S|\right).
\tag{RE.34}
$$

Each aggregate supported binary failure effect is $M/2$. No assertion
of unique binary-labelled failure-time CP measures is made. In
particular the universal results below include every compatible
exact-time splitting, every finite classical refinement, arbitrary
complex CP encoders and arbitrary full TP decoders, with arbitrary
finite jointly counted quantum fibres. At $\gamma=-\kappa$ the same
statements hold after exchanging the two binary labels.

Proof. Use the unnormalized output-input vectorization
$|L\rangle\!\rangle=\sum_{i,j}L_{ij}|i\rangle|j\rangle$.
The plus supported live map is a CP summand of the fixed live map, so
$0\preceq J_+\preceq J_*$. The three nonzero vectors
$|D\rangle\!\rangle,|T\rangle\!\rangle,|S\rangle\!\rangle$
are orthogonal and independent because their matrix supports are
disjoint. They are not normalized. Let $V$ have these columns in that
order and $G=V^\dagger V\succ0$. A positive dominated matrix kills
$\ker J_*$: its nonnegative quadratic form is zero there, which forces
its square root to kill those vectors. Its range is thus in
$\operatorname{ran}V$. It follows that

$$
J_+=VZV^\dagger,\qquad
Z=G^{-1}V^\dagger J_+VG^{-1},\qquad 0\preceq Z\preceq I_3.
\tag{RE.35}
$$

To verify the last inequalities with the correct normalization, apply
$0\preceq J_+\preceq VV^\dagger$ to $VG^{-1}z$ for each coefficient
vector $z$. This retains the Gram matrix and does not treat the Choi
columns as an orthonormal basis.

The total plus failure effect on the supported input satisfies
$0\preceq F_+^f\preceq M$. Because $M|0\rangle=0$, positivity
forces $F_+^f|0\rangle=0$ and hence $(F_+^f)_{01}=0$.
This follows by taking the event of all original labels and all times;
it includes every singular measure allowed by a candidate. Zero extra
sectors have zero CP branch maps, since positive summands of a zero
output are zero. Thus they cannot contribute a missing effect.

Writing $z=Z_{DT}$, the supported plus live effect has entry

$$
(F_+^L)_{01}=zbh_1+\overline z h_0a,
\qquad \operatorname{Re}(F_+^L)_{01}=\kappa\operatorname{Re}z.
\tag{RE.36}
$$

Indeed the effect of $VZV^\dagger$ is
$\sum_{i,j}Z_{ij}K_j^\dagger K_i$, for $(K_D,K_T,K_S)=(D,T,S)$;
only the $D,T$ pair has a $01$ entry. The required full binary effect
has that real entry $\kappa/2$. Since $\kappa>0$, it forces
$\operatorname{Re}z=1/2$.

The Hermitian matrix $Y=2Z-I$ is a contraction. Its $DT$ entry has
real part one, and absolute value at most one, so it is exactly one.
The $D$ and $T$ columns each already have squared norm at least one
from this entry. The contraction bounds each norm by one. Hence every
other entry in those two columns is zero: $Z_{DD}=Z_{TT}=1/2$ and
$Z_{DS}=Z_{TS}=0$. This argument also removes imaginary mixing; it
has not assumed a real encoder.

Let $Z_{SS}=z_S$. At input coordinate $0$, failure contributes zero,
and the required plus effect has value $1/2$. It follows that

$$
\frac{h_0^2+b^2}{2}+z_Sd^2=\frac12,
\qquad h_0^2+b^2+d^2=1.
\tag{RE.37}
$$

The second equality is coordinate $0$ of (RE.9). As $d\ne0$,
$z_S=1/2$. Expanding (RE.35) now gives (RE.34) for plus, and
subtracting from $J_*$ gives minus. Their live effects, subtracted from
the required binary total effects, leave $M/2$ for each supported
failure effect.

Only integrated failure effects were needed for this necessity proof.
It has not assumed the specific half-density split in (RE.29), nor
inferred that split from its integral. The full task still requires
every exact-time measure; the conclusion permits all their compatible
splittings. $\square$

**Lemma 6.2 (exhaustive low-rank cone and the high budget).** In every
factorization of Theorem 6.1, the supported live Choi matrix arising from
low fibres $d_\alpha\leq2$ and fixed record $r$ has, in the independent
coefficient basis $(K_r,S)$, exactly the form

$$
Q_{r,L}=\begin{pmatrix}t_r&w_r\\w_r&Rt_r+z_r\end{pmatrix},
\qquad t_r,z_r\geq0,\quad w_r\in\mathbb R,
\quad |w_r|\leq\sqrt R\,t_r.
\tag{RE.38}
$$

The complementary high live matrix has coefficient matrix

$$
Q_{r,H}=\frac{I_2}{2}-Q_{r,L}
=\begin{pmatrix}u_r&-w_r\\-w_r&v_r\end{pmatrix}\succeq0,
\tag{RE.39}
$$

where, with $u_0=(R-1)/(2R)>0$,

$$
u_0\leq u_r\leq\frac12,\quad
0\leq v_r\leq Ru_r-\frac{R-1}{2},\quad
w_r^2\leq u_rv_r,\quad
|w_r|\leq\sqrt R(1/2-u_r).
\tag{RE.40}
$$

Proof. Choose finite Kraus representations for an actual encoder and
for its decoder's supported live compression. Their products have the
form $L=BC$ through the same quantum block, so
$\operatorname{rank}L\leq d_\alpha$. A low fibre therefore contributes
only rank-at-most-two Choi vectors. Each positive rank-one summand is
dominated by $J_r$, and the same positive-kernel argument as in (RE.35)
puts its vector in $\operatorname{ran}J_r$. Hence
$L=uK_r+vS$ for complex $u,v$.

Lemma 4.2 classifies all nonzero possibilities: they are scalar multiples
of $S$, $K_r+\sqrt R S$ and $K_r-\sqrt R S$. All have rank two;
a scalar quantum fibre cannot supply a nonzero supported live product.
Their positive Choi sums in coefficient coordinates are generated by

$$
\begin{pmatrix}0&0\\0&1\end{pmatrix},\qquad
\begin{pmatrix}1&\sqrt R\\\sqrt R&R\end{pmatrix},\qquad
\begin{pmatrix}1&-\sqrt R\\-\sqrt R&R\end{pmatrix}.
\tag{RE.41}
$$

A complex scalar on any of the three lines contributes its modulus
squared, so the off-diagonal coefficient is real. Taking weights
$z_r$, $(t_r+w_r/\sqrt R)/2$ and
$(t_r-w_r/\sqrt R)/2$ proves both necessity and sufficiency of
(RE.38) for this low-rank cone. No complex directions are omitted.

The actual high live sum is positive and complements the low one in
(RE.34). Since the coefficient map has an injective column map,
positivity of the physical Choi matrix is equivalent to positivity of
its coefficient matrix, again by a left inverse. Therefore (RE.39)
is positive. Here $u_r=1/2-t_r$ and
$v_r=1/2-Rt_r-z_r$. Positivity gives $u_r,v_r\geq0$ and
$w_r^2\leq u_rv_r$; $t_r,z_r\geq0$ gives the upper bounds in
(RE.40), and $v_r\geq0$ then gives $u_r\geq u_0$.
This proves the entire stated high budget for arbitrary high-fibre
operations, without assuming that they are pure or isometric.

Full decoder TP gives (RE.19) for these actual high branches. It is
essential that $B$ and $C$ factor through the entire counted future
payload: an omitted accessible entanglement share or specimen would
invalidate this rank argument. Passive references do not supply such
an accessible channel. $\square$

## 7. The exact endpoint pointwise envelope

**Definition 7.1 (positive-input functionals).** For $\rho\succeq0$
in $M_3$ define real scalars

$$
\begin{aligned}
A_r(\rho)&=\operatorname{tr}(K_r^\dagger K_r\rho),&
C(\rho)&=\operatorname{tr}(S^\dagger S\rho),&
U_r(\rho)&=\operatorname{Re}\operatorname{tr}(K_r^\dagger S\rho),\\
\eta(x)&=\frac{R-1}{2(R-x^2)},&
I_R&=[-1/\sqrt R,1/\sqrt R],\\
b_r(\rho)&=\min_{x\in I_R}\eta(x)
\bigl(A_r(\rho)+C(\rho)x^2-2U_r(\rho)x\bigr),&
B(\rho)&=b_+(\rho)+b_-(\rho).
\end{aligned}
\tag{RE.42}
$$

The denominator is positive on this closed interval since $R>1$.
For $\rho=0$ set $B(0)=0$, consistent with the displayed minimum.
The letter $B$ in this scalar envelope is distinct from the target
matrices $B_y$.

**Theorem 7.2 (universal endpoint lower bound).** For every original
finite factorization satisfying the fixed complete channel and the
ceiling binary law, and every positive supported input,

$$
p_H^{\rm acq}(\rho;\mathfrak F)\geq
p_H^L(\rho;\mathfrak F)\geq B(\rho).
\tag{RE.43}
$$

For arbitrary $\sigma\succeq0$ in $M_5$ its lower bound is
$B(E^\dagger\sigma E)$, using the unnormalized compression.

Proof. Fix $r$ and suppress it on $u,v,w$. Equations (RE.39) and
(RE.42) express its high live mass as
$uA_r+vC-2wU_r$. Since $u\geq u_0>0$, put $x=w/u$.
Positivity gives $v\geq ux^2$. Together with the upper bound on $v$
this implies

$$
u(R-x^2)\geq(R-1)/2>0,
\qquad u\geq\eta(x).
\tag{RE.44}
$$

In particular $R-x^2>0$ before any division. The low-cone bound gives
$u|x|\leq\sqrt R(1/2-u)$, or
$u\leq\sqrt R/[2(\sqrt R+|x|)]$. Combining with (RE.44) and
multiplying positive denominators yields

$$
(\sqrt R|x|-1)(|x|+\sqrt R)\leq0,
\quad\text{hence}\quad |x|\leq1/\sqrt R.
\tag{RE.45}
$$

Since $C\geq0$,

$$
\begin{aligned}
uA_r+vC-2wU_r
&\geq u(A_r+Cx^2-2U_rx)\\
&\geq\eta(x)(A_r+Cx^2-2U_rx)\geq b_r(\rho).
\end{aligned}
\tag{RE.46}
$$

The second inequality is legitimate because the bracket is
$\operatorname{tr}((K_r-xS)^\dagger(K_r-xS)\rho)\geq0$.
Summing the two records and using acquired-live domination proves
(RE.43). No trace-one, nonsingularity or preparation-prior premise
was used.

For five modes, the full fixed live Choi support has both its output
and input in the supported three-dimensional spaces. Every positive
live Choi summand inherits that support by domination, including every
actual high submap. Its live mass therefore depends only on
$E^\dagger\sigma E$. This proves the five-mode version even when
$\sigma$ has cross-support coherence. An arbitrary acquired high
effect need not itself kill those cross terms; only its dominated
supported live submap has been proved to do so. Inequality (RE.19)
is what transfers this lower bound to acquisition. $\square$

**Proposition 7.3 (finite closed minimizer and degeneracies).** For
$\rho\succeq0$, $\rho\ne0$, abbreviate its functionals in (RE.42)
and put

$$
\mathscr D_r=(A_r+RC)^2-4RU_r^2\geq0.
\tag{RE.47}
$$

The unique minimizer in each record is

$$
x_r^*(\rho)=
\begin{cases}
0,&U_r=0,\\
\operatorname{sgn}(U_r)\displaystyle\min\left\{
\frac1{\sqrt R},
\frac{2R|U_r|}{A_r+RC+\sqrt{\mathscr D_r}}\right\},&U_r\ne0.
\end{cases}
\tag{RE.48}
$$

Thus an explicit value, with no remaining optimization, is

$$
B(\rho)=\sum_{r=\pm1}\eta(x_r^*)
\bigl(A_r+C(x_r^*)^2-2U_rx_r^*\bigr).
\tag{RE.49}
$$

Set $x_r^*(0)=0$. For a zero input every $x\in I_R$ minimizes; uniqueness
is asserted only for nonzero positive inputs.

Proof. $K_r$ is invertible, so $A_r>0$ on every nonzero positive input,
including singular ones. Hilbert–Schmidt Cauchy–Schwarz applied to
$K_r\rho^{1/2}$ and $S\rho^{1/2}$ gives $U_r^2\leq A_rC$.
Consequently
$\mathscr D_r=(A_r-RC)^2+4R(A_rC-U_r^2)\geq0$.
The denominator in (RE.48) is positive since $A_r>0$.
Moreover

$$
\det(K_r-xS)=h_1cd(R-x^2)>0\quad(x\in I_R),
\tag{RE.50}
$$

so the bracket in (RE.46) is strictly positive for such inputs.

Ignoring the positive constant $(R-1)/2$, differentiating the function
$(A_r+Cx^2-2U_rx)/(R-x^2)$ gives

$$
\frac{2\bigl((A_r+RC)x-U_r(R+x^2)\bigr)}{(R-x^2)^2}.
\tag{RE.51}
$$

When $U_r=0$ its sign is the sign of $x$, giving the unique minimum at
zero; this covers $C=0$, which forces $U_r=0$. For $U_r>0$, the
value at a positive $x$ is smaller than at $-x$. The numerator's
quadratic changes sign at the smaller positive root

$$
\frac{A_r+RC-\sqrt{\mathscr D_r}}{2U_r}
=\frac{2RU_r}{A_r+RC+\sqrt{\mathscr D_r}}.
\tag{RE.52}
$$

Both roots are positive and have product $R$; the smaller is at most
$\sqrt R$, the larger at least $\sqrt R$. Since
$1/\sqrt R<\sqrt R$, the derivative is negative up to the smaller
root in the allowed positive interval and positive thereafter if that
root lies in the interval. Otherwise it remains negative up to the
endpoint. This proves the clipped expression and uniqueness, including
a root exactly at the endpoint. If $\mathscr D_r=0$, the double root
is $\sqrt R$, strictly outside the allowed interval, and the minimum
is again uniquely the endpoint. Negative $U_r$ follows by $x\mapsto-x$.
All operations remain valid for singular and subnormalized inputs.
At zero input every functional is zero and the stated convention avoids
the indeterminate fraction. $\square$

## 8. Exact complete attainers, separately for every test input

**Theorem 8.1 (a common design for each fixed pair of design constants).**
Choose any public constants $x_+,x_-\in I_R$ before receiving the
unknown input. For each record put

$$
\eta_r=\eta(x_r),\qquad t_r=1/2-\eta_r,\qquad
\ell_{r,\epsilon}=\frac{t_r+\epsilon\eta_rx_r/\sqrt R}{2}.
\tag{RE.53}
$$

There is a finite factorization of the same complete channel and
ceiling binary law whose high effect is

$$
G_{x_+,x_-}=\sum_{r=\pm1}\eta_r
(K_r-x_rS)^\dagger(K_r-x_rS).
\tag{RE.54}
$$

Its five-mode effect is $EG_{x_+,x_-}E^\dagger$ and its acquired high
mass equals its supported live high mass on every positive input.

Proof. The weights in (RE.53) are nonnegative. To see endpoint feasibility
explicitly, write $z=|x_r|\leq1/\sqrt R$. Then

$$
t_r=\frac{1-x_r^2}{2(R-x_r^2)}>0,\qquad
t_r-\frac{\eta_r|x_r|}{\sqrt R}
=\frac{(1-\sqrt R z)(1+z/\sqrt R)}{2(R-z^2)}\geq0.
\tag{RE.55}
$$

For each $r$ supply the high encoder
$\sqrt{\eta_r}(K_r-x_rS)$ into a three-dimensional fibre and two low
encoders

$$
\sqrt{\ell_{r,\epsilon}}\,
(U_{r,\epsilon}^{(1)})^\dagger(K_r+\epsilon\sqrt R S)
\quad\text{into two-dimensional fibres}.
\tag{RE.56}
$$

Their actual acquired labels are $(r,H)$ and $(r,R_\epsilon)$.
Omit any zero-weight low branch; this includes one of the two at either
endpoint $|x_r|=1/\sqrt R$. Decode high by $E$ and low by
$EU_{r,\epsilon}^{(1)}$, each as an isometric full TP decoder.
Retain the scalar rows $\sqrt{m_k/2}\langle k|$, with the whole
five-sector failure decoder of Definition 5.1. For five modes compose
these rows and matrices with $E^\dagger$, and keep the two scalar
complement branches (RE.28) and their label-$2$ decoder.
There is no residual $T$ branch at the ceiling.

In coefficient coordinates $(K_r,S)$ the low matrix is

$$
\sum_\epsilon\ell_{r,\epsilon}
\begin{pmatrix}1&\epsilon\sqrt R\\\epsilon\sqrt R&R\end{pmatrix}
=\begin{pmatrix}t_r&\eta_rx_r\\\eta_rx_r&Rt_r\end{pmatrix}.
\tag{RE.57}
$$

The high matrix is
$\eta_r\left(\begin{smallmatrix}1&-x_r\\-x_r&x_r^2\end{smallmatrix}\right)$.
Their sum is $I_2/2$, because
$t_r+\eta_r=1/2$ and $Rt_r+\eta_rx_r^2=1/2$.
Thus their binary live maps are exactly (RE.34), on all complex matrices.
The scalar failure maps are exactly half of (RE.10) for each record,
not merely a chosen split with the correct integral.

The effects consequently sum at fixed $r$ to
$(I_3+r\kappa X_{01})/2$ and in total to $I_3$; the complement branches
complete this to $I_5$. Every encoder is CP/TNI, every live decoder is
TP on its whole fibre, and the scalar decoders are TP by
$\sum w=\int g=1$. The reference, cross-support and Borel-time proofs
are the same Kraus-product identities as in Theorem 5.2: each range
compression followed by its isometry is the displayed original matrix,
scalar branches retain their conditional reference operators, and
$CE^\dagger$ and the $Q$ trace kill cross-support units. This proves
(RE.14)–(RE.16) and the full complex/reference identities without an
input restriction. No extra sector is introduced.

Equation (RE.50) makes every high matrix invertible. Each nonzero low
matrix has rank two by Lemma 4.2 and (RE.26). Other fibres are scalar;
there are no retained uncounted systems. All high branches are decoded
wholly live, so summing their encoder effects gives exactly (RE.54)
and proves acquired-live equality. These facts also cover the zero
compression and arbitrary complementary five-mode input. $\square$

**Corollary 8.2 (the exact pointwise infimum and its quantifiers).** Let
$\mathcal F_{\rm ceil}$ denote all designs of Definition 3.1 with
(RE.15) at $s=1$. For every positive five-mode test input $\tau$,

$$
\min_{\mathfrak F\in\mathcal F_{\rm ceil}}
 p_H^{\rm acq}(\tau;\mathfrak F)
=B(E^\dagger\tau E).
\tag{RE.58}
$$

The minimum is attained separately for every test input. The same
statement holds with supported live high mass as objective. At the
negative ceiling exchange the binary labels.

Proof. Theorem 7.2 gives the lower bound for every allowed factorization.
Choose the fixed constants in Theorem 8.1 to be
$x_r=x_r^*(E^\dagger\tau E)$ from (RE.48), using zero when the
compression vanishes. Equation (RE.54) then has trace (RE.49) against
that compression. This is a single common instrument, valid on every
unknown input, with its constants chosen once from the public test
input for this mathematical optimization. It never consults the actual
input during execution. At zero compression its high probability is
zero. The input may be singular or subnormalized; homogeneity preserves
the equality. For a normalized complement input the scalar complement
branches carry its entire probability. Every original test input is
included without modification.

The quantifier is
$\forall\tau\succeq0\ \exists\mathfrak F_\tau\in\mathcal F_{\rm ceil}$
attaining the bound at $\tau$. It is not
$\exists\mathfrak F\ \forall\tau$ attaining it. The opposite assertion
will fail even on two original histories. $\square$

## 9. A universal paired inequality with one common sharp design

**Theorem 9.1 (paired high-resource inequality).** Put
$W=\operatorname{diag}(-1,-1,1)$ on the supported qutrit. For every
positive supported $\rho$, and every one allowed ceiling factorization,

$$
\frac{p_H^{\rm acq}(\rho;\mathfrak F)
+p_H^{\rm acq}(W\rho W^\dagger;\mathfrak F)}{2}
\geq\left(1-\frac1R\right)
\operatorname{tr}((D^\dagger D+T^\dagger T)\rho).
\tag{RE.59}
$$

The $s=1$ construction of Definition 5.1 attains this inequality
simultaneously for every such $\rho$, with one common design.

Proof. $W$ commutes with $K_r$ and anticommutes with $S$.
Consequently $A_r,C$ are unchanged by $\rho\mapsto W\rho W^\dagger$
and $U_r$ changes sign. For the actual fixed high coefficient matrices
(RE.39), averaging the two high live evaluations cancels the cross
terms. Equations (RE.19) and (RE.40) therefore give

$$
\begin{aligned}
\frac{p_H^{\rm acq}(\rho)+p_H^{\rm acq}(W\rho W^\dagger)}2
&\geq\sum_r(u_rA_r+v_rC)\\
&\geq u_0\sum_rA_r
=\left(1-\frac1R\right)
\operatorname{tr}((D^\dagger D+T^\dagger T)\rho).
\end{aligned}
\tag{RE.60}
$$

This uses the same actual factorization on both inputs, not independently
attained values. It is an algebraic inequality between two conditional
masses and supplies no source prior or new mixture preparation.

In Theorem 8.1 set $x_+=x_-=0$. Then $\eta_r=u_0$,
$\ell_{r,\epsilon}=1/(4R)$, and the instrument is exactly Definition
5.1 at $s=1$. Its effect is

$$
G_1=\left(1-\frac1R\right)(D^\dagger D+T^\dagger T).
\tag{RE.61}
$$

This diagonal effect commutes with $W$, so its two evaluations are
identical and equal the right side of (RE.59). This proves simultaneous
attainment without discarding any failure branch or exact-time record.
The proof is homogeneous, so no normalization of $\rho$ was needed.
For arbitrary five-mode inputs a corresponding inequality follows by
using the unitary $EWE^\dagger+Q$ and unnormalized compression; there
is no positive bound asserted on the complement alone. $\square$

**Corollary 9.2 (the six original beta-pair sums).** Define

$$
g_y=\left(1-\frac1R\right)
\left[\sum_iH_{ii}p_{yi}
+b^2\frac y{128}+a^2\frac{64-y}{128}\right].
\tag{RE.62}
$$

Write $\rho_{y,\beta,m}$ for (RE.2) with the signs (RE.3).
For each original $y\in\{5,16,27\}$ and $m\in\{0,1\}$, every
allowed ceiling factorization satisfies

$$
p_H^{\rm acq}(\rho_{y,\beta=0,m};\mathfrak F)
+p_H^{\rm acq}(\rho_{y,\beta=\pi,m};\mathfrak F)\geq2g_y.
\tag{RE.63}
$$

All six inequalities are equalities for one common construction,
Definition 5.1 at $s=1$.

Proof. By (RE.3), $W$ sends $(y,e,n)$ to $(y,-e,-n)$, precisely the
other value of $\beta$ at fixed $y,m$. Evaluating the diagonal effect
(RE.61) gives (RE.62) on either member. Apply Theorem 9.1.
All twelve histories, not only a subset chosen for a lower witness,
remain prescribed in the original error task. $\square$

## 10. Pareto optimality and failure of simultaneous pointwise minima

**Theorem 10.1 (a Pareto point in twelve resource coordinates).** Form
the twelve-vector of acquired high probabilities, one coordinate for
each original normalized specimen. The vector with value $g_y$ at
each of the four signs at height $y$ is Pareto optimal among all
ceiling factorizations: no allowed factorization weakly reduces every
coordinate and strictly reduces even one.

Proof. Every coordinate belongs to exactly one original beta-pair.
If both members are at most $g_y$ and one is strictly smaller, their
sum is below $2g_y$, contradicting (RE.63). The statement compares
coordinates and does not choose a scalar resource objective. $\square$

**Theorem 10.2 (strict per-input improvement and no universal least
vector).** On every original input,

$$
B(\rho_{y,e,n})<g_y,
\qquad B(W\rho_{y,e,n}W^\dagger)=B(\rho_{y,e,n}).
\tag{RE.64}
$$

No allowed factorization attains the pointwise envelope on both members
of any original beta-pair. Hence none attains it on all twelve histories
or on all supported inputs. The set of twelve-coordinate resource
vectors has no universally least vector. This does not classify its
complete Pareto frontier.

Proof. On an original input the coefficients in (RE.42) satisfy

$$
\begin{aligned}
C&=c^2/2+d^2y/128>0,\\
U_r&=(h_0c+h_2d)e\frac{\sqrt y}{16}
+r ac n\frac{\sqrt{64-y}}{16}.
\end{aligned}
\tag{RE.65}
$$

Their sum over $r$ is
$2(h_0c+h_2d)e\sqrt y/16\ne0$. At least one $U_r$ is therefore
nonzero. For that record the derivative of the function being minimized
in (RE.42) at zero is $-2\eta(0)U_r\ne0$. A sufficiently small step in
the sign of $U_r$ stays in $I_R$ and strictly improves its value.
For the other record minimization cannot increase its value at zero.
Since the sum of the zero-design values is
$u_0\sum_rA_r=\operatorname{tr}(G_1\rho)=g_y$, this proves the
strict inequality. Under $W$, only the $U_r$ signs reverse; the symmetric
interval in (RE.42) then gives equality of the two envelope values.

If one design attained both pointwise minima, its pair sum would be
$2B(\rho)<2g_y$, violating (RE.63). One can also see the obstruction
in the high coefficients themselves. Equality in (RE.46), on an
original input, forces $v_r=u_rx_r^2$ because $C>0$, and then
$u_r=\eta(x_r)$ because the bracket is strictly positive by (RE.50).
Equality at the minimum forces the unique $x_r^*(\rho)$ of (RE.48).
Thus the actual high coefficient matrix must be

$$
\eta(x_r^*)
\begin{pmatrix}1&-x_r^*\\-x_r^*&(x_r^*)^2\end{pmatrix}.
\tag{RE.66}
$$

For at least one record $x_r^*$ is nonzero and reverses sign on the
beta-mate. One fixed matrix cannot have those two opposite cross
entries. Any extra high acquisition mass that later fails is nonnegative
in (RE.19), and cannot repair equality.

By Corollary 8.2, a design attaining $B$ at one member does exist. Its
beta-mate must have high probability at least $2g_y-B(\rho)>g_y$.
Its resource vector is therefore incomparable with the Pareto vector
of Theorem 10.1. If a universally least vector existed, it would lie
coordinatewise below that Pareto vector and hence equal it, by Theorem
10.1. It would also have to lie below this per-input attainer, whose
selected coordinate is strictly smaller. This is impossible. No
scalarization or hidden distribution over histories enters the proof.
$\square$

## 11. Attribution, exact scope and the remaining original obligations

**Convention 11.1 (content and literature correspondence).** The
additional mathematics of this volume is the following composition:
the supplied coefficient box fixes $d>0$; the three singular complex
lines yield the all-$s$ replacement; saturation of the acquired binary
ceiling fixes the live branches; their exhaustive low-rank cone yields
the exact pointwise envelope, full separate attainers and the common
paired bound; the original beta-pairs then give the Pareto and
nonattainment conclusions. These are ordinary `repo-derived` deductions.
The supplied candidate and independent check contain the proposed
package and its assessment; they receive credit for that mathematical
proposal, while the proofs here carry each asserted implication.
An approval is not an additional mathematical premise.

The concrete reuse and literature map is limited to the supplied
bodies and the references they actually state:

| Supplied source or cited mechanism | Credit and applicability here |
| --- | --- |
| CG §§1–7 and its credited Acquired Continuation Limits, FiniteRectangleTransport, OriginalControlComposition and Instrument Boundaries suppliers | Original real histories, same preparation, old reach masses, legal relative ramp, normalized unresolved specimen and complete target law; their nested conditions are retained rather than recertified. |
| CG §§8–12 | Enlarged-class attainment, strict coherent-witness gap and distinct feasible upper processors; not new resource results of this volume. |
| CG §§13–17, (CG.112)–(CG.164) | Conditional root isolation, enclosures, exact normalization, full-class minimax and averaged-live rigidity. Definition 2.1 fixes their exact point; no whole-channel optimizer uniqueness is imported. |
| CG §§18–20 | Zero-transfer subclass separation, same effects with different successors, and the additional-services synthesis interface; not an exhaustive native-operation classification. |
| CG §§21–25 | Actual joint cut, Schmidt-number bottleneck, every-input nonsharp bound and unmixed sufficient factorization; the complete payload and actual-tag requirements are retained. |
| CG §§26–28, especially (CG.204), (CG.206), (CG.223), (CG.225) | Near-optimal averaged-live square-root stability and its resource/transfer penalties, credited in (RE.13), with no revised constant or new enclosure. |
| JR §§29–33 | Exact coefficient dictionary, finite phase-record family, whole-complex/reference/time identities, its attained family accounting and sharp binary ceiling. The new strict replacement refutes the additional universal-minimality assertion, not JR's stated family theorem. |
| Repository results named in CG/JR: FiniteKrausRepresentation, UnitaryKrausMixingInvariance and FiniteKrausInstrumentBornMarginal | Mature finite Choi/Kraus, mixing and Born-trace mechanisms. The displayed identities specialize them without a new compiled application or a duplicate generic theorem claim. |
| CG/JR's AntidistinguishabilityGram positive-support lemma and CoherentFlagPort results | Positive summand support and actual flagged-port principles; their other task-specific hypotheses do not acquire the instrument or prove this approximate task. |
| Heinosaari–Jivulescu–Reeb–Wolf, *Extending quantum operations*, arXiv:1205.0641v3, §§2.1, 6.1, as cited in CG | Finite CP/TP and Choi/Kraus framework. Its at-most-qubit compatibility result is not used for this qutrit task or as a continuous-time theorem. |
| Nechita–Park, *Random covariant quantum channels*, arXiv:2403.03667v2, §5, as cited in CG | Sign-covariant maps can have population transfer and reverse coherence. No Schur restriction or physical sign/conjugation gate follows. |
| Muñoz-Moller–Leppäjärvi–Heinosaari, *Adversarial Information Gain in Non-ideal Quantum Measurements*, arXiv:2602.20941v1, Definition 1 and Proposition 1; Leppäjärvi–Sedlák, *Incompatibility of quantum instruments*, arXiv:2212.11225v2, Definition 8, Remark 3 and Proposition 7, as cited in JR | Joint-instrument compatibility and finite dilation/postprocessing antecedents. The present proof uses finite live Choi domination and handles each time measure directly; no environment port or unproved continuous-outcome extension is assumed. |
| Terhal–Horodecki, *A Schmidt number for density matrices*, quant-ph/9911117v4; Chruściński–Kossakowski, *On partially entanglement breaking channels*, quant-ph/0511244v1; Sekatski, *The bottleneck dimension of quantum operations*, arXiv:2608.25010v1, as cited in CG | Mature Schmidt-rank and classical-assisted bottleneck mechanisms. They underlie the inherited obstruction and the product-rank step, rather than a capacity formula or this exact envelope. |
| CG §28's Ding–Udell and Nishijima–Li–Lourenço error-bound comparisons, positive compression and trace-pairing library references | Antecedents and tools for the inherited stability theorem with its own premises; not a new stability solve or an automatic certificate for the complete cq objective. |

This bounded source comparison does not establish absence from external
literature or worldwide originality. The literature entries are credited
through the supplied sources; no independent external search or
verification of their bodies is asserted. Source references to Lean
libraries are references, not kernel evidence for this volume.

**Boundary 11.2 (resolved quantifiers and unresolved native programme).**
For every $|\gamma|\leq\kappa$ the explicit finite construction strictly
reduces JR's high-acquisition mass wherever the positive input has
nonzero supported compression, while preserving even its binary-labelled
complete CP maps. For $|\gamma|>\kappa$ the credited ceiling excludes
the required law. At $|\gamma|=\kappa$, (RE.58) is the exact universal
pointwise endpoint envelope over every original finite fully counted
factorization, with a separate complete common design for each test
input. Equations (RE.59)–(RE.63) instead have one common attainer for
all paired inputs. Its twelve-vector is Pareto optimal, while (RE.64)
excludes a common all-pointwise attainer or universally least vector.
The full interior pointwise envelope for $|\gamma|<\kappa$ and the
complete multi-input Pareto frontier remain unresolved.

All asserted channel identities hold on the full complex five-mode
algebra and arbitrary passive references, retain the five separately
named exact-time CP measures and original cross-support action, and
introduce zero additional-sector maps. All probability claims are for
positive inputs; zero, singular and subnormalized inputs are included.
An arbitrary five-mode input uses its unnormalized supported compression;
no uniform positive high-resource bound is asserted on $V^\perp$.
All actual tags, fibre dimensions, effects and full TP decoders are part
of the explicit instruments. High acquisition counts all future-accessible
shares jointly and is never replaced silently by high live mass. No
retry, extra specimen, history helper, reach-mass prior, hidden bypass,
post-failure live action or acceptance normalization is supplied.

These are exact abstract factorizations of one particular channel.
They neither make the native encoder available nor derive coherent
storage, actual classical acquisition, calibrated range decoding or
their permissions from geometric reachability. The original-control
path predicate and the probability-changing, noncommuting fields in
CG/JR's Probability/Phase Transport source do not make diagonal filters
an exhaustive native menu. Conversely, an arbitrary Stinespring dilation
or a mathematical Kraus mixture does not supply an accessible quantum
port or enacted classical record. A physical realization must supply
those services at the original clock cut, and reproduce the absorbing
first failure at its actual elapsed time with all original archives and
updates. A sampled timestamp is insufficient.

No physical efficiency, finite exact-clock implementation, quantum
capacity, generic neural-network or empirical learning theorem follows.
No improved inherited error constant, unconditional-prefix optimum,
whole-channel optimizer classification, Lean/kernel/frozen-truth claim,
or completion of the continuing original acquisition/control/research
goal is asserted. The endpoint resource question has the stated
conditional mathematical answer; the remaining original native and
interior/frontier obligations retain their full scope.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md

## 追加锚（本行以下为增补区）
