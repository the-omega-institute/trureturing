# Native interior record and quantum-resource reduction

## 1. The original experiment and the fixed-channel question

**Convention 1.1 (conditional mathematical scope).** The object studied here
is the particular complete channel of [Complete Continuation
Distinguishability Gap][CG], (CG.135)–(CG.142), with the coefficient
convention of [Joint Record and Quantum Payload][JR], (JR.2). The
companion [Fixed-Channel Record and Resource Envelope][RE] supplies the
endpoint resource results and an earlier construction at every record
strength. The isolated algebraic point, enclosure inequalities, exact
normalization and complete-output minimax identification in CG are
conditional ordinary mathematical premises. Their preparation, original
control and calibrated-instrument suppliers retain their stated
conditions. No root isolation, enclosure computation, nested proof or
minimax certificate is authenticated anew here.

JR §§34–40 supply the joint scalar allocation, common finite attainer,
sharp original four-sign average laws and a stronger worst-history law
over **all** error-optimizing channels. The diagonal-input envelope and
common instrument in §§6–7 below reuse that scalar mathematics with
general nonnegative diagonal weights; the averages and the consequent
twelve-coordinate Pareto point in §9 are not additional mathematical
knowledge. Comparison 2.5 gives the exact parameter and model
correspondence. The uncovered content retained here is the exact binary
live freedom and interior nonuniqueness, strict operator improvement of
RE's earlier all-strength construction throughout the interior, lawful
individual-history perturbations with mate conflict and failure of
simultaneous pointwise optimality, and the exact compact reduction of the
original unrestricted finite problem to its full complex coefficient
cone. That reduction gives finite pointwise attainers with at most thirty
actual acquisition branches. It does not evaluate the general
coherent-input minimum or classify the entire frontier.

**Definition 1.2 (source, coordinates and histories).** Original modes have
basis $e_0,e_1,e_2,e_3,e_4$, with index $4$ naming original mode $13$.
Write

$$
\begin{gathered}
c_{\rm src}=1/4,\quad Z_{\rm src}=1/2,\quad
\mathfrak a=16/256,\quad \mathfrak h=11/256,\quad
\delta_{\rm ramp}=6/256,\quad L=1,\\
|+\rangle=(e_0+e_4)/\sqrt2,\quad
|-\rangle=(e_1+e_3)/\sqrt2,\quad |2\rangle=e_2,\\
E=(|+\rangle,|-\rangle,|2\rangle):\mathbb C^3\longrightarrow\mathbb C^5,
\quad P=EE^\dagger,\quad Q_5=I_5-P,\quad V=\operatorname{ran}E.
\end{gathered}
\tag{IR.1}
$$

Supported matrix indices $0,1,2$ mean $(+,-,2)$, rather than the five
failure labels. The actual normalized reached-old-live-cut inputs are

$$
\begin{aligned}
p_y&=(y/128,(64-y)/128,1/2),&
a_y&=(\sqrt{p_{y0}},\sqrt{p_{y1}},\sqrt{p_{y2}})^T,\\
U_{e,n}&=\operatorname{diag}(e,n,1),&
\rho_{y,e,n}&=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\\
y&\in\{5,16,27\},& e,n&\in\{+1,-1\}.
\end{aligned}
\tag{IR.2}
$$

Their source dictionary is

$$
x=y/256\in\{\mathfrak a-\mathfrak h,\mathfrak a,
\mathfrak a+\mathfrak h\},\qquad
 e=(-1)^{\beta_{\rm hist}/\pi},\qquad
 n=e(-1)^m,\qquad \beta_{\rm hist}\in\{0,\pi\},\quad m\in\{0,1\}.
\tag{IR.3}
$$

In particular $en=(-1)^m$. These twelve states come from one preparation,
not a selectable ensemble. To specify the credited source correspondence,
the double-wall populations and phase rates are

$$
\begin{aligned}
p(k)&=(k,c_{\rm src}-k,Z_{\rm src},c_{\rm src}-k,k),
\qquad 0<k<c_{\rm src},\\
w(k)&=\left(\frac{c_{\rm src}-k}{2c_{\rm src}},
-\frac{k}{2c_{\rm src}},0,-\frac{k}{2c_{\rm src}},
\frac{c_{\rm src}-k}{2c_{\rm src}}\right),\\
\psi_i(t)&=\sqrt{p(k(t))_i}\exp\left(-i\int_0^t
 w_i(k(u))\chi'(u)\,du\right).
\end{aligned}
\tag{IR.4}
$$

CG Proposition 2.2 gives six unit-duration legs from preparation height
$1/8$: a phase leg $0\to2\pi m$, descent to $1/16$, phase leg
$2\pi m\to2\pi m+B$, ascent to $1/8$, phase return to $2\pi m$,
and height change to $x$, where $B=8\beta_{\rm hist}-4\pi m$.
The resulting real residual is
$(\beta_{\rm hist},\beta_{\rm hist}-\pi m,0,
\beta_{\rm hist}-\pi m,\beta_{\rm hist})$, which gives (IR.2).
The positive old reach masses are $32/177,2/9,32/111$, respectively.
The experiment starts with the normalized specimen conditioned on that
already reached cut at time six. Those earlier masses are neither
history priors nor new acceptance weights.

All original path conditions remain: finite duration, continuous strict
height coordinates, a signed real phase lift of finite variation, and
absolute continuity or the specified finite-piecewise-$C^1$ alternative.
Composition is literal chronological composition of the same real lift.
The requested continuation is $k(t)=x+\delta_{\rm ramp}t$ with phase
fixed, $0\leq t\leq1$, legal on the common relative-command domain
$(0,58/256)$. Zero duration allows only the matching zero-displacement
identity. Denial, visible unexecuted rejection, permissions and controller
updates keep their original meanings. A partial command supplies no
unknown-height detector, waveform read or new original actuator.

**Definition 1.3 (the full original targets).** For each height set

$$
\begin{aligned}
\varsigma_y&=y/(y+6),& f_y(t)&=6y/(y+6t)^2,\\
d_y&=\left(y/128,\frac{y(58-y)}{128(y+6)},\frac{y}{2(y+6)}\right),&
(B_y)_{ij}&=\sqrt{d_{yi}d_{yj}},\\
w&=(0,1/4,1/2,1/4,0),&P_f&=|f\rangle\langle f|.
\end{aligned}
\tag{IR.5}
$$

The original target $\Omega_{y,e,n}$ has live block
$EU_{e,n}B_yU_{e,n}^\dagger E^\dagger$ and five separate failure
measures $w_\ell f_y(t)dt\,P_f$, $\ell=0,1,2,3,4$. Exact elapsed
time is $t\in[0,1]$, equivalently absolute time $6+t$. Labels $1,3$
are distinct, and the zero-density labels $0,13$ remain named. The
live trace is $\varsigma_y$ and $\int_0^1 f_y=1-\varsigma_y$.
For a common processor the original error is

$$
\mathcal E(\Phi)=\max_{y,e,n}\frac12
 \|\Phi(E\rho_{y,e,n}E^\dagger)-\Omega_{y,e,n}\|_{1,\mathrm{cq}},
\qquad \mathcal E_* =\inf_{\Phi\ \mathrm{common\ CPTP}}\mathcal E(\Phi).
\tag{IR.6}
$$

The full cq norm adds the live trace norm and variation trace norms
in every separately labelled time sector, including atoms and singular
measures through a common dominating scalar measure. All abort,
rejection, wrong-support and other zero-target outcomes are counted.
First executed failure is absorbing; every old stopped archive stays in
its own branch. The sole specimen and fixed common source/epoch,
calibration, permissions, controller and aligned-clock metadata are the
available input. No unknown history label or readable old programme is
supplied. Every new acquisition outcome remains unnormalized.

## 2. Exact coefficient data and inherited mathematics

**Definition 2.1 (exact algebraic supplier dictionary).** The coefficients
below are fixed by the following source specification. This definition
records the point used in CG, rather than selecting new approximate
coefficients. Let
$\mathbf x=(\lambda,\alpha_1,\alpha_2,\beta_1,\beta_2,z)$ and
$\eta=(\eta_0,\eta_1,\eta_2)$, and put

$$
\begin{aligned}
v_5&=(\alpha_1,\alpha_2,-1)^T,&v_{27}&=(\beta_1,\beta_2,1)^T,\\
R_y^{\rm src}&=v_yv_y^T/(v_y^Tv_y),&
A_5^{\rm src}&=\lambda R_5^{\rm src},\quad
 A_{27}^{\rm src}=(1-\lambda)R_{27}^{\rm src},\\
\zeta&=(z,59\lambda/128,\lambda/2),&
N^{\rm src}&=\sum_{y=5,27}A_y^{\rm src}\odot(a_ya_y^T),\\
S_0^{\rm src}&=\operatorname{diag}\zeta-N^{\rm src},&
S_{ij}^{\rm src}&=\begin{pmatrix}
\zeta_j-\sum_{y=5,27}(A_y^{\rm src})_{ii}p_{yj}&-N^{\rm src}_{ij}\\
-N^{\rm src}_{ij}&\zeta_i-\sum_{y=5,27}(A_y^{\rm src})_{jj}p_{yi}
\end{pmatrix},\\
F^{\rm src}&=\sum_{y=5,27}\operatorname{tr}(A_y^{\rm src}B_y)
 -\sum_i\zeta_i+6\lambda/11,&
\mathbf g^{\rm src}&=(1000\det S_0^{\rm src},\det S_{01}^{\rm src},
 \det S_{02}^{\rm src}),\\
\Psi(\mathbf x,\eta)&=
\left(\nabla_{\mathbf x}(F^{\rm src}+\eta\cdot\mathbf g^{\rm src}),
\mathbf g^{\rm src}\right).
\end{aligned}
\tag{IR.7}
$$

The two-dimensional formula is for $i<j$; $\odot$ denotes entrywise
multiplication. The credited premise is a unique zero $u_*$ in the
closed box of radius $10^{-24}$ in every coordinate, with these exact
rational centres:

| Coordinate | Centre |
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

At that same point define

$$
\begin{aligned}
H^{\rm src}&=1000\eta_0\operatorname{adj}S_0^{\rm src},&
Q^{01}&=\eta_1\operatorname{adj}S_{01}^{\rm src},&
Q^{02}&=\eta_2\operatorname{adj}S_{02}^{\rm src},\\
h&=H^{\rm src}e_0/\sqrt{H^{\rm src}_{00}},&
(a,b)^T&=Q^{01}e_0/\sqrt{Q^{01}_{00}},&
(c,d)^T&=Q^{02}e_0/\sqrt{Q^{02}_{00}},\\
m_1&=1-H^{\rm src}_{11}-Q^{01}_{00},&
m_2&=1-H^{\rm src}_{22}-Q^{02}_{00},\\
D&=\operatorname{diag}(h_0,h_1,h_2),&
T&=a|0\rangle\langle1|+b|1\rangle\langle0|,&
S&=c|0\rangle\langle2|+d|2\rangle\langle0|,\\
M&=\operatorname{diag}(0,m_1,m_2),&
\kappa&=h_0a+h_1b,&g(t)&=2/(1+t)^2.
\end{aligned}
\tag{IR.8}
$$

In the factor definitions $e_0$ is the first standard coordinate of the
relevant matrix size. The letters $c,d$ here are Kraus amplitudes, not
$c_{\rm src},\delta_{\rm ramp}$ or a carrier dimension. The coordinates
$\beta_1,\beta_2$ are unrelated to $\beta_{\rm hist}$.

**Convention 2.2 (specific supplied premises).** CG §§13–17, §22 and
JR §29 supply the rank-one factorizations
$H^{\rm src}=hh^T$, $Q^{01}=(a,b)^T(a,b)$,
$Q^{02}=(c,d)^T(c,d)$, and

$$
\begin{gathered}
h_0,h_1,h_2,a,b,c>0,\quad d\ne0,\quad m_1,m_2,\eta_2>0,\quad
0<\kappa<1/4,\\
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
h_0h_1>695/1000,\quad h_0h_2>796/1000,\quad
\operatorname{tr}Q^{01}+\operatorname{tr}Q^{02}<36/1000,\\
\lambda<49/100,\quad \alpha_1>0,\quad \alpha_2>1,\quad
2/5<\beta_1<1/2,\quad 0<\beta_2<5/6.
\end{gathered}
\tag{IR.9}
$$

These are exact identities and strict conditional inequalities, not
numerical tolerances established here. In particular the total effect
in (IR.9) is exactly $I_3$.

**Definition 2.3 (the fixed complete forgotten channel).** For every
complex $A\in M_5$, write $A_V=E^\dagger AE$ and define

$$
\begin{aligned}
\widehat\Phi_*^L(A)&=
 E(DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger)E^\dagger,\\
\widehat\Phi_{*,\ell}^f(A)(dt)&=
 g(t)\left[w_\ell\operatorname{tr}(MA_V)
 +\mathbf1_{\ell=2}\operatorname{tr}(Q_5A)\right]dt\,P_f.
\end{aligned}
\tag{IR.10}
$$

Every extra-sector map is zero. Its original completion kills all
$V$–$V^\perp$ cross operators and has no live complement output.
Kraus conjugations and positive trace functionals prove CP on the full
complex algebra, also at every passive reference amplification.
The identities $\sum_\ell w_\ell=1$, $\int_0^1g=1$ and (IR.9)
prove TP. On a joint input a trace branch retains its conditional
reference operator, rather than replacing it by an unconditional state.

CG identifies, conditionally on its certificate,

$$
\mathcal E(\widehat\Phi_*)=\mathcal E_*=F^{\rm src}(\mathbf x_*),
\qquad
0.14817810291080132013<\mathcal E_*<0.14817810291080132014.
\tag{IR.11}
$$

No uniqueness of the entire optimizing channel is inferred. The resource
problem here fixes (IR.10) itself. Equal canonical errors alone do not
permit substituting another optimizer.

**Convention 2.4 (inherited content and uncovered relations).** CG §§1–12
give the original complete-output experiment, coherent witnesses, enlarged-class
attainment and feasible upper channels. Its §§13–20 give the conditional
benchmark, averaged-live rigidity, restricted zero-transfer obstruction
and same-effects separation. CG §§21–25 already supply the actual joint
acquisition model, Schmidt-number-three obstruction, a nonsharp positive
resource requirement on every supported input and an unmixed sufficient
factorization. CG §§26–28 supply near-optimal averaged-live stability
and resource penalties with their own conditional constant. None of
these is a new theorem of the present volume.

JR §§29–33 give the finite record family, its exact binary winding law,
full-complex/reference/time identities, attained family accounting, and
sharp compatibility ceiling $|\gamma|\leq\kappa$. RE §§4–5 give a
strict all-strength replacement; RE §§6–10 solve the endpoint pointwise
resource problem, distinguish separate attainers from one common paired
attainer, and prove its endpoint Pareto and nonattainment results. Their
closed scalar endpoint minimizer package is credited there and is not
repeated as new content here.

JR §§34–40 supply the positive determinant parameters, joint rank/record
allocation, sharp scalar cost and sign averages, and one finite
complete-channel attainer. Their worst-history optimization ranges over
every error optimizer and constrains only the normalized winding
contrast. The overlapping scalar, diagonal/common-attainer and average
laws below are reused with explicit correspondence, not counted as new
results. The uncovered binary-live, comparison, perturbation and compact
reduction statements keep the original unrestricted finite class.

**Comparison 2.5 (exact current-JR correspondence and scope).** The
isolated point $u_*$ and the matrices $D,T,S,M,E$ and number $\kappa$
in (IR.7)–(IR.10) are exactly those of (JR.2), with no rescaling of
the input or error. The remaining dictionary is

| This volume | JR §§34–39 |
| --- | --- |
| $\alpha=ab/(h_0h_1)$ | $\theta$ |
| $\beta=cd/(h_0h_2)$ | $\omega$ |
| $\ell=\alpha+\beta$, $k=1-\ell$ | $\delta$, $k=1-\theta-\omega$ |
| $\sqrt\ell$, $1-q_{\max}=\beta/(1-\alpha)$ | $s_0$, $v_0$ |
| $1-q_s$, $1-p_s=\alpha(1-q_s)+\beta$ | $v_s$, $u_s=\theta v_s+\omega$ |
| $\mathscr H_s=(1-\beta)\ell-\alpha s^2$ | $\theta(1-s^2)+\omega k$ |
| $g_y(s)=p_sA_y+q_sB_y$ | $P_y(s)$ |
| $g_{27}(s)$ | $\mathsf C(s)$ |

Here $p_s,q_s,q_{\max},\mathscr H_s$ are (IR.31)–(IR.32),
$g_y$ is (IR.54), and the shared height weights are
$A_y=\sum_i h_i^2p_{yi}$,
$B_y=b^2p_{y0}+a^2p_{y1}$ and
$C_y=d^2p_{y0}+c^2p_{y2}$ as in (JR.23).
The resource coefficient $q_s$ is unrelated to the input coherence
$q_y=\sqrt{y(64-y)}/128$ in JR's winding law.

This dictionary identifies the closed formulas, including their root
branches. Indeed $p_s-\alpha q_s=k$ becomes
$u_s=\theta v_s+\omega$, and
$F(p,q)=\sqrt{pq}+\sqrt{(1-p)(1-q)}$ is unchanged by replacing
$(p,q)$ with $(1-p,1-q)$. Thus (IR.40) is exactly (JR.30)'s
unique strong-branch equation. Its interval
$0\leq q\leq k/(1-\alpha)$ maps to $v_0\leq v\leq1$.
Both weak branches have $(p_s,q_s)=(k,0)$, and both endpoints have
$p_1=q_1=k/(1-\alpha)$. The radical identity in the table follows
from $k=1-\alpha-\beta$. Hence the rationalized expression (IR.31)
and (JR.31) specify the same coefficients without a numerical root
choice. The diagonal proof in §6 retains this credited scalar argument
with arbitrary nonnegative weights
$\operatorname{tr}(D^\dagger D\tau)$,
$\operatorname{tr}(T^\dagger T\tau)$ and
$\operatorname{tr}(S^\dagger S\tau)$.

The comparison classes differ. JR Definition 34.1 permits every common
full-output optimizer $\Phi$ with $\mathcal E(\Phi)=\mathcal E_*$,
and asks only for normalized winding contrast
$\mathsf V(F)=2|\operatorname{Re}F_{01}|/\kappa\geq s$.
It includes finite, countable and explicitly stipulated measurable
integral actual factorizations. Here (IR.12) fixes the entire channel
$\widehat\Phi_*$, (IR.13) fixes both binary effects on every five-mode
input, and the implementation class remains finite. Its members have
contrast exactly $s$, so form a subclass of JR's comparison. JR's
explicit finite attainer belongs to this subclass: on the strong branch
$(r,\epsilon)=(\sigma,\tau)$ identifies (IR.43) with (JR.34).
On the weak branch, splitting JR's low labels with the kernel
$(1+r\sigma s/\sqrt\ell)/2$ gives (IR.42) with
$(\epsilon,\zeta)=(\sigma,\tau)$. Proportional high copies at a
fixed $r$ combine into $A_r=\sqrt{k/2}D$; the scalar failure and
complement copies combine into the halves in §7. Thus these particular
attainers also preserve JR §§30–31's binary-conditioned complete maps,
as verified on all complex inputs, passive references and labelled time
sets in Theorem 7.2. JR's lower bound and this attainer already give
worst-history minimum $g_{27}(s)$ even in the present fixed-channel,
exact-effect class. Neither this minimum nor JR's inverse scalar budget
evaluates the general coherent-input minimum or the whole twelve-vector
frontier.

JR Theorem 35.1 preserves the actual winding contrast and four-sign
averaged acquisition costs by relabelling the record during sign
averaging. It identifies the averaged live Choi matrix $J_*$ and total
canonical-failure effect $M$. It does **not** identify an arbitrary
optimizer's entire forgotten channel or individual labelled failure-time
CP measures, either before or after averaging. The explicit complete-map
identities of JR's attainer and §7 are proved identities for those
instruments, not a uniqueness assertion about all optimizers.

## 3. Every-input record law and the original finite resource class

**Definition 3.1 (actual finite common designs).** A design $\mathfrak F$
has a finite actually generated acquisition label $\xi$, common CP maps
$\mathcal C_\xi:M_5\to M_{d_\xi}$ with $1\leq d_\xi<\infty$,
and common CP full-output TP decoders $\mathcal R_\xi$, satisfying

$$
\sum_\xi\mathcal C_\xi^\dagger(I_{d_\xi})=I_5,
\qquad
\sum_\xi\mathcal R_\xi\mathcal C_\xi=\widehat\Phi_*.
\tag{IR.12}
$$

The second identity holds on all complex matrices, in every output
sector and every Borel time set. Only the total encoder is TP. Each
positive encoder effect is at most their joint sum and is therefore
TNI. Every decoder is TP on its entire fibre; its supported live
compression is only TNI. Arbitrarily large finite fibres, mixed
encoders, nonisometric decoders and arbitrary finite refinements of the
binary label are included in universal statements.

The block $M_{d_\xi}$ counts **jointly** everything accessible to future
execution that can influence output: specimen, quantum memory and
controller, accessible environment, returned systems and all retained
entanglement shares. There is no other quantum path across the cut.
Independent later blank ancillas may be absorbed into the decoders; a
receiver share of earlier entanglement is not a blank. Other dilation
systems must be permanently inaccessible before this cut if omitted
from the block. A passive reference can be arbitrary and entangled,
but is inaccessible to both maps. Their identities tensor with its
identity. There is no callback, helper specimen, source-dependent
programme, copy, reset, retry or acceptance division. Fixed common
classical metadata remain available. A coherent branch sum without an
actually enacted classical record is one quantum payload; an algebraic
Kraus decomposition does not supply acquired flags.

**Definition 3.2 (prescribed binary component and resource).** Fix a
public $s\in[0,1]$ before receiving the unknown specimen. The observed
component $r(\xi)\in\{+1,-1\}$ must have every-input effects

$$
F_r(s)=\frac{I_5+r s\kappa E X_{01}E^\dagger}{2},
\qquad X_{01}=|0\rangle\langle1|+|1\rangle\langle0|.
\tag{IR.13}
$$

A finite postprocessing coin is absorbed into $\xi$. On a positive
five-mode input $\sigma$, with unnormalized compression
$\rho=E^\dagger\sigma E$, its law is

$$
\Pr_\sigma(r)=\frac{\operatorname{tr}\sigma}{2}
 +r s\kappa\operatorname{Re}\rho_{01}.
\tag{IR.14}
$$

For (IR.2) it is $1/2+rs\kappa en\sqrt{y(64-y)}/128$.
This is a conditional law for each original history, with no prior on
histories. The finer label laws are not prescribed. In particular the
original class does not require the JR binary-conditioned output
channels. Some constructions below preserve that stronger property;
the lower proofs do not impose it. Negative coefficient
$\gamma=-s\kappa$ is obtained by exchanging $r=+1,-1$. JR's ceiling
excludes $|\gamma|>\kappa$ for this fixed channel.

The acquired high-dimensional effect and mass are

$$
G_H^{\rm acq}(\mathfrak F)=
 \sum_{d_\xi\geq3}\mathcal C_\xi^\dagger(I),
\qquad p_H^{\rm acq}(\sigma;\mathfrak F)
 =\operatorname{tr}(G_H^{\rm acq}(\mathfrak F)\sigma).
\tag{IR.15}
$$

Let $G_H^L,p_H^L$ count the supported live output of these same actual
high fibres. Full decoder TP and live TNI give the operator inequality

$$
G_H^{\rm acq}\succeq G_H^L\succeq0,
\qquad p_H^{\rm acq}(\sigma)\geq p_H^L(\sigma)\geq0.
\tag{IR.16}
$$

For supported inputs the notation means evaluation at $E\rho E^\dagger$.
Every mass is homogeneous on positive inputs; no division by live or
acquisition success occurs. The universal statements below concern this
original finite model. JR's broader all-optimizer and countable/integral
scalar law is reused through Comparison 2.5; it does not enlarge the
implementation class of the binary-live, perturbation or compact
reduction theorems here.

## 4. Positive coefficients and the full complex singular locus

**Lemma 4.1 (signs and dimensionless parameters).** The supplier premises
imply $d>0$. Define

$$
\alpha=\frac{ab}{h_0h_1},\qquad
\beta=\frac{cd}{h_0h_2},\qquad
\ell=\alpha+\beta,\qquad k=1-\ell.
\tag{IR.17}
$$

These $\alpha,\beta$ are dimensionless constants, neither an acquisition
label nor $\beta_{\rm hist}$ nor the root coordinates in (IR.7).
They satisfy $\alpha,\beta>0$, $0<\ell<1$, $k>0$.

Proof. The positive sign is already established in RE Lemma 4.1 and
JR Proposition 34.2. A self-contained deduction uses the exact source
formula

$$
N^{\rm src}_{02}=
-\frac{\lambda\alpha_1\sqrt5}{16(1+\alpha_1^2+\alpha_2^2)}
+\frac{(1-\lambda)\beta_1\sqrt{27}}
 {16(1+\beta_1^2+\beta_2^2)}.
\tag{IR.18}
$$

From (IR.9),
$\alpha_1/(1+\alpha_1^2+\alpha_2^2)<1/(2\sqrt2)<3/8$:
the first inequality follows from
$\alpha_1^2+2\geq2\sqrt2\alpha_1$ and $\alpha_2>1$.
Also
$\beta_1/(1+\beta_1^2+\beta_2^2)>
(2/5)/(1+1/4+25/36)=36/175>1/5$.
Positive squaring gives $\sqrt5/16<3/20$ and
$\sqrt{27}/16>3/10$. Thus the negative magnitude in (IR.18) is
less than $441/16000$, while the positive term exceeds $153/5000$.
Their difference is greater than $243/80000>0$. The adjugate formula
in (IR.8) gives $cd=\eta_2N^{\rm src}_{02}>0$; since $c>0$, $d>0$.
This is a symbolic deduction from the supplied box bounds.

Rank one and positivity give
$ab\leq(a^2+b^2)/2<18/1000$ and
$cd\leq(c^2+d^2)/2<18/1000$.
Consequently $0<\alpha<18/695$ and $0<\beta<18/796$.
Each upper bound is below $1/2$, so $\ell<1$. All denominators in
(IR.17) are positive by (IR.9). $\square$

**Lemma 4.2 (all complex low-rank directions and fixed compressions).**
For arbitrary complex coefficients put

$$
K(u,v,w)=uD+vT+wS=
\begin{pmatrix}
h_0u&av&cw\\bv&h_1u&0\\dw&0&h_2u
\end{pmatrix}.
\tag{IR.19}
$$

Then

$$
\det K(u,v,w)=h_0h_1h_2\,u(u^2-\alpha v^2-\beta w^2).
\tag{IR.20}
$$

Every nonzero singular matrix in this span has rank exactly two.
The full complex singular locus is the union of the plane $u=0$ and
the quadratic cone $u^2=\alpha v^2+\beta w^2$. Every singular
direction obeys

$$
|u|^2\leq\alpha|v|^2+\beta|w|^2.
\tag{IR.21}
$$

Proof. The determinant identity (IR.20) and low-rank inequality (IR.21)
are (JR.22) and the complex triangle step of JR Theorem 36.1 under
Comparison 2.5. We retain their derivation together with the exhaustive
rank and range statements needed for the actual finite reduction.
Expanding the determinant in (IR.19) gives
$h_0h_1h_2u^3-abh_2uv^2-cdh_1uw^2$, proving (IR.20).
When $u\ne0$, the minor in rows and columns $1,2$ is
$h_1h_2u^2\ne0$, so a singular such matrix has rank two.
When $u=0$ and $(v,w)\ne(0,0)$, its first row is nonzero and its
first column is nonzero. The first column has range in
$\operatorname{span}\{|1\rangle,|2\rangle\}$; a nonzero other
column has range in $|0\rangle$. These are independent, and the
remaining columns are parallel, so again the rank is two. There are
no nonzero rank-one directions. On the quadratic cone, absolute
values and the triangle inequality prove (IR.21); on the entire
plane $u=0$ it is immediate. No reality restriction was used.

For later actual encoders, fix range isometries by the following
formula. For $u\ne0$, choose columns $z_1,z_2$ numbered $1,2$ of
$K(u,v,w)$. They are independent by the same minor. If $u=0$, choose
column $0$ and column $1$ when $v\ne0$, and columns $0,2$ otherwise.
The preceding range argument proves independence. Define

$$
q_1=z_1/\|z_1\|,\qquad
q_2=\frac{z_2-q_1(q_1^\dagger z_2)}
 {\|z_2-q_1(q_1^\dagger z_2)\|},\qquad U_K=(q_1,q_2).
\tag{IR.22}
$$

Both denominators are nonzero. For each nonzero singular $K$,
$U_K^\dagger U_K=I_2$ and $U_KU_K^\dagger K=K$.
Thus encoder $U_K^\dagger K$ and full TP isometric decoder
$X\mapsto EU_KXU_K^\dagger E^\dagger$ have composite live matrix
$EK$. These are fixed matrices chosen before receiving the input.
The encoder map is CP and is TNI whenever $K^\dagger K\preceq I$,
as guaranteed by the joint effect identities in each construction below.
A zero matrix is simply omitted. $\square$

## 5. Exact binary live freedom

**Definition 5.1 (coefficient effects).** Use the unnormalized
output-input vectorization
$|K\rangle\!\rangle=\sum_{a,i}K_{ai}|a\rangle|i\rangle$.
Let $\mathcal V$ have columns
$|D\rangle\!\rangle,|T\rangle\!\rangle,|S\rangle\!\rangle$,
ordered $D,T,S$. They are independent and orthogonal, but not normalized.
For a Hermitian coefficient matrix $Z$, set

$$
\Lambda_Z(A)=\sum_{i,j\in\{D,T,S\}}Z_{ij}K_iAK_j^\dagger,
\qquad
\Theta(Z)=\sum_{i,j}Z_{ij}K_j^\dagger K_i.
\tag{IR.23}
$$

Thus $J_{\Lambda_Z}=\mathcal VZ\mathcal V^\dagger$ and
$\Lambda_Z^\dagger(I)=\Theta(Z)$. In this Choi convention
$\operatorname{Tr}_{\rm out}J_{\Lambda_Z}=\Theta(Z)^T$;
$\Theta$ is the actual effect, with no missing transpose. In
particular $\Theta(I_3)=I_3-M$, and $Z\succeq0$ implies
$\Theta(Z)\succeq0$ by a rank-one decomposition.

**Theorem 5.2 (necessary and sufficient binary live criterion).** The
possible supported plus live coefficient matrices of the entire
original class are exactly

$$
0\preceq Z\preceq I_3,\qquad
0\preceq N:=\frac{I_3+s\kappa X_{01}}2-\Theta(Z)\preceq M.
\tag{IR.24}
$$

The minus live coefficient matrix is $I_3-Z$. This characterizes live
maps, not unique binary-labelled time measures. Every such $Z$ has an
actual finite full-output realization in the original class.

Proof. The fixed supported live Choi matrix is
$J_*=\mathcal V\mathcal V^\dagger$. A positive summand $J_+$
satisfies $0\preceq J_+\preceq J_*$. If $z\in\ker J_*$,
positivity gives $z^\dagger J_+z=0$, hence $J_+z=0$ by its
positive square root. Its range is therefore in $\operatorname{ran}\mathcal V$.
With $G=\mathcal V^\dagger\mathcal V\succ0$,

$$
Z=G^{-1}\mathcal V^\dagger J_+\mathcal VG^{-1},
\qquad J_+=\mathcal VZ\mathcal V^\dagger.
\tag{IR.25}
$$

Testing domination on $\mathcal VG^{-1}z$ proves $0\preceq Z\preceq I$.
This keeps the correct nonunit Gram matrix.

The total supported failure event has effect $M$. Its plus effect is
$N$ because the full plus record effect is prescribed and its live
effect is $\Theta(Z)$. Positivity of both binary failure measures gives
$0\preceq N\preceq M$, including every label and time in that event.
All extra zero-sector summands vanish by positivity. This proves
necessity without requiring any particular time splitting.

Conversely factor $Z$ and $I-Z$ into finitely many coefficient vectors.
For each vector use its matrix $K(u,v,w)$ as encoder into $\mathbb C^3$
and decode isometrically by $E$ into live. Range compression is also
available for a singular vector. These give exactly $\Lambda_Z$ and
$\Lambda_{I-Z}$. Both $N$ and $M-N$ kill $|0\rangle$: their quadratic
forms there are bounded above by that of $M$, which is zero. Their
ranks are at most two. For each positive eigenvalue $\lambda_j$ and
unit eigenvector $v_j$ of $N$ or $M-N$, supply scalar encoder row
$\sqrt{\lambda_j}\langle v_j|$, tagged with its binary record.
Decode each scalar $z$ to all five measures
$z w_\ell g(t)dt\,P_f$. This is a full TP decoder since

$$
\int_0^1g(t)dt=\left[-2/(1+t)\right]_0^1=1,
\qquad \sum_\ell w_\ell=1.
\tag{IR.26}
$$

It realizes failure effects $N,M-N$, with the same forgotten failure
measure as (IR.10). Supported encoder effects sum to
$\Theta(I)+M=I_3$. On five modes replace every row or matrix $C$ by
$CE^\dagger$ and add scalar encoder $A\mapsto\operatorname{tr}(Q_5A)/2$
for each binary record, decoded with measure $zg(t)dt\,P_f$ at label
$2$ only. Their total effect is $P+Q_5=I_5$. Each positive individual
effect is bounded by that sum. At fixed record, the supported effect
is $\Theta(Z)+N$ or $\Theta(I-Z)+M-N$, which gives (IR.13).
Every live decoder is TP on its whole fibre; so are all scalar decoders.

All these identities are equalities of complex Kraus conjugations and
trace maps. Tensoring with an arbitrary passive reference identity
preserves them. Scalar rows retain their conditional reference operators;
the complement branch retains
$\operatorname{Tr}_5[(Q_5\otimes I)X]/2$ on a joint input $X$.
On any Borel time set, multiply the appropriate operator by
$\int_Bg(t)dt$, $P_f$ and its original label weight. Thus the forgotten
full CP measures, cross-support zero action and zero extra sectors agree
with (IR.10) at every amplification. The construction supplies actual
finite labels and only their stated fibres; other dilation systems are
permanently discarded. This proves full finite sufficiency. $\square$

**Proposition 5.3 (interior nonuniqueness and the endpoint boundary).**
Put

$$
Z_r^0(s)=\frac12\begin{pmatrix}1&rs&0\\rs&1&0\\0&0&1\end{pmatrix},
\qquad Y=\operatorname{diag}(d^2,0,-h_0^2).
\tag{IR.27}
$$

For every $s<1$ there is a nontrivial interval of distinct feasible plus
live matrices $Z_+^0(s)+\epsilon Y$. At $s=1$, the criterion instead
forces $Z=Z_+^0(1)$.

Proof. Directly from (IR.23),

$$
\Theta(Y)=\operatorname{diag}
 (0,h_1^2d^2,h_2^2d^2-h_0^2c^2)\ne0.
\tag{IR.28}
$$

Also $\Theta(Z_+^0)=(I-M+s\kappa X_{01})/2$.
For $s<1$, both $Z_+^0$ and $I-Z_+^0$ have least eigenvalue
$\delta_s=(1-s)/2>0$. Let $\mu=\min(m_1,m_2)>0$. Any

$$
0<|\epsilon|<\min\left\{
\frac{\delta_s}{\|Y\|_{\rm op}},
\frac{\mu}{2\|\Theta(Y)\|_{\rm op}}\right\}
\tag{IR.29}
$$

keeps $0\prec Z\prec I$ and
$N=M/2-\epsilon\Theta(Y)$ strictly between $0,M$ on the
$|1\rangle,|2\rangle$ support, with zero row and column at $0$.
Both norm denominators are positive by $h_0,d,h_1>0$.
Theorem 5.2 supplies finite realizations. Thus interior binary live
maps are not uniquely determined even within real coefficient matrices.

At $s=1$, $N|0\rangle=0$. The only contribution to the live $01$
effect is

$$
\Theta(Z)_{01}=bh_1 Z_{DT}+h_0a\overline{Z_{DT}},\qquad
\operatorname{Re}\Theta(Z)_{01}=\kappa\operatorname{Re}Z_{DT}.
\tag{IR.30}
$$

The record law forces $\operatorname{Re}Z_{DT}=1/2$.
The Hermitian contraction $2Z-I$ has $DT$ entry with real part one,
so that entry is exactly one. Its two corresponding column norms are
at most one and already contain an entry of squared modulus one.
All their other entries vanish. Hence
$Z_{DD}=Z_{TT}=Z_{DT}=1/2$, $Z_{DS}=Z_{TS}=0$.
The coordinate-$0$ effect condition is
$(h_0^2+b^2)/2+Z_{SS}d^2=1/2$.
Coordinate $0$ of (IR.9) is $h_0^2+b^2+d^2=1$; $d>0$ therefore
gives $Z_{SS}=1/2$. This endpoint fact agrees with RE Theorem 6.1.
It supplies no interior uniqueness premise. $\square$

## 6. The sharp universal diagonal envelope

The scalar allocation and common effect in this section reuse JR
§§36–38 under Comparison 2.5. Its proof uses the same joint determinant
and contrast constraint with arbitrary nonnegative diagonal test
weights, rather than only the three original-height averages. The full
derivation is retained to support the uncovered comparison and
perturbation arguments; these scalar laws are not counted as additional
knowledge.

**Definition 6.1 (closed coefficients at every strength).** Set
$q_{\max}=k/(1-\alpha)$. Since $k=1-\alpha-\beta>0$,
$0<q_{\max}<1$. Define

$$
(p_s,q_s)=
\begin{cases}
(k,0),&0\leq s\leq\sqrt\ell,\\
\left(k+\alpha\dfrac{\nu_s^2}{1+\nu_s^2},
\dfrac{\nu_s^2}{1+\nu_s^2}\right),&\sqrt\ell<s\leq1,
\end{cases}
\qquad
\begin{aligned}
\mathscr H_s&=(1-\beta)\ell-\alpha s^2,\\
\nu_s&=\frac{s^2-\ell}
 {s\sqrt{1-s^2}+\sqrt{\mathscr H_s}}.
\end{aligned}
\tag{IR.31}
$$

Here $\mathscr H_s\geq\beta k>0$ on $[0,1]$. The displayed denominator
is therefore positive, including at $s=1$. The strong formula extends
continuously to the threshold with $\nu_s=q_s=0$. At the endpoint,
$p_1=q_1=q_{\max}$. Throughout,

$$
0\leq q_s\leq q_{\max},\quad q_s\leq p_s<1,
\quad p_s-\alpha q_s=k.
\tag{IR.32}
$$

The assertions about the strong branch are also established in the
proof below; no root branch is chosen by a decimal approximation.

**Theorem 6.2 (original-class sharp diagonal lower bound).** For every
design of Definition 3.1 satisfying (IR.13), every positive diagonal
$\tau\in M_3$ satisfies

$$
p_H^{\rm acq}(\tau;\mathfrak F)\geq
p_H^L(\tau;\mathfrak F)\geq
\operatorname{tr}\bigl((p_sD^\dagger D+q_sT^\dagger T)\tau\bigr).
\tag{IR.33}
$$

For a positive $\sigma\in M_5$ with diagonal compression
$\tau=E^\dagger\sigma E$, the same inequality holds with that
unnormalized compression. One common finite design, supplied in §7,
attains both inequalities for all such inputs simultaneously. Thus the
right side is the exact pointwise minimum on this domain over the
entire original finite class.

Proof. Choose finite Kraus matrices for each actual encoder and each
decoder's supported live compression. After restricting the input to
$V$, their products are $L=BC$ through the same counted fibre, so
$\operatorname{rank}L\leq d_\xi$. Their rank-one Choi matrices are
positive summands of the fixed $J_*$. The positive-kernel argument of
Theorem 5.2 therefore puts each product uniquely in
$\operatorname{span}_{\mathbb C}\{D,T,S\}$. Separate these actual
products according to binary record $r$ and actual low fibres
$d_\xi\leq2$ or high fibres $d_\xi\geq3$. Their coefficient matrices
are $L_r\succeq0,H_r\succeq0$, with

$$
\sum_r(H_r+L_r)=I_3.
\tag{IR.34}
$$

The low vectors obey (IR.21). This uses arbitrary complex products and
arbitrary mixed encoders/decoders. It creates no new physically observed
Kraus tag. The supported plus failure event yields (IR.24) for
$Z_+=H_++L_+$.

For a diagonal test input we can analytically average these coefficient
matrices. Conjugation by $U_{e,n}$ acts on $(D,T,S)$ through characters

$$
C_{e,n}=\operatorname{diag}(1,en,e).
\tag{IR.35}
$$

Replace a pair of matrices indexed by $r$ by the average of
$C_{e,n}H_{enr}C_{e,n}$, and similarly for $L$, over all four signs.
Also average the result with its complex conjugate. Positivity and the
complex singular locus are invariant: the signs preserve the squares
in (IR.20), and the polynomial has real coefficients. The total identity
(IR.34) is fixed. For the binary constraints,
$\Theta(C_{e,n}ZC_{e,n})=U_{e,n}\Theta(Z)U_{e,n}^\dagger$,
$M$ is invariant, and conjugating the effect with record $enr$ gives
the required effect with record $r$. Complex conjugation also preserves
these real effects. Thus all necessary feasibility conditions survive.

For diagonal $\tau$, the matrix of pairings
$\operatorname{tr}(K_j^\dagger K_i\tau)$ is diagonal and real:
all cross products between $D,T,S$ are off-diagonal. Therefore this
average leaves the total high live cost on $\tau$ unchanged. If one
also averages the actual acquired effects by the same input
conjugations, their diagonal-input cost is unchanged and their domination
of the high live effect survives. Only analytic matrices and inequalities
are being averaged. No physical sign gate, conjugation channel or native
symmetry service is assumed or required.

In the averaged total binary matrices, the $DS,TS$ entries vanish by
the free sign remaining at fixed $en$. Opposite records have identical
diagonal entries, and their sum is $I_3$, so these entries equal $1/2$.
The $DT$ entries are real, opposite for the two records, and (IR.30)
fixes them to $rs/2$. Thus the total matrices are exactly $Z_r^0(s)$,
although the unaveraged original live maps need not be those matrices.
The averaged high and low matrices consequently have the form

$$
\begin{aligned}
H_r^{\rm av}&=\frac12
\begin{pmatrix}p&rt&0\\rt&q&0\\0&0&z\end{pmatrix},\\
L_r^{\rm av}&=\frac12
\begin{pmatrix}1-p&r(s-t)&0\\r(s-t)&1-q&0\\0&0&1-z\end{pmatrix},
\qquad 0\leq p,q,z\leq1,\quad t\in\mathbb R.
\end{aligned}
\tag{IR.36}
$$

Positivity implies
$t^2\leq pq$, $(s-t)^2\leq(1-p)(1-q)$, hence

$$
s\leq F(p,q):=\sqrt{pq}+\sqrt{(1-p)(1-q)}.
\tag{IR.37}
$$

Summing (IR.21) over all low vectors, before or after averaging, gives
$1-p\leq\alpha(1-q)+\beta(1-z)$, or

$$
p\geq k+\alpha q+\beta z.
\tag{IR.38}
$$

Let $A=\operatorname{tr}(D^\dagger D\tau)$,
$B=\operatorname{tr}(T^\dagger T\tau)$,
$C=\operatorname{tr}(S^\dagger S\tau)$. These are nonnegative and
the unchanged high live cost is $pA+qB+zC$. In the weak regime
(IR.38) already gives $pA+qB+zC\geq kA$.

For the strong regime consider $p_0(q)=k+\alpha q$ on
$0\leq q\leq q_{\max}$. It is at least $q$, with equality just at
$q_{\max}$. For fixed $q$, $F(p,q)$ is nonincreasing as $p$ increases
from $q$ to one. To check strict monotonicity along $p_0$, write
$F(p_0(q),q)=\cos(\arcsin\sqrt{p_0(q)}-\arcsin\sqrt q)$.
For $0<q<q_{\max}$ the angular gap is positive. Its derivative is
negative precisely when
$p_0(q)(1-p_0(q))>\alpha^2q(1-q)$. The difference is the affine function

$$
k\ell+\alpha(\beta-k)q.
\tag{IR.39}
$$

It is positive at zero, and at $q_{\max}$ it equals
$\beta k(1+\alpha)/(1-\alpha)>0$. Thus it is positive throughout
the interval. The continuous function $F(p_0(q),q)$ strictly increases
from $\sqrt\ell$ at zero to one at $q_{\max}$. Consequently, for
$\sqrt\ell<s\leq1$ there is a unique $q_s\in(0,q_{\max}]$ with

$$
\sqrt{(k+\alpha q_s)q_s}
 +\sqrt{(1-k-\alpha q_s)(1-q_s)}=s,
\qquad p_s=k+\alpha q_s.
\tag{IR.40}
$$

If a feasible $q<q_s$, then $q<q_{\max}$ and (IR.38) gives
$p\geq p_0(q)>q$. Monotonicity in $p$ and then in $q$ yields
$s\leq F(p,q)\leq F(p_0(q),q)<s$, a contradiction.
Hence $q\geq q_s$ and $p\geq k+\alpha q\geq p_s$.
This proves the claimed scalar lower bound for every allowed design.
It never assumes simultaneous attainment of independent scalar pieces.

For completeness, (IR.31) evaluates the unique root just used. Let
$\nu=\sqrt{q/(1-q)}$. On this angular branch (IR.40) is equivalent to
$\sqrt{p_0}=s\sqrt q+\sqrt{1-s^2}\sqrt{1-q}$. Squaring gives

$$
(1-\beta-s^2)\nu^2
 -2s\sqrt{1-s^2}\nu+(s^2-\ell)=0.
\tag{IR.41}
$$

The discriminant divided by four is $\mathscr H_s$ in (IR.31).
At the threshold the relevant root is zero. Rationalizing its smaller
branch gives exactly $\nu_s$ in (IR.31). When the leading coefficient
vanishes the same expression solves the remaining linear equation;
when it is negative the other quadratic root is negative and this is
the positive root. When it is positive the two roots are distinguished
by continuity from zero and the unique angular root on
$[0,q_{\max}]$. Indeed the branch has no collision because
$\mathscr H_s>0$, so it cannot exchange roots. Thus (IR.31) is valid
without division by that leading coefficient. At $s=1$ it gives
$\nu_1=\sqrt{k/\beta}$ and $p_1=q_1=k/(1-\alpha)$.
This also proves every range and endpoint assertion in (IR.32).

Finally the full five-mode live Choi matrix has input support $V$ and
output support $V$. Every positive live summand inherits both supports,
so each product kills $V^\perp$ and has no complement live range.
The actual high live effect is therefore supported on $V$ and its cost
on $\sigma$ depends only on $E^\dagger\sigma E$. Its acquired effect
can have further terms, but (IR.16) remains an operator inequality on
all five modes, including cross-support coherent inputs. This proves
the stated extension. At zero input all masses vanish; singular or
subnormalized diagonal inputs require no division and use the same
proof. $\square$

## 7. Actual finite common attainers

These instruments are JR Definition 38.1's attainers with the record
splitting and proportional-branch combination of Comparison 2.5. Their
common high effect is (JR.36), and their binary effect is (JR.41) with
the stated five-mode complement. The complete actual-encoder,
full-TP-decoder and reference/time proof is retained because §§8–11
use its exact branch maps. The subscript in $G_{\rm new}$ distinguishes
this shared attainer from RE's earlier comparison family, not from the
current JR attainer.

**Definition 7.1 (weak and strong live matrices).** Fix $s$ and all
following operations before the specimen arrives. In the weak regime
$0\leq s\leq\sqrt\ell$, for each $r=\pm1$ prescribe

$$
A_r=\sqrt{k/2}\,D,\qquad
B_{r,\epsilon,\zeta}=
\sqrt{\frac{1+r\epsilon s/\sqrt\ell}{8}}
 (\sqrt\ell D+\epsilon T+\zeta S),
\quad \epsilon,\zeta\in\{+1,-1\}.
\tag{IR.42}
$$

In the strong regime $\sqrt\ell\leq s\leq1$, prescribe

$$
A_r=\frac{\sqrt{p_s}D+r\sqrt{q_s}T}{\sqrt2},\qquad
B_{r,\epsilon}=
\frac{\sqrt{1-p_s}D+r\sqrt{1-q_s}T+\epsilon S}{2},
\quad\epsilon\in\{+1,-1\}.
\tag{IR.43}
$$

Use the continuous threshold values in (IR.43). Delete zero matrices
in (IR.42) before receiving any input. For each high label $(r,H)$,
use encoder $A_r$ into a three-dimensional fibre and decoder
$X\mapsto EXE^\dagger$ into live. For every nonzero displayed $B$,
use its own actually generated low label, encoder $U_B^\dagger B$
into a two-dimensional fibre, and full TP decoder
$X\mapsto EU_BXU_B^\dagger E^\dagger$, where (IR.22) fixes $U_B$.
For these $B$ matrices the $D$ coefficient is nonzero, so columns $1,2$
always give that formula.

For each $r$ and $j=1,2$, add scalar encoder
$\sqrt{m_j/2}\langle j|$ and decode a scalar $z$ to the entire
five-sector failure law $zw_\ell g(t)dt\,P_f$. On five modes compose
every supported encoder with $E^\dagger$. Add one scalar CP encoder
$A\mapsto\operatorname{tr}(Q_5A)/2$ for each $r$, decoded to
$zg(t)dt\,P_f$ at label $2$ only. This complement encoder may use the
two rows $\langle(e_0-e_4)/\sqrt2|/\sqrt2$ and
$\langle(e_1-e_3)/\sqrt2|/\sqrt2$ into a single scalar output;
its Kraus multiplicity is permanently inaccessible. No other quantum
system crosses the cut. The stated labels are acquired by enacting
these CP maps, and every other dilation system is discarded permanently.

**Theorem 7.2 (joint normalization and the whole complete channel).**
Definition 7.1 is a finite design in the original class. Its two
binary-conditioned live maps, on every complex supported $A$, are

$$
\Lambda_r^0(A)=\frac12\left[
 DAD^\dagger+TAT^\dagger+SAS^\dagger
 +rs(DAT^\dagger+TAD^\dagger)\right].
\tag{IR.44}
$$

Its conditioned failure measures are exactly half of (IR.10), including
the complement term. Consequently it has (IR.13), and its forgotten
channel is exactly (IR.10) on the full complex five-mode algebra, every
passive reference and every original labelled Borel time set.

Proof. All weak weights are nonnegative since $s/\sqrt\ell\leq1$.
Their nonzero matrices lie on the quadratic cone because
$\ell-\alpha-\beta=0$; Lemma 4.2 gives rank exactly two.
The weak $A_r$ is invertible. In the strong regime the determinant of
$A_r$ is nonzero: its coefficient expression has
$u^2-\alpha v^2=k/2>0$ and $u=\sqrt{p_s/2}>0$.
For each strong $B$, the relation
$1-p_s=\alpha(1-q_s)+\beta>0$ makes its determinant zero with
nonzero $D$ coefficient. Its rank is exactly two. Thus every stated
range compression and every dimension assignment is justified.

For weak $B$ write its nonnegative squared scalar prefactor as
$\omega_{r,\epsilon}=(1+r\epsilon s/\sqrt\ell)/8$.
Summing over both $\epsilon,\zeta$ gives coefficient entries

$$
DD=\ell/2,\quad TT=SS=1/2,\quad DT=TD=rs/2,
\quad DS=SD=TS=ST=0.
\tag{IR.45}
$$

For example $\sum_{\epsilon,\zeta}\omega_{r,\epsilon}=1/2$,
$\sum\omega_{r,\epsilon}\sqrt\ell\epsilon=rs/2$, and the terms
odd in $\zeta$ vanish. Adding $A_r$ supplies $k/2$ to $DD$, leaving
$DD=1/2$. This is exactly coefficient matrix $Z_r^0(s)$.
For strong $B$, summing its two signs cancels both $S$ cross terms.
Its diagonal coefficients plus those of $A_r$ are again all $1/2$;
its $DT$ entry is
$r[\sqrt{p_sq_s}+\sqrt{(1-p_s)(1-q_s)}]/2=rs/2$ by (IR.40).
Thus (IR.44) holds in both regimes. At $s=\sqrt\ell$, the weak
nonzero weights have $\epsilon=r$ and prefactor $1/2$, exactly the
two strong matrices; the other weak branches have zero weight.

Range compression followed by decoding multiplies to $EB$ by
$U_BU_B^\dagger B=B$. It also preserves the encoder effect:
$B^\dagger U_BU_B^\dagger B=B^\dagger B$. High branches similarly
have effect $A_r^\dagger A_r$. The supported live effect at fixed
record is therefore
$\Theta(Z_r^0)=(I-M+rs\kappa X_{01})/2$, since
$D^\dagger T+T^\dagger D=\kappa X_{01}$.
The scalar rows have effect $M/2$. Consequently the exact joint effect
identities are

$$
\sum_{\xi:r(\xi)=r}C_\xi^\dagger C_\xi
 =\frac{I_3+rs\kappa X_{01}}2,
\qquad \sum_\xi C_\xi^\dagger C_\xi=I_3
\tag{IR.46}
$$

on the supported input. The live decoders are TP on their complete
fibres because their isometries satisfy $U^\dagger U=I$. The scalar
failure decoders are TP by (IR.26), including the complement decoder
using only existing label $2$. On five modes the two complement effects
are $Q_5/2$ each, completing (IR.46) to (IR.13) and $I_5$.
Each branch is CP and its positive effect is at most $I_5$, hence TNI.
This proves joint encoder normalization, rather than assuming each
encoder branch TP.

The scalar rows give precisely
$w_\ell g(t)dt\,\operatorname{tr}(MA)/2$ on supported inputs and
$\mathbf1_{\ell=2}g(t)dt\,\operatorname{tr}(Q_5A)/2$ on the
complement. Summing (IR.44) over $r$ cancels the cross terms and gives
the fixed live map; the two scalar halves give the fixed failure map.
Compression by $E^\dagger$ and the $Q_5$ trace both kill cross-support
operators. No complementary live or extra-sector map is present.

These computations use arbitrary complex $A$: they never replace
$A_{ij}$ by $A_{ji}$ or discard its imaginary entries. On any joint
complex operator $X$ with passive reference $R$, replace every encoder
matrix and isometry by its tensor product with $I_R$. The same sum of
conjugations proves the live identity. A scalar row $C$ leaves the
actual reference operator $(C\otimes I_R)X(C^\dagger\otimes I_R)$.
Their failure sum is
$\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X]/2$;
the complement branch gives
$\operatorname{Tr}_5[(Q_5\otimes I_R)X]/2$.
For each label and each Borel $B\subseteq[0,1]$, the decoder multiplies
these operators by $\int_B g(t)dt$ and the stated $w_\ell P_f$ or
label-$2$ $P_f$. This proves equality of CP measures, including all
conditional reference states. The law has no endpoint atoms or singular
additions; the two zero-weight original labels have actual zero maps.
Every additional sector has zero map. Common metadata can be carried
identically in each branch. Thus the entire complex/reference/labelled-
time completion is (IR.10), and its canonical twelve-history error is
the credited (IR.11). Exposing a finer internal label would define a
different task, for which this error is not asserted. $\square$

**Corollary 7.3 (exact acquired-high operator and edge cases).** The
only high fibres in Definition 7.1 are the two genuinely rank-three
$A_r$ branches. Their acquired and supported live effects agree, with

$$
G_{\rm new}(s)=E(p_sD^\dagger D+q_sT^\dagger T)E^\dagger.
\tag{IR.47}
$$

For every positive five-mode $\sigma$, their mass is
$\operatorname{tr}((p_sD^\dagger D+q_sT^\dagger T)E^\dagger\sigma E)$. This one
design attains all diagonal minima in Theorem 6.2 simultaneously.

Proof. Both high decoders send their entire fibre into supported live
output, so there is no decoder trace loss. Summing $A_r^\dagger A_r$
cancels the $D,T$ cross terms and gives (IR.47), in the weak regime
as well as the strong one. Every nonzero other live fibre has dimension
two, and every failure fibre dimension one. Per record the weak design
has dimensions $3$, up to four $2$s, and three $1$s including the
complement; the strong design has $3,2,2,1,1,1$. No later accessible
share is omitted from this count. Formula (IR.47) equals the lower bound
for every diagonal compression, proving the asserted simultaneous
attainment.

At $s=0$, $r$ is a fair record independent of every input because its
effect is $I_5/2$; the finer acquired labels can still depend on input.
At the threshold the zero branches are deleted as above. At $s=1$,
$p_s=q_s=k/(1-\alpha)$, giving the common endpoint operator already
present in RE. On zero input every branch mass is zero. Positive
singular and subnormalized inputs use the same linear formulas with no
renormalization. Complement-only inputs have zero high mass and the
two complement branches give their required half/half binary record.
Cross-support coherence changes none of these effects. A joint input's
probabilities use its reduced specimen density; its full conditional
reference operators are those just proved. $\square$

## 8. Strict operator improvement of the earlier all-strength family

**Proposition 8.1 (credited comparison family and its exact effect).**
The earlier RE construction has supported high effect

$$
G_{\rm old}^{V}(s)=c_s(D^\dagger D+s^2T^\dagger T),\qquad
c_s=1-\frac{\beta}{1-\alpha s^2},\qquad
R_s=\frac{1-\alpha s^2}{\beta}>1.
\tag{IR.48}
$$

It and Definition 7.1 preserve the same binary-conditioned complete maps
of JR §§30–31, rather than only their effects. The comparison is with
RE's earlier all-strength family, not with the coincident common effect
of current JR §38.

Proof. To fix the comparison without assuming universal optimality of
that family, let $K_{r,s}=D+rsT$. Equation (IR.20) gives

$$
\det(uK_{r,s}+vS)=uh_1cd(R_su^2-v^2).
\tag{IR.49}
$$

Here $1-\alpha s^2\geq1-\alpha>\beta$, so $R_s>1$.
The matrix $K_{r,s}$ is invertible, whereas
$K_{r,s}+\epsilon\sqrt{R_s}S$ has rank exactly two. The two matrices
$B_{r,\epsilon}=(K_{r,s}+\epsilon\sqrt{R_s}S)/(2\sqrt{R_s})$
satisfy, on all complex $A$,

$$
\sum_\epsilon B_{r,\epsilon}AB_{r,\epsilon}^\dagger
 =\frac{K_{r,s}AK_{r,s}^\dagger}{2R_s}+\frac{SAS^\dagger}{2}.
\tag{IR.50}
$$

The opposite $K,S$ cross terms cancel. Add high matrix
$\sqrt{(R_s-1)/(2R_s)}K_{r,s}$, and low residual matrix
$\sqrt{(1-s^2)/2}T$. Compress each rank-two range with (IR.22)
or the range isometry $(|1\rangle,|0\rangle)$ for $T$. Their full
TP live decoders recover those matrices. Add the same scalar failure
and complement branches as in §7. Then (IR.50) gives

$$
\frac12\left[K_{r,s}AK_{r,s}^\dagger
 +(1-s^2)TAT^\dagger+SAS^\dagger\right]=\Lambda_r^0(A).
\tag{IR.51}
$$

The effect sum, full TP scalar decoding and joint reference/time
identities follow directly as in (IR.46) and Theorem 7.2, since the
composite matrices and failure maps are precisely the same. This
recovers the actual RE design, including the omitted zero residual
$T$ at $s=1$. Its only high matrices are the stated $K_{r,s}$ multiples;
their effect sum is (IR.48). This verifies the consumed comparison
identity without importing an endpoint pointwise formula. $\square$

**Theorem 8.2 (strict positive-operator saving).** For every $0\leq s<1$,

$$
G_{\rm old}^{V}(s)-(p_sD^\dagger D+q_sT^\dagger T)\succ0.
\tag{IR.52}
$$

At $s=1$ these two operators are equal. At every $s\in[0,1]$ the
shared operator of §7 and current JR §38 is strictly below the original
JR §§30–31 family's supported high effect
$D^\dagger D+s^2T^\dagger T$. Hence the saving is strict on every
positive five-mode input whose supported compression is nonzero.

Proof. Write $p_c=c_s$, $q_c=s^2c_s$. The comparison construction's
high and low coefficients have precisely form (IR.36) with $z=0$,
so the scalar necessity argument of Theorem 6.2 gives $q_c\geq q_s$.
In the weak regime this also follows from $q_s=0$ directly.
Moreover

$$
p_c-\alpha q_c=1-\alpha s^2-\beta
 =k+\alpha(1-s^2).
\tag{IR.53}
$$

Since $p_s=k+\alpha q_s$, for $s<1$,
$p_c-p_s=\alpha(q_c-q_s)+\alpha(1-s^2)>0$.
The difference in (IR.52) is therefore
$(p_c-p_s)D^\dagger D+(q_c-q_s)T^\dagger T$, positive definite
because $D$ is invertible. At $s=1$ both coefficient pairs equal
$(k/(1-\alpha),k/(1-\alpha))$.

The original JR §§30–31 family's effect minus RE's older effect is
$(D^\dagger D+s^2T^\dagger T)/R_s\succ0$ for every strength.
Adding the nonnegative old-minus-new difference, or using equality at
$s=1$, proves strict saving relative to that original JR family
throughout. A positive definite supported operator has positive trace against every nonzero
positive supported compression, including singular ones. On
$V^\perp$ all three explicit high effects are zero. Binary relabeling
proves the same claims for negative record coefficients. This comparison
is an operator theorem about explicit designs; it does not assert a
universal coherent-input minimum for the new design. $\square$

## 9. Exact original sign averages and a common Pareto point

The sharp averages are JR Theorem 37.2's $P_y(s)$, attained by its
§§38–39 instrument, with $P_y(s)=g_y(s)$ under Comparison 2.5.
JR proves them for every error optimizer in its larger actual
factorization class. Theorem 9.1 records their fixed-channel finite
specialization. The Pareto point of Theorem 9.2 follows directly from
these credited averages and is not additional knowledge. Neither result
gives an individual coherent-history minimum or the whole frontier.

**Theorem 9.1 (sharp four-sign laws at all three heights).** Define

$$
g_y(s)=p_s\sum_{i=0}^2h_i^2p_{yi}
 +q_s\left(b^2\frac y{128}+a^2\frac{64-y}{128}\right).
\tag{IR.54}
$$

For every original design and each $y\in\{5,16,27\}$,

$$
\frac14\sum_{e,n=\pm1}
 p_H^{\rm acq}(\rho_{y,e,n};\mathfrak F)\geq g_y(s).
\tag{IR.55}
$$

One common design, Definition 7.1, attains all three inequalities, with
value $g_y(s)$ separately on each of the four signs at that height.
These are exact inequalities among original conditional laws, with no
source prior and no averaged-to-individual lower-bound inference.

Proof. The signs in (IR.2) cancel each off-diagonal entry, giving the
linear identity

$$
\frac14\sum_{e,n}\rho_{y,e,n}=\operatorname{diag}(p_y).
\tag{IR.56}
$$

Each actual acquired high probability is a linear functional of the
input. Thus its four-sign mean is its value on this diagonal matrix.
Apply Theorem 6.2 to that matrix, and evaluate the diagonal operator
$p_sD^\dagger D+q_sT^\dagger T$ to obtain (IR.54)–(IR.55).
The same operator is the acquired effect of Definition 7.1, and its
value is independent of $e,n$. This proves simultaneous equality with
one actual finite common instrument, without any selection of history
or independently chosen output laws. All twelve original inputs and
their full canonical targets remain prescribed. $\square$

**Theorem 9.2 (twelve-coordinate Pareto optimality).** The vector with
four entries $g_y(s)$ at each original height is Pareto optimal among
all allowed designs for every $s\in[0,1]$: no design weakly reduces
all twelve coordinates and strictly reduces at least one.

Proof. A strictly reduced coordinate belongs to one fixed height.
If all four coordinates there are at most $g_y(s)$, and at least one
is smaller, their mean is below $g_y(s)$, contradicting (IR.55).
This compares the original twelve resource coordinates without choosing
a scalar objective or a distribution on histories. In the interior,
(IR.55) supplies no two-history beta-pair inequality and no individual
coherent-input lower bound $g_y(s)$. The next section explicitly
improves each selected individual coordinate. $\square$

## 10. Finite null decompositions and lawful interior perturbations

**Lemma 10.1 (real zero-trace decomposition).** Let
$B_0=\operatorname{diag}(1,-\alpha,-\beta)$. Every real symmetric
$L\succeq0$ with $\operatorname{tr}(B_0L)=0$ has a decomposition

$$
L=\sum_{j=1}^t z_jz_j^T,\qquad t\leq3,
\qquad z_j^TB_0z_j=0.
\tag{IR.57}
$$

All nonzero vectors here give genuine rank-two matrices
$K(z_j)$. When $\Theta(L)\preceq I$, this decomposition gives
actual CP/TNI low-fibre acquisition branches with the range encoders
(IR.22) and full TP live decoders. The remaining branches of a complete
design must still supply the complementary effect.

Proof. Factor $L=BB^T$ using its real positive square root, allowing
zero columns. The real symmetric matrix $A=B^TB_0B$ has trace zero.
We claim it has an orthonormal basis with every diagonal Rayleigh
value zero. If $A=0$, any basis works. Otherwise a real symmetric
nonzero trace-zero matrix has positive and negative eigenvalues.
For unit eigenvectors $e_+,e_-$ with eigenvalues
$\lambda_+>0>\lambda_-$, the unit vector

$$
f=\frac{\sqrt{-\lambda_-}\,e_+
 +\sqrt{\lambda_+}\,e_-}{\sqrt{\lambda_+-\lambda_-}}
\tag{IR.58}
$$

has $f^TAf=0$. Extend it to an orthonormal basis. The compression to
$f^\perp$ still has trace zero because the removed diagonal entry is
zero. Induction on its dimension produces the claimed basis, also
when an intermediate compression is the zero matrix. If $O$ has
these basis columns, the columns $z_j$ of $BO$ give (IR.57).
There are at most three, and zero columns are removed. This proves a
finite decomposition, including rank-zero $L$.

For a real null vector $(u,v,w)\ne0$, the identity
$u^2=\alpha v^2+\beta w^2$ and $\alpha,\beta>0$ force $u\ne0$.
Lemma 4.2 makes $K(z_j)$ rank exactly two. For each actual label $j$
use encoder $U_{K(z_j)}^\dagger K(z_j)$ and TP decoder by
$EU_{K(z_j)}$. Their coefficient sum is exactly $L$, their effects
are $K(z_j)^\dagger K(z_j)$, and their complex/reference composite
maps are exactly $\Lambda_L$. Their total encoder effect is
$\Theta(L)$. Under the stated effect bound every individual positive
effect is at most $I$, so these are lawful CP/TNI acquisition branches.
The jointly normalized uses below supply all remaining branches. An
arbitrary unbounded $L$ asserts only the algebraic decomposition, not
a normalized acquisition instrument. The decomposition in its bounded
uses is therefore turned into specified finite CP operations and
acquired labels, rather than treated as a preexisting observable flag. $\square$

**Proposition 10.2 (rank-one high branch and exact feasibility ellipse).**
For $s<1$, retain the total binary live matrices $Z_r^0(s)$ and the
half-weight failure maps. For real $x,z$ put

$$
v=(1,x,z)^T,\qquad
\delta(x,z)=1-\alpha x^2-\beta z^2,\qquad
\theta(x,z)=\frac{k}{2\delta(x,z)},\qquad
H_r=\theta(x,z)vv^T.
\tag{IR.59}
$$

When $\delta(x,z)>0$, this is a feasible high coefficient matrix
$H_r\preceq Z_r^0(s)$ if and only if

$$
A_s x^2-2krsx+(s^2-\ell)+B_s z^2\leq0,
\qquad
A_s=1-\beta-\alpha s^2>0,\quad
B_s=(1-\alpha)(1-s^2)>0.
\tag{IR.60}
$$

Every such point has an actual finite common realization with high
matrix $\sqrt\theta(D+xT+zS)$ for this record, at most three low
matrices for its residual, and the same conditioned complete output.

Proof. $Z_r^0(s)\succ0$ for $s<1$. For any positive definite $Z$,
$\theta vv^T\preceq Z$ is equivalent to
$\theta v^TZ^{-1}v\leq1$: conjugate by $Z^{-1/2}$ and use the
single nonzero eigenvalue of the rank-one matrix. Here the inverse of
the $D,T$ block is
$2(1-s^2)^{-1}\left(\begin{smallmatrix}1&-rs\\-rs&1\end{smallmatrix}\right)$,
and the $S$ inverse entry is $2$. The condition becomes

$$
k\left(\frac{1-2rsx+x^2}{1-s^2}+z^2\right)
 \leq1-\alpha x^2-\beta z^2.
\tag{IR.61}
$$

Multiplying by the positive $1-s^2$ and collecting terms yields
(IR.60). Its two coefficients are positive since $A_s\geq k>0$
and $s<1$.

The residual $L_r=Z_r^0-H_r$ is real positive and has
$\operatorname{tr}(B_0L_r)=k/2-\theta\delta=0$. Its encoder effect
is at most $\Theta(Z_r^0)\preceq I$, because $\Theta$ preserves
positive order and the remaining record and failure effects are positive.
Lemma 10.1 therefore supplies at most three rank-two low matrices and their
actual two-dimensional encoders and TP decoders. The high matrix is
invertible because its determinant is
$\theta^{3/2}h_0h_1h_2\delta\ne0$. Use it as encoder into a
three-dimensional fibre with live decoder $E$. For the other record
use any fixed feasible split, in particular Definition 7.1. Add the
scalar half failures and complement branches from §7. Both records
retain $Z_r^0$, so the same coefficient, effect and scalar-map sums
prove joint normalization, (IR.13), and exactly (IR.44) and (IR.10).
Theorem 7.2's tensor-Kraus and Borel-set argument applies verbatim to
these specified matrices: it preserves the full complex/reference map,
each original time measure, complement and cross-support action and
zero extra sectors. Only the actual fibre and generated label are
retained. The high acquisition mass equals its high live mass. $\square$

**Proposition 10.3 (an explicit perturbation through every interior base).**
For every $s<1$ and either record, the high branch of Definition 7.1
lies on a lawful two-sided curve of (IR.59) for which the $S$
coefficient is $z$, the $T$ coefficient is $x_r(z)$ with
$x_r'(0)=0$, and $\theta'(0)=0$.

Proof. If $s<\sqrt\ell$, take $x_r(z)=0$. The base has
$\theta(0)=k/2$, and (IR.60) is strict at zero. Explicitly any

$$
|z|<\frac12\min\left\{\frac1{\sqrt\beta},
 \sqrt{\frac{\ell-s^2}{B_s}}\right\}
\tag{IR.62}
$$

has positive denominator and satisfies the ellipse strictly. This
includes $s=0$. Its dependence on $z$ is even, so $\theta'(0)=0$.

For $\sqrt\ell\leq s<1$, put

$$
\Delta_s=(1-s^2)\mathscr H_s>0,\qquad
x_r(z)=r\frac{ks-\sqrt{\Delta_s-A_sB_sz^2}}{A_s}.
\tag{IR.63}
$$

The identity $k^2s^2-A_s(s^2-\ell)=\Delta_s$ shows that this
curve is on the boundary of (IR.60). At $z=0$ it is the root of smaller
absolute value. It equals $r\sqrt{q_s/p_s}$: the latter solves the
same boundary equation, starts at zero at the threshold, and varies
continuously without a root collision since $\Delta_s>0$ for $s<1$.
Thus $\theta(0)=p_s/2$, the new high matrix's coefficient.
At the threshold $\sqrt{\Delta_s}=ks$, so (IR.63) also starts at
$x_r(0)=0$, with no singular branch choice.

Here is an explicit nonempty interval that also controls the denominator.
Let $\delta_0=k/p_s>0$ and set

$$
\varepsilon_s^2=\min\left\{
\frac{\Delta_s}{2A_sB_s},\quad
\frac{\sqrt{\Delta_s}}{B_s},\quad
\frac{\delta_0}{2(\beta+3\alpha B_s/\sqrt{\Delta_s})}
\right\}>0.
\tag{IR.64}
$$

For $|z|<\varepsilon_s$, the radical in (IR.63) is positive.
Rationalizing its difference from the value at zero gives

$$
|x_r(z)-x_r(0)|=
\frac{B_sz^2}{\sqrt{\Delta_s}+\sqrt{\Delta_s-A_sB_sz^2}}
 \leq\frac{B_sz^2}{\sqrt{\Delta_s}}<1.
\tag{IR.65}
$$

Since $|x_r(0)|=\sqrt{q_s/p_s}\leq1$, it follows that
$|x_r(z)^2-x_r(0)^2|\leq3B_sz^2/\sqrt{\Delta_s}$.
Consequently
$\delta(x_r(z),z)\geq\delta_0-
(\beta+3\alpha B_s/\sqrt{\Delta_s})z^2>\delta_0/2>0$.
Thus this entire interval is lawful. Formula (IR.63) is differentiable
and even in $z$ there, so $x_r'(0)=0$ and $\theta'(0)=0$.
This treats both sides of the threshold and every interior strength;
no $s=1$ inverse is used. $\square$

**Theorem 10.4 (strict improvement at each original input and mate reversal).**
For every $s<1$ and every original individual input, there exists another
finite common design with the same JR binary-conditioned complete
channels and strictly smaller acquired high mass at that input than
$g_y(s)$. Its mass on the original beta-mate is strictly larger than
$g_y(s)$ for a sufficiently small chosen perturbation.

Proof. Fix a real original $\rho=\rho_{y,e,n}$, and write
$x_r^0=0$ in the weak regime and
$x_r^0=r\sqrt{q_s/p_s}$ in the strong regime. Let
$\theta_0=k/2$ or $p_s/2$, respectively. On the curve of Proposition
10.3 the derivative of this record's high probability at zero is

$$
2\theta_0\,\mathcal U_r(\rho),\qquad
\mathcal U_r(\rho)=
\operatorname{Re}\operatorname{tr}((D+x_r^0T)^\dagger S\rho)
=(h_0c+h_2d)\rho_{02}+x_r^0ac\rho_{12}.
\tag{IR.66}
$$

The derivatives of $x,\theta$ vanish, leaving precisely the two $S$
cross terms. The displayed expression follows by multiplying $D^\dagger S$
and $T^\dagger S=ac|1\rangle\langle2|$.
On the actual inputs,
$\rho_{02}=e\sqrt y/16\ne0$ and
$\rho_{12}=n\sqrt{64-y}/16$. Since $x_-^0=-x_+^0$,

$$
\mathcal U_+(\rho)+\mathcal U_-(\rho)
 =2(h_0c+h_2d)\rho_{02}\ne0.
\tag{IR.67}
$$

Thus at least one record has nonzero derivative. Perturb only that
record on its lawful curve, with a sufficiently small $z$ opposite
the sign of $\mathcal U_r$. The definition of a nonzero derivative
ensures strict reduction in that input's high probability; the other
record is unchanged. The null-decomposition encoders in Proposition
10.2 give an actual complete finite design for every such chosen $z$.

The unitary $W=\operatorname{diag}(-1,-1,1)$ sends this original input
to its other $\beta_{\rm hist}$ at the same $y,m$. It commutes with
$D,T$ and anticommutes with $S$. Therefore the derivative in (IR.66)
reverses sign on $W\rho W^\dagger$, while both base costs are $g_y(s)$.
For the same sufficiently small signed $z$ the beta-mate's cost strictly
increases. The constants are chosen using the fixed public test input
before execution; the resulting instrument is common on every unknown
input. It neither reads $y,e,n$ nor grants a parity sensor. $\square$

**Corollary 10.5 (no simultaneous pointwise optimum or least vector).**
For every interior $0\leq s<1$ there is no original-class design attaining
all twelve individual pointwise resource infima. There is no universally
least twelve-coordinate resource vector, and no common design attaining
the pointwise minimum on every supported input.

Proof. Theorem 10.4 puts each original individual infimum strictly below
its coordinate of the Pareto vector in Theorem 9.2. A design attaining
all these infima would strictly reduce every coordinate of that Pareto
vector, which is impossible. This reasoning does not assume that the
individual infima have already been evaluated or attained.

If a universally least vector existed, it would lie coordinatewise below
the common Pareto vector and hence equal it by Pareto optimality. But
it would also lie below the design in Theorem 10.4 that strictly reduces
one selected coordinate, a contradiction. An all-input simultaneous
attainer would in particular attain all twelve infima, so is excluded.
Individual pointwise attainment is established separately in §11. At
$s=1$ RE already supplies the stronger endpoint beta-pair obstruction;
that endpoint result is not used to infer interior rigidity or an
interior pair lower law. $\square$

## 11. The exact compact reduction for arbitrary complex inputs

**Definition 11.1 (the full singular coefficient cone).** Let

$$
\begin{aligned}
\mathcal C_2=\Bigl\{\sum_{j=1}^t z_jz_j^\dagger:
&t<\infty,\ z_j=(u_j,v_j,w_j)\in\mathbb C^3,\\
&u_j(u_j^2-\alpha v_j^2-\beta w_j^2)=0\Bigr\}.
\end{aligned}
\tag{IR.68}
$$

The empty sum is zero. This cone includes all complex phases and the
entire plane $u=0$. The real zero-trace cone of Lemma 10.1 is useful
for the explicit perturbation, but is not substituted for $\mathcal C_2$.
Let $\mathcal K_s$ be the set of four Hermitian coefficient matrices
satisfying

$$
\begin{gathered}
H_+,H_-\succeq0,\qquad L_+,L_-\in\mathcal C_2,\\
H_++H_-+L_++L_-=I_3,\\
0\preceq N:=\frac{I_3+s\kappa X_{01}}2
 -\Theta(H_++L_+)\preceq M.
\end{gathered}
\tag{IR.69}
$$

For a positive supported test input $\rho$ define the finite variational
quantity

$$
\mathsf E_s(\rho)=\min_{\mathcal K_s}
 \operatorname{tr}\bigl(\Theta(H_++H_-)\rho\bigr).
\tag{IR.70}
$$

Existence of the displayed minimum is proved below. The notation
$\mathsf E_s$ is a resource quantity, distinct from the complete-output
error $\mathcal E$ in (IR.6). Formula (IR.70) is an exact characterization,
not an evaluated closed law for general coherent inputs.

**Lemma 11.2 (closedness, compactness and finite cone representations).**
Every element of $\mathcal C_2$ is a sum of at most nine singular
rank-one coefficient matrices. Each bounded-trace part of this cone is
compact; in particular the cone is closed. The set $\mathcal K_s$ is
nonempty and compact for every $s\in[0,1]$.

Proof. Intersect the singular polynomial locus in (IR.68) with the unit
sphere of $\mathbb C^3$, considered as a finite real Euclidean space.
It is closed and bounded, hence compact. Its projectors $zz^\dagger$
form a compact set $\mathscr S$ in the trace-one Hermitian affine
space, whose real dimension is eight. A finite convex combination
with more than nine nonzero weights has affinely dependent projectors:
there are real $c_j$, not all zero, with
$\sum_jc_j=0$ and $\sum_jc_jP_j=0$. Both signs occur among the
$c_j$. Subtract from the weights $\lambda_j$ the multiple
$\min_{c_j>0}(\lambda_j/c_j)c_j$. This preserves the represented
matrix and total weight, keeps all weights nonnegative and removes
at least one. Repetition yields at most nine projectors.

The convex hull of $\mathscr S$ is consequently the continuous image
of the compact product of a nine-point simplex and $\mathscr S^9$,
with zero weights and repeated projectors allowed. It is compact.
Every nonzero cone element divided by its trace is in that hull,
since $\operatorname{tr}(zz^\dagger)=\|z\|^2$. Conversely every
positive multiple of a hull element is in the cone, by absorbing
weights into singular vectors; the locus is homogeneous. Thus the
trace-at-most-$T$ part is the compact image
$[0,T]\times\operatorname{conv}\mathscr S$ under multiplication,
including zero. A convergent sequence of cone matrices has bounded
traces, so its limit belongs to such a compact slice. This proves
closedness and the nine-term representation, with coefficients
absorbed into vectors. Nonzero represented singular matrices have
rank two by Lemma 4.2.

Every variable in (IR.69) is positive and bounded above by $I_3$,
so its trace is at most three and its norm is bounded. Membership in
the closed cone, the total coefficient identity, and both $N$
inequalities are closed conditions. The feasible set is therefore
closed and bounded in a finite real vector space, hence compact.
The instruments of §7 provide feasible coefficient matrices, proving
nonemptiness at every strength, including both endpoints. $\square$

**Theorem 11.3 (necessity from every original finite implementation).**
For every original design there is a point of $\mathcal K_s$ for
which, as a five-mode operator inequality,

$$
G_H^{\rm acq}(\mathfrak F)\succeq
 E\Theta(H_++H_-)E^\dagger=G_H^L(\mathfrak F).
\tag{IR.71}
$$

In particular every original pointwise resource cost is at least
$\mathsf E_s(E^\dagger\sigma E)$, and every original twelve-vector
is weakly dominated by the corresponding coefficient cost vector.

Proof. Refine a finite acquired label by its binary postprocessing coin
if required. Its fibre dimension is unchanged, and it is still an
actually enacted finite instrument. Choose finite Kraus matrices of its
encoders and of their supported live-decoder compressions. Each product
is a positive Choi summand of the fixed whole live Choi matrix.
Domination forces its output support and input support into $V$.
Thus its full five-mode live product has the form $EK(z)E^\dagger$
for a unique complex coefficient vector $z$, with the evident output
embedding; in supported coordinates it is $K(z)$.

For each binary record sum $zz^\dagger$ over products through actual
high fibres to obtain $H_r\succeq0$, and through low fibres to obtain
$L_r$. A product through a low fibre has rank at most two. Lemma 4.2
therefore puts its coefficient vector on precisely the singular locus
in (IR.68), including the plane as well as the quadratic cone. Hence
$L_r\in\mathcal C_2$. Summing the actual live products gives the
fixed live Choi matrix. The injectivity of $\mathcal V$ makes its
coefficient identity exactly the sum $I_3$ in (IR.69).

The total plus record effect minus its supported live effect is its
actual supported failure effect. Summing the entire original failure
register gives $0\preceq N\preceq M$ as in Theorem 5.2. This remains
true for whatever time or label splitting the actual design uses;
it does not enforce the chosen half-density split. Consequently the
four matrices are feasible. The full high live input effect is the
embedded coefficient effect in (IR.71). Full TP of each actual decoder
and live TNI prove (IR.71) before any input evaluation, on all five
modes. In particular it includes possible high acquired mass that later
fails, and any acquired effect involving the complementary input.
Taking a trace against any positive $\sigma$, with cross-support
coherence allowed, proves the bound. Taking the twelve original
expectations gives the asserted coordinatewise domination. No
restriction to real, covariant, pure or isometric original operations
has entered this necessity proof. $\square$

**Theorem 11.4 (full finite sufficiency and legitimate reassignment).**
Every feasible point of $\mathcal K_s$ has an actual finite common
realization of the complete fixed channel and binary law. It can be
realized with acquired high effect exactly $E\Theta(H_++H_-)E^\dagger$
using at most thirty branches and fibres of dimensions at most three.
Alternatively every singular high atom can be reassigned to low,
weakly lowering that effect. After reassignment there is a realization
with the same branch bound and only genuinely rank-three high branches.

Proof. Factor each $H_r$ spectrally as a sum of at most three vectors
$h_{rj}h_{rj}^\dagger$. For each nonzero vector supply encoder matrix
$K(h_{rj})$ into a declared three-dimensional fibre and live TP decoder
$X\mapsto EXE^\dagger$. This realizes its exact coefficient atom and
counts its entire acquisition effect as high. This literal realization
is permitted even if a matrix happens to be singular: the prescribed
carrier is three-dimensional. No assertion of minimal carrier dimension
for that individual branch is made. The compression variant below
removes all such unnecessary high dimensions.

Decompose each $L_r$ into at most nine singular atoms using Lemma 11.2.
Every nonzero atom gives a rank-two matrix $K(z)$, even for a complex
plane direction. Supply encoder $U_{K(z)}^\dagger K(z)$ into its
fixed two-dimensional range and full TP live decoder by $EU_{K(z)}$.
Formula (IR.22) supplies these isometries for $u\ne0$, for $u=0,v\ne0$,
and for $u=v=0,w\ne0$, so no singular direction is omitted. The
products and effects are exactly $EK(z)$ and $K(z)^\dagger K(z)$.
All displayed labels are outputs of these specified encoders.

Let $N_+=N$ and $N_-=M-N$. Positivity and domination by $M$ make
both effects kill $|0\rangle$; each has rank at most two. For each
of its at most two positive spectral eigenvalues $\lambda_{rj}$ and
unit eigenvectors $v_{rj}$, supply scalar row
$\sqrt{\lambda_{rj}}\langle v_{rj}|$ with label $(r,f,j)$.
Its full TP decoder sends scalar $z$ to
$zw_\ell g(t)dt\,P_f$ in the five original sectors. On five-mode
inputs precompose all supported encoders with $E^\dagger$. Add one
scalar complement encoder $A\mapsto\operatorname{tr}(Q_5A)/2$ per
record, decoded to $zg(t)dt\,P_f$ at original label $2$. It is one
acquired scalar branch, although its inaccessible Kraus multiplicity
can have two rows.

The supported effect sum at record $r$ is
$\Theta(H_r+L_r)+N_r$. For plus this is the required supported
$F_+(s)$ by (IR.69). Subtracting it from
$\Theta(I)+M=I_3$ gives the required minus effect. After adding the
complement halves the binary law is (IR.13). Total encoder normalization
is exactly

$$
E\bigl[\Theta(H_++H_-+L_++L_-)+N_++N_-\bigr]E^\dagger+Q_5
 =E[\Theta(I)+M]E^\dagger+Q_5=I_5.
\tag{IR.72}
$$

Every encoder is CP/TNI because its positive effect is bounded by this
joint sum. Every live decoder is isometric and TP on its entire
carrier. Every scalar decoder is TP by (IR.26). The coefficient sum
gives the fixed live channel; the two failure effects sum to $M$ and
the complement halves to $Q_5$, giving exactly (IR.10). The chosen
binary failure density is $w_\ell g(t)N_r$, which is sufficient;
necessity never asserted that all compatible designs use this split.

At passive reference amplification the scalar rows sum to
$\operatorname{Tr}_5[(EN_rE^\dagger\otimes I)X]$ in record $r$,
and the complement branch retains
$\operatorname{Tr}_5[(Q_5\otimes I)X]/2$. Multiplication by each
$w_\ell\int_Bg(t)dt\,P_f$, or by the label-$2$ complement measure,
gives equality on every original labelled Borel set. Tensoring each
live Kraus and range isometry with identity proves the complex live
identity. Both constructions kill cross-support input operators,
introduce no endpoint atoms or singular addition, retain both named
zero-weight labels with zero maps and introduce no extra-sector map.
These statements prove the complete joint operation, including
entangled references, rather than only scalar effects. All high
decoders are wholly live, so the literal acquired effect is exactly the
objective coefficient effect.

For reassignment, take any singular nonzero high spectral atom
$zz^\dagger$. Replace $H_r$ by $H_r-zz^\dagger$ and $L_r$ by
$L_r+zz^\dagger$. Both remain positive, the new $L_r$ is in the
cone, and $H_r+L_r$, all $N$ constraints and the complete channel are
unchanged. Its high effect decreases by $K(z)^\dagger K(z)\succeq0$.
Remove all singular atoms of the chosen spectral high decompositions,
then decompose the resulting low matrix afresh into at most nine atoms.
The remaining high atoms are genuinely rank three. At most three high
atoms remain per record; deleting others does not increase that count.
This is a change of specified encoders and acquired labels to a new
lawful design, not an assumption that an original high hardware flag
was already a low one.

In either version there are per record at most three high live branches,
nine low live branches, two scalar supported-failure branches and one
scalar complement branch. Thus the full five-mode instrument has at
most

$$
2(3+9+2+1)=30
\tag{IR.73}
$$

actual acquisition branches. Zero atoms and zero eigenvalues are
omitted. Every retained fibre has dimension $3,2$ or $1$; other dilation
systems are permanently inaccessible. The branch count does not count
original failure times as a finite alphabet: each scalar decoder still
outputs the entire prescribed continuous-time measure. $\square$

**Theorem 11.5 (exact pointwise minimum and finite attainment).** For every
positive five-mode test input $\sigma$,

$$
\min_{\mathfrak F\ \mathrm{original\ finite\ class}}
 p_H^{\rm acq}(\sigma;\mathfrak F)
 =\mathsf E_s(E^\dagger\sigma E).
\tag{IR.74}
$$

The same equality holds with $p_H^L$ as objective. For each test input
there is one common input-independent attaining design with at most
thirty actual branches, fibre dimensions at most three, and no high
acquisition loss to nonlive output.

Proof. Theorem 11.3 gives the lower bound for every original design.
Lemma 11.2 gives compact nonempty $\mathcal K_s$ and the objective is
continuous, so a minimizing coefficient point exists. Its literal
realization in Theorem 11.4 attains the value. If any high spectral atom
there is singular, its reassignment cannot decrease the chosen positive
objective strictly: a strict decrease would produce another feasible
coefficient point below the minimum. Thus every such reassignment
preserves this chosen value. The final realization has only genuine
rank-three high branches, the bound (IR.73), and all high acquisition
is live. This proves equality and attainment for both objectives.

This uses the unnormalized compression even if $\sigma$ has complement
mass or cross-support coherence. The constructed high effect is
supported on $V$ and has no such extra cost; necessity used the full
operator domination (IR.71). A zero compression gives minimum zero,
attained with the scalar complement completion. Zero input, singular
compression and subnormalized inputs all use continuity and linear
homogeneity; there is no inverse of a density or acceptance probability.
Rank-zero $N_r,H_r,L_r$ simply contributes no branch.

The quantifier is $\forall\sigma\succeq0\ \exists\mathfrak F_\sigma$:
constants can be selected from a fixed public test state for this
mathematical optimization, and the resulting operations are common on
every unknown input. It is not $\exists\mathfrak F\ \forall\sigma$.
Corollary 10.5 excludes the latter already on the twelve original
inputs in the interior. This theorem evaluates no new coherent-input
closed formula; it proves an exact finite reduction and existence.
$\square$

**Theorem 11.6 (exact undominated-vector correspondence).** Define the
compact coefficient image

$$
\mathscr W_s=\left\{
 \left(\operatorname{tr}(\Theta(H_++H_-)\rho_{y,e,n})\right)_{y,e,n}
 : (H_+,H_-,L_+,L_-)\in\mathcal K_s\right\}\subset\mathbb R^{12}.
\tag{IR.75}
$$

The Pareto frontier of original acquired-high twelve-vectors is exactly
the undominated part of $\mathscr W_s$. Every such frontier vector has
an actual realization with at most thirty branches, dimensions at most
three and only genuinely rank-three high branches.

Proof. The image is compact by Lemma 11.2 and continuity. Its literal
realizations in Theorem 11.4 show every vector in $\mathscr W_s$ is
an original achievable vector. Theorem 11.3 gives, below every original
vector, a vector of $\mathscr W_s$. If an original vector is
undominated, this dominator must equal it, and it must be undominated
in the smaller set too. Conversely if an undominated member of
$\mathscr W_s$ were strictly dominated by an original design, that
design would have its own coefficient dominator in $\mathscr W_s$,
a contradiction. This proves both directions without scalarizing
resource coordinates.

A singular high spectral atom can be reassigned as above, decreasing
all coordinates weakly. Its nonzero effect $K^\dagger K$ strictly
decreases at least one original coordinate: at any height
$\operatorname{diag}(p_y)\succ0$, and
$\frac14\sum_{e,n}\operatorname{tr}(K^\dagger K\rho_{y,e,n})
=\operatorname{tr}(K^\dagger K\operatorname{diag}(p_y))>0$.
Thus an undominated coefficient vector cannot retain any nonzero
singular atom in its spectral high realization: reassignment would
produce a strict coefficient dominator. Theorem 11.4 therefore gives
the asserted genuine finite frontier realization. This is an exact frontier correspondence,
not a classification of which feasible matrices are undominated.
The common point in §9 is one member; absence of a least vector does
not preclude the other minimal vectors. $\square$

## 12. Attribution, remaining mathematics and native obligations

**Convention 12.1 (content and credit map).** The scalar allocation,
diagonal/common-attainer laws and sharp four-sign averages reuse JR
§§34–39; the common Pareto point is a consequence of those laws.
The uncovered `repo-derived` ordinary deductions relative to the supplied
theory bodies are the exact binary-live criterion and interior freedom
in §5, the strict earlier-RE operator comparison in §8, the lawful
individual-input perturbations and mate conflict in §10, and the full
complex compact coefficient reduction, finite attainment and frontier
correspondence in §11. The supplied interior proposal and its independent
assessment receive credit for this package, including their overlapping
derivations. Their conclusions, including an approval, are fallible
evidence rather than proof premises. The ordinary proofs and complete
instruments in this volume carry the asserted conditional implications;
no worldwide priority or literature absence is asserted.

| Supplier or mature mechanism | Precise reuse and boundary |
| --- | --- |
| CG §§1–7 and its credited Acquired Continuation Limits, FiniteRectangleTransport, OriginalControlComposition and Instrument Boundaries suppliers | Same preparation, signed real histories, positive old cut masses, legal continuation and full original targets. Their nested regularity, synthesis and calibrated-instrument conditions remain premises. |
| CG §§8–12 | Common-channel attainment and separate upper processors for the original error objective, rather than new resource bounds here. |
| CG §§13–17 | Exact point specification, arithmetic inequalities, exact normalization, minimax benchmark and averaged-live rigidity. None is newly certified; averaged rigidity does not imply whole-channel uniqueness. |
| CG §§18–20 | Restricted Schur obstruction, same-effects/different-successor example and conditional synthesis interface. They do not classify the whole native menu. |
| CG §§21–25 | Actual finite jointly counted cut, homogeneous Schmidt bottleneck, nonsharp every-input high-mass necessity and unmixed sufficient factorization. The actual-tag, full-decoder and no-bypass requirements are retained. |
| CG §§26–28 | Near-optimal averaged-live stability and its resource/transfer penalties with the original conditional constant, unchanged here. |
| JR §§29–33 | Exact $D,T,S,M,\kappa$ dictionary, binary winding laws, original finite family, full complex/reference/time completion and sharp compatible binary ceiling. Only the resource curve of that original family lacked a universality claim; current JR §§34–40 supply the sharp universal scalar comparison. |
| JR §§34–40 | Positive determinant parameters and joint low-rank/record constraint; sharp scalar cost, common finite attainer, all three original-height averages, plateau, endpoints and inverse budget. Comparison 2.5 identifies the coefficients and actual instruments exactly. The worst-history law holds over every error optimizer, including the stipulated countable/integral factorizations; sign averaging fixes only the averaged live Choi and total failure effect. The overlapping laws in §§6–7 and §9, including the consequent Pareto point, are credited reuse. |
| RE §§4–5 | Positive-$d$ deduction and earlier all-strength rank-two replacement used for comparison in §8. The shared §7/JR §38 operator strictly improves that earlier RE operator throughout $s<1$; their effects agree at $s=1$. This is not a strict comparison against current JR §38. |
| RE §§6–10 | Endpoint binary-live forcing, exhaustive three-line cone, evaluated scalar pointwise envelope, separate complete attainers, common paired bound and endpoint Pareto/nonattainment. These endpoint results retain their own quantifiers and are not rebranded as new interior conclusions. |
| Repository declarations named by CG/JR: FiniteKrausRepresentation, UnitaryKrausMixingInvariance, FiniteKrausInstrumentBornMarginal, AntidistinguishabilityGram and CoherentFlagPort | Finite Choi/Kraus, mixing, Born-trace, positive-support and actual-port antecedents. These are source references, including their stated private dependencies, not newly compiled applications or a grant of access to an environment. |
| Heinosaari–Jivulescu–Reeb–Wolf, Extending quantum operations, arXiv:1205.0641v3, §§2.1, 6.1, as cited by CG | Mature finite CP/TP and Choi/Kraus framework. The at-most-qubit theorem is not used as a qutrit compatibility test or a continuous-time theorem. |
| Muñoz-Moller–Leppäjärvi–Heinosaari, Adversarial Information Gain in Non-ideal Quantum Measurements, arXiv:2602.20941v1, Definition 1 and Proposition 1; Leppäjärvi–Sedlák, Incompatibility of quantum instruments, arXiv:2212.11225v2, Definition 8, Remark 3 and Proposition 7, as cited by JR | Joint-operation and finite postprocessing/dilation antecedents. Here finite live Choi domination and each failure CP measure are treated explicitly, with no inferred physical environment port or unproved continuous-outcome extension. |
| Terhal–Horodecki, A Schmidt number for density matrices, quant-ph/9911117v4; Chruściński–Kossakowski, On partially entanglement breaking channels, quant-ph/0511244v1; Sekatski, The bottleneck dimension of quantum operations, arXiv:2608.25010v1, as cited by CG | Mature rank and classical-assisted bottleneck mechanisms. Product ranks here are applied to the actual joint fibres and TNI live submaps, without a capacity interpretation. |
| Nechita–Park, Random covariant quantum channels, arXiv:2403.03667v2, §5, and de Vicente–Streltsov, The power of the resource theory of genuine quantum coherence, arXiv:1604.08031v2, §II.2, as cited by CG | Covariance need not mean Schur, and zero transfer characterizes the stated Schur subclass. Analytic averaging in §6 supplies neither physical sign gates nor a restriction of original maps to that subclass. |
| Positive matrix factorization, real spectral theory, rank-one domination, finite affine-dependence elimination and finite-dimensional compactness | Mature tools specialized in the complete proofs above. JR already supplies the complex determinant inequality and scalar allocation; the unrestricted finite complex reduction and original-history frontier correspondence in §11 retain their separate content. |

The literature attributions in this table are inherited from the supplied
texts. Their external bodies, toolchain compatibility and originality
claims are not independently researched or authenticated here. CG's
error-bound comparisons and trace-class library references retain their
role in its inherited stability theorem, not an automatic stability or
optimality theorem for the coherent-input resource problem. Ordinary
proofs here are not Lean/kernel verification or frozen mathematical truth.

**Boundary 12.2 (exact resolved scope and the general gap).** For every
$|\gamma|\leq\kappa$, the original finite class has the sharp diagonal
law (IR.33) and one common actual attainer of all diagonal compressions,
reusing JR §§36–38's scalar allocation and instrument. For each strength
the common twelve-vector satisfies JR's sharp original four-sign laws
and is Pareto optimal by their direct consequence. JR's broader
worst-history minimum $\mathsf C(s)=g_{27}(s)$ is attained in this
fixed-channel, exact-effect class as well. The shared instrument strictly
improves RE's common all-strength operator on every nonzero positive
supported input when $|\gamma|<\kappa$, agrees with that operator at
the endpoint, and strictly improves the original JR §§30–31 family at
every allowed strength. It has the same common high effect as current
JR §38. Throughout the interior, each selected original individual input
admits a further lawful strict
improvement, and no one design attains all twelve pointwise minima.
For every positive input an individual minimum nevertheless exists,
with the exact unrestricted complex characterization (IR.70) and an
actual finite attainer of at most thirty branches. Its constants may
depend on a public test input, never on the specimen encountered during
execution. Negative coefficients use only binary relabeling.

The full original interior goal survives: evaluate $\mathsf E_s(\rho)$
for general coherent complex positive $\rho$, including the original
individual histories, and identify its minimizers beyond the diagonal
case. The finite minimum is not an evaluated general closed law, and
JR's stronger all-optimizer worst-history law does not evaluate these
individual coherent-input minima. Classify the complete twelve-coordinate
Pareto frontier, beyond the
common point and exact undominated-vector correspondence (IR.75).
The explicit real same-conditioned constructions do not exhaust that
problem: Proposition 5.3 exhibits other binary live maps, and the
universal reduction retains every complex plane and quadratic singular
direction. No lower bound on an individual coherent history is obtained
by replacing it with its diagonal or by treating a sign mean as a prior.
No independently attainable scalar pieces are assumed jointly attainable.

The fixed object remains (IR.10), not every minimax optimizer, and the
canonical error remains the conditional (IR.11) solely because the
forgotten full output channel is identical. Full-channel optimizer
classification and any independent original-control or unconditional-
prefix optimum are not supplied by these resource results. The source
root, interval-enclosure, minimax and nested-control assumptions keep
their original conditional status.

**Boundary 12.3 (native realization and the continuing programme).**
The constructions are exact abstract CP acquisition/execution
factorizations, with actual finite encoder operations specified rather
than inferred from a virtual decomposition. A native implementation
must still supply lawful access to the sole unknown specimen, enact
those encoders and classical flags, retain the joint counted coherent
payload, and provide the calibrated controlled range decoders under
the original permissions. The acquisition cut must fit the same aligned
clock and original available time; no extra acquisition interval is
created. A retained specimen, memory/controller, accessible environment
or entanglement share cannot be omitted and then used later as a bypass.
No history helper, source callback, copied specimen, reset, retry,
source-dependent programme or survival-mass prior is supplied.

The full five separate exact-time CP measures, cross-support zero
action and zero additional sectors are mathematical output identities.
A physical execution must additionally cause its first failure to be
absorbing at that actual elapsed time, allow no later positive-carrier
action on that failed branch, produce live output at terminal time one,
and preserve every old archive, source/epoch identity, aligned clock,
permission and declared controller update. A timestamp sampled from
$g(t)dt$, or an internal scalar label destined for later failure, does
not establish that physical event or timing service. Exact mathematical
CP measures do not establish finite exact-clock storage.

OriginalControl is a strict-domain regularity and chronological-path
predicate, not a common unknown-input encoder or decoder service.
The probability-changing and noncommuting fields cited by CG/JR from
Probability/Phase Transport, including $P=\partial_k$ and
$Q=\sum_aw_a(k)\partial_{h_a}$, do not justify replacing the full
native operation menu by diagonal filters. Conversely an abstract
Stinespring dilation, geometric reachability or equal effects do not
supply accessible quantum ports, enacted flags or full successors.
The original acquisition, coherent-control and absorbing-failure timing
programme remains unresolved in its full scope.

No physical efficiency, capacity, generic neural-network or empirical
learning result, worldwide originality, native impossibility theorem,
new source authentication, Lean/kernel/frozen-truth result, or completion
of the continuing original research goal follows.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[RE]: FIB_NATIVE_FIXED_CHANNEL_RECORD_RESOURCE_ENVELOPE.md

## 追加锚（本行以下为增补区）
