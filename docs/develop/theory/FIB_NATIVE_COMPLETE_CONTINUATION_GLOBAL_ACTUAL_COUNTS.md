# Global actual acquisition counts for the complete finite continuation

## 1. Mathematical scope and inherited hypotheses

**Convention 1.1 (status and ownership).** This volume concerns the minimum
number of actual acquisition labels among height-optimal instruments in the
original finite-activity, sharp-joint-cost problem. It gives ordinary
conditional mathematical proofs and an exact scalar interval certificate.
It is reference mathematics, not Lean/kernel verification. The numerical
source box is an enclosure of one stipulated isolated source; it does not
define a family of independently variable TP channels.

The new results are the complete weak minimum-budget boundary count,
continuity of the weak optimal value, relative closedness of the sublevels
of the minimum original actual count, an optimal strong upper bound, and
localization of the attained maximum count to an open strict weak region.
The sharp uniform count and the complete evaluated finite-plane frontier
remain open.

**Assumption 1.2 (separate published suppliers).** The following hypotheses
are used at precisely their stated scopes. The abbreviations name the
owning mathematical volumes, not new certification of their premises.

| Abbreviation and owning source | Required result and boundary |
| --- | --- |
| [CG, §§13–17](FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md) | The isolated original nine-coordinate source, source ranks and root TP identity; the complete stopped-output minimax certificate; the averaged-live and preaveraging consequences of Theorem 17.2 and Corollary 17.3. CG17 alone does not assert the unaveraged live channel equality used below. |
| [JR, §§34–42](FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md) | The original sharp worst-history **jointly acquired** cost, and the additional unaveraged supported real equality face of Theorem 42.1. This is a separate supplier from CG17. |
| [FA, §§69–72](FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md), [RC, §§67 and 75](FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md) | Actual-label double rigidity for full complex, multi-Kraus implementations; the physical capacity inequality; finite endpoint attainment; the full-fibre common constructor and the corrected treatment of supported-zero full encoders. |
| [FA, §§78–79](FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md) | The complete scalar finite feasibility domain and the forced entire equality class on its weak minimum-budget boundary, including the floor. |
| [RC, §68](FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md) | Actual two-sheet relative interiority with strict contrast slack. Feasibility alone is not substituted for this hypothesis. |
| [FA, Theorem 90.1 and §87](FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md) | A weak height optimizer with at most nine supported low labels; Theorem 87.3's one-high coherent completion and Corollary 87.4's identity of minimum total and supported-low counts. The nine-low result is an existence upper bound. |
| [ST, Theorem 8.2](FIB_NATIVE_COMPLETE_CONTINUATION_SATURATED_CONTACT_TRANSITIONS.md) | A nonempty ordinary open strict weak region with exact seven-low/eight-total optimal actual alphabet, under ST's source, joint-moment and whole-circle certificate hypotheses. No connected atlas or global ordering follows. |
| [ST, Definition 10.1](FIB_NATIVE_COMPLETE_CONTINUATION_SATURATED_CONTACT_TRANSITIONS.md) | The fixed-source dyadic enclosures used in §6. Source-root membership remains a hypothesis. |

Here FA denotes the finite-activity frontier, RC the residual-contact
curve, and ST the saturated-contact transitions. No source isolation,
minimax, native implementation, or complete-plane result is inferred
from the scalar certificate in this volume.

## 2. Original experiment, outputs and resources

**Definition 2.1 (one common unknown-input experiment).** In the ordered
five modes $0,1,2,3,13$, write their standard vectors as
$e_0,e_1,e_2,e_3,e_{13}$ and set
$$
\begin{gathered}
E=\left((e_0+e_{13})/\sqrt2,\ (e_1+e_3)/\sqrt2,\ e_2\right),\qquad
P=EE^\dagger,\\
p_y=\left(\frac y{128},\frac{64-y}{128},\frac12\right),\quad
a_y=\left(\sqrt{p_{y0}},\sqrt{p_{y1}},\sqrt{p_{y2}}\right)^T,\\
U_{\epsilon,\chi}=\operatorname{diag}(\epsilon,\chi,1),\qquad
\rho_{y,\epsilon,\chi}=U_{\epsilon,\chi}a_ya_y^TU_{\epsilon,\chi}^\dagger,
\quad y\in\{5,16,27\},\quad\epsilon,\chi\in\{\pm1\}.
\end{gathered}
\tag{GC.1}
$$
The sole input is the normalized state
$E\rho_{y,\epsilon,\chi}E^\dagger\in M_5$ with unknown history.
There is no prior on the twelve histories.

Let $\xi_y$ be the positive vector with squared entries
$$
\left(\frac y{128},
 \frac{y(58-y)}{128(y+6)},
 \frac{y}{2(y+6)}\right).
\tag{GC.2}
$$
The ideal live output is
$EU_{\epsilon,\chi}\xi_y\xi_y^TU_{\epsilon,\chi}^\dagger E^\dagger$.
The five **separate** failure-labelled Borel components have density
$$
w_\ell f_y(a)\,da\,P_f,\qquad
(w_0,w_1,w_2,w_3,w_{13})=(0,1/4,1/2,1/4,0),\qquad
f_y(a)=\frac{6y}{(y+6a)^2},\quad 0\le a\le1.
\tag{GC.3}
$$
Here $P_f=|f\rangle\langle f|$ is the prescribed one-dimensional
failure output. The direct sum of these five measures and the live
block is $\Omega_{y,\epsilon,\chi}$. The absolute FIRST time is $6+a$.
The two zero target components remain separate components of the
experiment.

**Definition 2.2 (original comparison class).** The error is
$$
\mathsf E(\Phi)=
 \max_{y,\epsilon,\chi}
 \frac12\left\|
 \Phi(E\rho_{y,\epsilon,\chi}E^\dagger)-\Omega_{y,\epsilon,\chi}
 \right\|_{1,\mathrm{stopped\text{-}cq}}.
\tag{GC.4}
$$
The HALF factor and the complete stopped-cq output are retained:
live off-diagonal coherences, all five failure measures, singular-time
parts, abort, wrong-support and zero-target sectors are included. Passive
references retain their conditional operators, rather than only
unconditional marginals. This convention does not replace the original
twelve-input minimax objective by a different diamond-norm objective.

A competitor is a common full complex CP acquisition instrument with
full-output TP conditional decoders. All live Kraus multiplicities and
all admitted failure-time laws are allowed. The resource constraints are
$$
\mathsf E(\Phi)=E_*,\qquad
\mathsf V(F)\ge s,\qquad
\mathsf W=\mathsf C(s),\qquad
\max_{j\ {\rm actually\ generated}}\int_0^1\|R_j(a)\|\,da\le A.
\tag{GC.5}
$$
Here $\mathsf V(F)=2|\operatorname{Re}F_{01}|/\kappa$ is the original
binary contrast, with $\kappa=h_0a+h_1b$ in the source notation of §3.
The binary report is produced from the same acquisition; its common
classical kernel may be absorbed into the actual label.

The cost $\mathsf W$ is the maximum over all twelve histories of the
probability that the **joint** future-accessible input-dependent quantum
fibre at the acquisition cut has dimension at least three. Specimen,
memory, controller, accessible environments and entangled shares are
counted together. Later blank ancillas are independent; a correlated
accessible share cannot be treated as blank. The activity acts on each
**entire** counted fibre. It is neither average activity nor the integral
of a maximum over different labels. Finite-budget survivor effects are
strictly positive. Survivor controls are TP. There is no forced terminal
absorption and no later positive-carrier action after failure.

There is one unknown specimen and one instrument fixed before its input:
no helper, copy, history oracle, reset, retry, quantum bypass,
postselection, acceptance division, or survival division is available.

**Convention 2.3 (necessity and attainment scopes).** Necessity covers
the original finite and countable classes, with convergent CP
instruments, and only the measurable extension stipulated in CG
Convention 21.3: measurable finite fibre dimensions, measurable
encoder/live-decoder Kraus fields, integrable effects and live Choi
matrices, and full-output TP decoders almost everywhere. Integral CP
densities need not be individually TNI relative to their reference
measure; their integrated effect is the identity. There is no
unrestricted continuous-outcome disintegration or infinite-dimensional
coding assertion. Every attainment used here is finite.

## 3. Source, physical dictionary and the original common law

**Definition 3.1 (fixed source and normalization).** At the isolated
source of Assumption 1.2 put
$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\qquad
T=ae_0e_1^T+be_1e_0^T,\qquad
S=ce_0e_2^T+de_2e_0^T,\\
M=\operatorname{diag}(0,m_1,m_2),\qquad
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
\theta=\frac{ab}{h_0h_1},\quad
\omega=\frac{cd}{h_0h_2},\quad
\delta=\theta+\omega,\quad
s_0=\sqrt\delta,\quad
\alpha=\frac{\theta}{\delta},\quad
\beta=\frac{\omega}{\delta}.
\end{gathered}
\tag{GC.6}
$$
All displayed source amplitudes, $m_1,m_2,\theta,\omega$ are positive,
$0<\delta<1$, and $\alpha+\beta=1$. The $e_i$ in these qutrit matrices
are the standard qutrit vectors. The TP identity is used only at the
stipulated root.

Define
$$
\begin{gathered}
\Delta=\rho_{27,+,+}-\rho_{5,+,+},\quad
(K_0,K_1,K_2)=(D,T,S),\quad N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\\
L=\operatorname{diag}(s_0,1,1),\qquad G=LNL,\qquad
H_0=(1-\delta)N_{00}>0.
\end{gathered}
\tag{GC.7}
$$
The real symmetric matrices $N,G$ encode the height difference. $L$
is a coefficient normalization, not a terminal survivor effect.

**Definition 3.2 (supported low law and physical capacity).** For a weak
supported-nonzero actual low label write
$$
\begin{gathered}
h=(1,z,w),\qquad \alpha z^2+\beta w^2=1,\qquad
K_h=s_0D+zT+wS,\qquad K_j=\sqrt{p_j}K_{h_j},\\
n_h=(0,dw/h_2,-bz/h_1)^T,\qquad
\ell(h)=h^TGh,\qquad f(h)=n_h^T\Delta n_h,\\
\mathfrak c(h)=
\frac{h_1^2h_2^2\delta+a^2h_2^2z^2+c^2h_1^2w^2}
 {h_0^2\delta+b^2z^2+d^2w^2}>0,\qquad t=e^A-1.
\end{gathered}
\tag{GC.8}
$$
The source amplitude $c$ and the capacity $\mathfrak c$ are distinct.
The complete joint law is
$$
\begin{gathered}
\sum_jp_jh_jh_j^T=I_3,\qquad
N_j^{\,f}=p_jb_jn_{h_j}n_{h_j}^T,\qquad
\sum_jN_j^{\,f}=M,\\
0\le b_j\le t\mathfrak c(h_j),\qquad
\sum_jp_j|z_j|\ge\tau:=s/s_0,\\
2T_{\rm actual}=H_0+\sum_jp_j|\ell(h_j)+b_jf(h_j)|.
\end{gathered}
\tag{GC.9}
$$
The $p_j$ are coefficient weights with sum one, **not** acquisition
probabilities. The actual acquisition effect on the supported input is
$K_j^\dagger K_j+N_j^{\,f}$.

The necessity of (GC.9) follows from JR's unaveraged equality face and
FA's actual-label double rigidity, not from a restriction of competitors
to real matrices. It applies to each existing supported-nonzero actual
low label without turning a hidden Kraus index into a readable label.
Proportional subdivisions may be merged. Distinct supported live rays
cannot be hidden in one actual low label.

Supported-zero full encoders are also admissible. Their full effects
may be nonzero although their compression by $E$ vanishes. They count
when actually generated, but have zero probability on the twelve
supported histories. For weak **minimum** counts, (GC.9) and the
coherent completion in §10 give
$$
\min(\text{total optimal actual labels})
 =1+\min(\text{supported low optimal actual labels}).
\tag{GC.10}
$$
This is an equality of minima, not a count identity for every instrument.

**Convention 3.3 (physical whitening).** For the lower two supported
coordinates let $M_2=\operatorname{diag}(m_1,m_2)$. A physical failure
effect $B_f$ is whitened by $M_2^{-1/2}B_fM_2^{-1/2}$. The height
pairing in this normalization is
$$
\begin{gathered}
\Xi=M_2^{1/2}\Delta_{\{1,2\}}M_2^{1/2}
 =\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},\\
d_f=11m_1/64,\qquad
z_f=\sqrt{m_1m_2}\,(\sqrt{37}-\sqrt{59})/16<0,\qquad
L_f=\sqrt{d_f^2+4z_f^2}.
\end{gathered}
\tag{GC.11}
$$
A unit spectral vector $e$ of $\Xi$ represents the physical effect
$M_2^{1/2}ee^TM_2^{1/2}$, not the bare projector $ee^T$.
No two-spectral-line allocation is imposed. The scalar $\nu$ below
has no relation to an auxiliary fixed-strength spectral allocation.

## 4. Entire finite feasible domain and count conventions

**Definition 4.1 (scalar parameters).** Put
$$
\begin{gathered}
V=\frac{m_2h_1^2}{b^2},\qquad
W=\frac{m_1h_2^2}{d^2},\qquad \mu=\alpha V+\beta W,\\
u_F=V/\mu,\quad v_F=W/\mu,\quad
\mathfrak c_f=\mathfrak c(1,\sqrt{u_F},\sqrt{v_F}),\quad
\nu=\mu/\mathfrak c_f,\quad t_0=W/\mathfrak c_f=\nu v_F.
\end{gathered}
\tag{GC.12}
$$
At this fixed source,
$0<u_F<1<v_F$ and $\alpha u_F+\beta v_F=1$.
For finite $t\ge t_0$ define
$$
\begin{gathered}
q=\nu/t,\quad
u_R=\frac{1-qu_F}{1-q},\quad
v_R=\frac{1-qv_F}{1-q},\\
\tau_{\max}(t)=q\sqrt{u_F}+\sqrt{(1-q)(1-qu_F)},\qquad
\tau_*=\tau_{\max}(t_0).
\end{gathered}
\tag{GC.13}
$$
Thus $0<q\le1/v_F<1$, $u_R>1$, $v_R\ge0$, and $v_R=0$
exactly on the floor $t=t_0$.

**Proposition 4.2 (reused exact feasibility).** Under Assumption 1.2,
all finite weak feasible parameters are exactly
$$
\mathcal D_w=\{(s,t):t\ge t_0,\quad
                 0\le s\le s_0\tau_{\max}(t)\}.
\tag{GC.14}
$$
Equivalently, for $0\le\tau=s/s_0<1$,
$$
t_{\min}(s)=
\begin{cases}
t_0,&0\le\tau\le\tau_*,\\
\displaystyle\nu\frac{1+u_F-2\tau\sqrt{u_F}}{1-\tau^2},
 &\tau_*<\tau<1.
\end{cases}
\tag{GC.15}
$$
Every threshold is attained. The remaining finite feasible parameters
form the isolated strong line
$$
\begin{gathered}
v_d=V/W,\quad u_d=\theta v_d+\omega=\delta\mu/W,\\
s^\dagger=\sqrt{u_dv_d}+\sqrt{(1-u_d)(1-v_d)},\qquad
s=s^\dagger,\quad t\ge t_0.
\end{gathered}
\tag{GC.16}
$$
The strong $s^\dagger$ is distinct from $s_0$ and from the static weak
contact. Finite $A=0$, $s=s_0$ and $s=1$ are infeasible. In particular,
$s<s_0$ at every finite weak point.

Proof. These are FA Theorem 78.3, its homogeneous correspondence
(FA.42), and Theorem 71.1, with
$(V,W,\mu,u_F,v_F)=(V_f,W_f,\mu_f,u_f,v_f)$.
No new feasibility or source claim is made. $\square$

**Definition 4.3 (value and original minimum count).** Let
$\mathcal T(s,t)$ be the maximum actual acquisition-record height TV
under (GC.5), and let $n(s,t)$ be the minimum **total** number of
actually generated acquisition labels among its original optimal
attainers. On empty classes $n$ and this optimal value are not defined.
An infinite-budget limit is not a finite attainment. Terminal failure
labels, hidden Kraus indices, static support rank and jointly acquired
quantum dimension are different from $n$.

By FA Theorem 90.1 and (GC.10), $n\le10$ throughout $\mathcal D_w$.
By ST Theorem 8.2, $n=8$ on a nonempty ordinary open strict weak
region. These two facts are reused at their published conditional scope.

## 5. Exact counts on the entire weak minimum-budget boundary

**Definition 5.1 (finite boundary scalars).** For $i=F,R$ and
$\sigma,\upsilon\in\{\pm1\}$ put
$$
\begin{gathered}
h_{i,\sigma,\upsilon}=(1,\sigma\sqrt{u_i},\upsilon\sqrt{v_i}),\\
L_{F,\sigma,\upsilon}
 =|\ell(h_{F,\sigma,\upsilon})+t\mathfrak c_f f(h_{F,\sigma,\upsilon})|,
\qquad L_{R,\sigma,\upsilon}=|\ell(h_{R,\sigma,\upsilon})|,\\
M_i=\tfrac14\sum_{\sigma,\upsilon}L_{i,\sigma,\upsilon},\quad
Z_i=\tfrac14\sum_{\sigma,\upsilon}\sigma L_{i,\sigma,\upsilon},\quad
Y_i=\tfrac14\sum_{\sigma,\upsilon}\upsilon L_{i,\sigma,\upsilon},\\
k_z=\frac{q\sqrt{u_F}}{(1-q)\sqrt{u_R}},\qquad
B_z=q\left(Z_F-\sqrt{u_F/u_R}\,Z_R\right).
\end{gathered}
\tag{GC.17}
$$
For $t>t_0$ also set
$$
k_w=\frac{q\sqrt{v_F}}{(1-q)\sqrt{v_R}},\qquad
B_w=q\left(Y_F-\sqrt{v_F/v_R}\,Y_R\right),\qquad
t_b=t_0+\nu.
\tag{GC.18}
$$
No formula involving $1/\sqrt{v_R}$ is used at the floor.

**Theorem 5.2 (complete boundary actual-total count).** Under
Assumption 1.2, on the entire floor
$t=t_0$, $0\le s\le s_0\tau_*$, the exact minimum is $n=5$.
On the rising boundary $t>t_0$,
$s=s_0\tau_{\max}(t)$,
$$
n(s,t)=
\begin{cases}
5,&t=t_b\ \text{and}\ |B_w(t_b)|\ge|B_z(t_b)|,\\
7,&\text{otherwise}.
\end{cases}
\tag{GC.19}
$$
All objective ties, zero signed heights, vanishing weights and the
collapsed floor directions are included. With the fixed-source
enclosures of §6, the comparison is strict in the displayed direction.
Consequently the rising boundary has exactly one five-total point,
$t=t_b$, and has seven total at every other rising point.

Proof. FA Theorem 79.1 forces every original boundary competitor,
after proportional subdivisions on the same ray are merged, to a
saturated $F$ family and a pure $R$ family. At $t>t_0$ their weights are
$$
p^F_{\sigma,\upsilon}=\frac q4(1+\sigma X+\upsilon Y),\qquad
p^R_{\sigma,\upsilon}=\frac{1-q}{4}
 (1-\sigma k_zX-\upsilon k_wY).
\tag{GC.20}
$$
Their positivity region and variable height contribution are
$$
|X|+|Y|\le1,\qquad k_z|X|+k_w|Y|\le1,\qquad B_zX+B_wY.
\tag{GC.21}
$$
For clarity, the underlying equality mechanism is distinct from
restricting to a convenient witness: strict Jensen forces all
failure-carrying directions to $u_F$ and saturation, and residual
Cauchy equality fixes $u_R$. The failure off-diagonal moment kills the
$\sigma\upsilon$ Fourier coefficient on $F$; the live $zw$ moment
kills it on $R$. The first live moments yield (GC.20).
Thus this is the entire forced original equality class.

The published source inequalities give $0<k_z<1$. Directly,
$$
k_w^2=\frac{q^2v_F}{(1-q)(1-qv_F)},\qquad
k_w=1\ \Longleftrightarrow
q=\frac1{1+v_F}\ \Longleftrightarrow
t=\nu(1+v_F)=t_b.
\tag{GC.22}
$$
In particular, $k_w>1$ for $t_0<t<t_b$ and $k_w<1$ for $t>t_b$.

Reflections let us use the nonnegative objective coefficients
$|B_z|,|B_w|$ and count the first-quadrant vertices. When $k_w<1$
the second diamond contains the first. Its axial vertices $(1,0)$
and $(0,1)$ each have two positive $F$ weights and four positive $R$
weights, hence six low labels. When $k_w>1$ the relevant vertices are
$$
(1,0),\qquad (0,1/k_w),\qquad
\left(\frac{k_w-1}{k_w-k_z},\frac{1-k_z}{k_w-k_z}\right).
\tag{GC.23}
$$
Their positive $(F,R)$ counts are respectively $(2,4)$, $(4,2)$
and $(3,3)$. At the mixed vertex one weight from each family vanishes
and the other three are strictly positive. At $k_w=1$, a signed
$(0,1)$ vertex has $(2,2)$ positive weights; the signed $(1,0)$
vertices still have $(2,4)$. A $Y$ vertex is optimal precisely when
$|B_w|\ge|B_z|$.

Here $u_F<1<u_R$ separates the two families, and all their signed
coordinates are nonzero for $t>t_0$, so these positive weights count
distinct supported rays. To exclude a smaller nonvertex optimum,
write any point of the optimal face as a convex combination of its
optimal vertices. Each weight in (GC.20) is nonnegative and affine.
A positive weight at any positive-coefficient constituent vertex
stays positive in the combination. The combination therefore contains
that vertex's support. This proves that the minimum support among
linear optima is achieved at an optimal vertex, including a constant
objective and every tie along an optimal edge.

At $t=t_0$, $v_R=0$. The live $w$ moment forces $Y=0$ and the two
$\upsilon$ signs in each $R$ direction coincide. The distinct-ray
weights are
$$
p^F_{\sigma,\upsilon}=\frac q4(1+\sigma X),\qquad
p^R_\sigma=\frac{1-q}{2}(1-\sigma k_zX),\qquad -1\le X\le1.
\tag{GC.24}
$$
Both $R$ weights are strictly positive. At $X=1$ or $-1$ there are
exactly two positive $F$ weights and two $R$ weights; at an interior
$X$ there are more. An objective-maximizing endpoint therefore gives
four low and none can give fewer. Its available contrast is
$s_0\tau_*$, so it also solves every lower requested floor contrast:
the original requirement is an inequality.

FA actual-label rigidity prohibits combining distinct rays into one
low outcome through hidden Kraus multiplicity. Proportional
subdivisions of a pure or saturated ray preserve its absolute height
sum and only increase the count. Supported-zero encoders add labels.
The high supported acquired mass is positive, hence requires at least
one additional high label. The common constructor in §10 attains the
counts with exactly one such label, including the complement. These
are lower and upper bounds for original **total actual** counts.
The strict scalar comparison follows from Proposition 6.2. $\square$

**Corollary 5.3 (boundary value, including ties).** In the same boundary
domain the original optimal value is the finite expression
$$
\mathcal T(s,t)=\frac{H_0+qM_F+(1-q)M_R+P_{\rm bd}}2,
\tag{GC.25}
$$
where
$$
P_{\rm bd}=
\begin{cases}
|B_z|,&t=t_0,\\
\max\{|B_z|,|B_w|\},&t>t_0,\ k_w\le1,\\
\displaystyle\max\left\{|B_z|,\frac{|B_w|}{k_w},
 \frac{|B_z|(k_w-1)+|B_w|(1-k_z)}{k_w-k_z}\right\},
 &t>t_0,\ k_w>1.
\end{cases}
\tag{GC.26}
$$
Proof. The constant part of the height sum in (GC.20) is
$qM_F+(1-q)M_R$; evaluating the linear part at (GC.23) and the axial
vertices gives (GC.26). At the floor use (GC.24). This is also the
published FA boundary value, with the normalization of (GC.7)–(GC.9).
Absolute values are evaluated before weighting, so zero signed
heights require no extra branch convention. $\square$

## 6. Exact scalar certificate for the exceptional rising point

**Definition 6.1 (dyadic data and interval rules).** Each endpoint
integer in the following table is divided by $D_{\rm src}=2^{224}$.
These are the required source rows of ST Definition 10.1. The
parameters remain those of the same isolated root.

| Quantity | Lower numerator | Upper numerator |
| --- | --- | --- |
| $h_0$ | $26537788820506109500788498850443291999899441414357450708533697655768$ | $26537788820506109500793183315073538792668688684001205079732940054331$ |
| $h_1$ | $19041394653590742992836842417055357808127410672381937576282066738318$ | $19041394653590742992839410055472468226237891451663919566364482743060$ |
| $h_2$ | $21824004785988993361054584934895991870094398276315525145506200547608$ | $21824004785988993361057348440025413753058042469208985303844669006803$ |
| $a$ | $1770311394972945197641994965733434776804318798358636960993665423441$ | $1770311394972945197642330191383860313598676849494811590399527112584$ |
| $b$ | $3935965654294995608601979521892857651473674590095072143984588712921$ | $3935965654294995608602313422828891500221393677289956783118602628225$ |
| $c$ | $417790356983612701857377130657326048451791786364520663159403140999$ | $417790356983612701857967962172137068830255220590298423542851403047$ |
| $d$ | $2663205433690388662341049091689729175826547547021472884789707223172$ | $2663205433690388662342459064972096088182130849082266016544667607076$ |
| $m_1$ | $13395056598782546673904842458375183527737029361412185934273944851861$ | $13395056598782546673906662453967195540019733666091401589339664139139$ |
| $m_2$ | $9286998735773460367948153511490550124076700197961256553923028397389$ | $9286998735773460367951141007906400979909044212876537994791222399466$ |

All interval operations are outward exact rational operations. For
$I=[l,u]$, $J=[r,v]$, addition has endpoints $l+r,u+v$,
subtraction $l-v,u-r$, multiplication takes the minimum and maximum
of the four endpoint products, and division multiplies by
$[1/v,1/r]$ when $0<r\le v$.
Squaring uses zero as the lower bound if the interval crosses zero;
absolute value uses the same sign cases. For a nonnegative interval,
the square-root enclosure uses denominator $Q=2^{192}$:
$$
\sqrt{[l,u]}\subseteq
\left[\frac{k_l}{Q},\frac{k_u+1}{Q}\right],
\qquad k_x=\max\{k\in\mathbb Z_{\ge0}:k^2\le Q^2x\}.
\tag{GC.27}
$$
All comparisons defining $k_x$ are integer/rational comparisons.

For direct evaluation from the original matrices, the exact height
difference is
$$
\Delta=
\begin{pmatrix}
11/64&(\sqrt{999}-\sqrt{295})/128&(\sqrt{27}-\sqrt5)/16\\
(\sqrt{999}-\sqrt{295})/128&-11/64&(\sqrt{37}-\sqrt{59})/16\\
(\sqrt{27}-\sqrt5)/16&(\sqrt{37}-\sqrt{59})/16&0
\end{pmatrix}.
\tag{GC.28}
$$
Use (GC.6) to form $\theta,\omega,\delta,\alpha,\beta,s_0$,
(GC.28) and the trace formula (GC.7) to form $N,G$, then
(GC.12)–(GC.13) to form the boundary parameters. In the capacity
expression use its squared coordinates directly, $z^2=u_F$, $w^2=v_F$,
and compute $G_{ij}=L_{ii}N_{ij}L_{jj}$.
At $t_b=t_0+\nu$ evaluate the eight absolute values and their Fourier
coefficients in (GC.17)–(GC.18). All denominators are strictly positive.
This specifies the scalar expression without any fitted height signs.

**Proposition 6.2 (strict exceptional inequality).** Under the
source-enclosure premise, the following rational enclosures hold.
Every endpoint integer in this table is divided by $10^{25}$.

| Expression | Lower numerator | Upper numerator |
| --- | --- | --- |
| $u_F$ | $7226550620205194187464273$ | $7226550620205194187491411$ |
| $v_F$ | $29906450227381110568953095$ | $29906450227381110569085941$ |
| $\mathfrak c_f$ | $1259947042588917333362731$ | $1259947042588917333370829$ |
| $\nu$ | $885457917523522290190443942$ | $885457917523522290198785534$ |
| $t_0$ | $2648090313885774784411626004$ | $2648090313885774784432478599$ |
| $t_b$ | $3533548231409297074602069947$ | $3533548231409297074631264132$ |
| $H_0$ | $795273560426923433145088$ | $795273560426923433145905$ |
| $B_z(t_b)$ | $-6469634636316157424434$ | $-6469634636316157403374$ |
| $B_w(t_b)$ | $-17426011732742545104987$ | $-17426011732742545082488$ |
| $\lvert B_w(t_b)\rvert-\lvert B_z(t_b)\rvert$ | $10956377096426387658054$ | $10956377096426387701613$ |

In particular,
$$
0.00109563770964263
 < |B_w(t_b)|-|B_z(t_b)|
 < 0.00109563770964265.
\tag{GC.29}
$$

Proof. Apply the rational operations of Definition 6.1 to the displayed
source rows, with (GC.28), (GC.6)–(GC.8), (GC.12)–(GC.13), and then
(GC.17)–(GC.18) at $t_b$. The endpoint square roots are rounded
outward by (GC.27); matrix multiplication and trace use rational sums
and products. Outward rounding the resulting rational endpoints to
denominator $10^{25}$ gives the table. Both Fourier intervals are
strictly negative, so subtracting their negative intervals in the
order $-B_w+B_z$ gives the last row. The lower numerator is strictly
positive. Comparing that row with the two terminating rationals in
(GC.29) gives the strict displayed inequalities.

This is a finite scalar certificate conditional on the input
enclosures. It neither isolates the original root nor proves TP on
off-root points of its box. Those are separate premises of
Assumption 1.2. Together with Theorem 5.2 it resolves the occurrence
of the exceptional boundary point, rather than leaving its scalar
comparison unevaluated. $\square$

## 7. Continuity of the entire finite weak optimal value

**Definition 7.1 (fixed compact two-sheet projection).** Put
$u=\sqrt\alpha\,z$, $v=\sqrt\beta\,w$ and let
$$
\begin{gathered}
\mathcal X=\{(u,v,\eta):u^2+v^2=1,\ \eta\in\{0,1\}\},\\
\Gamma_\eta=
 (1,u,v,u^2,uv,\eta\mathfrak c,\eta\mathfrak c u^2,
                         \eta\mathfrak c uv),\\
B(t)=(1,0,0,\alpha,0,\mu/t,\alpha V/t,0),\\
g_t(u,v,\eta)=|\ell(h)+\eta t\mathfrak c(h)f(h)|,\qquad
r(s)=\sqrt\alpha\,s/s_0.
\end{gathered}
\tag{GC.30}
$$
Every occurrence of $h$ here means
$(1,u/\sqrt\alpha,v/\sqrt\beta)$. Endpoint families satisfy
$$
\sum_jp_j\Gamma_{\eta_j}=B(t),\qquad
\sum_jp_j|u_j|\ge r(s).
\tag{GC.31}
$$
The first five coordinates recover all live Gram entries. The last
three give
$\sum p\eta t\mathfrak c=\mu$,
$\sum p\eta t\mathfrak c z^2=V$ and
$\sum p\eta t\mathfrak c zw=0$.
The ellipse identity recovers the $w^2$ moment $W$.
Congruence by
$(z,w)\mapsto(dw/h_2,-bz/h_1)$ recovers exactly $M$.
Thus these are constraints on one common joint law.

**Lemma 7.2 (bounded concave roofs at relative interior targets).**
Fix a continuous payoff on $\mathcal X$. On the mass-one moment
projection, with a contrast coordinate allowed to decrease below its
achieved value, the maximum payoff is continuous at every relative
interior target where it is finite.

Proof. The common-law feasible set is convex. Mixtures preserve the
moment and contrast-slack targets, so its upper payoff roof $F$ is
concave. Since the payoff is bounded on $\mathcal X$, there is a
constant $C$ such that $|F|\le C$ on the projection. At a relative
interior point $y$ choose $R>0$ with the affine-hull ball
$B(y,R)$ contained in the projection. For a unit direction $e$
and $0<h<R$, concavity on the segment from $y$ to $y+Re$ gives
the lower bound below. Concavity with $y$ between $y-Re$ and
$y+he$ gives the upper bound:
$$
-\frac{2C}{R}h\le F(y+he)-F(y)
                      \le\frac{2C}{R}h.
\tag{GC.32}
$$
Indeed, $y=\frac{h}{R+h}(y-Re)+\frac{R}{R+h}(y+he)$ for the
upper bound; each payoff difference at the endpoints is bounded by
$2C$. These inequalities prove continuity in the affine hull.

Ordinary probability measures on $\mathcal X$ can be used for this
convex argument. Their finite vectors consisting of moment,
contrast and payoff coordinates belong to the convex hull of a
compact image in a finite-dimensional space. Finite convex
combinations represent the same vectors. Thus this argument computes
the same finite-law value and introduces no new measurable physical
disintegration assumption. $\square$

**Theorem 7.3 (whole-domain weak continuity).** Under Assumption 1.2,
$\mathcal T$ is continuous on all of $\mathcal D_w$ in its relative
topology, including the floor, its join, the rising boundary, $s=0$,
contact collisions, vanishing weights and zero signed heights.

Proof. First prove upper continuity. Along a convergent sequence of
finite weak feasible parameters $(s_j,t_j)\to(s,t)$ choose the inherited
at-most-nine-supported-low endpoint optimizer, padded with zero
weights to nine atoms. Endpoint reduction preserves feasibility and
cannot decrease the absolute-height objective; at an optimum it
therefore preserves its value. The probability simplex and the two
circles are compact. Along a subsequence achieving the upper limit,
all weights, directions and endpoint sheets converge. The limit
satisfies (GC.31), including its contrast inequality, since $B(t)$
and all integrands are continuous for finite $t\ge t_0>0$.
The limiting height sum equals the limiting value, so
$\limsup_j\mathcal T(s_j,t_j)\le\mathcal T(s,t)$.
Omit zero weights. This uses only finite families.

For lower continuity at $t>t_0$, $s<s_0\tau_{\max}(t)$, use RC
§68's relative-interiority result. Its full-support positive
components on **both** sheets and its strict contrast slack imply
that the target lies in the relative interior after quotienting
moment identities. Multiplying the last three moment coordinates
by the nonzero scalar $t$ transfers that result to (GC.30).
The fixed projection is independent of the neighboring budget.
Allowing the contrast target to decrease below zero also provides
the same local projection near $s=0$; the final assertion is relative
to $s\ge0$.

For explicit content of this premise, RC constructs a failure moment
measure with a small uniform angular component, adjusts its
four-sign component to preserve $(\mu,V,W,0)$, and divides by
$t\mathfrak c$. At $t>t_0$ the residual live diagonal is
$\operatorname{diag}(1-q,1-qu_F,1-qv_F)\succ0$.
A small full-support pure-sheet component can also be subtracted
and restored. The achieved contrast approaches $\tau_{\max}(t)$,
hence can be chosen strictly above the requested value.
A nonnegative supporting functional that vanishes at this target
must have zero contrast coefficient by slack, vanish on both entire
circles by their full support, and therefore be a moment identity.
This is the required relative interiority, not just feasibility.

Apply Lemma 7.2 with the payoff frozen at the limiting $t$. The
targets $(B(t_j),r(s_j))$ converge in the same projection and the
roof is continuous at the limiting target. Moreover,
$$
\|g_{t'}-g_t\|_\infty
 \le |t'-t|\max_h\mathfrak c(h)|f(h)|.
\tag{GC.33}
$$
This uniform bound, and continuity of $H_0$, transfer the fixed-payoff
conclusion to the moving actual payoff. Thus lower continuity holds
at all strict weak points, including $s=0$.

Now take a rising boundary point with $t>t_0$. Choose a maximizing
polygon point $(X_*,Y_*)$ in (GC.21). For any approaching feasible
$t_j$ define
$$
a_j=\min\left\{1,
 \frac1{k_z(t_j)|X_*|+k_w(t_j)|Y_*|}\right\},
\tag{GC.34}
$$
using $a_j=1$ if the denominator is zero.
The limiting denominator is at most one, hence $a_j\to1$.
The point $(a_jX_*,a_jY_*)$ lies in the new polygon. Its family has
available contrast $\tau_{\max}(t_j)$ and therefore meets every
admissible nearby requested $s_j$. All weights and directions
converge, as does the continuous absolute-height sum. This proves
the lower-limit inequality at the boundary, even across $k_w=1$
and objective-sign or vertex-type changes.

Finally take a floor point and choose an optimal endpoint
$(X_*,Y_*)=(1,0)$ or $(-1,0)$ in (GC.24).
For all $t_j\ge t_0$ sufficiently close to $t_0$ the same endpoint
is feasible because $k_z(t_j)<1$. These maximum-contrast families
meet every admissible requested $s_j$. Their two $R$ directions
with opposite $w$ signs merge as $v_R\downarrow0$, and their
heights converge to the floor optimum. There is no division by
$v_R$ in this limiting statement. This includes the floor join.
Upper and lower continuity together prove the theorem. $\square$

## 8. Closed sublevels of the minimum original actual count

**Theorem 8.1 (count closure with fractional capacities).** For each
integer $k$, the set
$$
\{(s,t)\in\mathcal D_w:n(s,t)\le k\}
\tag{GC.35}
$$
is relatively closed. Consequently $n$ is lower semicontinuous on
the entire finite weak domain. Neither optimizer continuity nor
continuity of the count is asserted.

Proof. Suppose $(s_j,t_j)\to(s,t)$ in $\mathcal D_w$ and
$n(s_j,t_j)\le k$. By the minimum-count identity (GC.10), choose an
optimal supported low family with at most $k-1$ actual labels.
Keep each original fractional-capacity coordinate
$$
\xi_{ji}=\frac{b_{ji}}{t_j\mathfrak c(h_{ji})}\in[0,1].
\tag{GC.36}
$$
Do **not** split it into pure and saturated labels: that can increase
the actual count. Pad to $k-1$ labels with zero weights. The simplex,
ellipse and interval $[0,1]$ are compact. A subsequence has a joint
limit of all weights, directions and fractions.

Set $b_i=t\mathfrak c(h_i)\xi_i$ in the limit. Equation (GC.9) and
the contrast inequality pass to the limit continuously. The absolute
height sum converges without a sign assumption. By Theorem 7.3 its
value is $\mathcal T(s,t)$, so the limit is optimal. Omitting zero
weights leaves at most $k-1$ supported low labels. The constructor
in §10 supplies one high label, hence $n(s,t)\le k$.

Colliding directions can only reduce the needed count. Supported-zero
full labels do not obstruct this argument because (GC.10) concerns
minima and provides the one-high completion. Thus the proof is about
original fractional-capacity actual atoms, not only endpoint atoms.
Relative closedness of (GC.35) is equivalent to lower
semicontinuity for the integer-valued function $n$. $\square$

## 9. Optimal strong upper bound and the global maximum

**Theorem 9.1 (strong optimal upper bound).** At every finite feasible
strong point (GC.16) an original height-optimal instrument exists with
at most six supported low and two high actual labels, hence
$n\le8$. At $t/t_0=1$ or $2$ this construction needs at most four
supported low and two high. No exact strong optimal minimum-count
classification follows.

Proof. Write $(u_d,v_d)$ as in (GC.16). JR's sharp-cost equality
gives low and high coefficient Grams
$\operatorname{diag}(u_d,v_d,1)$ and
$\operatorname{diag}(1-u_d,1-v_d,0)$.
Their contrast upper bounds are
$\sqrt{u_dv_d}$ and $\sqrt{(1-u_d)(1-v_d)}$.
Their sum is the requested $s^\dagger$, so the original contrast
inequality forces equality in both Cauchy bounds and their alignment.

The full complex equality face removes a common phase. On a low
product Cauchy equality gives
$|z|=\sqrt{v_d/u_d}|x|$, and the singular equation
$x^2=\theta z^2+\omega w^2$ then fixes the remaining real ratio.
Consequently all nonzero supported low products are proportional to
the four rays
$$
\mathbf c_{\sigma,\upsilon}
 =(\sqrt{u_d},\sigma\sqrt{v_d},\upsilon),\qquad
K_{\sigma,\upsilon}
 =\sqrt{u_d}D+\sigma\sqrt{v_d}T+\upsilon S.
\tag{GC.37}
$$
The complete low Gram kills the first and mixed sign moments and
forces total coefficient weight $1/4$ on each ray.
For a fixed actual report, equality also aligns every supported
high hidden Kraus direction with the corresponding ray. Proportional
subdivision does not increase the absolute height. Thus the two
actual high matrices
$$
H_\sigma=
 \frac{\sqrt{1-u_d}D+\sigma\sqrt{1-v_d}T}{\sqrt2},
\qquad \sigma\in\{\pm1\},
\tag{GC.38}
$$
attain the high part's universal upper bound. They are invertible
at this fixed source.

The strong ray is $1/\sqrt{v_F}$ times the weak $F$ coefficient
ray, since $u_d=\delta/v_F$ and $v_d=u_F/v_F$.
Its physical null vector is
$$
n_{\sigma,\upsilon}
 =(0,d\upsilon/h_2,-b\sigma\sqrt{v_d}/h_1)^T.
\tag{GC.39}
$$
The homogeneous capacity is therefore still $\mathfrak c_f$.
Let $C=t\mathfrak c_f$, $r=t/t_0\ge1$.
Endpoint splitting bounds every original low height sum above while
preserving all joint moments. If $a_{\sigma,\upsilon}$ is the
saturated coefficient mass, the complete feasible conditions are
$$
0\le a_{\sigma,\upsilon}\le\tfrac14,\qquad
\sum_{\sigma\upsilon=+1}a_{\sigma,\upsilon}=\frac1{2r},\qquad
\sum_{\sigma\upsilon=-1}a_{\sigma,\upsilon}=\frac1{2r}.
\tag{GC.40}
$$
Indeed, the diagonal failure moment is $\sum pb=W$ and the
off-diagonal one is $\sum pb\,\sigma\upsilon=0$;
$W/(t\mathfrak c_f)=1/r$. The second diagonal follows from
$v_d=V/W$. Each ray's remaining pure mass is $1/4-a_{\sigma,\upsilon}$.

Define the actual strong payoffs
$$
\ell_{\sigma,\upsilon}=\mathbf c_{\sigma,\upsilon}^TN
                                      \mathbf c_{\sigma,\upsilon},\qquad
f_{\sigma,\upsilon}=n_{\sigma,\upsilon}^T\Delta n_{\sigma,\upsilon}.
\tag{GC.41}
$$
The low height is a linear function of the four saturated masses,
with coefficient
$|\ell_{\sigma,\upsilon}+Cf_{\sigma,\upsilon}|-
 |\ell_{\sigma,\upsilon}|$ on each $a_{\sigma,\upsilon}$.
The high part is the fixed sum
$\sum_\sigma|\operatorname{tr}(H_\sigma\Delta H_\sigma^\dagger)|$.
Thus a maximizing vertex of the product of the two parity intervals
attains a universal upper bound for all original decompositions.

Explicitly put $S_r=1/(2r)$,
$L_r=\max(0,S_r-1/4)$ and $U_r=\min(1/4,S_r)$.
In either parity pair choose its first saturated mass to be $U_r$
when its coefficient is at least the second coefficient, and $L_r$
otherwise; give the second mass $S_r$ minus the first. This
maximizes that pair, including ties. At a vertex at least one ray
has either zero saturated or zero pure mass, so there are at most
three occupied pure/saturated pieces per parity. At $r=1$ both
masses are $1/4$; at $r=2$ a vertex has masses $0,1/4$.
There are then at most two pieces per parity.

These finite families satisfy the exact common Gram, failure
covariance and contrast equalities. Section 10 constructs them with
the two high labels in (GC.38), the complement in the plus fibre,
and the original cost and outputs. Their height matches the
universal endpoint bound, hence they are optimal. The inherited
four/five-low **feasibility** counts have not been promoted to
height-optimal counts, and six low have not been proved necessary.
$\square$

**Theorem 9.2 (attained maximal count on an open weak region).**
On the whole finite feasible original domain let
$M_{\max}=\max n(s,t)$. Under Assumption 1.2,
$$
M_{\max}\in\{8,9,10\}.
\tag{GC.42}
$$
It is attained at finite parameters, and
$$
\mathcal U_{\max}=
\{(s,A):t=e^A-1>t_0,
        0<s<s_0\tau_{\max}(t),
        n(s,t)=M_{\max}\}
\tag{GC.43}
$$
is nonempty and ordinary open in the original $(s,A)$ plane.

Proof. The weak upper bound is ten, the strong upper bound is eight
by Theorem 9.1, and ST supplies a weak open region with count eight.
The nonempty image of $n$ is thus a subset of the finite integer set
bounded by ten with at least one value eight. Its greatest value is
one of (GC.42) and occurs at a finite point. This argument uses no
compactification at infinite budget.

Theorem 8.1 makes the weak maximal stratum
$\{n>M_{\max}-1\}=\{n=M_{\max}\}$ relatively open.
Intersecting it with the strict weak interior gives an ordinary
open subset. If $M_{\max}=8$, ST's open eight-total region shows
this intersection is nonempty. If $M_{\max}=9$ or $10$, Theorem
5.2 excludes the entire weak minimum-budget boundary and Theorem
9.1 excludes the strong line. A maximizing point must have
$t>t_0$, $s<s_0\tau_{\max}(t)$, possibly $s=0$.
Its relatively open maximal neighborhood contains points with
$s>0$. Around any such point all weak feasibility inequalities
are strict, giving an ordinary open neighborhood with the same
maximal count. The smooth bijection $A=\log(1+t)$ preserves
openness. $\square$

**Corollary 9.3 (location of any larger-count obstruction).** A genuine
need for nine or ten total optimal labels cannot occur only on the
minimum-budget boundary, on an isolated interior transition, on the
strong line, or at an unattained infinite-budget limit. A maximal
count occurs on a nonempty open strict weak region. No location,
quantitative width, connectedness, ordering or uniqueness of its
optimal laws is asserted.

Proof. Theorem 9.2 gives the open region. Theorem 8.1 additionally
gives a relatively open maximal neighborhood at every weak
maximal-count point. $\square$

## 10. One common original chronological constructor

**Proposition 10.1 (full-fibre simultaneous realization).** Every finite
weak fractional-capacity family in (GC.9), and every finite strong
family used in Theorem 9.1, has one common original instrument
attaining its actual height, contrast, sharp worst-history jointly
acquired cost, complete output errors and activity bound. Its low
labels are exactly the occupied family atoms; it has one high label
in the weak case and the two high labels in the strong construction.
All five Borel failure components and arbitrary passive-reference
conditional operators have the original meanings.

Proof. Omit zero coefficient weights. For an occupied low label use
its actual $K_j$ and $N_j^{\,f}$. For a strong piece with coefficient
mass $p_j$ on ray $(\sigma,\upsilon)$ these mean explicitly
$K_j=\sqrt{p_j}K_{\sigma,\upsilon}$ and
$N_j^{\,f}=p_jb_jn_{\sigma,\upsilon}n_{\sigma,\upsilon}^T$,
with $b_j=0$ for its pure piece and $b_j=t\mathfrak c_f$ for its
saturated piece. Choose an isometry
$J_j:\mathbb C^2\to\operatorname{ran}K_j^\dagger$. Set
$$
\begin{gathered}
Q_j=J_j^\dagger(K_j^\dagger K_j+N_j^{\,f})J_j\succ0,\qquad
C_j=Q_j^{1/2}J_j^\dagger E^\dagger,\\
B_j=K_jJ_jQ_j^{-1/2},\qquad
F_j=Q_j^{-1/2}J_j^\dagger N_j^{\,f}J_jQ_j^{-1/2}.
\end{gathered}
\tag{GC.44}
$$
For the weak ray, $\ker K_h$ is spanned by
$(s_0,-bz/h_1,-dw/h_2)^T$ and is orthogonal to $n_h$.
Rank is two, including at the axes; the strong case follows by its
homogeneous rescaling. Thus the inverses in (GC.44) are on the
entire two-dimensional fibre, and
$$
B_jC_j=K_jE^\dagger,\quad
C_j^\dagger F_jC_j=EN_j^{\,f}E^\dagger,\quad
B_j^\dagger B_j+F_j=I_2,\quad I_2-F_j\succ0.
\tag{GC.45}
$$
FA's physical capacity identity gives the sole nonzero failure
eigenvalue and its odds:
$$
\lambda_j=\frac{b_j}{\mathfrak c(h_j)+b_j},\qquad
\frac{\lambda_j}{1-\lambda_j}=\frac{b_j}{\mathfrak c(h_j)}.
\tag{GC.46}
$$
For strong rays use $\mathfrak c_f$. Pure atoms have $F_j=0$.

Use the single common relative-time law
$$
g(a)=\frac2{(1+a)^2},\qquad G_{\rm time}(a)=\frac{2a}{1+a},\qquad
Z_j(a)=\sqrt{I_2-G_{\rm time}(a)F_j},\qquad
R_j(a)=g(a)F_j[I_2-G_{\rm time}(a)F_j]^{-1}.
\tag{GC.47}
$$
The not-yet-failed propagator from $a$ to $b$ is
$\operatorname{Ad}_{Z_j(b)Z_j(a)^{-1}}$.
On its current survivor matrix $Y$, the jump into the original
component $\ell$ has density
$$
Y\longmapsto w_\ell g(a)\,
 \operatorname{tr}\!\left(F_jZ_j(a)^{-1}YZ_j(a)^{-1}\right)P_f.
\tag{GC.48}
$$
This positive functional is CP. Summing the five jumps gives the
instantaneous survivor loss effect $R_j(a)$.
Pulled back to the initial decoder input, the jump density is
$w_\ell g(a)\operatorname{tr}(F_jY)P_f$.
At every cut its integrated effect plus the survivor effect is
$$
G_{\rm time}(a)F_j+Z_j(a)^\dagger Z_j(a)=I_2.
\tag{GC.49}
$$
Only terminal survivors receive
$EB_j(I_2-F_j)^{-1/2}$, an isometry by (GC.45).
The cumulative live map is $\operatorname{Ad}_{EB_j}$.
There is no terminal failure atom. Since all functions of $F_j$
commute and the largest eigenvalue controls the norm,
$$
\int_0^1\|R_j(a)\|\,da
 =-\log(1-\lambda_j)
 =\log(1+b_j/\mathfrak c(h_j))\le A,\qquad
I_2-F_j\succeq e^{-A}I_2.
\tag{GC.50}
$$
This bound holds on the entire qubit, not only on history-populated
vectors. Saturated atoms have activity $A$ and pure atoms activity
zero. The density $g$ is a sufficiency witness and is different from
the ideal $f_y$; all admitted original time laws remained in the
necessity arguments.

Choose isometries
$W_\perp:\mathbb C^2\to P^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$.
For weak families the single high encoder is
$$
C_H=\begin{pmatrix}\sqrt{1-\delta}\,DE^\dagger\\W_\perp^\dagger\end{pmatrix}
:\mathbb C^5\longrightarrow\mathbb C^3\oplus\mathbb C^2.
\tag{GC.51}
$$
Its entire five-dimensional joint fibre is counted, even though its
supported original-history part has rank three. Its rate is zero
and report is plus. Its terminal decoder has hidden Kraus matrices
$E[I_3\ 0]$ and $EJ_0[0\ I_2]$; their effects sum to $I_5$.
The hidden index is not a readable acquisition label. This is JR's
free coherent completion, not a certain-failure complement fixed in
a different completion class.

For the strong family use $H_\sigma$ from (GC.38).
The plus encoder is the stack of $H_+E^\dagger$ and
$W_\perp^\dagger$ into dimension five, with those same two hidden
terminal Kraus matrices. The minus encoder is $H_-E^\dagger$ into
dimension three with decoder $E$. Both have zero rate and report
$\sigma$. The two high actual labels, hidden Kraus multiplicity and
fibre dimensions remain different notions.

In the weak case the low live Gram is
$\operatorname{diag}(\delta,1,1)$ and the high part supplies
$(1-\delta)D^\dagger D$. In the strong case the low and high Grams
are $\operatorname{diag}(u_d,v_d,1)$ and
$\operatorname{diag}(1-u_d,1-v_d,0)$.
Their sum gives the same complete live map. Since
$\sum_jN_j^{\,f}=M$, root TP and the complement imply
$$
\sum_jC_j^\dagger C_j+\sum_{\rm high}C_H^\dagger C_H=I_5.
\tag{GC.52}
$$
Every acquisition is CP/TNI and their sum TP. For every complex
$X\in M_5$, the forgotten-label outputs are exactly
$$
\begin{aligned}
\Phi^L(X)
 &=E\left[\Lambda_*(E^\dagger XE)
       +J_0W_\perp^\dagger XW_\perp J_0^\dagger\right]E^\dagger,\\
\Lambda_*(Y)&=DYD^\dagger+TYT^\dagger+SYS^\dagger,\\
\Phi^f_\ell(\mathcal B)(X)
 &=w_\ell\left(\int_{\mathcal B}g(a)\,da\right)
               \operatorname{tr}(EME^\dagger X)P_f.
\end{aligned}
\tag{GC.53}
$$
The full live Gram gives the first identity on all complex matrices,
not just diagonal effects or the twelve test states. The pullback
of (GC.48) and $\sum N_j^{\,f}=M$ give the second on every Borel
subset, including the two zero components separately.

With any passive reference $R$, tensor every live Kraus matrix with
$I_R$. The failure conditional operator for a joint input $X$ is
$$
w_\ell\left(\int_{\mathcal B}g(a)\,da\right)P_f\otimes
 \operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
\tag{GC.54}
$$
This retains conditional reference operators and all live coherences.
No wrong-support, abort, singular-time or extra uncounted sector is
introduced.

For each original history the complement has zero probability. The
complete stopped-cq error, with $\rho_y=a_ya_y^T$, is
$$
e_y=\frac12\left[
 \|\Lambda_*(\rho_y)-\xi_y\xi_y^T\|_1+
 \sum_\ell w_\ell\int_0^1
 \left|\operatorname{tr}(M\rho_y)g(a)-\frac{6y}{(y+6a)^2}\right|da
 \right].
\tag{GC.55}
$$
Covariance gives the same value for all four sign pairs. The inherited
CG certificate gives $e_5=e_{27}=E_*$ and
$e_{16}<71/484<37/250<E_*$. Thus all twelve required errors are
preserved; they are not all equal.

For a weak label choose the deterministic report
$\operatorname{sgn}z_j$, with either fixed sign at zero.
Failure effects have zero $01$ entry, and the high report has no
relevant interference term. The complete live moments yield zero
total $z$ moment, so
$\mathsf V=s_0\sum_jp_j|z_j|\ge s$.
The actual label mass includes failure:
its signed height difference is $p_j(\ell+b_jf)$.
The high difference is $H_0>0$, proving (GC.9) directly for the
constructed actual record. No extra readable coin is introduced.

Only the high fibre has joint dimension at least three in the weak
construction. At height $y$ its probability is
$(1-\delta)A_y$, where $A_y=\sum_i h_i^2p_{yi}$.
Its maximum is at $27$ and equals the inherited sharp weak
$\mathsf C(s)$. In the strong construction the sum of high effects
is $(1-u_d)D^\dagger D+(1-v_d)T^\dagger T$ on the support, giving
the inherited sharp worst-history joint cost. Reports $\sigma$ on
the strong low and high rays give exactly
$\sqrt{u_dv_d}+\sqrt{(1-u_d)(1-v_d)}=s^\dagger$.

All operations are fixed before the sole unknown input. Equations
(GC.48)–(GC.49) give chronological FIRST time $6+a$; only survivors
receive the terminal isometry. Failed carriers receive no later
positive-carrier action. The instrument has finite positive survivors,
full-output TP at every cut, the entire-fibre activity bound, and
the exact actual label counts claimed. It supplies a mathematical
CP/TP realization, not native access, calibration, actuation or clock
permission. $\square$

## 11. Sharp missing theorem, literature interfaces and programme boundary

**Open problem 11.1 (sharp uniform original actual alphabet).** Determine
whether every finite feasible weak parameter admits an optimal
**original** common law with at most seven supported low actual
atoms $(h,\xi)$, $0\le\xi\le1$, preserving all common live/failure
moments, the contrast inequality and the true optimal height.
If so, (GC.10) and ST imply $M_{\max}=8$.
Otherwise prove genuine eight- or nine-low necessity on an interior
open region and a matching uniform upper bound to distinguish nine
from ten total. Theorem 9.2 localizes the obstruction but does not
choose among these three values.

A seven-**endpoint** theorem would suffice but is stronger than the
actual-count question: one minimum-count original label can have an
interior capacity fraction. A contact count, face-rank calculation,
SDP, KKT system, finite grid or quantifier-elimination prescription
does not supply the missing evaluated theorem. A universal
two-saturated-physical-line restriction is already false on ST's
open eight-total region.

**Convention 11.2 (mathematical provenance and literature scope).** The
proofs of Theorems 5.2, 7.3, 8.1, 9.1 and 9.2 and the scalar
comparison in §6 are repo-derived deductions under Assumption 1.2.
The common constructor specializes the published FA/RC constructor
to the same laws; it is not a new source or minimax certificate.
Elementary finite convex-hull representation, continuity of bounded
concave functions at relative interior points and compactness are used
at their stated finite-dimensional interfaces.

| Literature | Interface and unproved transfer |
| --- | --- |
| P. J. di Dio and K. Schmuedgen, *The multidimensional truncated Moment Problem: The Moment Cone*, [arXiv:1809.00584, §5 Theorem 19 and §7 Theorem 52](https://arxiv.org/abs/1809.00584) | Contextual finite moment-atom representation and its connected-component refinement. The full lift $(\Gamma,\lvert u\rvert,g_t)$ has at most ten coordinates and two circle components, consistent with nine low atoms. An exposed equality subset need not preserve connectedness, so this gives no seven-low theorem. The exact served HTML revision is not authenticated as a version-exact premise here. |
| H. Dette and V. B. Melas, *A note on the de la Garza phenomenon for locally optimal designs*, [arXiv:1105.3575v1, §3 Theorem 1](https://arxiv.org/abs/1105.3575v1), journal/PDF Theorem 3.1 | The ordinary Chebyshev-system and distinguished information-entry hypotheses are required. On eight pure-sheet points the last three columns of $\Gamma$ vanish, so the needed full determinant condition is unavailable. Information-matrix Loewner dominance has not been shown to preserve this absolute-height objective and joint physical covariance. |
| ST Convention 9.2 and RC whole-circle contact results | Their Fejér–Riesz, moment-duality and continuation interfaces retain their own hypotheses; none selects a complete global optimal contact inventory here. |

These literature interfaces are contextual, not additional
load-bearing source assumptions. There is no exhaustive literature
search, worldwide novelty or nonexistence claim.

**Open problem 11.3 (unchanged complete mathematical target).** The
original quantum-first AURIC FIB ATOM programme retains the complete
evaluated finite-$(s,A)$ roof for **every** common joint oriented
failure allocation and **all** live-height decompositions, including
ones below maximum contrast at a fixed allocation. It requires
selected roots, weights, contact ranges, universal necessity and
common original attainments throughout the plane. A fixed
decomposition, maximum-contrast facet, isolated seed, implicit
optimization or algorithm does not complete that target.

The unresolved atlas includes global ordering and certified connected
coverage from first activation to the later pure-contact seed and
$\lambda=1/4$ point, through the selected seam and the interval to
$\lambda=23/5$, as well as the whole plane. No event is declared
chronologically next. Maximal continuation ranges, all remaining
contact roots and multiplicities, height-sign and unused-root changes,
collisions, zero weights, rank, capacity and count transitions, and
their endpoint, threshold, budget and degenerate-orientation gluing
remain to be evaluated.

The precontact/contact coefficient $K(s)$ still requires its remaining
evaluated source parameters, physical orientations and coefficient
gluing beyond the credited suppliers. Existence is not evaluation
or continuity. Limiting transition-root isolation, multiplicities
and sign intervals, next terms, critical five-label/static-contact
interpolation and uniform joint-limit rates beyond the JS/WE/TC/SC
supplier scopes remain open. Limiting three-line structure does not
force a finite-activity optimizer support restriction. Exact strong
optimal counts remain distinct from the prior strong feasibility
counts and from Theorem 9.1's optimal upper bound.

**Convention 11.4 (unresolved native bridges).** Native
calibration/access, coherent jointly counted storage and accessible
shares, acquisition duration, actuation on every entire fibre,
alignment of the absolute FIRST clock, archive/source/epoch/controller
and permissions, and all quantum/native-count relations remain
separate unresolved premises. Control geometry supplies no physical
actuator or permission. No Weil or RH analogy transfers a quantum
theorem. The original through-2027 programme is neither completed nor
narrowed by the boundary counts or global localization in this volume.

## 追加锚（本行以下为增补区）

## 12. The common fractional law and its operational data

**Definition 12.1 (fractional lift of the same source).** Retain
Assumption 1.2, Definitions 2.1–3.2 and all the source quantities in
(GC.6)–(GC.13). In particular the source is one consistent isolated
root, all amplitudes and $m_1,m_2$ are positive, $0<\delta<1$, and
$\alpha,\beta>0$ with $\alpha+\beta=1$. For finite $t\ge t_0$ put
$$
\begin{gathered}
X=\{(u,v,\xi):u^2+v^2=1,\ 0\le\xi\le1\},\qquad
h=(1,u/\sqrt\alpha,v/\sqrt\beta),\qquad
b_x=t\mathfrak c(h)\xi,\\
\Gamma(x)=(1,u,v,u^2,uv,\xi\mathfrak c,
                    \xi\mathfrak c u^2,\xi\mathfrak c uv),\\
B(t)=(1,0,0,\alpha,0,\mu/t,\alpha V/t,0),\qquad
k(x)=|u|,\qquad g_t(x)=|\ell(h)+b_xf(h)|.
\end{gathered}
\tag{GC.56}
$$
A finite common law is $\pi=\sum_i p_i\delta_{x_i}$ with $p_i\ge0$
and $\sum_i p_i\Gamma(x_i)=B(t)$. Write
$K(\pi)=\sum p_i k(x_i)$ and $J_t(\pi)=\sum p_i g_t(x_i)$.
The symbols $K(\pi)$ and $J_t(\pi)$ are scalar functionals, distinct
from the live matrices $K_h$ and the row-space isometries of §10.
Define
$$
R_t(r)=\max\{J_t(\pi):\sum p_i\Gamma(x_i)=B(t),\ K(\pi)\ge r\}.
\tag{GC.57}
$$
Its request interval is $0\le r\le r_{\max}(t)$, where
$r_{\max}(t)=\sqrt\alpha\,\tau_{\max}(t)$. Then
$$
\mathcal T(s,t)=\frac{H_0+R_t(r)}2,\qquad
r=\frac{\sqrt\alpha}{s_0}s.
\tag{GC.58}
$$
Actual low labels remain the original pairs $(h,\xi)$; endpoint sheets
are the special cases $\xi=0,1$.

**Proposition 12.2 (complete joint constraints and finite realization).**
Under Assumption 1.2 the laws of Definition 12.1 are precisely the
finite weak laws (GC.9), with the same complete live Gram, failure
covariance, contrast and actual height. Their moment, contrast and
height vectors admit exact finite representations. The maximum in
(GC.57) exists, and $R_t$ is finite, concave and nonincreasing on its
request interval. Every finite law has the simultaneous original
realization of Proposition 10.1.

Proof. The first five moments give
$$
\sum p=1,\quad\sum pu=\sum pv=\sum puv=0,\quad
\sum pu^2=\alpha,\quad\sum pv^2=\beta.
$$
Rescaling $z=u/\sqrt\alpha$, $w=v/\sqrt\beta$ therefore gives
$\sum phh^T=I_3$, including all off-diagonal entries. The last three
moments, multiplied by $t$, give
$$
\sum pb_x=\mu,\qquad \sum pb_xz^2=V,\qquad
\sum pb_xzw=0.
$$
The identity $\alpha z^2+\beta w^2=1$ and
$\mu=\alpha V+\beta W$ then give $\sum pb_xw^2=W$.
Since $n_h=(0,dw/h_2,-bz/h_1)^T$, the two lower diagonal entries of
$\sum pb_xn_hn_h^T$ are $d^2W/h_2^2=m_1$ and
$b^2V/h_1^2=m_2$, and the cross entry vanishes. Its first row and
column vanish. Thus this sum is exactly $M$. Conversely the complete
Gram and $M$ recover these eight moments by the same equations and
the ellipse identity. No independent choice of a failure marginal is
involved. The capacity condition holds pointwise because
$0\le b_x\le t\mathfrak c(h)$.

Deterministic reports $\operatorname{sgn}z$ give
$\mathsf V=s_0K(\pi)/\sqrt\alpha$; a fixed choice at $z=0$ is harmless.
The signed acquired mass of label $i$ is
$p_i(\ell(h_i)+b_if(h_i))$, with live and eventual failure mass added
inside that label. The high signed mass is $H_0>0$, giving (GC.58).
The normalization $\sum p_i=1$ is for coefficient weights: the actual
supported acquisition effect is
$K_i^\dagger K_i+p_ib_in_{h_i}n_{h_i}^T$, rather than $p_iI$.

The capacity is continuous and strictly positive on the compact circle,
so $x\mapsto(\Gamma(x),k(x),g_t(x))$ has compact image. Its convex
hull in a finite-dimensional real space is compact: by the ordinary
finite-dimensional convex-hull theorem every point is a combination
of at most one more than the ambient dimension of image points, and
the corresponding finite simplex times compact power of $X$ is compact.
Integrals of these vectors against probability measures belong to the
same convex hull and hence have exact finite representations.
Intersecting with the moment target and the closed inequality $K\ge r$
is compact and nonempty at feasible requests. Maximizing its height
coordinate gives (GC.57). Mixtures of two common laws preserve the
moment target and give at least the mixed request with the mixed
height, proving concavity. Increasing a request shrinks the feasible
set, proving monotonicity. Boundedness follows from continuity of $g_t$.
This argument uses measures only for finite-dimensional convex geometry,
not a physical measurable disintegration.

For every occupied finite atom the established equalities are exactly
the same-joint-data premises of Proposition 10.1: complete live Gram
$I_3$, complete physical covariance $M$, the pointwise physical capacity
bound, and the requested contrast inequality. Thus that proposition
applies to this very law with its actual $p_i,h_i,b_i$, not to separately
chosen marginal representations. Its full-complex CP and Borel identities
(GC.53)–(GC.54) and actual height formula consequently apply. $\square$

## 13. Fixed coefficient states do not fix original contrast

**Theorem 13.1 (a fixed-block contrast obstruction).** Let $m>0$,
$a_c,b_c>0$, $a_c^2+b_c^2=1$, and fix the angular coefficient block
$$
C=m\operatorname{diag}(1,a_c^2,b_c^2)
 =\int(1,u,v)(1,u,v)^T\,d\zeta,\qquad u^2+v^2=1.
\tag{GC.59}
$$
Its unconstrained minimal null-ray length is three, but its maximum
contrast $\int|u|\,d\zeta=ma_c$ requires exactly four positive masses.
Coefficient states, even with a fixed complete saturated failure law,
therefore do not in general preserve original contrast under short
coefficient decompositions. For every $t>t_0$ this obstruction has the
finite original embedding specified below.

Proof. First identify precisely what the coefficient-state description
retains. This is a reuse of real null-cone and two-qubit moment-face
geometry inside the original contrast application. Set
$$
Q_\alpha=\operatorname{diag}(1,-\alpha,-\beta),\quad
\mathcal C_\alpha=\{B\in\operatorname{Sym}_3(\mathbb R):
 B\succeq0,\ \operatorname{tr}(Q_\alpha B)=0\},\quad
T_\alpha=\frac12
\begin{pmatrix}1&\sqrt\alpha&0\\0&0&\sqrt\beta\\
0&0&\sqrt\beta\\1&-\sqrt\alpha&0\end{pmatrix}.
\tag{GC.60}
$$
Use $\Gamma_B$ for second-factor partial transpose, to distinguish it
from the moment vector $\Gamma$. With
$s_-=(|01\rangle-|10\rangle)/\sqrt2$, define
$$
\mathcal F=\{\rho\succeq0:\rho^{\Gamma_B}\succeq0,
                       \ \rho s_-=\rho^{\Gamma_B}s_-=0\}.
$$
The real map $\Psi_\alpha(B)=T_\alpha BT_\alpha^T$ identifies
$\mathcal C_\alpha$ with this exposed PPT face, preserves rank and
satisfies $\rho^{\Gamma_B}=\rho$ on the face. Here are the full
support and field details needed for this application.

A Hermitian matrix annihilating $s_-$ has the form
$$
\rho=\begin{pmatrix}
A&B&B&C\\ \overline B&D&D&E_c\\
\overline B&D&D&E_c\\ \overline C&\overline E_c&\overline E_c&F_c
\end{pmatrix},\qquad A,D,F_c\in\mathbb R.
$$
The further equation $\rho^{\Gamma_B}s_-=0$ forces
$B,E_c\in\mathbb R$ and $C=D\in\mathbb R$ by its four entries.
Thus $\rho$ is real and partial-transpose invariant. Conversely
$T_\alpha$ has full column rank and image the symmetric tensor
subspace. In real coefficients
$$
\rho_{00,11}=(B_{00}-\alpha B_{11})/4,\qquad
\rho_{01,10}=\beta B_{22}/4.
$$
Their equality is exactly $\operatorname{tr}(Q_\alpha B)=0$.
The full-column-rank congruence and its left inverse preserve positivity
in both directions on this support and preserve rank. This proves the
claimed real cone correspondence, including singular elements.
For $P_-=|s_-\rangle\langle s_-|$, the functional
$$
\operatorname{tr}[(P_-+P_-^{\Gamma_B})\rho]
 =\langle s_-,\rho s_-\rangle+
   \langle s_-,\rho^{\Gamma_B}s_-\rangle
$$
is nonnegative on the PPT cone. Each summand vanishes exactly when
the respective positive operator annihilates $s_-$. Its zero set is
therefore $\mathcal F$, proving exposedness. Moreover
$$
T_\alpha^TT_\alpha=\tfrac12\operatorname{diag}(1,\alpha,\beta),
\qquad\operatorname{tr}\Psi_\alpha(B)=B_{00}.
$$
If a positive $B$ in this cone has $B_{00}=0$, its first row and
column vanish and $\alpha B_{11}+\beta B_{22}=0$ forces $B=0$.
Every nonzero element has positive trace, and normalized coefficient
states correspond exactly to $B_{00}=1$.

For completeness, the available length is a rank statement, including
all boundaries. Factor $B=AA^T$ with $A$ of full column rank $r$.
The real symmetric matrix $S_A=A^TQ_\alpha A$ has trace zero.
A zero-trace real symmetric matrix has a zero Rayleigh value on the
unit sphere: unless it is zero it has both a nonpositive and a
nonnegative eigenvalue and continuity gives such a vector. Compress
to its orthogonal complement; the trace remains zero. Induction gives
an orthonormal basis $o_1,\ldots,o_r$ with $o_i^TS_Ao_i=0$.
Consequently
$$
B=\sum_{i=1}^r(Ao_i)(Ao_i)^T
$$
is an $r$-term null-ray decomposition. Each $Ao_i$ is nonzero, and
its first coordinate is nonzero because
$x_0^2=\alpha x_1^2+\beta x_2^2$. Normalize it to $h=(1,z,w)$
and absorb its squared first coordinate into its positive weight.
The converse length lower bound is matrix rank.

Writing $u=\cos\phi$, $v=\sin\phi$ gives
$$
T_\alpha h(\phi)=\psi_\phi\otimes\psi_\phi,\qquad
\psi_\phi=(\cos(\phi/2),\sin(\phi/2))^T.
\tag{GC.61}
$$
No antipodal averaging of $\phi$ and $\phi+\pi$ is performed.
In any complex positive pure-product decomposition of an element of
$\mathcal F$, the first kernel condition forces each positive
$v\otimes w$ to be orthogonal to $s_-$, hence $v\parallel w$.
Applying the second kernel condition to the partial-transpose
summands forces $v\parallel\overline w$. Thus the projective factor
is real and every summand is one of (GC.61). This argument uses
positivity term by term and also applies to singular states. The
complex separable length is therefore the same rank. Rank zero has
the empty decomposition; rank one one ray; rank two two rays and a
normalized exposed chord; rank three lies in the relative interior
and has length three. To see the rank-two chord assertion, expose
its support by a nonzero null-vector functional $B\mapsto w^TBw$.
On its two-dimensional range the restricted null equation has exactly
two projective rays: it is indefinite, since its trace against a
positive definite rank-two factor is zero, and cannot vanish
identically because $Q_\alpha$ has no two-dimensional totally
isotropic real subspace. The normalized face is their chord.
Positive definite matrices give the relative interior in rank three.
For $B=I_3$ the eigenvalues of $\Psi_\alpha(B)$ are
$1/2,\alpha/2,\beta/2,0$, and both kernels are exactly $\mathbb Cs_-$.

The real-field condition cannot be dropped. For $0<\varepsilon<1$,
$$
B=I_3+i\varepsilon(E_{01}-E_{10})\succ0,\qquad
\operatorname{tr}(Q_\alpha B)=0,
$$
has eigenvalues $1,1+\varepsilon,1-\varepsilon$. Yet the middle
$2\times2$ principal minor of
$(T_\alpha BT_\alpha^*)^{\Gamma_B}$ is
$$
(\beta/4)^2-|\beta/4-i\varepsilon\sqrt\alpha/2|^2
 =-\alpha\varepsilon^2/4<0.
$$
It does not define a PPT state.

This coefficient face is the known $G_{3,3}$ trigonometric moment
face: Kye, *Faces for two qubit separable states and the convex hulls
of trigonometric moment curves*,
[arXiv:1302.2226v1, §4, (7)–(11), Theorems 5.1–5.2](https://arxiv.org/pdf/1302.2226v1).
Indeed for $U=2^{-1/2}\begin{pmatrix}1&i\\1&-i\end{pmatrix}$,
$$
(\overline U\otimes U)(\psi_\phi\otimes\psi_\phi)
 =\tfrac12(1,e^{i\phi})^T\otimes(1,e^{-i\phi})^T,
$$
with $\omega=e^{-i\phi}$ in the convention
$(1,\overline\omega)\otimes(1,\omega)$. Chen–Đoković,
[arXiv:1210.0111v2, Table I and Theorem 23](https://arxiv.org/pdf/1210.0111v2),
also supplies the relevant birank $(2,2)$ and $(3,3)$ length facts.
The normalized slice is affinely the circle moment body
$\operatorname{conv}\{(\omega,\omega^2):|\omega|=1\}$: with
$\omega=u-iv$, its first complex moment records the two first
angular moments and its second records $u^2-v^2$ and $-2uv$.
Together with mass one and $u^2+v^2=1$, these recover every entry
of the angular Gram, and conversely that Gram recovers both complex
moments. The symmetric-support argument is consistent with
Bohnet-Waldraff–Braun–Giraud,
[arXiv:1606.07635v1, Theorem 1](https://arxiv.org/pdf/1606.07635v1);
the second kernel condition here supplies the further real-circle
restriction. Giraud–Braun–Braun,
[arXiv:0805.2592v1, §III.B, (12)–(21)](https://arxiv.org/pdf/0805.2592v1),
uses the spin-one first/second moment criterion $W-uu^T\succeq0$
and positive coherent-state representations. These are established
coefficient geometry and moment results reused here; their short
lengths do not preserve extra original resource functionals.

Now apply this distinction to (GC.59). Cauchy gives
$$
\int|u|\,d\zeta\le
\sqrt{\left(\int1\,d\zeta\right)\left(\int u^2\,d\zeta\right)}=ma_c.
$$
Equality forces $|u|=a_c$ almost everywhere, hence $|v|=b_c$.
Write the four possible masses as
$m(1+\sigma X+\upsilon Y+\sigma\upsilon Z)/4$.
The zero $u,v,uv$ moments force $X=Y=Z=0$. All four masses
are $m/4>0$, and conversely these four masses attain the bound.
Axis masses $ma_c^2/2$ at each $(\pm1,0)$ and
$mb_c^2/2$ at each $(0,\pm1)$ give the same block but contrast
$ma_c^2<ma_c$. A length-three representation is also explicit:
mass $ma_c^2/(1+a_c^2)$ at $(1,0)$ and mass
$m/[2(1+a_c^2)]$ at each
$(-a_c^2,\pm\sqrt{1-a_c^4})$. Its first and mixed moments vanish,
its second moments are $ma_c^2,mb_c^2$, and its contrast is
$2ma_c^2/(1+a_c^2)<ma_c$. The angular block is congruent to a
rank-three member of (GC.60), explaining exactly the unconstrained
length and why it does not solve the contrast-constrained problem.

For the original embedding fix any $t>t_0$ and retain one and the
same saturated law
$$
p^F_{\sigma,\upsilon}=q/4,\qquad
h^F_{\sigma,\upsilon}=(1,\sigma\sqrt{u_F},\upsilon\sqrt{v_F}),
\qquad b_F=t\mathfrak c_f,\qquad q=\nu/t.
\tag{GC.62}
$$
Since $qt\mathfrak c_f=\mu$, its complete failure covariance is
$M$: its signed mixed moment vanishes and its $z^2,w^2$ intensity
moments are $V,W$. Its live block is
$\operatorname{diag}(q,qu_F,qv_F)$. The residual pure block
$$
B_R=\operatorname{diag}(r_0,r_1,r_2)
 =\operatorname{diag}(1-q,1-qu_F,1-qv_F)\succ0
\tag{GC.63}
$$
is $Q_\alpha$-null. Represent it either by the four signs
$(1,\sigma\sqrt{r_1/r_0},\upsilon\sqrt{r_2/r_0})$, each mass
$r_0/4$, or by the pure axes $(1,\pm1/\sqrt\alpha,0)$, each mass
$\alpha r_1/2$, and $(1,0,\pm1/\sqrt\beta)$, each mass
$\beta r_2/2$. Both are normalized with the unchanged $F$ law,
satisfy the whole live Gram and $M$, and satisfy all pure/saturated
capacity inequalities. Their original $z$-contrast sums are respectively
$$
\tau_{\rm rect}=q\sqrt{u_F}+\sqrt{r_0r_1}=\tau_{\max}(t),\qquad
\tau_{\rm axes}=q\sqrt{u_F}+\sqrt\alpha\,r_1.
\tag{GC.64}
$$
The strict inequality follows from
$r_0r_1-\alpha r_1^2=\beta r_1r_2>0$; physical contrast is
$s_0\tau$. Proposition 12.2 verifies Proposition 10.1's premises
for each finite family, so both are original feasible instruments.
The pure block can alternatively be given the preceding three-point
representation after angular rescaling. In particular a shorter
coefficient representation need not meet the original contrast request.

Fixing each sheet's coefficient block is stronger than the original
aggregate constraint: the original law permits opposite sheetwise
odd moments that cancel. These examples prove feasible data
insufficiency, not eight-low optimal necessity. Finally $T_\alpha$
and $U$ act on auxiliary coefficient geometry. They are not local
channels on the original $M_5$ acquisition or its Choi support, and
do not remove its physical product-vector obstruction. A same-named
PPT condition, full-support maximally correlated condition, exact
zero-leakage condition or finite LOSR construction supplies no map
preserving the original source, cost, capacity and recorded height
without an additional proved operational correspondence. $\square$

## 14. Fixed coefficient blocks and contrast still miss height

**Assumption 14.1 (signed pure interface and full support).** In addition
to Assumption 1.2, assume the signed pure-contact information of the
connected-interval source, Definition 3.1 and its strict signed geometry:
there are two circle points with $u<0$ and with respectively
$\ell>0$ and $\ell<0$. In that contact indexing they are pure
indices $1$ and $2$, with report sign $-$ and height signs $+$ and
$-$, respectively. Only these signed points are required here; no
numeric contact table or enlarged budget interval is required.
At a strict weak request, use RC §68's jointly feasible two-sheet
law whose pure component $\mu_0$ has full circle support and whose
achieved contrast strictly exceeds the request, as described in §7.
Keep its jointly feasible saturated component $\mu_1$. Full support
means every nonempty open arc has positive $\mu_0$ mass; it does
not require a uniform positive density lower bound.

**Theorem 14.2 (height does not factor through block states and contrast).**
Under Assumption 14.1 there are two finite original common laws with
identical pure and saturated coefficient blocks, the same saturated
law and complete failure covariance $M$, and identical actual
contrast, but different actual TV heights. These are feasible laws;
no optimum-preserving perturbation is asserted.

Proof. In $L^2(\mu_0;\mathbb R)$ take the finite-dimensional closed
space
$$
\mathcal V=\operatorname{span}_{\mathbb R}
                  \{1,u,v,u^2,uv,|u|\}.
$$
First $|\ell|\notin\mathcal V$. Otherwise a continuous representative
of a function $P\in\mathcal V$ would equal $|\ell|$ almost everywhere.
Full support makes this equality pointwise: a nonzero continuous
difference at a point is bounded away from zero on an arc of positive
measure. On the connected open half-circle $u<0$, the function $P$
is an analytic trigonometric polynomial of degree at most two because
$|u|=-u$. So is $\ell$. Near the assumed positive signed point,
$P=\ell$ on a nonempty open interval. The real analytic identity
theorem makes $P=\ell$ on the whole connected half-circle. Near the
negative signed point this contradicts $P=|\ell|=-\ell$.
Strict signs provide open intervals, so no claim about a zero-height
point is used in this step.

Let $q_\perp=|\ell|-\Pi_{\mathcal V}|\ell|$. The projection has a
continuous representative, even if the displayed spanning functions
are linearly dependent; full support identifies continuous
representatives uniquely. Thus $q_\perp$ is bounded, continuous,
nonzero and
$$
\int q_\perp P\,d\mu_0=0\quad(P\in\mathcal V),\qquad
\int q_\perp|\ell|\,d\mu_0=\|q_\perp\|_{L^2(\mu_0)}^2>0.
$$
Choose $0<\varepsilon<\|q_\perp\|_\infty^{-1}$ and put
$$
d\mu_0^\pm=(1\pm\varepsilon q_\perp)d\mu_0,\qquad
\mu_1^\pm=\mu_1.
\tag{GC.65}
$$
Both densities are strictly positive. Orthogonality preserves mass,
all pure Gram entries (using $v^2=1-u^2$), and pure contrast.
The saturated law, its complete live and capacity moments, its
failure covariance and its height are unchanged. Hence both common
laws meet the same moment target and the same original contrast
inequality, with the baseline's strict slack. Their low heights
differ by $2\varepsilon\|q_\perp\|_2^2$ and their actual TV values
by $\varepsilon\|q_\perp\|_2^2>0$, because actual TV includes HALF
the low-height sum. Their individual TV shifts from the baseline
are $\pm\varepsilon\|q_\perp\|_2^2/2$.

To obtain finite laws, for each $\mu_0^\pm$ preserve exactly the
vector
$(1,u,v,u^2,uv,|u|,|\ell|)$ by a compact-image finite convex
representation. For the saturated law perform this representation
once, preserving its full live Gram, all three capacity moments,
contrast and saturated absolute height, and use that same finite
saturated law for both choices. All these integrands are continuous.
The pure masses are positive before zero terms are omitted; both
component masses and hence total coefficient normalization are
preserved. Each recovered atom has $\xi=0$ or $1$ and legal capacity.
The joint equations from Proposition 12.2 still give exactly $I_3$
and $M$. The strict height difference and identical contrast remain.
These finite laws satisfy every premise of Proposition 10.1 and thus
have common original CP/TP realizations with all original outputs
and resources. No continuous physical disintegration has been added.
The full-support baseline is merely feasible; this proof does not
place the perturbation on an optimal face. $\square$

## 15. Exact fractional merge loss in an original finite common law

**Theorem 15.1 (merge defect, including zero cases).** At one fixed
original direction $h$, let a pure endpoint have coefficient mass
$a_p\ge0$ and a saturated endpoint have mass $a_s\ge0$. Put
$H_p=\ell(h)$ and $H_s=\ell(h)+t\mathfrak c(h)f(h)$.
If $a_p+a_s>0$, replacing the pair by the single original atom
$$
p=a_p+a_s,\qquad \xi=\frac{a_s}{a_p+a_s},\qquad
b=t\mathfrak c(h)\xi
\tag{GC.66}
$$
preserves complete live and failure moments, normalization and
contrast. Its low-height loss and actual TV loss are respectively
$$
\begin{aligned}
D_{\rm low}
 &=a_p|H_p|+a_s|H_s|-|a_pH_p+a_sH_s|,\\
D_{\rm TV}&=D_{\rm low}/2.
\end{aligned}
\tag{GC.67}
$$
If both masses are positive, the loss is zero exactly when
$H_pH_s\ge0$, and when $H_pH_s<0$ it is
$$
D_{\rm low}=2\min\{a_p|H_p|,a_s|H_s|\},\qquad
D_{\rm TV}=\min\{a_p|H_p|,a_s|H_s|\}.
\tag{GC.68}
$$
If either mass is zero the loss is zero irrespective of the two
height signs; if both vanish the label is omitted.

Proof. The live contribution is $(a_p+a_s)hh^T$ both before and
after merging. The failure contribution is
$a_st\mathfrak c(h)n_hn_h^T$ in both cases. The contrast contribution
is $(a_p+a_s)|u|$, and (GC.66) lies in the allowed capacity interval.
The merged signed height is $a_pH_p+a_sH_s$, which proves (GC.67).
For two nonzero real numbers, equality in the triangle inequality
holds exactly when they have the same sign; if one is zero equality
also holds. With positive masses these are precisely $H_pH_s\ge0$.
For opposite signs put $A=a_p|H_p|$, $B=a_s|H_s|$; then
$A+B-|A-B|=2\min(A,B)$. Zero masses and zero heights give the
stated cases directly. The high contribution stays fixed, so HALF
gives the actual TV formulas. $\square$

**Theorem 15.2 (finite source-compatible opposite-sign embedding).**
For the original source define
$$
h_*=(1,0,1/\sqrt\beta),\qquad
f_*=-\frac{11d^2}{64h_2^2\beta}<0,\qquad
\ell_*=\delta N_{00}+\frac{N_{22}}\beta+
                    \frac{2\sqrt\delta N_{02}}{\sqrt\beta}>0.
\tag{GC.69}
$$
For every finite
$$
t>\max\left\{t_0,\frac{\ell_*}{\mathfrak c(h_*)|f_*|}\right\}
\tag{GC.70}
$$
there is a finite original feasible common law with positive pure and
saturated masses at this same $h_*$. Merging just that pair strictly
lowers actual TV by (GC.68), preserving all common moments and
contrast. No optimality of this law is asserted.

Proof. Formula (GC.28) gives
$\Delta_{11}=-11/64$, $\Delta_{22}=0$, $\Delta_{02}>0$.
The source matrices therefore give
$$
N_{22}=11d^2/64>0,\qquad
N_{02}=(h_0c+h_2d)\Delta_{02}>0.
$$
Together with $N_{00}>0$, these prove (GC.69), including the cross
term in $\ell_*$. The point $h_*$ is on the ellipse, and (GC.70)
makes its pure signed height positive and its saturated signed height
strictly negative.

It remains to place both endpoint masses in the same legal common
law. Work first with failure intensity, whose measure is $t\mathfrak c$
times saturated coefficient measure. Choose a sufficiently small
$a_0>0$ with $a_0<\beta W$ and put intensity $a_0/2$ at each
unit-circle point $(u,v)=(0,\pm1)$. Put intensity
$(\mu-a_0)/4$ at each of the four sign points with
$$
u_c^2=\frac{\alpha V}{\mu-a_0},\qquad
v_c^2=\frac{\beta W-a_0}{\mu-a_0}.
\tag{GC.71}
$$
Both squares are strictly positive, sum to one, and are below one:
$\mu=\alpha V+\beta W$ and $a_0<\beta W$ imply each assertion.
The full intensity moments are
$$
\int1=\mu,\qquad\int u^2=\alpha V,\qquad\int uv=0.
$$
Dividing each intensity weight by its own positive
$t\mathfrak c(h)$ gives legal saturated coefficient masses. The
capacity depends only on squared coordinates, so sign symmetry
makes their live Gram diagonal. Their complete physical failure
covariance is $M$ by Proposition 12.2.

At $a_0=0$ the four sign points are precisely (GC.62) in angular
coordinates, since $u_c^2=\alpha u_F$ and $v_c^2=\beta v_F$.
Their residual pure Gram is (GC.63), strictly positive for $t>t_0$.
Weights, coordinates and capacities are continuous as $a_0\downarrow0$,
so the residual diagonal remains strictly positive for sufficiently
small $a_0>0$. From this residual subtract a pure axial pair at
$(0,\pm1)$, of total coefficient mass $\eta>0$ small enough to
leave every diagonal entry positive. Its Gram is
$\eta\operatorname{diag}(1,0,1/\beta)$. If the remaining diagonal
is $(r_0,r_1,r_2)$, each subtraction has zero $Q_\alpha$ trace, so
$$
r_0=\alpha r_1+\beta r_2>0.
$$
Represent it explicitly by four pure rays
$$
h_{\sigma,\upsilon}=
 (1,\sigma\sqrt{r_1/r_0},\upsilon\sqrt{r_2/r_0}),\qquad
p_{\sigma,\upsilon}=r_0/4.
\tag{GC.72}
$$
They lie on the original ellipse, have exactly that diagonal Gram
and zero odd and mixed moments. Together with the pure axial pair
and the six saturated points they have total live Gram $I_3$ and
hence coefficient mass one. All masses are positive, all capacities
are pure or saturated, and the failure sum is exactly $M$.
In particular $h_*$ has pure mass $\eta/2>0$ and saturated mass
$a_0/[2t\mathfrak c(h_*)]>0$ in this very finite law.
Take as a requested contrast its achieved contrast, or any smaller
nonnegative request. Proposition 12.2 verifies every common-data
premise of Proposition 10.1, so the law is an original feasible
instrument with the sharp weak joint cost and complete outputs.
Only the positive-$v$ pair is merged in (GC.66). Its strict opposite
heights give the asserted loss, while every moment and its achieved
contrast are unchanged. $\square$

**Proposition 15.3 (one explicit finite conditional parameter choice).**
Under the same isolated-source enclosure of Definition 6.1, the
construction of Theorem 15.2 is valid with
$t=10^6$, $a_0=1/100$ and pure axial total mass $\eta=1/100$.
The following bounds specify sufficient conditional constants. Every
endpoint integer in the table is divided by $10^{12}$.

| Expression | Lower numerator | Upper numerator |
| --- | --- | --- |
| $N_{00}$ | $80796697284$ | $80796697285$ |
| $\ell_*$ | $27612835160$ | $27612835161$ |
| $f_*$ | $-20930231667$ | $-20930231666$ |
| $\mathfrak c(h_*)$ | $64355091074$ | $64355091075$ |
| $H_s(h_*)$ at $t=10^6$ | $-1346939352248332$ | $-1346939352248331$ |
| Total saturated axial coefficient mass $s_a$ | $155387$ | $155388$ |
| Total saturated four-sign coefficient mass $s_c$ | $88404744$ | $88404745$ |
| Remaining pure $r_0$ after subtracting $\eta$ | $989911439867$ | $989911439868$ |
| Remaining pure $r_1$ after subtracting $\eta$ | $999936056547$ | $999936056548$ |
| Remaining pure $r_2$ after subtracting $\eta$ | $917959691100$ | $917959691101$ |

Proof. These are enclosures of the following explicit expressions,
with the rational outward operations and square-root rule (GC.27)
on the source rows of Definition 6.1. Put
$$
\begin{gathered}
z_c^2=\frac V{\mu-a_0},\qquad
w_c^2=\frac{\beta W-a_0}{\beta(\mu-a_0)},\qquad
c_c=\mathfrak c(1,\sqrt{z_c^2},\sqrt{w_c^2}),\\
s_a=\frac{a_0}{10^6\mathfrak c(h_*)},\qquad
s_c=\frac{\mu-a_0}{10^6c_c},\\
r_0=1-s_a-s_c-\eta,\quad r_1=1-s_cz_c^2,\quad
r_2=1-s_a/\beta-s_cw_c^2-\eta/\beta.
\end{gathered}
\tag{GC.73}
$$
The source rows also imply the coarse rational bounds
$13/1000<\theta<15/1000$, $1/1000<\omega<3/1000$ and
$30<W<40$, directly by multiplication and reciprocal endpoint
bounds in (GC.6) and (GC.12). Hence
$\beta W=\omega W/(\theta+\omega)>5/3>1/100$.
Proposition 6.2 gives $t_0<265<10^6$. Thus all denominators in
(GC.71) and (GC.73) are positive and both circle squares are interior.
Use (GC.28) to form $N$, then (GC.69), the capacity formula and
(GC.73); outward enclosure and rounding to the displayed denominator
give the table. In particular $H_p>0>H_s$, $s_a,s_c>0$ and
$r_0,r_1,r_2>0$. These strict inequalities justify the chosen
positive $\eta$ and the four-sign residual (GC.72), so the exact
common-law identities follow from Theorem 15.2. The resulting finite
example has positive pure and saturated masses at $h_*$ and strictly
positive merge loss.

These constants are conditional source-enclosure bounds. They do
not isolate the original root or assert TP at unrelated off-root
points of its rectangular enclosure. The general proof for all
eligible finite $t$ is the small-mass argument of Theorem 15.2;
this single parameter choice makes no universal count or optimality
claim. $\square$

## 16. Contrast endpoints of original multiplier faces

**Definition 16.1 (multiplier face).** For fixed finite feasible weak
$t$ and $\lambda\ge0$ define
$$
C_t(\lambda)=\max_{\sum p\Gamma=B(t)}
                    \sum p(g_t+\lambda k).
\tag{GC.74}
$$
Its optimal face consists of common laws attaining this value.
Let $r_-(t,\lambda)$ and $r_+(t,\lambda)$ be the minimum and
maximum achieved $K$ on that face. A law on the face need not be
optimal for an arbitrary larger requested contrast.

**Theorem 16.2 (eight low atoms at both face contrast extrema).**
Both $r_-$ and $r_+$ have multiplier-optimal realizations with at
most eight original supported low atoms. They may also be chosen
as endpoint atoms. This is a statement about contrast extrema on
one common multiplier face, not all its interior contrasts.

Proof. Compactness of the finite-dimensional vector hull in
Proposition 12.2 gives each contrast extremum and an exact finite
law attaining it. Omit zero weights. Suppose a contrast-maximizing
law has $N>8$ positive weights. Its eight-component moment columns
have a nonzero real dependence $c=(c_i)$ with
$\sum c_i\Gamma(x_i)=0$. Since the first coordinate is one,
$\sum c_i=0$; the vector has both positive and negative entries.
For all sufficiently small positive $\varepsilon$, both
$p+\varepsilon c$ and $p-\varepsilon c$ are nonnegative and
preserve all joint moments. Multiplier maximality in both directions
forces
$$
\sum c_i(g_t(x_i)+\lambda k(x_i))=0.
$$
Thus both perturbations stay on the same multiplier-optimal face.
Contrast maximality there forces $\sum c_i k(x_i)=0$, and
therefore $\sum c_i g_t(x_i)=0$. Move in either direction to the
finite endpoint of the interval of nonnegative weights. At least
one weight vanishes; the moment target, multiplier optimum and
contrast extremum are retained. Repeat with the remaining positive
weights until at most eight remain. For the contrast minimum the
same two-sided argument reverses only the extremality inequality,
so gives exactly the same conclusion. No independence or generic
rank of the eight moments is assumed.

For the endpoint version first split each fractional atom into
$(h,0)$ and $(h,1)$ with weights $p(1-\xi)$ and $p\xi$.
All moments and contrast stay fixed, and convexity of the absolute
value makes height nondecreasing. A strict increase would exceed
$C_t(\lambda)$; hence equality holds. This split law is still a
contrast extremum on the multiplier face. Apply the same elimination
within its finite endpoint table. Zero split masses are omitted.
This is the classical finite linear-programming face-elimination
argument applied to the original joint constraint table. $\square$

**Theorem 16.3 (platform endpoint and non-affine requests).** Every
request on the height-maximizing platform, including its right
endpoint, has an original optimum with at most eight supported low
atoms. At an interior strict weak request, the same bound holds
whenever the request is not in the interior of any nontrivial
strictly decreasing affine segment of $R_t$.

Proof. At $\lambda=0$ let $r_P=r_+(t,0)$, the largest achieved
contrast among all unrestricted height maximizers. Theorem 16.2
provides such a maximizer with at most eight low atoms. It meets
every request $0\le r\le r_P$ and attains the unrestricted height
$C_t(0)$, proving the assertion also at $r=r_P$. Conversely if
$R_t(r)=C_t(0)$, its attained law is on this same face, so
$r\le r_P$. This identifies the entire platform, including a
platform consisting of a single request or extending to the whole
request interval.

Now let $r_P<r<r_{\max}(t)$. Finiteness and concavity of $R_t$
on the interval give a finite supporting slope $-\lambda$:
$$
R_t(q)\le R_t(r)-\lambda(q-r)\qquad(0\le q\le r_{\max}(t)).
\tag{GC.75}
$$
Monotonicity permits $\lambda\ge0$; comparison with $q=r_P$
forces $\lambda>0$, because $R_t(r)<C_t(0)$.
Every optimizer at request $r$ has $K=r$. Indeed if $K>r$, its
height is at most $R_t(K)$, which (GC.75) makes strictly less than
$R_t(r)$. For any common law with achieved $K$ and height $J$,
$J\le R_t(K)$, so (GC.75) yields
$J+\lambda K\le R_t(r)+\lambda r$. Equality at the request
optimizer proves
$C_t(\lambda)=R_t(r)+\lambda r$ and multiplier optimality of
that same law.

Write $r_-=r_-(t,\lambda)$ and $r_+=r_+(t,\lambda)$.
The active optimizer shows $r\in[r_-,r_+]$. The endpoint laws
of Theorem 16.2 have heights $C_t(\lambda)-\lambda r_\pm$.
For each $q\in[r_-,r_+]$, a mixture of the two laws achieves
exact contrast $q$ and height $C_t(\lambda)-\lambda q$.
Every competitor with achieved $K'\ge q$ obeys
$$
J'\le C_t(\lambda)-\lambda K'
                  \le C_t(\lambda)-\lambda q.
\tag{GC.76}
$$
Consequently
$$
R_t(q)=C_t(\lambda)-\lambda q
               \quad(q\in[r_-,r_+]).
\tag{GC.77}
$$
Both endpoints are global optima for their own requested contrasts
and have at most eight low atoms. If $r$ is not interior to a
nontrivial strictly decreasing affine segment, it must be one of
these endpoints (possibly both), and has the same eight-low bound.
If such an affine segment exists, this proof supplies only its two
contrast endpoints. It supplies no universal eight-low bound for
the segment's interior. Every finite law here satisfies (GC.56)
and the pointwise fractional capacity condition, so its realization
is by Proposition 12.2 with the original contrast inequality.
$\square$

## 17. Genuine nine-low necessity forces two-sided affine coexistence

**Theorem 17.1 (exact ranks and fixed-fraction two-sided elimination).**
Assume a strict weak point $t>t_0$, $0<r<r_{\max}(t)$ genuinely
requires nine supported low actual labels at the optimal height.
Choose a minimum optimizer
$\pi=\sum_{i=1}^9p_i\delta_{x_i}$ with every $p_i>0$. Put
$$
A_\Gamma=[\Gamma(x_1)\ \cdots\ \Gamma(x_9)],\qquad
\widehat A=\begin{pmatrix}A_\Gamma\\k(x_1)\ \cdots\ k(x_9)\end{pmatrix}.
$$
Then
$$
\operatorname{rank}A_\Gamma=8,\qquad
\operatorname{rank}\widehat A=9.
\tag{GC.78}
$$
The contrast inequality is active. There exist $\lambda>0$ and
explicit original common laws $\pi_-,\pi_+$, each with at most
eight positive low atoms on the very same $h_i,\xi_i$ table,
that are global optima at contrasts $r_-<r<r_+$. On the whole
$[r_-,r_+]$ the value is strictly decreasing and affine.

Proof. If $\operatorname{rank}\widehat A\le8$, choose a nonzero
$c\in\ker\widehat A$. Its moment first coordinate gives
$\sum c_i=0$, hence both signs. For sufficiently small positive
$\varepsilon$ the two laws $p\pm\varepsilon c$ preserve all
moments and achieved contrast and remain feasible at the original
request, whether or not that request was initially active. Optimality
in both directions forces $\sum c_i g_t(x_i)=0$. Moving to a
nonnegative-weight endpoint deletes a positive atom without changing
height or feasibility. This contradicts nine-low necessity.
Thus $\operatorname{rank}\widehat A=9$. Adding one row increases
rank by at most one, and $A_\Gamma$ has eight rows, so its rank
is exactly eight, with a one-dimensional kernel.

The platform assertion of Theorem 16.3 excludes the platform.
The supporting-line proof there provides $\lambda>0$, proves
$K(\pi)=r$, and makes $\pi$ multiplier-optimal at this $\lambda$.
For a nonzero generator $c\in\ker A_\Gamma$ one has
$d=\sum c_i k(x_i)\ne0$, since otherwise
$c\in\ker\widehat A$. Choose its orientation so $d>0$. Define
$$
\begin{gathered}
a_+=\min_{c_i<0}\frac{p_i}{-c_i}>0,\qquad
a_-=\min_{c_i>0}\frac{p_i}{c_i}>0,\\
p_i^+=p_i+a_+c_i,\qquad p_i^-=p_i-a_-c_i,\qquad
\pi_\pm=\sum_i p_i^\pm\delta_{x_i}.
\end{gathered}
\tag{GC.79}
$$
Both index sets are nonempty because $\sum c_i=0$ and $c\ne0$.
The minima are finite and strictly positive. Every new weight is
nonnegative and at least one is zero at each endpoint. Thus each
law has at most eight positive atoms, remains normalized, and
preserves all eight joint moments. Coordinates with $c_i=0$ retain
their positive weights; multiple simultaneous zero weights only
further reduce the count. All original $h_i$, all fractions $\xi_i$
and the capacities $b_i=t\mathfrak c(h_i)\xi_i$ are fixed.
There is no endpoint splitting or doubling of labels.

Two-sided small moment-preserving perturbations and multiplier
optimality force
$$
\sum_i c_i g_t(x_i)=-\lambda d.
$$
Writing $v=R_t(r)$, the two new laws have
$$
\begin{gathered}
r_+=r+a_+d,\quad r_-=r-a_-d,\qquad
v_+=v-\lambda a_+d,\quad v_-=v+\lambda a_-d,\\
\pi=\frac{a_+\pi_-+a_-\pi_+}{a_++a_-}.
\end{gathered}
\tag{GC.80}
$$
Both contrasts are feasible achieved contrasts, so belong to the
request interval, and $r_-<r<r_+$. The laws attain
$C_t(\lambda)-\lambda r_\pm$; inequality (GC.76) for every
competitor proves they are global optima at their own requests.
Mixtures prove (GC.77) on this whole interval. Therefore the original
request has a genuine neighborhood of strictly decreasing affine
optimal height.

The moments in (GC.79) are the original complete joint data, not
just an augmented matrix of unrelated marginal values.
Proposition 12.2 gives the exact live Gram and $M$ for both endpoint
laws, with legal unchanged fractions. Proposition 10.1 consequently
supplies a finite original instrument at each new request: its
actual height is the proved global value and all original error,
sharp joint cost, activity and reference/Borel constraints hold
simultaneously. The one-high completion is the same type of coherent
completion as for the original law; no additional readable Kraus
indices occur. $\square$

**Corollary 17.2 (physical strength slope).** On the affine interval
in Theorem 17.1 the physical value has slope
$$
\frac{\partial\mathcal T}{\partial s}
             =-\frac{\lambda\sqrt\alpha}{2s_0}<0.
\tag{GC.81}
$$

Proof. Equation (GC.58) adds the constant high contribution and divides
the low height by two, while $dr/ds=\sqrt\alpha/s_0$.
Equation (GC.77) gives $dR_t/dr=-\lambda$. Their product is
(GC.81). The multiplier here is the one conjugate to $|u|$, rather
than to an unscaled physical strength. $\square$

Theorem 17.1 is an implication from genuine nine-low necessity.
An arbitrary table having the ranks (GC.78), or a linear synthetic
payoff on such a table, does not prove an optimum or necessity for
the actual isolated-source function $g_t$. No such necessity example
is furnished by the rank argument itself.

## 18. Ten total labels require an ordinary open affine rectangle

**Theorem 18.1 (actual-surface rectangle necessity).** Under
Assumption 1.2, the whole-domain value continuity of Theorem 7.3,
the original fractional-count closure of Theorem 8.1, and the
minimum-count identity (GC.10), if $M_{\max}=10$, then there are
nonempty ordinary open intervals $I_s,I_t$ whose rectangle is
contained in the strict weak domain and continuous real functions
$a,b$ on $I_t$ such that
$$
\mathcal T(s,t)=a(t)-b(t)s\quad(s\in I_s,\ t\in I_t),
\qquad b(t)>0.
\tag{GC.82}
$$
Here $s,t$ are the actual physical request and finite budget coordinate,
not coordinates in an ambient unconstrained moment space.

Proof. The weak upper count is ten. Relative closedness of $\{n\le9\}$
therefore makes $\{n=10\}$ relatively open in $\mathcal D_w$.
If the global maximum is ten, the strong bound $n\le8$ of
Theorem 9.1 and the entire weak minimum-budget boundary bound
$n\le7$ of Theorem 5.2 exclude both those parts of the domain.
A maximizing weak point has $t>t_0$ and
$s<s_0\tau_{\max}(t)$, possibly $s=0$. Its relatively open
maximal neighborhood contains a positive-$s$ point with all weak
inequalities strict. Continuity of $\tau_{\max}$ permits an
ordinary open rectangle $I_s\times I_t$ about that point,
contained in $0<s<s_0\tau_{\max}(t)$, $t>t_0$, and with
$n=10$ everywhere. Equivalently one may use Theorem 9.2;
$A=\log(1+t)$ is a homeomorphism, so the passage between $(s,A)$
and $(s,t)$ does not change ordinary openness.

Fix any $t\in I_t$. At every $s\in I_s$, identity (GC.10)
makes the minimum supported low count exactly nine. Theorem 17.1
and Corollary 17.2 make $\mathcal T(\cdot,t)$ locally affine
with strictly negative slope about every point of this connected
interval. These affine germs agree on overlaps, since two affine
functions agreeing on an open interval have identical slope and
intercept. Hence their slope and intercept are locally constant
functions of $s$ and, by connectedness, constant on all of $I_s$.
Thus (GC.82) holds for this $t$ with $b(t)>0$.

Choose fixed $s_1<s_2$ in $I_s$. The coefficients are explicitly
$$
b(t)=\frac{\mathcal T(s_1,t)-\mathcal T(s_2,t)}{s_2-s_1},\qquad
a(t)=\mathcal T(s_1,t)+b(t)s_1.
\tag{GC.83}
$$
Theorem 7.3 gives their continuity in $t$, and the strict decreasing
slice gives $b(t)>0$ at every $t$. The argument requires neither a
continuous choice of optimizers nor a joint analytic contact atlas.
It uses count closure for original fractional atoms; replacing that
premise by closure only after endpoint splitting would not suffice.
$\square$

**Corollary 18.2 (a sufficient missing relation, not a converse).**
If the actual strict weak optimal surface contains no rectangle of
the form (GC.82) with continuous $a,b$ and $b>0$, then
$M_{\max}\in\{8,9\}$ and every finite weak request has an optimum
with at most eight supported low actual labels.

Proof. Theorem 18.1 would otherwise force such a rectangle when
$M_{\max}=10$. Theorem 9.2 leaves only eight or nine total.
Identity (GC.10) then gives the eight-low bound on the weak domain,
including its floor and rising boundary. $\square$

**Open problem 18.3 (absence and the remaining support distinction).**
The rectangle-absence premise of Corollary 18.2 is unproved.
An affine rectangle by itself does not imply nine-low necessity:
its points might admit shorter optimal laws with different atom
tables. Thus no converse is asserted. Absence of that rectangle
would exclude nine-low necessity, but would not prove universal
seven-low, which is needed to force $M_{\max}=8$.
Finite grids, curvature samples, a Sard statement in a larger moment
space, and generic auxiliary-state lengths do not decide absence
on this actual two-parameter constrained surface.

A different sufficient eight-low statement would be that, on every
original multiplier-optimal face with $\lambda>0$, each achieved
contrast admits an original fractional law with at most eight low
atoms and the same true height. Theorem 16.2 supplies only the two
contrast extrema. A possible certificate of nine-low necessity
would instead need a genuine actual optimal contact set, positivity
of its nine necessary weights, augmented rank nine, and a full-circle
original dual exclusion of every alternative optimal direction,
together with the original fractional-label equality conditions.
Ranks or positive weights alone are insufficient. Neither such a
certificate nor a universal interior-face compression is supplied
by the preceding implications.

## 19. Rational reweighting and the limits of polynomial quadrature

**Proposition 19.1 (exact common reweighting and its missing functionals).**
For an endpoint law let $\mu_0,\mu_1$ be its pure and saturated
coefficient measures on the circle. Write $c_{\rm src}$ for the
source amplitude $c$ in $S$ and define the positive polynomials
$$
\begin{aligned}
D_c&=h_0^2\delta+(b^2/\alpha)u^2+(d^2/\beta)v^2>0,\\
N_c&=h_1^2h_2^2\delta+(a^2h_2^2/\alpha)u^2
                      +(c_{\rm src}^2h_1^2/\beta)v^2>0.
\end{aligned}
\tag{GC.84}
$$
Then $\mathfrak c=N_c/D_c$. Set
$d\sigma_0=d\mu_0$ and $d\sigma_1=D_c^{-1}d\mu_1$.
The same joint constraints, contrast and height become exactly
$$
\begin{gathered}
\int hh^T\,d\sigma_0+\int D_chh^T\,d\sigma_1=I_3,
\qquad t\int N_cn_hn_h^T\,d\sigma_1=M,\\
K=\int|u|\,d\sigma_0+\int D_c|u|\,d\sigma_1,\\
J_t=\int|\ell|\,d\sigma_0+
                   \int|D_c\ell+tN_cf|\,d\sigma_1.
\end{gathered}
\tag{GC.85}
$$
The polynomial moment equations alone have a three-plus-five-node
representation. That representation does not in general preserve
$K$ or $J_t$, and gives no eight-low optimal theorem.

Proof. The substitution $d\mu_1=D_c\,d\sigma_1$ cancels the
capacity denominator in each failure covariance. Since $D_c>0$,
$D_c|\ell+tN_cf/D_c|=|D_c\ell+tN_cf|$, proving the height
identity with the absolute value in the correct place. Conversely
a saturated $\sigma_1$ mass $w$ at $h$ recovers coefficient mass
$D_c(h)w$ and capacity $tN_c(h)/D_c(h)$; pure masses remain
unchanged. Positivity follows from $D_c,N_c>0$, and normalization
is the first diagonal entry of the SAME live Gram equation in
(GC.85). Thus reversal preserves one common law and its full $M$,
not independently optimized sheet marginals.

The entries of $hh^T$ are trigonometric polynomials of degree at
most two. The entries of $D_chh^T$ and $N_cn_hn_h^T$ have degree
at most four. Reuse the scalar circle moment representation theorem
of Curto–Fialkow, *Recursiveness, Positivity, and Truncated Moment
Problems*, Houston J. Math. 17 (1991), 603–635,
[Theorem 6.12, printed p.634](https://www.math.uh.edu/~hjm/v017n4/0603CURTO.pdf).
The Toeplitz matrix of moments of orders $-d,\ldots,d$ of an
existing positive circle measure is positive semidefinite and has
rank at most $d+1$. That theorem, in both its singular and full-rank
cases, supplies a representing measure with its rank many nodes.
Applying it with $d=2$ to $\sigma_0$ and $d=4$ to $\sigma_1$
preserves their full polynomial spaces with at most three and five
nodes. Zero measures need no nodes; singular moment matrices only
reduce these bounds. Recovering coefficient masses as above preserves
all joint moment equations and legal capacities.

The unpreserved tests in (GC.85) are $|u|$, $D_c|u|$ and the two
absolute-height functions. They are not among those polynomial
moment tests. Theorem 13.1 already gives original common laws with
the same blocks and same failure law but different contrasts;
Theorem 14.2 gives the further same-contrast height obstruction
under its signed/full-support assumptions. Thus preserving polynomial
moments is an insufficient justification for preserving these
operational functionals.

There is an additional exact degree-four contrast counterexample.
Let $\zeta_0$ and $\zeta_1$ be uniform probability measures at
$$
\phi_j=j\pi/4\quad\hbox{and}\quad
\widetilde\phi_j=\pi/8+j\pi/4,\qquad j=0,\ldots,7.
\tag{GC.86}
$$
For each $n=1,2,3,4$ the geometric sum
$8^{-1}\sum_{j=0}^7e^{in j\pi/4}$ vanishes. Rotation multiplies
it by $e^{in\pi/8}$, so both laws have identical real trigonometric
moments through degree four, including the common mass one.
Nevertheless
$$
\int|\cos\phi|\,d\zeta_0=\frac{1+\sqrt2}{4},\qquad
\int|\cos\phi|\,d\zeta_1=
 \frac{\sqrt{2+\sqrt2}+\sqrt{2-\sqrt2}}4.
\tag{GC.87}
$$
The numerators are positive, and the square of the second numerator
is $4+2\sqrt2$, whereas that of the first is $3+2\sqrt2$.
The second contrast is strictly larger. Equal degree-four moments
therefore do not determine contrast even without the height issue.
These two scalar laws are a moment counterexample, not a claim of
original optimality or a replacement for the full common-law
embeddings above. $\square$

**Proposition 19.2 (matrix mass rank does not count recovered labels).**
A node count, the sum of ranks of positive matrix masses, and the
number of original height-preserving fractional labels are different
quantities. Rank-one matrix quadrature by itself does not justify
identifying these three counts in (GC.85).

Proof. With diagonal matrix tests, a rank-one positive matrix
$vv^*$ may have two positive diagonal entries at the same angular
node. Discarding its off-diagonal entries leaves a positive pure
and a positive saturated endpoint mass, while preserving those
diagonal tests. After the positive $D_c$ recovery in Proposition
19.1, these are two original endpoint coefficient masses at one
$h$. They may be combined into one legal fractional label, preserving
all joint moments and contrast, but Theorem 15.1 proves that height
is preserved exactly when their signed endpoint heights have the
same weak sign, or a mass is zero. Rank one does not impose that
sign condition. Theorem 15.2 supplies a finite original common law
with strictly opposite signs and positive masses at the same node,
where the recovered fractional merge has a strict actual TV loss.
Thus matrix rank or angular-node counting alone cannot bound the
number of original labels while retaining the optimal height.
This obstruction does not prohibit keeping two legal endpoint
labels and does not prove that the exhibited law is optimal.
$\square$

**Convention 19.3 (precise matrix-quadrature reuse).** Mädler–Schmüdgen,
[arXiv:2310.00957v1, Theorem 5.1, Corollary 5.3 and Definitions 5.5–5.7](https://arxiv.org/pdf/2310.00957v1),
gives rank-one matrix-mass representation for a finite-dimensional
Hermitian matrix test space with a dimension bound. Its node count
and rank-sum definitions remain distinct; applying its general
bound to all the original tests does not supply seven or eight
original height-preserving labels. Zalar–Zobovič,
[*Matricial Gaussian quadrature rules: nonsingular case*, served arXiv:2508.21534v1, Theorem 1.1 and §2](https://arxiv.org/html/2508.21534v1),
requires a complete polynomial matrix moment functional and a positive
definite block moment matrix; its minimality concerns the sum of mass
ranks, and its prescribed-node assertion concerns that node's mass
rank. The served page has an arXiv v1 header of 29 August 2025 and
a body date of 24 August 2026; a historical version-exact identity
of that body is not an assumption here. The theorem is used only
at the stated served-text scope.

Their [*The matricial univariate rational truncated moment problem*,
arXiv:2608.28227v1, Theorem 1.1, Theorems 2.12–2.13 and Theorem 4.2](https://arxiv.org/html/2608.28227v1)
requires its complete rational moment data, matrix positivity,
column-space conditions, pole avoidance and simultaneous node
conditions. Its atomic multiplicities are also mass-rank sums.
Half-angle rationalization of the circle still requires valid charts,
coverage of excluded chart points and the appropriate pole/endpoint
conditions; it does not eliminate the original absolute-value sign
partitions. Completing the polynomial or rational moment sequence
adds data not determined by the original eight moments. None of
these literature conclusions provides the missing simultaneous
preservation of (GC.85)'s contrast and absolute height or the
label recovery sign condition of Proposition 19.2. They are
contextual reusable results, not new original support theorems.
No exhaustive priority or nonexistence claim is made.

**Open problem 19.4 (the required optimal quadrature transfer).** The
missing transfer is a constrained quadrature on an ACTUAL original
optimal law that simultaneously preserves
$$
\left(hh^T,\ t\mathfrak c(h)\xi n_hn_h^T,\ |u|,
                    \ |\ell(h)+t\mathfrak c(h)\xi f(h)|\right)
\tag{GC.88}
$$
and controls the number of recovered original fractional atoms.
The absolute height is evaluated after live and failure signed
mass are added inside each acquired label. Separate short
coefficient decompositions, a three-plus-five polynomial node count for
polynomial data, or a generic matrix-rank bound does not establish
this transfer. Any seven-low theorem or genuine eight-/nine-low
necessity result must still satisfy this original interface.

## 20. Simultaneous physical meaning and remaining mathematical domain

**Proposition 20.1 (common realization of the appended constructions).**
Under the source, minimax, sharp joint cost, unaveraged real-face,
full-class rigidity and capacity hypotheses of Assumption 1.2, every
finite law constructed in §§13–17 has a common original realization
with the claimed feasible or optimal height at its own request.
All original twelve-history, complete-output, chronological and
resource requirements of §2 persist.

Proof. For (GC.62)–(GC.64), the two pure residual representations
and the unchanged saturated law give exactly $I_3$ and $M$.
For (GC.65), orthogonality and finite vector representation preserve
the whole pure Gram and contrast and the identical saturated law.
For (GC.71)–(GC.73), the intensity moments give $M$ and the
positive diagonal residual gives $I_3$. For (GC.66), both Grams
and contrast are preserved by the explicit merge formulas.
For the endpoint eliminations of §16 and fixed-fraction laws of
§17, all eight common moments are fixed and the pointwise capacity
bounds hold on the unchanged original atoms; mixtures retain the
same conditions. These are exactly Proposition 12.2's equivalence
and hence Proposition 10.1's same-joint-data premises. Zero
weights are omitted before any encoder inverse. Rank two holds
on every occupied original ellipse ray, including axes. Therefore
the low acquisition effects are the actual
$K_i^\dagger K_i+p_ib_in_in_i^T$, and the sum of these effects
and the single coherent high effect is $I_5$ at the stipulated
source root. All coefficient weights sum to one without interpreting
them as acquired probabilities.

The complete live Gram cancels every cross Kraus coefficient, not
just diagonal input effects. Consequently the forgotten-label live
map is exactly (GC.53) on every complex $M_5$ input. The same
complete failure covariance gives each of the five CP Borel maps
there, separately for weights $(0,1/4,1/2,1/4,0)$, including both
zero components. Tensoring the finite live Kraus matrices with an
arbitrary passive reference and taking the failure partial trace
gives exactly (GC.54), preserving conditional reference operators
and live off-diagonal coherences. The complete stopped-cq HALF
errors (GC.55) therefore hold simultaneously for all twelve signed
histories $y=5,16,27$. The inherited minimax statement makes the
$5$ and $27$ errors $E_*$ and the $16$ error strictly smaller;
it does not make all twelve errors equal.

The sole weak high fibre has counted joint dimension five,
including its coherent complement. Its hidden terminal Kraus
indices are discarded, not readable labels. Its worst-history
probability is the inherited sharp $\mathsf C(s)$; the full cost
counts specimen, controller, memory, accessible environment and
entangled shares together. No marginal or sign average substitutes
for that sharp joint-cost premise. Low reports give
$\mathsf V=s_0K/\sqrt\alpha\ge s$; equality is used in §§16–17
only where multiplier optimality proved activity. Each law has its
own attaining instrument, fixed before the sole unknown input,
common to all histories; this is not one instrument for all requests.

Proposition 10.1 uses the same
$g(a)=2/(1+a)^2$, $G_{\rm time}(a)=2a/(1+a)$ and actual failure
operator $F_i$ to define
$$
Z_i(a)=\sqrt{I-G_{\rm time}(a)F_i},\qquad
R_i(a)=g(a)F_i[I-G_{\rm time}(a)F_i]^{-1}.
$$
Its pulled-back cumulative jump effect plus survivor effect is
$I$ at every cut. Its integrated operator norm on each ENTIRE
joint fibre is $\log(1+b_i/\mathfrak c(h_i))\le A$, and terminal
survivor effect is at least $e^{-A}I>0$. Terminal survivor processing
is TP/isometric, there is no terminal absorption, FIRST is absolute
$6+a$, and failed carriers receive no later positive-carrier action.
Neither average activity nor the integral of a maximum across labels
replaces this per-fibre bound. The witness $g$ is not the ideal
density $f_y$ and does not restrict admitted competitor time laws.

Necessity still concerns full complex CP instruments and all hidden
Kraus multiplicities with full-output TP decoders, in the finite,
convergent countable and only the stipulated measurable
finite-dimensional-fibre/Kraus/integrable-effect/live-Choi extension
of Convention 2.3. The finite convex representations introduce no
additional continuous physical implementation theorem. No helper,
copy, history oracle, reset, retry, postselection, acceptance or
survival division, quantum bypass or uncounted accessible share
has entered these constructions. Optimality is claimed only for
the globally supported multiplier laws in §§16–17; the obstruction
laws in §§13–15 are feasible examples. $\square$

**Open problem 20.2 (unchanged original finite plane and sharp count).**
The maximum minimum total alphabet remains
$M_{\max}\in\{8,9,10\}$. No actual nine-low necessity example,
universal eight-low or universal seven-low theorem follows without
the missing relations of §§18–19. Sharp strong optimal counts remain
open beyond Theorem 9.1's existence upper bound, and are different
from earlier strong feasibility counts.

The original target is still an evaluated finite-$(s,A)$ roof for
ALL budgets, every feasible requested contrast, every common oriented
failure allocation and all live-height decompositions, including
those below the maximum contrast at a fixed allocation. It needs
selected roots, weights, actual contact ranges, universal necessity
and a finite common original attainer at every point. A coefficient
state, fixed decomposition, optimal marginal, maximum-contrast facet,
implicit SDP/KKT/QE prescription or limiting support theorem does
not supply that complete roof.

The conditional connected interval at $t=1000$,
$\lambda\in[1/4,23/5]$, retains exactly its supplied source and
signed/root/whole-circle hypotheses. The connection below $1/4$
from first activation through the later pure-contact seam, the
optimizing events above $23/5$, transverse budget coverage and maximal
ranges remain open. No additional transverse strip is included.
Global ordering and connected coverage of all branches, occupied
and unused-root signs, multiplicities, collisions, zero-weight,
rank, capacity and count transitions, and all endpoint, threshold,
budget and degenerate-orientation gluing remain required.

Remaining evaluated $K(s)$ source parameters, physical orientations
and coefficient gluing, limiting root isolation, multiplicities and
sign intervals, next terms, critical five-label/static-contact
interpolation and uniform joint-limit rates remain within the
original JS/WE/TC/SC supplier boundaries of §11. Limiting
three-line structure does not force a finite-activity optimal support
restriction. None of the new joint-data obstructions, multiplier
endpoints or conditional affine implications discharges source
existence/isolation/dictionary/rank/root TP, the complete stopped-cq
minimax, sharp worst-history joint cost, the separately supplied
unaveraged real equality face, or full-class double rigidity.

**Open problem 20.3 (physical correspondence and native realization).**
The coefficient-space PPT correspondence supplies no physical
transfer from same-named PPT, MC, zero-leakage or LOSR conditions.
The needed source-preserving operations, common capacity pairing,
resource inequalities and recorded absolute height must each be
proved for the original acquisition. Native access and calibration,
coherent jointly counted storage and accessible shares, acquisition
duration, entire-fibre actuation, absolute FIRST alignment,
archive/source/epoch/controller/permissions and quantum/native-count
relations remain separate unresolved bridges. The finite CP/TP
constructors do not grant native control, calibration or clock
permission. The full original mathematical and physical target of
§11 is unchanged.

## 追加锚（本行以下为增补区）


## 21. The fixed complex-linear five-mode dictionary

**Definition 21.1 (coordinate identification and operational algebras).**
Retain the original source and all the separately scoped suppliers of
Assumption 1.2. Write Native for
[the static compatibility-fibre owner](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md),
with its ideal independently addressed menu in Assumption 55.2. Define
one COMPLEX-linear map by its ordered orthonormal bases:

$$
\begin{array}{c|ccccc}
\text{GC vector}&e_0&e_1&e_2&e_3&e_{13}\\ \hline
\mathcal V\text{ image}&|000\rangle&|100\rangle&|010\rangle&|001\rangle&|101\rangle
\end{array}
\qquad \mathcal V:\mathbb C^5\longrightarrow\mathcal K_3.
\tag{GC.89}
$$

For a finite weak law with $m$ occupied low labels, its acquisition
output is the CLASSICAL direct sum

$$
\mathcal A_{\rm acq}=\left(\bigoplus_{j=1}^m M_2(\mathbb C)\right)
                         \oplus M_5(\mathbb C).
\tag{GC.90}
$$

Each label is genuinely generated and dephased. Every conditional
decoder is TP on its entire matrix block, with a live five-mode output
and the five separately labelled Borel failure measures of §2.
Decoder Kraus indices are traced out unless the original instrument
actually records them. A coherent Hilbert sum before measurement and
this classical algebra after measurement are different interfaces.

**Theorem 21.2 (full complex and reference correspondence).** The map
$\mathcal V$ is unitary and transports the specified five-mode source,
controls, effects and full instruments without any real-input restriction.
In particular, with $E$ from (GC.1),

$$
\begin{gathered}
E_N=\mathcal VE=
 \left(\frac{|000\rangle+|101\rangle}{\sqrt2},
       \frac{|100\rangle+|001\rangle}{\sqrt2},|010\rangle\right),\\
E_N^\dagger E_N=I_3,\qquad P_N=E_NE_N^\dagger=\mathcal VP\mathcal V^\dagger,\\
n_1=\operatorname{diag}(0,1,0,0,1),\qquad
 E_N^\dagger n_1E_N=\operatorname{diag}(1/2,1/2,0),\\
S_{\star,3}=\operatorname{diag}(1,1,1,1,i).
\end{gathered}
\tag{GC.91}
$$

The three restricted native flips have, respectively, the edge lists

$$
\{000\leftrightarrow100,\ 001\leftrightarrow101\},\qquad
\{000\leftrightarrow010\},\qquad
\{000\leftrightarrow001,\ 100\leftrightarrow101\}.
\tag{GC.92}
$$

An encoder $C_j$ in (GC.44), or $C_H$ in (GC.51), becomes
$C_j\mathcal V^\dagger$ or $C_H\mathcal V^\dagger$. Every live
output matrix $A$ from a conditional fibre becomes $\mathcal VA$.
The failure output $P_f$, original labels and physical clock are kept.
These substitutions preserve every complex matrix unit and every
conditional reference operator.

Proof. A complex-linear map sending an orthonormal basis to an
orthonormal basis is unitary. Applying it to the three columns of $E$
gives (GC.91); their norms are one and their supports disjoint.
The two occupied-first-site native basis vectors are $100,101$.
Their squared overlaps with the first two columns are $1/2$, and
with the third column zero; mixed entries vanish. The flip edges are
Native Proposition 43's restricted operators, and $n_1n_3$ is the
projector onto $101$ on $\mathcal K_3$, giving the fixed phase.
Thus no passive real-frame matrix such as Native's $D_3$ is being
mistaken for an available gate or inserted into the source dictionary.

For arbitrary complex $X$, input conjugation gives
$(C_j\mathcal V^\dagger)(\mathcal VX\mathcal V^\dagger)
(C_j\mathcal V^\dagger)^\dagger=C_jXC_j^\dagger$.
Conjugating each live Kraus matrix gives the corresponding live output
identity. Effects transform by the inverse pullback. Tensor these
identities with $I_R$ for any finite passive reference $R$; partial
trace on the five-mode factor gives the failure reference operators
in (GC.54), with $EME^\dagger$ replaced in native coordinates by
$E_NME_N^\dagger$. All five weights, including the two separate zeros,
are retained. Summing the encoder effects is still $I_5$, and each
conditional decoder remains TP on its ENTIRE block. Hence the
correspondence applies to the complete instrument, not merely its
probabilities on the twelve histories. $\square$

The dictionary is a coordinate identification. It supplies no preparation,
control, acquisition or read service. A terminal PVM probability formula
alone supplies neither its Lüders post-state nor a reusable carrier.
In particular the elementary compressed effect in (GC.91) is not the
original $M$. Native Theorem 65.2 matches that supported effect after
an exact word, while leaving the full acquisition and chronological
instrument requirements distinct.

## 22. A four-axis common-law witness with five actual outputs

**Theorem 22.1 (one finite feasible law, including every signed history).**
At the source of Assumption 1.2 define

$$
\begin{aligned}
h_{z,\pm}&=(1,\pm1/\sqrt\alpha,0),&p_{z,\pm}&=\alpha/2,
 &B_z&=m_2h_1^2/b^2=V,\\
h_{w,\pm}&=(1,0,\pm1/\sqrt\beta),&p_{w,\pm}&=\beta/2,
 &B_w&=m_1h_2^2/d^2=W,\\
c_z&=\mathfrak c(h_{z,+})=\mathfrak c(h_{z,-})>0,
 &c_w&=\mathfrak c(h_{w,+})=\mathfrak c(h_{w,-})>0,\\
A_{\rm axes}&=\log\left(1+\max\{B_z/c_z,B_w/c_w\}\right)<\infty.
\end{aligned}
\tag{GC.93}
$$

Use failure capacity $b_j=B_z$ on each $z$ atom and $b_j=B_w$
on each $w$ atom. For every finite $A\ge A_{\rm axes}$ this SAME
four-atom law satisfies all the complete joint equations (GC.9) and
has achieved contrast $\sqrt\theta<s_0$. Thus for every request
$0\le s\le\sqrt\theta$ it has the §10 weak constructor with error
$E_*$, sharp joint cost $\mathsf C(s)$ and exactly five actual
acquisition labels, each with positive probability on EVERY one of
the original twelve histories. It is a feasible witness, not a
height optimizer or a minimum-alphabet theorem.

Proof. Each point lies on the original ellipse. The opposite signs
cancel both first moments; $zw=0$ pointwise. The three diagonal
entries of $\sum phh^T$ are $\alpha+\beta,1,1$, so this is exactly
$I_3$, including all off-diagonals. On the $z$ pair
$n_h=(0,0,-bz/h_1)^T$, giving

$$
\sum_{z\text{ pair}}p_jb_jn_{h_j}n_{h_j}^T
 =\operatorname{diag}(0,0,B_zb^2/h_1^2)
 =\operatorname{diag}(0,0,m_2).
\tag{GC.94}
$$

On the $w$ pair the result is $\operatorname{diag}(0,m_1,0)$.
Consequently the complete covariance is $M$ for the very law that
has the complete live Gram $I_3$. These are not independently
chosen marginal decompositions. Positivity of the capacity follows
from (GC.8), and it depends only on squared coordinates. The stated
$A$ makes every $b_j\le(e^A-1)\mathfrak c(h_j)$. Finally
$s_0\sum p_j|z_j|=s_0\sqrt\alpha=\sqrt\theta$; since
$\omega>0$, this is strictly below $s_0$.

Each live $K_h$ has rank two by §10. Its kernel is spanned by
$(s_0,-bz/h_1,-dw/h_2)^T$. On a $z$ axis the third coordinate
of this vector is zero, and on a $w$ axis the second is zero.
Every signed $U_{\epsilon,\chi}a_y$ has all three coordinates
nonzero. It therefore lies in none of these four kernels. Each
low acquisition mass
$p_j\langle U_{\epsilon,\chi}a_y,
(K_h^\dagger K_h+b_jn_hn_h^T)U_{\epsilon,\chi}a_y\rangle$
is strictly positive. The single high mass is
$(1-\delta)\sum_i h_i^2p_{yi}>0$. These exhaust the five
acquisition outputs and sum to one by root TP and (GC.52).

Proposition 10.1 now applies to this common law on the entire complex
$M_5$ input and all passive references. Its four qubit fibres have
positive terminal survivor effects and activity at most $A$; its
high fibre has dimension five, zero rate and the coherent complement.
The sharp-cost and $E_*$ identifications use their separate inherited
suppliers, including the unaveraged JR face. The witness does not
reverify those suppliers or choose an optimal height. $\square$

## 23. The literal pre-read menu does not acquire a low quantum fibre

**Theorem 23.1 (supported unitary-cut obstruction).** Fix any one
$y\in\{5,16,27\}$. At a cut reached using only native unitary
words before the permitted terminal read, the joint accessible quantum
image of the four signed original inputs has dimension at least three.
This remains true with an independently initialized accessible ancilla
and with input-independent classical randomization. Thus the literal
unitary-only acquisition cut has $\mathsf W=1$. It cannot implement
the low/high acquisition of Theorem 22.1, whose worst-history high
probability is strictly below one. The comparison with the original
sharp $\mathsf C(s)$ is at its inherited weak scope.

Proof. Put $v_{\epsilon,\chi}=(\epsilon a_{y0},\chi a_{y1},a_{y2})^T$.
Then

$$
\sum_{\epsilon,\chi}\epsilon v_{\epsilon,\chi}=4a_{y0}e_0,
\quad
\sum_{\epsilon,\chi}\chi v_{\epsilon,\chi}=4a_{y1}e_1,
\quad
\sum_{\epsilon,\chi}v_{\epsilon,\chi}=4a_{y2}e_2.
\tag{GC.95}
$$

All coefficients on the right are nonzero, so the COMPLEX span is
three-dimensional. The isometry $E_N$ and every native word preserve
that dimension. Appending an independent pure ancilla and applying a
joint unitary is also an isometry on this span. An independent mixed
ancilla has support of rank at least one; the joint support initially
has dimension three times that rank, and a unitary preserves it.
Every future-accessible input-bearing share is included here; removing
one by an irreversible channel would leave the stipulated unitary-only
menu.

If the seed is recorded, each seed label has input effect $p_jI$;
conditional on any positive-weight seed the joint span is still at
least three. If the seed is forgotten, the support of a positive
mixture contains the support of every positive-weight term, so mixing
cannot turn this into a two-dimensional acquisition fibre. This also
covers a continuous seed: positivity of the mixture excludes a smaller
support unless the almost-everywhere images already lie in it. Thus
no actually generated label at this cut has joint fibre dimension below
three, and the total high probability is one.

For the §10 weak acquisition only $H$ is high. Its probability is
$(1-\delta)\sum_i h_i^2p_{yi}$, independent of signs. Root TP gives
$h_i^2\le1$, and $0<\delta<1$, hence

$$
\mathsf W_{\rm GC}=(1-\delta)\max_y\sum_i h_i^2p_{yi}<1.
\tag{GC.96}
$$

Under the original weak sharp-cost supplier this equals
$\mathsf C(s)$ for the stated witness requests. $\square$

A terminal bit cannot retroactively create an earlier acquisition cut
or authorize a later quantum output. This theorem concerns the literal
menu before that read; it is not a no-go for every conceivable optimizer,
every stronger measurement interface or the strong boundary. Its joint
span is essential: the two-dimensional marginal of a larger accessible
joint carrier does not qualify as a low fibre.

## 24. The specified full high completion has a separate Choi obstruction

**Theorem 24.1 (full-$M_5$ obstruction for GC.51).** Consider an upgrade
of the native $\mathcal K_3$ menu allowing any finite adaptive sequence
of the same two-outcome read with effects $\{n_1,I-n_1\}$, intervening
native unitaries and input-independent randomization, but no additional
quantum carrier or other nonunitary primitive. Allow arbitrary hidden
Kraus multiplicities for that read and classical merging of complete
records. No actual branch of such an instrument can equal
$X\mapsto C_HXC_H^\dagger$ from (GC.51) on the full complex
$M_5$. Identify its five-dimensional output with $\mathcal K_3$ by
any fixed unitary if needed.

Proof. If a read outcome $b$ has effect $P_b$, its Kraus operators
$L_{b\mu}$ obey $\sum_\mu L_{b\mu}^\dagger L_{b\mu}=P_b$.
For $v\in\ker P_b$, the sum $\sum_\mu\|L_{b\mu}v\|^2$
is zero, so every $L_{b\mu}=L_{b\mu}P_b$. Each Kraus matrix
therefore has rank at most $\operatorname{rank}P_b\le3$.
Every trajectory containing a read has Kraus rank at most three,
even after pre/post unitaries and further reads. A trajectory with
no read is a scalar-weighted unitary and has scalar input effect.

In contrast the particular coherent high encoder has effect

$$
C_H^\dagger C_H=(1-\delta)ED^\dagger DE^\dagger+P^\perp.
\tag{GC.97}
$$

Its eigenvalues are $(1-\delta)h_0^2,(1-\delta)h_1^2,
(1-\delta)h_2^2,1,1$. The first three are strictly between zero
and one. Thus $C_H$ has rank five and nonscalar effect.
Its Choi matrix is the single positive ray
$|C_H\rangle\!\rangle\langle\!\langle C_H|$. If positive Kraus
terms sum to this ray, expectation on any vector orthogonal to
$|C_H\rangle\!\rangle$ is a sum of nonnegative squares equal
to zero. Every nonzero Kraus vector must be collinear with
$|C_H\rangle\!\rangle$. A measured trajectory violates its
rank five, while an unmeasured trajectory violates its nonscalar
effect. Classical merging and hiding Kraus indices are positive sums,
so neither helps. For a convergent countable sum the same squares
vanish termwise. For an integrable random seed they vanish almost
everywhere; a finite basis of the orthogonal complement suffices.
The argument is the Choi-ray mechanism already used in Native
Proposition 44, now applied to this specified nonunitary encoder.
A normalized maximally entangled five-dimensional input and passive
reference distinguishes any unequal CP maps. $\square$

This is specifically the full completion (GC.51). Its supported
restriction $C_HE$ has rank THREE, so the preceding rank-five
argument does not follow after replacing the full $M_5$ problem by
that restriction. Theorem 23.1 supplies the separate supported-cut
cost obstruction. Neither theorem excludes all lawful full completions
or all optimizers of the original problem. Matching the supported
effect in Native Theorem 65.2 is compatible with both obstructions:
an effect and a complete conditional quantum map are different data.

## 25. A conditional orthogonal layout and rank-five legal-chain tree

**Assumption 25.1 (counterfactual apparatus interfaces).** Fix one finite
weak common law from (GC.9) with $m\ge1$ occupied low labels and its
actual encoders (GC.44), (GC.51). In addition to Native Assumption
55.2, suppose the following operations are supplied independently:
an initialization embedding of the sole five-mode specimen in the
chosen legal chain with added positions in their specified zero state;
a nondestructive, reusable, exact Lüders read of the first-position
PVM; classical feedback retaining the complete read record; and
branch-dependent routing/isolation to the stipulated output carriers.
Every other input-bearing quantum share must become permanently
inaccessible before the acquisition cut. Routing, removal and terminal
environment disposal are actual supplied operations, not an inference
from a dimension count. Controls, initialization, reads and routing
must finish by their required cut on a supplied aligned clock. These
are counterfactual added permissions, not services authorized by the
original theory or by unitary controllability.

For a general layout, also suppose an exact complete read of its
orthogonal sectors is supplied. The special $m=4$ case below derives
that sector read from the reusable rank-five detector instead. If a
chronological decoder is wanted, independently supply the causal
reservoir, calibrated coupling, survivor output and real clock required
by JRH §66; finite acquisition dimension does not supply them.

**Theorem 25.2 (exact columns and complete acquisition).** Under these
assumptions, an orthogonal-layout acquisition has Hilbert output space
and dephased output algebra

$$
\begin{gathered}
\mathcal H_\oplus=\left(\bigoplus_{j=1}^m\mathbb C^2\right)
                          \oplus\mathbb C^5,
\qquad \dim\mathcal H_\oplus=2m+5,\\
\mathcal A_{\rm acq}=\left(\bigoplus_{j=1}^mM_2\right)\oplus M_5,
\qquad \dim_{\mathbb C}\mathcal A_{\rm acq}=4m+25.
\end{gathered}
\tag{GC.98}
$$

For $d_n\ge2m+5$, its column isometry can be obtained by an exact
finite native word on $\mathcal K_n$. With the sector read and the
specified routing, the resulting acquisition branches are exactly
$\operatorname{Ad}_{C_j}$ and $\operatorname{Ad}_{C_H}$ on ALL
complex input matrices, including their passive-reference extensions.
For the four-axis law, $m=4$, the orthogonal Hilbert layout has dimension
$13=d_5$, whereas its cq algebra has complex vector dimension $41$.
Within this layout $n=5$ is the smallest chain length, since $d_4=8$.
This is not a universal ancilla or instrument-dimension minimum.

Proof. Stack the actual columns, without replacing coefficient weights
by acquisition probabilities:

$$
\mathcal A\psi=C_1\psi\oplus\cdots\oplus C_m\psi\oplus C_H\psi.
\tag{GC.99}
$$

Equation (GC.52) gives $\mathcal A^\dagger\mathcal A=I_5$ on
the full complex input, including its complementary two dimensions.
Choose a sector embedding $J_\oplus:\mathcal H_\oplus\to\mathcal K_n$
and the supplied input embedding $I_{\rm init}:\mathbb C^5\to\mathcal K_n$.
Complete the five columns of $I_{\rm init}$ and $J_\oplus\mathcal A$
to orthonormal bases. Their basis correspondence is a unitary $U_0$
with $U_0I_{\rm init}=J_\oplus\mathcal A$. Since $2m+5>5$,
there is an unused input column; multiplying its output column by
$(\det U_0)^{-1}$ gives $U\in SU(d_n)$ with the same prescribed
five columns. Native Theorem 64.1 supplies this $U$ as an ACTUAL
finite word, without invoking an approximate matrix completion.

Let $Q_j$ be the output sector projections. Then
$Q_jUI_{\rm init}=J_jC_j$, also for $H$. The supplied sector
Lüders read, followed by the inverse sector identification, gives the
claimed CP map in each branch. Tensoring these exact matrix identities
with $I_R$ proves the complete reference statement. When $d_n>2m+5$,
complete the sector read with the orthogonal remainder. Its Kraus map
on every initialized $M_5$ input is zero, so it generates no additional
actual label there; it is still included in the full apparatus read.
All occupied conditional output carriers and their full-domain TP
decoders are the specified ones after routing, not enlarged padding
blocks. Summing their effects gives $I_5$ exactly.

For $m=4$, identify the original native specimen with $\mathcal K_3$
by §21 and explicitly supply

$$
I_{\rm init}|x\rangle=|x00\rangle\in\mathcal K_5
\qquad(x\in\Sigma_3).
\tag{GC.100}
$$

All five images are legal and orthonormal. This is an initialized
mapping, not a free operation on an unknown source. The five output
sectors have dimensions $5,2,2,2,2$ and exhaust $\mathcal K_5$.
The dimension statements in (GC.98) follow by adding Hilbert dimensions
or, respectively, matrix-block dimensions. Since $d_n$ increases and
$d_4<13=d_5$, the layout-specific minimum follows. $\square$

**Theorem 25.3 (the rank-five detector reads exactly five leaves).**
For $m=4$, Assumption 25.1's reusable first-position Lüders detector
on $\mathcal K_5$ suffices for the entire sector read, using the
conditional splits

$$
13\longrightarrow5\mid8,\qquad
8\longrightarrow4\mid4,\qquad
4\longrightarrow2\mid2.
\tag{GC.101}
$$

The complete path record has exactly five possible leaves: the single
high prefix and the four low three-bit prefixes. No random seed or
readable hidden Kraus label is added.

Proof. On $\mathcal K_5$, $n_1$ has rank $F_5=5$ and complement
rank eight. On a known $r$-dimensional sector $S$, suppose a prescribed
split has dimensions $a,r-a$. A rank-five projector whose restriction
to $S$ is the first split projector and which commutes with $P_S$
exists exactly when

$$
a\le5,\qquad r-a\le8.
\tag{GC.102}
$$

Necessity is the rank bound for the projector and its complement.
For sufficiency, add $5-a$ orthogonal padding directions in $S^\perp$;
this is possible iff $5-a\le13-r$, the second inequality. Any two
rank-five projectors on $\mathcal K_5$ are unitarily conjugate.
Multiply a conjugating unitary by a scalar to make its determinant one,
without changing its projector conjugation. Native Theorem 64.1 gives
it and its inverse exactly. Conjugating the detector before the read
and undoing that conjugation afterward therefore realizes the padded
Lüders projector. The post-state assertion uses the stipulated Lüders
instrument; equality of effects alone would not suffice.

Apply this with $(r,a)=(13,5),(8,4),(4,2)$, using the last split
in each four-sector. All inequalities hold. The initial read isolates
$H$ from the sum of the four low sectors. Its low result splits that
sum into two pairs, and the final conditional read separates each pair.
At a child node the padded projection commutes with its known parent
sector and restricts to the prescribed child. Thus the product of path
Kraus projectors is exactly the final sector projector, not a finer
measurement within it. The two outcomes at every node sum to identity
on its parent; all trajectories are retained and no acceptance division
occurs. With outcome one selecting the root high sector, the complete
codes can be chosen as $1,000,001,010,011$. They are in bijection
with $H,L_1,L_2,L_3,L_4$. The high path has one read and a low path
three; no reset is used, and each is a complete branch.

Every conjugating word and detector projection remains within the legal
chain. For Theorem 22.1 each leaf has strictly positive probability on
each original history, so these are five actual outputs, not five
formal possible labels padded by zeros. $\square$

**Proposition 25.4 (whole-fibre and decoder completion conditions).**
The preceding construction realizes the original acquisition resource
only if the ENTIRE future-accessible quantum fibre, after recording a
leaf and routing, is the stated $\mathbb C^2$ or $\mathbb C^5$.
A retained input-bearing chain, controller, detector environment or
correlated share must be counted jointly. A same-effect
measure-and-prepare detector need not implement this acquisition.

Proof. The branch column identity requires the coherent map $C_j$,
not only the effect $C_j^\dagger C_j$. Measuring a basis within a
sector and preparing a fixed state can have that same sector effect
while deleting its off-diagonal matrix units, so it fails (GC.99).
The Lüders tree preserves them. The supplied routing must identify each
sector with the declared output carrier and make every other quantum
output either independent conditional on the record or permanently
inaccessible before the cut. If another input-bearing share remains
accessible, its joint algebra is larger than (GC.90), violating the
claimed cost interface even if the displayed carrier marginal has rank
two. No rank-of-populated-history argument exempts it.

For the high decoder the two prescribed matrices in native coordinates
are explicitly

$$
A_0=\mathcal VE[I_3\ 0],\qquad
A_1=\mathcal VEJ_0[0\ I_2],\qquad
A_0^\dagger A_0+A_1^\dagger A_1=I_5.
\tag{GC.103}
$$

Consequently $x\mapsto A_0x\otimes|0\rangle+A_1x\otimes|1\rangle$
is an isometry. Discarding its two-component environment yields the
specified high TP decoder; its index is not another acquisition label.
Retaining an accessible returning environment changes that interface.
The low full-domain TP decoders, all reference/Borel identities and
whole-fibre activity bounds are exactly those of Proposition 10.1.
Their causal monitor is direct reuse of JRH Theorem 66.1 and
(JRH.54)–(JRH.56); no additional monitor construction is needed here.
Scheduling and causal coupling are precisely the extra assumptions,
not consequences of the column completion. $\square$

Finite column dilations and measurement trees are established methods.
Andersson–Oi, [*Binary search trees for generalized measurement*,
§§II–IV](https://arxiv.org/html/0712.2665v1), explicitly supplies an
initialized probe, joint unitary, nondestructive output and adaptive
probe read/reset. The present application proves its own no-reset,
fixed-rank legal-chain tree (GC.101) for the GC columns. Lloyd–Viola,
[*Control of open quantum system dynamics*, Eqs. 3–7](https://arxiv.org/html/quant-ph/0008101v1),
also requires an independent initialized apparatus, controlled coupling,
read and feedback; its continuous-time enactment is a scaled approximate
construction. Oreshkov–Brun,
[*Weak measurements are universal*](https://arxiv.org/html/quant-ph/0503017v4),
uses an adjustable two-outcome family depending on the current walk
coordinate. None of these interfaces is supplied by a literal terminal
bit, nor do they certify the prescribed FIRST clock or activity.
These methods are credited applications, without a literature-priority
claim for their general principles.

Theorems 25.2–25.3 concern the weak high completion of dimension five.
The original
root existence/isolation, ranks and root TP, complete minimax, separate
unaveraged face, sharp JOINT cost and full-class rigidity/capacity remain
Assumption 1.2's conditional supplies. Extra apparatus permissions are
not authorized by this application. The all-budget/all-contrast roof,
sharp optimal actual counts, coefficients and orientations, global
ordering, connected coverage, all gluing and joint limits in §§11,20
remain unchanged; the finite witness and conditional apparatus do not
complete that original mathematical or native programme.

## 追加锚（本行以下为增补区）
