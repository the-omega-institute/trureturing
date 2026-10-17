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
