# Residual height records: global quadratic certificates and actual acquisition-label rigidity

## 1. The original experiment and the conditional statement

This companion to [JR, §§41–57][JR] and [RC, §§58–66][RC] proves a
global all-four-full-PSD quadratic upper certificate and the sharp minimum
of actual low live-bearing acquisition labels among height-optimal
instruments throughout the original weak interval. That minimum is three
through the contact $s_\dagger=s_0\tau_\dagger$, including the contact,
and four for $s_\dagger<s\leq s_0$. The separately proved
inequality-feasibility threshold is the strictly later $s_0\tau_3$.

RC supplies the complete conditional residual value, the selected
post-contact algebraic curve, the simple first $d_+$ zero, quantitative
$C^1$ gluing, the three-to-four positive-real-atom onset, and the absence
of later interior contact or aggregate-rank transitions. Those results
are credited and are not left open or claimed anew. The additional
actual-label theorem requires a common-decoder rigidity argument:
real-atom counts alone do not count actual acquisition labels. All
statements are ordinary symbolic mathematics conditional on the specified
CG, JR and RC premises, including RC's interval/Bernstein comparisons.

**Definition 1.1 (unchanged specimen, targets and error).** Let
$E:\mathbb C^3\to\mathbb C^5$ be the original calibrated isometry and
$P_V=EE^\dagger$. The sole unknown reached-cut specimen is
$E\rho_{y,e,n}E^\dagger$, where

$$
\begin{aligned}
p_y&=(y/128,(64-y)/128,1/2),&
a_y&=(\sqrt{p_{y0}},\sqrt{p_{y1}},\sqrt{p_{y2}})^T,\\
\rho_{y,e,n}&=U_{e,n}a_ya_y^TU_{e,n}^\dagger,&
U_{e,n}&=\operatorname{diag}(e,n,1),\\
y&\in\{5,16,27\},& e,n&\in\{+1,-1\}.
\end{aligned}
\tag{RH.1}
$$

The original height is $x=y/256$, and $en=(-1)^m$ is the original
winding parity. The ideal live matrices $B_y^{\rm id}$ are the fixed
coherent matrices designated by CG.111 in JR.1. They are conditional
input data here; none of their coherent entries is replaced by a
population or a sign average. The ideal output $\Omega_{y,e,n}$ consists
of $EU_{e,n}B_y^{\rm id}U_{e,n}^\dagger E^\dagger$ in live and the
five separately labelled measures, in original label order
$(0,1,2,3,13)$,

$$
w_\ell f_y(t)dt\,P_f,\qquad
w=(0,1/4,1/2,1/4,0),\qquad
f_y(t)=\frac{6y}{(y+6t)^2},\quad 0\leq t\leq1.
\tag{RH.2}
$$

The error of a common full-output processor is

$$
E(\Phi)=\max_{y,e,n}\frac12
 \|\Phi(E\rho_{y,e,n}E^\dagger)-\Omega_{y,e,n}\|_{1,\rm cq}.
\tag{RH.3}
$$

The norm includes the full coherent live block, each labelled failure
measure, singular-time components, abort, wrong-support, zero-ideal and
extra sectors. The actual simulator density is $g_{\rm time}(t)=2/(1+t)^2$; it is
distinct from the ideal $f_y$ above. The isolated CG root, coefficient relations, ranks,
normalization, strict enclosures, endpoint witnesses, support and
endpoint-saturation consequences, and the complete-output minimax value
$E_*$ are named conditional antecedents. Their root, Jacobian and minimax
certification are not reauthenticated here.

**Definition 1.2 (actual acquisition and original objective).** Competitors
are every original complex, coherent, potentially noncovariant optimal
common processor, with actual CP acquisition maps $\mathcal E_\alpha$
and full-output TP decoders $\mathcal R_\alpha$ on their entire declared
fibres:

$$
\Phi=\sum_\alpha\mathcal R_\alpha\mathcal E_\alpha,
\qquad \sum_\alpha\mathcal E_\alpha^\dagger(I)=I_5,
\qquad E(\Phi)=E_*.
\tag{RH.4}
$$

The sum also denotes the countable convergent instruments and precisely
the stipulated integrals of CG Convention 21.3 as specified in JR
Definition 41.1: measurable finite fibre dimensions, measurable encoder
and live-decoder Kraus fields, integrable effects and live Choi matrices,
and full-output TP decoders almost everywhere. Integral encoder densities
are CP and need not be individually TNI relative to the reference measure.
Only the restriction of a decoder to supported live output is TNI.

The dimension $d_\alpha$ counts jointly every future-accessible
input-dependent quantum share at this acquisition cut: retained specimen,
memory, controller, accessible environment and entanglement shares.
All other dilation systems are permanently inaccessible before the cut.
Let $Q_H$ be the total acquired effect of $d_\alpha\geq3$ and
$\mathsf W=\max_{y,e,n}\operatorname{tr}(Q_HE\rho_{y,e,n}E^\dagger)$.
High acquisition is charged even if execution later fails. A binary
report is a common classical processing of the actual acquired label;
its supported plus effect is $F$. The original winding contrast is

$$
\Gamma_y(F)=\frac14\sum_{e,n}en\operatorname{tr}(F\rho_{y,e,n}),
\qquad \mathsf V(F)=\frac{|\Gamma_y(F)|}{\kappa q_y}
                  =\frac{2|\operatorname{Re}F_{01}|}{\kappa},
\qquad q_y=\frac{\sqrt{y(64-y)}}{128}.
\tag{RH.5}
$$

The Fourier sum is a deterministic comparison of four conditional laws,
not a source prior. For the sharp original cost $\mathsf C(s)$, the
height objective is

$$
\mathcal T(s)=\sup\left\{
 \operatorname{TV}(P^R_{5,+,+},P^R_{27,+,+}):
 E(\Phi)=E_*,\ \mathsf W=\mathsf C(s),\ \mathsf V(F)\geq s\right\},
\quad \operatorname{TV}(P,Q)=\frac12\int|dP-dQ|.
\tag{RH.6}
$$

Here $R$ is the entire actually generated record. An inaccessible Kraus
index is not part of $R$. No other entry of $F$ is prescribed, and no
particular forgotten complete channel is imposed on competitors.
There is no prior, helper, copy, readable old history, callback, reset,
retry, bypass, postselection, survival division or extra execution time.
Every matrix, choice probability and decoder is fixed before the specimen.

## 2. Dictionary and the full-class normalized reduction

**Definition 2.1 (original and normalized coordinates).** Write the
original Kraus amplitudes with subscripts to distinguish them from
normalized parameters:

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=a_K|0\rangle\langle1|+b_K|1\rangle\langle0|,\quad
S=c_K|0\rangle\langle2|+d_K|2\rangle\langle0|,\\
M=\operatorname{diag}(0,m_1,m_2),\quad
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\\
\kappa=h_0a_K+h_1b_K>0,\qquad
\kappa_{02}=h_0c_K+h_2d_K>0,\\
\theta=\frac{a_Kb_K}{h_0h_1},\quad
\omega=\frac{c_Kd_K}{h_0h_2},\quad
\delta=\theta+\omega<1,\quad s_0=\sqrt\delta,\\
A_y=\sum_i h_i^2p_{yi},\quad
B_y=b_K^2p_{y0}+a_K^2p_{y1},\quad
C_y=d_K^2p_{y0}+c_K^2p_{y2}.
\end{gathered}
\tag{RH.7}
$$

All $h_i,a_K,b_K,c_K,d_K,m_1,m_2$ are positive under the JR premises;
$A_y,B_y,C_y$ strictly increase through the three heights. The scalar
$B_y$ in RH.7 is distinct from the ideal matrix $B_y^{\rm id}$.
Throughout $0\leq s\leq s_0$, the credited sharp cost is
$\mathsf C(s)=(1-\delta)A_{27}$.

Set $\Delta=\rho_{27,+,+}-\rho_{5,+,+}$ and

$$
\begin{gathered}
\Delta A=A_{27}-A_5,\quad\Delta B=B_{27}-B_5,\quad
\Delta C=C_{27}-C_5,\\
\xi=\kappa(q_{27}-q_5)>0,\quad
\eta=\kappa_{02}(\sqrt{27}-\sqrt5)/16>0,\quad
\zeta=a_Kc_K(\sqrt{37}-\sqrt{59})/16<0,\\
N=\begin{pmatrix}\Delta A&\xi&\eta\\\xi&\Delta B&\zeta\\
\eta&\zeta&\Delta C\end{pmatrix},\quad
L_0=\operatorname{diag}(\delta,1,1),\quad
L=\operatorname{diag}(s_0,1,1),\\
Q_0=\operatorname{diag}(1,-\theta,-\omega),\quad
\beta=\chi=\omega/\delta,\quad\alpha=1-\beta,\quad
Q=\operatorname{diag}(1,-\alpha,-\beta),\\
LQ_0L=\delta Q,\quad
G=LNL=\begin{pmatrix}g_0&x&y\\x&g_1&z\\y&z&g_2\end{pmatrix},\quad
(g_0,g_1,g_2,x,y,z)=(\delta\Delta A,\Delta B,\Delta C,s_0\xi,s_0\eta,\zeta),\\
C=\frac{|0\rangle\langle1|+|1\rangle\langle0|}{2},\qquad
\tau=s/s_0.
\end{gathered}
\tag{RH.8}
$$

The entries $x,y,z$ of $G$ are not the original height, the original
height index or a CG root coordinate. For a real vector $f$ in normalized coefficient coordinates,
its original coefficient vector is $c=Lf$ and its live matrix is
$K(c)=c_0D+c_1T+c_2S$. Original and normalized moment slots correspond
by $Z_{r,\epsilon}=LX_{r,\epsilon}L$.

Define the unnormalized failure difference on coordinates $1,2$:

$$
\begin{gathered}
\Xi=M^{1/2}\Delta M^{1/2}\big|_{\{1,2\}}
 =\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},\quad
 d_f=11m_1/64>0,\quad
 z_f=\sqrt{m_1m_2}(\sqrt{37}-\sqrt{59})/16\ne0,\\
 L_f=\|\Xi\|_1=\sqrt{d_f^2+4z_f^2}>d_f,\qquad
 T_{\rm flat}=(d_f+L_f)/2.
\end{gathered}
\tag{RH.9}
$$

The trace identity in RH.7 and $\operatorname{tr}\Delta=0$ give

$$
\Delta A+\Delta B+\Delta C=d_f,
\qquad (1-\delta)\Delta A+\operatorname{tr}G=d_f.
\tag{RH.10}
$$

**Theorem 2.2 (credited reduction with its equality mechanism).** Define

$$
\begin{aligned}
J(\tau)=\max\quad&\sum_{r,\epsilon=\pm1}
                    \epsilon\operatorname{tr}(GX_{r,\epsilon})\\
\text{subject to}\quad&X_{r,\epsilon}\in\operatorname{Sym}_3(\mathbb R),
\quad X_{r,\epsilon}\succeq0,\quad
\operatorname{tr}(QX_{r,\epsilon})=0,\\
&\sum_{r,\epsilon}X_{r,\epsilon}=I_3,\qquad
 t(X):=\sum_{r,\epsilon}r\operatorname{tr}(CX_{r,\epsilon})\geq\tau.
\end{aligned}
\tag{RH.11}
$$

Then, in the entire original comparison class of Definition 1.2,

$$
\mathcal T(s_0\tau)=
 \frac{(1-\delta)\Delta A+L_f+J(\tau)}2,
\qquad 0\leq\tau\leq1.
\tag{RH.12}
$$

Every sharp-cost optimizer has supported live map
$\Lambda_*=D(\cdot)D^\dagger+T(\cdot)T^\dagger+S(\cdot)S^\dagger$,
total supported failure effect $M$, no other supported output mass, and
high acquired effect $(1-\delta)D^\dagger D$. Every nonzero low
encoder/live-decoder Kraus product is a common phase times a real
$K(c)$ with $c^TQ_0c=0$ and $c_0\ne0$. These are supported equalities,
not uniqueness of the complete channel or individual failure measures.

Proof. The CG support and endpoint-saturation premises used in JR42
place every product in the span of $D,T,S$ and fix its total diagonal
coefficient masses to $(1,1,1)$. Positivity gives this support for each
summand, or almost every integrand: a positive total matrix killing a
vector has every positive summand killing that vector. The three Kraus
vectors have disjoint supports and are linearly independent; applying
their Gram left inverse transfers Choi equalities to coefficient Grams.
The same CG premises give no other supported output and a total failure
effect killing coordinate $0$ before averaging.

For complex coefficients direct determinant expansion gives

$$
\det K(c)=h_0h_1h_2c_0
 (c_0^2-\theta c_1^2-\omega c_2^2).
\tag{RH.13}
$$

For a low product, rank at most two therefore implies
$|c_0|^2\leq\theta|c_1|^2+\omega|c_2|^2$, including the singular
plane $c_0=0$. Let $(u_L,v_L,w_L)$ be its aggregate low squared
coefficient masses. Four-sign averaging of acquisition probabilities,
solely as a necessary cost test, yields

$$
\begin{aligned}
u_L&\leq\theta v_L+\omega w_L\leq\delta,\qquad
v_L,w_L\leq1,\\
\mathsf W&\geq\overline p_{H,27}\geq
 A_{27}(1-u_L)+B_{27}(1-v_L)+C_{27}(1-w_L).
\end{aligned}
\tag{RH.14}
$$

The second inequality uses the TNI live restriction of a whole TP
decoder. Its acquired effect minus supported live effect is PSD, so
it also counts high branches later failing. At sharp cost, positivity
of all three weights forces $(u_L,v_L,w_L)=(\delta,1,1)$. The aggregate
high acquired-minus-live effect has zero trace against
$\operatorname{diag}(p_{27})\succ0$ and thus is zero. Every branch
slack is nonnegative, so it vanishes separately, or almost everywhere.
High products are multiples of $D$ and have no supported later failure.

The low triangle slacks also sum to zero. Each nonzero low product
therefore satisfies both
$c_0^2=\theta c_1^2+\omega c_2^2$ and
$|c_0|^2=\theta|c_1|^2+\omega|c_2|^2$, and cannot have $c_0=0$.
Divide by $c_0^2$. Equality in the complex triangle inequality makes
the nonzero squared ratios nonnegative real, so $c_1/c_0,c_2/c_0$
are real, also when either is zero. Removing one common phase leaves
a real null vector. Complex, noncovariant acquisitions were not excluded
in advance.

The total coefficient Gram is consequently real with diagonal one.
TP and the failure effect killing coordinate $0$ force its $DT,DS$
entries to vanish, since $\kappa,\kappa_{02}>0$. A remaining real
$TS$ entry $t$ changes the height-$27$ endpoint live witness by
$n t C_{TS}$, where
$C_{TS}=2(\zeta_{27}^TTa_{27})(\zeta_{27}^TSa_{27})>0$ for the
credited positive CG endpoint witness vector $\zeta_{27}$.
Each sign separately saturates that witness, whose nonlive payoff is
zero. Both signs of $n$ force $t=0$. The supported live Gram is $I$,
the failure effect is $M$ by TP, the high Gram is
$\operatorname{diag}(1-\delta,0,0)$, and the low Gram is $L_0$.
This also proves the stated high acquired effect.

The failure plus subeffect is dominated by $M$ and hence kills
coordinate $0$. After one global binary reversal, the exact winding
coordinate is
$\mathsf V(F)=\left|\sum_j r_j(c_j)_0(c_j)_1\right|$ on the analytic low products;
the high products have no $DT$ coordinate. Stochastic reports use their
mean coefficients in $[-1,1]$, or may be included as actual generated
coins. Write $c_j=Lf_j$ and group the real projectors $f_jf_j^T$ by
the actual report $r$ and the sign $\epsilon$ of $f_j^TGf_j$.
Their total is $I$, each has zero $Q$ trace, and their signed $01$
moment is at least $\tau$. Splitting a label analytically and separating
its live and failure differences can only increase its absolute height
difference. No such refinement is made readable. The high absolute sum
is $(1-\delta)\Delta A$. For failure subeffects $B_\alpha\succeq0$
summing to $M$, write
$B_\alpha=M^{1/2}E_\alpha M^{1/2}$ on $\operatorname{ran}M$, with
$\sum E_\alpha=I$. Then

$$
\sum_\alpha|\operatorname{tr}(B_\alpha\Delta)|
 \leq\sum_\alpha\operatorname{tr}(E_\alpha|\Xi|)=L_f.
\tag{RH.15}
$$

The same inequality integrates in the stipulated integral class. This
proves the upper direction of RH.12 without sign averaging height TV.

For the reverse direction, a real PSD slot $X$ with zero $Q$ trace
has a null decomposition with at most $\operatorname{rank}X$ vectors.
Indeed $X^{1/2}QX^{1/2}$ on $\operatorname{ran}X$ is symmetric and
traceless. If nonzero it has both signs, so continuity between positive
and negative unit eigenvectors gives a unit zero-Rayleigh vector. Its
orthogonal compression remains traceless; induction supplies an
orthonormal zero-Rayleigh basis. A zero compression permits any basis.
Multiplication by $X^{1/2}$ yields
$X=\sum_jf_jf_j^T$ with $f_j^TQf_j=0$.
Section 5 gives actual range encoders for these atoms, spectral failure
rows and complementary completion, with all output identities. A
maximizing tuple is attained because RH.11 is nonempty, closed and
bounded by $0\preceq X\preceq I$. Its actual refined objective is at
least the grouped signed objective; strict excess would contradict the
upper direction just proved. Thus RH.12 is exact with finite attainment.
All sums of nonnegative slacks and all moment steps above extend under
exactly the specified measurable/integrable hypotheses. This is the
JR45/JR50 reduction, reconstructed for its use here, rather than new
mathematical credit. $\square$

## 3. Credited spectral data and the initial height plateau

**Convention 3.1 (fixed spectral frame and scalar hypotheses).** The JR50
spectral data are the fixed orthonormal real $Q$-null frame $(v,u,w)$,

$$
\begin{gathered}
q(t)=\sqrt{\alpha+\beta t^2},\quad
D_t=(1+\alpha)+(1+\beta)t^2,\quad
v=\frac{(q(t_*),-1,-t_*)^T}{\sqrt{D_{t_*}}},
\quad 17/20<t_*<9/10,\\
B_*=\alpha t_*^2+\beta,\quad
z_*=
 \frac{\alpha q(t_*)t_*-\sqrt{B_*-\alpha\beta q(t_*)^2}}{B_*},
\quad b_*=q(t_*)-t_*z_*,\\
u=\frac{(1,b_*,z_*)^T}{\sqrt{1+b_*^2+z_*^2}},\qquad w=v\times u,\\
\mu=v^TGv<0,\quad
\lambda_{\rm sp}=\mu-g_0+(x+yt_*)/q(t_*),\quad
H=G+\lambda_{\rm sp}Q,\quad Hv=\mu v,\\
P_*=vv^T,\qquad H_+=H-\mu P_*.
\end{gathered}
\tag{RH.16}
$$

The conditional stationary point $t_*$, the eigenvector identity and
positive spectrum of $H_+$ on $v^\perp$ are credited JR50 results.
Their quantitative hypotheses include

$$
\begin{gathered}
-1/10<z_*<0,\qquad49/50<b_*<27/25,\qquad
v_0v_1<0,\quad u_0u_1>0,\quad w_0w_1<0,\\
-129/10^5<\mu<-107/10^5,\qquad
-9/10000<b_{\rm end}<-8/10000,\\
b_{\rm end}=\frac{g_0+g_1+g_2-2x-2y+2z}{4},\\
12227/100000<\beta<12230/100000,\\
1269/10^6<g_0<1270/10^6,\quad
29222/10^7<g_1<29224/10^7,\quad
16771/10^7<g_2<16773/10^7,\\
2370/10^6<x<2372/10^6,\quad
2207/10^6<y<2209/10^6,\quad
-1017/10^7<z<-1016/10^7.
\end{gathered}
\tag{RH.17}
$$

All terminating scalar bounds used below are exact rationals inherited
from the specified source box, not newly executed numerical evidence.
Here $b_{\rm end}$ is JR's $\mathsf b(1)$, distinct from $b_*$,
$\beta$ and the original amplitude $b_K$. The displayed radicals are
well-defined: $q(t_*)>0$, $B_*>0$, and

$$
B_*-\alpha\beta q(t_*)^2
 =\alpha(1-\beta^2)t_*^2+\beta(1-\alpha^2)>0.
$$

All frame normalization denominators are positive. To check the fixed
frame itself, $q(t_*)^2=\alpha+\beta t_*^2$ gives $v^TQv=0$
and $\|v\|=1$. The displayed root $z_*$ solves
$B_*z_*^2-2\alpha q(t_*)t_*z_*+\alpha q(t_*)^2-1=0$;
with $b_*=q(t_*)-t_*z_*$ this gives $u^TQu=0$ and $u^Tv=0$.
The unit cross product $w$ is orthogonal to both, and
$w^TQw=\operatorname{tr}Q-v^TQv-u^TQu=0$.
The initial product signs follow as well: $v_0>0$, $v_1<0$,
$u_0,u_1>0$, and the signs of $w_0,w_1$ are those of
$t_*b_*-z_*>0$ and $-t_*-q(t_*)z_*<0$.
The latter uses $t_*>17/20$, $q(t_*)<1$ and $-z_*<1/10$.

Put

$$
\bar\tau=\bar s/s_0=2u_0u_1<1,\quad
J_{\rm bar}=\operatorname{tr}G-2\mu,\quad
T_{\rm bar}=T_{\rm flat}-\mu,\quad
T_{\rm end}=T_{\rm flat}-b_{\rm end}.
\tag{RH.18}
$$

The strict upper inequality for $\bar\tau$ follows from
$2b_*/(1+b_*^2+z_*^2)=1-((b_*-1)^2+z_*^2)/(1+b_*^2+z_*^2)$.
In particular $T_{\rm bar}>T_{\rm end}$ by RH.17.

**Proposition 3.2 (reused maximal plateau and aggregate supports).** The
credited value is $J(\tau)=J_{\rm bar}$ and
$\mathcal T(s_0\tau)=T_{\rm bar}$ for $0\leq\tau\leq\bar\tau$;
for $\bar\tau<\tau\leq1$ it is strictly smaller. Its equality
aggregate consists of $P_*$ on the negative line and $I-P_*$ on the
positive plane, whose null lines are exactly $u,w$.

Proof. For $X_-=X_{+,-}+X_{-,-}$ one has $0\preceq X_-\preceq I$ and
$\operatorname{tr}(QX_-)=0$. Therefore
$\operatorname{tr}(GX_-)=\operatorname{tr}(HX_-)\geq\mu$.
The unique negative eigenspace of $H$ is $v$ and its complementary
spectrum is strictly positive, so equality forces $X_-=P_*$.
The compression of $Q$ to $v^\perp$ is nonzero traceless: a totally
null two-plane would contain a nonzero vector with coordinate $0$
zero, where $Q$ is strictly negative. It consequently has precisely
two real null lines, $u,w$. The null decomposition in Theorem 2.2
classifies the equality atoms as $v,u,w$, with total projectors one
on each line. Their maximal signed contrast is
$|v_0v_1|+|u_0u_1|+|w_0w_1|=2u_0u_1=\bar\tau$.
Reports $(-,+,-)$ attain it. The actual instrument in Section 5 attains
that value in the original class. Compactness excludes plateau equality
above $\bar\tau$. This recalls the JR50–51 proof and counts none of
its plateau or aggregate classification as new content. $\square$

## 4. A global four-slack quadratic upper certificate

**Theorem 4.1 (finite positive quadratic certificate).** There is an
explicit finite constant $\kappa_d>0$ such that

$$
\begin{aligned}
J(\tau)&\leq J_{\rm bar}-\frac{(\tau-\bar\tau)^2}{4\kappa_d},\\
\mathcal T(s_0\tau)&\leq T_{\rm bar}
                         -\frac{(\tau-\bar\tau)^2}{8\kappa_d},
\qquad \bar\tau\leq\tau\leq1.
\end{aligned}
\tag{RH.19}
$$

These are upper bounds, including the closed endpoint, not claims that
the following dual family is optimal.

Proof. Since $v,u,w$ are orthonormal and $Q$-null, the compression of $Q$
to $\operatorname{span}(u,w)$ is
$\begin{pmatrix}0&q_{uw}\\q_{uw}&0\end{pmatrix}$ with
$q_{uw}=u^TQw\ne0$. Otherwise that plane would be totally null, contrary
to the argument in Proposition 3.2. Define

$$
\begin{gathered}
\sigma_Q=-\frac{u^TCw}{u^TQw},\qquad D_c=C+\sigma_QQ,\qquad
c_v=v^TCv,\ c_u=u^TCu,\ c_w=w^TCw,\\
A_c=|c_v|vv^T+|c_u|uu^T+|c_w|ww^T,\qquad
h=(I-P_*)D_cv,\qquad m=-\mu>0.
\end{gathered}
\tag{RH.20}
$$

Let $R_+$ be the inverse of $H_+$ on $v^\perp$, extended by zero on
$v$. It is finite and positive definite on that plane. In the fixed
frame, $D_c$ has diagonal $c_v,c_u,c_w$, zero $uw$ entry and remaining
cross term $vh^T+hv^T$. In particular
$\operatorname{tr}A_c=\bar\tau$. Put

$$
E_c=\frac{hh^T}{2m}+\frac{h^TR_+h}{2}P_*,\qquad
\kappa_d=\operatorname{tr}E_c
 =\frac12\left(\frac{\|h\|^2}{m}+h^TR_+h\right).
\tag{RH.21}
$$

For every contrast multiplier $\lambda\geq0$ supply

$$
Y_\lambda=|H|+\lambda A_c+\lambda^2E_c,\qquad
\nu_{r,\epsilon}=-\epsilon\lambda_{\rm sp}-\lambda r\sigma_Q.
\tag{RH.22}
$$

The four required original dual slacks are exactly

$$
S_{r,\epsilon}=Y_\lambda-\epsilon G-\lambda rC+\nu_{r,\epsilon}Q
 =|H|-\epsilon H+\lambda(A_c-rD_c)+\lambda^2E_c.
\tag{RH.23}
$$

Here $\lambda_{\rm sp}$ is the spectral multiplier, $\lambda$ is the
nonnegative contrast multiplier, and $\sigma_Q$ is a fixed scalar
eliminating a cross entry. They have different roles. Set
$B_r=\operatorname{diag}_{(v,u,w)}(|c_i|-rc_i)\succeq0$.
For each of the two signs $r=+1,-1$ the positive-report slack has the
explicit decomposition

$$
\begin{aligned}
S_{r,+}={}&\lambda B_r+\frac{\lambda^2h^TR_+h}{2}P_*\\
 &+\left(\sqrt{2m}\,v-\frac{\lambda r}{\sqrt{2m}}h\right)
   \left(\sqrt{2m}\,v-\frac{\lambda r}{\sqrt{2m}}h\right)^T
 \succeq0.
\end{aligned}
\tag{RH.24}
$$

For each $r=+1,-1$ the negative-report slack is

$$
\begin{aligned}
S_{r,-}={}&\lambda B_r+\frac{\lambda^2}{2m}hh^T\\
 &+\left[2H_+-\lambda r(vh^T+hv^T)
                      +\frac{\lambda^2h^TR_+h}{2}P_*\right]\succeq0.
\end{aligned}
\tag{RH.25}
$$

Indeed the bracket, in $\mathbb Rv\oplus v^\perp$, has positive
block $2H_+$ on the plane and scalar Schur complement
$\lambda^2h^TR_+h/2-\lambda^2h^T(2H_+)^{-1}h=0$.
Equivalently its quadratic form on $tv+z$, $z\perp v$, is

$$
2\left\|H_+^{1/2}z-\frac{\lambda rt}{2}R_+^{1/2}h\right\|^2.
$$

These formulas prove all four PSD inequalities, also for $\lambda=0$.
Every denominator is positive; no positivity on a null cone substitutes
for positivity of the full slack matrix.

For any feasible tuple, multiplication by its PSD slots and summation
of RH.23 give

$$
\sum_{r,\epsilon}\epsilon\operatorname{tr}(GX_{r,\epsilon})
 \leq\operatorname{tr}Y_\lambda-\lambda t(X)
 \leq\operatorname{tr}Y_\lambda-\lambda\tau.
\tag{RH.26}
$$

The last direction uses exactly $\lambda\geq0$ and the original
inequality $t(X)\geq\tau$. Every $Q$ term vanishes by its individual
null-trace constraint. Since $\operatorname{tr}Q=0$ and
$|H|=H-2\mu P_*$, the final objective is
$J_{\rm bar}-\lambda(\tau-\bar\tau)+\kappa_d\lambda^2$.

To prove $\kappa_d>0$, suppose $h=0$. Then $D_c$ is diagonal in the
frame and $A_c-rD_c\succeq0$ for both signs. Every feasible tuple would
have
$t(X)=\sum r\operatorname{tr}(D_cX_{r,\epsilon})\leq\operatorname{tr}A_c
=\bar\tau$. But the four vectors
$d_{\sigma,t}=(1,\sigma,t)^T/2$, $\sigma,t=\pm1$, have null
projectors summing to $I$, and report $r=\sigma$ gives contrast one.
This contradicts $\bar\tau<1$. Thus $h\ne0$, so RH.21 is strictly
positive and finite. Choosing
$\lambda=(\tau-\bar\tau)/(2\kappa_d)$ proves RH.19 by RH.12.
No endpoint dual attainment has been invoked. $\square$

## 5. Actual range encoders and the entire original output

**Definition 5.1 (common finite realization).** Fix before receipt of the
specimen any finite family of nonzero real $Q$-null vectors $f_j$ with
$\sum_jf_jf_j^T=I$. This includes every frame below, the four endpoint
vectors, and the null decomposition of the four slots in RH.11.
Set $c_j=Lf_j=(x_j,z_j,w_j)^T$ and $K_j=x_jD+z_jT+w_jS$.
Nullity gives $x_j^2=\theta z_j^2+\omega w_j^2$ and $x_j\ne0$.
RH.13 gives zero determinant, while the rows/columns $1,2$ minor is
$x_j^2h_1h_2>0$. Thus every $K_j$ has exactly rank two.

Here is a fixed range isometry with no singular normalization. Let
$k_{j1},k_{j2}$ be columns $1,2$ of $K_j$ and set

$$
\begin{gathered}
v_{j1}=k_{j1}/\|k_{j1}\|,\qquad
\widetilde v_{j2}=k_{j2}-v_{j1}(v_{j1}^\dagger k_{j2}),\qquad
v_{j2}=\widetilde v_{j2}/\|\widetilde v_{j2}\|,\qquad
V_j=(v_{j1},v_{j2}).
\end{gathered}
\tag{RH.27}
$$

The same nonzero minor proves column independence, so both denominators
are strictly positive, including at both closed frame endpoints.
Consequently $V_j^\dagger V_j=I_2$ and $V_jV_j^\dagger K_j=K_j$.
Supply the actual encoder and full-fibre decoder

$$
C_j=V_j^\dagger K_jE^\dagger:\mathbb C^5\to\mathbb C^2,
\qquad\mathcal R_j(Z)=EV_jZV_j^\dagger E^\dagger
\quad\text{in live}.
\tag{RH.28}
$$

Retain its generated label $j$ and chosen report $r_j$.
Add two high encoders

$$
C_{H,r}=\sqrt{(1-\delta)/2}\,DE^\dagger,\qquad r=\pm1,
\qquad\mathcal R_{H,r}(Z)=EZE^\dagger\quad\text{in live}.
\tag{RH.29}
$$

Their full fibres have dimension three. For failure, the eigenvalues of
$\Xi$ are $\lambda_\epsilon=(-d_f+\epsilon L_f)/2$, with opposite
strict signs. One explicit fixed real unit eigenvector is

$$
f_\epsilon^{\rm fail}
 =\frac{(z_f,\lambda_\epsilon+d_f)^T}
        {\sqrt{z_f^2+(\lambda_\epsilon+d_f)^2}},\qquad\epsilon=\pm1.
\tag{RH.30}
$$

Its denominator is positive because $z_f\ne0$. The projections satisfy

$$
\Pi_\epsilon=\frac12\left[I_2+
              \epsilon\frac{2\Xi+d_fI_2}{L_f}\right],\qquad
(2\Xi+d_fI_2)^2=L_f^2I_2.
\tag{RH.31}
$$

Extend the eigenvectors by zero in coordinate $0$. For each
$\epsilon,r=\pm1$ use the scalar encoder row

$$
C_{f,\epsilon,r}=\frac1{\sqrt2}
 \langle f_\epsilon^{\rm fail}|M^{1/2}E^\dagger.
\tag{RH.32}
$$

Its whole scalar-fibre decoder sends $z$ to
$z w_\ell g(t)dt\,P_f$ separately in each original label
$\ell\in\{0,1,2,3,13\}$, where $g(t)=g_{\rm time}(t)=2/(1+t)^2$.
Finally choose once an orthonormal basis $t_1,t_2$ of
$\operatorname{ran}(I_5-P_V)$. For each $r=\pm1$ add one actual scalar
complement branch with Kraus rows $\langle t_k|/\sqrt2$, $k=1,2$:

$$
\mathcal E_{\perp,r}(A)=\frac12\operatorname{tr}((I_5-P_V)A).
\tag{RH.33}
$$

Its full decoder sends $z$ to $zg(t)dt\,P_f$ only at original label
$2$. The two rows are inaccessible Kraus multiplicity, not two retained
quantum shares or decoder-controlling labels. All scalar and high
branches retain the displayed fair report $r$.

**Theorem 5.2 (normalization and full complex/reference/output identities).**
Definition 5.1 is one finite normalized acquisition with whole-fibre TP
decoders. Its output at the cut consists of its declared joint quantum
fibre and its actual classical label. It forgets to the particular
complete approximate channel $\widehat\Phi_*$ on every complex input,
every passive reference, and every separately labelled Borel-time set.

Proof. For every complex $A_V\in M_3(\mathbb C)$, the coefficient
Gram identity and the range reconstruction in RH.27 give

$$
\begin{aligned}
\sum_jK_jA_VK_j^\dagger
 &=\delta DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger,\\
\sum_jK_j^\dagger K_j
 &=\delta D^\dagger D+T^\dagger T+S^\dagger S,\\
C_j^\dagger C_j&=EK_j^\dagger K_jE^\dagger.
\end{aligned}
\tag{RH.34}
$$

Adding RH.29 makes the live coefficient Gram $I_3$. The four spectral
row effects sum to $EME^\dagger$, because
$\Pi_++\Pi_-=I_2$ and each report receives half the mass. The
complementary effects sum to $I_5-P_V$. Thus

$$
\sum_{\text{all actual labels }\alpha}
       \mathcal E_\alpha^\dagger(I)
 =E(D^\dagger D+T^\dagger T+S^\dagger S+M)E^\dagger
     +(I_5-P_V)=I_5.
\tag{RH.35}
$$

Every finite encoder effect is positive and bounded by this sum, hence
is TNI. Every live decoder is TP on its entire fibre because $EV_j$
and $E$ are isometries. The scalar decoders are TP because
$\sum_\ell w_\ell=1$ and
$\int_0^1g(t)dt=[-2/(1+t)]_0^1=1$. No branch is normalized by
survival, by its own probability, or by an acceptance event.

For every complex $A\in M_5(\mathbb C)$, put $A_V=E^\dagger AE$.
The exact forgotten maps are

$$
\begin{aligned}
\Phi^L(A)&=E(DA_VD^\dagger+TA_VT^\dagger+SA_VS^\dagger)E^\dagger,\\
\Phi^f_\ell(A)(B)&=G_B\left[
 w_\ell\operatorname{tr}(EME^\dagger A)
 +\mathbf1_{\ell=2}\operatorname{tr}((I_5-P_V)A)\right]P_f,\\
G_B&=\int_B\frac{2}{(1+t)^2}\,dt,
\qquad B\subseteq[0,1]\text{ Borel},\quad\ell\in\{0,1,2,3,13\}.
\end{aligned}
\tag{RH.36}
$$

The live identity is an identity of Kraus conjugations; the failure
identities are identities of trace functionals, each multiplying its
own labelled measure. They hold on all complex matrix units. All
$P_V$–$(I_5-P_V)$ cross-support operators are killed, and every
wrong-support or extra-sector output is zero. Both zero-weight original
labels $0,13$ remain zero; labels $1,2,3$ remain separate. The density $g$ is
finite on the closed time interval, with no endpoint atom or singular
addition. The common metadata remain in their original fixed state.

For an arbitrary joint operator $X$ with passive reference $R$, define

$$
\begin{aligned}
\Theta_M(X)&=\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X],\\
\Theta_\perp(X)&=\operatorname{Tr}_5[((I_5-P_V)\otimes I_R)X].
\end{aligned}
\tag{RH.37}
$$

The full amplified live output is

$$
\sum_{K\in\{D,T,S\}}(EKE^\dagger\otimes I_R)X
                              (EK^\dagger E^\dagger\otimes I_R),
\tag{RH.38}
$$

and the amplified labelled failure output is, with output-reference
order fixed,

$$
G_B P_f\otimes
 [w_\ell\Theta_M(X)+\mathbf1_{\ell=2}\Theta_\perp(X)].
\tag{RH.39}
$$

More finely, a scalar spectral row contributes its exact conditional
reference operator
$(C_{f,\epsilon,r}\otimes I_R)X(C_{f,\epsilon,r}^\dagger\otimes I_R)$;
a complement branch contributes $\Theta_\perp(X)/2$.
Their sums give RH.39. Thus no conditional reference state is replaced
by an unconditional marginal, and no time binning is used. The identities
hold for every passive reference amplification and every labelled Borel
set. Tensoring the fixed metadata state completes the original output.

The actual density $g$ has not replaced the ideal $f_y$ of RH.2.
RH.36–39 identify the same complete approximate channel used in the
inherited certificate; consequently all twelve original full-cq errors,
including height $16$, keep their credited values and their maximum is
$E_*$. This uses the original certificate conditionally. $\square$

**Proposition 5.3 (all twelve acquired laws, contrast and charged mass).**
For every $y,e,n$ in RH.1, the full actual acquired law is

$$
\begin{aligned}
p(j\mid y,e,n)={}&x_j^2A_y+z_j^2B_y+w_j^2C_y
 +2x_jz_j\kappa enq_y\\
 &+2x_jw_j\kappa_{02}e\frac{\sqrt y}{16}
 +2z_jw_ja_Kc_Kn\frac{\sqrt{64-y}}{16},\\
p(H,r\mid y,e,n)&=(1-\delta)A_y/2,\\
p(f,\epsilon,r\mid y,e,n)&=\frac12\left|
 \left\langle f_\epsilon^{\rm fail},
 (\sqrt{m_1}n\sqrt{p_{y1}},\sqrt{m_2}\sqrt{p_{y2}})^T
 \right\rangle\right|^2,\\
p(\perp,r\mid y,e,n)&=0.
\end{aligned}
\tag{RH.40}
$$

These are nonnegative norm squares and sum to one by RH.35. The binary
plus effect and its twelve laws, allowing all its other coordinates,
are

$$
\begin{aligned}
F&=\frac12I_3+\frac12\sum_jr_jK_j^\dagger K_j,\\
F_5&=EFE^\dagger+(I_5-P_V)/2,\\
\Pr(+\mid y,e,n)&=\frac12+\frac12\sum_jr_jp(j\mid y,e,n),\\
\mathsf V(F)&=s_0\left|\sum_jr_j(f_j)_0(f_j)_1\right|.
\end{aligned}
\tag{RH.41}
$$

The only high fibres are RH.29, and on every normalized five-mode input
$\sigma$ their acquired probability is exactly

$$
p_H(\sigma)=(1-\delta)\operatorname{tr}(ED^\dagger DE^\dagger\sigma).
\tag{RH.42}
$$

In particular each original history has mass $(1-\delta)A_y$ and
$\mathsf W=(1-\delta)A_{27}=\mathsf C(s)$ throughout the weak interval.
The full retained-record height TV is exactly

$$
\frac12\left[(1-\delta)\Delta A+L_f+
                         \sum_j|f_j^TGf_j|\right].
\tag{RH.43}
$$

Proof. The cross effects are
$D^\dagger T+T^\dagger D=\kappa X_{01}$,
$D^\dagger S+S^\dagger D=\kappa_{02}X_{02}$ and
$T^\dagger S+S^\dagger T=a_Kc_KX_{12}$.
Born traces give RH.40. High, spectral and complement reports are fair,
so RH.35 gives RH.41, with
$\operatorname{Re}F_{01}=\kappa\sum_jr_jx_jz_j/2$.
Only the high fibres have dimension at least three; their effect proves
RH.42 even on complex coherent inputs and on reduced inputs of passive
reference states. Each low height difference is $f_j^TGf_j$, the two
high differences are positive with total $(1-\delta)\Delta A$, and
the spectral differences sum in absolute value to
$|\lambda_+|+|\lambda_-|=L_f$. This proves RH.43. $\square$

**Definition 5.4 (actual retained choice and cut accounting).** To mix
instruments with weights $a_i\geq0$, $\sum_i a_i=1$, supply encoder
Kraus matrices $\sqrt{a_i}C_{i,\alpha}$ and retain the actual choice
$i$ in the generated label $(i,\alpha)$. Keep the whole-fibre TP
decoder $\mathcal R_{i,\alpha}$. Zero-weight choices may be removed.
If the choices have the common output RH.36 and high effect RH.42,
the mixed acquisition still has total effect $I_5$, that output and
that high effect. Its oriented winding contrast is the affine sum.
Its TV is also exactly affine, since

$$
\frac12\sum_{i,\alpha}
 |a_i p_{27}(\alpha\mid i)-a_i p_5(\alpha\mid i)|
 =\sum_i a_i\operatorname{TV}_i.
\tag{RH.44}
$$

This is an actual generated choice, not a choice of unknown history or a
combination of separately attainable extrema.

A normalized acquisition dilation may use
$\sum_{\alpha,k}|\alpha\rangle_C\otimes C_{\alpha k}|\psi\rangle
\otimes|\alpha,k\rangle_Z$. RH.35 makes it an isometry. Permanently
discarding $Z$ before the counted cut dephases the actual label and
leaves exactly the declared fibre. This is environmental copying of
an instrument label, not copying the specimen. No retained specimen,
controller, entanglement share or other input-bearing share outside that
fibre is available to any later execution. If such a share is retained,
it changes the counted acquisition. Later independent blanks may serve
the TP decoders; later accessible correlated shares are not blanks.
These statements specify supplied mathematical operations, not native
permission to enact a dilation or to access a discarded environment.

## 6. The credited moving frame and actual lower bounds

The following radical coordinates reparameterize the frame in JR54.
They are used to construct common lower instruments and to express the
actual-label results. Neither the frame nor its already certified initial
optimal branch is counted as a new branch theorem here.

In Sections 6–7, $F$ denotes a moving frame vector. It is distinct from
the binary plus effect called $F$ in RH.5 and RH.41; the latter is
always the effect of the actual reports of the constructed instrument.

**Theorem 6.1 (radical frame on a closed interval).** Put

$$
\gamma=1-2\beta>0,\qquad d=1+\alpha=2-\beta,\qquad e=1+\beta,
\qquad \tau_3=\frac{2\sqrt\alpha}{d}.
\tag{RH.45}
$$

Then $\bar\tau<\tau_3<1$. For $\bar\tau\leq\tau\leq\tau_3$ define

$$
\begin{gathered}
\rho=\sqrt{\beta^2+e\gamma\tau^2},\qquad
A=\frac{\beta+\rho}{2e},\qquad B=\frac{\rho-\beta}{2\gamma},
\qquad Z=1-A-B,\\
U=(\sqrt A,\sqrt B,-\sqrt Z)^T,\qquad n_0=\sqrt{A+B},\\
p=\frac{(\sqrt B,-\sqrt A,0)^T}{n_0},\qquad
q=\frac{(\sqrt{AZ},\sqrt{BZ},A+B)^T}{n_0},\\
\alpha_0=\frac{B-\alpha A}{A+B},\qquad
\beta_0=\frac{d\sqrt{ABZ}}{A+B},\qquad
k=-\frac{\alpha_0}{\beta_0+\sqrt{\alpha_0^2+\beta_0^2}},\\
F=\frac{p+kq}{\sqrt{1+k^2}},\qquad
W=\frac{-kp+q}{\sqrt{1+k^2}}.
\end{gathered}
\tag{RH.46}
$$

The scalars $A,B,Z$ here are squared frame coordinates, not input
matrices or resource functions. These formulas give a continuous
orthonormal $Q$-null frame $(U,F,W)$ on the entire closed interval,
smooth near $\bar\tau$. It starts with $U=u$, $F=v$, and $W$ on
the $w$ line. At $\tau_3$ it equals

$$
U=\frac{(\sqrt\alpha,1,0)^T}{\sqrt d},\qquad
F=\frac{(1,-\sqrt\alpha,-\sqrt d)^T}{\sqrt{2d}},\qquad
W=\frac{(1,-\sqrt\alpha,\sqrt d)^T}{\sqrt{2d}}.
\tag{RH.47}
$$

Proof. A unit $Q$-null vector with squared coordinates $(A,B,Z)$
satisfies

$$
A=\alpha B+\beta Z,\quad A+B+Z=1,\qquad
A=\frac{\alpha-\gamma Z}{d},\quad
B=\frac{1-eZ}{d},\quad0\leq Z\leq1/e.
\tag{RH.48}
$$

On this range the numerator of the derivative of
$AB=(\alpha-\gamma Z)(1-eZ)/d^2$ is
$-(\alpha e+\gamma)+2\gamma eZ\leq\gamma-\alpha e
=-\beta(2-\beta)<0$. Thus its maximum is $\alpha/d^2$, only at
$Z=0$. For the initial $u$, $Z/A=z_*^2>0$, so
$\bar\tau=2\sqrt{AB}<\tau_3$. Also
$d^2-4\alpha=\beta^2>0$ gives $\tau_3<1$.

Solving $eA-\gamma B=\beta$ and $AB=\tau^2/4$ with positive
$A,B$ gives precisely RH.46. Its initial solution is the squared
coordinates of $u$ with the indicated signs. As $\tau$ increases,
$\rho,A,B$ increase and $Z$ decreases continuously to zero, with
endpoint $(A,B,Z)=(\alpha/d,1/d,0)$. Therefore $A,B>0$, $Z\geq0$
and $n_0>0$ on the closed interval. All square roots are defined;
only $\sqrt Z$ reaches zero, at the final endpoint.

Direct dot products give $p^Tp=q^Tq=1$, $p^Tq=p^TU=q^TU=0$.
Their $Q$ compression has diagonal $\alpha_0,-\alpha_0$ and
cross entry $\beta_0$. Initially $B/A=b_*^2>(49/50)^2>\alpha$,
so $\alpha_0>0$. The numerator $B-\alpha A$ increases with $\rho$
since $e-\alpha\gamma=2\beta(2-\beta)>0$. Thus $\alpha_0>0$
everywhere on the closed interval, while $\beta_0\geq0$.
Consequently the denominator defining $k$ is positive and
$-1\leq k<0$, with $k=-1$ exactly at the final endpoint.
The algebraic identity
$\alpha_0(1-k^2)+2\beta_0k=0$ proves $F^TQF=W^TQW=0$.
Their orthonormality follows from the displayed rotation of $(p,q)$.
This proves all radical and frame denominator claims, without claiming
smoothness at the final square-root boundary.

To identify the initial negative line, $Z=A z_*^2<1/100$ there and
$B/A=b_*^2>\alpha>87/100$, so $B>AZ$. The formulas and
$-1\leq k<0$ give $F_0>0$, $F_1<0$, $F_2<0$ initially.
The only real null lines in $u^\perp$ are the $v,w$ lines. The line
$v$ has first coordinate positive and third negative; for
$w=v\times u$, its first and third coordinates are proportional to
$t_*b_*-z_*>0$ and $q(t_*)b_*+1>0$. Thus $F$ initially belongs to
$v$, not $w$, and its unit normalization and first sign give $F=v$.
The other line is $w$ up to its irrelevant vector sign. Substitution
of $Z=0$, $k=-1$ gives RH.47. $\square$

**Proposition 6.2 (actual frame and retained-mixture lower bounds).** Use
Definition 5.1 with the three vectors $(U,F,W)$ and reports $(+,-,-)$.
It has eleven base labels, with dimensions
$(2,2,2,3,3,1,1,1,1,1,1)$, and contrast exactly $s_0\tau$ because

$$
U_0U_1-F_0F_1-W_0W_1=2U_0U_1=\tau.
\tag{RH.49}
$$

No assumption on the individual signs of $F_0F_1,W_0W_1$ away from
the initial point is needed. It actually attains the value

$$
T_3(\tau)=\frac12\left[(1-\delta)\Delta A+L_f+
 |U^TGU|+|F^TGF|+|W^TGW|\right],
\qquad\mathcal T(s_0\tau)\geq T_3(\tau).
\tag{RH.50}
$$

At the closed endpoint define

$$
B_0=\frac{g_0+\alpha g_1}{2d}+\frac{g_2}{2}
                         -\frac{\sqrt\alpha x}{d},\qquad
D_0=\frac{y-\sqrt\alpha z}{\sqrt d}.
\tag{RH.51}
$$

Then $T_3(\tau_3)=T_{\rm flat}-B_0+D_0$.
For $\tau_3\leq\tau\leq1$ an actual retained mixture gives

$$
\mathcal T(s_0\tau)\geq
\frac{1-\tau}{1-\tau_3}T_3(\tau_3)
 +\frac{\tau-\tau_3}{1-\tau_3}T_{\rm end}.
\tag{RH.52}
$$

Proof. Orthonormality makes the three $01$ products sum to zero,
which proves RH.49. RH.35–43 prove every original-class assertion
and the exact attained value RH.50. At RH.47, expansion gives
$U^TGU>0$, $F^TGF=B_0-D_0$ and $W^TGW=B_0+D_0$.
For completeness the coarse conditional bounds RH.17 already imply
that only $F$ is negative. They give
$87/100<\alpha<88/100$, $187/100<d<188/100$,
$9/10<\sqrt\alpha<1$, $\sqrt d<7/5$, and

$$
\begin{aligned}
B_0&>-\frac{2372/10^6}{187/100}>-13/10000,\\
B_0&<\frac{1270/10^6+(88/100)(293/10^5)}{2(187/100)}
       +\frac{168/10^5}{2}
       -\frac{(9/10)(2370/10^6)}{188/100}<8/10000,\\
D_0&>\frac{2207/10^6}{7/5}>15/10000.
\end{aligned}
\tag{RH.53}
$$

These are rational comparisons, not sampled signs. Positivity of the
entries $g_0,g_1,x$ makes $U^TGU>0$. Thus replacing the sole negative
live difference by its absolute value in RH.43 and using RH.10 proves
$T_3(\tau_3)=T_{\rm flat}-(B_0-D_0)$.

For the other endpoint use the four low vectors
$d_{\sigma,t}=(1,\sigma,t)^T/2$, reporting $r=\sigma$, in
Definition 5.1. Their Gram is $I$, all four are null and rank-two
compressed, and RH.49's signed sum is replaced by one. The three
positive and one negative $G$ values give its exact actual TV
$T_{\rm end}$, as also proved in Section 10. It has twelve base labels.
Retain a choice between that instrument and the $\tau_3$ frame with
weights $(1-\tau)/(1-\tau_3)$ and $(\tau-\tau_3)/(1-\tau_3)$.
They lie in $[0,1]$, have a positive denominator, and give oriented
contrast exactly $\tau$. Definition 5.4 proves the full output, sharp
cost and affine actual TV simultaneously. Interior mixtures have at
most twenty-three labels; zero-weight endpoint choices are removed.
Neither RH.50 nor RH.52 is asserted globally height-optimal. $\square$

## 7. The credited complete residual curve and its curvature corollaries

**Proposition 7.1 (credited initial branch and identified contact).** Let
$t_\dagger$ be the least active discriminant zero of JR.142–143, and
$\tau_\dagger=h(t_\dagger)$ in JR.141. JR54 and RC63 give

$$
\bar\tau<\tau_\dagger<\tau_3,
\qquad J(\tau)=\operatorname{tr}G-2\phi(\tau),\qquad
\mathcal T(s_0\tau)=T_{\rm flat}-\phi(\tau),
\quad \bar\tau\leq\tau\leq\tau_\dagger,
\tag{RH.54}
$$

where $\phi(\tau)=F(\tau)^TGF(\tau)$ for Theorem 6.1's frame.
Throughout this closed interval the optimal grouped tuple is uniquely

$$
X_{-,-}=FF^T,\qquad X_{+,+}=UU^T,\qquad
X_{-,+}=WW^T,\qquad X_{+,-}=0.
\tag{RH.55}
$$

JR54 supplies uniqueness before the contact; RC62–63 supplies it also
at the contact. RC's complete-source comparisons identify the first
factor and give

$$
\begin{gathered}
1.04175447537<t_\dagger<1.04175447539,\qquad
.9962433511188<\tau_\dagger<.9962433511192,\\
d_+(t_\dagger)=0,\quad d_+'(t_\dagger)<0,\quad
 d_-(t_\dagger)>0,\quad d_N(t_\dagger)>0,\\
.0460291518<\lambda_\dagger<.0460291520,\qquad
.0081796784563<J(\tau_\dagger)<.0081796784566.
\end{gathered}
\tag{RH.54a}
$$

These are named conditional RC comparisons, not newly executed
arithmetic. The zero is a genuine support transition, as specified in
Proposition 7.5. Definition 5.1 gives a matching eleven-label instrument
with exactly three actual low live-bearing labels on the whole closed
initial branch.

Proof of correspondence. JR54's positive-positive-negative vector has
unit norm, is $Q$-null and has $01$ product $\tau/2$. Its squared
coordinates therefore solve the two linear relations and positive
quadratic root in RH.46–48. Hence its projector is $UU^T$. The
compression of $Q$ to $U^\perp$ is nonzero traceless, with exactly two
real null lines. Both parameterizations continue the same initial
negative line $v$; continuity selects $FF^T$ and the remaining line
$WW^T$. The strictly increasing JR parameter $h(t)$ maps its certified
interval to the stated one. JR.144–152 supplies the initial value and
interior uniqueness. RC.37–46 identifies its endpoint and proves the
unique aggregate there and the gluing to the next branch. Theorem 5.2
supplies the actual common realization. None of these reused branch,
discriminant or gluing results is a new claim of this companion.
$\square$

**Proposition 7.2 (an explicit alternative four-block certificate).** In
the smooth interior $\bar\tau<\tau<\tau_3$ use the ordered frame
$(f,u,w)=(F,U,W)$ and put

$$
\begin{gathered}
g_{ij}=f_i^TGf_j,\quad c_{ij}=f_i^TCf_j,\quad
q_{ij}=f_i^TQf_j,\qquad(f_f,f_u,f_w)=(f,u,w),\\
\mathsf P=q_{fu},\quad\mathsf R=q_{fw},\quad\mathsf S=q_{uw},\\
D_1=c_{fu}-\mathsf P c_{uw}/\mathsf S,\qquad
D_2=c_{fw}-\mathsf R c_{uw}/\mathsf S,\\
E_g=g_{uw}-\mathsf S g_{fw}/\mathsf R,\qquad
\phi=g_{ff},\qquad
\lambda=\frac{\mathsf P g_{fw}/\mathsf R-g_{fu}}{D_1},\\
B_\lambda=\begin{pmatrix}
g_{uu}&E_g-\lambda c_{uw}\\
E_g-\lambda c_{uw}&g_{ww}-\lambda c_{ww}
\end{pmatrix},\qquad z_c=(c_{fu},c_{fw})^T.
\end{gathered}
\tag{RH.56}
$$

All $\mathsf P,\mathsf R,\mathsf S,D_1$ are nonzero. They are moving
quantities evaluated at the current $\tau$. Define $\mathcal D$ by the
following simultaneous strict scalar conditions:

$$
\begin{gathered}
\lambda>0,\quad\phi<0,\quad g_{uu},g_{ww}>0,\quad
c_{uu}>0,\quad c_{ff},c_{ww}<0,\\
M_1=(-\phi)c_{uu}-\lambda D_1^2>0,\\
M_2=(-\phi-\lambda c_{ff})(-c_{ww})-\lambda D_2^2>0,\\
M_3=(g_{uu}+\lambda c_{uu})g_{ww}-E_g^2>0,\\
M_4=\det B_\lambda>0,\qquad
M_5=-c_{ff}-\lambda z_c^TB_\lambda^{-1}z_c>0.
\end{gathered}
\tag{RH.57}
$$

The inverse exists under the preceding positive-pivot conditions.
For every $\tau\in\mathcal D$, RH.54–55 hold, including grouped
uniqueness. This domain contains an interval immediately to the right
of $\bar\tau$. It is a pointwise sufficient certificate domain, with
no assertion of connectedness, maximality or a new optimal branch.
The certificate is an alternative gauge for the already credited
initial branch.

Proof. In this orthonormal null frame, $Q$ has zero diagonal and

$$
2\mathsf P\mathsf R\mathsf S=\det Q=\alpha\beta>0.
\tag{RH.58}
$$

Differentiate the smooth frame with respect to $\tau$ as
$f'=a u+b w$, $u'=-a f+c w$, $w'=-b f-c u$. Nullity gives
$b=-a\mathsf P/\mathsf R$ and $c=a\mathsf P/\mathsf S$.
Since $2u^TCu=\tau$,

$$
1=-4aD_1,\qquad
f'=-\frac{u-(\mathsf P/\mathsf R)w}{4D_1},\qquad
\phi'=\frac{\mathsf P g_{fw}/\mathsf R-g_{fu}}{2D_1}
       =\lambda/2.
\tag{RH.59}
$$

This proves the denominator claims and a derivative identity of the
frame, without assuming its optimality. In this proof $a,b,c$ are only
frame-derivative coefficients, not Kraus amplitudes or normalized
parameters.

Choose

$$
\nu_{-,+}=0,\qquad \nu_{+,+}=2\lambda c_{uw}/\mathsf S,\qquad
\nu_{-,-}=-2g_{fw}/\mathsf R,\qquad \nu_{+,-}=\nu_{-,-},
\tag{RH.60}
$$

and define the symmetric $Y$ in this frame by diagonal
$(-\phi-\lambda c_{ff},\ g_{uu}+\lambda c_{uu},\ g_{ww}-\lambda c_{ww})$
and upper entries
$(g_{fu}+\lambda c_{fu}-\nu_{+,+}\mathsf P,
 g_{fw}-\lambda c_{fw},
 g_{uw}-\lambda c_{uw})$.
For the original dual slacks
$S_{r,\epsilon}=Y-\epsilon G-\lambda rC+\nu_{r,\epsilon}Q$,
substitution yields all four full matrices:

$$
\begin{aligned}
\frac{S_{-,+}}2&=\begin{pmatrix}
-\phi&\lambda D_1&0\\\lambda D_1&\lambda c_{uu}&0\\0&0&0
\end{pmatrix},\\
\frac{S_{+,+}}2&=\begin{pmatrix}
-\phi-\lambda c_{ff}&0&-\lambda D_2\\0&0&0\\
-\lambda D_2&0&-\lambda c_{ww}
\end{pmatrix},\\
\frac{S_{-,-}}2&=\begin{pmatrix}
0&0&0\\0&g_{uu}+\lambda c_{uu}&E_g\\0&E_g&g_{ww}
\end{pmatrix},\\
\frac{S_{+,-}}2&=\begin{pmatrix}
-\lambda c_{ff}&-\lambda c_{fu}&-\lambda c_{fw}\\
-\lambda c_{fu}&g_{uu}&E_g-\lambda c_{uw}\\
-\lambda c_{fw}&E_g-\lambda c_{uw}&g_{ww}-\lambda c_{ww}
\end{pmatrix}.
\end{aligned}
\tag{RH.61}
$$

The first two nonzero block determinants are $\lambda M_1$ and
$\lambda M_2$, with positive first pivots. The third block has positive
first pivot and determinant $M_3$. Their kernels are respectively
$w,u,f$. The fourth lower block is $B_\lambda\succ0$ and its scalar
Schur complement is $\lambda M_5>0$. Thus the first three full slacks
are PSD of rank two and the fourth is PD. Positivity only on the null
cone has not replaced matrix positivity.

RH.55 is primal feasible with contrast
$-c_{ff}+c_{uu}-c_{ww}=2c_{uu}=\tau$. Its objective is
$\operatorname{tr}G-2\phi$. Also
$\operatorname{tr}Y=\operatorname{tr}G-2\phi+\lambda\tau$.
For every feasible original tuple, summing its PSD pairings with RH.61
therefore gives

$$
\text{objective}\leq\operatorname{tr}Y-\lambda t(X)
\leq\operatorname{tr}Y-\lambda\tau
=\operatorname{tr}G-2\phi.
\tag{RH.62}
$$

This direction uses $\lambda\geq0$ and the original contrast
inequality. Theorem 2.2 transfers the upper bound to every original
complex optimizer; Section 5 gives actual equality. Complementarity
forces each slot into the corresponding kernel and kills the fourth
slot. Normalization fixes the other three weights to one, proving
precisely grouped uniqueness.

At $\bar\tau$, $Gv=\mu v-\lambda_{\rm sp}Qv$, so
$\lambda=0$ and $\phi=\mu$. The $2\times2$ matrix with diagonal
$g_{uu},g_{ww}$ and cross entry $E_g$ is $H_+|_{v^\perp}\succ0$.
The limits of $M_1,M_2$ are $(-\mu)c_{uu}>0$, $\mu c_{ww}>0$;
$M_3,M_4$ tend to its positive determinant, and $M_5$ to $-c_{ff}>0$.
Twice differentiating the unit and null equations gives

$$
\phi''(\bar\tau)=2f'(\bar\tau)^T(H-\mu I)f'(\bar\tau)>0.
\tag{RH.63}
$$

RH.59 makes $f'$ nonzero and perpendicular to $v$, where $H-\mu I$
is positive definite. Thus $\lambda=2\phi'>0$ just to the right;
continuity preserves every other strict margin there. This proves
nonemptiness. These extra fourth-gauge filters need not locate the
first active zero in JR54, and their failure is not an optimal-support
transition theorem. $\square$

**Corollary 7.3 (explicit optimized initial curvature).** Only in this
corollary, stars on the following scalar quantities denote evaluation
at $\tau=\bar\tau$:

$$
\begin{gathered}
\mathsf P_*=v^TQu,\quad\mathsf R_*=v^TQw,\quad\mathsf S_*=u^TQw,\\
D_*=v^TCu-\mathsf P_*(u^TCw)/\mathsf S_*,\qquad
z_{\rm tan}=u-(\mathsf P_*/\mathsf R_*)w,\\
K_{\rm opt}=\frac{z_{\rm tan}^T(H-\mu I)z_{\rm tan}}{16D_*^2}>0.
\end{gathered}
\tag{RH.64}
$$

As $h\downarrow0$,

$$
\begin{aligned}
T_{\rm bar}-\mathcal T(s_0(\bar\tau+h))
 &=K_{\rm opt}h^2+O(h^3),\\
J(\bar\tau)-J(\bar\tau+h)&=2K_{\rm opt}h^2+O(h^3),\\
\lambda(\bar\tau+h)&=4K_{\rm opt}h+O(h^2).
\end{aligned}
\tag{RH.65}
$$

The optimized curve has zero right derivative at $\bar\tau$ and
$\bar s$; its physical-$s$ quadratic coefficient is $K_{\rm opt}/s_0^2$.
Every optimal normalized contrast multiplier on the differentiable
initial branch equals $2\phi'$. This is an explicit corollary of
JR54's exact branch and JR.151–152, not a new exact branch theorem.

Proof. RH.58–59 prove that all denominators in RH.64 are nonzero and
$f'(\bar\tau)=-z_{\rm tan}/(4D_*)$. Substitution in RH.63 gives
$\phi''(\bar\tau)=2K_{\rm opt}$. The vector $z_{\rm tan}$ is nonzero
in $v^\perp$, which proves strict positivity. The initial radicals and
normalizations are strictly positive, so the frame is real analytic
near $\bar\tau$. Taylor expansion of the true value in RH.54 gives
RH.65. At a moving point, any optimal dual supports the concave value
function by
$J(\tau')\leq J(\tau)-\lambda(\tau'-\tau)$; differentiability forces
$\lambda=-J'(\tau)=2\phi'(\tau)$. Thus the contrast multiplier is
unique even if other dual coordinates have a common $Q$ gauge. The
moving identities RH.56–59 use moving $\mathsf P,\mathsf R,\mathsf S$;
initial starred constants are not substituted into those identities.
$\square$

**Corollary 7.4 (constructive improvement of the old residual chord).**
The global quadratic upper bound and the exact initial branch imply
locally, for some finite $K>0$,

$$
0<\frac{(\tau-\bar\tau)^2}{8\kappa_d}
\leq T_{\rm bar}-\mathcal T(s_0\tau)
\leq K(\tau-\bar\tau)^2.
\tag{RH.66}
$$

There is an actual piecewise affine lower bound strictly above the
credited plateau-to-endpoint chord at every residual interior point.

Proof. RH.19 gives the left inequality, and RH.65 the right. Write

$$
\ell_{\rm old}(\tau)=\frac{1-\tau}{1-\bar\tau}T_{\rm bar}
+\frac{\tau-\bar\tau}{1-\bar\tau}T_{\rm end}.
$$

Choose a fixed $\vartheta\in(\bar\tau,\tau_\dagger)$ sufficiently close
to $\bar\tau$ that $V_0=T_3(\vartheta)>\ell_{\rm old}(\vartheta)$;
the quadratic loss and strictly negative chord slope ensure existence.
Retain the actual choice between the $\bar\tau$ and $\vartheta$
instruments below $\vartheta$, and between the $\vartheta$ and endpoint
instruments above it. The resulting lower value is

$$
\ell_{\rm imp}(\tau)=\begin{cases}
\dfrac{\vartheta-\tau}{\vartheta-\bar\tau}T_{\rm bar}
+\dfrac{\tau-\bar\tau}{\vartheta-\bar\tau}V_0,
&\bar\tau\leq\tau\leq\vartheta,\\[2mm]
\dfrac{1-\tau}{1-\vartheta}V_0
+\dfrac{\tau-\vartheta}{1-\vartheta}T_{\rm end},
&\vartheta\leq\tau\leq1.
\end{cases}
\tag{RH.67}
$$

Definition 5.4 proves exact affine TV and oriented contrast, with common
output, high effect and sharp cost. Subtracting $\ell_{\rm old}$ gives
respectively $(\tau-\bar\tau)/(\vartheta-\bar\tau)$ and
$(1-\tau)/(1-\vartheta)$ times the strictly positive number
$V_0-\ell_{\rm old}(\vartheta)$. Thus the improvement is strict at every
interior point and vanishes at the closed endpoints. The two segments
use at most twenty-two and twenty-three actual labels. This constructive
corollary is a lower bound below the complete value supplied by RC; it
is not an additional exact branch theorem. $\square$

**Proposition 7.5 (RC's complete post-contact value and contact data).**
Use the same $Q,C,G,L$ as in RH.8. To state the supplied algebraic
continuation without confusing its scalar coordinates with source Kraus
matrices, for $0\leq a\leq37/125$ and $7/20\leq k\leq2/5$ put

$$
\begin{aligned}
D_a&=\alpha(1-2a)+a^2,&U_a&=-\alpha+2a-a^2,&V_a&=\alpha-a^2,\\
n_a&=(D_a,U_a,V_a)^T,&\sigma_a&=D_aU_a,\\
W_a&=D_a Cn_a-2\beta akQn_a,&H_a&=-n_a^TQW_a,&R_a&=W_a^TQW_a,\\
Z_a&=2H_aW_a+R_an_a,&
\mathcal E_a&=2H_aW_a^TW_a+D_aR_a\sigma_a,\\
g_a&=Z_a^TGZ_a,&
\ell_a&=D_a^2\sigma_a Z_a^TCZ_a-\mathcal E_a^2,\\
\mathcal P(a,k)&=a^{-1}\det[D_a^2\sigma_a CZ_a-\mathcal E_aW_a,\ QZ_a,\ GZ_a].
\end{aligned}
\tag{RH.67a}
$$

The divisions defining $\ell_a/a$ and $\mathcal P$ are exact polynomial
divisions before evaluation, including at $a=0$. RC59–60 supplies a
unique analytic selected root $k(a)\in(7/20,2/5)$ of $\mathcal P=0$.
All subsequent expressions in this proposition use that root. Its
full-rectangle comparisons give $D_a,H_a,R_a,\mathcal E_a>0$,
$\sigma_a<0$, $g_a<0$, $\ell_a/a<0$. Define

$$
\begin{aligned}
B_a&=-\frac{R_a}{2D_a\sigma_a H_a}n_an_a^T,&
C_a&=\frac{Z_aZ_a^T}{2H_a\mathcal E_a},&A_a&=I-B_a-C_a,\\
\omega_a&=\operatorname{tr}A_a-1,&\tau(a)&=2(A_a)_{01}.
\end{aligned}
\tag{RH.67b}
$$

RC60 supplies the unique simple zero $a_\dagger$ of $\omega_a$ with
$.2951251<a_\dagger<.2951252$. RC61–63 supplies the following whole
conditional conclusion, including original all-four-PSD necessity:

$$
\begin{gathered}
\tau:[0,a_\dagger]\longrightarrow[\tau_\dagger,1]
\text{ is a continuous strictly decreasing bijection},\\
J(\tau(a))=\operatorname{tr}G-\frac{g_a}{H_a\mathcal E_a},\qquad
\mathcal T(s_0\tau(a))=T_{\rm flat}-\frac{g_a}{2H_a\mathcal E_a},\\
(X_{+,+},X_{+,-},X_{-,+},X_{-,-})=(A_a,0,B_a,C_a),\\
\operatorname{rank}(A_a,B_a,C_a)=
\begin{cases}(2,1,1),&0\leq a<a_\dagger,\\(1,1,1),&a=a_\dagger.
\end{cases}
\end{gathered}
\tag{RH.67c}
$$

For $0<a\leq a_\dagger$ the aggregate tuple is unique. At $a=0$ it
is the unique endpoint aggregate of Proposition 10.1. The two null
lines in $W_a^\perp$ and their exact weights are

$$
\begin{aligned}
N_{Q,a}&=\beta(W_a)_1^2+\alpha(W_a)_2^2-\alpha\beta(W_a)_0^2>0,\\
v_\pm(a)&=\frac{-\alpha(W_a)_0(W_a)_2
 \pm(W_a)_1\sqrt{N_{Q,a}}}
 {\alpha(W_a)_2^2+\beta(W_a)_1^2},\\
u_\pm(a)&=-\frac{(W_a)_0+(W_a)_2v_\pm(a)}{(W_a)_1},\qquad
q_\pm(a)=(1,u_\pm(a),v_\pm(a))^T,\\
w_+(a)&=\frac{(A_a)_{02}-v_-(a)(A_a)_{00}}{v_+(a)-v_-(a)},\qquad
w_-(a)=\frac{v_+(a)(A_a)_{00}-(A_a)_{02}}{v_+(a)-v_-(a)},\\
A_a&=w_+(a)q_+(a)q_+(a)^T+w_-(a)q_-(a)q_-(a)^T.
\end{aligned}
\tag{RH.67d}
$$

Every denominator displayed here is nonzero by RC60's comparisons.
The lines $q_+,q_-,n_a,Z_a$ are distinct. Both $w_\pm$ are positive
for $0\leq a<a_\dagger$; at contact $w_+=0<w_-$. The $A_a$ rays
have positive $01$ product and positive height difference; $n_a$ has
negative $01$ product and positive height difference; $Z_a$ has
negative $01$ product and negative height difference.

At $a=a_\dagger$ the surviving three weighted vectors are exactly the
orthonormal frame in RH.55 and $Z_2/Z_1=t_\dagger$. RC63 matches both
values and normalized multipliers there, giving $C^1$ gluing. It also
supplies the positive linear onset

$$
\lim_{a\uparrow a_\dagger}\frac{w_+(a)}{a_\dagger-a}
=\frac{-\omega'(a_\dagger)}{w_-(a_\dagger)K_A(a_\dagger)}>0,
\quad K_A=\|q_+\|^2\|q_-\|^2-(q_+^Tq_-)^2>0,
\tag{RH.67e}
$$

and $w_+(a)>9(a_\dagger-a)/1000$ on $7/25\leq a<a_\dagger$.
There is no later interior contact or aggregate-rank transition.
At $a=0$ the four coordinate-$0$-one rays are $(1,\pm1,\pm1)$,
each with coefficient weight $1/4$. RC64 identifies the same inherited
endpoint square-root constant and multiplier law of Section 10.

Proof of use and actual correspondence. This proposition invokes
RC.8–46's selected root, interval/Bernstein comparisons, matching four
dual blocks, uniqueness, coverage and gluing as named conditional
suppliers; it does not repeat or numerically reauthenticate them. The
coefficient dictionary RC.2–3 is exactly RH.7–8, so its $j$ is this
$J$, its $C_0$ is $C_a$, and its $T_{\rm flat}$ is RH.9's constant
by RH.10. Thus its original contrast inequality, not a prescribed
effect, is the same optimization RH.11.

For the actual converse take the nonzero members of

$$
\sqrt{w_+}\,q_+,\quad\sqrt{w_-}\,q_-,\quad
\sqrt{-R_a/(2D_a\sigma_a H_a)}\,n_a,\quad
Z_a/\sqrt{2H_a\mathcal E_a},
\tag{RH.67f}
$$

reporting $(+,+,-,-)$. Their real null projectors sum to $I$ by
RH.67b,d. Their signed $01$ sum is
$\operatorname{tr}(CA_a)-\operatorname{tr}(CB_a)-\operatorname{tr}(CC_a)
=2(A_a)_{01}=\tau(a)$, since $\operatorname{tr}C=0$.
Their absolute $G$ sum is
$\operatorname{tr}G-2\operatorname{tr}(GC_a)
=\operatorname{tr}G-g_a/(H_a\mathcal E_a)$ by the stated signs.
Definition 5.1 therefore supplies one normalized finite instrument
with the full complex/reference/five-labelled-Borel output RH.36–39,
all twelve inherited errors, sharp high acquired cost and exactly the
value RH.67c. All its decoders are TP on their entire declared fibres.
It has four actual low live-bearing labels above contact and three
at contact, and twelve or eleven total labels in this construction.
The upper bound applies to every original optimizer by RC's original
four-block certificate and Theorem 2.2. The algebraic coefficients are
not Born probabilities or a source prior. This is a reuse of RC's
actual realization, not a new residual-curve discovery. The universal
actual-label lower bound is proved separately in Theorem 9.5.
$\square$

## 8. Actual low live-bearing label rigidity and the feasibility threshold

**Definition 8.1 (the counted labels).** A low live-bearing acquisition
label is an actual CP acquisition outcome with whole joint fibre
dimension at most two and nonzero supported decoded live CP map.
Ignore null outcomes and outcomes with zero supported decoded live map.
The count is a count of actual labels, not projective-ray classes,
analytic Kraus products, total alphabet or original failure labels.

For a stipulated integral record, a finite count means that its
live-bearing CP subinstrument is supported on that many actual labels
of nonzero CP mass, modulo null outcomes. A positive nonatomic
live-bearing component has infinitely many actual labels. A pointwise
count of a chosen density representative is not intrinsic. If an
integral variable is not acquired, it belongs to inaccessible encoder
Kraus multiplicity of the coarse actual label; it cannot select a
separate decoder. These conventions retain the original integral scope.

**Lemma 8.2 (one actual low branch has one real-null ray).** In the
original sharp-cost weak class, every actual low live-bearing label
has dimension two, and the coefficient Gram of all its supported
encoder/live-decoder products has rank one on a projective real-null
ray. Arbitrary inaccessible encoder and decoder Kraus multiplicities
are allowed.

Proof. Restrict an actual encoder to the supported qutrit and write its
Kraus matrices as $C_j:\mathbb C^3\to\mathbb C^d$ and its compressed
live-decoder matrices as $R_i:\mathbb C^d\to\mathbb C^3$.
Theorem 2.2 puts every nonzero product $R_iC_j$ on a phase multiple
of a real-null matrix

$$
K(x,z,w)=\begin{pmatrix}
xh_0&za_K&wc_K\\zb_K&xh_1&0\\wd_K&0&xh_2
\end{pmatrix},\qquad x\ne0.
\tag{RH.68}
$$

Its nonzero $1,2$ minor makes its rank exactly two. Dimension one is
therefore not live-bearing. For $d=2$, choose a nonzero
$R_{i_0}C_{j_0}$. Rank two makes $R_{i_0}$ injective and $C_{j_0}$
onto. Every nonzero $C_j$ gives a nonzero product $R_{i_0}C_j$;
it has rank two and the same image $\operatorname{ran}R_{i_0}$.

The left null line of RH.68 is generated by

$$
\left(1,-\frac{a_Kz}{h_1x},-\frac{c_Kw}{h_2x}\right)^T.
\tag{RH.69}
$$

For a common complex phase the same real representative gives the line.
Because $a_K,c_K,h_1,h_2$ are nonzero, the image determines $z/x,w/x$
and therefore its coefficient ray. Thus all $R_{i_0}C_j$ are
proportional to $R_{i_0}C_{j_0}$, and injectivity makes all nonzero
$C_j$ proportional to $C_{j_0}$.

For every nonzero $R_i$, surjectivity of $C_{j_0}$ makes $R_iC_{j_0}$
nonzero, hence rank two. Its right kernel is the fixed
$\ker C_{j_0}$, and its right null line is generated by

$$
\left(1,-\frac{b_Kz}{h_1x},-\frac{d_Kw}{h_2x}\right)^T.
\tag{RH.70}
$$

The nonzero $b_K,d_K,h_1,h_2$ again determine the same coefficient
ray. Hence all nonzero products of the actual label lie on that ray;
their summed coefficient Gram is rank one. All denominators used in
RH.69–70 are nonzero. The proof never assumes an isometric encoder or
a TP live decoder. Attached later failure subeffects are allowed and
are dominated by $M$, so they add no $01$ winding coordinate.
This argument applies to each convergent countable CP branch and
almost everywhere under the stipulated integral Kraus hypotheses.
If a hidden integral index is aggregated into one actual label, the
aggregated CP map has its ordinary finite-dimensional Kraus
representation and its one actual decoder; the same proof applies.
No inaccessible index is made readable. $\square$

**Theorem 8.3 (exact three-versus-four inequality-feasibility minimum).**
The minimum number $n_{\rm low}(s)$ of actual low live-bearing labels
in the original sharp-cost contrast-inequality feasibility class is

$$
\boxed{
n_{\rm low}(s)=
\begin{cases}
3,&0\leq s\leq s_0\tau_3,\\
4,&s_0\tau_3<s\leq s_0.
\end{cases}}
\tag{RH.71}
$$

This is not a minimum total alphabet, an exact-contrast attenuation
count, an optimal-height sufficiency statement or an optimal-contact
threshold.

Proof. The normalized low coefficient Gram is $I_3$ by Theorem 2.2.
Lemma 8.2 makes each actual low live-bearing label's contribution rank
one, so there must be at least three such labels, also for $s=0$.
If there are at most three, there are exactly three. Absorb their
positive weights into real vectors $f_i$ and form the square column
matrix $F_0$. The identity $F_0F_0^T=I$ implies $F_0^TF_0=I$;
thus they are a unit orthonormal $Q$-null frame. Arbitrary assigned
reports, including stochastic mean reports in $[-1,1]$, have normalized
contrast at most $\sum_i|(f_i)_0(f_i)_1|$.
The three products sum to zero. For three real numbers summing to zero,
their absolute sum is twice the largest absolute one: if two have the
same sign, their sum is the opposite of the third; zero cases obey the
same identity.

For any unit null vector, RH.48 gives

$$
AB=\frac{(\alpha-\gamma Z)(1-eZ)}{d^2}\leq\frac\alpha{d^2},
\qquad
\alpha-(\alpha-\gamma Z)(1-eZ)
 =Z(\alpha e+\gamma-\gamma eZ)\geq0,
\tag{RH.72}
$$

strictly when $Z>0$, since $0\leq Z\leq1/e$ and $\alpha e>0$.
It follows that $2|f_0f_1|\leq2\sqrt\alpha/d=\tau_3$.
Every implementation with at most three actual low live-bearing labels
therefore has $\mathsf V(F)\leq s_0\tau_3$.

The frame RH.47 has products
$\sqrt\alpha/d,-\sqrt\alpha/(2d),-\sqrt\alpha/(2d)$.
Its reports $(+,-,-)$ reach $\tau_3$ with exactly three actual low
live-bearing labels, error $E_*$, sharp cost and the full output of
Section 5. Because the requirement is $\mathsf V(F)\geq s$, that
one instrument is feasible for every required $s\leq s_0\tau_3$.
For larger requirements, the four-low-ray endpoint instrument of
Proposition 6.2 has contrast $s_0$ and is feasible, with exactly four
such labels. The obstruction excludes three, proving RH.71.
Neither sufficiency uses report attenuation that might add labels.

If the actual record is countable, nonnegative sums give the same
rank-one contribution for each nonzero CP label. If it is an allowed
integral and has only finitely many actual live-bearing labels, their
CP masses are atoms and the same finite Gram sum applies. A positive
nonatomic live-bearing component has infinitely many labels, so cannot
be a counterexample with at most three. Null density values or arbitrary
changes on null sets do not alter this conclusion. Inaccessible integral
indices remain multiplicity, as in Lemma 8.2.

Every height-optimal implementation above $s_0\tau_3$ must in
particular have at least four such labels. The construction proving
four-label feasibility does not itself prove height-optimal attainment.
Theorem 9.5 uses the complete RC curve and common-decoder rigidity to
prove the different optimal-height threshold and exact counts. The
feasibility count alone supplies neither that threshold nor that proof. $\square$

## 9. Actual-three-label height bounds and strict optimality obstructions

**Theorem 9.1 (universal actual-three-label cap value).** Among every
original implementation of Definition 1.2 with sharp weak cost, required
contrast at least $s_0\tau_3$, and at most three actual low live-bearing
labels, the largest height TV is

$$
T_{3,\rm cap}=T_{\rm flat}-B_++D_+,\qquad
B_+=\frac{g_0+\alpha g_1}{2d}+\frac{g_2}2-\frac{\sqrt\alpha x}{d},
\qquad D_+=\frac{y-\sqrt\alpha z}{\sqrt d},\quad d=1+\alpha.
\tag{RH.73}
$$

This restricted value is attained by the three-label cap frame of
RH.47 with the common completion in Section 5. Its real cap frames and
sign pattern are credited to JR.153; the additional assertion is the
universal actual-label scope, justified by Lemma 8.2, and the comparison
of both cap orientations. This is not the full value
$\mathcal T(s_0\tau_3)$.

Proof. Theorem 8.3 forces exactly three normalized rank-one contributions,
forming an orthonormal null frame. The contrast requirement at the cap
saturates the unit-null product bound RH.72. One frame vector therefore
has third coordinate zero. Up to overall signs and column permutations,
the exhaustive possibilities are

$$
U_\sigma=\frac{(\sqrt\alpha,\sigma,0)^T}{\sqrt d},\qquad
F_{\sigma,t}=\frac{(1,-\sigma\sqrt\alpha,t\sqrt d)^T}{\sqrt{2d}},
\qquad \sigma,t\in\{+1,-1\}.
\tag{RH.74}
$$

The two vectors $F_{\sigma,\pm1}$ are exactly the two null lines in
$U_\sigma^\perp$. Their dot products and nullity follow by substitution;
there are no other lines because that plane compression of $Q$ is
nonzero traceless. Thus both cap orientations have been included, without
assuming a selected family is exhaustive.

Put $r=\sqrt\alpha$ and

$$
A_\sigma=\frac{\alpha g_0+g_1+2\sigma rx}{d},\qquad
B_\sigma=\frac{g_0+\alpha g_1-2\sigma rx}{2d}+\frac{g_2}2,\qquad
D_\sigma=\frac{y-\sigma rz}{\sqrt d}.
\tag{RH.75}
$$

The three low height differences are $A_\sigma,B_\sigma-D_\sigma,
B_\sigma+D_\sigma$. For an arbitrary actual implementation, separating
its products and later failure only increases the possible absolute sum.
The high and failure contributions are bounded by
$(1-\delta)\Delta A$ and $L_f$ as in Theorem 2.2. This gives the
corresponding universal height upper bound from these three values,
even when an actual label also has later failure mass.

Here are coarse rational comparisons sufficient to select the larger
orientation, using RH.17 only. Terminating decimals in this proof are
exact rationals. We have

$$
\begin{gathered}
.87<\alpha<.88,\quad1.87<d<1.88,\quad .9<r<1,
\quad1.3<\sqrt d<1.4,\\
.001269<g_0<.001270,\quad .0029222<g_1<.00293,
\quad .0016771<g_2<.00168,\\
.002370<x<.002372,\quad .002207<y<.002209,
\quad -.0001017<z<0.
\end{gathered}
\tag{RH.76}
$$

For $\sigma=+$, $A_+>0$, $B_+>-x/d>-.0013$, and

$$
B_+<\frac{.001270+.88(.00293)}{2(1.87)}
+\frac{.00168}2-\frac{.9(.002370)}{1.88}<.0008,
\qquad D_+>\frac{.002207}{1.4}>.0015.
\tag{RH.77}
$$

Thus only $B_+-D_+$ is negative. RH.10 makes the resulting bound
$T_{\rm flat}-B_++D_+>T_{\rm flat}+.0007$.
For $\sigma=-$, the numerator of $A_-$ exceeds
$.87(.001269)+.0029222-2(.002372)>-.000718$, so $A_->-.0004$.
Also

$$
B_->\frac{.001269+.87(.0029222)+2(.9)(.002370)}{3.76}
+\frac{.0016771}2>.0029,
\qquad |D_-|<\frac{.002209+.0001017}{1.3}<.0018.
\tag{RH.78}
$$

Both $B_-\pm D_-$ are positive. That orientation's upper value is
$T_{\rm flat}+[-A_-]_+<T_{\rm flat}+.0004$, strictly smaller.
These are symbolic inequalities on the supplied coarse box, not a new
numerical authentication of the narrow CG enclosures.

The plus frame reports $+$ on $U_+$ and $-$ on its other two vectors,
giving exactly $\tau_3$. The actual instrument of Section 5 has exactly
three low live-bearing labels and attains its live, high and spectral
failure terms simultaneously. Thus the upper bound RH.73 is attained.
Lemma 8.2 makes the preceding upper argument apply to arbitrary complex
Kraus multiplicities and to the stipulated countable/integral scope,
with the finite CP-mass convention of Definition 8.1. $\square$

**Theorem 9.2 (strict common-realization gap at the cap).** In the full
unchanged original class,

$$
\mathcal T(s_0\tau_3)>T_{3,\rm cap}.
\tag{RH.79}
$$

One finite retained-choice instrument witnesses this strict inequality,
with the common complete output, sharp cost, and exact contrast
$s_0\tau_3$. This constructive actual-label statement uses the cap
geometry already present in JR54.4; it does not rediscover that
section's real-atom nonoptimality result.

Proof. Use a small real parameter $z_0$ distinct from $G_{12}=z$, and set

$$
A(z_0)=\frac{\alpha-(1-2\beta)z_0^2}{d},\qquad
B(z_0)=\frac{1-(1+\beta)z_0^2}{d},\qquad
U(z_0)=(\sqrt{A(z_0)},\sqrt{B(z_0)},-z_0)^T,
\qquad \tau(z_0)=2\sqrt{A(z_0)B(z_0)}.
\tag{RH.80}
$$

The completion in RH.46 extends analytically through $z_0=0$ by using
$\beta_0=d\sqrt{AB}\,z_0/(A+B)$ there. Its other denominator contains
$\alpha_0>0$, so remains positive. At zero the frame is

$$
U=\frac{(r,1,0)^T}{\sqrt d},\qquad
f=\frac{(1,-r,-\sqrt d)^T}{\sqrt{2d}},\qquad
w=\frac{(1,-r,\sqrt d)^T}{\sqrt{2d}},\qquad r=\sqrt\alpha.
\tag{RH.81}
$$

Only $f$ has negative $G$ value by RH.77. The signs persist locally,
so its attained height TV is $T_{\rm flat}-\phi(z_0)$, where
$\phi=f^TGf$. At zero, direct products give
$U'=(f-w)/\sqrt2$, $f^TQU=U^TQw=r/\sqrt2$, $f^TQw=\beta$.
Differentiating orthonormality and nullity therefore yields

$$
f'=-U/\sqrt2+\frac r{2\beta}w,\qquad
\dot\phi=-\sqrt2 f^TGU+\frac r\beta f^TGw,
\tag{RH.82}
$$

where the dot is the $z_0$ derivative at zero. Expanding these two
bilinear products gives

$$
2\beta d\dot\phi=
 r[(1-2\beta)g_0+(1+\beta)g_1-dg_2]
 -2(\beta^2+\alpha)x
 +2\beta\sqrt d(ry+z).
\tag{RH.83}
$$

The bracket has positive upper bound
$.76(.001270)+1.13(.00293)-1.87(.00167)$; this also bounds its product
with $0<r<1$, even if the bracket is negative. Since $z<0$, RH.76 and
$.12<\beta<.13$ give the strict rational bound

$$
2\beta d\dot\phi<
.76(.001270)+1.13(.00293)-1.87(.00167)
-2(.87)(.002370)+2(.13)(1.4)(.002209)<-.002.
\tag{RH.84}
$$

Also $0<2\beta d<.5$, so $\dot\phi<-.004$.
The contrast and attained value have expansions

$$
\begin{aligned}
\tau_3-\tau(z_0)
 &=\frac{\alpha(1+\beta)+(1-2\beta)}{d\sqrt\alpha}z_0^2+O(z_0^4),\\
T_3(\tau(z_0))&=T_{3,\rm cap}-\dot\phi z_0+O(z_0^2).
\end{aligned}
\tag{RH.85}
$$

The first coefficient is strictly positive. Fix any sufficiently small
positive rational $z_0$, before receipt of the unknown specimen.
Retain an actual choice between this frame instrument and the
contrast-one endpoint instrument, with frame weight

$$
a_3=\frac{1-\tau_3}{1-\tau(z_0)}\in(0,1).
\tag{RH.86}
$$

The two instruments have the same full complex/reference/labelled-time
output RH.36–39, whole-fibre TP decoders, and the same high effect
RH.42. Definition 5.4 proves normalization and exact affine oriented
contrast $\tau_3$. Its actual height TV is

$$
\begin{aligned}
M(\tau_3)&=a_3 T_3(\tau(z_0))+(1-a_3)T_{\rm end}\\
&=T_{3,\rm cap}-\dot\phi z_0+O(z_0^2)>T_{3,\rm cap},
\end{aligned}
\tag{RH.87}
$$

because $a_3=1+O(z_0^2)$ and $-\dot\phi>0$. This is one common
finite instrument, not the juxtaposition of separately attainable
maxima. A nontrivial mixture uses at most twenty-three total labels and
seven low live-bearing labels; it proves no four-label optimal-height
sufficiency. $\square$

**Theorem 9.3 (actual-label obstruction strictly before the cap).** There
exists $\eta_3>0$ with $\tau_3-\eta_3>\bar\tau$ such that every
height-optimal original implementation at each
$\tau\in(\tau_3-\eta_3,\tau_3]$ has at least four actual low live-bearing
labels. Three such labels do suffice for optimal height on the credited
closed initial interval $[0,\tau_\dagger]$. Thus loss of three-label
optimal-height sufficiency occurs strictly before its feasibility cap.
Theorem 9.5 strengthens this local consequence to the exact unique
actual-label threshold and matching four-label height attainments, using
RC's complete curve.

Proof. The set $\mathcal F$ of orthonormal $Q$-null frames is compact.
Its continuous functions

$$
\gamma(F)=\sum_i|(f_i)_0(f_i)_1|,\qquad
V(F)=\frac{(1-\delta)\Delta A+L_f+\sum_i|f_i^TGf_i|}{2}
\tag{RH.88}
$$

bound every actual-three-label implementation by Lemma 8.2 and the TV
inequalities in Theorem 2.2. Conversely Section 5 realizes each frame
with deterministic reports maximizing $\gamma(F)$, exactly three low
live-bearing labels, and actual TV $V(F)$. Therefore the restricted
maximum is $\max_{\gamma(F)\geq\tau}V(F)$. This compact maximum is used
only for the following obstruction, not as a purported evaluation of
the full residual target.

For any sequence $\tau_n\uparrow\tau_3$, maximizing frames have a
subsequence converging to a frame with $\gamma\geq\tau_3$. Theorem 9.1
bounds its limiting value by $T_{3,\rm cap}$. The cap frame remains
feasible below the cap, so the restricted maxima converge to that value.
Keep the two fixed instruments in Theorem 9.2 and vary their retained
choice weights to produce contrast $\tau$ on $[\tau(z_0),1]$. Their
actual value $M(\tau)$ is affine and continuous, with positive gap at
$\tau_3$. Thus $M(\tau)$ strictly exceeds the restricted maximum
throughout a sufficiently small left neighborhood of the cap.
The exact full-class reduction has finite optimum attainment, so no
height optimizer there has at most three such labels. A positive
nonatomic live-bearing record, if present, already has infinitely many.

Theorem 8.3 proves the lower bound of three labels everywhere. The
spectral frame attains optimal height on $[0,\bar\tau]$ for the
inequality requirement, and Proposition 7.1 extends that actual
three-label sufficiency through $\tau_\dagger$. This proves the
claimed separation of feasibility from optimality. The real-atom
left-neighborhood obstruction is already JR54.4; the present conclusion
requires the actual-label bridge and the strict common realization.
$\square$

**Corollary 9.4 (explicit current-DEV interval lifted to actual labels).**
For every

$$
\tau\in I=[996999/10^6,997001/10^6],
\tag{RH.89}
$$

every height-optimal original implementation needs at least four actual
low live-bearing labels. Three labels remain inequality-feasible there.
The inherited JR56 strict comparison uses a feasible four-real-atom
instrument and gap $>17/5000000$ against every saturated aligned
three-atom candidate. That margin and its source-box enclosures are
credited conditional results, not newly evaluated arithmetic here.

Proof. Suppose an optimal actual implementation had at most three such
labels. Lemma 8.2 gives its orthonormal null frame. Its actual height
TV is at most $V(F)$, while Section 5 attains $V(F)$ with that frame
and contrast at least the same required value. Full optimality forces
equality, giving an optimal three-real-atom representation. This
contradicts JR56.1. This reasoning is essential: atom count alone does
not count actual labels. The supplied JR56 inequalities place
$\bar\tau<\inf I<\sup I<\tau_3$, so the cap instrument is feasible
on $I$ by Theorem 8.3. The four-atom witness in JR56 is a strict feasible
lower value, not the proof of pointwise optimality. Pointwise optimal
four-label attainment on this interval instead follows from RC via
Theorem 9.5. $\square$

**Theorem 9.5 (sharp actual-label minimum at optimal height).** Define
$n_{\rm opt}(s)$ as the minimum number of actual low live-bearing
acquisition labels among instruments attaining RH.6, with its original
contrast inequality and sharp acquired cost. All original complex,
potentially noncovariant optimizers, arbitrary inaccessible Kraus
multiplicities and the stipulated countable/integral scope remain in
this minimization. With $s_\dagger=s_0\tau_\dagger$,

$$
\boxed{\displaystyle
n_{\rm opt}(s)=
\begin{cases}
3,&0\leq s\leq s_\dagger,\\
4,&s_\dagger<s\leq s_0.
\end{cases}}
\tag{RH.89a}
$$

The contact belongs to the three-label branch, and the closed endpoint
$s=s_0$ belongs to the four-label branch. This is an attained minimum
of actual low live-bearing labels. It does not minimize the total
acquisition alphabet or classify complete channels or decoders.

Proof. First consider a sharp-cost original instrument with finitely
many such labels. Lemma 8.2 gives to each label $\alpha$ a real-null
rank-one normalized coefficient matrix
$M_\alpha=f_\alpha f_\alpha^T\ne0$, obtained by summing all its
encoder/live-decoder products and applying $L^{-1}$ on both sides.
Theorem 2.2 gives

$$
\sum_\alpha M_\alpha=I,\qquad
f_\alpha^TQf_\alpha=0.
\tag{RH.89b}
$$

In particular at least three labels are necessary by rank, at every
weak parameter, including $s=0$. Attached later-failure subeffects
are PSD summands of $M$ and kill coordinate $0$, so they contribute
no $01$ winding coordinate. Neither high branches nor failure-only
labels contribute that coordinate. If $r_\alpha\in[-1,1]$ is the
mean binary report of the actual acquisition label, RH.5 therefore
implies, after a single global report reversal if needed,

$$
\tau\leq\mathsf V(F)/s_0
=\left|\sum_\alpha r_\alpha(f_\alpha)_0(f_\alpha)_1\right|
\leq\sum_\alpha|(f_\alpha)_0(f_\alpha)_1|.
\tag{RH.89c}
$$

For an upper-bound construction only, assign each $M_\alpha$ to the
slot with $r=\operatorname{sgn}((f_\alpha)_0(f_\alpha)_1)$ and
$\epsilon=\operatorname{sgn}(f_\alpha^TGf_\alpha)$, choosing either
sign at a zero. Their grouped tuple $X$ is feasible in RH.11 by
RH.89b,c. It changes no competitor and grants no readable refinement.
Splitting the actual record analytically into its supported live,
high and failure pieces, using the triangle inequality and RH.15,
gives the full original height bound

$$
\begin{aligned}
T_{\rm actual}
&\leq\frac{(1-\delta)\Delta A+L_f+
                  \sum_\alpha|f_\alpha^TGf_\alpha|}{2}\\
&=\frac{(1-\delta)\Delta A+L_f+
       \sum_{r,\epsilon}\epsilon\operatorname{tr}(GX_{r,\epsilon})}{2}
\leq\mathcal T(s_0\tau).
\end{aligned}
\tag{RH.89d}
$$

This includes labels which later fail and the entire actually generated
record. No probability is divided by survival. If the original
instrument is height-optimal, both inequalities are equalities; hence
$X$ is an optimizer of the original four-slot problem. This equality
step is required: a necessary real-atom reduction alone would not
identify the actual-label optimum.

For $\tau_\dagger<\tau<1$, choose the unique $0<a<a_\dagger$
with $\tau=\tau(a)$. Proposition 7.5's credited aggregate uniqueness
forces $X=(A_a,0,B_a,C_a)$. The rank-two $A_a$ is supported on
$W_a^\perp$, whose real $Q$-null set consists of exactly the two
distinct lines $q_+,q_-$. Positivity of each summand forces every
label contributing to $A_a$ into that plane. Its two null-line masses
are exactly $w_+,w_->0$ by RH.67d. Therefore at least one actual
label is needed on each line. Likewise the nonzero rank-one $B_a,C_a$
force labels on the lines $n_a,Z_a$. All four lines are distinct.
Lemma 8.2 forbids one actual label, with its one common decoder, from
serving two of them. Thus at least four actual low live-bearing labels
are necessary on this whole open post-contact interval. In particular
an inaccessible Kraus index or a split inside a grouped rank-two slot
cannot be used to reduce this count.

At $\tau=1$ the universal feasibility theorem 8.3 already excludes
three labels since $\tau_3<1$. Alternatively RH.90 forces the four
corner rays, and their Gram fixes a positive $1/4$ coordinate-$0$
mass on each; Lemma 8.2 again requires four actual labels. This
endpoint argument needs no finite optimal dual, which does not exist.

It remains to exhibit matching height-optimal actual instruments.
For $0\leq\tau\leq\bar\tau$, the plateau frame $(v,u,w)$ of
Proposition 3.2 has exactly three low live-bearing labels and contrast
$s_0\bar\tau\geq s_0\tau$. The requirement is an inequality, so
attenuation or extra labels are unnecessary. For
$\bar\tau<\tau\leq\tau_\dagger$, use Theorem 6.1's three-vector
frame and Proposition 7.1, including the contact. For
$\tau_\dagger<\tau\leq1$, use exactly the four nonzero vectors
RH.67f, including their finite endpoint values. Definition 5.1 and
RH.35–43 establish simultaneously total encoder effect $I_5$, whole-
fibre TP decoders, all-complex/passive-reference/separate-five-label
Borel output identities, all twelve original HALF complete-cq errors,
sharp jointly counted acquired cost and the optimal height value.
No channel or additional binary-effect coordinate has been imposed
on the necessity class. These constructions prove the claimed upper
counts and attainment at both closed boundaries.

For countably many labels the same sums converge positively. Under
the specified measurable finite-fibre, measurable-Kraus and integrable
effect/live-Choi extension they are the corresponding integrals;
support and equality hold almost everywhere. In particular a proposed
counterexample with at most three actual labels has at most three
nonzero CP-mass atoms and the finite argument applies to their CP
maps. A positive nonatomic live-bearing component already has
infinitely many actual labels. An unacquired integral variable is
hidden encoder multiplicity with one common decoder and is governed
by Lemma 8.2. No unrestricted disintegration is invoked. The finite
constructions therefore achieve the minimum even in these larger
comparison classes. $\square$

**Corollary 9.6 (contact masses and separation of the two thresholds).**
For a height optimizer at $\tau_\dagger<\tau<1$, its actual low-label
coefficient mass is supported on exactly the four RC contact lines,
possibly subdivided into further actual labels. The total normalized
coefficient Grams on them are, respectively,

$$
w_+q_+q_+^T,\quad w_-q_-q_-^T,\quad B_a,\quad C_a.
\tag{RH.89e}
$$

At contact there are exactly three positive ray masses, and the fourth
exposed line has zero mass. At the endpoint there are the four corner
masses $1/4$. These masses are coefficient moments, not acquisition
probabilities. The two actual-label minima compare as follows:

| Original required contrast | Inequality-feasible minimum | Height-optimal minimum |
| --- | --- | --- |
| $0\leq s\leq s_\dagger$ | $3$ | $3$ |
| $s_\dagger<s\leq s_0\tau_3$ | $3$ | $4$ |
| $s_0\tau_3<s\leq s_0$ | $4$ | $4$ |

Proof. The equality tuple in RH.89d is unique after contact, so its
positive summands lie in the stated supports. In the $A_a$ plane the
two null-line projectors are independent, and RH.67d uniquely fixes
their masses; $B_a,C_a$ are rank one. This argument also holds almost
everywhere for the stated integral class. At contact, unique aggregate
rank one eliminates $q_+$ completely; at the endpoint Proposition
10.1 fixes the four corner weights. The strict ordering
$\bar\tau<\tau_\dagger<\tau_3<1$ follows from Propositions 7.1 and
Theorem 6.1. The table is then exactly Theorems 8.3 and 9.5.
It does not assert common-decoder coarsening permission, native
execution, a minimum total alphabet or uniqueness of full instruments.
$\square$

## 10. Credited endpoint attainment, duality and asymptotic laws

**Proposition 10.1 (endpoint facts used in these bounds).** At $\tau=1$
the normalized primal has a finite attainer with
$J(1)=\operatorname{tr}G-2b_{\rm end}$ and actual original value
$T_{\rm end}$. Its dual infimum equals that value of $J$, but no
finite dual minimizer exists. Interior dual minima are finite and
attained. These are the inherited JR51 endpoint facts, checked here
only to justify their use in the residual bounds.

Proof. The four endpoint vectors of Proposition 6.2 have projectors
summing to $I$ and are $Q$-null. With report $r=\sigma$ their contrast
is one. Conversely, decompose any endpoint feasible slots into real
null atoms $f$. The bound

$$
\sum r f_0f_1\leq\frac12\sum(f_0^2+f_1^2)=1
\tag{RH.90}
$$

must be equality. Every nonzero atom has $f_1=rf_0$, and nullity with
$\beta>0$ gives $f_2^2=f_0^2$. Thus the four endpoint rays are
exhaustive. Their total Gram forces mass $1/4$ on each unscaled
$(1,\sigma,t)$ ray: the total mass and three zero signed cross
moments determine the four weights. Under RH.17 the $G$ values of
$(+,+),(+,-),(-,+)$ are positive and $(-,-)$ equals
$b_{\rm end}<0$. Assigning $\epsilon$ to those signs maximizes the
objective, proving the formula. Section 5 supplies its finite actual
full-output realization; this is not merely a PSD endpoint witness.

For any feasible dual tuple the constraints and weak bound are

$$
Y-\epsilon G-\lambda rC+\nu_{r,\epsilon}Q\succeq0,
\quad\lambda\geq0,
\qquad J(\tau)\leq\operatorname{tr}Y-\lambda\tau.
\tag{RH.91}
$$

For $\tau<1$, let $X^{(0)}_{r,\epsilon}=I/4$ and let $X^{(1)}$
be an endpoint tuple. Mix them with any $\eta\in(\tau,1)$.
Every slot is positive definite, its null trace is zero, and the
contrast is $\eta>\tau$. Finite-dimensional Slater duality therefore
applies to this original inequality, giving equal values and a finite
dual minimizer. On the residual interval a minimizer must have
$\lambda>0$, since $\lambda=0$ bounds the unconstrained spectral
optimum $J_{\rm bar}$, which is strictly larger there. Complementarity
then forces $t(X)=\tau$ at every residual optimum; this is a consequence,
not a prescribed extra constraint in RH.11.

Compactness and nested feasible sets give $J(\tau)\to J(1)$ as
$\tau\uparrow1$: any limiting subsequence of maximizers is endpoint
feasible, and the endpoint tuple is feasible for every preceding
parameter. An interior optimal dual tuple remains endpoint-dual
feasible, since its matrix constraints contain no $\tau$, with
objective $J(\tau)-\lambda(1-\tau)\leq J(\tau)$.
Endpoint weak duality sandwiches the infimum between $J(1)$ and these
converging upper values, proving equality of the endpoint infimum.

Suppose a finite endpoint dual minimizer existed. Complementarity with
the two independent positive atoms $d_{+,t}$ forces
$S_{+,+}=a_0kk^T$, where $k=(1,-1,0)^T$, $a_0\geq0$.
With $\nu_0=\nu_{+,+}$, this gives
$Y=G+\lambda C-\nu_0Q+a_0kk^T$.
The positive atom $(1,-1,1)$ in $S_{-,+}$ gives

$$
(\nu_{-,+}-\nu_0)Q(1,-1,1)^T+(2a_0-\lambda)k=0.
\tag{RH.92}
$$

Its third coordinate and $\beta>0$ give $\nu_{-,+}=\nu_0$,
and then $2a_0=\lambda$. The negative atom $(1,-1,-1)$ in
$S_{-,-}$ cancels these $\lambda$ terms. Its first coordinate gives
$\nu_{-,-}-\nu_0=2(x+y-g_0)$, and the remaining coordinates require

$$
R_1=x-g_1-z+\alpha(x+y-g_0)=0,
\qquad R_2=y-z-g_2+\beta(x+y-g_0)=0.
\tag{RH.93}
$$

Already the coarse rational bounds RH.17 imply
$x+y-g_0>0.00330$, and

$$
\begin{aligned}
R_1&>0.00237-0.00293+0.00010+0.87(0.00330)
       =0.002411>0,\\
R_2&>0.00220+0.00010-0.00168+0.12(0.00330)
       =0.001016>0.
\end{aligned}
\tag{RH.94}
$$

Thus both necessary zero residues are impossible. This proves
nonattainment without relying on a prior verdict or extrapolating
interior Slater attainment. The finite certificates of Section 4 are
not endpoint minimizers. These endpoint-duality arguments alone give no
multiplier-divergence rate. The endpoint laws below are credited to JR55. No native
impossibility follows. $\square$

**Proposition 10.2 (JR55 endpoint laws in the present notation).** Let
$\varepsilon=1-s/s_0=1-\tau$, $\gamma_{\rm ep}=\alpha/\beta$, and
use $R_1,R_2$ from RH.93. Define

$$
\begin{aligned}
b_{++}&=R_1-\gamma_{\rm ep}R_2,&
b_{+-}&=-(1+\gamma_{\rm ep})R_2,\\
b_{-+}&=(1+\gamma_{\rm ep})R_1,&
b_{--}&=-(\gamma_{\rm ep}+2)R_1+(2\gamma_{\rm ep}+1)R_2,\\
\Gamma_{\rm ep}&=\sqrt{\frac18\sum_{\sigma,\eta=\pm1}b_{\sigma\eta}^2}.
\end{aligned}
\tag{RH.95}
$$

JR55 gives $.008<\Gamma_{\rm ep}<.009$ and, for
$0<\varepsilon\leq10^{-8}$,

$$
T_{\rm end}+\Gamma_{\rm ep}\sqrt\varepsilon-15\varepsilon
\leq\mathcal T(s_0(1-\varepsilon))
\leq T_{\rm end}+\Gamma_{\rm ep}\sqrt\varepsilon+11\varepsilon.
\tag{RH.96}
$$

Every optimal multiplier $\lambda_s$ of the normalized contrast obeys

$$
\lambda_s\sqrt\varepsilon\longrightarrow\Gamma_{\rm ep},\qquad
\lambda_s=\Gamma_{\rm ep}/\sqrt\varepsilon+O(\varepsilon^{-1/4}).
\tag{RH.97}
$$

For each optimal real-null decomposition near the endpoint, write its
atoms $\sqrt\pi(1,u,v)^T$, with $\alpha u^2+\beta v^2=1$, and signs
$(\sigma,\eta)$ of $(u,v)$. Its sector weights tend to $1/4$ and

$$
\mathbb E_\pi\left[
\left(\frac{|u|-1}{\sqrt\varepsilon}
      +\frac{b_{\sigma\eta}}{\Gamma_{\rm ep}}\right)^2\right]
\longrightarrow0.
\tag{RH.98}
$$

The expectation is over coefficient weights, not unknown histories.
These are credited JR.155–174 with unchanged normalization: the present
$J(\tau)$ is JR's $j(\tau)$ and $T_{\rm end}$ is its $T_0$.
Theorem 2.2 retains their full original comparison class. The matching
lower family has twelve actual labels, all full-output identities and
sharp cost, and is asymptotically optimal. It is not asserted pointwise
optimal at nonzero $\varepsilon$. Exact report attenuation retains all
old labels and may increase the alphabet to twenty-four. The
contact limit and this asymptotic family alone do not prove pointwise
optimal sufficiency. RC's exact curve, Proposition 7.5 and Theorem 9.5
supply that pointwise four-label attainment throughout the post-contact
interval. The multiplier
in RH.97 is the normalized contrast multiplier, distinct from
$\lambda_{\rm sp}$ and from a physical-$s$ derivative. No narrow
coefficient enclosure or endpoint constant is numerically reauthenticated
here.

## 11. Mathematical credit, conditional completion and native boundaries

**Convention 11.1 (scope and source correspondence).** The independent
companion content is the global all-four-full-PSD certificate RH.20–26,
the arbitrary-multiplicity one-ray-per-actual-label proof RH.68–70,
the actual-label feasibility minimum RH.71–72, the universal restricted
cap value and both-orientation comparison RH.73–78, and the strict
common-realization consequences RH.79–89. The sharp actual-label
height-optimal minimum RH.89a–e combines that common-decoder bridge
with RC's complete value/contact theorem. Its proof includes the
necessary equality step from actual-record TV to an optimal grouped
tuple and matching actual common attainments at every parameter.
These are conditional repository deductions; no worldwide priority or
literature-absence assertion is made. The inherited exact branches,
real-atom transition, gluing and arithmetic comparisons are credited
suppliers, not additional independent increments.

CG supplies the isolated root, coefficient formulas and strict enclosures,
exact ranks, normalization, endpoint witness data, calibration assumptions
and original HALF complete-cq minimax certificate. JR34–40 supplies the
sharp jointly counted acquired worst-history cost and its attainments.
JR41–49 supplies supported sharp-equality rigidity, the four-PSD reduction,
failure spectral readout, evaluated strong regime and full complex/
reference/labelled-Borel realization. JR50–52 supplies the maximal initial
height plateau, spectral frame, strict residual decrease, old chord,
interior dual attainment and endpoint finite primal/equal dual infimum/
no finite dual minimum.

JR53–54 supplies the original residual sign reduction, the exact initial
continuation through its least active certificate zero, grouped uniqueness
before that zero, its three-real-atom cap and pre-cap nonoptimality.
The radical frame here is a reparameterization of that frame.
Proposition 7.2 gives an alternative four-block gauge and sufficient
scalar filters; it supplies no new branch-discovery claim. The optimized
initial curvature RH.64–65 is an explicit corollary of JR54's already
exact branch and constrained Hessian. JR55 supplies RH.95–98, including
the quantitative endpoint remainders, every-optimal-multiplier law and
first-order contacts. JR56 supplies the exhaustive real-atom comparison
on RH.89 and its strict witness margin.

RC58–66 supplies the full selected post-contact algebraic curve, all four
matching original dual blocks, simple first $d_+$ zero, quantitative
$C^1$ gluing, exact positive contact weights, three-to-four real-atom
onset and absence of later interior support/rank transitions. Its entire
nine-coordinate source-box inclusion, independent seven-coordinate box,
polynomial root selection and interval/Bernstein comparisons remain
named conditional antecedents; they are not executed or reauthenticated
here. RH.67a–f states the precise correspondence and matching actual
construction. RC64 retains JR55's endpoint constant and all-multiplier
law, and RC65 retains the all-complex/reference/five-Borel-output and
sharp worst-history acquired-cost scopes. Neither a real-atom count nor
RC's construction alphabet alone establishes a universal actual-label
minimum. Lemma 8.2 and RH.89b–d supply the missing common-decoder and
optimality-equality implications.

CA's exposed real equality face, real-null decomposition and compatible
finite resource constructions, and IR's rank/image compression, spectral
scalar realization and compact-moment mechanism retain their supplied
scopes. Their prescribed complete binary effects or fixed-channel models
are distinct from the free other effect coordinates and all-error-optimizer
necessity in RH.6. The exact supported rigidity and normalized SDP used
here are reused with complete reasoning for their interface; they are
not new full-channel uniqueness or minimax certificates.

RC66 also distinguishes the selected-input all-strength acquired-mass
law, which fixes a complete channel and complete binary effects, from
this worst-history sharp-cost height problem over all original error
optimizers with only a contrast inequality. Its critical-energy response
comparison concerns a complex differential-operator domain and a
same-realization energy coefficient. Neither acquired payload mass,
spectral energy nor a machine-learning error is identified with another
of these objectives. No value, exponent, capacity or control conclusion
transfers between them without a separate proved correspondence.

The underlying support, spectral, Gram, Born, trace-norm, image compression
and Slater mechanisms are mature finite-dimensional mathematics.
The supplied literature attributions are `literature-attested` within
their named scope: Leppäjärvi–Sedlák, *Incompatibility of quantum
instruments*, Definition 8, Remark 3 and Proposition 7, and
Muñoz-Moller–Leppäjärvi–Heinosaari, *Adversarial Information Gain in
Non-ideal Quantum Measurements*, Definition 1 and Proposition 1, concern
finite joint compatibility, dilation and complementary postprocessing.
They grant neither a readable discarded environment nor unrestricted
continuous-outcome disintegration. Sekatski's *The bottleneck dimension
of quantum operations* supplies finite rank/image compression, not the
original state-dependent acquisition cost. Uhlmann's *Roofs and Convexity*,
Proposition 2.2, is an affine-flat decomposition antecedent.
Xia–Wang–Sheu's *S-Lemma with Equality and Its Applications*, Theorem 3,
under the sign-changing nonzero quadratic-constraint hypotheses stated
in JR54, supplies that section's fourth-block completion. The explicit
four matrices here need no additional S-lemma invocation. These general
mechanisms do not replace any source-specific value or actual realization.

The source attributes Kraus-mixing and Born marginal identities to
`UnitaryKrausMixingInvariance` and `FiniteKrausInstrumentBornMarginal`,
finite Choi/Kraus correspondence to `FiniteKrausRepresentation` with
selected Physlib declarations at `6a09b2d1761a0d4430083045a247eb121d8da260`,
and positive-support identities to
`AntidistinguishabilityGram.psd_summand_projection` and its kernel helper.
Its mathlib pin is `db584cd6d46c92f209a44c0f1c829460d327499d`.
These are conditional source references, not newly inspected or compiled
applications. No root, Jacobian, minimax, calibration, library or
literature assertion is reauthenticated by this volume.

**Definition 11.2 (complete conditional value and remaining questions).**
The original RH.6/RH.11 goal is to determine $J(\tau)$, equivalently
$\mathcal T(s_0\tau)$, throughout $\bar\tau<\tau<1$ with
full-class upper bounds and actual common normalized matching
instruments, and to identify the global contacts, grouped ranks and
genuine transitions. JR54 and RC58–66 now supply that complete
conditional value/contact theorem: RH.54 and RH.67c cover the entire
residual interval with no gap. The simple $d_+$ zero is the genuine
three-to-four real-atom onset; its $C^1$ gluing and absence of later
interior transitions are supplied results. The global quadratic bound,
trial frames, chords and endpoint asymptotics remain useful bounds and
corollaries; they are not substitutes for, or discoveries of, that curve.

Theorem 9.5 resolves the additional sharp actual-low-label question
throughout the original weak interval, including transition and endpoint.
It uses all original error optimizers and the contrast inequality with
other effect entries free. The earlier local obstructions do not leave
a second unknown threshold: their exact threshold is $s_\dagger$,
strictly before the feasibility cap $s_0\tau_3$. Grouped rank,
projective real-null atoms, actual low live-bearing labels, hidden Kraus
multiplicity, exact-contrast attenuation counts and total alphabets
remain different notions even where their proved numerical minima
coincide.

Minimum total acquisition alphabet, whole five-mode optimizer uniqueness,
classification of individual original labelled failure-time CP measures
and all native enactment obligations remain separate unresolved
questions. No analytic refinement makes an inaccessible Kraus index
readable, and no contact decomposition grants native execution or
permission. No statement here extends beyond the finite/countable and
explicitly stipulated measurable finite-fibre integrable class.

**Definition 11.3 (unresolved native operation and time bridge).** Native
enactment must supply lawful acquisition on the sole unknown specimen,
calibrated support, D/T/S and image operations, generated classical flags,
coherent retention, controlled whole-fibre TP decoding and permanent
environmental discard under the original permissions. Every future-
accessible input-dependent specimen, controller, memory, environment or
entanglement share must be counted jointly at the same cut. No prior,
hidden history, helper, specimen copy, callback, reset, retry, bypass,
postselection, survival division or recovered discarded environment is
introduced by the conditional mathematics.

Acquisition placement and duration must fit the same original aligned
clock without extra time. The actual FIRST absorbing failure must occur
at elapsed time $t$, with no subsequent positive-carrier action on that
failed branch; terminal live output must occur at time one. All five
original labels, stopped archives, source/epoch identity, controller
updates and permissions retain their original semantics. A CP output
measure, a failure-destined acquired label, a sampled timestamp or an
abstract dilation supplies neither the native event nor its timing,
actuator or permission.

`OriginalControlComposition.OriginalControl` is the supplied finite-
duration, continuity, strict-height-domain, bounded-phase-variation and
absolute-continuity/finite-piecewise-$C^1$ path predicate. Its analytic
helpers and chronological concatenation concern geometric paths, not
constructors of these acquisition and decoding maps. The original
probability-changing noncommuting fields in [Probability/Phase Transport,
Definition 10.1 and Theorem 8.7][PPT] remain in scope; their nonzero
double-wall commutator does not justify an exhaustive Schur/diagonal
restriction and supplies no arbitrary native actuator.

All results are ordinary conditional supplied-operation mathematics.
They assert no Lean/kernel/frozen evidence, numerical reauthentication,
native feasibility, efficiency, impossibility or capacity, resource
migration, generic neural-network or empirical ML theorem, or completion
of the wider programme. The conditional residual value/contact and
actual-low-label minima are given above; the native bridges and the
wider programme remain active.

[RC]: FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[CA]: FIB_NATIVE_COMPLEX_ATOMIC_CONE_AND_OPTIMAL_RESOURCE_FACES.md
[IR]: FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md
[PPT]: AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md

## 追加锚（本行以下为增补区）
