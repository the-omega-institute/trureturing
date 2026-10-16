# Native complete-continuation joint record and payload: height and clock

## 59. The original class and the complete conditional classification

**Convention 59.1 (objects, quantifiers and credited supplies).**
This is a same-topic continuation of [JR], §§29–57, linked by
[the owner's Convention 58.1](FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md#58-the-joint-height-record-and-decoder-clock-continuation).
Throughout, the
isolated point of [CG, Proposition 13.2], its existence/isolation,
nonsingular Jacobian, slack and adjugate ranks, exact normalization and
original minimax identification in CG §§13–17 are inherited conditional
premises. They are not established anew here. All exact TP identities
below apply at that point, rather than at arbitrary points of its
rational source box. These are ordinary conditional mathematical proofs;
they carry no Lean/kernel certification or native-execution conclusion.

The sole input is the normalized reached-cut unknown specimen with
supported coordinates

$$
\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger,\quad
U_{e,n}=\operatorname{diag}(e,n,1),\quad
p_y=(y/128,(64-y)/128,1/2),\quad (a_y)_i=\sqrt{p_{yi}},
\tag{JRH.1}
$$

for all twelve histories $y\in\{5,16,27\}$ and $e,n=\pm1$.
The fixed calibrated isometry $E:\mathbb C^3\to V\subset\mathbb C^5$
embeds them in the original five modes. The ideal live block is still
$EU_{e,n}B_y^{\rm ideal}U_{e,n}^\dagger E^\dagger$, where
$B_y^{\rm ideal}$ is CG.111, and the five separately labelled ideal
failure measures are

$$
w_\ell f_y(t)dt\,P_f,\quad f_y(t)=\frac{6y}{(y+6t)^2},\quad
(\ell,w_\ell)=(0,0),(1,1/4),(2,1/2),(3,1/4),(13,0).
\tag{JRH.2}
$$

Time $t\in[0,1]$ means the original absolute time $6+t$.
The objective $E(\Phi)$ is the maximum over all twelve histories of
HALF the complete cq trace norm, as in CG Definitions 3.1–3.2 and
JR Definition 41.1. It counts live coherences, every labelled Borel
failure measure, singular-time mass, wrong support, abort and all
zero-target sectors. Passive references are arbitrary and inaccessible.
There is one common all-complex CPTP processor, no source prior, helper,
readable history, acceptance division, postselection, copy, reset, retry
or free bypass.

The acquisition is an actual CP instrument $\mathcal E_\alpha$,
with full-output TP conditional decoders $\mathcal R_\alpha$ and
$\sum_\alpha\mathcal E_\alpha^\dagger(I)=I$. Its classical labels,
including report coins, are actually generated and dephased. At the
same cut $d_\alpha$ counts jointly every future-accessible input-bearing
specimen, memory, controller, environment and entanglement share.
All other dilation systems are permanently inaccessible before that
cut. Independent blanks introduced later are allowed. A Kraus index
used in a proof is not a readable record.

Let $F$ be the plus effect of an acquired binary report, let
$\mathsf V(F)=2|\operatorname{Re}F_{01}|/\kappa$, and let
$\mathsf W=\max_{y,e,n}\sum_{d_\alpha\ge3}
\operatorname{tr}\mathcal E_\alpha(E\rho_{y,e,n}E^\dagger)$.
The original cost $\mathsf C(s)$ and height-record optimum
$\mathcal T(s)$ are exactly JR.20 and JR.43, under
$E(\Phi)=E_*$, $\mathsf V(F)\ge s$ and
$\mathsf W=\mathsf C(s)$. Full effects and the forgotten complete
channel are not fixed competitor hypotheses. The height comparison
uses $\Delta=\rho_{27,+,+}-\rho_{5,+,+}$; it does not replace the
twelve-history error or cost maximum.

Necessity statements retain JR Definition 41.1's finite class, its
convergent countable version, and only CG Convention 21.3's expressly
stipulated measurable finite-fibre Kraus fields with integrable effects
and live Choi matrices and full TP decoders almost everywhere. In the
integral case CP encoder densities need not individually be TNI relative
to the reference measure. No arbitrary disintegration or infinite-memory
extension is presumed. All constructions in this continuation are finite.

The exact source dictionary is CA.7–CA.9, equivalently CG.112–CG.116,
CG.134 and JR.2, JR.21–JR.23:

$$
\begin{gathered}
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=a|0\rangle\langle1|+b|1\rangle\langle0|,\quad
S=c|0\rangle\langle2|+d|2\rangle\langle0|,\quad
M=\operatorname{diag}(0,m_1,m_2),\\
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\quad
\kappa=h_0a+h_1b,\quad
\theta=\frac{ab}{h_0h_1},\quad\omega=\frac{cd}{h_0h_2},\\
\delta=\theta+\omega,\quad k=1-\delta,\quad
s_0=\sqrt\delta,\quad v_0=\frac{\omega}{1-\theta},\\
\mathfrak f(v)=\sqrt{v(\theta v+\omega)}+
 \sqrt{(1-v)(1-\theta v-\omega)}.
\end{gathered}
\tag{JRH.3}
$$

All seven amplitudes and $m_1,m_2$ are positive. On $[v_0,1]$,
$\mathfrak f$ decreases strictly from $1$ to $s_0$. Put $v=v_s=1$
for $s\le s_0$, $v=\mathfrak f^{-1}(s)$ otherwise, and
$u=\theta v+\omega$. Reuse the sharp result of JR §§34–40:

$$
\begin{gathered}
A_y=\sum_i h_i^2p_{yi},\quad
B_y=b^2p_{y0}+a^2p_{y1},\quad C_y=d^2p_{y0}+c^2p_{y2},\\
P_y(s)=(1-u)A_y+(1-v)B_y,\qquad
\mathsf C(s)=P_{27}(s).
\end{gathered}
\tag{JRH.4}
$$

Here $B_y$ is a scalar resource expression, distinct from
$B_y^{\rm ideal}$. Set $K_0=D,K_1=T,K_2=S$,
$N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger)$ and

$$
N=\begin{pmatrix}\Delta A&\xi&\eta\\
\xi&\Delta B&\zeta\\\eta&\zeta&\Delta C\end{pmatrix},\quad
\ell(K)=\operatorname{tr}(K^\dagger K\Delta),
\tag{JRH.5}
$$

where $\Delta A=A_{27}-A_5$, and similarly for $B,C$;
$\xi,\eta,\zeta$ are JR.49. In particular
$\Delta A,\Delta B,\Delta C,\xi,\eta>0$ and $\zeta<0$.
For $K=xD+zT+wS$ with real coefficients,
$\ell(K)=\Delta Ax^2+\Delta Bz^2+\Delta Cw^2+
2\xi xz+2\eta xw+2\zeta zw$.

For each actual label let $A_\alpha$ be its supported acquisition
effect, $N_\alpha$ its pulled total canonical-failure effect, and
$\Lambda_\alpha=\mathcal R_\alpha^L\mathcal E_\alpha$ its entire
supported live CP map. Define

$$
Z_{\rm cf}=\sum_{\alpha:\Lambda_\alpha=0}A_\alpha,\qquad
p_{\rm cf}(y,e,n)=\operatorname{tr}(Z_{\rm cf}\rho_{y,e,n}).
\tag{JRH.6}
$$

The sum becomes an integral over this measurable zero-map set in the
stipulated integral model. The condition concerns the whole supported
map at an actual label, not a single hidden product or an unused decoder
direction. Define $\mathfrak P_s$ to consist of finite actual
instruments with $E=E_*$, $\mathsf V\ge s$,
$\mathsf W=\mathsf C(s)$ and terminal live effect
$L_\alpha=(\mathcal R_\alpha^L)^\dagger(I)\succ0$ on the
ENTIRE decoder fibre for every nonzero acquisition branch. Zero
encoder branches are omitted; unused fibre directions are not exempt.
The original free coherent full-$M_5$ completion is allowed.

**Theorem 59.2 (height equality, positive decoders and clock).**
With Convention 59.1, define

$$
\begin{gathered}
d_f=11m_1/64,\quad
z_f=\frac{\sqrt{m_1m_2}}{16}(\sqrt{37}-\sqrt{59})<0,\quad
L_f=\sqrt{d_f^2+4z_f^2},\\
t_f=\frac{-2z_f}{d_f+L_f},\quad
b_-=(0,\sqrt{m_1},t_f\sqrt{m_2})^T,\quad
B_-=\frac{b_-b_-^\dagger}{1+t_f^2},\quad
\gamma_f=\frac{L_f-d_f}{2}>0,\\
v^\dagger=\frac{m_2d^2h_1^2}{m_1b^2h_2^2},\qquad
s^\dagger=\mathfrak f(v^\dagger).
\end{gathered}
\tag{JRH.7}
$$

Every original optimizer with actual height TV $\mathcal T(s)$ has
$Z_{\rm cf}\succeq B_-$ for every $0\le s\le1$; $B_-$ is
nonzero rank one and positive only on its support. For $s\ge s_0$
one has the stronger identity $Z_{\rm cf}=M$. Each history satisfies

$$
p_{\rm cf}(y,e,n)\ge
\frac{\left(n\sqrt{m_1(64-y)/128}+t_f\sqrt{m_2/2}\right)^2}
 {1+t_f^2}>0.
\tag{JRH.8}
$$

In the strong range its exact value is
$m_1(64-y)/128+m_2/2$, with sharp worst value
$59m_1/128+m_2/2$.

The finite positive-decoder class has precisely the following values:

| Original contrast requirement | $\mathfrak P_s$ | Height-TV supremum | Attained |
| --- | --- | --- | --- |
| $0\le s<s_0$ | nonempty | $\mathcal T(s)$ | no |
| $s\in[s_0,1]\setminus\{s^\dagger\}$ | empty | — | — |
| $s=s^\dagger$ | nonempty | $\mathcal T(s^\dagger)-\gamma_f$ | no |

One has $v_0<v^\dagger<1$, so $s_0<s^\dagger<1$. All
nonempty cases have explicit finite approximants with the original
error, contrast inequality and sharp joint cost, complete complex
supported maps, arbitrary passive references, all five separately
labelled Borel measures and a lawful coherent counted complement.
Their decoders admit the conditional same-clock first-absorbing-failure
synthesis of §66. Each member has finite integrated absorption;
the supplied approximating families have diverging activity.

For the declared finite-label finite-dimensional decoder class with
positive absorbing $R_\alpha(t)$, TP controls on not-yet-failed carriers,
$\int_0^1\|R_\alpha(t)\|dt<\infty$, no forced singular or terminal
absorption and no later positive-carrier action, the simultaneous
equalities $E=E_*$, $\mathsf V\ge s$,
$\mathsf W=\mathsf C(s)$, TV $=\mathcal T(s)$ are impossible
for every $s$. Independently of this decoder class, every admitted
original error optimizer has no singular canonical-failure CP mass on
the supported algebra. This concerns all five measures before selecting
any density for a construction. The proof is given in §§60–66.

## 60. Actual spectral equality and the whole-range certain-failure effect

**Theorem 60.1 (actual-label equality obstruction).** The assertions
about $Z_{\rm cf}$ and probabilities in Theorem 59.2 hold for the
whole necessity scope of Convention 59.1.

Proof. Reuse JR Theorem 42.1 at its original hypotheses. On the
supported algebra, every sharp-cost error optimizer satisfies

$$
\Lambda_\Phi=\Lambda_*=D(\cdot)D^\dagger+T(\cdot)T^\dagger+
S(\cdot)S^\dagger,\quad G_f=M,\quad G_o=0,
\quad Q_H=(1-u)D^\dagger D+(1-v)T^\dagger T.
\tag{JRH.9}
$$

Each high branch has zero supported nonlive mass. Every nonzero low
encoder/live-decoder Kraus product is, after removing a common phase,

$$
K=xD+zT+wS,\qquad x,z,w\in\mathbb R,\quad
x^2=\theta z^2+\omega w^2,\quad x\ne0.
\tag{JRH.10}
$$

These are consequences of JR.45–JR.48's vanishing rank/triangle slack,
not assumptions of real or Schur controls. CA Lemma 3.1 excludes a
nonzero rank-one matrix even in the full complex span: if $x\ne0$
the $(1,2)$ minor is $h_1h_2x^2\ne0$; if $x=0$, column $0$
and a nonzero column $1$ or $2$ are independent. Thus every nonzero
low product has rank exactly two. High products and all analytic
refinements remain attached to their actual labels.

On $\operatorname{ran}M$ the height-difference matrix is

$$
\Xi=M^{1/2}\Delta M^{1/2}=
\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix}.
\tag{JRH.11}
$$

Its eigenvalues $\lambda_\pm=(-d_f\pm L_f)/2$ have strict
opposite signs. Unit eigenvectors are
$e_-=(1,t_f)^T/\sqrt{1+t_f^2}$ and
$e_+=(t_f,-1)^T/\sqrt{1+t_f^2}$, in coordinates $(1,2)$.
Put $B_\pm=M^{1/2}e_\pm e_\pm^\dagger M^{1/2}$, embedded
in three coordinates. Then $B_-+B_+=M$ and
$\operatorname{tr}(B_\pm\Delta)=\lambda_\pm$.

Since $\sum_\alpha N_\alpha=M$, write
$N_\alpha=M^{1/2}E_\alpha M^{1/2}$ with $E_\alpha\succeq0$
and $\sum E_\alpha=I_2$. This uses the inverse of $M^{1/2}$ only
on its support. For a positive $E$ set
$a=\lambda_+\langle e_+,Ee_+\rangle$ and
$b=-\lambda_-\langle e_-,Ee_-\rangle$, both nonnegative. Its
trace-norm deficit is exactly

$$
\operatorname{tr}(E|\Xi|)-|\operatorname{tr}(E\Xi)|
=a+b-|a-b|=2\min(a,b)\ge0.
\tag{JRH.12}
$$

Equality requires one diagonal pairing to vanish. Positivity then kills
the entire corresponding row and column: the other spectral line is
the whole support of $E$, unless $E=0$. Consequently

$$
\sum_\alpha|\operatorname{tr}(N_\alpha\Delta)|\le L_f,
\quad\text{with equality exactly when each nonzero }N_\alpha
=q_\alpha B_+\text{ or }q_\alpha B_-,\quad q_\alpha>0.
\tag{JRH.13}
$$

The $q_\alpha$ sum to one on each sign. This proves the full
positive-POVM equality characterization, not only equality for a chosen
spectral measurement. Nonnegative deficits give the same almost-everywhere
conclusion in the admitted integral model.

Choose arbitrary encoder Kraus $C_{\alpha b}$ and live-decoder Kraus
$B_{\alpha a}$. With $K_{\alpha ab}=B_{\alpha a}C_{\alpha b}$,
full TP and $G_o=0$ give

$$
\begin{aligned}
2\operatorname{TV}_{\rm generated}
&=\sum_\alpha\left|\sum_{a,b}\ell(K_{\alpha ab})+
 \operatorname{tr}(N_\alpha\Delta)\right|\\
&\le\sum_{\alpha,a,b}|\ell(K_{\alpha ab})|+
 \sum_\alpha|\operatorname{tr}(N_\alpha\Delta)|\\
&\le U_s+L_f=2\mathcal T(s).
\end{aligned}
\tag{JRH.14}
$$

Here the universal live bound $U_s$ is the six-ray sum in JR.51
for $s\ge s_0$ and $k\Delta A+J_s$ from JR.58–JR.59 for
$s\le s_0$. JR Theorem 43.2, Proposition 44.2 and Theorem 45.1
give finite actual attainment at every $s$. Thus TV $=\mathcal T(s)$
forces equality both in JRH.13 and in every actual-label triangle
inequality in JRH.14. If the chosen height record coarsens the full
generated label, contraction and the same upper bound first force
equality for the full generated label. In a saturated label all nonzero
live-product height differences and its failure difference have the same
sign. This argument never makes $a,b$ into acquired labels.

The source-specific row sign needed here is as follows. Suppose a
nonzero real null $K$ in JRH.10 has
$\operatorname{ran}B_-\subseteq\operatorname{ran}K^\dagger$.
Its right kernel is spanned by

$$
\nu=\left(1,-\frac{bz}{h_1x},-\frac{dw}{h_2x}\right)^T.
\tag{JRH.15}
$$

The first row of $K\nu$ is zero by the null equation, and the last
two rows vanish directly. Orthogonality to $b_-$ is equivalent to

$$
z=-q_fw,\qquad q_f=\frac{dh_1}{bh_2}
 \sqrt{\frac{m_2}{m_1}}\,t_f>0.
\tag{JRH.16}
$$

Here $w\ne0$, since otherwise $z=x=0$. Substitution gives

$$
\begin{aligned}
\frac{\ell(K)}{w^2}
={}&\Delta A(\theta q_f^2+\omega)+\Delta Bq_f^2+\Delta C
 -2\zeta q_f\\
&\quad\pm2(\eta-\xi q_f)\sqrt{\theta q_f^2+\omega}.
\end{aligned}
\tag{JRH.17}
$$

Both signs are strictly positive throughout the conditional source box.
For clarity, the sufficient outward rational bounds derived in §67 are

$$
\begin{gathered}
.49<m_1<.50,\quad .34<m_2<.35,\quad
.58<dh_1/(bh_2)<.60,\quad 0<\theta<.015,\quad0<\omega<.0021,\\
\Delta C>.00167,\quad .0188<\xi<.0191,\quad
.0175<\eta<.0178,\qquad .39<t_f<.42.
\end{gathered}
\tag{JRH.18}
$$

They imply $.18<q_f<.22$,
$\sqrt{\theta q_f^2+\omega}<.054$ and
$0<\eta-\xi q_f<.014416$. Dropping the other positive terms in
JRH.17 gives the strict universal lower bound

$$
\ell(K)/w^2>.00167-.108(.014416)
=.000113072>1/10000.
\tag{JRH.19}
$$

It remains to justify that this row test applies to an entire arbitrary
actual fibre. Suppose $N_\alpha=q_\alpha B_-$, $q_\alpha>0$,
and its supported live map is nonzero. A high fibre cannot have such
failure by JRH.9. A low fibre has some nonzero product
$B_{a_0}C_{b_0}$ of rank two. Thus $d_\alpha=2$,
$C_{b_0}$ is onto, and $B_{a_0}$ is injective. For every other
nonzero encoder Kraus $C_b$, injectivity makes $B_{a_0}C_b\ne0$;
rank-one exclusion makes it rank two, so $C_b$ is onto. For every
nonzero decoder Kraus $B_a$, surjectivity of $C_{b_0}$ makes
$B_aC_{b_0}\ne0$ and rank two, so $B_a$ is injective. Hence
every product of nonzero factors has rank two with
$\ker(B_aC_b)=\ker C_b$.

Let $F_\alpha$ be the decoder's total failure effect. It is nonzero.
For every nonzero $C_b$, the positive operator
$N_b=C_b^\dagger F_\alpha C_b$ is nonzero because $C_b$ is onto.
The positive sum $\sum_bN_b=q_\alpha B_-$ forces each $N_b$ to
have exactly the line $\operatorname{ran}B_-$ as its range.
It annihilates $\ker C_b$, so this line lies in the row space of
every $B_aC_b$. Equations JRH.17–JRH.19 therefore make EVERY
nonzero live product's height difference positive. Their total is
strictly positive, whereas the actual-label failure difference is
$q_\alpha\lambda_-<0$. The label's triangle inequality is strict,
contrary to JRH.14. Thus each negative spectral label has its whole
supported live map zero. Its acquisition effect equals its failure
effect, because $G_o=0$ and the decoder is full TP. Summing these
labels gives $Z_{\rm cf}\succeq B_-$.

For $s\ge s_0$, JR.47 restricts all nonzero low products to the
four real rays $(\sqrt u,\sigma\sqrt v,\tau)$, up to a scalar,
where $\sigma,\tau=\pm1$. Compatibility of $B_+$ with the row
space would instead require

$$
z/w=\frac{dh_1}{bh_2}\sqrt{m_2/m_1}\,t_f^{-1}
>\frac{.58(.82)}{.42}>1.
\tag{JRH.20}
$$

The four rays have $|z/w|=\sqrt v\le1$, so compatibility is
impossible. Applying the same surjective/injective argument to a
positive-spectral failure label excludes any nonzero live product
there, irrespective of its sign. All failure labels are then supported
live-zero. Conversely every supported live-zero label's effect is its
failure effect. Hence $Z_{\rm cf}=B_-+B_+=M$.

Taking the Born pairing of $B_-$ gives JRH.8. Its square never
vanishes: $m_1(64-y)/128\ge .49(37/128)$, whereas
$t_f^2m_2/2<.42^2(.35)/2$, and the former is strictly greater.
The formula covers both $e$ signs and every $n$. In the strong range
pairing $M$ gives the stated exact probabilities, maximized at $y=5$.
These are unconditional actual acquisition probabilities. No weak
minimum-certain-failure claim or additive error gap follows. $\square$

## 61. Full-output domination and finite integrated absorption

**Theorem 61.1 (no singular supported failure at the original error).**
For any admitted original common processor with $E(\Phi)=E_*$,
each of its five canonical-failure CP measures is absolutely continuous
with respect to Lebesgue measure on the supported input algebra, at all
passive-reference amplifications. In particular acquisition-time and
deadline atoms cannot be inserted while preserving $E_*$. This theorem
requires neither sharp acquisition cost nor a chosen simulator density.

Proof. Use the original full-output effects of CG Theorem 14.1, not
just the compressed output of CG.155. At each of the four height-$5$
histories the effect is $U_{e,n}R_5U_{e,n}^\dagger$ on live and
identity on the ENTIRE five-label failure register, including every
time and stopped support. The four height-$27$ effects vanish on all
nonlive sectors. All eight weights are strictly positive. As in CG.157
and Corollary 17.3, equality of the original maximum to the lower
certificate forces each effect to attain its individual HALF full-cq
norm; a slack in one cannot be compensated by another.

Write the Hermitian operator measure of ideal minus actual output as
$H$, and dominate both outputs by a common positive scalar measure
on each classical sector. Since the full difference has trace zero,
its half norm is the total trace of its positive part. For an effect
$0\preceq Q\preceq I$ the deficit is

$$
\tfrac12\|H\|_{1,\rm cq}-\operatorname{tr}(QH)
=\operatorname{tr}((I-Q)H_+)+\operatorname{tr}(QH_-)\ge0.
\tag{JRH.21}
$$

The traces include integration and direct sums. On a failure sector of
a height-$5$ witness $Q=I$, so equality makes $H_-=0$ there.
Equivalently, for every Borel $B\subseteq[0,1]$ and each original
label $\ell$, its actual positive output measure obeys

$$
0\preceq\Phi^f_\ell(B)(E\rho_{5,e,n}E^\dagger)
\preceq w_\ell\left(\int_B f_5(t)dt\right)P_f.
\tag{JRH.22}
$$

This is operator-measure domination of each separately labelled full
output, not an inequality of pooled total failure probabilities.
It also excludes wrong stopped support and the two zero-target labels.
For a Lebesgue-null set $B$ the positive CP effect
$H_\ell(B)=(\Phi^f_\ell(B)\circ\operatorname{Ad}_E)^\dagger(I)$
has zero trace against every $\rho_{5,e,n}$. Their four-sign mean
is $\operatorname{diag}(p_5)\succ0$. Positivity and this faithful
mean give $H_\ell(B)=0$. A CP map with zero effect has zero output
on every positive input, hence on every complex matrix by linearity.
Its passive-reference amplifications are zero as well. Thus there is
no singular part on the supported algebra. Nothing in this proof fixes
the density of the absolutely continuous part for all optimizers.
In particular no common $g(t)$ is a premise. $\square$

**Theorem 61.2 (declared finite-activity obstruction).** In the
finite-label, finite-dimensional decoder class specified in Theorem
59.2, no instrument attains all four conditions
$E=E_*$, $\mathsf V\ge s$, $\mathsf W=\mathsf C(s)$ and
actual height TV $=\mathcal T(s)$, for any $0\le s\le1$.

Proof. In a decoder fibre let $\sigma(t)\succeq0$ be its unnormalized
not-yet-failed state. The declared regularity means its survival trace
is absolutely continuous between TP controls and obeys

$$
p'(t)=-\operatorname{tr}(R_\alpha(t)\sigma(t))
\ge-\|R_\alpha(t)\|p(t),\qquad p(t)=\operatorname{tr}\sigma(t).
\tag{JRH.23}
$$

Hamiltonians and other TP controls contribute zero trace derivative;
instantaneous TP controls preserve $p$. Integrating the differential
inequality, or its integrating-factor form on every piece, gives

$$
p(1)\ge e^{-A_\alpha}p(0),\qquad
A_\alpha=\int_0^1\|R_\alpha(t)\|dt<\infty,\qquad
L_\alpha\succeq e^{-A_\alpha}I\succ0.
\tag{JRH.24}
$$

There is no additional singular or terminal absorption in this class.
Every nonzero acquired state therefore has positive terminal live mass,
so its supported live-zero acquisition effect is zero. This contradicts
Theorem 60.1's $Z_{\rm cf}\succeq B_-\ne0$.

A model with at most one absorbing jump can still have infinite
integrated hazard; finite jump count does not imply JRH.24. Replacing a
failure-destined acquired label by an already executed failure at the
cut or by forced absorption at the deadline instead violates Theorem
61.1's no-atom consequence at $E_*$. The conclusion is restricted to
the declared decoder class, not a classification of native operations.
$\square$

## 62. Entire-fibre positive decoders and the general sharp-cost face

**Theorem 62.1 (strong necessity and sharp certain-failure minima).**
For any original sharp-cost error optimizer at $s\ge s_0$, set

$$
R(v)=\frac{d^2h_1^2}{vb^2h_2^2},\qquad
\overline p_{{\rm cf},y}=\frac14\sum_{e,n}p_{\rm cf}(y,e,n).
\tag{JRH.25}
$$

Without assuming height-TV optimality, one has

$$
\begin{aligned}
\overline p_{{\rm cf},y}&\ge
 \frac{64-y}{128}(m_1-Rm_2)_+
 +\frac12(m_2-m_1/R)_+,\\
\max_{y,e,n}p_{\rm cf}(y,e,n)&\ge
 \frac{59}{128}(m_1-Rm_2)_+
 +\frac12(m_2-m_1/R)_+.
\end{aligned}
\tag{JRH.26}
$$

Finite common instruments attain both bounds simultaneously.
The first is a four-sign mean bound, not the same lower bound at
each individual sign history. If every decoder's entire-fibre live
effect is strictly positive, necessarily $v=v^\dagger$.

Proof. By JRH.9–JRH.10 and JR.47 every nonzero low live product is
a scalar multiple of
$K_{\sigma\tau}=\sqrt uD+\sigma\sqrt vT+\tau S$.
Its kernel is the line through

$$
\nu_{\sigma\tau}=
\left(1,-\frac{\sigma\sqrt v\,b}{\sqrt u\,h_1},
 -\frac{\tau d}{\sqrt u\,h_2}\right)^T.
\tag{JRH.27}
$$

At a low actual label with nonzero live map, the arbitrary multiple-Kraus
argument in §60 makes each nonzero $C_b$ onto and each nonzero $B_a$
injective. Write its pulled failure terms as
$N_b=C_b^\dagger F_\alpha C_b\succeq0$. Every such term is
bounded by the total $M$, so it annihilates $|0\rangle$. It also
annihilates $\ker C_b=\ker(B_aC_b)$. Thus, if nonzero, its
range is the one-dimensional intersection

$$
\operatorname{ran}N_b\subseteq
\mathbb C(0,dh_1,-\sigma\tau\sqrt v\,bh_2)^T,
\quad (N_b)_{11}=R(v)(N_b)_{22}.
\tag{JRH.28}
$$

This holds even if different products in one actual fibre use different
rays: a nonzero term must satisfy each applicable kernel constraint.
No proof-only Kraus index is made readable.

High fibres have no supported failure. All remaining labels are supported
live-zero and their acquisition effect equals their failure effect.
Hence, with $N_{\rm mixed}$ the sum over live-active labels,

$$
M=N_{\rm mixed}+Z_{\rm cf},\quad
\operatorname{diag}N_{\rm mixed}=(0,Rq,q),\quad
0\le q\le\min(m_2,m_1/R).
\tag{JRH.29}
$$

Four-sign averaging removes the off-diagonal entries of $Z_{\rm cf}$.
The resulting lower expression decreases with $q$, giving the first
bound in JRH.26. Its $y=5$ value is a lower bound for the original
maximum and gives the second. At most one of the positive-part terms
is nonzero. In particular the use of $59/128$ does not assert an
individual-sign lower bound.

If $L_\alpha\succ0$ on the entire fibre, a nonzero supported
encoder cannot have zero supported live map: for $X\succeq0$,
$\operatorname{tr}(L_\alpha X)=0$ implies $X=0$. Thus
$Z_{\rm cf}=0$. Summing JRH.28 then requires $m_1=Rm_2$,
equivalently $v=v^\dagger$. Section 63 gives attaining instruments.
$\square$

**Theorem 62.2 (a row-space factor used by the finite constructions).**
The constructions in §63, §64 and §65 are legal on entire decoder
fibres, including unused input directions.

Proof. The common factorization step is elementary positive-operator
algebra, used here inside the construction. Let $K:\mathbb C^3\to
\mathbb C^3$ have rank $r$, let $N\succeq0$ satisfy
$\ker K\subseteq\ker N$, and choose an isometry
$J:\mathbb C^r\to\operatorname{ran}K^\dagger$. Put

$$
\begin{gathered}
Q=J^\dagger(K^\dagger K+N)J,\quad C=Q^{1/2}J^\dagger,\quad
B=KJQ^{-1/2},\quad F=Q^{-1/2}J^\dagger NJQ^{-1/2}.\\
BC=K,\quad C^\dagger FC=N,\quad
B^\dagger B+F=I_r,\qquad B^\dagger B\succ0.
\end{gathered}
\tag{JRH.30}
$$

Indeed $K^\dagger K$ is strictly positive on its row space, so
$Q\succ0$. With $P_K=JJ^\dagger$ the kernel condition gives
$KP_K=K$ and $P_KNP_K=N$. Multiplication proves the first two
identities. The live effect is
$Q^{-1/2}J^\dagger K^\dagger KJQ^{-1/2}\succ0$ and its sum
with $F$ is $I_r$. Consequently $0\preceq F\prec I_r$ on the
whole fibre, not only on reached states. When $N=0$ this is the
usual fixed-image compression with a TP isometric live decoder.

Use encoder $A\mapsto CAC^\dagger$ and live decoder
$X\mapsto EBXB^\dagger E^\dagger$.
For clarity, its five failure measures, for every Borel set $\mathcal B$,
are

$$
\mathcal R^f_\ell(\mathcal B)(X)=
w_\ell\left(\int_{\mathcal B}g(t)dt\right)
 \operatorname{tr}(FX)P_f,\qquad
g(t)=\frac2{(1+t)^2},\quad G(t)=\frac{2t}{1+t}.
\tag{JRH.31}
$$

Their integral effect is $F$, since $G(1)=1$ and $\sum w_\ell=1$;
thus the entire decoder is TP. The weights in JRH.2 are kept separately.
For any passive reference and joint complex input $X$, the failure
reference factor is exactly

$$
P_f\otimes\operatorname{Tr}_{\mathbb C^r}[(F\otimes I_R)X]
=P_f\otimes\operatorname{Tr}_{\mathbb C^r}
 [(\sqrt F\otimes I_R)X(\sqrt F\otimes I_R)].
\tag{JRH.32}
$$

The second form proves complete positivity; the identity follows from
cyclicity of the partial trace on the traced factor. Multiplying by
the separate scalar weights and Borel integrals gives the complete
amplified measures. The pullback is exactly $N$ by JRH.30. Thus
$\sum K_\alpha(\cdot)K_\alpha^\dagger=\Lambda_*$ and
$\sum N_\alpha=M$ prove all complex supported map identities,
all references and every Borel set at once. They are stronger than a
fit on the twelve states. Total encoder effect is $I_3$ at the
conditional root; each individual positive effect is then at most $I_3$,
so every branch is TNI. $\square$

## 63. Finite feasibility, sharp masses and a coherent five-mode completion

**Theorem 63.1 (strong finite instruments).** For every $s\ge s_0$
the lower bounds in Theorem 62.1 are sharp. At $s=s^\dagger$ they
give an instrument in $\mathfrak P_s$.

Proof. Reuse JR.34's rank-three and rank-two live matrices

$$
H_\sigma=\frac{\sqrt{1-u}D+\sigma\sqrt{1-v}T}{\sqrt2},\qquad
L_{\sigma\tau}=\frac{\sqrt uD+\sigma\sqrt vT+\tau S}{2}.
\tag{JRH.33}
$$

Their coefficient Grams sum to $I_3$. Their ranks, including both
endpoints, are JR.37: the high determinant has strictly positive
factor $(1-u)-\theta(1-v)=k$, and the low $(1,2)$ minor is
$uh_1h_2/4>0$. Set

$$
\begin{gathered}
\widetilde m_1=\min(m_1,Rm_2),\quad
\widetilde m_2=\min(m_2,m_1/R),\quad
\widetilde m_1=R\widetilde m_2,\\
b_{\sigma\tau}=(0,\sqrt{\widetilde m_1},
 -\sigma\tau\sqrt{\widetilde m_2})^T,\quad
N_{\sigma\tau}=b_{\sigma\tau}b_{\sigma\tau}^\dagger/4.
\end{gathered}
\tag{JRH.34}
$$

One has $N_{\sigma\tau}\nu_{\sigma\tau}=0$. Apply JRH.30 to
$(L_{\sigma\tau},N_{\sigma\tau})$ into dimension two; use $H_\sigma$
as a dimension-three encoder with pure live TP decoder. All these
actual branches report $r=\sigma$. For every nonzero remainder
$m_j-\widetilde m_j$, add scalar rows
$\sqrt{(m_j-\widetilde m_j)/2}\langle j|$, one for each
fair report $r=\pm1$, with full-failure TP decoder JRH.31 for $F=1$.
Zero rows are omitted. The scalar rows are needed only for the general
sharp-face bound; they are absent at $v=v^\dagger$.

The mixed failure effects sum to
$\operatorname{diag}(0,\widetilde m_1,\widetilde m_2)$, so
$\sum N_\alpha=M$ and the residual actual certain-failure effect is

$$
Z_{\rm cf}=\operatorname{diag}(0,m_1-\widetilde m_1,
 m_2-\widetilde m_2).
\tag{JRH.35}
$$

No other branch has zero live map. The diagonal formula attains each
four-sign mean and the worst-history bound in JRH.26. Failure effects
attached to report $\sigma=+1$ sum to half their total, since the
$\sigma\tau$ terms cancel on summing $\tau$. The residual fair
rows contribute half their effect. Expanding the live signed effect
therefore gives

$$
F_+=\frac{I_3}{2}+\frac{\kappa\mathfrak f(v)}2X_{01},\quad
X_{01}=|0\rangle\langle1|+|1\rangle\langle0|,\quad
Q_H=(1-u)D^\dagger D+(1-v)T^\dagger T.
\tag{JRH.36}
$$

Thus $\mathsf V=s$ and each history has high probability $P_y(s)$,
with maximum $\mathsf C(s)$. At $v^\dagger$, $\widetilde M=M$
and the only failure-bearing branches have strictly positive whole-fibre
live effect by JRH.30. Section 67 proves $v_0<v^\dagger<1$,
so this is an interior strong point. $\square$

**Theorem 63.2 (weak finite positive decoders).** For every
$0\le s<s_0$ there is a finite instrument in $\mathfrak P_s$.

Proof. Choose

$$
\varepsilon=\frac{1-s/s_0}{2}>0,\qquad
s_{\rm raw}=(1-\varepsilon)s_0+\varepsilon\sqrt\theta,\qquad
\eta_s=s/s_{\rm raw}<1.
\tag{JRH.37}
$$

Indeed $s_{\rm raw}-s=\varepsilon(s_0+\sqrt\theta)>0$.
Supply the following pairs of live matrices and attached failure
effects, all with fixed input-independent coefficients:

$$
\begin{array}{c|c}
K&N_K\\ \hline
\sqrt kD&0\\
A_\sigma=\sqrt{\varepsilon/2}(\sqrt\theta D+\sigma T)
 &m_2|2\rangle\langle2|/2\\
B_\tau=\sqrt{\varepsilon/2}(\sqrt\omega D+\tau S)
 &m_1|1\rangle\langle1|/2\\
C_{\sigma\tau}=\sqrt{1-\varepsilon}
 (\sqrt\delta D+\sigma T+\tau S)/2&0
\end{array}
\tag{JRH.38}
$$

Every nonzero low matrix is null and rank two. The row space of
$A_\sigma$ contains $|2\rangle$, and that of $B_\tau$ contains
$|1\rangle$; consequently each pair satisfies JRH.30's kernel
condition. Use that factor for all low pairs and the pure live
dimension-three encoder $\sqrt kD$ for the high branch.
The coefficient Grams sum to
$\operatorname{diag}(k,0,0)+
\varepsilon\operatorname{diag}(\theta,1,0)+
\varepsilon\operatorname{diag}(\omega,0,1)+
(1-\varepsilon)\operatorname{diag}(\delta,1,1)=I_3$.
The attached effects sum to $M$. Thus the total encoder is TP and
the forgotten supported maps are exactly $\Lambda_*$ and JRH.31
pulled back with $M$.

On $A_\sigma,C_{\sigma\tau}$ generate report $r$ with probability
$(1+r\eta_s\sigma)/2$; on $B_\tau$ and the high branch use a
fair coin. Keep both the branch and report as the actual label.
The failure signed effects vanish. Summing the live signed effects
gives $\eta_s[\varepsilon\sqrt\theta+(1-\varepsilon)s_0]
\kappa X_{01}$, so $F_+=I_3/2+\kappa sX_{01}/2$.
The only high effect is $kD^\dagger D$, giving cost $kA_{27}$,
exactly the original plateau cost. The two mixed decoder live effects
have eigenvalues $1$ and, respectively,

$$
\ell_A=\frac{\varepsilon\theta h_2^2}
 {\varepsilon\theta h_2^2+m_2}>0,\qquad
\ell_B=\frac{\varepsilon\omega h_1^2}
 {\varepsilon\omega h_1^2+m_1}>0.
\tag{JRH.39}
$$

These follow because the attached failure direction is the separate
one-dimensional row block of the corresponding live matrix. All other
decoders are pure live. This includes $s=0$, with fair binary report.
The $s=s_0$ exclusion follows from Theorem 62.1 and $v^\dagger<1$,
not from a limit of JRH.39. $\square$

**Theorem 63.3 (full completion and the individual twelve-history laws).**
The finite constructions of this continuation extend to a lawful common
all-complex five-mode CPTP map with a coherent, counted complementary
qubit. Their supported complete output is the original approximate
channel, with error $E_*$; it is not the ideal target itself.

Proof. Put $P=EE^\dagger$, $Q_5=I_5-P$, and choose fixed
isometries $W:\mathbb C^2\to V^\perp$ and
$J_0:\mathbb C^2\to\mathbb C^3$. Precompose each supported
encoder with $E^\dagger$. Add one dimension-two encoder
$A\mapsto W^\dagger AW$ with pure live decoder by $EJ_0$,
and a generated fair report. Its full complementary qubit is retained
coherently. The forgotten complete channel is explicitly

$$
\begin{aligned}
\Phi_{\rm new}^L(A)&=E[\Lambda_*(E^\dagger AE)+
 J_0W^\dagger AWJ_0^\dagger]E^\dagger,\\
\Phi_{{\rm new},\ell}^f(\mathcal B)(A)&=
w_\ell\left(\int_{\mathcal B}g(t)dt\right)
 \operatorname{tr}(ME^\dagger AE)P_f.
\end{aligned}
\tag{JRH.40}
$$

These are CP compressions/Kraus maps and positive trace functionals.
Their total effect is $P+Q_5=I_5$. They kill cross-support blocks
and preserve arbitrary complex operators within the complement through
an isometry. The terminal live effect is
$E(I_3-M)E^\dagger+Q_5\succ0$. The complementary branch has
zero probability on every original history, but is still a real,
counted dimension-two branch with a TP decoder on its entire domain.
It is neither reset nor an uncounted bypass.

JRH.40 agrees with CG.135 on every supported complex matrix unit.
JRH.32 gives its exact passive-reference failure factors, with the
corresponding Kraus conjugations for live output. Integrating the
explicit density proves every Borel identity, including the absence
of singular mass and separate zero labels $0,13$. Common fixed metadata
are preserved. Thus the twelve original HALF complete-cq errors are
exactly those of the credited channel, including height $16$.
Only the high fibres in the specified supported constructions count
dimension at least three; any extra accessible correlated share would
change this cost statement.

For explicit individual probabilities write $\psi=U_{e,n}a_y$ and
for real $K=xD+zT+wS$ define

$$
\begin{aligned}
\mathsf p_K(y,e,n)=\|K\psi\|^2
={}&x^2A_y+z^2B_y+w^2C_y
 +2xz\kappa en\sqrt{p_{y0}p_{y1}}\\
&+2xw(h_0c+h_2d)e\sqrt{p_{y0}p_{y2}}
 +2zwacn\sqrt{p_{y1}p_{y2}}.
\end{aligned}
\tag{JRH.41}
$$

A pair $(K,N)$ in JRH.30 has unnormalized encoder mass
$\mathsf p_K+\langle\psi,N\psi\rangle$; a generated report coin
multiplies it by its stated conditional probability, without dividing
by any live or acceptance mass. In Theorem 63.1 these masses are

$$
\begin{aligned}
p(H,\sigma)&=P_y(s)/2+
 \sigma\sqrt{(1-u)(1-v)}\kappa en\sqrt{p_{y0}p_{y1}},\\
p(L,\sigma,\tau)&=\mathsf p_{L_{\sigma\tau}}+
 \tfrac14(n\sqrt{\widetilde m_1p_{y1}}-
 \sigma\tau\sqrt{\widetilde m_2p_{y2}})^2,\\
p(f,j,r)&=(m_j-\widetilde m_j)p_{yj}/2,\qquad
p(\perp,r)=0,\\
\Pr(r=+)&=\tfrac12+\kappa s\,en\sqrt{y(64-y)}/128.
\end{aligned}
\tag{JRH.42}
$$

In Theorem 63.2 the pre-coin masses are $kA_y$,
$\mathsf p_{A_\sigma}+m_2/4$,
$\mathsf p_{B_\tau}+m_1(64-y)/256$ and
$\mathsf p_{C_{\sigma\tau}}$, with exactly the coins in its proof.
These formulas specify every $y,e,n$, and high probability is $kA_y$.
Zero-probability coin refinements are omitted.

The distinction from CA.10 is essential. If instead that full completion
were fixed, every nonzero complementary input would have zero live
probability. For an arbitrary TP acquisition with $L_\alpha\succ0$
on all entire fibres, its nonzero acquired mass would have strictly
positive total live probability $\sum_\alpha
\operatorname{tr}(L_\alpha\mathcal E_\alpha(\rho))$. This is a
contradiction. Thus the separately fixed CA.10 problem has no such
all-positive-decoder factorization for ANY $s$. The original JR class
does not impose that completion. $\square$

## 64. The weak-range supremum with finite positive decoders

**Theorem 64.1 (every weak value is an unattained supremum).** For
every $0\le s<s_0$, $\sup_{\mathfrak P_s}\operatorname{TV}=
\mathcal T(s)$ and this supremum is not attained. The approximants
below do not require an evaluated residual curve or a contact/rank
classification beyond the finite compact problem in JR Theorem 45.1.

Proof. Write
$L_0=\operatorname{diag}(\delta,1,1)$,
$Q_0=\operatorname{diag}(1,-\theta,-\omega)$ and
$\mathcal G=L_0^{1/2}NL_0^{1/2}$. Choose two fixed compatible
null directions using the spectral vectors from §60:

$$
\begin{gathered}
r_\pm=\frac{dh_1}{bh_2}\sqrt{\frac{m_2}{m_1}}
 \frac{(e_\pm)_2}{(e_\pm)_1},\qquad
c_\pm=(\sqrt{\theta r_\pm^2+\omega},-r_\pm,1)^T,\\
a_0=\frac1{4\sum_{\pm}c_\pm^TL_0^{-1}c_\pm},\qquad
R_0=L_0-a_0(c_+c_+^T+c_-c_-^T).
\end{gathered}
\tag{JRH.43}
$$

The coordinate subscripts of $e_\pm$ are the physical supported
coordinates $1,2$. Both denominators $(e_\pm)_1$ are nonzero.
For $v_\pm=L_0^{-1/2}c_\pm$, the norm of
$a_0\sum v_\pm v_\pm^T$ is at most
$a_0\sum\|v_\pm\|^2=1/4$. Therefore
$R_0\succeq(3/4)L_0\succ0$.
Every removed direction is $Q_0$-null, as is $L_0$ in trace, so
$\operatorname{tr}(Q_0R_0)=0$. Reuse IR Lemma 10.1, or JR.60's
support-restricted zero-Rayleigh construction, to decompose
$R_0=\sum_{j=1}^3d_jd_j^T$ with real null $d_j$.
The construction is finite and explicit: diagonalize
$R_0^{1/2}Q_0R_0^{1/2}$ on its support, choose a zero-Rayleigh unit
vector between one positive and one negative eigenvector using IR.58,
compress to its orthogonal complement and repeat. Zero compression
permits any orthonormal basis. Multiplication by $R_0^{1/2}$ gives
the required $d_j$. All nonzero null vectors give rank-two live matrices.

This supplies a fixed auxiliary decomposition of $L_0$ with live
matrices $K_\pm=K(\sqrt{a_0}c_\pm)$ and $K_j=K(d_j)$.
By the kernel computation JRH.15, $\operatorname{ran}B_\pm$
lies in the row space of $K_\pm$ respectively. This decomposition
and both compatible row spaces are fixed independently of the input
and of the subsequent approximation parameter.

For the main decomposition at $s'<s_0$, use exactly the compact
four-PSD problem of JR.58:

$$
\begin{gathered}
Z_{r,\epsilon}\succeq0,\quad Z_{r,\epsilon}\in\operatorname{Sym}_3(\mathbb R),
\quad\operatorname{tr}(Q_0Z_{r,\epsilon})=0,\\
\sum_{r,\epsilon}Z_{r,\epsilon}=L_0,\qquad
\sum_{r,\epsilon}r(Z_{r,\epsilon})_{01}\ge s',\qquad
J_{s'}=\max\sum_{r,\epsilon}\epsilon\operatorname{tr}(NZ_{r,\epsilon}).
\end{gathered}
\tag{JRH.44}
$$

Choose any maximizing tuple; compactness and finite realization are
JR Theorem 45.1. Apply the stated zero-Rayleigh procedure on each
matrix's support. It gives at most twelve low matrices $K_i^{[s']}$,
each with its actual report $r_i$, total coefficient Gram $L_0$,
contrast at least $s'$ and total absolute low height difference
$J_{s'}$. Equality of that last sum follows from JR.59's universal
upper bound and actual finite realization; a strict excess would
violate the same bound. Thus this is an exact finite-matrix prescription
even where the value of the residual curve is left implicit.

Fix $s<s_0$ and choose $0<\varepsilon<1-s/s_0$, with
$s'=s/(1-\varepsilon)<s_0$. An explicit sequence is
$\varepsilon_j=(1-s/s_0)/(2j)$, $j=1,2,\ldots$. Keep the
high live matrix $\sqrt kD$ and a fair report. Use main low
matrices $\sqrt{1-\varepsilon}K_i^{[s']}$ with pure live
decoders and their original reports. Use auxiliary low matrices
$\sqrt\varepsilon K_\pm$, with the ENTIRE effects $B_\pm$
attached respectively, and $\sqrt\varepsilon K_j$ with no
failure. Give all auxiliary branches fair generated reports.
Use JRH.30 for each pair and the coherent completion JRH.40.

The total low Gram is $(1-\varepsilon)L_0+\varepsilon L_0=L_0$;
failure is exactly $B_-+B_+=M$. Thus the complete supported channel
and all five measures are unchanged. The high effect stays
$kD^\dagger D$, and the signed contrast is at least
$(1-\varepsilon)s'=s$. There are finitely many actual labels;
each low fibre is two-dimensional and has whole-fibre positive live
effect by JRH.30. The two failure-bearing directions remain nonzero
for each $\varepsilon>0$.

Before fair coins, the individual history probabilities are

$$
\begin{array}{c|c}
\text{actual branch}&\text{probability on }\rho_{y,e,n}\\ \hline
H&kA_y\\
\text{main }i&(1-\varepsilon)\mathsf p_{K_i^{[s']}}(y,e,n)\\
\text{auxiliary }\pm&\varepsilon\mathsf p_{K_\pm}(y,e,n)
 +\langle\psi,B_\pm\psi\rangle\\
\text{auxiliary }j&\varepsilon\mathsf p_{K_j}(y,e,n)\\
\perp&0
\end{array}
\tag{JRH.45}
$$

Each fair report halves its branch probability; every main report keeps
its own prescribed value. JRH.41 and the explicit spectral vectors
give exact probabilities for every one of the twelve histories.

For any decomposition $L_0=\sum c_ic_i^T$, the normalized frame
$v_i=L_0^{-1/2}c_i$ satisfies $\sum v_iv_i^T=I$. Hence

$$
\sum_i|c_i^TNc_i|=\sum_i|v_i^T\mathcal Gv_i|
\le\sum_i v_i^T|\mathcal G|v_i=\|\mathcal G\|_1.
\tag{JRH.46}
$$

Let $J_{s'}$ be the main sum and $U_{\rm aux}$ the auxiliary
sum; both are bounded by $\|\mathcal G\|_1$. The reverse triangle
inequality for each attached spectral branch gives

$$
\begin{aligned}
2\operatorname{TV}_\varepsilon
&\ge k\Delta A+(1-\varepsilon)J_{s'}+L_f
 -\varepsilon U_{\rm aux},\\
\mathcal T(s')-\varepsilon\|\mathcal G\|_1
&\le\operatorname{TV}_\varepsilon\le\mathcal T(s).
\end{aligned}
\tag{JRH.47}
$$

This counts all generated labels, including the fair report splits.
It makes no claim that the approximants themselves use optimal spectral
readout as actual failure-only labels.

For completeness, $\mathcal T$ is right continuous at each $s<s_0$
directly from JRH.44. Mix a maximizing tuple at $s$ with any feasible
tuple at $s_0$ in proportion
$\alpha=(s'-s)/(s_0-s)$. The mixture is feasible at $s'$ and its
linear objective tends to $J_s$. Monotonicity of the constraint gives
$J_{s'}\le J_s$, so $J_{s'}\to J_s$. JR.59 transfers this to
$\mathcal T$. Therefore JRH.47 tends to $\mathcal T(s)$.
Theorem 60.1 excludes attainment in $\mathfrak P_s$, since positive
entire-fibre decoders force $Z_{\rm cf}=0$. This proves the exact
unattained weak supremum, without any later-curve formula. $\square$

## 65. The isolated positive-decoder point and its exact TV deficit

**Theorem 65.1 (strict bound and exact exceptional supremum).**
At $s=s^\dagger$, every member of $\mathfrak P_s$ satisfies
$\operatorname{TV}<\mathcal T(s^\dagger)-\gamma_f$.
There is a finite sequence in $\mathfrak P_s$ approaching this bound.

Proof. At this point $R=m_1/m_2$. By JRH.28 every nonzero
pulled failure Kraus term at a live-active low label is a positive
multiple of the outer product of

$$
b_{\sigma\tau}=(0,\sqrt{m_1},-\sigma\tau\sqrt{m_2})^T.
\tag{JRH.48}
$$

There are no supported live-zero labels in $\mathfrak P_s$ and no
high failure. The height pairing of this outer product is
$-d_f-2\sigma\tau z_f$, strictly negative for both signs, because
$d_f>2|z_f|$ throughout the source box (§67). Thus every nonzero
actual failure effect has negative height pairing, even if it combines
multiple encoder Kraus terms. Their absolute sum is exactly
$-\operatorname{tr}(M\Delta)=d_f$ instead of $L_f$.

Both signs of $\sigma\tau$ must occur with nonzero pulled failure
mass: all terms are supported in coordinates $(1,2)$, and the two
families in JRH.48 have opposite, nonzero off-diagonal entries. A sum
using only one sign cannot equal the diagonal matrix $M$.
In particular some failure-bearing actual label has a term of type
$\sigma\tau=-1$. Its encoder is onto and the decoder has nonzero
live products by entire-fibre positivity. The same injective/surjective
argument as in §60 gives at least one live product on the compatible
ray of that sign. Both live rays $\ell_{-,+}$ and $\ell_{+,-}$
are strictly positive throughout $v\in[v_0,1]$, by JR Theorem 43.2's
interval-wide sign proof, expanded in §67. That label therefore contains
a strictly positive live difference and a strictly negative failure
difference. Even if it contains further products of either sign,
the triangle inequality on the full list of products and failure is
strict. Using the universal strong live sum $U_s$ yields

$$
2\operatorname{TV}<U_s+d_f
=2\mathcal T(s)-(L_f-d_f).
\tag{JRH.49}
$$

For sharpness retain $H_\sigma$ and $L_{\sigma\tau}$ of JRH.33
at $v^\dagger$. Put $N_{\sigma\tau}=
b_{\sigma\tau}b_{\sigma\tau}^\dagger/4$. Split each low matrix
into two ACTUAL acquired branches:

$$
(\sqrt{1-\varepsilon}L_{\sigma\tau},0),\qquad
(\sqrt\varepsilon L_{\sigma\tau},N_{\sigma\tau}),
\qquad 0<\varepsilon<1.
\tag{JRH.50}
$$

Apply JRH.30 and report $r=\sigma$ on both. All mixed decoders
are positive on the whole fibre; pure branches have isometric live
decoders. The total live map, failure effect and high effect do not
change. The signed failure effect still vanishes, so the binary effect
is exactly $I_3/2+\kappa s^\dagger X_{01}/2$.
The coherent complement is JRH.40. On every original history the
pure-low probability is $(1-\varepsilon)\mathsf p_{L_{\sigma\tau}}$,
and the mixed-low probability is

$$
\varepsilon\mathsf p_{L_{\sigma\tau}}(y,e,n)+
\tfrac14(n\sqrt{m_1(64-y)/128}-\sigma\tau\sqrt{m_2/2})^2.
\tag{JRH.51}
$$

The high and binary probabilities are JRH.42 with $s=s^\dagger$;
there are no scalar failure rows.

Write $\ell_{\sigma\tau}=\ell(L_{\sigma\tau})$ and
$n_{\sigma\tau}=\operatorname{tr}(N_{\sigma\tau}\Delta)<0$.
Choose $\varepsilon$ smaller than $1$ and than
$-n_{\sigma\tau}/\ell_{\sigma\tau}$ for every positive
$\ell_{\sigma\tau}$. This is a positive explicit bound over four
fixed numbers. Then each mixed total difference
$\varepsilon\ell_{\sigma\tau}+n_{\sigma\tau}$ is negative.
The low actual absolute-difference sum is

$$
\begin{aligned}
\sum_{\sigma,\tau}\bigl[(1-\varepsilon)|\ell_{\sigma\tau}|
 +|\varepsilon\ell_{\sigma\tau}+n_{\sigma\tau}|\bigr]
&=\sum_{\sigma,\tau}|\ell_{\sigma\tau}|+d_f
 -2\varepsilon\sum_{\sigma,\tau}(\ell_{\sigma\tau})_+.
\end{aligned}
\tag{JRH.52}
$$

Adding the unchanged high sum and dividing by two gives the exact law

$$
\operatorname{TV}_\varepsilon=
\mathcal T(s^\dagger)-\gamma_f
-\varepsilon\sum_{\sigma,\tau}(\ell_{\sigma\tau})_+.
\tag{JRH.53}
$$

It approaches the strict bound. These deficits concern acquired height
TV only; every approximant has exactly the same original error $E_*$.
Neither $\gamma_f$ nor any certain-failure probability is added to that
error. Together with §§62–64, this proves the full table in Theorem
59.2. $\square$

## 66. Conditional first-failure synthesis on the original clock

**Theorem 66.1 (finite activity for each positive finite approximant).**
Every decoder of Theorem 63.1 at $v=v^\dagger$, Theorem 63.2 and
the approximants in §§64–65 has a conditional same-clock realization with the exact
first-failure CP measures of JRH.31, terminal live map from JRH.30,
finite integrated positive absorption and no later positive-carrier
action after failure. This assumes access to the specified encodings,
embeddings, stopped instruments and survivor isometries within the
original aligned clock. It does not supply that access.

Proof. A pure live decoder needs only its specified isometry. Every
nontrivial mixed decoder has rank-one failure effect
$F=f|q\rangle\langle q|$ with $0<f<1$ and
$B^\dagger B=I-F$. This follows from JRH.30 and the rank-one
attached $N$. Define, on its entire fibre,

$$
\begin{gathered}
K(t)=\sqrt{I-G(t)F},\qquad
R(t)=g(t)F(I-G(t)F)^{-1},\\
J_\ell(t)=\sqrt{\frac{w_\ell g(t)f}{1-fG(t)}}
 |f,\ell\rangle\langle q|,\qquad
U=B(I-F)^{-1/2}.
\end{gathered}
\tag{JRH.54}
$$

Use zero Hamiltonian. Since $F$ commutes with its functions,
$K'=-RK/2$ and $K(0)=I$; moreover

$$
\begin{gathered}
\sum_\ell J_\ell(t)^\dagger J_\ell(t)=R(t),\qquad
J_\ell(t)K(t)=\sqrt{w_\ell g(t)f}
 |f,\ell\rangle\langle q|,\\
U^\dagger U=I,\qquad UK(1)=B,\\
K(t)^\dagger K(t)+\sum_\ell\int_0^t
 K(\tau)^\dagger J_\ell(\tau)^\dagger J_\ell(\tau)K(\tau)d\tau=I.
\end{gathered}
\tag{JRH.55}
$$

Thus these are the no-event and actual FIRST-event CP operators, not
a terminal draw of a timestamp. Each label's first-event density is
$w_\ell g(t)\operatorname{tr}(FX)dt\,P_f$ with the reference
factor JRH.32. The exact integration identity proves the instrument
on every Borel set. At the deadline apply $U$ only to survivors;
no terminal failure mass is added. Extend by identity on already
stopped/archive sectors, let every jump vanish there, and stop all
positive-carrier controls at first failure. The rates are bounded for
each $f<1$ and

$$
\|R(t)\|=h_f(t)=\frac{2f}{(1+t)[1+(1-2f)t]},\qquad
\int_0^1h_f(t)dt=-\log(1-f)<\infty.
\tag{JRH.56}
$$

The same elapsed $t$ is translated to absolute $6+t$; no extra
execution interval is introduced by these formulas.

There is also an explicit correspondence with the PARTICULAR canonical
instrument OC.19–OC.19b. At the double-wall base let
$c_{\rm src}=1/4$, $p(k)=(k,c_{\rm src}-k,Z,c_{\rm src}-k,k)$,
keep phases fixed, and take $k'\ge0$. Then its original rates are

$$
\gamma_0=\gamma_{13}=0,\qquad
\gamma_1=\gamma_3=\frac{c_{\rm src}k'}{k(c_{\rm src}-k)},\qquad
\gamma_2=k'/k.
\tag{JRH.57}
$$

Indeed OC.19 has $\lambda=k'/k$ and
$\gamma_i=\lambda-(\log p_i)'$. Put $\ell=1-f>0$ and
$s_f(t)=1-fG(t)\in[\ell,1]$. For selectors $i=1,2,3$ use

$$
k_1(t)=k_3(t)=\frac{c_{\rm src}\ell}{s_f(t)+\ell},\qquad
k_2(t)=\frac{c_{\rm src}\ell}{2s_f(t)}.
\tag{JRH.58}
$$

They are smooth increasing strict-interior paths on $[0,1]$, with
$k_i(1)=c_{\rm src}/2$. Substitute in JRH.57: on the occupied
bad mode $i$, $\gamma_i=-s_f'/s_f=h_f$, and on good mode $0$
the rate is zero. Embed the decoder's good eigenvector into mode $0$
and $q$ into mode $i$ by a fixed calibrated isometry. The restriction
of OC.19's no-event map is exactly
$\operatorname{diag}(1,\sqrt{s_f(t)})$; OC.19b's first-event
map is the corresponding single-mode version of JRH.55. The complete
instrument therefore agrees on ALL complex operators in the occupied
two-dimensional subspace, including its coherences and passive
references, not just its endpoint survival probability.

Generate an input-independent selector $i=1,2,3$ with probabilities
$1/4,1/2,1/4$ and retain it as a classical control flag. Each selected
branch still has positive terminal live effect. Its actual mode of first
failure is $i$; forgetting only the selector gives exactly the five
weights in JRH.2. No modes $0,13$ acquire failure mass on the
occupied decoder input. The terminal survivor isometry can undo the
chosen embedding before applying $U$. Stopped sectors carry identity,
with no later positive-carrier action.

Even on the complete canonical five-mode carrier the maximum rate is
finite. For $i=1,3$, JRH.57's maximum is $h_f$ and its integral
is $-\log\ell$. For $i=2$ the maximum is
$\gamma_1=\gamma_3=-s_f'/(s_f-\ell/2)$ and its integral is
$\log((2-\ell)/\ell)$. Thus the full canonical instrument, not
only its occupied restriction, meets the finite integrated condition.
The selectors, embeddings and rates describe that specified instrument;
they neither classify all controls nor change the original unknown
source ramp $x+6t/256$. These paths satisfy the regularity of
OriginalControl, but geometric path existence does not grant its
actuator calls. $\square$

**Theorem 66.2 (activity of the displayed approximation families).**
For a fixed nonzero attached rank-one $N$ and fixed rank-two $K_0$
with $\ker K_0\subseteq\ker N$, the mixed pair
$(\sqrt\varepsilon K_0,N)$ in JRH.30 has nonzero failure eigenvalue
and direct-synthesis activity

$$
f_\varepsilon=\frac{\nu}{\varepsilon+\nu},\qquad
A_\varepsilon=\log(1+\nu/\varepsilon)\longrightarrow\infty,
\quad \nu>0.
\tag{JRH.59}
$$

Proof. On the row space let $N=nn^\dagger$, $n_r=J^\dagger n$,
$A=J^\dagger K_0^\dagger K_0J\succ0$ and
$\nu=n_r^\dagger A^{-1}n_r>0$. The only nonzero eigenvalue
of $F=(\varepsilon A+n_rn_r^\dagger)^{-1/2}
n_rn_r^\dagger(\varepsilon A+n_rn_r^\dagger)^{-1/2}$ is
$n_r^\dagger(\varepsilon A+n_rn_r^\dagger)^{-1}n_r$.
The rank-one inverse identity, obtained by multiplying
$(\varepsilon A+n_rn_r^\dagger)$ by
$\varepsilon^{-1}A^{-1}-
\varepsilon^{-1}A^{-1}n_rn_r^\dagger A^{-1}/(\varepsilon+\nu)$,
gives exactly $\nu/(\varepsilon+\nu)$. JRH.56 proves JRH.59.
In §64 both auxiliary $K_\pm$ and their attached $B_\pm$ are
fixed, so the corresponding $\nu_\pm$ are fixed positive numbers.
The same holds for all four mixed branches in §65. The maximum of
their direct activities diverges as well. All other branches are pure
live; generating the classical coins and selectors does not remove
this divergence. Each individual approximant is finite, but these
families establish no common finite budget and no exact quantitative
$(s,A)$ frontier. $\square$

## 67. Exact source-box signs and immutable mathematical supplies

**Proposition 67.1 (derived comparisons over the conditional source box).**
The inequalities used in §§59–66 follow from the entire rational
nine-coordinate box of CG Proposition 13.2 with radius $10^{-24}$
and exact source formulas, without fitting parameters or using an
off-root TP identity. In particular

$$
\begin{gathered}
.12534<s_0<.12535,\quad
.24163<v^\dagger<.24165,\quad
.90417<s^\dagger<.90419,\\
v_0<18/677<6/25<v^\dagger<1/4<1,\qquad
d_f>2|z_f|,\quad\gamma_f>0.
\end{gathered}
\tag{JRH.60}
$$

Proof. Use CG.112–CG.116's matrices $A_y^{\rm src}$,
$S_0^{\rm src},S_{01}^{\rm src},S_{02}^{\rm src}$, their
adjugates $H^{\rm src}=1000\eta_0\operatorname{adj}S_0^{\rm src}$,
$Q^{01}=\eta_1\operatorname{adj}S_{01}^{\rm src}$ and
$Q^{02}=\eta_2\operatorname{adj}S_{02}^{\rm src}$. Define the
amplitudes by the positive-pivot first-column formulas CA.8/CG.134.
Their pivot denominators are separated from zero throughout the box.
The mass definitions on this box are
$m_1=1-H^{\rm src}_{11}-Q^{01}_{00}$ and
$m_2=1-H^{\rm src}_{22}-Q^{02}_{00}$. At the conditional root,
rank-one identities additionally identify $H^{\rm src}=hh^T$ and
$Q^{01}=(a,b)^T(a,b)$, $Q^{02}=(c,d)^T(c,d)$.
Useful root identities, consistent with these box definitions, are

$$
\begin{aligned}
b^2&=\eta_1\left[59\lambda/128-
 \{59(A_5^{\rm src})_{00}+37(A_{27}^{\rm src})_{00}\}/128\right],\\
d^2&=\frac{\eta_2}{2}
 [\lambda-(A_5^{\rm src})_{00}-(A_{27}^{\rm src})_{00}].
\end{aligned}
\tag{JRH.61}
$$

They express adjugate diagonal entries at the root. Interval evaluation
of the positive-pivot formulas themselves suffices off root; no exact
rank factorization is asserted on the whole box.

All terminating decimals below mean exact rationals. Direct outward
substitution gives sufficient, deliberately coarse enclosures:

| Quantity | Strict lower bound | Strict upper bound |
| --- | --- | --- |
| $m_1$ | $.496850$ | $.496851$ |
| $m_2$ | $.344473$ | $.344475$ |
| $dh_1/(bh_2)$ | $.590360$ | $.590362$ |
| $\theta$ | $.013789$ | $.013790$ |
| $\omega$ | $.001921$ | $.001922$ |
| $\Delta A$ | $.0807$ | $.0809$ |
| $\Delta B$ | $.00291$ | $.00294$ |
| $\Delta C$ | $.00167$ | $.00169$ |
| $\xi$ | $.0188$ | $.0191$ |
| $\eta$ | $.0175$ | $.0178$ |
| $-\zeta$ | $.000100$ | $.000104$ |
| $t_f$ | $.404699$ | $.404701$ |
| $q_f$ | $.198937$ | $.198938$ |
| $(dh_1/(bh_2))\sqrt{m_2/m_1}/t_f$ | $1.21464$ | $1.21466$ |
| $d_f-2|z_f|$ | $.002738$ | $.002740$ |
| $\gamma_f$ | $.0167257$ | $.0167258$ |

These comparisons can be specified using only rational operations and
integer square roots. At mesh $2^{-256}$, embed each of the nine
rational coordinate intervals outwards. After each sum, product and
quotient round the lower and upper endpoints down and up to this mesh.
For a nonnegative interval with integer scaled endpoints $a,b$, use
$[\lfloor\sqrt{a2^{256}}\rfloor,
\lceil\sqrt{b2^{256}}\rceil]/2^{256}$. Form determinants by
first-row expansion and adjugates by cofactors, then the positive-pivot
amplitudes and the displayed expressions in JRH.3, JRH.5 and JRH.7.
For height differences one can use directly

$$
\begin{gathered}
\Delta A=\frac{22}{128}(h_0^2-h_1^2),\quad
\Delta B=\frac{22}{128}(b^2-a^2),\quad
\Delta C=\frac{22}{128}d^2,\\
\xi=(h_0a+h_1b)\frac{\sqrt{999}-\sqrt{295}}{128},\quad
\eta=(h_0c+h_2d)\frac{\sqrt{27}-\sqrt5}{16},\quad
\zeta=ac\frac{\sqrt{37}-\sqrt{59}}{16}.
\end{gathered}
\tag{JRH.62}
$$

This is a finite rational enclosure specification for the entire box,
not a finite set of sign samples. For the compatible-row formula
JRH.17 the two values enclose respectively in
$(.000656,.000657)$ and $(.003408,.003410)$; the much weaker
analytic bound JRH.19 already suffices. Alternatively the coarse
$t_f$ bound in JRH.18 follows from

$$
\frac{t_f}{1-t_f^2}=\frac4{11}\sqrt{m_2/m_1}
 (\sqrt{59}-\sqrt{37}),
\tag{JRH.63}
$$

since $t/(1-t^2)$ is strictly increasing on $(0,1)$ and direct
rational-square comparisons bracket its right side between its values
at $.39$ and $.42$. The source coarse bounds give
$.82<\sqrt{m_2/m_1}<.85$, and then the $q_f$ and positive-row
ratio estimates used in §60. The strict sign $d_f>2|z_f|$ also
follows already from $d_f>.49(11/64)$ and
$2|z_f|<\sqrt{.50(.35)}(1.6)/8$, using
$\sqrt{59}-\sqrt{37}<1.6$; squaring positive rationals verifies
the gap. Thus no near equality in the table is needed for that sign.

For the strong live-ray signs in §65, reuse the precise finite
comparisons of JR.52, obtained by the same source-box substitution.
Writing $\mathfrak a=\theta\Delta A+\Delta B$ and
$\mathfrak b=\omega\Delta A+\Delta C$, these include

$$
\begin{gathered}
\mathfrak a,\mathfrak b>0,\quad \Delta A/2>\xi,\quad
\mathfrak a<2\sqrt\theta\,\xi,\quad
\mathfrak a+\mathfrak b>2\sqrt\delta\,\xi,\\
\mathfrak a+2\sqrt\theta\,\xi>\theta\eta/\sqrt\omega,\quad
\xi\sqrt\omega>|\zeta|,\quad
\ell_{\sigma\tau}(v_0)>1/25000.
\end{gathered}
\tag{JRH.64}
$$

These finite comparisons imply the required whole-interval signs,
rather than just the signs of finitely many rays at sampled $v$.
Indeed $q(v)=(\mathfrak av+\mathfrak b)^2-
4\xi^2v(\theta v+\omega)$ is strictly concave, with positive
values at $0,1$. Hence
$\mathfrak av+\mathfrak b>2\xi\sqrt{v(\theta v+\omega)}$
throughout $[0,1]$. In the JR.50 formula for $4\ell_{-,+}$,
the remaining terms $2\eta\sqrt{\theta v+\omega}-
2\zeta\sqrt v$ are positive, so $\ell_{-,+}>0$.
For $\ell_{+,-}$ its derivative times four is

$$
\mathfrak a+
\xi\frac{2\theta v+\omega}{\sqrt{v(\theta v+\omega)}}
-\frac{\theta\eta}{\sqrt{\theta v+\omega}}
-\frac{\zeta}{\sqrt v}
>\mathfrak a+2\sqrt\theta\,\xi-
 \theta\eta/\sqrt\omega>0.
\tag{JRH.65}
$$

Its positive value at $v_0$ therefore persists through $1$.
This proves both $\sigma\tau=-1$ signs needed for strict TV loss.
High differences are positive as in JR §43 from $u\le v$,
$1-u\ge1-v$ and $\Delta A/2>\xi$.

Finally the same direct substitution in the exact ratios gives
$6/25<v^\dagger<1/4$ and the tighter enclosures JRH.60;
the inherited coarse bound $v_0<18/677$ places it strictly in the
strong interval. Monotonicity of $\mathfrak f$ locates
$s^\dagger$ without a fitted inverse root. No root-existence,
Jacobian, rank or minimax recertification is part of these derived
comparisons. $\square$

**Convention 67.2 (immutable supplies and mathematical attribution).**
The source links [CG], [JR], [CA], [IR], [OC], [OCC] and [CE] fix the
same immutable snapshot. Their exact uses are as follows.

| Source | Supplied statement and hypothesis boundary |
| --- | --- |
| CG Definitions 3.1–3.2, 13.1; §§13–17; Definitions 21.1–21.2 and Convention 21.3 | Original twelve states, complete HALF cq error, all-complex common input, conditional root/ranks/normalization/minimax, full-output endpoint saturation, and actual finite/countable/stipulated integral scope. |
| JR Definitions 34.1 and 41.1; §§34–40 | Original contrast inequality and sharp worst-history joint acquisition cost, credited in full to those sections. |
| JR Theorem 42.1, JR.44–JR.48 | All-error-optimizer sharp-cost supported rigidity and vanishing high nonlive mass; no full completion or per-label time-law uniqueness. |
| JR Theorem 43.2, Proposition 44.2, Corollary 44.3 | Universal strong live-TV sum, finite actual spectral attainment and the already identified spectral-versus-coordinate gain $(L_f-d_f)/2$. |
| JR Theorem 45.1, JR.58–JR.61 | Compact weak moment maximum, actual finite attainment and support-restricted zero-Rayleigh construction. No evaluation of a later residual branch is imported. |
| CA Definitions 2.1–2.2, CA.7–CA.10; Lemma 3.1; Theorem 5.1 | Exact source dictionary, distinguish fixed completion, complex rank-one exclusion and the exposed real equality face. CA's prescribed full effects are not competitor hypotheses here. |
| IR Lemmas 4.2 and 10.1, IR.57–IR.58 | Fixed-image rank-two realization and real zero-Rayleigh decomposition, used as intermediate supplies. |
| OC §5.2, OC.19–OC.19b; OCC's `concatenate-original` statement | The particular full complex stopped instrument and original path regularity; geometric concatenation supplies no actuator. |

The source-specific implications in Theorems 60.1, 62.1, 63.1–63.3,
64.1 and 65.1, with their conditional decoder correspondence in §66,
are `repo-derived`. Positive spectral deficits, row-space factorization,
zero-Rayleigh decomposition, trace estimates and first-jump calculus are
reused intermediate mathematical mechanisms, not new general theorems
or a claim of worldwide novelty.

For primary-literature scope, Leppäjärvi–Sedlák,
[*Incompatibility of quantum instruments*, arXiv:2212.11225v2](https://arxiv.org/html/2212.11225v2),
§3 and §5.2 Proposition 7, treats finite-dimensional finite-outcome
instruments and compatible postprocessing of complementary instruments.
Muñoz-Moller–Leppäjärvi–Heinosaari,
[*Adversarial Information Gain in Non-ideal Quantum Measurements*,
arXiv:2602.20941v2](https://arxiv.org/html/2602.20941v2),
§4 Proposition 1, gives the conjugate-instrument meter criterion;
its §3 Theorems 1–2 evaluate their specified noisy-qubit cases.
These are `literature-attested` compatibility mechanisms, not supplies
of source-specific $\mathsf C(s)$, $\mathcal T(s)$, $\gamma_f$,
accessible discarded environments or acquisition permissions.
Coppola–Karevski–Landi,
[*Conditional no-jump dynamics of non-interacting quantum chains*,
arXiv:2311.05515v1](https://arxiv.org/html/2311.05515v1),
§II equations II.5–II.11 and II.17–II.21, gives the unnormalized
no-jump and first-jump framework before its later Gaussian-chain
specialization. This framework is `literature-attested`; the exact
time-dependent instrument identities needed here are proved directly
in JRH.54–JRH.59. No chain ansatz, semigroup universality, sampled
timestamp or native measurement access is inferred from that paper.

## 68. Remaining original mathematical and native interfaces

**Definition 68.1 (scope of the finite conditional synthesis).**
The conclusions require an actually supplied common acquisition on the
sole unknown specimen; genuine generated/dephased flags; calibrated
$D,T,S$, support and row/image isometries; coherent storage of every
jointly counted input-bearing share; specified controlled decoding;
and acquisition and control within the same original aligned clock.
The first absorbing failure must actually occur at absolute $6+t$,
with no subsequent positive-carrier operation. Terminal live output,
the existing stopped/event archives, source/epoch identity, controller
updates and permissions retain their original semantics. An abstract
CPTP factorization, a positive whole-fibre decoder or a geometric
OriginalControl path supplies none of these services by itself.
An ideal exact-time measure does not supply finite exact-event storage.

The full quantum-first AURIC FIB ATOM programme through 2027, the
entire original residual/contact/rank target and the exact quantitative
$(s,A)$ feasibility/TV frontier remain separate required questions.
The present proof needs only the published JR finite moment problem
and strong equality face. It imposes no later residual formula,
common $g$ on all optimizers, contact/rank restriction or endpoint-hazard
equivalence. The full-output atom exclusion precedes and is independent
of the particular $g$ used in the finite approximants. The finite-rate
no-go retains its declared class, rather than every possible native
mechanism; noncommuting probability-phase controls prevent assuming
that a Schur menu is exhaustive.

The generic actual-instrument inequality sometimes expressed in B14's
notation remains $\text{actual TV gain}\le-\mathbb E r$.
Equality additionally requires actually generated refined labels and
optimal spectral failure readout; an analytic Kraus refinement alone
does not meet those conditions. The positive-decoder approximants
do not attain the original height optimum. Their height deficits and
certain-failure effects do not add to the original error $E_*$.
Real-null atoms, aggregate coefficient rank, physical labels and
joint quantum fibre dimensions are different quantities.

The [critical-response source][CE], §§14–15, supplies differential
ratio images across admitted fixed native datasets and conditional
negative-response consequences at its own analytic hypotheses. The
full-band surplus estimate in
[Spectral construction and the actual Weil comparison](https://github.com/the-omega-institute/trureturing/blob/08c605faf9961fd5381c4ef09db19cabc302657a/Library/Weil/connesconsanimoscovici2026spectral.md),
“Use the complete band to tighten the same-source surplus budget”,
retains its common form/domain, closed-short, cosine-identification,
source and complete-far hypotheses. Neither
provides an object/operation correspondence to the acquisition,
complete CP outputs, TV objective or finite-activity same-clock
decoders above. No such transfer or completion of the continuing
programme is a consequence of these conditional results.

[CG]: https://github.com/the-omega-institute/trureturing/blob/08c605faf9961fd5381c4ef09db19cabc302657a/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: https://github.com/the-omega-institute/trureturing/blob/08c605faf9961fd5381c4ef09db19cabc302657a/docs/develop/theory/FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[CA]: https://github.com/the-omega-institute/trureturing/blob/08c605faf9961fd5381c4ef09db19cabc302657a/docs/develop/theory/FIB_NATIVE_COMPLEX_ATOMIC_CONE_AND_OPTIMAL_RESOURCE_FACES.md
[IR]: https://github.com/the-omega-institute/trureturing/blob/08c605faf9961fd5381c4ef09db19cabc302657a/docs/develop/theory/FIB_NATIVE_INTERIOR_RECORD_RESOURCE_REDUCTION.md
[OC]: https://github.com/the-omega-institute/trureturing/blob/08c605faf9961fd5381c4ef09db19cabc302657a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md
[OCC]: https://github.com/the-omega-institute/trureturing/blob/08c605faf9961fd5381c4ef09db19cabc302657a/Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.scribe.cs
[CE]: https://github.com/the-omega-institute/trureturing/blob/08c605faf9961fd5381c4ef09db19cabc302657a/docs/develop/theory/FIB_NATIVE_EXACT_CRITICAL_ENERGY_RESPONSE_AND_SCALE_ALTERNATIVES.md

## 追加锚（本行以下为增补区）
