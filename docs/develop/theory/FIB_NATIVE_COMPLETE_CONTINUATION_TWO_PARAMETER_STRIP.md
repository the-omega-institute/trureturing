# An original finite-activity two-parameter strip with exactly eight actual outputs

## 1. Conditional theorem and the original experiment

This volume gives an ordinary conditional mathematical theorem for the original experiment. Its proof consists of the displayed algebra, finite rational interval inequalities and their continuum consequences. The numerical appendices are part of the theorem: their constants define the selected roots and contain every preconditioner, box and covering leaf. The complete numerical appendices are stored in the fixed-version data files linked below; their [manifest](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/manifest.json) records their SHA-256 hashes. This is neither a Lean/kernel certificate nor a physical implementation theorem.

**Theorem 1.1 (the entire closed strip).** Under the separate hypotheses in §2, for every

$$
(t,\lambda)\in\mathcal P=[99999/100,100001/100]\times[91/20,23/5],\qquad A=\log(1+t),
$$

there is a unique merged optimizing endpoint law specified in §§3–6. It has four positive pure low weights, three positive saturated low weights, and one required high outcome. The minimum original actual acquisition alphabet is exactly seven low plus one high, hence **eight total outputs**. At each chosen parameter there is one common instrument acting on all twelve histories. The instrument may depend on the parameter.

The law and its value are analytic in the interior and extend continuously to the closed strip. The map $(t,\lambda)\mapsto(A,s(t,\lambda))$ is injective, has a nonzero interior Jacobian, and covers the whole closed region between its two edge curves. In particular it covers every point of the exact original closed rectangle

$$
\mathcal R=[1249633/10^7,624827/5000000]\times[\log(100099/100),\log(100101/100)],
$$

The strength endpoints are exactly $0.1249633$ and $0.1249654$. Throughout the strip the exact value is the root expression in (8), and

$$
0.09958337<\mathcal T_{\log(1+t)}(s(t,\lambda))<0.09965764.
$$

There is no optimizing support, occupied-sign, collision, failure-line, moment-rank or regularity event inside this strip. This does not inventory positive-level stationary points unrelated to the optimum.

**Definition 1.2 (one unknown specimen and the complete error).** Order the five modes as $(0,1,2,3,13)$ and put

$$
E=\left((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2\right),\quad P=EE^\dagger,\quad p_y=(y/128,(64-y)/128,1/2),
$$

$$
a_y=(\sqrt{p_{y0}},\sqrt{p_{y1}},\sqrt{p_{y2}})^T,\quad U_{e,n}=\operatorname{diag}(e,n,1),\quad\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger,
\quad y\in\{5,16,27\},\ e,n\in\{-1,1\}.
$$

The input is the sole normalized specimen $E\rho_{y,e,n}E^\dagger$; there is no history oracle, source prior, copy, helper, retry, reset or postselection. The ideal live block is $EU_{e,n}\xi_y\xi_y^TU_{e,n}^\dagger E^\dagger$, with positive entries determined by

$$
\xi_y^2=\left(y/128,\ y(58-y)/(128(y+6)),\ y/[2(y+6)]\right).
$$

The five ideal separately labelled Borel failure measures, in the same mode order, have weights $w=(0,1/4,1/2,1/4,0)$, fixed normalized stopped output $P_f$, and density

$$
f_y(a)=\frac{6y}{(y+6a)^2},\qquad 0\le a\le1.
$$

Their absolute FIRST coordinate is $6+a$. The error is HALF the norm of the **complete** stopped classical–quantum output difference: trace norm on the live block plus the trace-norm total variation of each separate operator-valued failure measure and every other output sector. Singular-time mass, wrong support, aborts, zero-target components and live off-diagonal entries participate. This is not a survival-normalized error or a diamond-norm claim. All passive-reference conditional maps are retained. The two zero failure components are separate zero measures.

**Definition 1.3 (original resources and height).** An acquisition has actual CP encoders $\mathcal E_j$ with $\sum_j\mathcal E_j^\dagger(I)=I_5$, and full-output TP decoders. Each $d_j$ counts the entire jointly accessible quantum fibre, including every future-accessible retained specimen, memory, controller, environment and entanglement share. Discarded Kraus indices are not readable acquisition outcomes. A binary report is classical processing of the actual label; any independent readable coin belongs to that label. If $F_+$ is its plus effect on the supported qutrit, the original requirement is

$$
\mathsf V(F_+)=\frac{2|\operatorname{Re}(F_+)_{01}|}{\kappa}\ge s,\qquad\kappa=h_0a+h_1b>0.
$$

Write $Q_H=\sum_{d_j\ge3}\mathcal E_j^\dagger(I)$ and $\mathsf W=\max_{y,e,n}\operatorname{tr}(Q_HE\rho_{y,e,n}E^\dagger)$. This is the worst-history probability of **jointly acquired dimension at least three**, including subsequent failure. The sharp cost $\mathsf C(s)$ minimizes this quantity among original error-optimal instruments satisfying the contrast inequality. Height is the total variation of the actual acquired-label laws for $\rho_{27,+,+}$ and $\rho_{5,+,+}$; $\mathcal T_A(s)$ is its maximum at error $E_*$, cost $\mathsf C(s)$ and activity at most $A$.

Activity is $\sup_{j\text{ actually generated}}\int_0^1\|R_j(a)\|\,da$, on each whole fibre, for positive absorbing rates. Intervening not-yet-failed controls and terminal survivor processing are TP. Finite activity leaves strictly positive survivors; forced terminal absorption and later action on a stopped carrier are excluded. The no-jump branch itself is trace decreasing. Arbitrary admitted failure-time laws remain in the competitor class.

## 2. Separate original interfaces and the consistent source

The owning definitions are [CG §§13–17 and positive-pivot dictionary](FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md), [JR §§34–42](FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md), [FA §§67–72 and 78](FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md), and [corrected RC §§67 and 75](FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md). The following are explicit conditional inputs. They have distinct scopes; none is recertified by the strip arithmetic.

**Convention 2.1 (source hypothesis).** The original nine-coordinate CG point is the stipulated isolated consistent root in the radius-$10^{-24}$ box specified in Appendix A. At this one root its source slacks are PSD with the stipulated ranks, the positive pivots exist, the dictionary below is exact, and the normalization/TP equations hold. The source enclosure is a bound on that root. Independent coordinates in the surrounding box are used only for enclosing expressions; they are not asserted to satisfy ranks or TP.

For completeness the dictionary is restated. In coordinate order $(\lambda_{\rm CG},\alpha_1,\alpha_2,\beta_1,\beta_2,z_{\rm CG},\eta_0,\eta_1,\eta_2)$ set $v_5=(\alpha_1,\alpha_2,-1)^T$, $v_{27}=(\beta_1,\beta_2,1)^T$,

$$
A_5=\lambda_{\rm CG}\frac{v_5v_5^T}{v_5^Tv_5},\quad A_{27}=(1-\lambda_{\rm CG})\frac{v_{27}v_{27}^T}{v_{27}^Tv_{27}},\quad N^{\rm dual}=A_5\odot\rho_{5,+,+}+A_{27}\odot\rho_{27,+,+},
$$

$$
\zeta=(z_{\rm CG},59\lambda_{\rm CG}/128,\lambda_{\rm CG}/2),\quad S_0=\operatorname{diag}(\zeta)-N^{\rm dual},\quad
S_{ij}=\begin{pmatrix}\zeta_j-\sum_{y=5,27}(A_y)_{ii}p_{yj}&-N^{\rm dual}_{ij}\\-N^{\rm dual}_{ij}&\zeta_i-\sum_{y=5,27}(A_y)_{jj}p_{yi}\end{pmatrix}.
$$

Put $H=1000\eta_0\operatorname{adj}S_0$, $Q^{01}=\eta_1\operatorname{adj}S_{01}$, $Q^{02}=\eta_2\operatorname{adj}S_{02}$. Their rank-one positive-pivot factors at the root are

$$
(h_0,h_1,h_2)^T=He_0/\sqrt{H_{00}},\quad(a,b)^T=Q^{01}e_0/\sqrt{Q^{01}_{00}},\quad(c_{\rm src},d)^T=Q^{02}e_0/\sqrt{Q^{02}_{00}}.
$$

Thus $H_{ij}=H_{i0}H_{0j}/H_{00}$, and analogously for $Q$, at the root. The factor $1000$ here belongs to the fixed source reconstruction and is not the varying activity parameter $t$. Define

$$
D=\operatorname{diag}(h_0,h_1,h_2),\quad T=ae_0e_1^T+be_1e_0^T,\quad S=c_{\rm src}e_0e_2^T+de_2e_0^T,\quad M=\operatorname{diag}(0,m_1,m_2),
$$

$$
m_1=1-h_1^2-a^2,\quad m_2=1-h_2^2-c_{\rm src}^2,\quad D^\dagger D+T^\dagger T+S^\dagger S+M=I_3.
$$

In particular $1-h_0^2-b^2-d^2=0$ is a root equation. A zero-containing enclosure of its left side would not prove this equality. All amplitudes and $m_1,m_2$ are positive. Set

$$
\theta=ab/(h_0h_1),\quad\omega=c_{\rm src}d/(h_0h_2),\quad\delta=\theta+\omega\in(0,1),\quad s_0=\sqrt\delta,\quad\alpha=\theta/\delta,\quad\beta=\omega/\delta.
\tag{1}
$$

These common definitions imply $\alpha+\beta=1$ exactly. Let $\Delta=\rho_{27,+,+}-\rho_{5,+,+}$, $K^{(0)},K^{(1)},K^{(2)}=(D,T,S)$,

$$
N_{ij}=\operatorname{tr}(K^{(i)}\Delta K^{(j)\dagger}),\quad G=\operatorname{diag}(s_0,1,1)N\operatorname{diag}(s_0,1,1),\quad H_{\rm high}=(1-\delta)N_{00}>0.
$$

The physical $1,2$ submatrix of $\Delta$ is $\left(\begin{smallmatrix}-11/64&(\sqrt{37}-\sqrt{59})/16\\(\sqrt{37}-\sqrt{59})/16&0\end{smallmatrix}\right)$. Appendix A contains both source enclosures and the independent outward derived bounds. Either radical construction or the common enclosed dictionary gives expressions at the same root, never independent source choices.

**Convention 2.2 (minimax hypothesis).** CG14–16 supply the complete HALF stopped-cq minimax value $E_*$ and its attainer with supported live map $\Lambda_*(X)=DXD^\dagger+TXT^\dagger+SXS^\dagger$, failure effect $M$ and witness density $g(a)=2/(1+a)^2$. On all sign copies, $e_{5,e,n}=e_{27,e,n}=E_*$ and $e_{16,e,n}<E_*$. CG17 supplies exactly its averaged-live and preaveraged support/effect consequences. It supplies neither the sharp joint cost nor the unaveraged real equality face. The ideal density remains $f_y$, distinct from $g$.

**Convention 2.3 (sharp cost and equality-face hypothesis).** JR34–40 and JR42 supply the original sharp worst-history joint acquired cost and the unaveraged supported real face for every error- and cost-optimal competitor. On this weak branch $\mathsf C(s)=(1-\delta)A_{27}$, where $A_y=\sum_i h_i^2p_{yi}$; $A_y$ strictly increases with $y$. The coefficient Grams, no supported high failure and real null supported live products are consequences of this additional hypothesis, not of CG17 alone.

**Convention 2.4 (full class, actual-label and capacity hypothesis).** FA69–72 and corrected RC67/75 supply reduction on each existing supported-nonzero actual low label, double rank rigidity, capacity necessity, endpoint value reduction and the common constructor interface. The competitor class is the original full complex, arbitrary multi-Kraus finite/countable class and only its explicitly stipulated measurable extension: measurable finite-dimensional fibres and Kraus fields, integrable effects and live Choi fields, and full-output TP decoders almost everywhere. No unrestricted disintegration or infinite-dimensional extension is assumed.

Specifically each such actual low label has a real direction $h=(1,z,w)$ with $\alpha z^2+\beta w^2=1$, weight $p>0$, live product $\sqrt p(s_0D+zT+wS)$ and attached failure $pb_hn_hn_h^T$, where

$$
n_h=(0,dw/h_2,-bz/h_1)^T,\quad\ell(h)=h^TGh,\quad f(h)=n_h^T\Delta n_h,\quad
c(h)=\frac{\delta h_1^2h_2^2+a^2h_2^2z^2+c_{\rm src}^2h_1^2w^2}{\delta h_0^2+b^2z^2+d^2w^2}>0.
\tag{2}
$$

Here $0\le b_h\le tc(h)$ and, for that same joint law,

$$
\sum p hh^T=I_3,\quad\sum p b_hn_hn_h^T=M,\quad\sum p|z|\ge s/s_0,\quad
2T_{\rm actual}=H_{\rm high}+\sum p|\ell(h)+b_hf(h)|.
\tag{3}
$$

The contrast available from a law bounds its actual contrast above. Distinct supported live directions cannot share one existing low label by exposing a hidden Kraus index. Every supported-nonzero low fibre is exactly two dimensional; its supported encoder and live decoder have CP Kraus rank one, with an onto encoder and injective live decoder. Finite whole-fibre activity gives survivor effect at least $e^{-A}I$, excluding a nonzero supported encoder with zero live composition. Supported-zero full-$M_5$ encoders remain legal, count if generated and obey their whole-fibre activity bound; they contribute zero to (3). Positive compulsory high mass requires another actual label. These statements retain their full complex/multi-Kraus and stipulated measurable scopes.

FA78 supplies only the additional feasibility interface used here: with $V=m_2h_1^2/b^2$, $W=m_1h_2^2/d^2$, $\mu=\alpha V+\beta W$, $r_f=V/\mu$, $c_f=c(1,\sqrt{r_f},\sqrt{(1-\alpha r_f)/\beta})$, $\nu=\mu/c_f$, $t_0=W/c_f$ and $q=\nu/t$, the weak maximum strength is $s_0[q\sqrt{r_f}+\sqrt{(1-q)(1-qr_f)}]$ for $t\ge t_0$. The bounds in Appendix A give $t_0<265$ and this strength $>0.12520565$ throughout the budget interval. No boundary classification or global count theorem is needed for Theorem 1.1.

## 3. One eight-moment system and its complete Jacobian

Use $u=\cos\phi$, $v=\sin\phi$, $z=u/\sqrt\alpha$, $w=v/\sqrt\beta$. For $\eta=0,1$ define

$$
\Gamma_\eta=(1,u,v,u^2,uv,\eta c,\eta cu^2,\eta cuv),\quad H_\eta=\ell+\eta tc f,\quad
B(t)=(1,0,0,\alpha,0,\mu/t,\alpha V/t,0).
\tag{4}
$$

Seven contacts have the following order; it also fixes the order of every array in the appendices.

| $i$ | $\eta_i$ | height sign $\epsilon_i$ | report sign $\sigma_i$ | base $\psi_i$ |
| --- | --- | --- | --- | --- |
| 0 | 0 | +1 | +1 | $0$ |
| 1 | 0 | +1 | −1 | $\pi$ |
| 2 | 0 | −1 | −1 | $\pi$ |
| 3 | 1 | +1 | +1 | $0$ |
| 4 | 1 | −1 | +1 | $3\pi/2$ |
| 5 | 0 | +1 | +1 | $0$ |
| 6 | 1 | −1 | −1 | $\pi$ |

Set $\phi_i=\psi_i+2\arctan x_i$. The unknown order is **exactly** $X=(x_0,\ldots,x_6,p_0,\ldots,p_6,Y_0,\ldots,Y_7)$. The residual order is eight moments, followed by the interleaved pairs $(P_0,P'_0),\ldots,(P_6,P'_6)$.

Here are all cleared expressions. For an indeterminate $x$, put $r=1+x^2$ and choose $(U,V_c)=(1-x^2,2x)$ at base $0$, $(-1+x^2,-2x)$ at base $\pi$, and $(2x,-1+x^2)$ at base $3\pi/2$. Write $Z=U/\sqrt\alpha$, $W_c=V_c/\sqrt\beta$ and

$$
\begin{aligned}
D_c&=\delta h_0^2r^2+b^2Z^2+d^2W_c^2,&N_c&=\delta h_1^2h_2^2r^2+a^2h_2^2Z^2+c_{\rm src}^2h_1^2W_c^2,\\
L_c&=(r,Z,W_c)G(r,Z,W_c)^T,&F_c&=-\frac{11}{64}(dW_c/h_2)^2-2\Delta_{12}dbZW_c/(h_1h_2).
\end{aligned}
$$

The following tuple defines respectively the moment numerator $g_\eta$, positive denominator $d_\eta$, height numerator $h_\eta$ and report numerator $w_\eta$:

$$
\begin{aligned}
(g_0,d_0,h_0^{\rm num},w_0)&=((r^2,rU,rV_c,U^2,UV_c,0,0,0),r^2,L_c,rU),\\
(g_1,d_1,h_1^{\rm num},w_1)&=((D_cr^2,D_crU,D_crV_c,D_cU^2,D_cUV_c,N_cr^2,N_cU^2,N_cUV_c),D_cr^2,D_cL_c+tN_cF_c,D_crU).
\end{aligned}
$$

Both $D_c,N_c$ are strictly positive. For each contact use its chart and sheet, and put $P_i(x)=Y\cdot g_{\eta_i}(x)-\epsilon_i h_{\eta_i}^{\rm num}(x)-\lambda\sigma_i w_{\eta_i}(x)$. The entire square system is

$$
F_a=\sum_{i=0}^6p_i\frac{g_{\eta_i,a}(x_i)}{d_{\eta_i}(x_i)}-B_a(t)\quad(0\le a<8),\qquad
F_{8+2i}=P_i(x_i),\quad F_{9+2i}=P_i'(x_i).
\tag{5}
$$

Primes always differentiate the displayed polynomial in its own $x$ chart. For all $0\le a<8$, the moment Jacobian entries are

$$
J_{a,x_i}=p_i\frac{g'_{i,a}d_i-g_{i,a}d_i'}{d_i^2},\quad J_{a,p_i}=g_{i,a}/d_i,\quad J_{a,Y_b}=0.
$$

The value and stationary rows have $J_{8+2i,x_j}=\mathbf1_{i=j}P_i'$, $J_{9+2i,x_j}=\mathbf1_{i=j}P_i''$, all their weight entries zero, and dual entries $J_{8+2i,Y_b}=g_{i,b}$, $J_{9+2i,Y_b}=g'_{i,b}$. These formulas specify every entry of $J=F_X$; interval $P_i'$ is **not** replaced by zero when enclosing $J$.

The only nonzero moment entries of $F_t$ are $(F_t)_5=\mu/t^2$, $(F_t)_6=\alpha V/t^2$. On a saturated contact $(F_t)_{8+2i}=-\epsilon_iN_cF_c$ and $(F_t)_{9+2i}=-\epsilon_i(N_cF_c)'$; they vanish on a pure contact. All moment entries of $F_\lambda$ vanish, and its contact pair is $(-\sigma_iw_i,-\sigma_iw_i')$. These are exact partial derivatives at fixed $X$ and source.

## 4. Finite interval data and the uniform existence proof

**Lemma 4.1 (all fifty boxes).** The data in Appendix B have precisely the parameter rectangles

$$
\mathcal P_j=[99999/100,100001/100]\times[91/20+j/1000,91/20+(j+1)/1000],\quad 0\le j<50.
$$

For every fixed parameter in each rectangle the residual (5) has a unique zero in the displayed box $\mathcal X_j=C_j+[-r_j,r_j]$. Its Jacobian is invertible there. The weighted bounds used for contraction satisfy $q<0.0215$ and $\iota<0.490$. Appendix C additionally records the independent bounds $q<0.021354$ and $\iota<0.489708$.

Proof. The appendices use exact rational strings and integer endpoint pairs. At grid denominator $D$ a pair $[a,b]$ means $[a/D,b/D]$. Addition and subtraction use endpoint algebra; multiplication takes the minimum/maximum of four products and rounds outward. Division reverses reciprocal endpoints only if zero is excluded. Squaring uses lower endpoint zero when the interval contains zero. For nonnegative endpoints square roots are bounded using integer square roots and exact squaring. The source radius and all parameter endpoints are rational. Appendix B's $D=2^{190}$; the independent calculation and Appendix C use $D=2^{210}$. Decimal `display` fields are orientation only, never interval endpoints.

Let $t_c,\lambda_c$ be parameter midpoints and let $R$ be the displayed fixed rational matrix. With weighted maximum norm $\|v\|_r=\max_i|v_i|/r_i$, form $E=I-R[J]_{\mathcal X,\mathcal P}$ and $q_i=\sum_j\sup|E_{ij}|r_j/r_i$. At the fixed centre all parameter dependence is affine except $-B_*/t$ in the two moment rows. Its exact Taylor remainder is

$$
-\frac{B_*}{t}+\frac{B_*}{t_c}-\frac{B_*}{t_c^2}(t-t_c)
=-\frac{B_*(t-t_c)^2}{t_c^2t}.
$$

Consequently an enclosure of $RF(C;t_c,\lambda_c)$, the two preconditioned partial derivatives at the centre, their parameter halfwidths, and that explicit remainder give $e_i\ge\sup_{\mathcal P}|(RF(C;t,\lambda))_i|$. Set

$$
q=\max_iq_i,\qquad\iota=\max_i(e_i/r_i+q_i).
\tag{6}
$$

All exact per-cell independent fractions are in Appendix C. Direct outward evaluation of (1)–(5) in the written polynomial order gives the Appendix D bounds $q<0.021454$ and $\iota<0.489657$, already sufficient for (6). For every cell its Appendix D inclusion is strictly smaller than the corresponding Appendix C inclusion. Thus the latter fractions are also valid image factors. No improvement of $q$ is needed to use those factors. Thus $T(X)=X-RF(X;t,\lambda)$ is a contraction and maps the closed box strictly into itself, for **every** parameter section. Its fixed point exists and is unique. Since $\|I-RJ\|_r<1$, $RJ$ is invertible; square $R$ and $J$ are then invertible. The fixed point really has $F=0$. The analytic implicit-function theorem applies at each section. This proves parameter-uniform existence, not a mesh extrapolation.

The fixed point also obeys $|X_i-C_i|\le\iota r_i$. For refinement use each cell's own exact independent `inclusion` fraction, and round each endpoint of $C\pm\iota r$ outward to the $2^{-210}$ grid. Rebuild all polynomial coefficients from the original nine source-coordinate intervals and (1)–(5) on this contracted image. Use the **same** eight arc charts, factor lists and leaves, without asserting new contact equations off the root. Appendix C's refined constants refer to precisely this rule; Appendix D gives a separate direct-polynomial evaluation on those same images. This image inclusion follows from $X=T(X)$; it is not an extra fixed-point assumption. ∎

**Lemma 4.2 (strict geometry).** Throughout every actual root section all seven weights exceed $0.0000242$, signed heights exceed $0.003262$, signed reports exceed $0.6240$, and angular gap curvatures exceed $0.4195$. Every squared circle separation exceeds $0.01646$, every squared wedge between the three saturated directions exceeds $0.1996$, and the determinant of the seven moment columns on rows $(0,1,2,3,4,5,7)$ exceeds $0.0095048>0.00855$.

Proof. Evaluate $p_i$, $\epsilon_iH_{\eta_i}$, $\sigma_iu_i$ and $P_i''(x_i)(1+x_i^2)^2/(4d_i)$ on the stated boxes; at exact stationary zeros the last expression is the angular curvature. Separations are $(u_i-u_j)^2+(v_i-v_j)^2$. Saturated wedges are $(u_iv_j-v_iu_j)^2$ for $(i,j)=(3,4),(3,6),(4,6)$. The fixed invertible map $(u,v)\mapsto(dv/(h_2\sqrt\beta),-bu/(h_1\sqrt\alpha))$ preserves noncoincidence of their physical failure lines. For the direct bound let $A_0$ be the rational entrywise integer-midpoint matrix of its interval matrix. Exact rational elimination gives $A_0^{-1}$ and $\det A_0$. The identity $\det A=\det A_0\det(A_0^{-1}A)$ permits interval elimination near the identity with nonzero pivots. Appendix D includes every resulting seven-dimensional preconditioner and determinant factor. This is also an explicit way to evaluate the determinant's multilinear formula. The exact per-cell original and independent bounds are in Appendices B–C. The contracted-image lower bounds strengthen the separations to $>0.0164789$ and wedges to $>0.1997043$. These are simultaneous inequalities for the same root. ∎

## 5. Complete-circle signs and exact equality sets

**Lemma 5.1 (all sheets and all arcs).** On both whole circles,

$$
Y\cdot\Gamma_\eta(\phi)\ge |H_\eta(\phi)|+\lambda|u(\phi)|.
\tag{7}
$$

The zeros are exactly the seven contacts in §3. The pure and saturated equality directions are disjoint.

Proof. Use base $0$ on $u\ge0$ and base $\pi$ on $u\le0$, each with the full closed interval $x\in[-1,1]$. Together they cover both axes and the infinity omitted by either single half-angle chart. Check the eight cases in lexicographic order $\eta=(0,1)$, $\epsilon=(-1,+1)$, $\sigma=(-1,+1)$. Their occupied root lists are respectively $[2],[],[1],[0,5],[6],[4],[],[3]$, with quotient degrees $2,4,2,0,6,6,8,6$. Contact 4 is converted to base $0$ by $x=(x_4-1)/(x_4+1)$; this chart change has nonzero derivative and the clearing denominator stays positive.

At the actual zero of (5), each occupied polynomial has exactly $P(a_i)=P'(a_i)=0$. The polynomial remainder theorem therefore gives exact divisibility by $(x-a_i)^2$. Distinct contacts, certified in Lemma 4.2, permit successive divisions. Equivalently, after dividing at one root, the other root's quotient and derivative still vanish because its removed factor is nonzero. This proves exact factorization of the whole polynomial. An interval remainder containing zero would not prove any of these equalities and is not used to do so.

For specificity, ascending coefficients $c_0,\ldots,c_n$ divide once at $a$ by $b_{n-1}=c_n$, $b_{k-1}=c_k+ab_k$ for $k=n-1,\ldots,1$, with remainder $c_0+ab_0$. Apply this twice for each listed root. Enclosing these expressions gives the quotient coefficients. For a leaf $[a,b]$, $x=a+(b-a)y$, define

$$
A_j=\sum_{k=j}^nq_k\binom{k}{j}a^{k-j}(b-a)^j,\quad
C_i=\sum_{j=0}^i A_j\frac{\binom{i}{j}}{\binom{n}{j}},\quad
Q(x)=\sum_{i=0}^n C_i\binom ni y^i(1-y)^{n-i}.
$$

Every supplied leaf's degree and ordered rational endpoints are in Appendix B. On each arc they start at $-1$, abut exactly and end at $1$: 35 leaves per cell, 400 complete arcs and 1750 leaves in all. Nonnegative Bernstein basis functions sum to one, so strictly positive enclosing control lower endpoints prove positivity at every point, including leaf boundaries.

The independent **full-box** control bound is $>0.00012057$. This alone does not establish the stronger $>0.0001206$ bound. On the contracted fixed-point image specified after (6), recomputation gives the exact refined fractions in Appendix C and a uniform lower bound $>0.00016645$, which does establish $>0.0001206$ for the actual root family. All leaves are retained in this refinement. The direct-polynomial Appendix D evaluation gives $>0.00016650$ on those same images and partitions; either sufficient lower bound proves the claimed $>0.0001206$. The positive quotients and nonnegative removed squares give the exact zero sets. The opposite report sign is weaker by $2\lambda|u|$, with $\lambda>0$. Checking both height signs therefore proves (7) everywhere. ∎

## 6. Original global optimality, uniqueness, actual count and joins

**Theorem 6.1 (one law, global bound and exact actual count).** Define

$$
k=\sum_i p_i|u_i|,\quad s(t,\lambda)=\frac{s_0}{\sqrt\alpha}k,\qquad
\mathcal T_{\log(1+t)}(s(t,\lambda))=
\frac{H_{\rm high}+Y\cdot B(t)-\lambda k}{2}.
\tag{8}
$$

This is the original global optimum in the full competitor class of §2, with unique merged endpoint law and minimum actual total count eight.

Proof. The first five exact equations give $\sum p=1$, zero first and mixed moments, $\sum pu^2=\alpha$, and $\sum pv^2=\beta$. Hence $\sum phh^T=I_3$. Put $b_i=\eta_i tc(h_i)$. The last three give $\sum pb_i=\mu$, $\sum pb_iz^2=V$, $\sum pb_izw=0$. Since $\alpha z^2+\beta w^2=1$ and $\mu=\alpha V+\beta W$, they also give $\sum pb_iw^2=W$. Congruence under $(z,w)\mapsto(dw/h_2,-bz/h_1)$ yields $\sum pb_in_in_i^T=M$, including its off-diagonal zero. These are joint live and failure constraints of one law.

For any original competitor invoke (3) on its existing actual supported labels. Retain its original fractional $\xi=b_h/[tc(h)]\in[0,1]$. Convexity gives $|\ell+b_hf|\le(1-\xi)|H_0|+\xi|H_1|$. Integrating both whole-sheet inequalities (7) against that **same** split law gives

$$
2T_{\rm actual}\le H_{\rm high}+Y\cdot B(t)-\lambda\sum p|u|
\le H_{\rm high}+Y\cdot B(t)-\lambda\sqrt\alpha s/s_0.
$$

It permits every original failure allocation, intermediate capacity, live decomposition, complex multi-Kraus implementation and admitted time law. There is no maximum-contrast-facet, fixed-allocation or two-failure-line restriction. At the selected exact root the signed heights, reports, contacts and common moments attain equality. The instrument in §9 realizes them simultaneously, giving (8). Evaluating its signed primal height on the contracted images gives the value enclosure in Theorem 1.1; every exact per-cell value bound is in Appendix C.

At equality $\lambda>0$ forces contrast equality and all nonnegative dual slacks to vanish. This is pointwise on every positive-weight actual label and almost everywhere in the stipulated integrable extension. For $0<\xi<1$, both endpoint gaps at the same direction would have to vanish. Lemma 5.1 excludes that. Thus every optimal supported low label is one of the seven endpoints. The seven independent columns force the merged weights to be exactly the selected ones, all positive. Double rigidity in Convention 2.4 prevents distinct directions being combined inside one actual low label, even with discarded multi-Kraus representations. Hence seven low labels are necessary. The positive compulsory high acquired mass requires at least one more actual label. Section 9 uses precisely one high label, including its whole dimension-five complement, so eight are sufficient.

This proves uniqueness of the merged endpoint law, not uniqueness of the CP instrument, Kraus representation, time law or arbitrary added supported-zero outcomes. Fractional capacities remained legal until equality excluded them on this exposed face. Endpoint splitting by itself is a value argument, not a minimum-actual-count closure proof. In any count-closure argument the original fractional coordinate must instead be retained. ∎

**Lemma 6.2 (all forty-nine joins).** Adjacent cells define the same analytic law and dual on their whole shared $t$ edge.

Proof. Fix any $t$ on a shared edge and its common $\lambda$. Each root is a primal/dual optimum of the **same** penalized moment problem

$$
\max_{\sum p\Gamma_\eta=B(t)}\sum p\bigl(|H_\eta|+\lambda|u|\bigr).
\tag{9}
$$

No strength is fixed in (9). This avoids assuming that adjacent roots have equal strengths before proving they are the same law. Each law attains its own globally feasible dual $Y\cdot B(t)$, so both have the same optimal value and mutual zero slack. Either finite strict zero set forces the other law onto its same seven endpoints; the minor fixes weights. Their dual difference annihilates every contact value and angular derivative. The vector consisting of zero angle/weight differences and this dual difference is then in the kernel of the nonsingular contact Jacobian, so it vanishes. Local analytic uniqueness gives agreement on neighborhoods of the edge. The argument holds for every $t$, identifying all 49 joins. No prior connected one-parameter source is needed. ∎

## 7. Strict strength order and analytic coordinates

**Lemma 7.1 (strict response on the whole strip).** $k_\lambda>0$ everywhere. The map in Theorem 1.1 has the asserted injectivity and analytic inverse.

Proof. In physical variables $z_{\rm phys}=(p,\phi)$ let $M_0=d_z(\sum p\Gamma)$ and

$$
L=Y\cdot(\sum p\Gamma-B)-\sum p(|H|+\lambda|u|).
$$

Nonzero chart and row scalings identify the contact Jacobian with the KKT Jacobian at the positive root. A nonzero left null vector of $M_0$ would give a pure-dual kernel vector, so $\operatorname{rank}M_0=8$. The Hessian has zero weight and mixed blocks and angular block $\operatorname{diag}(p_i\gamma_i)>0$. It is positive definite on $\ker M_0$: vanishing forces zero angular variation, then the independent columns force zero weight variation. For a basis matrix $N_T$ of this kernel, implicit differentiation and projection give

$$
k_\lambda=q^T(N_T^TL_{zz}N_T)^{-1}q,\qquad q=N_T^T\nabla k.
\tag{10}
$$

To prove $q\ne0$, use only pure contacts $0,1,2$. Let the columns of $A_p$ be $\sqrt{p_i}(1,u_i,v_i)^T$, $Q=\operatorname{diag}(1,-1,-1)$, and $S_{ij}=(A_p^TQA_p)_{ij}=\sqrt{p_ip_j}[1-\cos(\phi_i-\phi_j)]>0$ for $i\ne j$. Choose skew $\Omega$ by $\Omega_{10}=1/S_{01}$, $\Omega_{20}=-1/S_{02}$, $\Omega_{21}=1/S_{12}$. Then $\dot A_p=A_p\Omega$ preserves $A_pA_p^T$, and $\operatorname{diag}(S\Omega)=0$ preserves the three null conditions to first order. Positive weights turn this into legitimate weight/angle variations. Saturated columns stay fixed; the last three moments on pure columns vanish identically. Thus this is a tangent to all eight constraints.

For $a=x_0,b=x_1,c=x_2$, $\rho_1=(a-b)/(1+ab)$, $\rho_2=(a-c)/(1+ac)$, direct differentiation of $k$ with signs $+,-,-$ gives

$$
\dot k=2\frac{1-a^2}{1+a^2}(\rho_1-\rho_2)
\left(\rho_1+\rho_2-\frac{2a}{1-a^2}\right)>0.006533.
$$

The exact tangent bounds in Appendix C establish this throughout every box. Hence $q\ne0$ and (10) is strictly positive. The joined continuous law is strictly strength ordered at each fixed $t$. Differentiating the moment/contact identities also gives $\partial_\lambda\sum p|H|=-\lambda k_\lambda$, so $\mathcal T_s=-\lambda\sqrt\alpha/(2s_0)$.

Since $t\mapsto\log(1+t)$ is injective, the full parameter map is injective. In coordinate order $(t,\lambda)\mapsto(A,s)$ its determinant is $s_0k_\lambda/[(1+t)\sqrt\alpha]>0$. Compactness gives a homeomorphism onto the closed image and the analytic inverse theorem gives an interior analytic inverse. For each fixed $t$, the intermediate value theorem identifies the entire image strength interval with the interval between the two edges. Strict geometry and quotient bounds persist through all joins. ∎

## 8. Both edges and the exact closed original rectangle

**Lemma 8.1 (edge integration).** Let $s_-(t)=s(t,91/20)$ and $s_+(t)=s(t,23/5)$. Uniformly on the closed budget interval,

$$
0.1249631858479<s_-(t)<0.1249631904871,
\qquad0.1249655224418<s_+(t)<0.1249655270641.
\tag{11}
$$

Proof. Appendix B includes two separate full-$t$ edge boxes and two separately contracted point boxes at $t=1000$. They use exactly (5), with a degenerate multiplier interval. Appendix C gives their independent contractions, strict containment margins, uniform implicit derivative bounds, midpoint strengths and integrated strengths.

The derivative is from $JX_t=-F_t$. For any fixed rational approximate tangent $v_t$, set $e=\max_i|(R(Jv_t+F_t))_i|/r_i$. The Neumann series for $RJ$ gives

$$
|(X_t)_i-(v_t)_i|\le r_i e/(1-q).
\tag{12}
$$

Appendix D gives fixed rational tangents and the exact $q,e$ and resulting $s_t$ intervals for (12). To obtain those tangents, enclose $F_t$ at the dyadic centre and parameter midpoint, take each integer midpoint (floor the average of its two integer endpoints), multiply by $-R$ with outward grid operations, and take integer midpoints again. All source and matrix inputs for these operations are in the linked data records. Multiplying this derivative enclosure by the exact rational derivative of $k=\sum p\sigma_iU_i/r_i^{\rm chart}$, then by $s_0/\sqrt\alpha$, gives $s_t$. This use of an implicit equation is uniform on the full edge, not a finite difference.

The stronger independent intervals in Appendix C, displayed decimally for orientation, are respectively

$$
(s_-)_t\in[1.1654281940881829,2.3179357111638457]\,10^{-7},\quad
(s_+)_t\in[1.15605707928324,2.3094528228122073]\,10^{-7}.
$$

The separate midpoint roots give $s_-(1000)\in[0.12496318816747852,0.12496318816749688]$ and $s_+(1000)\in[0.12496552475290233,0.12496552475292068]$. The exact Appendix C intervals, rather than these decimal displays, carry comparisons. Each point box lies strictly inside its edge box, and each edge box inside the adjacent strip box. Contraction uniqueness therefore identifies the actual roots before integration.

The explicit Appendix D tangents separately prove $(s_-)_t\in(1.1638,2.3196)10^{-7}$ and $(s_+)_t\in(1.1544,2.3111)10^{-7}$. These slightly wider bounds already imply (11) when integrated against the exact midpoint intervals. For $|t-1000|\le1/100$, integrating the stronger Appendix C intervals gives enclosing intervals with decimal displays $[0.12496318584954282,0.12496319048543258]$ and $[0.12496552244344951,0.12496552706237350]$. Exact rational comparisons place them strictly inside (11). Therefore $s_-(t)<0.1249633\le0.1249654<s_+(t)$ throughout the budget interval. Lemma 7.1 covers every intermediate requested strength, including both endpoints. Finally $1+t\in[1000.99,1001.01]$ exactly; monotonicity of the logarithm gives the stated closed $A$ interval without a numerical logarithm approximation. This proves rectangle inclusion. ∎

## 9. One common original CP instrument at each parameter

**Theorem 9.1 (simultaneous full-output realization).** Every selected law is realized by seven actual low qubit fibres and one actual high dimension-five fibre, with activity at most $\log(1+t)$, strictly positive survivors, original sharp joint acquired cost and complete original output identities.

Proof. For a general allowed fractional label set $K=\sqrt p\,L_h$, $L_h=s_0D+zT+wS$, and $N=pb_hn_hn_h^T$. At a selected endpoint $b_h=\eta tc(h)$. Expansion gives

$$
\det L_h=s_0^3h_0h_1h_2(1-\alpha z^2-\beta w^2)=0.
$$

Its lower rows $(bz,s_0h_1,0)$ and $(dw,0,s_0h_2)$ are independent, so it has rank two. Its kernel is spanned by $(s_0,-bz/h_1,-dw/h_2)^T$, orthogonal to $n_h$, proving $\operatorname{ran}N\subset\operatorname{ran}K^\dagger$.

Here is also the exact capacity algebra. Write $L_h=T_hR_h$, where $R_h$ consists of those lower rows and $T_h$ has rows $(az/(s_0h_1),c_{\rm src}w/(s_0h_2)),(1,0),(0,1)$. Then $n_h=R_h^T(dw,-bz)^T/(s_0h_1h_2)$. The $2\times2$ inverse of $T_h^TT_h$, using $ab h_2z^2+c_{\rm src}d h_1w^2=\delta h_0h_1h_2$, gives

$$
n_h^T(L_h^\dagger L_h)^+n_h=1/c(h).
$$

Equivalently, for $G_h=L_h^\dagger L_h$ and its positive $00$ pivot,

$$
G_h-\frac{G_he_0e_0^TG_h}{(G_h)_{00}}=c(h)n_hn_h^T.
$$

Indeed $(G_h)_{01}=s_0z(h_0a+h_1b)$, $(G_h)_{02}=s_0w(h_0c_{\rm src}+h_2d)$, $(G_h)_{11}=a^2z^2+\delta h_1^2$, $(G_h)_{22}=c_{\rm src}^2w^2+\delta h_2^2$, $(G_h)_{12}=ac_{\rm src}zw$. Multiplying the residual $11,12,22$ entries by $(G_h)_{00}$ gives the numerator of (2) times $d^2w^2/h_2^2,-bdzw/(h_1h_2),b^2z^2/h_1^2$, respectively. This also proves $N\preceq tK^\dagger K$ iff $b_h\le tc(h)$ by the Schur complement.

Choose a row-space isometry $J:\mathbb C^2\to\operatorname{ran}K^\dagger$ and put

$$
Q=J^\dagger(K^\dagger K+N)J>0,\quad C=Q^{1/2}J^\dagger E^\dagger,\quad B=KJQ^{-1/2},\quad F=Q^{-1/2}J^\dagger NJQ^{-1/2}.
$$

Then $BC=KE^\dagger$, $C^\dagger FC=ENE^\dagger$ and $B^\dagger B+F=I_2$. Since $K$ has rank two, $I_2-F\succ0$ on the entire fibre. The rank-one update formula gives the nonzero failure eigenvalue $b_h/[c(h)+b_h]$, zero for a pure label and $t/(1+t)$ for a saturated one.

Use the common witness time law, distinct from the ideal $f_y$,

$$
g(a)=2/(1+a)^2,\quad G_{\rm time}(a)=2a/(1+a),\quad Z(a)=[I-G_{\rm time}(a)F]^{1/2},\quad R(a)=g(a)F[I-G_{\rm time}(a)F]^{-1}.
$$

The positive rate acts on the whole fibre; $Z(a)$ is invertible for every cut. The no-jump propagator from $a$ to $b$ is $Z(b)Z(a)^{-1}$. Intervening survivor controls can be identity TP controls. From a current surviving operator $Y$ the CP density to each separately labelled failure component is

$$
Y\longmapsto w_\ell g(a)\operatorname{tr}\bigl(FZ(a)^{-1}YZ(a)^{-1}\bigr)P_f,
\qquad\ell\in\{0,1,2,3,13\}.
\tag{13}
$$

Pullback through the no-jump path gives $w_\ell g(a)\operatorname{tr}(FY)P_f$ from the initial decoder input. Accumulated jump effect $G_{\rm time}(a)F$ plus survivor effect $I-G_{\rm time}(a)F$ is identity at every cut; the same identity conjugated by $Z(a)^{-1}$ gives TP from any intermediate cut. Thus survivor plus stopped outputs are a chronological TP instrument, although the survivor branch alone decreases trace.

On terminal survivors only, use the isometry $EB(I-F)^{-1/2}$, whose composition with $Z(1)$ gives $EB$. For each eigenvalue $f$ of $F$,

$$
\int_0^1\frac{g(a)f}{1-G_{\rm time}(a)f}\,da=-\log(1-f).
$$

Hence $\int\|R(a)\|da=\log(1+b_h/c(h))\le\log(1+t)$, with equality for the three saturated labels and zero on the four pure labels. The terminal survivor effect is at least $(1+t)^{-1}I_2>0$. The failure law has no deadline atom, its FIRST time is **absolute $6+a$**, and no stopped carrier receives terminal or later processing.

For the high outcome choose fixed isometries $W_\perp:\mathbb C^2\to P^\perp$, $J_0:\mathbb C^2\to\mathbb C^3$. Use the single encoder

$$
C_H=\begin{pmatrix}\sqrt{1-\delta}\,DE^\dagger\\W_\perp^\dagger\end{pmatrix}:\mathbb C^5\to\mathbb C^3\oplus\mathbb C^2.
$$

Its entire **dimension-five** fibre is counted. Its rate is zero and its report is plus. Two hidden terminal Kraus matrices $E[I_3\ 0]$ and $EJ_0[0\ I_2]$ have effects summing to $I_5$ on this fibre. They do not create another readable outcome or an uncounted complement. This is the allowed JR coherent completion, distinct from a fixed certain-failure complement.

The joint moments give $\sum_iK_i^\dagger K_i=\delta D^\dagger D+T^\dagger T+S^\dagger S$ and $\sum_iN_i=M$. Source-root TP and $W_\perp W_\perp^\dagger=I_5-P$ make all eight encoder effects sum to $I_5$. Moreover cross terms cancel as Kraus maps. For **every complex** $X\in M_5$ the forgotten-label maps are exactly

$$
\Phi^L(X)=E[\Lambda_*(E^\dagger XE)+J_0W_\perp^\dagger XW_\perp J_0^\dagger]E^\dagger,
$$

$$
\Phi^f_\ell(\mathcal B)(X)=w_\ell\left(\int_{\mathcal B}g(a)\,da\right)\operatorname{tr}(EME^\dagger X)P_f.
\tag{14}
$$

The same composed Kraus identities tensor with the identity on every passive reference. In particular the conditional failure operator is exactly

$$
w_\ell\left(\int_{\mathcal B}g(a)\,da\right)P_f\otimes\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
$$

It is not replaced by the unconditioned reference marginal. Equality of CP densities proves equality on every Borel set, and the live Kraus identities preserve all supported off-diagonal coherences. All five failure components, including both zero measures, remain separate.

On all twelve original histories the complement has probability zero. Convention 2.2 therefore transfers exactly the original complete HALF error, with equality at $y=5,27$ and strict inequality at $y=16$. The acquisition effect of low label $i$ is $E(K_i^\dagger K_i+N_i)E^\dagger$, including later-failure mass. Only the one high fibre has dimension at least three. Its history-$y$ acquired mass is $(1-\delta)A_y$, maximized at $27$; Convention 2.3 identifies this with the sharp joint cost. Low reports are $\sigma_i=\operatorname{sign}z_i$. The high supported effect is diagonal, and the plus low effects have $01$ entry $\kappa s_0\sum_{z_i>0}p_iz_i$. Since $\sum p_iz_i=0$, this gives $\mathsf V=s_0\sum p_i|z_i|=s(t,\lambda)$. Every operation is fixed at the chosen parameter before the unknown input arrives. The construction therefore supplies one common simultaneous attainer, with the full resource and output accounting, for each parameter. ∎

## 10. Attribution, literature scopes and the continuing programme

The source/minimax, sharp cost/unaveraged equality face, actual-label rigidity/capacity and common construction are reused original interfaces, not new claims of this volume. The strip is a source presentation of a completed conditionally assessed mathematical result. Its numerical bounds are explicit finite inequalities; identities, filenames, hashes, worker authority and successful program exits are not mathematical substitutes for them. No pending draft or review is cited as published literature, and no novelty claim is made.

The proof uses the standard Banach contraction theorem, polynomial remainder theorem, Bernstein convex-hull identity, analytic implicit-function theorem, constrained positive Hessians and CP-map composition at the precise hypotheses established above. Relevant literature has the following narrower scopes. Martin–Goldsztejn–Granvilliers–Jermann, *On Continuation Methods for Non-Linear Bi-Objective Optimization: Towards a Certified Interval-Based Approach*, DOI [10.1007/s10898-014-0201-3](https://doi.org/10.1007/s10898-014-0201-3), §§3.1–3.3, treats regular certified continuation tubes and active-set conditions; it supplies neither all global components nor these whole-circle dual signs. Dritschel–Rovnyak, [arXiv:0903.3639v1](https://arxiv.org/abs/0903.3639v1), Theorem 2.1, factors an already nonnegative trigonometric polynomial; it does not select our contacts.

Di Dio–Schmüdgen, [arXiv:1703.01494v2](https://arxiv.org/abs/1703.01494v2), §3, Definitions 22/26, Proposition 23, Theorems 25/27 and Proposition 30, gives moment-map rank/Sard and atom-number conclusions under their stated smoothness hypotheses. Ambient measure-zero or genericity statements do not prove a seven-atom theorem on the actual two-parameter optimal target. Their [arXiv:1809.00584v1](https://arxiv.org/abs/1809.00584v1), Theorem 19, Theorems 52/54 and Lemma 55, supplies finite moment representations and connected-normalized-image refinements under the corresponding hypotheses. Applied to the ten original moment/contrast/height coordinates, such a bound gives at most nine low atoms, not seven. An exposed equality subset need not inherit the ambient cylinder's connectedness. Eight pure-sheet evaluation columns of (4) have three zero rows, so an ordinary eight-function Chebyshev hypothesis is also unavailable. Leppäjärvi–Sedlák, [arXiv:2212.11225v2](https://arxiv.org/abs/2212.11225v2), §6.1, Definition 7, describes CP postprocessing per output; it does not replace the full Borel/reference identities (13)–(14). None of these general results is invoked as an unproved complete-class or native bridge.

The full original programme remains **NOT_COMPLETE**. This strip removes only its stated region from possible nine- or ten-total-label obstructions. It does not settle the global maximum $M\in\{8,9,10\}$, a universal seven-original-fractional-low-optimizer theorem, exact strong optimal counts, the whole finite $(s,A)$ frontier, all branches, maximal continuation ranges, every contact/height-sign/unused-zero/collision/rank/capacity/weight/count degeneracy, or all global ordering and gluing. Existing limiting, precontact/contact $K(s)$, orientation/coefficient, transition-root multiplicity/sign/next-term, critical five-label/static-contact interpolation and uniform joint-limit obligations retain their original credited scopes. No unassessed coefficient assertion is an antecedent here. Classical literal-read or atom counts and common-source inverse-energy analogies have no proved quantum operation/resource/count bridge and are not transferred.

All native access and calibration, coherent storage and jointly counted future-accessible shares, acquisition duration, whole-fibre actuation, absolute FIRST clock alignment, archive/source/epoch/controller/permissions and quantum-native-count bridges remain unresolved. Source/minimax/sharp-cost/full-class hypotheses remain conditional. There is no kernel, native, physical, source-final, publication, global-$M=8$ or full-programme approval. This theorem does not narrow or terminate the original continuing programme.
## Appendix A. Exact source data and conventions

All JSON objects below are inert mathematical data. Array order is part of their schema. Rational strings mean exact fractions; integers in endpoint pairs use the explicitly declared scale. A field named `file`, `edge` or `cell` is a selector for the correspondingly named record in the fixed-version dataset. `display`, decimal centres and rounded scalar summaries are orientation only. No path, hash or execution result is a proof premise.

Exact JSON data (1 record): [appendix-a-source-box.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-a-source-box.json).

The following common source enclosure has scale `D=2^224`. In `RC.coefficients`, `(g0,g1,g2,x,y,z)` denotes `(G00,G11,G22,G01,G02,G12)`; `RC.c` denotes the source amplitude. The `beta_direct`, `beta_cancelled` and `coefficients.beta` entries are alternative enclosures of the circle beta in (1); the cancelled-denominator entry is auxiliary and is not used in the strip proof. `box_derived.m` is ordered `(0,m1,m2)`.

Exact JSON data (1 record): [appendix-a-source-enclosures.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-a-source-enclosures.json).

Independent outward derived source bounds use scale `2^210=1645504557321206042154969182557350504982735865633579863348609024`. `high_acquired_probabilities` is ordered by heights `(5,16,27)`. The exact root identity for the omitted zero coordinate is a hypothesis, not an interval diagnostic.

Exact JSON data (1 record): [appendix-a-derived-enclosures.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-a-derived-enclosures.json).

## Appendix B. Complete root boxes, matrices, cover and leaves

The root schema is ordered exactly as the original numeric records: `parameters, scale, center, dyadic_center, radii, R, q_upper, q_exact, inclusion_upper, inclusion_exact, arcs, geometry, min_separation, saturated_wedge_squares, column_minor, k_lambda_diagnostic_enclosure, k_t_enclosure, s_t_enclosure, pure_tangent_witness, s_range`. The actual centre and radii are singleton endpoint pairs divided by `scale`; `center` is a decimal selection aid. `R` has 22 rows and 22 singleton pairs per row. Angles, weights, duals and residuals have §3 order. `geometry` has seven objects, each ordered `weight,signed_height,signed_report,curvature`; all interval pairs use that record's scale. The three saturated wedges have pair order `(3,4),(3,6),(4,6)`. The moment minor has row order `(0,1,2,3,4,5,7)` and column order `0..6`.

Each `arc` has fields `eta,epsilon,sigma,roots,quotient,leaves`. Coefficients in `quotient` ascend in power; every pair uses the record scale. Each leaf is ordered `a,b,lower,degree`, with exact rational endpoints and integer lower bound divided by that scale. No recorded zero-containing remainder is used. The field `k_lambda_diagnostic_enclosure` is retained as an auxiliary interval only; it can contain zero and is not the proof of strict response. Strict response uses (10) and the separate positive tangent.

### B.1. The complete rational parameter cover

Exact JSON data (1 record): [parameter-cover.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/parameter-cover.json).

### B.2.0000. cell-0000.json

Exact JSON data (1 record): [final-strip/cell-0000.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0000.json).

### B.2.0001. cell-0001.json

Exact JSON data (1 record): [final-strip/cell-0001.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0001.json).

### B.2.0002. cell-0002.json

Exact JSON data (1 record): [final-strip/cell-0002.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0002.json).

### B.2.0003. cell-0003.json

Exact JSON data (1 record): [final-strip/cell-0003.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0003.json).

### B.2.0004. cell-0004.json

Exact JSON data (1 record): [final-strip/cell-0004.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0004.json).

### B.2.0005. cell-0005.json

Exact JSON data (1 record): [final-strip/cell-0005.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0005.json).

### B.2.0006. cell-0006.json

Exact JSON data (1 record): [final-strip/cell-0006.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0006.json).

### B.2.0007. cell-0007.json

Exact JSON data (1 record): [final-strip/cell-0007.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0007.json).

### B.2.0008. cell-0008.json

Exact JSON data (1 record): [final-strip/cell-0008.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0008.json).

### B.2.0009. cell-0009.json

Exact JSON data (1 record): [final-strip/cell-0009.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0009.json).

### B.2.0010. cell-0010.json

Exact JSON data (1 record): [final-strip/cell-0010.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0010.json).

### B.2.0011. cell-0011.json

Exact JSON data (1 record): [final-strip/cell-0011.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0011.json).

### B.2.0012. cell-0012.json

Exact JSON data (1 record): [final-strip/cell-0012.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0012.json).

### B.2.0013. cell-0013.json

Exact JSON data (1 record): [final-strip/cell-0013.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0013.json).

### B.2.0014. cell-0014.json

Exact JSON data (1 record): [final-strip/cell-0014.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0014.json).

### B.2.0015. cell-0015.json

Exact JSON data (1 record): [final-strip/cell-0015.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0015.json).

### B.2.0016. cell-0016.json

Exact JSON data (1 record): [final-strip/cell-0016.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0016.json).

### B.2.0017. cell-0017.json

Exact JSON data (1 record): [final-strip/cell-0017.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0017.json).

### B.2.0018. cell-0018.json

Exact JSON data (1 record): [final-strip/cell-0018.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0018.json).

### B.2.0019. cell-0019.json

Exact JSON data (1 record): [final-strip/cell-0019.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0019.json).

### B.2.0020. cell-0020.json

Exact JSON data (1 record): [final-strip/cell-0020.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0020.json).

### B.2.0021. cell-0021.json

Exact JSON data (1 record): [final-strip/cell-0021.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0021.json).

### B.2.0022. cell-0022.json

Exact JSON data (1 record): [final-strip/cell-0022.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0022.json).

### B.2.0023. cell-0023.json

Exact JSON data (1 record): [final-strip/cell-0023.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0023.json).

### B.2.0024. cell-0024.json

Exact JSON data (1 record): [final-strip/cell-0024.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0024.json).

### B.2.0025. cell-0025.json

Exact JSON data (1 record): [final-strip/cell-0025.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0025.json).

### B.2.0026. cell-0026.json

Exact JSON data (1 record): [final-strip/cell-0026.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0026.json).

### B.2.0027. cell-0027.json

Exact JSON data (1 record): [final-strip/cell-0027.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0027.json).

### B.2.0028. cell-0028.json

Exact JSON data (1 record): [final-strip/cell-0028.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0028.json).

### B.2.0029. cell-0029.json

Exact JSON data (1 record): [final-strip/cell-0029.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0029.json).

### B.2.0030. cell-0030.json

Exact JSON data (1 record): [final-strip/cell-0030.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0030.json).

### B.2.0031. cell-0031.json

Exact JSON data (1 record): [final-strip/cell-0031.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0031.json).

### B.2.0032. cell-0032.json

Exact JSON data (1 record): [final-strip/cell-0032.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0032.json).

### B.2.0033. cell-0033.json

Exact JSON data (1 record): [final-strip/cell-0033.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0033.json).

### B.2.0034. cell-0034.json

Exact JSON data (1 record): [final-strip/cell-0034.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0034.json).

### B.2.0035. cell-0035.json

Exact JSON data (1 record): [final-strip/cell-0035.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0035.json).

### B.2.0036. cell-0036.json

Exact JSON data (1 record): [final-strip/cell-0036.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0036.json).

### B.2.0037. cell-0037.json

Exact JSON data (1 record): [final-strip/cell-0037.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0037.json).

### B.2.0038. cell-0038.json

Exact JSON data (1 record): [final-strip/cell-0038.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0038.json).

### B.2.0039. cell-0039.json

Exact JSON data (1 record): [final-strip/cell-0039.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0039.json).

### B.2.0040. cell-0040.json

Exact JSON data (1 record): [final-strip/cell-0040.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0040.json).

### B.2.0041. cell-0041.json

Exact JSON data (1 record): [final-strip/cell-0041.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0041.json).

### B.2.0042. cell-0042.json

Exact JSON data (1 record): [final-strip/cell-0042.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0042.json).

### B.2.0043. cell-0043.json

Exact JSON data (1 record): [final-strip/cell-0043.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0043.json).

### B.2.0044. cell-0044.json

Exact JSON data (1 record): [final-strip/cell-0044.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0044.json).

### B.2.0045. cell-0045.json

Exact JSON data (1 record): [final-strip/cell-0045.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0045.json).

### B.2.0046. cell-0046.json

Exact JSON data (1 record): [final-strip/cell-0046.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0046.json).

### B.2.0047. cell-0047.json

Exact JSON data (1 record): [final-strip/cell-0047.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0047.json).

### B.2.0048. cell-0048.json

Exact JSON data (1 record): [final-strip/cell-0048.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0048.json).

### B.2.0049. cell-0049.json

Exact JSON data (1 record): [final-strip/cell-0049.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/final-strip/cell-0049.json).

### B.3. Both uniform edges and both separate midpoint roots

The linked record is `edge-91.json`.

Exact JSON data (1 record): [edge-91.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/edge-91.json).

The linked record is `edge-23.json`.

Exact JSON data (1 record): [edge-23.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/edge-23.json).

The linked record is `edge-center-91.json`.

Exact JSON data (1 record): [edge-center-91.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/edge-center-91.json).

The linked record is `edge-center-23.json`.

Exact JSON data (1 record): [edge-center-23.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/edge-center-23.json).

### B.4. Original outward edge constants

Exact JSON data (1 record): [appendix-b-edge-constants.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-b-edge-constants.json).

## Appendix C. Exact independent enclosures and contracted-image bounds

All bare endpoint pairs in this appendix have scale `2^210`. Rational fractions are absolute, without additional scaling. The per-root records are in cell order `0..49` followed by edge order `91/20,23/5,1000 at 91/20,1000 at 23/5`. Their keys retain their mathematical input ordering. Decimal summaries do not replace exact endpoints; `degrees` and `leaves` describe the mathematical covers. The remainder-containment diagnostic is excluded because it proves no divisibility.

Exact JSON data (54 records): [appendix-c-independent-enclosures.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-c-independent-enclosures.json).

The following fifty records refer to the exact fixed-point images defined after (6), with the original 35 leaves per cell. `bernstein_lower`, `separation`, `wedge`, `weight_lower`, `signed_height_lower`, `curvature_lower` are absolute rational lower bounds; `T.dyadic` encloses the actual signed primal value on the same image.

Exact JSON data (50 records): [appendix-c-contracted-image-bounds.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-c-contracted-image-bounds.json).

The next records give both stronger uniform implicit edge derivatives, separate midpoint strengths, their integrated intervals, and strict box-identification margins. The margins are the minimum coordinate distance of a contained box from the outer box boundary, in ordinary variable units.

Exact JSON data (2 records): [appendix-c-edge-identification.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-c-edge-identification.json).

These exact common extrema summarize the preceding inequalities and the FA78 feasibility expressions.

Exact JSON data (1 record): [appendix-c-extrema.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-c-extrema.json).

## Appendix D. Direct rational evaluation bounds

These are additional mathematical interval enclosures for the written evaluation order in §§3–5, rather than execution receipts. For each cell `q,inclusion` are the absolute rational bounds from (6). Every inclusion here is strictly smaller than that cell's independent image factor in Appendix C. Thus Appendix C image contraction is valid using these bounds alone. Each `bernstein_lower` below is the absolute minimum enclosing control endpoint after double division on that contracted image and exact power-to-Bernstein conversion on all 35 original leaves. All fifty exceed `0.00016650`.

Exact JSON data (50 records): [appendix-d-direct-cell-bounds.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-d-direct-cell-bounds.json).

The next four contraction records apply respectively to both uniform edge boxes and both separate midpoint boxes, in Appendix B edge order.

Exact JSON data (4 records): [appendix-d-direct-edge-bounds.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-d-direct-edge-bounds.json).

The following direct contracted-image geometry records use scale `2^210`. `geometry_min` is ordered weight, signed height, signed report, angular curvature; separation and wedge entries are lower endpoints. The seven-column minor and tangent are endpoint pairs. For each `minor_preconditioner`, `midpoint_determinant` is the exact rational determinant of the integer-midpoint matrix and `inverse` encloses its exact inverse on the same grid, row by row. These give the explicit preconditioned determinant calculation of Lemma 4.2. `T` is the signed primal value interval.

Exact JSON data (50 records): [appendix-d-direct-cell-geometry.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-d-direct-cell-geometry.json).

The explicit fixed rational edge tangents use singleton integer pairs on scale `2^210`. `residual_norm` is the absolute rational `e` of (12), `q` is its whole-edge weighted bound, and `s_t` is the resulting whole-edge derivative enclosure. The tangent selection rule in §8 uses the original nine-coordinate source box and the displayed positive-pivot construction; these constants remove any need for an unspecified approximate solve. Their derivative intervals are contained in the rational outward bounds `(1.1638,2.3196)10^-7` and `(1.1544,2.3111)10^-7`, respectively. Integration with Appendix C midpoint intervals proves (11) independently of its tighter derivative displays.

Exact JSON data (2 records): [appendix-d-direct-edge-tangents.json](https://github.com/the-omega-institute/trureturing-experiments/blob/08cfceafd9500530ffa128764313472b003a72ab/experiments/theory/fib-native-complete-continuation/two-parameter-strip/appendix-d-direct-edge-tangents.json).

## 追加锚（本行以下为增补区）
