# Native complete-continuation saturated contact transitions

## 1. Original objects and conditional source

**Convention 1.1 (scope and mathematical status).** This continuation concerns the original weak finite-activity problem of [FA, §§67–72, 77–79][FA] and [RC, §§58, 67–76][RC]. Its new conclusions are a selected third-saturated-contact activation, an exact seven-to-eight change in the minimum total actual acquisition alphabet, a separate selected eight-output optimum, and their local persistence. The arguments are ordinary conditional mathematics, not Lean/kernel proofs or native realizations. The source, minimax and sharp-cost assumptions below remain assumptions. All terminating decimals in this volume, including matrix entries written in scientific notation, denote exact rational numbers. The certificate tables are part of the definitions and proofs, rather than external proof dependencies. The mathematical deductions specific to these selected roots are `repo-derived`; this attribution asserts no worldwide novelty.

**Definition 1.2 (one original unknown specimen and complete output).** Let the ambient Hilbert space have ordered orthonormal modes $(e_0,e_1,e_2,e_3,e_{13})$. Put

$$
E=((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2),\qquad P=EE^\dagger,
$$

$$
p_y=(y/128,(64-y)/128,1/2),\quad a_y=(\sqrt{p_{yi}})_{i=0}^2,
\quad U_{e,n}=\operatorname{diag}(e,n,1),\quad
\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^\dagger.
$$

There is one normalized reached-cut unknown input $E\rho_{y,e,n}E^\dagger$, where $y\in\{5,16,27\}$ and independently $e,n\in\{\pm1\}$. One fixed complex CPTP instrument acts on this input, without a history oracle, prior, helper specimen, copying, reset, retry, postselection, acceptance division or uncounted subsequently accessible quantum share. The output is the complete stopped classical–quantum output: the live operator retains its off-diagonal entries; each of the five failure components, in order $(0,1,2,3,13)$, is a separate CP Borel measure on relative time $a\in[0,1]$. The ideal failure density is

$$
w_\ell f_y(a)P_f,\qquad
w=(0,1/4,1/2,1/4,0),\qquad f_y(a)=\frac{6y}{(y+6a)^2}.
$$

For the ideal live operator, define the original CG.111 quantities

$$
d_y=\left(\frac y{128},\frac{y(58-y)}{128(y+6)},\frac y{2(y+6)}\right),\quad
\xi_y=(\sqrt{d_{yi}})_{i=0}^2,\quad
\mathsf B_{y,e,n}=U_{e,n}\xi_y\xi_y^TU_{e,n}^\dagger.
$$

Its physical live block is $E\mathsf B_{y,e,n}E^\dagger$, and $\operatorname{tr}\mathsf B_{y,e,n}=y/(y+6)$. Error is HALF the norm of the complete stopped output difference, including the live block, all five time measures, singular-time, wrong-support, abort and zero-target sectors, and the original passive-reference amplification. Thus a scalar equality of total failure probabilities is not an equality of outputs. The other outputs and completion on $P^\perp$ have the original JR freedoms; a particular fixed completion is not imposed on all competitors.

**Assumption 1.3 (fixed original source, with separate logical suppliers).** Use the isolated nine-coordinate source root of [CG, Proposition 13.2 and §§13–17][CG], the source correspondence of FA Convention 67.1 at revision `e35db6260a4bd66b11e6b36cbece55650c937e70`, and RC.2–RC.5. Its coordinate order is $(\lambda_{\rm CG},\alpha_1,\alpha_2,\beta_1,\beta_2,z_{\rm CG},\eta_0,\eta_1,\eta_2)$; its box has radius $10^{-24}$ in every coordinate and the following exact centres:

| Coordinate | Centre |
| --- | --- |
| $\lambda_{\rm CG}$ | $0.479508042205945691075728241615$ |
| $\alpha_1$ | $1.412018697539825943102823246594$ |
| $\alpha_2$ | $1.185897402486986028204155873343$ |
| $\beta_1$ | $0.413330945620125544606320492846$ |
| $\beta_2$ | $0.809647491041060318009094562763$ |
| $z_{\rm CG}$ | $0.066998926272600209516864472757$ |
| $\eta_0$ | $0.279795267654829218213193898783$ |
| $\eta_1$ | $0.199570407911600478528148253443$ |
| $\eta_2$ | $0.091392615490799158339482855657$ |

The source-root isolation, its positive pivots and exact ranks, and the derived source dictionary and TP identity are inherited source premises. Complete-output minimax identification and precisely CG17's averaged-live/preaverage consequences are a separate inherited premise. The original sharp worst-history jointly acquired cost and the unaveraged supported real equality-face bridge are further JR premises; they are not inferred from CG17 alone or from TP. No premise here recertifies any of these suppliers. In particular source-root identities hold at the isolated root, not at arbitrary off-root interval points.

At that root define

$$
D=\operatorname{diag}(h_0,h_1,h_2),\quad
T=ae_0e_1^T+be_1e_0^T,\quad
S=ce_0e_2^T+de_2e_0^T,\quad M=\operatorname{diag}(0,m_1,m_2),
$$

$$
D^\dagger D+T^\dagger T+S^\dagger S+M=I_3,\qquad
\Lambda_*=\operatorname{Ad}_D+\operatorname{Ad}_T+\operatorname{Ad}_S.
$$

The seven amplitudes and $m_1,m_2$ are positive; $D$ has rank three, $T,S,M$ have rank two and the three source live Kraus matrices are linearly independent. The adjugate/positive-pivot definitions in RC.5 specify them from the original root without inverting singular source matrices. The exact dyadic enclosures in §10 specify all source expressions used in the present certificates. Their input identity is SHA256 `210bd09d6dfad81d2179b4c91418b90f160aec604119a825b4063f82070039ed`, with recorded parent certificate identity `cfea57666a799df3d74adfbdc624c32705219e214cfb85840b5d3d125ad5d346`. These identities bind the assumed data; they do not prove source isolation, minimax or cost.

**Definition 1.4 (actual acquisition class).** An actual generated acquisition label $j$ has a CP encoder $\mathcal E_j$ and full-output TP decoder. Its fibre contains jointly every subsequently accessible input-bearing specimen, memory, controller, environment or entanglement share. A discarded Kraus index is not an actual label. A low fibre has dimension at most two; a high fibre has dimension at least three. The cost $\mathsf W$ is the maximum, over the twelve original histories, of the probability of acquiring a high fibre, including mass that later fails. It is not expected dimension or postselected cost.

On each entire fibre a positive absorbing first-event rate $R_j(a)$ has integrable operator norm. Controls on not-yet-failed survivors are TP; terminal processing on survivors is TP. Trace balance is

$$
-\frac{d}{da}\operatorname{tr}\mathcal S_{j,a}(X)
=\operatorname{tr}(R_j(a)\mathcal S_{j,a}(X)),\quad
\mathcal S_{j,0}=\mathrm{id}.
$$

The uniform activity is $\mathsf A=\max_j\int_0^1\|R_j(a)\|\,da$, using supremum or essential supremum in the stipulated extensions. It is neither expected activity nor the integral of the cross-label maximum. Finite activity requires positive terminal survival on every nonzero positive decoder input. First failure is actual FIRST at absolute time $6+a$; there is no forced terminal absorption, singular first-event atom or subsequent positive-carrier action.

The domain is finite/countable instruments and only CG Convention 21.3's expressly stipulated measurable finite-dimensional-fibre, measurable-Kraus, integrable-effect/live-Choi extension, with full-output TP decoders almost everywhere. No general disintegration or infinite-dimensional coding theorem is assumed. Let $F$ be the supported plus-report effect and $\kappa=h_0a+h_1b$. Define $\mathsf V(F)=2|\operatorname{Re}F_{01}|/\kappa$. The original class $\mathfrak F_{s,A}$ imposes $E(\Phi)=E_*$, the inequality $\mathsf V(F)\ge s$, $\mathsf W=\mathsf C(s)$ and $\mathsf A\le A$. Its weak acquired-record height frontier is

$$
\mathcal T_A(s)=\sup_{\Phi\in\mathfrak F_{s,A}}
\frac12\sum_{j\ \mathrm{actual}}
\left|\Pr_\Phi(j\mid27,+,+)-\Pr_\Phi(j\mid5,+,+)\right|.
$$

For integral labels the last expression is the corresponding total variation integral. Empty classes have no claimed optimum.

## 2. Physical dictionary and the two-sheet equations

**Definition 2.1 (normalized null circle and physical failure).** Put

$$
\theta=\frac{ab}{h_0h_1},\quad\omega=\frac{cd}{h_0h_2},\quad
\delta=\theta+\omega\in(0,1),\quad s_0=\sqrt\delta,\quad
\alpha=\theta/\delta,\quad\beta=\omega/\delta=1-\alpha.
$$

Let $\Delta=\rho_{27,+,+}-\rho_{5,+,+}$, $(K_0,K_1,K_2)=(D,T,S)$,

$$
N_{ij}=\operatorname{tr}(K_i\Delta K_j^\dagger),\quad
L=\operatorname{diag}(s_0,1,1),\quad G=LNL,\quad
H_{\rm high}=(1-\delta)N_{00}>0.
$$

In particular $\Delta_{11}=-11/64$, $\Delta_{22}=0$ and $\Delta_{12}=(\sqrt{37}-\sqrt{59})/16$. The other entries are $\Delta_{ij}=\sqrt{p_{27,i}p_{27,j}}-\sqrt{p_{5,i}p_{5,j}}$. Writing $G_{00}=g_0$, $G_{11}=g_1$, $G_{22}=g_2$, $G_{01}=g_x$, $G_{02}=g_y$, $G_{12}=g_z$, the explicit coefficient correspondence is

$$
\begin{aligned}
N_{00}&=\sum_i h_i^2\Delta_{ii},&g_0&=\delta N_{00},\\
g_1&=b^2\Delta_{00}+a^2\Delta_{11},&g_2&=d^2\Delta_{00}+c^2\Delta_{22},\\
g_x&=s_0(h_0a+h_1b)\Delta_{01},&g_y&=s_0(h_0c+h_2d)\Delta_{02},\\
g_z&=ac\Delta_{12}.&&
\end{aligned}
$$

For $u=\cos\phi$, $v=\sin\phi$ put $z=u/\sqrt\alpha$, $w=v/\sqrt\beta$, $h=(1,z,w)^T$ and

$$
\overline K_h=s_0D+zT+wS,\quad\ell(h)=h^TGh,\quad
n_h=(0,dw/h_2,-bz/h_1)^T,\quad f(h)=n_h^T\Delta n_h,
$$

$$
\operatorname{cap}(h)=
\frac{h_1^2h_2^2\delta+a^2h_2^2z^2+c^2h_1^2w^2}
{h_0^2\delta+b^2z^2+d^2w^2}>0.
$$

The circle identity $\alpha z^2+\beta w^2=1$ is exactly the rank-two null equation for $\overline K_h$. Both capacity numerator and denominator have positive constant terms. Set

$$
V=\frac{m_2h_1^2}{b^2},\quad W=\frac{m_1h_2^2}{d^2},\quad
\mu=\alpha V+\beta W,\quad t=e^A-1.
$$

The scalar $V$ is a failure moment, distinct from contrast $\mathsf V$ and the height frontier. For $\eta\in\{0,1\}$ define

$$
\Gamma_\eta(\phi)=(1,u,v,u^2,uv,\eta\operatorname{cap},
\eta\operatorname{cap}u^2,\eta\operatorname{cap}uv)^T,
$$

$$
H_\eta(\phi;t)=\ell+\eta t\operatorname{cap}f,\qquad
B(t)=(1,0,0,\alpha,0,\mu/t,\alpha V/t,0)^T.
$$

The selected budget is $t=1000$, $A=\log1001$. The multiplier $\lambda$ below multiplies $|u|$, with physical contrast multiplier $\lambda\sqrt\alpha/s_0$. It is not $\lambda_{\rm CG}$.

**Assumption 2.2 (reused original-class reduction and actual-label rigidity).** At the original source and sharp-cost/error equality face, FA69–72 and corrected RC67/75 give each existing supported-nonzero actual low label its own $p_j>0$, circle direction $h_j$ and $b_j\in[0,t\operatorname{cap}(h_j)]$, with

$$
K_j=\sqrt{p_j}\overline K_{h_j},\quad
N_j=p_jb_j n_{h_j}n_{h_j}^T,\quad
\sum_jp_jh_jh_j^T=I_3,\quad \sum_jN_j=M,
$$

$$
\sum_jp_j|z_j|\ge s/s_0,\qquad
2T_{\rm actual}=H_{\rm high}+\sum_jp_j|\ell(h_j)+b_jf(h_j)|.
$$

The supported low encoder is onto a two-dimensional fibre and the live decoder is injective; both supported CP maps have Kraus rank one. Distinct supported live directions cannot occupy the same actual low label, even when the starting competitor is complex and multi-Kraus. These are equality consequences for the existing label, not permission to read or refine its hidden Kraus index. The high supported coefficient Gram is $\operatorname{diag}(1-\delta,0,0)$ and the low Gram is $\operatorname{diag}(\delta,1,1)$. The positive high mass is mandatory.

Supported-zero nonzero full-$M_5$ low labels remain admitted. Each encoder Kraus matrix then kills $E$, so all its supported live/failure maps, contrast and height contributions vanish. Such labels remain actual labels and count if generated. Finite whole-fibre positive survival excludes a nonzero supported encoder with failure-only composition, but does not exclude supported-zero labels. Necessity retains every admitted original time law and TP survivor control. At $t=0$ the capacity forces $M=0$, contrary to $m_1,m_2>0$, so this class is empty. These supplier statements are reused, not new claims of source, minimax, cost, survival or capacity certification.

**Definition 2.3 (whitening and auxiliary dictionary).** On failure support let

$$
M_2=\operatorname{diag}(m_1,m_2),\quad
\Delta_f=\begin{pmatrix}-11/64&\Delta_{12}\\\Delta_{12}&0\end{pmatrix},\quad
\Xi=M_2^{1/2}\Delta_fM_2^{1/2}
=\begin{pmatrix}-d_f&z_f\\z_f&0\end{pmatrix},
$$

$$
d_f=11m_1/64,\quad z_f=\sqrt{m_1m_2}\Delta_{12}<0,\quad
L_f=\sqrt{d_f^2+4z_f^2},\quad
\lambda_-^f=-(L_f+d_f)/2,\quad\lambda_+^f=(L_f-d_f)/2.
$$

If $e_\pm$ are unit eigenvectors of $\Xi$, their physical effects are $M_2^{1/2}e_\pm e_\pm^TM_2^{1/2}$. Conversely a physical effect $B_f$ is whitened as $M_2^{-1/2}B_fM_2^{-1/2}$. Bare eigenprojectors are not physical failure effects. The selected finite saturated directions below are not restricted to $e_\pm$.

For correspondence with FA's separate fixed-strength auxiliary family, let $L_0=\operatorname{diag}(\delta,1,1)$,

$$
r_\epsilon^{\rm aux}=\frac{dh_1}{bh_2}\sqrt{\frac{m_2}{m_1}}
\frac{(e_\epsilon)_2}{(e_\epsilon)_1},\quad
\mathbf c_\epsilon=(\sqrt{\theta(r_\epsilon^{\rm aux})^2+\omega},-r_\epsilon^{\rm aux},1)^T,
$$

$$
a_0=\left(4\sum_\epsilon\mathbf c_\epsilon^TL_0^{-1}\mathbf c_\epsilon\right)^{-1},\qquad
\nu_\star^{\rm aux}=\max_\epsilon
\frac{m_1h_2^2(e_\epsilon)_1^2}{a_0d^2\mathfrak c(\mathbf c_\epsilon)}.
$$

Here $\mathfrak c(x,z,w)=(h_1^2h_2^2x^2+a^2h_2^2z^2+c^2h_1^2w^2)/(h_0^2x^2+b^2z^2+d^2w^2)$ is FA69's homogeneous capacity. The family has two vectors $\sqrt{a_0}\mathbf c_\epsilon$ and a support-restricted null decomposition of the residual Gram into at most three vectors. This dictionary is credited to FA/JS and is not used to infer optimality of the seven contacts. In particular $\nu_\star^{\rm aux}$ is neither the radial constant $\nu=\mu/c_f$ nor a measure. Define $c_*(r)=\operatorname{cap}(1,\sqrt r,\sqrt{(1-\alpha r)/\beta})$, $u_f=V/\mu$, $c_f=c_*(u_f)$, $\nu=\mu/c_f$, $t_0=W/c_f$ and $q=\nu/t$. The reused FA78 feasibility boundary is

$$
\tau_{\max}(t)=q\sqrt{u_f}+\sqrt{(1-q)(1-qu_f)},\qquad \tau=s/s_0.
$$

## 3. Exact selected contacts and their rational certificates

**Definition 3.1 (charts and contact equations).** The seven indexed contacts have the following sheet, height sign, report sign and base chart:

| $i$ | $\eta_i$ | $\epsilon_i$ | $\sigma_i$ | $\phi_i^{\rm base}$ |
| --- | --- | --- | --- | --- |
| 0 | 0 | $+1$ | $+1$ | $0$ |
| 1 | 0 | $+1$ | $-1$ | $\pi$ |
| 2 | 0 | $-1$ | $-1$ | $\pi$ |
| 3 | 1 | $+1$ | $+1$ | $0$ |
| 4 | 1 | $-1$ | $+1$ | $3\pi/2$ |
| 5 | 0 | $+1$ | $+1$ | $0$ |
| 6 | 1 | $-1$ | $-1$ | $\pi$ |

Write $\phi_i=\phi_i^{\rm base}+2\arctan x_i$. Thus the exact centre entries $x_i$ in §11 are half-angle coordinates, not the angles $\phi_i$. Set $r=1+x^2$. The base-$0$, base-$\pi$ and base-$3\pi/2$ charts respectively use

$$
(U,V_v)=(1-x^2,2x),\quad(-1+x^2,-2x),\quad(2x,-1+x^2),
\qquad (u,v)=(U/r,V_v/r).
$$

Let $Z=U/\sqrt\alpha$, $W_n=V_v/\sqrt\beta$ and

$$
\begin{aligned}
D_c&=h_0^2\delta r^2+b^2Z^2+d^2W_n^2,\\
N_c&=h_1^2h_2^2\delta r^2+a^2h_2^2Z^2+c^2h_1^2W_n^2,\\
L_c&=(r,Z,W_n)G(r,Z,W_n)^T,\\
F_c&=-\frac{11}{64}(dW_n/h_2)^2
-\frac{2\Delta_{12}db}{h_1h_2}ZW_n.
\end{aligned}
$$

The numerator vector, positive denominator, height numerator and report numerator are

$$
\begin{aligned}
\Gamma^0_{\rm num}&=(r^2,rU,rV_v,U^2,UV_v,0,0,0)^T,&D^0_{\rm num}&=r^2,\\
H^0_{\rm num}&=L_c,&W^0_{\rm num}&=rU,\\
\Gamma^1_{\rm num}&=(D_cr^2,D_crU,D_crV_v,D_cU^2,D_cUV_v,N_cr^2,N_cU^2,N_cUV_v)^T,
\\D^1_{\rm num}&=D_cr^2,&H^1_{\rm num}&=D_cL_c+tN_cF_c,\quad W^1_{\rm num}=D_crU.
\end{aligned}
$$

Dividing gives $\Gamma_\eta,H_\eta,u$. For $\mathbf d=(d_0,\ldots,d_7)$ put

$$
P_i(x)=\mathbf d^T\Gamma^{\eta_i}_{\rm num}(x)
-\epsilon_iH^{\eta_i}_{\rm num}(x)-\lambda\sigma_iW^{\eta_i}_{\rm num}(x).
$$

The exact contact equations are $P_i(x_i)=P_i'(x_i)=0$, where the prime is local-$x$ differentiation. The denominators are strictly positive on every chart used here.

**Definition 3.2 (the two 22-dimensional systems).** At $t=1000$, the seam system $F_S$ has unknown order

$$
X_S=(x_0,\ldots,x_5,p_0,\ldots,p_5,d_0,\ldots,d_7,\lambda,x_6).
$$

Its first eight equations are $\sum_{i=0}^5p_i\Gamma_{\eta_i}(x_i)=B(1000)$, followed, in index order $i=0,\ldots,6$, by the fourteen equations $(P_i(x_i),P_i'(x_i))=(0,0)$. The weight $p_6$ is identically zero. The point system $F_8$, with external $\lambda=23/5$, has order

$$
X_8=(x_0,\ldots,x_6,p_0,\ldots,p_6,d_0,\ldots,d_7),
$$

the eight equations $\sum_{i=0}^6p_i\Gamma_{\eta_i}(x_i)=B(1000)$ and the same fourteen contacts. Select each zero in the full rational box $\prod_j[c_j-10^{-12},c_j+10^{-12}]$, using the complete centre tables in §11. No short decimal display replaces those boxes.

For an $n$-contact fixed-$\lambda$ system, moment derivatives are $\partial_{x_i}F_k=p_i\Gamma_{i,k}'$, $\partial_{p_i}F_k=\Gamma_{i,k}$. Contact-value and contact-derivative rows have $x_i$ entries $P_i'$ and $P_i''$, and $d_k$ entries $\Gamma_{{\rm num},i,k}$ and $\Gamma_{{\rm num},i,k}'$. A variable-$\lambda$ column has entries $-\sigma_iW_{{\rm num},i}$ and $-\sigma_iW_{{\rm num},i}'$. These formulas specify the complete analytic Jacobians, including off-root value derivatives. They are not set to zero inside interval boxes.

**Theorem 3.3 (unique selected real zeros).** Under Assumption 1.3's source enclosures, both boxes in Definition 3.2 contain a unique real zero. Their Jacobians are nonsingular. At the seam $p_0,\ldots,p_5>0$ and $p_6=0$ exactly; at the point all seven weights are positive.

Proof. The exact rational preconditioners $R_S,R_8$ in §12 and the interval data in §13 use the common grid $2^{-300}$. For a rational $q$, embed it with endpoints $\lfloor2^{300}q\rfloor$, $\lceil2^{300}q\rceil$; addition and negation are exact, multiplication encloses all four endpoint products with outward floor/ceiling, division uses a nonzero interval reciprocal, and square roots use integer-square-root floor/ceiling. Source intervals have denominator $2^{224}$. Thus every evaluation encloses the expressions for the assumed original source. Let $r_*=10^{-12}$, $c$ be the displayed centre and $J$ the Jacobian on its whole box. The row bounds in §13 enclose

$$
q_i=\sum_j\sup|(I-RJ)_{ij}|,\quad
RF(c),\quad q_i+\frac{\sup|(RF(c))_i|}{r_*}.
$$

They give respectively

$$
\begin{array}{c|cc}
&\max_iq_i&\max_i(q_i+\sup|(RF(c))_i|/r_*)\\
S&<7.889\cdot10^{-8}&<2.375\cdot10^{-6}\\
8&<6.132\cdot10^{-9}&<3.724\cdot10^{-7}.
\end{array}
$$

These are strict rational comparisons of the full table entries. For $\Psi(X)=X-RF(X)$, the mean-value formula yields $\|D\Psi\|_\infty<1$ and, coordinate by coordinate, $|\Psi_i(X)-c_i|<r_*$. Banach's contraction theorem therefore gives a unique fixed point in each closed box. Since $\|I-RJ\|<1$, the Neumann series makes $RJ$ invertible; for square matrices this implies both $R$ and $J$ invertible. A fixed point satisfies $RF(X)=0$, hence $F(X)=0$. Conversely every zero is a fixed point, proving uniqueness as a zero. This proof selects no other roots outside the boxes. Positivity of the occupied weights follows directly from their centre-radius intervals; the seam's seventh weight is excluded from its variables and is exactly zero. Source identities are used at the stipulated root only; no off-root TP assertion enters the contraction argument. $\square$

**Definition 3.4 (selected strength and value).** At either selected root put

$$
k=\sum_i p_i\sigma_i u_i=\sum_i p_i|u_i|,\quad
\tau=k/\sqrt\alpha,\quad s=s_0\tau,\quad
\mathcal V=\frac{H_{\rm high}+\mathbf d^TB(1000)-\lambda k}{2}.
$$

The signs and equality with the original optimum are proved below. The exact enclosures in §13 imply

| Selected root | Multiplier | Strength | Value |
| --- | --- | --- | --- |
| Seam $S$ | $4.52667157096<\lambda_S<4.52667157097$ | $0.124962083660<s_S<0.124962083663$ | $0.09965916109<\mathcal V_S<0.09965916113$ |
| Point $8$ | $\lambda=23/5$ | $0.124965524751<s_8<0.124965524755$ | $0.09960047739<\mathcal V_8<0.09960047743$ |

The geometry tables give $0<\tau_S,\tau_8<0.998$, while the reused feasibility formula gives $t_0<265$ and $\tau_{\max}(1000)>0.99892345794$. Both points are therefore strict weak feasible interior points, rather than minimum-budget boundary points.

## 4. Complete-circle inequalities and exact equality sets

**Theorem 4.1 (whole-circle two-sheet dual certificate).** At either selected root, for every $\phi\in\mathbb R$ and $\eta\in\{0,1\}$,

$$
\mathbf d^T\Gamma_\eta(\phi)\ge |H_\eta(\phi;1000)|+\lambda|\cos\phi|.
$$

The equality set consists exactly of the seven sheet contacts in Definition 3.1. Their height and report signs are $\epsilon_i$ and $\sigma_i$, their angular curvatures are positive, and no two circle directions coincide. The three saturated physical failure lines at indices $3,4,6$ are pairwise distinct.

Proof. On $u\ge0$ use the base-$0$ chart $x\in[-1,1]$; on $u\le0$ use the base-$\pi$ chart with the same closed interval. These two arcs cover the circle, including both $u=0$ axes and the point missed by a single unbounded half-angle chart. For the eight lexicographically ordered cases $(\eta,\epsilon,\sigma)$, with $\epsilon,\sigma\in\{-1,+1\}$, the report sign chooses its corresponding hemisphere. Clear the positive denominators from $\mathbf d^T\Gamma_\eta-\epsilon H_\eta-\lambda\sigma u$. The contact equations justify exactly the following factorizations:

| Case | Exact double factors removed | Quotient degree |
| --- | --- | --- |
| $(0,-1,-1)$ | $(x-x_2)^2$ | 2 |
| $(0,-1,+1)$ | none | 4 |
| $(0,+1,-1)$ | $(x-x_1)^2$ | 2 |
| $(0,+1,+1)$ | $(x-x_0)^2(x-x_5)^2$ | 0 |
| $(1,-1,-1)$ | $(x-x_6)^2$ | 6 |
| $(1,-1,+1)$ | $(x-(x_4-1)/(x_4+1))^2$ | 6 |
| $(1,+1,-1)$ | none | 8 |
| $(1,+1,+1)$ | $(x-x_3)^2$ | 6 |

The converted root for contact 4 follows from $\tan(3\pi/4+\arctan x_4)=(x_4-1)/(x_4+1)$. At a zero the derivative of the positive denominator contributes zero, so stationarity is invariant under this chart change. Pairwise root separation permits successive exact divisions. If $P(x)=\sum_{j=0}^na_jx^j$ has an exact root $\xi$, the synthetic quotient has $q_{n-1}=a_n$, $q_j=a_{j+1}+\xi q_{j+1}$; its remainder is $P(\xi)=0$ by the equations, not by rounding. Applying this twice at each listed contact yields the exact quotient, enclosed coefficientwise by §14.

For a quotient $Q(x)=\sum_{j=0}^nq_jx^j$, substitute $x=2y-1$ and write

$$
c_j=2^j\sum_{k=j}^n(-1)^{k-j}\binom{k}{j}q_k,\qquad
b_i=\sum_{j=0}^i\frac{\binom{i}{j}}{\binom{n}{j}}c_j.
$$

Then $Q(2y-1)=\sum_{i=0}^nb_i\binom ni y^i(1-y)^{n-i}$. The Bernstein functions are nonnegative on $[0,1]$ and sum to one. Midpoint subdivision uses $b_i^{(0)}=b_i$ and $b_i^{(r+1)}=(b_i^{(r)}+b_{i+1}^{(r)})/2$; the left controls are $(b_0^{(r)})_{r=0}^n$ and the right controls are $(b_{n-r}^{(r)})_{r=0}^n$. These exact formulas also propagate interval enclosures.

Section 14 gives every quotient coefficient interval, every covering leaf $(d,j)$, and every control interval on $[j/2^d,(j+1)/2^d]$. For each root the leaf counts are $(5,5,5,1,4,3,6,1)$, and their displayed rational endpoints form disjoint covers of $[0,1]$ with adjacent endpoints equal. Every lower control is strictly greater than $238/10^6$. Consequently every exact quotient is strictly positive on its entire closed arc. The only zeros of the cleared gaps are the factored double contacts. No numerical mesh or finite number of sampled angles is used to infer positivity. On the opposite hemisphere the other report sign reduces the right side by $2\lambda|u|$; it is weaker. At the two axes the strict quotient bounds give positive gaps, so they introduce no additional equality directions. Taking both height signs proves the absolute-value inequality everywhere.

The signed heights $\epsilon_iH_i$ exceed $0.00326$ and the angular second derivatives exceed $0.418$, as enclosed in §13. The angular curvature equals

$$
\frac{P_i''(x_i)}{D_{{\rm num},i}(x_i)}\frac{(1+x_i^2)^2}{4},
$$

because the value and first derivative vanish. Section 16 gives strictly positive signed report coordinates, pairwise squared circle distances exceeding $0.01644$ at the seam and $0.01657$ at the point, and nonzero pairwise saturated wedges $u_iv_j-u_jv_i$. The physical failure map $(u,v)\mapsto(dw/h_2,-bz/h_1)$ is an invertible linear map from the circle plane. Thus a nonzero circle wedge implies distinct physical failure projection lines, even after identifying opposite vectors. These strict comparisons establish precisely the geometric properties claimed. $\square$

## 5. Universal original optimum and one common joint law

**Theorem 5.1 (joint moments and a universal original-class bound).** The selected law has the complete live Gram and physical failure covariance of Assumption 2.2. For every original competitor in $\mathfrak F_{s,A}$, at $t=1000$ and for either selected dual pair,

$$
T_{\rm actual}\le
\frac{H_{\rm high}+\mathbf d^TB(1000)-\lambda\sqrt\alpha\,s/s_0}{2}.
$$

This includes every joint oriented failure allocation and every live-height decomposition, including decompositions below maximum contrast for a fixed allocation.

Proof. The first five moment equations give

$$
\sum p_i=1,\quad\sum p_iu_i=\sum p_iv_i=\sum p_iu_iv_i=0,
\quad\sum p_iu_i^2=\alpha,\quad\sum p_iv_i^2=\beta.
$$

After $z=u/\sqrt\alpha$, $w=v/\sqrt\beta$, they are exactly $\sum p_ih_ih_i^T=I_3$, with all mixed entries. The last three equations give

$$
t\sum p_i\eta_i\operatorname{cap}_i=\mu,\quad
t\sum p_i\eta_i\operatorname{cap}_iz_i^2=V,\quad
t\sum p_i\eta_i\operatorname{cap}_iz_iw_i=0.
$$

The circle identity gives $t\sum p_i\eta_i\operatorname{cap}_iw_i^2=W$. Congruence by $(z,w)\mapsto(dw/h_2,-bz/h_1)$ gives

$$
\sum p_i\eta_it\operatorname{cap}_i n_in_i^T
=\operatorname{diag}(0,d^2W/h_2^2,b^2V/h_1^2)=M.
$$

Thus both matrices come from the same weights and directions. There is no combination of independently attainable marginal optima.

Now take an arbitrary admitted competitor in Assumption 2.2, with its existing actual low labels. At each label let $r_j=b_j/(t\operatorname{cap}_j)\in[0,1]$. Convexity of absolute value gives

$$
|\ell_j+b_jf_j|\le(1-r_j)|H_0(h_j)|+r_j|H_1(h_j)|.
$$

Apply Theorem 4.1 to both endpoints and integrate with masses $p_j(1-r_j)$ and $p_jr_j$. Their first five moments are the competitor's live Gram; their last three moments are its full physical failure covariance. They therefore sum to the same $B(1000)$. The report coordinate is unchanged by endpoint splitting, so

$$
\sum_jp_j|\ell_j+b_jf_j|
\le\mathbf d^TB(1000)-\lambda\sum_jp_j|u_j|
\le\mathbf d^TB(1000)-\lambda\sqrt\alpha\,s/s_0.
$$

The final inequality uses original contrast $\mathsf V\ge s$ and $\lambda>0$. It does not impose maximal contrast at a chosen allocation. Adding the fixed positive high height and dividing by two proves the bound. Nonnegative slack has zero integral only if it vanishes almost everywhere in the stipulated measurable extension; the same argument holds for convergent countable sums. Supported-zero labels contribute zero supported height, and are not removed from the original class. Arbitrary complex/multi-Kraus competitors and every admitted time law enter through the explicitly inherited full-class reduction, without additional realness or single-Kraus restrictions. $\square$

**Theorem 5.2 (simultaneous CP/Borel/reference/error/resource/FIRST attainment).** At either selected root, one common original instrument attains Theorem 5.1 at strength $s$ from Definition 3.4. It has $\mathsf A=\log1001$, $\mathsf V=s$, $\mathsf W=\mathsf C(s)$, all twelve original errors, and the minimum counts stated in §6. Hence $\mathcal T_A(s)=\mathcal V$ at the two selected points.

Proof. For each occupied contact let

$$
K_i=\sqrt{p_i}\overline K_{h_i},\quad
N_i=p_i\eta_it\operatorname{cap}_i n_in_i^T.
$$

The rank-two property follows directly as well: the last two rows of $\overline K$ are $R_1=(zb,s_0h_1,0)$, $R_2=(wd,0,s_0h_2)$ and are independent. Row zero is $v_1R_1+v_2R_2$ with $v=(az/(s_0h_1),cw/(s_0h_2))$, by the circle equation. Thus $n=R^Tq$ for $q=(dw/(s_0h_1h_2),-bz/(s_0h_1h_2))$. On its row space,

$$
n^T(\overline K^\dagger\overline K)^+n
=q^T(I+vv^T)^{-1}q
=q^Tq-\frac{(q^Tv)^2}{1+v^Tv}
=\frac1{\operatorname{cap}(h)}.
$$

For the final equality expand the numerator and use $ab h_2z^2+cd h_1w^2=h_0h_1h_2\delta$. This is the row-space form of FA69's capacity identity, reused at these selected parameters.

Choose an isometry $J_i:\mathbb C^2\to\operatorname{ran}K_i^\dagger$ and set

$$
Q_i=J_i^\dagger(K_i^\dagger K_i+N_i)J_i,\quad
C_i=Q_i^{1/2}J_i^\dagger E^\dagger,\quad
B_i=K_iJ_iQ_i^{-1/2},\quad
F_i=Q_i^{-1/2}J_i^\dagger N_iJ_iQ_i^{-1/2}.
$$

Here $Q_i\succ0$, $B_i^\dagger B_i+F_i=I_2$, $I_2-F_i\succ0$, $B_iC_i=K_iE^\dagger$ and $C_i^\dagger F_iC_i=EN_iE^\dagger$. For a general ratio $b$, the one nonzero failure eigenvalue is $b/(\operatorname{cap}+b)$, because the preceding inverse metric gives the rank-one generalized eigenvalue $b/\operatorname{cap}$ of $(N,K^\dagger K)$ and normalization replaces it by $r/(1+r)$. Consequently a saturated label has $\lambda_{\max}(F_i)=t/(1+t)$; a pure label has $F_i=0$.

Use the FA70 first-event construction with

$$
g(a)=\frac2{(1+a)^2},\quad G_{\rm time}(a)=\frac{2a}{1+a},\quad
Z_i(a)=\sqrt{I-G_{\rm time}(a)F_i},\quad
R_i(a)=g(a)F_i(I-G_{\rm time}(a)F_i)^{-1}.
$$

On current survivor input $Y$, component $\ell$ has CP density

$$
\mathcal J_{i,\ell}(a)(Y)=w_\ell g(a)
\operatorname{tr}(F_iZ_i(a)^{-1}YZ_i(a)^{-1})P_f.
$$

Precomposition with $\operatorname{Ad}_{Z_i(a)}$ gives the initial-input density $w_\ell g(a)\operatorname{tr}(F_iY)P_f$. The survivor effect is $I-G_{\rm time}(a)F_i$ and the accumulated first-jump effect is $G_{\rm time}(a)F_i$, so every cut is TP on the whole fibre. Between cuts $Z_i(a)Z_i(b)^{-1}$ is contractive for $a\ge b$, and splitting the jump integral proves chronological consistency. At the terminal time apply to survivors only the isometry $EB_i(I-F_i)^{-1/2}$. Its effect is $I_2$ and the terminal live matrix after the no-jump path is $EB_i$. The prescribed terminal live CP map is therefore $\operatorname{Ad}_{EB_i}$, with whole-fibre effect $I_2-F_i$ before that final normalization. No absorbed carrier is acted on again; no terminal failure atom is present.

Since $F_i$ commutes with the path,

$$
\int_0^1\|R_i(a)\|\,da
=-\log(1-\lambda_{\max}(F_i))
=\begin{cases}0&\eta_i=0,\\\log(1+t)&\eta_i=1.\end{cases}
$$

The minimum terminal survivor eigenvalue on each saturated entire fibre is $1/(1+t)=1/1001$. These are entire-fibre statements. For general prescribed noncommuting laws the separate FA68 requirement is $\mathcal L_{\rm dec}^\dagger(I)=I-\int B(a)\,da\succ0$, and its minimum is the integral of $\|S(a)^{-1/2}B(a)S(a)^{-1/2}\|$. Endpoint coercivity alone does not replace that path requirement. The chosen $g$ here is one sufficiency witness, not a restriction on competing laws.

Choose typed isometries $W_\perp:\mathbb C^2\to P^\perp$ and $J_0:\mathbb C^2\to\mathbb C^3$. Use one high encoder

$$
C_H=\begin{pmatrix}\sqrt{1-\delta}DE^\dagger\\W_\perp^\dagger\end{pmatrix}
:\mathbb C^5\to\mathbb C^3\oplus\mathbb C^2.
$$

Its entire dimension-five fibre is counted. Its rate is zero, report is $+1$, and its terminal Kraus matrices are $E[I_3\ 0]$ and $EJ_0[0\ I_2]$. Their effects add to $I_5$ on that fibre. These indices are discarded, not two readable acquisition outcomes. This is the allowed original JR coherent complement completion, explicitly different from fixed CA10 certain-failure completion.

By Theorem 5.1,

$$
\sum_iK_i^\dagger K_i=\delta D^\dagger D+T^\dagger T+S^\dagger S,\quad
\sum_iN_i=M.
$$

The source-root TP identity consequently gives

$$
\sum_iC_i^\dagger C_i+C_H^\dagger C_H
=E(D^\dagger D+T^\dagger T+S^\dagger S+M)E^\dagger
+W_\perp W_\perp^\dagger=I_5.
$$

All acquisition branches are CP/TNI; every entire decoder is TP. The full coefficient Gram, including mixed terms, gives for every complex $X\in M_5$ the forgotten-label identities

$$
\Phi^L(X)=E[\Lambda_*(E^\dagger XE)+J_0W_\perp^\dagger XW_\perp J_0^\dagger]E^\dagger,
$$

$$
\Phi^f_\ell(B)(X)=w_\ell\left(\int_Bg(a)\,da\right)
\operatorname{tr}(EME^\dagger X)P_f,
\qquad \ell\in\{0,1,2,3,13\}.
$$

Tensoring the live Kraus matrices with $I_R$ gives the live identity for every passive reference. Each failure component becomes exactly

$$
w_\ell\left(\int_Bg(a)\,da\right)P_f\otimes
\operatorname{Tr}_5[(EME^\dagger\otimes I_R)X].
$$

This is equality of full CP/Borel components and their conditional reference operators, not just effects. Both zero measures remain separately labelled. The five failure components and actual acquisition labels are different coordinates of the output.

All twelve original inputs are supported on $P$, so the complement changes none of their outputs or errors. Under the inherited complete-output minimax identification,

$$
e_{5,e,n}=e_{27,e,n}=E_*,\qquad e_{16,e,n}<E_*
\quad(e,n\in\{\pm1\}).
$$

They are not all equal to $E_*$. For this constructed family the HALF error is the original expression $\tfrac12[\|\Lambda_*(a_ya_y^T)-\mathsf B_{y,+,+}\|_1+\int_0^1|q_yg(a)-f_y(a)|\,da]$, where $q_y=\operatorname{tr}(Ma_ya_y^T)$, with sign covariance for the other histories. Its minimax value is a supplier premise, not inferred anew from the moment equations.

Give low label $i$ report $\sigma_i=\operatorname{sgn}z_i$. Since $N_i$ kills coordinate zero, it changes no $01$ entry. The moment $\sum p_iz_i=0$ implies $\sum_{z_i>0}p_iz_i=\tfrac12\sum p_i|z_i|$, while $(K_i^\dagger K_i)_{01}=p_is_0\kappa z_i$. Thus the actual report effect gives $\mathsf V=s_0\sum p_i|z_i|=s$. Only the high fibre has dimension at least three. Its probability on history $y$ is $(1-\delta)A_y$, with

$$
A_y=h_0^2y/128+h_1^2(64-y)/128+h_2^2/2.
$$

The worst history is $27$, and the inherited sharp weak cost is $\mathsf C(s)=(1-\delta)A_{27}$. Acquired low effects are $K_i^\dagger K_i+N_i$, so every later-failure mass is counted before survival; there is no survival division. The original FIRST clock is $6+a$ throughout. All operations and reports are fixed before the sole unknown input, and the declared fibres omit no accessible share.

Finally each occupied contact has its verified height sign, so its equality equation gives $|H_i|=\mathbf d^T\Gamma_i-\lambda|u_i|$. Summing with the same weights yields $\sum p_i|H_i|=\mathbf d^TB-\lambda k$. The constructed actual TV is precisely $\mathcal V$, matching the universal bound at its own strength. This proves selected global optimality within the full original conditional class, not only within the seven-contact ansatz. $\square$

## 6. Equality rigidity and exact minimum actual alphabets

**Theorem 6.1 (unique merged endpoint law and sharp counts).** Every optimum at $(s_S,\log1001)$ has at least six supported-nonzero low actual labels and at least seven total actual labels; both minima are attained. Every optimum at $(s_8,\log1001)$ has at least seven supported-nonzero low actual labels and at least eight total actual labels; both minima are attained. Its supported law, after merging identical endpoints, is the unique law specified by Definition 3.2. This is not uniqueness of the whole instrument or of its failure-time CP law.

Proof. Every step in Theorem 5.1 has nonnegative slack. At an optimum matching Theorem 5.2 all slack vanishes, and $\lambda>0$ forces the contrast coordinate used by that proof to saturate. If $0<b_j<t\operatorname{cap}_j$, both endpoint chord masses are positive. Zero integrated dual slack would require the pure and saturated gaps both to vanish at the same circle direction. Theorem 4.1's two equality sets are disjoint, so this cannot occur. Every supported-nonzero optimal low label is therefore one of exactly seven pure/saturated endpoints. In the measurable extension this holds almost everywhere; finite cardinal minima are witnessed by the finite constructor.

The seven columns $\Gamma_i$ have a nonzero minor on zero-based rows $(0,1,2,3,4,5,7)$, with strict enclosures

$$
0.009593173233<\det\Gamma_{S,\rm minor}<0.009593173364,
$$

$$
0.009569506897<\det\Gamma_{8,\rm minor}<0.009569507027.
$$

The exact interval bounds are in §13. They can be obtained by Gaussian elimination with enclosed nonzero pivots; row swaps change the determinant sign and multiplying the pivots gives the enclosure. Thus the columns are linearly independent, and the eight moment equations admit at most one merged seven-endpoint weight vector. The seam's vector is its six strictly positive weights plus the identically zero seventh; the point's vector has seven strictly positive weights, the last exceeding $0.0001240025058$. No alternative optimizer can omit a required positive endpoint.

The inherited double rigidity applies to each existing actual label and forbids merging different directions into a single low label, even using hidden multi-Kraus multiplicity. Splitting or duplicating a direction can only increase the number of actual labels. Consequently the required low counts are six and seven. Mandatory positive high acquired mass needs a separate high actual label, as a label cannot simultaneously have low and high fibre dimension. The common dimension-five high constructor includes the entire complement in just one such label, giving exactly seven and eight total. Supported-zero outcomes remain admitted and counted but cannot replace a positive supported endpoint or the mandatory high label. Neither a classical failure-label count nor a hidden Kraus count nor a quantum dimension is substituted for this actual acquisition count. $\square$

## 7. Local third-saturated activation and value gluing

**Definition 7.1 (fixed-multiplier branches and tangent certificates).** The six-contact system $F_6(Y_6;t,\lambda)$ has order $Y_6=(x_0,\ldots,x_5,p_0,\ldots,p_5,d_0,\ldots,d_7)$, eight moments and twelve occupied contact equations. The seven-contact system $F_7(Y_7;t,\lambda)$ has order $Y_7=(x_0,\ldots,x_6,p_0,\ldots,p_6,d_0,\ldots,d_7)$, eight moments and fourteen contacts. At the seam embed the selected $X_S$ with $p_6=0$. The matrices $R_6,R_{7S}$ and $R_{7,8}$ in §12 are rational preconditioners for the two seam branch Jacobians and the point response respectively. Their coordinate orders are exactly those just specified; equation order is moments then contact value/derivative pairs.

For $Jv=b$ write $w=Rb$ and $q=\|I-RJ\|_\infty$. If $q<1$, the Neumann series gives

$$
\|J^{-1}b-w\|_\infty\le\frac{q}{1-q}\|w\|_\infty.
$$

For $v=\partial_\lambda Y$ the first eight entries of $b$ are zero and each contact pair is $(\sigma_iW_{{\rm num},i},\sigma_iW_{{\rm num},i}')$. This is $-\partial_\lambda F$. For the unused contact on the six-contact branch, track its stationary local-$x$ root near $x_6$ and let $P_{\rm unused}$ denote its cleared gap evaluated there. At the seam,

$$
\frac{dP_{\rm unused}}{d\lambda}
=\sum_{k=0}^7\Gamma_{{\rm num},6,k}\frac{dd_k}{d\lambda}
-\sigma_6W_{{\rm num},6};
$$

the moving angle contributes zero because its exact first derivative vanishes. If $k=\sum p_i\sigma_iu_i$, then

$$
\tau_\lambda=\frac1{\sqrt\alpha}\sum_i\sigma_i
\left((\partial_\lambda p_i)u_i+p_i u_i'(x_i)\partial_\lambda x_i\right).
$$

These formulas and all rational tangent enclosures are in §15; no finite-difference derivative is substituted.

**Theorem 7.2 (global optima on connected local sides of the seam).** There is $\varepsilon>0$ such that the original global optimum at $t=1000$ has minimum six supported low/seven total labels on a connected strength interval immediately below $s_S$ and at $s_S$, and minimum seven supported low/eight total labels on a connected interval immediately above $s_S$. The upper-side law has three distinct saturated physical failure lines. No maximal interval or ordering relative to earlier selected roots is asserted.

Proof. The exact tangent certificates give

$$
\|I-R_6J_6\|_\infty<2.836\cdot10^{-8},\qquad
\|I-R_{7S}J_{7S}\|_\infty<6.060\cdot10^{-9},
$$

$$
-0.003919<\partial_\lambda P_{\rm unused}<-0.003918,
\qquad0.0017109<\partial_\lambda p_6<0.0017111,
$$

$$
0.000336<\partial_\lambda\tau_6<0.000338,
\qquad0.000379<\partial_\lambda\tau_7<0.000380.
$$

Nonsingular $J_6$ gives the analytic six-contact branch by the implicit function theorem. The unused gap has positive second derivative, so a second implicit-function application to its stationary equation tracks its strict local minimum analytically. Its value is zero at the seam with negative derivative. It is therefore strictly positive just below $\lambda_S$ and strictly negative just above. All six old weights remain positive on a sufficiently small interval.

Whole-circle feasibility on the lower side needs more than these local derivatives. Take disjoint small neighborhoods of the seven seam equality directions on their appropriate sheet/sign cases. Around each occupied contact, the continued exact double factor and strictly positive second derivative give a nonnegative gap with precisely that zero. Around the unused contact the continued minimum is strictly positive on the lower side, and curvature stays positive. On the compact remainder of the two circles all seam gaps have a strictly positive minimum by Theorem 4.1. Continuity preserves that margin after shrinking the interval. The report axes are in this strict remainder. The other height/report cases have the same strict or weaker-sign bounds. Thus the six-contact dual is globally valid below the seam. Its moment law and common constructor match the bound, so it is an original global optimum there. The equality-set and independent-column arguments preserve its exact six-low/seven-total minimum.

Independently nonsingular $J_{7S}$ continues the seven-contact branch through the seam. Since $p_6=0$ and its derivative is positive, its seventh weight is positive on exactly the upper side locally; the other six weights remain positive. The seven exact contacts and their deflated positive quotients persist on their compact arcs, as do noncollision, nonzero height/report signs, curvature and the independent moment minor. Hence its two-sheet dual remains globally valid, and its own common constructor matches it. It gives an original global optimum and exact seven-low/eight-total minimum just above the seam. The six-contact dual's failure above the seam is not being used alone as an optimizer lower bound; the positive attaining seven-contact law and equality rigidity supply that bound.

Both $\tau_6'$ and $\tau_7'$ are positive, so each multiplier side maps monotonically to a nonempty connected strength side. Contact 6 activates a third distinct physical failure line; the wedge bounds exclude an antipodal coincidence, and the height and curvature bounds exclude a height-sign crossing or collision at this event. $\square$

**Theorem 7.3 (the value is locally $C^1$ and not $C^2$).** At fixed $A=\log1001$, the original global value across this local seam is $C^1$, has different finite one-sided second derivatives, and therefore is not $C^2$.

Proof. On either analytic branch let $V_{\rm low}=\sum p_i\epsilon_iH_i$. Differentiate its moment equation at fixed $t$, giving $\sum(p_i'\Gamma_i+p_i\Gamma_i'x_i')=0$. Contact values give $\epsilon_iH_i=\mathbf d^T\Gamma_i-\lambda\sigma_iu_i$, and contact stationarity gives $\epsilon_iH_i'=\mathbf d^T\Gamma_i'-\lambda\sigma_iu_i'$. Substitution into the differentiated height yields

$$
\frac{dV_{\rm low}}{d\lambda}=-\lambda\frac{dk}{d\lambda}.
$$

As $s=s_0k/\sqrt\alpha=s_0\tau$, the globally attained value satisfies

$$
\mathcal T_s=-\frac{\lambda\sqrt\alpha}{2s_0},\qquad
\mathcal T_{ss}=-\frac{\sqrt\alpha}{2\delta\tau_\lambda}.
$$

At the seam both laws have the same six positive weights and zero seventh, the same multiplier and dual values; their values and first derivatives agree. The analytic one-sided extensions and this agreement give $C^1$. The strictly positive, disjoint derivative intervals in Theorem 7.2 give distinct one-sided second derivatives by the last formula. Thus no common second derivative exists there. This is a local statement about the global optimum, not a claim that an entire branch or plane is everywhere $C^1$. $\square$

## 8. Budget persistence, open eight-output region and obstruction

**Theorem 8.1 (analytic persistence of the seam).** With the original source fixed, there is an open interval of $t$ containing $1000$ and analytic functions $X_S(t)$, $\lambda_S(t)$, $s_S(t)$ giving the same local third-saturated activation, exact seven-to-eight total count change and $C^1$/not-$C^2$ gluing at each such budget. No numerical width is asserted.

Proof. Replace $1000$ by external $t>0$ in $H_\eta$ and $B(t)$. All source expressions and charts are analytic on the positive domains; the only new division is by $t$, away from zero. The seam Jacobian from Theorem 3.3 is nonsingular, so the analytic implicit function theorem gives $X_S(t)$. Its value coordinate remains defined by its own moment equation, and $p_6=0$ remains identically enforced by the seam system. The strict weight, rank, sign, curvature, wedge, unused-gap crossing and positive/disjoint response inequalities persist near $1000$. Around exact moving contacts the positive double-factor quotients persist; off those neighborhoods compactness preserves the strict whole-circle margins. Shrinking the $t$ interval therefore supplies all hypotheses of Theorems 5–7 at every such budget. The local count change, analytic seam strength and gluing type follow. This proof gives existential neighborhoods, with no maximal continuation range. $\square$

**Theorem 8.2 (a nonempty open region in the original finite plane).** There is an open neighborhood $\mathcal U$ of $(s_8,\log1001)$ in the original $(s,A)$ plane on which every optimum has at least seven supported low/eight total labels and three distinct saturated physical failure lines. The exact minima are seven low/eight total. The global optimal value and the merged endpoint law are analytic on $\mathcal U$.

Proof. The nonsingular point system gives an analytic $Y_7(t,\lambda)$ near $(1000,23/5)$. Its seven weights are strictly positive at the seed. The exact additional point tangent certificate in §15 gives

$$
\|I-R_{7,8}J_{7,8}\|_\infty<6.132\cdot10^{-9},\qquad
0.0003694<\partial_\lambda\tau<0.0003697.
$$

For the map $\Psi(t,\lambda)=(A=\log(1+t),s=s_0\tau(t,\lambda))$,

$$
\det D\Psi=\frac{s_0\tau_\lambda}{1+t}>0
$$

at the seed. The analytic inverse-function theorem maps a sufficiently small neighborhood diffeomorphically onto an open neighborhood in the original finite plane; exchanging coordinate order to $(s,A)$ only changes the determinant sign. After shrinking, all seven weights, the independent minor, disjoint sheet zero sets, nonzero report/height signs, curvature, wedge separation and complete-arc quotient positivity remain strict. Thus the universal original-class inequality and common constructor persist, and Theorem 6.1 gives the exact counts and unique merged law throughout. Composing the analytic root, law and value with the analytic inverse gives the asserted analyticity in $(s,A)$. No connection of this neighborhood to the seam neighborhood, nor a quantitative width, follows. $\square$

**Theorem 8.3 (conditional obstruction to smaller universal optimum restrictions).** Under Assumptions 1.3 and 2.2, a rule that every feasible original finite-plane point has an optimum with at most two supported saturated physical failure lines is false. A rule that every such point has an optimum with at most seven total actual acquisition labels is also false. Both fail on the nonempty open set $\mathcal U$ of Theorem 8.2.

Proof. At its seed the unique merged optimal law has strictly positive weights on saturated contacts $3,4,6$ and seven positive low endpoints in total. The physical wedges exclude coincidence of those three lines. Theorem 6.1 forces every optimizer to use all three saturated endpoints and all seven low directions, plus a high actual label. Theorem 8.2 preserves these strict properties throughout $\mathcal U$. Thus these are obstructions for all optima at each such point, rather than merely constructions with unnecessarily many labels. Their scope is precisely the inherited original conditional model. They assert no obstruction for a different experiment or any unproved native implementation. $\square$

## 9. Attribution, transfer boundaries and remaining mathematical target

**Convention 9.1 (which facts are reused).** Source isolation/rank/TP, complete-output minimax and CG17 consequences, sharp joint cost/unaveraged real face, FA69 double rigidity and physical capacity, FA70/72 endpoint construction, and FA78 feasibility are distinct inherited premises at their stated scopes. The displayed constructors apply those suppliers to the new common moment laws; they do not receive separate new-theorem credit for the reused premises. Earlier selected pure-contact activation and the $\lambda=1/4$ seven-total optimum are scoped seeds, not connected intervals or ordering theorems for these roots. No unassessed coefficient expansion is a premise. The static sign/strict-decrease, limiting moment, critical-limit and earlier coefficient suppliers retain their own scopes; this continuation does not enlarge them.

**Convention 9.2 (authenticated literature interfaces).** The load-bearing sign proof is the elementary factor/Bernstein argument of Theorem 4.1; the local arguments use the ordinary analytic implicit and inverse function theorems and Banach contraction theorem. The following literature interfaces are `literature-attested` intermediate context, not proofs of contact selection or of the original-model bridge:

| Source and exact locator | Applicable interface and missing transfer |
| --- | --- |
| Dritschel–Rovnyak, *The Operator Fejér–Riesz Theorem*, [arXiv:0903.3639v1, Theorem 2.1](https://arxiv.org/abs/0903.3639v1) | An operator Laurent polynomial already nonnegative on the entire circle admits polynomial $P^*P$ factorization. It neither proves the required nonnegativity from selected zeros nor selects contacts. |
| Dette–Melas, *A note on the de la Garza phenomenon for locally optimal designs*, [arXiv:1105.3575v1, §3 Theorem 1](https://arxiv.org/abs/1105.3575v1), journal/PDF Theorem 3.1 | The stated Chebyshev-system hypotheses imply complete classes for information-matrix Loewner dominance. The unmodified eight-function two-sheet vector here fails its ordinary Chebyshev determinant condition on eight pure-sheet points: the last three functions are identically zero there. Loewner dominance has not been shown to preserve this absolute-height objective and physical failure covariance. |
| Goldsztejn et al., *Certified parametric continuation*, [§§3.1–3.3](https://pagesperso.ls2n.fr/~jermann-c/dw/mggj-jogo14.pdf) | Certified initial solutions, regularity, domain control and verified crossings are prerequisites for regular-curve continuation. They do not supply missing active-set changes or coverage of all components. |
| *Duality attainment and strict feasibility of the generalized moment problem and its relaxations*, [arXiv:2604.15072v1, Theorem 1.1](https://arxiv.org/abs/2604.15072v1) | The GMP dual-attainment assertion requires $h_1\equiv1$, $b_1>0$ and $b$ in the moment-cone relative interior. Attainment does not evaluate or select original contact branches. |

None of those unproved transfers is used in Theorems 3–8. The inspected literature scope is not exhaustive and supports no worldwide novelty or nonexistence assertion.

**Definition 9.3 (unchanged open target).** The original quantum-first AURIC FIB ATOM programme retains the complete evaluated original finite-$(s,A)$ frontier as its first mathematical target: every feasible point, joint oriented failure allocation and all live-height decompositions, selected roots/weights/contact ranges, universal necessity, one common original attainer, all transitions/gluing and exact minimum actual alphabets. An implicit SDP, fixed decomposition, fixed maximum-contrast facet, algorithm or isolated seed is not that evaluation.

The unresolved atlas includes global ordering and certified connected coverage from the earlier first activation to the later pure-contact seed and $\lambda=1/4$ point, onward to the present seam, and across the entire interval to $23/5$. In particular this seam is not asserted to be chronologically next. Maximal continuation ranges, all additional zero-height/sign/unused-root/zero-weight/collision/rank/capacity/count transitions, budget branches, endpoint/threshold and degenerate-orientation gluing remain unspecified. The precontact/contact coefficient $K(s)$ still requires its remaining evaluated source parameters, orientations and gluing beyond credited suppliers; mere coefficient existence is not its value or continuity. The limiting transition-root inventory, multiplicities/sign intervals, next terms, critical five-label/static-contact joint interpolation and uniform joint rates beyond the JS/WE/TC/SC scopes remain open. Limiting three-line structure gives no automatic finite-activity optimum support restriction. Weak feasibility counts, static support counts, exact finite-optimizer alphabets, hidden Kraus multiplicity and joint quantum dimension remain different questions. No strong-region count is transferred; the original strong fixed-source counts remain four at its two specified endpoint ratios and five at other feasible ratios, without a six-label strong region.

Native access/calibration, coherent jointly counted storage and accessible shares, acquisition duration, entire-fibre decoder actuation, alignment of the absolute FIRST clock, archive/source/epoch/controller and permissions, and every quantum/native-count bridge are separate unresolved premises. Mathematical control geometry supplies no actuator or permission. The through-2027 programme is not completed or narrowed by the selected roots, local transition, open set or small-alphabet obstruction proved here.


## 10. Complete source enclosure data

**Definition 10.1 (conditional dyadic input).** Every endpoint integer in this section is divided by $D_{\rm src}=2^{224}$. The row names are source dictionary names: `DeltaA` means $N_{00}$; `x,y,z` in the coefficient rows mean $g_x,g_y,g_z$. The cancelled and direct beta rows are enclosures of the same source ratio; their denominator row records its cancelled comparison denominator. They introduce no independent source parameters. These are enclosures of the fixed source expressions under Assumption 1.3, not independent choices of an off-root TP channel.

| Expression | Lower integer | Upper integer |
| --- | --- | --- |
| RC/DeltaA | $2178274649664917026219840788436610404284546028134588617028215950658$ | $2178274649664917026222049243107662090560048935982720049984373276804$ |
| RC/a | $1770311394972945197641994965733434776804318798358636960993665423441$ | $1770311394972945197642330191383860313598676849494811590399527112584$ |
| RC/b | $3935965654294995608601979521892857651473674590095072143984588712921$ | $3935965654294995608602313422828891500221393677289956783118602628225$ |
| RC/beta_cancelled | $3296842078597743037413473231959988404966987722955647639968047305372$ | $3296842078597743037414228158069975732764908643825242059562820404625$ |
| RC/beta_cancelled_denominator | $234633687557844213249748463929000961213455673673408373759120497001$ | $234633687557844213249770741572269232300046810020635897034911557353$ |
| RC/beta_direct | $3296842078597743037408846983351284754082692944506057606586721001861$ | $3296842078597743037418854406678679383649210729385024052454153059601$ |
| RC/c | $417790356983612701857377130657326048451791786364520663159403140999$ | $417790356983612701857967962172137068830255220590298423542851403047$ |
| RC/coefficients/beta | $3296842078597743037413473231959988404966987722955647639968047305372$ | $3296842078597743037414228158069975732764908643825242059562820404625$ |
| RC/coefficients/g0 | $34221372174431290786718999261791211913632513952393836659553436688$ | $34221372174431290786780685200389826628501112496695844777618146828$ |
| RC/coefficients/g1 | $78783570610947918076504457783823376875791541957489725211853654103$ | $78783570610947918076528781413699780090811566031886072291211212877$ |
| RC/coefficients/g2 | $45217132639885265280065628896983675495273546961325526453963593339$ | $45217132639885265280113507252983523546922593561790580491093661556$ |
| RC/coefficients/x | $63910117293406567136997332254455271417331233917251423202613394599$ | $63910117293406567137040175213816913730280255820235874754516426984$ |
| RC/coefficients/y | $59527865208926896968702198521424412882206778336312391207706909528$ | $59527865208926896968773639959878055405231936608490807444733614519$ |
| RC/coefficients/z | $-2740627279025051691705416351839235775900350270525561152827355761$ | $-2740627279025051691701021642264762102188060554422868821033090259$ |
| RC/d | $2663205433690388662341049091689729175826547547021472884789707223172$ | $2663205433690388662342459064972096088182130849082266016544667607076$ |
| RC/delta | $423549146495968554146011830551315873699107220910873798103439460242$ | $423549146495968554146345884167486240808334297711005281549257059179$ |
| RC/h/0 | $26537788820506109500788498850443291999899441414357450708533697655768$ | $26537788820506109500793183315073538792668688684001205079732940054331$ |
| RC/h/1 | $19041394653590742992836842417055357808127410672381937576282066738318$ | $19041394653590742992839410055472468226237891451663919566364482743060$ |
| RC/h/2 | $21824004785988993361054584934895991870094398276315525145506200547608$ | $21824004785988993361057348440025413753058042469208985303844669006803$ |
| RC/omega | $51794414349620443188334230846373069826950088927783643990123454218$ | $51794414349620443188450600275043575937037912978110040885162911192$ |
| RC/s0 | $3379180729178077789001472963110194729984725431101496002002178454791$ | $3379180729178077789002805544643664895183520534907765266655915068614$ |
| RC/theta | $371754732146348110957677599704942803872157131983090154113316006024$ | $371754732146348110957895283892442664871296384732895240664094147987$ |
| derived/m/0 | $0$ | $0$ |
| derived/m/1 | $13395056598782546673904842458375183527737029361412185934273944851861$ | $13395056598782546673906662453967195540019733666091401589339664139139$ |
| derived/m/2 | $9286998735773460367948153511490550124076700197961256553923028397389$ | $9286998735773460367951141007906400979909044212876537994791222399466$ |


## 11. Complete rational root boxes

**Definition 11.1 (box centres).** Every coordinate has the common radius $1/10^{12}$. Each entry below is the exact centre, not a rounded enclosure endpoint. Labels use the variable orders in Definition 3.2. The seam fixes $p_6=0$ outside its coordinate list; the point fixes external $\lambda=23/5$.

| Index | Seam coordinate | Seam centre | Point coordinate | Point centre |
| --- | --- | --- | --- | --- |
| 0 | $x_0$ | $0.1525526286139938996270995732246051530780792880984985794395001239329070430414$ | $x_0$ | $0.15266891620659142380752238430665002295210180174393875553910505170964463452494$ |
| 1 | $x_1$ | $-0.163668099389138096627793858737560752200318005206130088651259165577305658215528$ | $x_1$ | $-0.163608622540310502046102396173089653859527805956679710258110842372655504194404$ |
| 2 | $x_2$ | $0.1537461602432470532073428102721862744653560450119017580968840865235590632355$ | $x_2$ | $0.153833550209006642635600705243841200456074125638174352421939919611500279277625$ |
| 3 | $x_3$ | $0.218948915531468257687537331979129121988298582893893339549474615099416503510915$ | $x_3$ | $0.219341203105478410666114952210156967153277709074613276819848679149941001595811$ |
| 4 | $x_4$ | $0.34999791776474826719080866720860211125310419313678266277447906667872607930557$ | $x_4$ | $0.351147895566865210442654548923171385941836931324694456668904036369467341516272$ |
| 5 | $x_5$ | $-0.151342500138537763410511961840672056826366303808475218888332760857372769690067$ | $x_5$ | $-0.151478115683379664941088630328799167627701236297910003486108638414628817401771$ |
| 6 | $p_0$ | $0.237419686268866772652649054535323212837608036555581149031002107921216374627213$ | $x_6$ | $0.480066074916083173965238165203700856214156921173267058743182690242226639497868$ |
| 7 | $p_1$ | $0.249278084500729656412135268407102705429783954576267530759344192211485529097495$ | $p_0$ | $0.237359133546858811604144992626704809633810668806525924874098431082898650559182$ |
| 8 | $p_2$ | $0.24191769030080145516918786175820007695162127982718097333770602808742557769254$ | $p_1$ | $0.249382710059006473424933710847328214224771046473091573737208161026269837995001$ |
| 9 | $p_3$ | $0.0387490285880080131933856031238501971326850683579472025863971860705055318374755$ | $p_2$ | $0.241749246639475312580840604895693294626890992258297627740201544666373318876419$ |
| 10 | $p_4$ | $0.051340347361368398552307688893420897906683417851677239556584996129269727405842$ | $p_3$ | $0.0386918424096338608055210585004396767585757475126013905186353455511007881649598$ |
| 11 | $p_5$ | $0.181295162980225704020334523282102909741618242831345904728965489580097259339435$ | $p_4$ | $0.0512556701822173809151639665246403855227892988321860854445640348846809349673412$ |
| 12 | $d_0$ | $2.1769990082007216421190220694327908067328938857207745270370716889448245442538$ | $p_5$ | $0.181437394655946398768152477726100299480592972369518914006421880146921438811511$ |
| 13 | $d_1$ | $0.00332793917148978488579896638393796608197559242200617788578937103062873314727896$ | $p_6$ | $0.000124002506861761901243188879093319752569273747778483678870602641755030625586693$ |
| 14 | $d_2$ | $0.00727192110378663081092024400481887655408059143104534765092020347842086002234571$ | $d_0$ | $2.21184011063671078295349537147278555570613853015480561355837790929936773487205$ |
| 15 | $d_3$ | $2.36083420658169287728227384171036602665577864306797511524141563071399561560724$ | $d_1$ | $0.0033277061952244647710272862435125069704048838311159736205316406674821309402586$ |
| 16 | $d_4$ | $0.00498888437083694579086485934617778235250379825039659417318608795843226407229249$ | $d_2$ | $0.00727232197019650731235614716379900601378182918804500699476800235025288517299119$ |
| 17 | $d_5$ | $11.7672271556531373853306417498156855160445287443868252375356535330466190111231$ | $d_3$ | $2.39941629122969727202702961473823401378763620240915194864943901914689046342458$ |
| 18 | $d_6$ | $-4.60156092468028777941775734407145454467594438884773918963486157400927432723183$ | $d_4$ | $0.0049888944949794599540985435454591411836164437730932481032141070725424338997506$ |
| 19 | $d_7$ | $-15.3163598311567414363835303703069051656278461241587215551429797634635345031353$ | $d_5$ | $11.6861031391743104530257946829460690665576826514290510476798751534521125684433$ |
| 20 | $\lambda$ | $4.52667157096255576416861686424076325036238253963018948631874808210226934548773$ | $d_6$ | $-4.50376209943097130978369286136621660292000649304978261480685546783066311100555$ |
| 21 | $x_6$ | $0.481326958852706088437905684773152009573792351541059433188340267434287757118011$ | $d_7$ | $-15.3163223656877777198541456270062554691047616360817846902998557088917265892084$ |


## 12. Full rational preconditioner matrices

**Definition 12.1 (matrices).** $R_S$ acts on the 22 seam equations, $R_8$ on the 22 point equations, $R_6$ on the 20 fixed-multiplier six-contact equations, $R_{7S}$ on the 22 fixed-multiplier seven-contact equations at the seam, and $R_{7,8}$ on the 22 fixed-multiplier equations at the point. The separate point-response matrix is retained in full; its rational entries are not silently replaced by those of $R_8$.


### 12.1 Matrix $R_S$

The following table gives every entry; indices start at zero. The entries are exact rationals, with the coordinate and equation orders of Definitions 3.2 and 7.1.

| $i$ | $j$ | Entry |
| --- | --- | --- |
| 0 | 0 | $0.941125428667045666584025011880041997930479190133316113691601810659078780784702$ |
| 0 | 1 | $0.00410239811112193894983566872283624080376150550066461805476203356819994157616264$ |
| 0 | 2 | $-0.0107444872782288422900100742347489885445691005204335990012540332914873360734009$ |
| 0 | 3 | $-1.03649092151741694004091226714379982045755968865491680420215172479898560570573$ |
| 0 | 4 | $0.00880548909342418076107200782616307872101979274227721502706171640357435842569959$ |
| 0 | 5 | $-23.147747581905534207983748575966153964770377188051534292880741250718874117173$ |
| 0 | 6 | $32.0592534428378052872351165208149456155569410350641809285763581917411723970675$ |
| 0 | 7 | $-10.1636487312549401965419564569781286964270254057150803229317850633001516003323$ |
| 0 | 8 | $-1.88936330294028558852342229383853262763810953061002489743941461414721173295233$ |
| 0 | 9 | $0.435073396952801887183803885559326265163568351752619865374595838309428832419761$ |
| 0 | 10 | $-0.153342198210100998259368530959809514417848889313794106941074883609573554985798$ |
| 0 | 11 | $0.142826348183209820893762183764364902030607104420213778529210134926157602907049$ |
| 0 | 12 | $0.190962051729528073123098643759173030165439836593261361900312750558030409543026$ |
| 0 | 13 | $-0.15270967390508903507026997335276362203280928816737380820573219927486551813718$ |
| 0 | 14 | $0.457880033169972344225250462743139016761044798193367930101149716262263496331826$ |
| 0 | 15 | $0.0999839229823529742582214043907944536890286955583207691196034330363537801051739$ |
| 0 | 16 | $0.243824959388734594768816495819601105094143250273359098962706101352748976126603$ |
| 0 | 17 | $-0.0548205516863904965815219361273736326753322704739418168224946222339610035593334$ |
| 0 | 18 | $1.85187491269557998599504458324483301266329160130914128961982592060910635795244$ |
| 0 | 19 | $0.124472025127858306028722934624662069047632132757356419461335121157653208593778$ |
| 0 | 20 | $-0.401787683865971338725993022632297807576903599599069093070807890769662727602602$ |
| 0 | 21 | $1.75868540077612034375500629645289504247960462803735399707665470078034371003647\cdot10^{-87}$ |
| 1 | 0 | $-0.791406568070086696549735230677573614176780724053782535946125875639630455904936$ |
| 1 | 1 | $-0.0034497684485888386505118437592716080553207808803588218991491964810810066872487$ |
| 1 | 2 | $0.00903520141261011902635193463220164546315477790794201452797711609677156173627691$ |
| 1 | 3 | $0.871600849416750588361945723925122848734812450154729324890414524768257832326977$ |
| 1 | 4 | $-0.00740466859287342282821350205996093014957163468834055063864975265319385269875436$ |
| 1 | 5 | $2.16109946055017425190110406589933377228564405785311174684759471072881385334481$ |
| 1 | 6 | $0.322346364361491211841713275712028504776963310692768368727893841993931270100226$ |
| 1 | 7 | $-5.18642688688787374318908459720395710811512473341198055965107260517400885015959$ |
| 1 | 8 | $-0.0392219686636368571577181936898109776849048001685710197437896229777224060646117$ |
| 1 | 9 | $0.136561381583434804451897702105540200614222299289565142811206423452239044544676$ |
| 1 | 10 | $1.51843430557130511371446859432335857152590096373222588989496004095043203366288$ |
| 1 | 11 | $0.361730778697737417302925674602150183699948103579906613138472334018925940921301$ |
| 1 | 12 | $-1.499654671331047539562991501744623567003636080614733195504364745962535056521$ |
| 1 | 13 | $0.128415868124508202323814133158054965152155453068900551950014614343515652910595$ |
| 1 | 14 | $0.298049882445277072710571488009064123797162867154821374737095768847873749185904$ |
| 1 | 15 | $0.0319723854138697247599798798574406934151245672445230890012990158494570197236567$ |
| 1 | 16 | $0.177439975223958155275309526758864375951643211344403000222010630317304615327419$ |
| 1 | 17 | $-0.0505038189202091241139086499092688506798267003952504170801149262094805867060089$ |
| 1 | 18 | $0.0219880788872272986249291982120603031518951358260366594158360951987451858389539$ |
| 1 | 19 | $-0.104670403356004102399332924664421946329558594996391326556108881851166406563115$ |
| 1 | 20 | $-0.218265373621099531687075693978714803418379210800097554900803296415622723069422$ |
| 1 | 21 | $9.55380519355146404004647957250768126938129014933288891120345267814863174878355\cdot10^{-88}$ |
| 2 | 0 | $0.868854175113598690584986070992456144781711915341027991922730445726891948324442$ |
| 2 | 1 | $0.00378736523130059565134982505725140568370634642353010730245626050064035550197919$ |
| 2 | 2 | $-0.00991939261950043501844721757574959893507200287900403876238582859005138780430028$ |
| 2 | 3 | $-0.956896325607999094134436057211073607864114230318573878324284716589332206221751$ |
| 2 | 4 | $0.00812929470365585077648901166468735950148232291277227340110737211871961625265422$ |
| 2 | 5 | $-19.1554749707620043995022353422906025673104358945250078514613631790918703815245$ |
| 2 | 6 | $26.105690223716485850754834306880205687707307356857730318246754880686997704821$ |
| 2 | 7 | $-7.62549529936736237829624318192983153038552004375315051553568892034320403658073$ |
| 2 | 8 | $0.152676839833354000054755142782549870782543247313587974455272198172256535904702$ |
| 2 | 9 | $-0.14992537506656232420009349311760822774628960928356412986389474503189940991223$ |
| 2 | 10 | $1.60942312277998515486080466828737984129649133776624849794541497550584389778278$ |
| 2 | 11 | $0.131858374192451260398104972898814702174614205024457943829983849223245991073006$ |
| 2 | 12 | $-1.57424970712764034111336524067614029470750808139984712722783198794002567022439$ |
| 2 | 13 | $0.386376839450297000014487103892997678421151183815901204219119348952715952286141$ |
| 2 | 14 | $0.335292307571112297322764505223526996964447866758995058501685582192340242069956$ |
| 2 | 15 | $0.0774530433067523167208486998232041015323303688509995854068320838205867977200006$ |
| 2 | 16 | $0.176149303680066136338350231683385999827208734733722590297299440373354906090637$ |
| 2 | 17 | $-0.0382468433794662562993737540505823604200556772858805578679341451230829705405055$ |
| 2 | 18 | $-0.187940870789950739220523733277352783265098026450540146668300666501385799126497$ |
| 2 | 19 | $0.114913523131936766066646156926781912093288056385475629764388812965986231893735$ |
| 2 | 20 | $-0.299755741079643730929633416856133422249939852312202797312628599991004051014974$ |
| 2 | 21 | $1.31207617058628409383984437884966948665538909846207122200097835105623743790773\cdot10^{-87}$ |
| 3 | 0 | $-0.0231274666349370892981916984792722830252954873704782144159126312036873799119161$ |
| 3 | 1 | $-0.000100813422470776577659240068237294490629893584435402769465590792848055742536439$ |
| 3 | 2 | $0.000264037888540206608206638133705215390706470394151295756950219538481252273987209$ |
| 3 | 3 | $0.0254710036246294419424977398694062766980451653743130415344211223983874258975141$ |
| 3 | 4 | $-0.000216388431349587563714846238807518508379668342655439734814650739507964648657038$ |
| 3 | 5 | $-42.3854082206106336982703469284498385873166003007408440237335626998725142121335$ |
| 3 | 6 | $66.9330122637388288425598540981442673065158396250684691647427491427695701602479$ |
| 3 | 7 | $-33.8401827481074003270517679488470879783773973606448873075901357197395973570106$ |
| 3 | 8 | $-0.333030385356806034483371727625079375970630365135930922704689043739159531324762$ |
| 3 | 9 | $0.00399076647025262127683306639577880416943176011893554963932833701278997173822894$ |
| 3 | 10 | $-0.21748282349960148741975278400596715786691238009563382739689312984574038006904$ |
| 3 | 11 | $-0.00350985267380944750938229118109577911742800295133877054564916162618037967092457$ |
| 3 | 12 | $0.449191186467365019407820895102959332551974875369944867651248642581574751792446$ |
| 3 | 13 | $0.00375272814918441316703258423606737777590480960058417504293238014493703868862208$ |
| 3 | 14 | $2.35733213294846455203973133254838898361791989549160875147110515946200418245979$ |
| 3 | 15 | $0.612581447173382934259173358716505556427814974985763208858629338758028110161555$ |
| 3 | 16 | $1.19997186209857294229525134981097148406472727281035515063749072871292845645031$ |
| 3 | 17 | $-0.238451372580703215610695654111842226239275964027518518370909252664583036471791$ |
| 3 | 18 | $0.097684646773767992632522013350093381798488066941043120292587187085799924036421$ |
| 3 | 19 | $-0.00305880865657285045745676296977593392781525146639695637889134211969226497643996$ |
| 3 | 20 | $-2.1963993665853513018433684695432539257392817840307786325524774878559628109621$ |
| 3 | 21 | $9.61397189460920161604760873377874181136390148404697017445031374686438191239887\cdot10^{-87}$ |
| 4 | 0 | $-0.0318114664667977285695441815802881888230528739891696093757558143926826350971297$ |
| 4 | 1 | $-0.000138667276401453788894846123409505155058971361368769599409472748230249350005117$ |
| 4 | 2 | $0.000363179961292103132378178542760376248067111673695756880476703593452751010498955$ |
| 4 | 3 | $0.0350349647227060831747223310431525203415527964789241556376192948114667224344609$ |
| 4 | 4 | $-0.000297638882647082967496178252435023985685494208558643036099418924126450591635067$ |
| 4 | 5 | $-125.360426939070856727509981335725842821809022901874445787272351732253183014137$ |
| 4 | 6 | $197.790763833878674533598057551755499927636387629714471439911878407752034077436$ |
| 4 | 7 | $-99.7677007926997185617776071253132640215253071701450422022029745895163786863835$ |
| 4 | 8 | $-0.458078055129429807333968122061325907102580753262097014844061220536828390805184$ |
| 4 | 9 | $0.00548923648876803702041846377136208334762211399685420640468522305895994622545214$ |
| 4 | 10 | $-0.299144201830166476198960186580925348366079691733249787092499029162303125938833$ |
| 4 | 11 | $-0.00482774712849967549554299615600680764502318901830326616835744526534896804162414$ |
| 4 | 12 | $0.617855409372922771847099215305811356888430334951313363774810118372121675766984$ |
| 4 | 13 | $0.00516181852345422686617576314744631008073017534100996345560159322275340715790492$ |
| 4 | 14 | $3.24247325840316064786487719565526453889886099103375492534316710056296449085565$ |
| 4 | 15 | $0.842596142177571613527944959738583870800438081294659627005021656139711992397468$ |
| 4 | 16 | $1.65054241585563174498862923784333554322344830662613537496461285318464777209184$ |
| 4 | 17 | $-0.327986111170258987204880261860102209986654788139993779404926748270005904595634$ |
| 4 | 18 | $0.134363694658645621864472204962302807182533057895917312378805236137694374998496$ |
| 4 | 19 | $-0.00420734317955627346988539069399658845665587500872791264013560853135596561859159$ |
| 4 | 20 | $-3.02111277040074885464866965313284524739269883139802334852251470633833444136996$ |
| 4 | 21 | $1.32238670739705238013544864293961583685422965614412002389574858016455781083441\cdot10^{-86}$ |
| 5 | 0 | $-0.944261756359551782637631963613313147075723044264315252836570236162504627007044$ |
| 5 | 1 | $-0.00411606947139940995472071859086953491327861929756032835532546545053795903267535$ |
| 5 | 2 | $0.0107802935926328818942050921132615509590211764681913454111849939917015300212412$ |
| 5 | 3 | $1.03994505747120841669028122032441576586499452541213756182392643814145568134019$ |
| 5 | 4 | $-0.00883483364033423691966427367393805000806377686116829040453387843146589409800099$ |
| 5 | 5 | $25.3092730196798529241629763655839397510420426048126869731110153559681587813407$ |
| 5 | 6 | $-35.4522932186114888049582263042507647587840023149590984356748523380640072643814$ |
| 5 | 7 | $11.8517579155367114816100383710054537048138664755582308735405870128894981329528$ |
| 5 | 8 | $-2.03014168491008515913701182096662414505192756015641789232451927451250766355901$ |
| 5 | 9 | $0.162937351327922459763954990413396794746486378088024206994204875828368568912439$ |
| 5 | 10 | $-0.0145366439608635746455286666579328788889736512048848290015747891547189854906872$ |
| 5 | 11 | $-0.143302321116659267417207202476935047964120040852050480698980413931677405037232$ |
| 5 | 12 | $-0.0302998774625133824245513062754321876806316422610765562671139223282467364055817$ |
| 5 | 13 | $0.153218583307165719291559312072654574885391246476195091912752300638960912404299$ |
| 5 | 14 | $-0.541687649958726524266849580005601439387332447493191520305694895362330742815128$ |
| 5 | 15 | $-0.114296027934896883786578863429019900430165789798384593483771797368130828781545$ |
| 5 | 16 | $-0.290708857565184319881036729554939488284380411790341464779624524918886980394747$ |
| 5 | 17 | $0.0666396350756604895353448735744280704304380083098196638315122735642672480345988$ |
| 5 | 18 | $2.07464679524517021662040121610233561755862798773813004755826011073542379169179$ |
| 5 | 19 | $0.472582726629785328468741906125363032546841588358057187621335903313177318022271$ |
| 5 | 20 | $0.470116134877862370266020408094766581566465848459839769359159880119358624198865$ |
| 5 | 21 | $-2.05776935500789044062587547335132695854142809822088438213337642381063591249382\cdot10^{-87}$ |
| 6 | 0 | $0.0909903032019607025479372398364977262499072300950048295106392365679306788370941$ |
| 6 | 1 | $0.261156477138955746722345487019403189955852078337001639299240664466938811745365$ |
| 6 | 2 | $0.840499999343486083455417550729741941126733163408343406504281654074485664633462$ |
| 6 | 3 | $0.173104006014961133223459298999697572383080013525522487787878166042675513903581$ |
| 6 | 4 | $0.883364566604675319544552021555746595047444684768747460269972565108379016954917$ |
| 6 | 5 | $20.9515631514618546998522623791646994450292681209097125188094185161937799046131$ |
| 6 | 6 | $-33.8099721643689802721545725844105675619195230943945785125189188005384601306024$ |
| 6 | 7 | $-0.520514763728329420749398068392292183900361911943786298881578343607372921381659$ |
| 6 | 8 | $2.51007379312473645241513003954704250951990183802924810761355950074921452881046$ |
| 6 | 9 | $-0.374887696707853542583044916021522488430234713683828593025055093444616250586243$ |
| 6 | 10 | $0.291839985650273240285484054815411065311954275092558422435419065767354956252842$ |
| 6 | 11 | $0.0167231738672070976339990054721437924453541001463290964230514335556681749139961$ |
| 6 | 12 | $-0.349114991608013841871943594333043007411645373272784409987869107131708648106561$ |
| 6 | 13 | $0.0245485713833611092275026668528479057803057442830768671526839161727627087830958$ |
| 6 | 14 | $-0.575441835478928860135391802626837290345255083210570181494151787647883450614892$ |
| 6 | 15 | $-0.15565387148089737873167763566426421818640360785561996427298133950263114774402$ |
| 6 | 16 | $-0.289461568497950103590036761625496777602020122808678647584911213517144485340819$ |
| 6 | 17 | $0.055469349211320650382242675098529225667139883838105828094015603457616815306361$ |
| 6 | 18 | $-2.45164106136992990536597141255147390294593102440291443444635709210297757486182$ |
| 6 | 19 | $-0.361447037753507923808447365547000061150596797125305718454114401306221374633403$ |
| 6 | 20 | $0.54415296621620240007344198972892346277636246886945671868301448173180799977862$ |
| 6 | 21 | $-2.38183975244171841025899240833682624509979628817703327120929102791450292766385\cdot10^{-87}$ |
| 7 | 0 | $0.289655334240168429718103903795548909040691199980073369423523893190328375387966$ |
| 7 | 1 | $-0.254819831752991110902830018815914261628759215653431177819400586921400803647981$ |
| 7 | 2 | $0.809818957185801448085715256296345328640244116712473525827061157672809367322947$ |
| 7 | 3 | $-0.0509173491445421653050069199322033055779269815124394721312254651954370802195549$ |
| 7 | 4 | $-0.848534882048159320964362339139407055810285584066755377977564177459127959345112$ |
| 7 | 5 | $-2.250590144064906315589482178433255923689919096002999302471766587720701063677$ |
| 7 | 6 | $4.15782277139887097178853127413660110556797217258589677757804048095056710629974$ |
| 7 | 7 | $-3.63850958220488319472353031051183552878880793468010707828904437035167901716909$ |
| 7 | 8 | $0.248587358406626572621828994911694477431974302045790803788110958106659781420474$ |
| 7 | 9 | $-0.0499838765311451559896794207775975630848174851118405628683638764815173687607714$ |
| 7 | 10 | $2.21184100490723219026679327847370311983720071212523461063182352277082089597908$ |
| 7 | 11 | $0.325936835698283418480107605995740547257014087960081738186847586926663004791775$ |
| 7 | 12 | $-2.19825415032955424781992172478519765722670277069101272934742678381604173332429$ |
| 7 | 13 | $0.377680054493418529060305658474500171423194240676038264710742082812847700944102$ |
| 7 | 14 | $0.187238338087310184325428114579411101189792793166889370692703453227971045610924$ |
| 7 | 15 | $0.0128379292817202406198269141690628909864272802400753970067765411809805693691811$ |
| 7 | 16 | $0.115568681949290935588144498456460940120235707129287341950491579065861243041122$ |
| 7 | 17 | $-0.0349708174869495320282878876204552366759445649134278906666341215485385285599757$ |
| 7 | 18 | $-0.260883545902434008394374706999477470488515771332245694705426798112701671807592$ |
| 7 | 19 | $0.00647474558938143070028413313373305059057355273561121871277364826118369752554893$ |
| 7 | 20 | $-0.127645093382126372349149350813065993280817565001278997432152503672953531651874$ |
| 7 | 21 | $5.58721860391158651673698598396161593806484131114127833361795559394370629485313\cdot10^{-88}$ |
| 8 | 0 | $0.219212565206299562616688880867367248381005504712182220721100245731392811732841$ |
| 8 | 1 | $-0.269868507470241000840991104435380735884368290288704477090335841321447525065862$ |
| 8 | 2 | $-0.807673237893556268749552473467998565730598741334379584822443608365672933482941$ |
| 8 | 3 | $0.0422958629009215474153433484510157017266874893014694033645384462735815486753788$ |
| 8 | 4 | $0.845617392225199752753105447508570651307717434801700518090309072952036194467845$ |
| 8 | 5 | $-3.02924475692816708204206417085453040452537460367279342100944340712981417736718$ |
| 8 | 6 | $2.73826007454667438319353617063633108035888993112396041915840928562391453542096$ |
| 8 | 7 | $2.14845139495735539003643232243302296931714772412919593263714587256072656169403$ |
| 8 | 8 | $-0.224268705253087102156556873469172174560299106167718195026253121681724747665907$ |
| 8 | 9 | $0.00534633726932567110668150556805860364343529321631700128399234038284443365859589$ |
| 8 | 10 | $-2.20820844577983844429297274424896545606561389679333770797867032001726212930672$ |
| 8 | 11 | $-0.362831647896965144391528423186266010174218155535920586547521438285291278187784$ |
| 8 | 12 | $2.20134767050796665616830141547227878529906262302092428013698560410782156031172$ |
| 8 | 13 | $-0.338518521966306020780730724650412931285925109539889806015512974018254724062015$ |
| 8 | 14 | $-0.139156610308028142702285270019894786620273404271547178630720667155282095187543$ |
| 8 | 15 | $0.00534591648324133698217904225083520024499167237730687266617054582840627774551741$ |
| 8 | 16 | $-0.0943108282661896768249490293239086575458320139602023273951404470322816601549345$ |
| 8 | 17 | $0.0326535163169970647799073054187458785967732631029246762090218406088120181288502$ |
| 8 | 18 | $0.229513729477467377662596688930165670410484633384812731537619944597610269612266$ |
| 8 | 19 | $0.0275147436361720592087236224860469917640485204029507216998255153858556940043094$ |
| 8 | 20 | $0.0754106407897447267423067240794841405516612861232052943361728110091594922403771$ |
| 8 | 21 | $-3.30083768979680668275117080917449607441833701376083816337979460613160675241117\cdot10^{-88}$ |
| 9 | 0 | $-0.000985238014861760347115149803311710829828691611388201165648782545252330681355341$ |
| 9 | 1 | $-0.00000429468639148241409139206573163311040119874485350574527844459733642548034074125$ |
| 9 | 2 | $0.0000112481046566798571648705306536313304984612375523786481020854958715950538489915$ |
| 9 | 3 | $0.00108507349480973001197710942685633589129232082306828479083362086052733419516432$ |
| 9 | 4 | $-0.0000092182214294003189893515464858759373982839119319359821435466805912529532288255$ |
| 9 | 5 | $0.743621921351419708276315189301718081613806044886421626668672615684809867160136$ |
| 9 | 6 | $4.30817984145942779898260196769757452419620044491863616357615936050584829324639$ |
| 9 | 7 | $4.94979134648750120439766440811043877880434304511922188346421310003395530104568$ |
| 9 | 8 | $-0.014187208695911676819000914718836938470169469263678792810279355896135733880077$ |
| 9 | 9 | $0.000170008021068290356984877832288262684711913296447936016735679856260126162128488$ |
| 9 | 10 | $-0.0092648429105326792960749170937908135275621917532354503985319139455381023022369$ |
| 9 | 11 | $-0.000149520928313758140402625570102012396713607433517750172932089710270638369290174$ |
| 9 | 12 | $0.0191356986839172400578587106531558683317786756261798798016502511554099423036662$ |
| 9 | 13 | $0.0001598675069076953675591582466862369018872406168833596573995104564542165221726$ |
| 9 | 14 | $0.100423157784497317385943700375756960468112925266361252752767209119868655954032$ |
| 9 | 15 | $0.0260961798575259233252716535070304936143395701952194037973819616717845938742122$ |
| 9 | 16 | $0.0511192130969507716634267765345537300180396078110313049677704068214353578446386$ |
| 9 | 17 | $-0.0101581102967663229459780389849286528887112320669450242991968268166958518750869$ |
| 9 | 18 | $0.00416139947314732061793659217505744246405830465089278754134923703931475048164449$ |
| 9 | 19 | $-0.000130306298403270873483343327105564629781945029561648783485552460704164284313906$ |
| 9 | 20 | $-0.0935673667131880286627357081337095629440099123729559569228808554016380811636969$ |
| 9 | 21 | $4.09558501754478586718367015066671524989021363642480112636085622929287827994185\cdot10^{-88}$ |
| 10 | 0 | $0.00161633341863715508745059500172254537231329964903652628643835813778799295262089$ |
| 10 | 1 | $0.00000704565296142498760393798541423210560932925529591000269981411721013635692156299$ |
| 10 | 2 | $-0.0000184530917186247692270199962313635553991856889874093868714840166661267604153128$ |
| 10 | 3 | $-0.00178011863619011823224536596954915200574684287655331771690061336093540331068607$ |
| 10 | 4 | $0.0000151229643314438017326261630411332514550967990051386374810068346956822814506243$ |
| 10 | 5 | $15.5752129440955053091213035025767215272699082281268817112219858419196438385219$ |
| 10 | 6 | $-17.3079088395734303829155583131640393599172781515173585192863531352790944643973$ |
| 10 | 7 | $-3.39907477510923547587563967879070295394376189760301035718307267911528959356521$ |
| 10 | 8 | $0.0232748424101349779444078917883437063785315768059387955996270258675600589029301$ |
| 10 | 9 | $-0.000278906864883409140319825352301517311712743992876040778895110595765478901042728$ |
| 10 | 10 | $0.0151994492587851090091914756345858201713076516270904813654700263417801215684155$ |
| 10 | 11 | $0.000245296740050258239229714891051161404380951660271049271103071899274750995416554$ |
| 10 | 12 | $-0.0313930936537464324190741997814820774506470326368783318482446429294088284215829$ |
| 10 | 13 | $-0.000262270832094689817753867888791504468728324709954535356276524774032722519433723$ |
| 10 | 14 | $-0.164749333139495102539982529107638967026003065569055067525519628197932806759699$ |
| 10 | 15 | $-0.0428121194738951226587888411496380803254236034318242763838805377934561529028027$ |
| 10 | 16 | $-0.0838636869636307728210969124778181058402755264613682482119815028536071396067096$ |
| 10 | 17 | $0.016664900151228276328030170066248113367203887565563373584837369255829361794675$ |
| 10 | 18 | $-0.00682698894610844403859112738600641037193968552332881074241318843353157261965537$ |
| 10 | 19 | $0.000213774155677158010745494344990972460201885800803575551284970094425368968839908$ |
| 10 | 20 | $0.153502056793478098603438236130183278707743552462391564889248122309623181155594$ |
| 10 | 21 | $-6.71901696125287158276082987253289571884088902132499587168457458974915701856504\cdot10^{-88}$ |
| 11 | 0 | $0.399510701947795910376934530302175281785911457175091255223947048917812471770833$ |
| 11 | 1 | $0.263529111117706422447963090312209208562067297094691611353074394256035806091897$ |
| 11 | 2 | $-0.842638513648669317879518184092510971811477814335002316770129804860827566766902$ |
| 11 | 3 | $-0.163787474629960127113527470975817152417385999261067386095124154620411913243883$ |
| 11 | 4 | $-0.880452981524617794816038404541465447858933348390765803038054920755391681405871$ |
| 11 | 5 | $-31.990563115915706319618334721755352725697688694247223133218866978947718369251$ |
| 11 | 6 | $39.9136183165374375011054614851041002117137386972834436714926628087372246600326$ |
| 11 | 7 | $0.459856379597591496914471327151368918511440974978485918252336420479659669376265$ |
| 11 | 8 | $-2.54348007999249922400580913805907158029993914144958071916476500714557388758788$ |
| 11 | 9 | $0.419634134813488146249377778751074702498617736275780259371586060282794538427333$ |
| 11 | 10 | $-0.30140715112591941597242114758094373572728655029831035605551038091715574219138$ |
| 11 | 11 | $0.0200758625197381281785947223974325214641826232027564528394514356139559858558867$ |
| 11 | 12 | $0.358278866399430625884779392774288088458153877953571311244904678613927707237049$ |
| 11 | 13 | $-0.0636077005852866230568828910348298783507337913261541501490360106497771796679221$ |
| 11 | 14 | $0.591686283054644603666287786799202982333625834617921804204921420653258650997178$ |
| 11 | 15 | $0.154185965332305000463188866886973713666068688474842567186532828614915859657912$ |
| 11 | 16 | $0.300948188681528845984511428436208870849852348289930576273771177515736684216702$ |
| 11 | 17 | $-0.0596588378958301365159142239781393280664612375262209629220438649570238147948236$ |
| 11 | 18 | $2.48567646726785765951840396583173467093184354322278342081522789701228579919516$ |
| 11 | 19 | $0.327374080670680546762177458909334610965554783215501851273715820025460778419019$ |
| 11 | 20 | $-0.55185320370411082440730189099181532581093983008081862355340205597599906035902$ |
| 11 | 21 | $2.41554485540104899841812686304473230563021339692900872871784676517892084728198\cdot10^{-87}$ |
| 12 | 0 | $-0.721389904954910332268972286273982308382540453863557071962261093533496566122192$ |
| 12 | 1 | $-0.00314456340602869336287524794203746683460150708861171775161171098998143235725899$ |
| 12 | 2 | $0.00823584659423001156568774258575793875595568158754730004888828894472306325075443$ |
| 12 | 3 | $0.794489304596832318492392113320024988488463901145659100536093297774453134831279$ |
| 12 | 4 | $-0.00674956891684845498532942127645664701313744978968807291636814994267002992974493$ |
| 12 | 5 | $-3765.12635915164641916727128486685534544653594543497019019649285560386310839135$ |
| 12 | 6 | $5939.42578353252147626236858107628553618915632754578201987343935723294311960359$ |
| 12 | 7 | $-2994.42290214286247992428758685100342651307802334997642819173614659156927785075$ |
| 12 | 8 | $-14.8448490513533206733469571602316506032768641550776441737135889751992116708485$ |
| 12 | 9 | $0.124479636707110205979802257511256269441768075510771919631894414655120308359565$ |
| 12 | 10 | $-10.5725737240833554161945985276068759076657990128781510247614782794230209052963$ |
| 12 | 11 | $-0.109479015870257794786373520864766025490875625980247999902082049942184594295057$ |
| 12 | 12 | $23.3632031767279390372607121233340902033450979062524566857633109827741142159939$ |
| 12 | 13 | $0.117054766334510998818478940445358066182083233567163768131214385081818881505248$ |
| 12 | 14 | $148.978934578043534140175274034090531368148206810717024722283897562270776438594$ |
| 12 | 15 | $25.2931356394261783445332383418295617786288559971545614322439247097981710937761$ |
| 12 | 16 | $83.426204734156109545515413364609207756223826738837220613773249079720812017129$ |
| 12 | 17 | $-21.07641736875304565278107463639069816668153906574387638937440323302417549515$ |
| 12 | 18 | $2.66620128258900283442185740106628380315562169417018425191292253891135675082409$ |
| 12 | 19 | $-0.0954100905590322935455806363041837115100632083139497045875528586015349750239735$ |
| 12 | 20 | $-121.268642040647235696958946343103298225134949214654562918555505704282496684023$ |
| 12 | 21 | $5.30811169413484238465781036875393963281671387052158911620417215138703614166748\cdot10^{-85}$ |
| 13 | 0 | $-0.00538420225002882651950476161562615893233061961355534839832097478745883446108303$ |
| 13 | 1 | $-0.0000234699227835136564702722448574008929098644190012432754340043263672571610865917$ |
| 13 | 2 | $0.0000614694819805069418043605915897306580378606038876935812355222790489743210232298$ |
| 13 | 3 | $0.00592979063340437868049942160506383112979964462432740895218029073187499725705775$ |
| 13 | 4 | $-0.0000503764245925946760613761553151973544061078282233318516866994407672430187199998$ |
| 13 | 5 | $0.0848469720160203922940909647124650108289525251282215124353854974444905335253392$ |
| 13 | 6 | $-0.108395122167625747925848802885727098561521752380974419243464794245720888272659$ |
| 13 | 7 | $0.0203839013767130032826920470391782673758281640369298920593706985701085350313034$ |
| 13 | 8 | $0.24896241252669327434644362885332227417928822509601976725042412895689555812945$ |
| 13 | 9 | $0.000929072524355723065089363327986017760437910442734183829428533256040014285997166$ |
| 13 | 10 | $-0.242152416189939582861082281030454173801249222804822795817491184724592868563172$ |
| 13 | 11 | $-0.000817113130542666777836328872865712859946584309858773568786832942685645096685706$ |
| 13 | 12 | $-0.258219687483830836369741056838355584443869046343500879495098711185310258318872$ |
| 13 | 13 | $0.000873655885598046326398123656441098700862330265087915599954896047465740465289751$ |
| 13 | 14 | $-0.000741234450969811614740445888913698797623847254218833668120385808071850568158081$ |
| 13 | 15 | $-0.000252903194538148209170494635655787861058583401802076814882555161471303693942587$ |
| 13 | 16 | $-0.00034322233808922364878625469491354770043026601284561120017126634480006599601768$ |
| 13 | 17 | $0.0000479967836227020805652714840992469958116693352042427327189684879637211019193939$ |
| 13 | 18 | $0.251413493405553564937976024666196565197355772550131715292647960043031626796789$ |
| 13 | 19 | $-0.000712107586667025050813244935087513832408067873767140953660097811209610408763364$ |
| 13 | 20 | $0.000769416475536548768357442641018441997565735574516747843497791094872178900512146$ |
| 13 | 21 | $-3.36785216914248168538022013748832356633800652207816934453449134035549621142142\cdot10^{-90}$ |
| 14 | 0 | $0.0140984820460118376565755498306734349978001747253085294772698419886039150516539$ |
| 14 | 1 | $0.0000614557681192009277752043269659911919045642155219507924033351551410783232451843$ |
| 14 | 2 | $-0.000160957250087547409333597257830799909894950165863949367410878328938227089415763$ |
| 14 | 3 | $-0.0155271000046874545358603332312564278917033999445178603384160629860021378168239$ |
| 14 | 4 | $0.000131910185516742565211894452069941757513710402058947384928027705296658874629826$ |
| 14 | 5 | $-0.199046576916939702589771085473368397551122912145424685110273991543501594158904$ |
| 14 | 6 | $0.247374091618221266226375270378991268660891667289584643252603623554101066224109$ |
| 14 | 7 | $-0.0350227371235922919383991309146594615303347150049997196797774865621554611070449$ |
| 14 | 8 | $0.803973555166813083124629679281630445584682760660100488701418029227132387883378$ |
| 14 | 9 | $-0.00243276751054474767768880003387451760474060629298143759467992538092241226694552$ |
| 14 | 10 | $0.769373391205689410861416651022196700398984455301013442897068695659210314125899$ |
| 14 | 11 | $0.00213960290968910709175166889320431414286737052868242561534768598526156042240955$ |
| 14 | 12 | $-0.769187866616970896193029970303701235268406507807090549641561636190497562442692$ |
| 14 | 13 | $-0.0022876595724892546301455343035127293051312572926103403282677272870136258529038$ |
| 14 | 14 | $0.00102807241899064496363147071162331941318423302307856597283194685130803061185279$ |
| 14 | 15 | $0.000507140998673831258640634319764318288622662370917626193584071357681173539165364$ |
| 14 | 16 | $0.000387603585479664436837205544351504200077010964574028302438406276334710013112442$ |
| 14 | 17 | $0.00000341636304678657021915727888069601782110994134939329440137067192230979022732721$ |
| 14 | 18 | $-0.804171249316718556701355780614611759261726918444699437628806657085477813774192$ |
| 14 | 19 | $0.00186464689832186747145217486668588343283541683122915143791636276984424141793797$ |
| 14 | 20 | $-0.00127152061886247911404174828634395075001844102186113285400429706405984154873148$ |
| 14 | 21 | $5.5656378703863273180296834283512012243076786692236578705641061194191569110832\cdot10^{-90}$ |
| 15 | 0 | $1.9275367483674243700637762381240592498486198954354544195456060840740595525353$ |
| 15 | 1 | $0.00840219897874865990551003357163240574973231500723872210807411659288842152264053$ |
| 15 | 2 | $-0.0220059871302015037928054407475629219676707999935716492765060284788997414060495$ |
| 15 | 3 | $-2.12285661370738650675282907439752123032612046968928776901136895708517191032676$ |
| 15 | 4 | $0.0180346883613197880064122749141235908687193608458447766537602975415639911686639$ |
| 15 | 5 | $-4199.36701026253844152827518650824750377361750672146427432923256356127753680177$ |
| 15 | 6 | $6611.55825615210283397084818805604805643371467035277885322768345573313102775475$ |
| 15 | 7 | $-3315.95074803791451929816275520583407529378747783011426600087230088104104102707$ |
| 15 | 8 | $-16.0905653966976996903866539552913560273808087803180075267425541006799000092137$ |
| 15 | 9 | $-0.332606642438916039457884217943909692665930746690759228235711606446498594497275$ |
| 15 | 10 | $-11.7928809342732333596788289177083662555026121126354258189956046034526659404907$ |
| 15 | 11 | $0.292525338676886847272081775213855654878795472047645367953675804894085868716772$ |
| 15 | 12 | $25.9402104828774155116667899349817227446222032069135797883654667429790345602937$ |
| 15 | 13 | $-0.312767564574437134908239517999270301508769546712146184656251950773047964616315$ |
| 15 | 14 | $164.837565628120813107602848956613530893126468526789729581570455977485525368352$ |
| 15 | 15 | $28.0498398754023738644046469602209406962832587397638289585726789959410107025813$ |
| 15 | 16 | $92.270471442998790066847294230352450269260783077719907768139002108847481707654$ |
| 15 | 17 | $-23.2912074039085555961503216269950716677430046349832333110748022739717969712072$ |
| 15 | 18 | $2.59091532182925206506846234843328940805098010200979698080462388728245409549569$ |
| 15 | 19 | $0.254933503303034810982905104809467487360019553925934443441203055370378596983854$ |
| 15 | 20 | $-134.261552386545568601108923034615953751464347931956087131163652085374609030566$ |
| 15 | 21 | $5.87683101173709320140495591313954125264312202936297670694084792880442965495753\cdot10^{-85}$ |
| 16 | 0 | $-0.011549138588726402140057724990350888794960785959163030120762895029893291048749$ |
| 16 | 1 | $-0.0000503430923108535393837224635689962854310965493689412683131348990720787534419474$ |
| 16 | 2 | $0.000131852321551682815246127423251059204486878419805924260236223387964976017511779$ |
| 16 | 3 | $0.0127194281802754024310270779678043201004099699560347291143897929989090653080028$ |
| 16 | 4 | $-0.000108057662436674990925990351310793018816328213443919709397908993741168801025612$ |
| 16 | 5 | $0.125792023030534992710142824226478790302075109653683626489377122075524090750671$ |
| 16 | 6 | $-0.143896114412072090017837604836682374712227822743776056849365615970674084686061$ |
| 16 | 7 | $-0.000882728476250277754805555766603687092527748971257660481522298079124516726675621$ |
| 16 | 8 | $0.842453773318082669781479707490250115972476535203817198895965057751702436475052$ |
| 16 | 9 | $0.00199286483762839406757310857818038805774050449860391881657585960073742431279081$ |
| 16 | 10 | $-0.805974716265049634383019762803419190430066544442819918103925093391638761914581$ |
| 16 | 11 | $-0.00175271142298839580571283996846670761218696141100198380853229685324547464723018$ |
| 16 | 12 | $0.805921108895146181171253685116135168797214539889852236890041818397571581525718$ |
| 16 | 13 | $0.00187399589262723461241412293666511237508219742284677670443179360639256676389868$ |
| 16 | 14 | $0.000628762728417753483078227305224055571057193445890431024613223775262987536054885$ |
| 16 | 15 | $-0.000165539448545206614591346794661119176761359380938473815525213791101840029560585$ |
| 16 | 16 | $0.000506093310189300130602911128448977490604304620661715131361010500182392881762054$ |
| 16 | 17 | $-0.000210820229373475698721186143926795076510983397614150262314036713911591090998696$ |
| 16 | 18 | $-0.842386630337283064051687746502604308303314908971776025878592815360015705049349$ |
| 16 | 19 | $-0.00152747404844551261720631779216377605301478533537427701943447629527564207370659$ |
| 16 | 20 | $-0.000155959324768455772759030580509250537064408165268843644918774473384334346732093$ |
| 16 | 21 | $6.82657529335021696716595889552464827987468852213510053883698122667500857437382\cdot10^{-91}$ |
| 17 | 0 | $12.4246334942510672948028992683681343755287752561339084640373231127218673865682$ |
| 17 | 1 | $0.0541594047144066310051926324238687133320284371945146625891880530331435846202036$ |
| 17 | 2 | $-0.14184752897890862295058401536399465931949855195516083138942369054980219763856$ |
| 17 | 3 | $-13.6836381503495422058173789832379925545884861181724377563874922250279530531002$ |
| 17 | 4 | $0.116249090069083852216040349481901373795609057420537813350799322955147982331205$ |
| 17 | 5 | $8679.13099307992709776729940525761266650708409686459080258515726928424805428235$ |
| 17 | 6 | $-13741.9029532738927902104360589579462992276206698899856824001166101450897516327$ |
| 17 | 7 | $6996.40303004164978092425810431662747615544552062290254254712374745301590683142$ |
| 17 | 8 | $49.6796031184165689873258534639039079869554832499445859531056371604858796412663$ |
| 17 | 9 | $-2.14393610578739033707229236631914641146131909960017887506582134056892491019634$ |
| 17 | 10 | $35.1768756029709226410312633202797413610969920392448228472419132347747959502887$ |
| 17 | 11 | $1.88557760256468965066858540203336893062220820732341854974735619758403289548909$ |
| 17 | 12 | $-73.6061453912134292793996321547699407980480759316390047193800751160955819814074$ |
| 17 | 13 | $-2.01605617221993270129188095820584983685600140286525515418174698882306816400478$ |
| 17 | 14 | $-441.471145885869774372726655068785781159559200451195678816125110115426735252089$ |
| 17 | 15 | $-58.9359879740935746940344774556502013934205310832711479340836971303388924777174$ |
| 17 | 16 | $-141.388807310704280705469751497489126742333655615408201500297619427002744755385$ |
| 17 | 17 | $49.434844231332142552903970561050417697969304050380890153817751606039750891714$ |
| 17 | 18 | $-20.1960066190990532668644237003062670076307336201553029153273748760906855715452$ |
| 17 | 19 | $1.64326586594440143134078048497989446297781859023325965208202778273467798629337$ |
| 17 | 20 | $363.866542795336456529516916873730714004366593910842534698048240866934556243457$ |
| 17 | 21 | $-1.59269883657883583445227776812203648281183445753310447390283066493667709418534\cdot10^{-84}$ |
| 18 | 0 | $-14.2165625181946618000085350688451571684405044885917808714778109212676196480587$ |
| 18 | 1 | $-0.0619704849585167015110036877939632923455209170715052547789322405129246387750877$ |
| 18 | 2 | $0.162305331961153290199136329555282411532741097838307332723539360247683043946687$ |
| 18 | 3 | $15.657145728347617585857127628047883313298392579202354836688285606354470652058$ |
| 18 | 4 | $-0.133014986511679961213677715041184343006215342504396380985169914811031691066308$ |
| 18 | 5 | $-10468.4440063933411152555869030104514537627580927922812429004155828224801811525$ |
| 18 | 6 | $16571.3440898297947198745980797110838045932929510366963452060967851721461395721$ |
| 18 | 7 | $-8432.08922271940408331376045518653509108710276118703795686268980557647213884357$ |
| 18 | 8 | $-65.6245992318054478568267122282451964340191898642522895512924160214530804312007$ |
| 18 | 9 | $2.45314291943051618903285885513726946705185063381056137585757535136407654824662$ |
| 18 | 10 | $-45.0030348235045343128090920662734213212228650305416431587131524775497426232564$ |
| 18 | 11 | $-2.1575229468275238637339703252286095103702694873925097312323566113094785845553$ |
| 18 | 12 | $94.4624196226013001477771548088766011542959952976158357991337188597042125001102$ |
| 18 | 13 | $2.30681964388073484121430058838569986545678468256926179779834278784380254680906$ |
| 18 | 14 | $658.793557472399870987907714690712513206741814718019642269751825611553580023384$ |
| 18 | 15 | $71.0412064303173802626365036981341654974143514945109039740097393728798961219851$ |
| 18 | 16 | $212.557051258856401612411833681247972541693603579547040798682432514109024980583$ |
| 18 | 17 | $-59.5656229783464694902615054122801969377995008581482006367821265340077469408021$ |
| 18 | 18 | $20.1813923323462156432695797140991691757269461432285336702605177768762383292361$ |
| 18 | 19 | $-1.88026406799229794158435967913387782080448780121195413258946223155304753073971$ |
| 18 | 20 | $-468.389001148616995561991923232370661064617455332362178245035575896034471095488$ |
| 18 | 21 | $2.05020942971205906367433908849662264148636291949242768490616576324944296991233\cdot10^{-84}$ |
| 19 | 0 | $0.0478503047227170344606104464935401686370585732617966148663933766438885703711009$ |
| 19 | 1 | $0.000208581123973148478130824734368365503686186149465892424600264505176465118951227$ |
| 19 | 2 | $-0.000546289553647260063411884446205546319018661043474921108143774169103608627836582$ |
| 19 | 3 | $-0.0526990398157486833709121348618896971417028950768235271345335455045453748522293$ |
| 19 | 4 | $0.000447703699760484637658895932656612963232643336002777479025156201608516666337899$ |
| 19 | 5 | $-4.60150368844180624787895276444296105248768020472109733414876954942984789694721$ |
| 19 | 6 | $7.02914873315307664116585556071115888698263230692077327452636593876750905747547$ |
| 19 | 7 | $-3.23462546286650799584887488359259356229285493546084080530762757334967865844058$ |
| 19 | 8 | $-5.52173909839727587419702844590076104135957877967305450390815580176068243419387$ |
| 19 | 9 | $-0.00825682270752130029006869974660085671741001114445672218695888144978528248585778$ |
| 19 | 10 | $5.20326345962258290946266914197046375046965425387213840760478956878801383550562$ |
| 19 | 11 | $0.00726182087405623289758933550320016248011905237145125563592897646503761803373671$ |
| 19 | 12 | $-11.9190739059193270576056864343877168427774980217614847463892772106591449373463$ |
| 19 | 13 | $-0.00776432578260556813483338666201681682998662318351119961687979724550920252583588$ |
| 19 | 14 | $0.0977013077609733450328228004467355401854851723702192607163076554782877409067701$ |
| 19 | 15 | $0.0280505063363898729348964243258987676331863365784763752613040855283399176763713$ |
| 19 | 16 | $-92.3769609411517522859845762181493676281247225608458440841182036360731732361762$ |
| 19 | 17 | $-0.0219055489263162647830826604962780394345087237423877029028160887367168570268088$ |
| 19 | 18 | $12.2372818991615118828973128299467659440909898007754259100593833284317417796999$ |
| 19 | 19 | $0.00632861906649092660829471890661149371179803190502017034981943990927651698226479$ |
| 19 | 20 | $63.6881958542344650820157775343601552590178403520805349564110116392772902827664$ |
| 19 | 21 | $-2.78772856282911695977235006427385600900707706887004294567318206383647171326036\cdot10^{-85}$ |
| 20 | 0 | $1.079670229883696893607981399145912856581319900527933653057794079964535614333$ |
| 20 | 1 | $0.0047063196645135568500034762708520029890736277775877006945777983004276635143803$ |
| 20 | 2 | $-0.0123262029654198766663468333263162503466741570712641058553573495092020335824794$ |
| 20 | 3 | $-1.18907465192185550949844783791974300501340050462631640132786874599318730501185$ |
| 20 | 4 | $0.0101017612999798098059509433870945908948077485550482602714059750819019527777896$ |
| 20 | 5 | $-7952.84249554395552084412945136352900153933353802908529862878847797108948317766$ |
| 20 | 6 | $12533.2115142691591143189017904459646842797072074828768845886612651416308457078$ |
| 20 | 7 | $-6302.23007496167135144167424496125402788575973499197388696751067492698728042581$ |
| 20 | 8 | $-31.1601760702621031743320421732893512760515711943170138011859846077912832056834$ |
| 20 | 9 | $-0.186302798329018870270980216289077138456336504349639828052128210340652591301583$ |
| 20 | 10 | $-22.5749984528525396910146651924217180267725405568599986266620064018831760177029$ |
| 20 | 11 | $0.163852076970040452026373334312644451432559186393629439410443778650125134095731$ |
| 20 | 12 | $48.9786410429179195699595085594196563579892013101859741743901769316265622772724$ |
| 20 | 13 | $-0.175190345206262885733361923550163917129237625106003574200996585791163315335678$ |
| 20 | 14 | $313.417844155305040970663744723054949856405579416130069621348869048799105228475$ |
| 20 | 15 | $53.2722648595115767349741538981261683805505478301974380408759915631709169637092$ |
| 20 | 16 | $175.475146749479906799211869944694180548284897463471604220854624764252977792565$ |
| 20 | 17 | $-44.3125812379682215979547452501630477378614591069397678972451100978120570726787$ |
| 20 | 18 | $5.01535954552817908803240655724340334214281536612970988071981791228436218932301$ |
| 20 | 19 | $0.142795780339528523518120841563312295721227278893275583463247896937530669772064$ |
| 20 | 20 | $-255.201731439400942142238820903427519207437107424668892012586267439875533110198$ |
| 20 | 21 | $1.11705653846019896827055940776833479234646974636964492454410516269400293757024\cdot10^{-84}$ |
| 21 | 0 | $0.0358102940270364327922258373363552718836340436537475590719187530702218030922936$ |
| 21 | 1 | $0.000156098303265811682762640678612243014713440288503127932456065404105536481574222$ |
| 21 | 2 | $-0.000408833123495646200397712864064988430067033419803135313074973465959750017109178$ |
| 21 | 3 | $-0.0394389988042964987616770514006227401827526489067237373159849670779255084570443$ |
| 21 | 4 | $0.000335053271203173315182483816479709171636527447604379294862569825078675697832703$ |
| 21 | 5 | $137.558034455167086395132568585402713394202167381490434713442074822115111241777$ |
| 21 | 6 | $-217.040123097641821472777002555611854642538019617402020172097690639184953518633$ |
| 21 | 7 | $109.483007916685605308965291532774201292462453718256159695551343318687896492777$ |
| 21 | 8 | $0.435534992494261834623489535093074347005775727837021859561193663718567269252581$ |
| 21 | 9 | $-0.00617925529625884391396252601438252313207784711080328281463864215503219132138811$ |
| 21 | 10 | $0.392148960562259399281772534503338191320246954531284132625842336010841326616908$ |
| 21 | 11 | $0.00543461409866771629661526754628809988860987191870540637053395601425311443694129$ |
| 21 | 12 | $-0.755119298958832043521269783829735651375823288691377563664283959193715106289586$ |
| 21 | 13 | $-0.00581067959353671042721359273863153256527195392184411995546129213888325249164441$ |
| 21 | 14 | $-3.55453817773590304465664957710163543640406685060567086004996312962495018390447$ |
| 21 | 15 | $-0.924634052816925113875807223345962751436512229987086869870884476881942807990414$ |
| 21 | 16 | $-3.3988598569633212069425207986974179130780892393278357565431772289103760897384$ |
| 21 | 17 | $0.770769580411199580663711722039905991461813156589569057231636701132052256557753$ |
| 21 | 18 | $-0.0670685998026829621038097774987036912523701804364380941226325079300816064103914$ |
| 21 | 19 | $0.0047362229116287314913928863446459213367055352645724379310172230463081848430826$ |
| 21 | 20 | $2.72754750484894848675294439740178529489442906570873140113070326768778169853759$ |
| 21 | 21 | $0.311566645339197032761755822570745500669850013822273012062874097779931945706007$ |


### 12.2 Matrix $R_8$

The following table gives every entry; indices start at zero. The entries are exact rationals, with the coordinate and equation orders of Definitions 3.2 and 7.1.

| $i$ | $j$ | Entry |
| --- | --- | --- |
| 0 | 0 | $0.937990608960515335242243152984089614940184446592231117147881833244491846081878$ |
| 0 | 1 | $0.004023612776712626235423962044229254749519434925981664667545045948008019917756$ |
| 0 | 2 | $-0.0105489252398127542868799415199290236447511345691788497517860820735750130154668$ |
| 0 | 3 | $-1.03312832023080154777509068150839416457591860300126484782442845282624610432691$ |
| 0 | 4 | $0.0086484319196038618967905970191844786483670242365287607730592440520758858522803$ |
| 0 | 5 | $-10.3322172824172724269898016279106261795821219166329808483957218382938819373901$ |
| 0 | 6 | $11.8804537841486721458799039429520890333913664909697082243121553809177007228385$ |
| 0 | 7 | $-0.0353135421230408960444140336221897112744934924924633157635166972862225631988993$ |
| 0 | 8 | $-1.80602363528241472248642805514191426682319659905403942297026137346782766235489$ |
| 0 | 9 | $0.427871714739779209942745575539742641967738655093808295902052618093332041084536$ |
| 0 | 10 | $-0.114142860063807677600997907776013903522026771495065187691989952305065430907018$ |
| 0 | 11 | $0.140401516726175846578037764207869713227096886560069372181218814388636400836973$ |
| 0 | 12 | $0.109409216533628256002038765802721045078265554913667464804972362338914884425038$ |
| 0 | 13 | $-0.149767789680514800878941469159081742942911764270820165862101984119340314343892$ |
| 0 | 14 | $-0.0452699430257450600117486588504011410280917363824340096558020973277875870233644$ |
| 0 | 15 | $0.0142354077365801362469165130266095896944379894033251325410617460101121854713467$ |
| 0 | 16 | $-0.0373880955442275401565212207126439723529694841545679496247764694148468668139117$ |
| 0 | 17 | $0.0160938216612526752316304614430208091052207375272346991591764284492953848671635$ |
| 0 | 18 | $1.81047274861885279634545999611934526818209770914212592495740794494683047283665$ |
| 0 | 19 | $0.122067919059272144436920494447914981677109109084418398971124566517285180834211$ |
| 0 | 20 | $0.00820683489776320546356599032800915762270703493755352685986197036274572615634024$ |
| 0 | 21 | $-0.0000301261966180207104305477010147257752491235094242128128932411359898615465812211$ |
| 1 | 0 | $-0.793166723862330087110503421232104104664463250916249410343032009526197995034543$ |
| 1 | 1 | $-0.0034023749637882658747833463581764209542006167407212648100031961191943390408286$ |
| 1 | 2 | $0.00892019215629816382219759608755158520714004873671465596348981125631240624164345$ |
| 1 | 3 | $0.873615361666538296201301900496425831631261530734713987441315133178434436868521$ |
| 1 | 4 | $-0.00731313122614360223751129475877157557603738212181335575754178171475000724576673$ |
| 1 | 5 | $8.73694347666292104944602829477534819157552492459878519976619306417023409208992$ |
| 1 | 6 | $-10.0461353407512554993893254371481955602572318960407215078756525858356989896194$ |
| 1 | 7 | $0.0298612014300942747427921755286994031021193713748180024890513848181913121110441$ |
| 1 | 8 | $-0.0127816171147831170283501825379648163969183098203523176125891299752440869746094$ |
| 1 | 9 | $0.134537485115670499279471430551881025740387012196565932564426909313285403411805$ |
| 1 | 10 | $1.51418617186743038084162693124758228409891616750694410052383432280913236198776$ |
| 1 | 11 | $0.356232695574208254282923051924005038025767631731038455900792305728014752036565$ |
| 1 | 12 | $-1.51722661461205170781740462209732736005451258315137405031301903122908275280646$ |
| 1 | 13 | $0.126643940724140987887851385952075788704057131837472623043632819337561151623723$ |
| 1 | 14 | $0.038280353828868701108260758766817680853113605536609561192534662178897150124187$ |
| 1 | 15 | $-0.0120374890850778555166200273074540968113741814918831551847879418160053752001639$ |
| 1 | 16 | $0.0316154479277042150455475643207814319254208479082000624836071314425420443134606$ |
| 1 | 17 | $-0.0136089675947040666445740417770859985109694177008205872491134286200683021684402$ |
| 1 | 18 | $0.0171217008027551368444818483296922271155144418378505718312664410040451238588522$ |
| 1 | 19 | $-0.103220875053569550706970285325749526626538708568020306597541451871783624065923$ |
| 1 | 20 | $-0.00693971590648611143598738697436565661750011011296081372924963224401013920776526$ |
| 1 | 21 | $0.0000254747717575003549048119154635617875822001953227201502295873012007084340854115$ |
| 2 | 0 | $0.867527716433815408208241438869998533314385811185971449736312116358384799406937$ |
| 2 | 1 | $0.00372135453239102128551985355348027929102754275708507449295178454740788247780982$ |
| 2 | 2 | $-0.00975647830234410009772085158385535589999453097056021743061075504397695787317529$ |
| 2 | 3 | $-0.955518577553966933444571753709040292571309183599380999861322768711738756257157$ |
| 2 | 4 | $0.0079987521434375949136291739364041982655574157590724915818900161878909028858029$ |
| 2 | 5 | $-9.55604968651746467952638630597417539087224815161003270010729733884497311426707$ |
| 2 | 6 | $10.9879809489583442123266012124488241705660602227880975408853973977712259326595$ |
| 2 | 7 | $-0.0326607497607479958964386372173382339906880055513592003118158670849636738164412$ |
| 2 | 8 | $0.186672001075625118873633224165209196075381513151731059605089906854017188976978$ |
| 2 | 9 | $-0.147150647809330280147768516813886539297363604165606453298539919814813787975765$ |
| 2 | 10 | $1.61224269448435580920404116185679042130320845639278101798020001601394316775903$ |
| 2 | 11 | $0.129854399421210760028302257746856729239906326903986657562407091032655220139141$ |
| 2 | 12 | $-1.60892063798635333678553744050807953931058292639056702746856933122954914709066$ |
| 2 | 13 | $0.380733832613180040915689273495846626958211679935412978742487517241232564169311$ |
| 2 | 14 | $-0.0418692148098752786489689753658299024902190846691972415035386756499303998450953$ |
| 2 | 15 | $0.0131660281544881550891760768012345359678776541868007543912757709711128329909839$ |
| 2 | 16 | $-0.0345794604332316777274293696468867031472537508514312365203789007914138769133107$ |
| 2 | 17 | $0.0148848359686161096889916952846935339650156371529327066306296879907795724602775$ |
| 2 | 18 | $-0.190391443010458044809216465901205526310045362704311671373510341806446029606746$ |
| 2 | 19 | $0.112898041899027069638607366146838702489129502211880483237954830026880926800463$ |
| 2 | 20 | $0.00759032837854942761729208680658061062911337155728483963156758211544936978709934$ |
| 2 | 21 | $-0.0000278630833903879779151453244723387922091303782141011172819329705558489300048962$ |
| 3 | 0 | $-0.0292098928281199737344611757891401987397475100074811722376481421342749748498274$ |
| 3 | 1 | $-0.000125299013515579262995737769318653335343512412888598525500573530603570785471313$ |
| 3 | 2 | $0.000328503262999887013446861189613309723251749065689383022228717981851792405022207$ |
| 3 | 3 | $0.0321725689184460148427171301338201231846772017983681478280229809448265994542479$ |
| 3 | 4 | $-0.00026932014786680526206187694916228744865921986909777777505391299052934670971313$ |
| 3 | 5 | $0.321754777300720193646430324487440259393852391832039527432185824765598636152407$ |
| 3 | 6 | $-0.369968290161232493656293392247214327575049854204973833024484136777995613793319$ |
| 3 | 7 | $0.00109969627727770353326388116002988411561904750564416699271811030772779420551358$ |
| 3 | 8 | $-0.166330616512990071425626566933287486855000078227724319730163427038858299198424$ |
| 3 | 9 | $0.00495460210743236004989196032790942232896295084236274712095876717890306762179942$ |
| 3 | 10 | $-0.0964034457940661965399689246524006843891138410494760361919514225040670523774137$ |
| 3 | 11 | $-0.00437223274657510621127520339935177620193835400261361164519761615899517760290643$ |
| 3 | 12 | $0.186700928438989764575713587677575486065740089941661688944096161713953799238865$ |
| 3 | 13 | $0.0046639071264480033871220989043427669619819944643693326338338759001405625898785$ |
| 3 | 14 | $0.680884017168481149887172938978902903435026706812346528040360534391282767065958$ |
| 3 | 15 | $0.326326122300606522027349148090559494189904096200813551221801772544495548680457$ |
| 3 | 16 | $0.255163021740248794982584519418547317064128342746945072377701567810286152687767$ |
| 3 | 17 | $-0.000501176452545758039507109384306950450378202167987931405736272700891877020325164$ |
| 3 | 18 | $0.0710317981823641867204673742894994248161965896302233479923913014720225525302866$ |
| 3 | 19 | $-0.00380130760309462354025010595721579086012908570272164970005234323963884435016172$ |
| 3 | 20 | $-0.832135364468923982551968748808747900945364725082239997100545631623573637488619$ |
| 3 | 21 | $0.000000938157553097952384668411740183016806510646883393923505409647429834752184036929$ |
| 4 | 0 | $-0.0489833423080295746914834215389968323208983649864627053287848234357369763515265$ |
| 4 | 1 | $-0.000210119376541617840529795769021913162046186187711568247419993260808040734514478$ |
| 4 | 2 | $0.000550881438542539270976972802848930943652039042632307428953044167684484127866274$ |
| 4 | 3 | $0.0539515829631458585292373797526589298925289806228907341170949951549755633129556$ |
| 4 | 4 | $-0.000451634693459364817819092833280871180153789808163583181215734070980190429006059$ |
| 4 | 5 | $0.539564608761332348065640387197130281364201854096950313857154681953718299459493$ |
| 4 | 6 | $-0.620415949716802152574197844308614195671179546320251059030146299823446866342463$ |
| 4 | 7 | $0.00184412861429271351270595290204220705423237692613330224808939592099295003775775$ |
| 4 | 8 | $0.036023252998907402283639859573355086758521899527644588231320930213424330540236$ |
| 4 | 9 | $0.00830858820525376019205118809129961286281403033962657456413018938811967625278813$ |
| 4 | 10 | $0.0581675598590308010979031765882017898124141276713977132162360451660547374859226$ |
| 4 | 11 | $-0.00733198764323056501131310357458856137035914086161567755973104869558934227403327$ |
| 4 | 12 | $-0.157289047564307560494766332213866398434585513680826542191601278608559890965077$ |
| 4 | 13 | $0.00782110912258232391005377464570666095709995630810309251359457223195171689269699$ |
| 4 | 14 | $-1.71695788163887907084172479737873490185111744727204846048450193240456088732635$ |
| 4 | 15 | $-0.000743395342548285609468118788643703283633518390145817624658570480485882526206465$ |
| 4 | 16 | $-1.11422872158480058730539059065916519000482990447727216319271514595500205551907$ |
| 4 | 17 | $0.36964598715715020004835985779031909102575240547618947125724969077105934833653$ |
| 4 | 18 | $0.0541213366994591685285295365665573419640157853374076738893563107481707725492292$ |
| 4 | 19 | $-0.0063745783880879696567994011156752000362976924378128090422125676815779454480195$ |
| 4 | 20 | $1.01894082938709656964190762732592410122199427697214887310503965605464713218976$ |
| 4 | 21 | $0.00000157323728754050894800200570815944297242405070784500748618250841238776610398234$ |
| 5 | 0 | $-0.940793688367863411159735442485946494992084518833698147862146564827340092963885$ |
| 5 | 1 | $-0.00403563689082400807185020467951837660902008263143518084827789522426306714493279$ |
| 5 | 2 | $0.0105804495160975056839909373745841756677033442938455583041655498574880744007822$ |
| 5 | 3 | $1.03621570798492454546500938502490267327666193818626515689828988943189596319872$ |
| 5 | 4 | $-0.00867427678541393511002686232097445417812697264242867859235603659656918761274832$ |
| 5 | 5 | $10.3630939513518213340281960975956515858669770043426103227077793222782564419111$ |
| 5 | 6 | $-11.9159571836861183737644194842503258007617492001714673737555437338437103065127$ |
| 5 | 7 | $0.0354190726707670744285666786092985977067852933609303052272732718252947124170761$ |
| 5 | 8 | $-2.04961964865807100076811157776568750362290876339612983242420533349083284626526$ |
| 5 | 9 | $0.15957807234948660444921231649325150643516804285238981393879570230010790016517$ |
| 5 | 10 | $-0.0569989775873585317667124023396925789790890265511243374057269422075381112339362$ |
| 5 | 11 | $-0.140821090863204490011180134701737911360829872983136582377035509707592761875383$ |
| 5 | 12 | $0.0615924895892676004729768407124720123045736853451584965167468465010925205040405$ |
| 5 | 13 | $0.150215353870525961886531547757807742653223549708980066825794768111599028677064$ |
| 5 | 14 | $0.0454052271574357945339012943991842569566970567044153316466110539868846981892309$ |
| 5 | 15 | $-0.0142779486510630988123494267498568097561797015036000474527612024004034550141684$ |
| 5 | 16 | $0.0374998256614577417623211311837859498209289778477010957464659550011752220110284$ |
| 5 | 17 | $-0.0161419162366708485000295625837843067186956039654312951497757480443408661138915$ |
| 5 | 18 | $2.04518416195942841719792994799190685623741679660206075594901816429352910545319$ |
| 5 | 19 | $0.464541621530405368466083302554002465652288726233875598371706913806271894243242$ |
| 5 | 20 | $-0.00823136010055486151797572368343126977494768929935371697701126683112922541680952$ |
| 5 | 21 | $0.000030216225367301341935270638928645849342468952106861908059645493325769591730582$ |
| 6 | 0 | $0.0545566290987255593852729490347068490082820505245240304124291459248591651545863$ |
| 6 | 1 | $0.000234026596640739366917409619042198529881238175438511230371666834390078962620907$ |
| 6 | 2 | $-0.000613560302417564218024098284652240728125449176889901743570531590713200594130312$ |
| 6 | 3 | $-0.0600901523317850672279041532584426663417267229564302778135883720106416267587155$ |
| 6 | 4 | $0.000503021339463398218833864860066668622299308531596906737566675353246125043954687$ |
| 6 | 5 | $-0.600955852499382353899656358615617583722696127103925351403864149286465019591644$ |
| 6 | 6 | $0.691006396476229314366934975035428367777075973186255458839897003734506834381637$ |
| 6 | 7 | $-0.00205395214127358425293353871516865464834759445041949595368344981323140559641776$ |
| 6 | 8 | $-0.106011570462604296191887441529923426868315060873022354926992602460100786383753$ |
| 6 | 9 | $-0.00925393294311340037246816979233972466661838195644846171975455618635888592218962$ |
| 6 | 10 | $-0.000374565804486915014692029519826882029569472453202450048332742535092721390380872$ |
| 6 | 11 | $0.00816621552471313581155936735566776160150377295901839021318973604036908872554887$ |
| 6 | 12 | $0.0959370182455582313559178276386728606037407324944915078238629387286101699176007$ |
| 6 | 13 | $-0.00871098886756523359799477691377514392823717243182412717118664089478896105549708$ |
| 6 | 14 | $1.88462916742740880989082037553708575798223484267774385672547001840289275377404$ |
| 6 | 15 | $0.000827978289478187365360435069458175892579243140536280357994870273864262503251159$ |
| 6 | 16 | $-0.343821595304411031240061175556087229256603465154804545313972377718083635082442$ |
| 6 | 17 | $0.000936069775929875887825658395468366631353140851242570351187814663300435569901508$ |
| 6 | 18 | $0.0202889851361832197577899949003608339938118758748641155245164265443167345441429$ |
| 6 | 19 | $0.00709987298524254104856107906787190476755334158808922399907203104957383231705734$ |
| 6 | 20 | $-1.70224388202751810033127621498564800695815785300301312726530636237040724386492$ |
| 6 | 21 | $0.309383424394364355537267119659419587729193567639413101371349076475970650283601$ |
| 7 | 0 | $0.0928188626815868388001057165963402683303173984192192375156740530041839887495278$ |
| 7 | 1 | $0.261195976452191488730116305319324909690364369904144774571028195675244945041398$ |
| 7 | 2 | $0.839835276794583601480136452561645238312065070884815265686220232337037411704013$ |
| 7 | 3 | $0.171137960491505894763995562457755694077460295445635437011970106242212542027731$ |
| 7 | 4 | $0.882717809964104238886033445755417547109918215067429000865932347490213034964238$ |
| 7 | 5 | $14.3709629864522487606299102869406394974550918033628579968793796744117470930618$ |
| 7 | 6 | $-23.4582274395786888546905218638954136310696228602002204628700237865659628323413$ |
| 7 | 7 | $-5.74455363596372422389894743946644081670903677180873890786110115210959834895326$ |
| 7 | 8 | $2.43827820823476182681717858507125458758651130841947167300186533995767975244629$ |
| 7 | 9 | $-0.368069056121103529486629141206681344187847629739422315213727016272229628702648$ |
| 7 | 10 | $0.269322684686005745919166088969028061837547728418515459759433685606803036151817$ |
| 7 | 11 | $0.0167215182634504063747902721185412805122765328491874667545443380635677802218607$ |
| 7 | 12 | $-0.304941469562496958664372236028912614464219589653834151208723308703083707092675$ |
| 7 | 13 | $0.0238820483472116836644815972524742671463137620790807111133202947404737613563334$ |
| 7 | 14 | $-0.319642045123814142201468892688938025167573317235729682230528179281942614080829$ |
| 7 | 15 | $-0.111416545856670020442593708899700670191896353967046727493312482232613482689995$ |
| 7 | 16 | $-0.143275231628725887828733203928359784978293044892459931489808958272793129160352$ |
| 7 | 17 | $0.0188419635927045410278658179473408210430111513284361395548714539159090996258892$ |
| 7 | 18 | $-2.40130306763210833123737022307867506668465921459964006921395139889578397756334$ |
| 7 | 19 | $-0.354850355690189924300120553963877672019690513229249161196843590125501709824591$ |
| 7 | 20 | $0.335957663732980634591308247349248765009606302863568117742971495658986663368469$ |
| 7 | 21 | $-0.0000861849052136604055237325812194146842084594488326224907491211779788248830199772$ |
| 8 | 0 | $0.286860406995149851866764177877673755720394734893619707990781669326089194591316$ |
| 8 | 1 | $-0.254956013266776920858995266575850402146482528303351064541600353855163443910739$ |
| 8 | 2 | $0.809745629710173964321969526865242202226934423346922920841254105441812348448329$ |
| 8 | 3 | $-0.0477357216482264997623067356123193869423201814292270181574208078050052326913291$ |
| 8 | 4 | $-0.848508816923790529587385383370509092440353579954948178043170342679798496881649$ |
| 8 | 5 | $9.30679233096378416355161199988588384812211948413992151876448795806076882345377$ |
| 8 | 6 | $-14.048205100594659844923114954066093126855808261758631397657379005124928382519$ |
| 8 | 7 | $5.47357834935567383148398843843312570412736532281282530177629253810833066664877$ |
| 8 | 8 | $0.289456275954729759967124360574201206022164376777651237025604132576413453834854$ |
| 8 | 9 | $-0.0486610926578264341232758382338508922452103344875027849258172786555075748766433$ |
| 8 | 10 | $2.21076147351722213375558819578521083858984492764065335984148182388968827108006$ |
| 8 | 11 | $0.320988696078910606413347266975116094617940771163578334699086637838122063094649$ |
| 8 | 12 | $-2.23554246118254416816690076906932400309221566102988041304237351376117992516377$ |
| 8 | 13 | $0.371994933505158512620084594837337823655186486424241875596706483387974003769629$ |
| 8 | 14 | $-0.268669405221045619629290991146329123414047800187552752183743475842862590699628$ |
| 8 | 15 | $-0.0642765126612992206079481091040555951105656452630318272896900292737999202229223$ |
| 8 | 16 | $-0.137591723760219796153684614930909229564620760195585254404869373655401291012362$ |
| 8 | 17 | $0.0290878298041628770164367167006500874727676563570189088974744935590084120958118$ |
| 8 | 18 | $-0.263777604319031561574937583913462173832201096805836111521173611567278026765065$ |
| 8 | 19 | $0.00598777609378959319384160841753782726075412486833602634707588726902343104271049$ |
| 8 | 20 | $0.243690383663135124089754770483376068847331776105829297059122189594484702255349$ |
| 8 | 21 | $-0.0000043406089160998033011778889809440863903575214055669334526932616909457088877174$ |
| 9 | 0 | $0.223057741483440847604463362876987337708216613514277954964304486356089722333393$ |
| 9 | 1 | $-0.269751097317194663654229876744191893365923770920966654003118893960657719430055$ |
| 9 | 2 | $-0.807643303678112275822904810399356030941315320222400818003901928698901404253264$ |
| 9 | 3 | $0.0379384071214561073154140279366958473592185539097440039242042407911429331925468$ |
| 9 | 4 | $0.845644525365596023758880779282592484169418935869389589980700804768348195793833$ |
| 9 | 5 | $-21.6319766474093128416121248669176571680976791300918498497584615798003771444746$ |
| 9 | 6 | $32.0402593028109955081717603392545060612577944979192788758988884348543353486082$ |
| 9 | 7 | $-12.4980453857310642485175477125668824950869784386766687347773464300892711128445$ |
| 9 | 8 | $-0.293535917938710986431631079300108318166776447822163271875245953365553754046005$ |
| 9 | 9 | $0.00460380836453500078035064288397347480022932968117661783874321600506481888449877$ |
| 9 | 10 | $-2.22747093617175037907167957205785902732288758457115935011400975054433842346812$ |
| 9 | 11 | $-0.357216438607693849551697326313820113834705831151501200046479417029807196086953$ |
| 9 | 12 | $2.28234375071778613791712005645839304746479759000174971581066380311488680096111$ |
| 9 | 13 | $-0.3336279981215933487367263274030275229501736220358781081432391993458585604182$ |
| 9 | 14 | $0.595142191527226711509088262018672199337738356254130295663574804516122598396631$ |
| 9 | 15 | $0.129327063745872932098859398423414155450143738120542539172789264891661798771976$ |
| 9 | 16 | $0.3119548540609956446837616835509167725025175294735602036101733900869322465456$ |
| 9 | 17 | $-0.0702037621043041003377230505974460501843682610745784759817849048667470580268799$ |
| 9 | 18 | $0.237670032175654803319046536694321915765809151786150810912656890930596438668755$ |
| 9 | 19 | $0.0275969794712109656280207441007136377975847947978139607422529462708627630310233$ |
| 9 | 20 | $-0.522784052997542579356115646461671777617865165342814708774222155398375461969836$ |
| 9 | 21 | $0.0000701354824349092598397297474476371431452732612729717360865048523936966012042924$ |
| 10 | 0 | $-0.00014686303829103093100226234172547254179795501455217342796667843309049850703949$ |
| 10 | 1 | $-0.000000629984982418414020737122563879535009099118795609289881253551041480408348650533$ |
| 10 | 2 | $0.00000165166601522879282711216373416823814902397090929839166026652726459022550464438$ |
| 10 | 3 | $0.000161758937247517443718580779744623973947302978634901817515918678098346884467637$ |
| 10 | 4 | $-0.00000135410203048165311928882033425186373127428812743406097016697251329078525628492$ |
| 10 | 5 | $-5.57253285539370869567157701653105142747399342821871315125282467956111459060481$ |
| 10 | 6 | $14.254074732246858201605507297702987458081136614934928717344514412393902755175$ |
| 10 | 7 | $-0.00362717930097706876750235737825083152340696569514240801149240717072191065797017$ |
| 10 | 8 | $-0.039073359799210395311870291979346892930372782689793992682526812889454044999738$ |
| 10 | 9 | $0.0000249110095440050470309306318064384142877004274552706385249377147481864534191393$ |
| 10 | 10 | $-0.0271440946691446889573177160422681352310782734976698955251238466104748932367656$ |
| 10 | 11 | $-0.0000219829421852379890726544232984027454981974108126914312194520326922402033665448$ |
| 10 | 12 | $0.0579979830824310230475113077753451477563225465724358579847621099837332254857475$ |
| 10 | 13 | $0.0000234494380012906989819942028689034811501099340827818935623858157405416467167629$ |
| 10 | 14 | $0.350328857730087787207405483876444087521177224279615245784585300527073832108365$ |
| 10 | 15 | $0.0681377562766129314731008051494285264456925821065508271002214815455544338812979$ |
| 10 | 16 | $0.187996823635350663203978444244746430768713115633766449733437489948039740344631$ |
| 10 | 17 | $-0.0448509700019692054688152995963131688877327734032134781061784573716961940227968$ |
| 10 | 18 | $0.00826587272436494746108455824620070346178010202952839146388171005116330563586147$ |
| 10 | 19 | $-0.0000191124146656174002440283038917115933951373451366416704950487088507178584919186$ |
| 10 | 20 | $-0.297322974966269354055584482969288507839967839648100024568873947324381821365629$ |
| 10 | 21 | $0.0000827433774496852777534783116213910407674047271437067330376041037713039390859033$ |
| 11 | 0 | $0.00285687099407889460960847540902845809521062853424414027083242503019947253059776$ |
| 11 | 1 | $0.0000122548589755437742587074049062620782265757898386723628425476031783728730730857$ |
| 11 | 2 | $-0.0000321292326900006490722863064614117087900726019381327918200873671993542709542723$ |
| 11 | 3 | $-0.00314663526802225417736759444351986914930561398923658331128434597171947051343488$ |
| 11 | 4 | $0.0000263408333296249308790315309419414461729050111945280759570216286723525946324786$ |
| 11 | 5 | $6.25844467037834654313382022503332767598329377681109055286270678802973158275552$ |
| 11 | 6 | $-2.6370485195961756322726438436572034187212796167263331026840010586246465009698$ |
| 11 | 7 | $-10.7466151801064214336407493362146518077229397856565476309725015563088990176198$ |
| 11 | 8 | $-0.0131937520045045055768973264749451535006321095043740737446972014364524859202364$ |
| 11 | 9 | $-0.000484584422517948145609017821421803334141364554003218213967959041350532622141944$ |
| 11 | 10 | $-0.0111456085106552681175420018943223245565934850924092389082152710249639227750948$ |
| 11 | 11 | $0.000427625838497685004389607363393092633766640531166506549372975089867559765803197$ |
| 11 | 12 | $0.0257574686746668056635028950514116741853783199529427148666976587966688797261954$ |
| 11 | 13 | $-0.000456153025518811118724482685049702033460078281530430675141571426944603241445081$ |
| 11 | 14 | $0.200885674707520372124081282871258255183996281297330893562479900851498661578267$ |
| 11 | 15 | $0.0193542622186118427414141263177977956435298718552936260480492017308755754157182$ |
| 11 | 16 | $0.119481538054221484710959265530095914788242631021144734291293098168595399060021$ |
| 11 | 17 | $-0.0346543815083418293608048916613428652091617141342090164488226434636438900689586$ |
| 11 | 18 | $-0.000873740801044759617594936577928706326571384647453434470386218646781937299261277$ |
| 11 | 19 | $0.000371786555149492679521523727670418025675180053149095740893425046346601143527849$ |
| 11 | 20 | $-0.144458303742422698136238613930114376868760081787270731353629702189231994210955$ |
| 11 | 21 | $-0.0000295227897903955897065709447542978175410991713155683343089065209222604179704319$ |
| 12 | 0 | $0.396366670297531512557104479775558691577827167745226361918157970410444317716664$ |
| 12 | 1 | $0.263507289275867558483547082533552150601276508981768958828471465921586605070381$ |
| 12 | 2 | $-0.841927522558033471515503072412565509327705255906998787195771234714990174912905$ |
| 12 | 3 | $-0.160353416390001295778283339196932337694033365715679365477700615117408237474355$ |
| 12 | 4 | $-0.879861782614332749538192021860354912684379134361800728522941171185151703746874$ |
| 12 | 5 | $-16.4026599403545562850931636417942114197023338823211685454042562778490397229731$ |
| 12 | 6 | $15.3764869630957713368115056066440418469623737978675427322147499402275942744109$ |
| 12 | 7 | $12.7694058693353971642936493960237134411571368931083269323968631041605525373265$ |
| 12 | 8 | $-2.43560078599157428219112725817520231076471042398252363277994417380386600155075$ |
| 12 | 9 | $0.412278374581883939061113310754788036744011350358481072002592572998224215866029$ |
| 12 | 10 | $-0.252990520444957978337620850964730990755425737258160534630213048951542564642963$ |
| 12 | 11 | $0.0193720603604863846496415952037461149504132135934764053127378675656106418876196$ |
| 12 | 12 | $0.258345299077471086811666774514570072332847985900156530412022782787972062173804$ |
| 12 | 13 | $-0.0621058696679640637822619158536394461372932888164323393083176769571294700071334$ |
| 12 | 14 | $-0.0195212529985658938902173327393603544741697832734138403781747209156065996963683$ |
| 12 | 15 | $0.049941913114540520756343490634287159681749144922596689276893631972476333152507$ |
| 12 | 16 | $-0.0413338376501748361504175521150433354525182044218719509493800940476310505873845$ |
| 12 | 17 | $0.0266003590664345651820612752348444263619924439276378153190575372426211302916362$ |
| 12 | 18 | $2.42882464420727302771241179330438942536921430712128423220406133934366973522015$ |
| 12 | 19 | $0.321148955312089427436822521319805070051319484964360630618017507474591782460175$ |
| 12 | 20 | $-0.0540198102101897717400605584830883860584311893582922053953554897414184326648804$ |
| 12 | 21 | $0.000012419357710464980108457176354372692352153262436919388120688157349355990670981$ |
| 13 | 0 | $-0.00181368941349691450704395019386303889016858809203522923178392569391619741445901$ |
| 13 | 1 | $-0.00000778001808058806067621481517714732245205633263907792774170783314727923570893803$ |
| 13 | 2 | $0.0000203972980629533925470775277613432006621305286902530723586464749765830592771683$ |
| 13 | 3 | $0.00199764675604053019482949807857542837503300880012862419271550318267911857437312$ |
| 13 | 4 | $-0.0000167225228761267970965625177537157370460673431367782955084930497700919389248266$ |
| 13 | 5 | $13.6709694553631983550615230133830689937135013763178614779089681167082839587814$ |
| 13 | 6 | $-21.5273399383841007147024925819828251896545941720365653622467489371602946623639$ |
| 13 | 7 | $10.7498571624111159790471090111693868057578597459159454474492859034096071861002$ |
| 13 | 8 | $0.0536693315445085827272230102841468817538160788017320610549446689612330802355817$ |
| 13 | 9 | $0.000307639245484966867019112991386089808670948313815357873651527251050514997485626$ |
| 13 | 10 | $0.038667001593280434809405856204941577438592424360230199576646407634828496891061$ |
| 13 | 11 | $-0.000271478991465994901398760923678066134193129575094821838042949494668608679613275$ |
| 13 | 12 | $-0.083960570807313926608528028701483324182911191743570254823049532218997336090414$ |
| 13 | 13 | $0.00028958952470473665416453964903567683827663069643550952310928378574432689409952$ |
| 13 | 14 | $-0.538524020621409215119597812191747038987120961134380160218193629854283287606439$ |
| 13 | 15 | $-0.0910679368376689860191760025211713719186533377749051268149510686341547383085815$ |
| 13 | 16 | $-0.297232422711447272465864022351446768064041266618554250790845552227741915190154$ |
| 13 | 17 | $0.0751789611513131519409794319722667494034914969989081067653825209845485001052982$ |
| 13 | 18 | $-0.00880613635510812606264014467484609775337186488403381937508871121558553789710607$ |
| 13 | 19 | $-0.000236029327383937237841815297957569522247934109273910580901127226472149994353341$ |
| 13 | 20 | $0.438937094520308644606936284011538214528086197167080255289987609399936344587483$ |
| 13 | 21 | $-0.00004524991367490371917018382046874428812491510929984009873407615292232552108305$ |
| 14 | 0 | $-1.25346742352566585147332758979535460179290749548032856767924160492120810010187$ |
| 14 | 1 | $-0.00537688489875193446933212644339750176575685714350218797636293527920814187937757$ |
| 14 | 2 | $0.0140968726285718817646437761255570710375956192090075191316256875362610010661966$ |
| 14 | 3 | $1.38060304800515812836182478403821533477368463935229638579111324878858369113907$ |
| 14 | 4 | $-0.0115571814602882796207714656840981781120954759926890466282567212533904583969519$ |
| 14 | 5 | $13.8072787217468946393921245140310766806119054930221278806479456050745950367735$ |
| 14 | 6 | $-15.8762376220756503309769657524890791574158566643668084363133540122121533322121$ |
| 14 | 7 | $0.0471906373450658401765777920460873662699580521896343632490107667677246722850953$ |
| 14 | 8 | $-0.0382421248943918296063974724184030102384628011902128464140415579595358573800042$ |
| 14 | 9 | $0.212614006314305075468280406778434677701620936264701647835127981846604113274927$ |
| 14 | 10 | $0.152512507151548153061350049376742028704613238039154200808059307753240423079994$ |
| 14 | 11 | $-0.187623123034127897123577857984282598634971659384679455662213979263781161154146$ |
| 14 | 12 | $0.0925580700738612870759767003296301298166128581618701325346771011184426780035013$ |
| 14 | 13 | $0.200139578866371291818624448250553981725335994825341461919803091895582823508704$ |
| 14 | 14 | $0.0604957003892807615772629737417043075555260054610854405188984804519879204564021$ |
| 14 | 15 | $-0.0190232393458424914481290783389261563944613542678212562917570811570677416669858$ |
| 14 | 16 | $0.0499629306995834666547650450004702826325119122691529447323530657211431456175341$ |
| 14 | 17 | $-0.0215066984463392714197951099411254765389870747936387221673046915195654820900661$ |
| 14 | 18 | $0.282162930794761118583966073378964691916816493014255930526639163196022387607601$ |
| 14 | 19 | $-0.163123338908402915688321444874631055098548307643911369119604445470019806166433$ |
| 14 | 20 | $-0.0109670609666336192463038894577507318813698274970200522485821506223452252119195$ |
| 14 | 21 | $0.0000402586184708888126136943747734662281466505843303716642872926343191165256776029$ |
| 15 | 0 | $-0.00537688489875193446933212644339750176575685714350218797636293527920814187937757$ |
| 15 | 1 | $-0.0000230647328138038559745381689075313905247010039122038714466586527886799463734281$ |
| 15 | 2 | $0.0000604700689731531925991977418694658026145186460984463996356570900110792179501969$ |
| 15 | 3 | $0.00592224699315277201141884806668200075055977319471493072878675368947745177122259$ |
| 15 | 4 | $-0.000049575787371619295802377881438593161077231268844548616846867234894764123833071$ |
| 15 | 5 | $0.0592278244000967115834749674213129930165045796141571660582810821417547922867029$ |
| 15 | 6 | $-0.0681028487194569427829736206533864009987429296286903065474150804121432254774686$ |
| 15 | 7 | $0.000202429373544838738663389853826352009905187878101023792134434666278793746306073$ |
| 15 | 8 | $0.248888733663260331605878274782856717556772080700936199750295916404323572272411$ |
| 15 | 9 | $0.000912030913894051712214747964426734101167175845025405036779023228967799223336113$ |
| 15 | 10 | $-0.242348889862560304320282634529225325337290223796669902697409478278260813291286$ |
| 15 | 11 | $-0.000804829800890491096170401186684634474609027208903120925795527374779202552550577$ |
| 15 | 12 | $-0.257939281511956069384553894111511732056492736612958886894348045775200743629686$ |
| 15 | 13 | $0.000858520500056002410681164884780777508436355177579941098464748864827928816837001$ |
| 15 | 14 | $0.000259502889151777694975687709585279465572102972265629166218886624308365002145002$ |
| 15 | 15 | $-0.000081602255028137737142550247539352097429162273946675769055440357638031491972901$ |
| 15 | 16 | $0.000214321427532878380067251468029039699951436745296530509895499384985294154257085$ |
| 15 | 17 | $-0.0000922553230564795035900365191883839195943005833293145196126000795452950566674991$ |
| 15 | 18 | $0.251403977874348930680439218766827587256237136187473180476229735727671788684968$ |
| 15 | 19 | $-0.00069973531114478636578223977891755990440480385746409196780709840094123967559207$ |
| 15 | 20 | $-0.0000470444013050784049961905473755477525271132180342276100484452478960412007839907$ |
| 15 | 21 | $0.000000172693724334596096199647260225933766903776413017816234336222385334213565214625$ |
| 16 | 0 | $0.0140968726285718817646437761255570710375956192090075191316256875362610010661966$ |
| 16 | 1 | $0.0000604700689731531925991977418694658026145186460984463996356570900110792179501969$ |
| 16 | 2 | $-0.000158537680498491320075894479976985781191847040511566071959738303772498932626784$ |
| 16 | 3 | $-0.0155266781992665961879660721269150971280500230207867028246683628883227050427326$ |
| 16 | 4 | $0.000129975547775087691538017617003398251855865300900502926448507483039498214023048$ |
| 16 | 5 | $-0.155280820095179237692529050268114697956976752760354214970595806782011219173346$ |
| 16 | 6 | $0.178548955783659234047420560646787559000472584418008526929848784062530151045488$ |
| 16 | 7 | $-0.000530720137938151460837193725522186004836307709728669700993209277012779550343593$ |
| 16 | 8 | $0.803440195210587999147217830219551142266802917436654182844886642168962485978091$ |
| 16 | 9 | $-0.00239112122884920454736885298975603798278599563312396468728949797206256461576293$ |
| 16 | 10 | $0.769420816196150168055929147187647426480581235396585995926975453279354759322828$ |
| 16 | 11 | $0.00211006621946949661537295473536549888893941355465302932899218255567229877707258$ |
| 16 | 12 | $-0.769380246376209318445999392862469737886179027657007025968640556024733080659551$ |
| 16 | 13 | $-0.00225083005610116156237588564931067370639145184736659893646927893800165271921133$ |
| 16 | 14 | $-0.000680352889080467964931445198369678653314966169649874543086864803631717418214328$ |
| 16 | 15 | $0.000213941086148767955467858668925661766547990744210744135268858545831875643438079$ |
| 16 | 16 | $-0.000561898184989225095488167488098856029523877300811658730200898552781751035082904$ |
| 16 | 17 | $0.000241870816081038479654639365756985119538254904029158135093339079171187484100367$ |
| 16 | 18 | $-0.803494070516926571743826681856468497491839368600467613389179373553877642630436$ |
| 16 | 19 | $0.00183453425927190427733554003884252468651697391760313313110743243552980882694911$ |
| 16 | 20 | $0.000123338874752376804307166538445914968917690565178868023003999201533029509995969$ |
| 16 | 21 | $-0.000000452760563326096206095262808475907275691737583759416603725298225076336540555314$ |
| 17 | 0 | $1.38060304800515812836182478403821533477368463935229638579111324878858369113907$ |
| 17 | 1 | $0.00592224699315277201141884806668200075055977319471493072878675368947745177122259$ |
| 17 | 2 | $-0.0155266781992665961879660721269150971280500230207867028246683628883227050427326$ |
| 17 | 3 | $-1.52063367614284441066642951443860239538490995023619129146627097619530172598024$ |
| 17 | 4 | $0.0127293934018190242246768648318848933491443344254343628446174282854552647989261$ |
| 17 | 5 | $-15.2077116087175339920234843410647461408415611993728501240807399575697491171043$ |
| 17 | 6 | $17.4865191073256481825850823772939122750080598749131011368060883790920910935857$ |
| 17 | 7 | $-0.0519770490505850045750408385495271320912297081008821396011490898547092711601375$ |
| 17 | 8 | $0.303180805998650355440271222785041440027004058633111221793072065466050643439772$ |
| 17 | 9 | $-0.234178838362213826010826517833216444141972590442203698265273409349909733726526$ |
| 17 | 10 | $0.0864360276785266533859851222191086679250107894622673343975218886143036904409586$ |
| 17 | 11 | $0.206653201092832259455334913932532503164388694575332685894850960139068292412507$ |
| 17 | 12 | $0.168712573780079157371500494325251868013473499268423639675034421770020813331602$ |
| 17 | 13 | $-0.220439165329232169667407632240478013974653613629407782403883928644413850467272$ |
| 17 | 14 | $-0.0666316066784783845871028684545917289606078233692147920394903396769624174454969$ |
| 17 | 15 | $0.0209527122371712956857405706957762368693002533562466823859165077347343649498497$ |
| 17 | 16 | $-0.0550305282103751587767610936777095390941798967868813447251959504921519635308268$ |
| 17 | 17 | $0.0236880615086330742660278376000056432468435185707180490008384455358721258616999$ |
| 17 | 18 | $-0.0468188847241078799261071655393546433854134445674621166093490162140274606066431$ |
| 17 | 19 | $0.179668473763975825391857051188436152318243381626570707351809972513978235114335$ |
| 17 | 20 | $0.0120794186701755492199782733381752288622928356527555663395815490286399478299538$ |
| 17 | 21 | $-0.0000443419352798583357522550934938080462947420554262880081758243067838447539274542$ |
| 18 | 0 | $-0.0115571814602882796207714656840981781120954759926890466282567212533904583969519$ |
| 18 | 1 | $-0.000049575787371619295802377881438593161077231268844548616846867234894764123833071$ |
| 18 | 2 | $0.000129975547775087691538017617003398251855865300900502926448507483039498214023048$ |
| 18 | 3 | $0.0127293934018190242246768648318848933491443344254343628446174282854552647989261$ |
| 18 | 4 | $-0.000106559166037469979488777176984745801448241978936692976844317322014453791175834$ |
| 18 | 5 | $0.127305443017553350895291517044395293289706294689465829525919439359756432685113$ |
| 18 | 6 | $-0.146381593698615160094172047980090107416874168008240239484638601334401457743971$ |
| 18 | 7 | $0.000435105650763180996700369359345286789996528912136668138511164714272348275013972$ |
| 18 | 8 | $0.84179470751942750135497212192768675375350822270563698479279981924620704041926$ |
| 18 | 9 | $0.00196033706648857964206258960322220415974796547742952621538633536463000181739804$ |
| 18 | 10 | $-0.805946942981427959667845018622344568444819328712611846954861971622120816182878$ |
| 18 | 11 | $-0.00172991689959704007613196722226044904559782780331743785962234306253840074550862$ |
| 18 | 12 | $0.805888531630173162446807873298838733282693154910537258558845274951054559946113$ |
| 18 | 13 | $0.00184532073744553006742858220563285299169478386522841218099224077688364642996351$ |
| 18 | 14 | $0.000557780580367698853460890316351181740213658637296616075657269638116696931347202$ |
| 18 | 15 | $-0.000175397481383285153052891522942442850051243230266845520537990686343729875606924$ |
| 18 | 16 | $0.000460666663963820806136552144084230151080219126364539696602537186566790095021024$ |
| 18 | 17 | $-0.000198295393953613629964323079809176286302103273602739854291151512121240750607655$ |
| 18 | 18 | $-0.841723115311819819492633397740995631512340625761281878755667621560027358305765$ |
| 18 | 19 | $-0.00150402474989723087433666392688316049826047253887536067838865472531810122249405$ |
| 18 | 20 | $-0.000101118155365314956336923207954988473213689253805435051313207700239962365988228$ |
| 18 | 21 | $0.000000371191265346074256585101310817129633612999386734067763478104444137539587522607$ |
| 19 | 0 | $13.8072787217468946393921245140310766806119054930221278806479456050745950367735$ |
| 19 | 1 | $0.0592278244000967115834749674213129930165045796141571660582810821417547922867029$ |
| 19 | 2 | $-0.155280820095179237692529050268114697956976752760354214970595806782011219173346$ |
| 19 | 3 | $-15.2077116087175339920234843410647461408415611993728501240807399575697491171043$ |
| 19 | 4 | $0.127305443017553350895291517044395293289706294689465829525919439359756432685113$ |
| 19 | 5 | $-152.090865803103992029690977142549589538238413343288778732603131618716293782441$ |
| 19 | 6 | $174.881001122558629973410166031595107890392118191375593604401498853446244676603$ |
| 19 | 7 | $-0.519817484404580048608347557357092991935631934056100668006893339252362123867459$ |
| 19 | 8 | $15.1213928439423226402257052731349599104747080591720116392623769784847698882458$ |
| 19 | 9 | $-2.34200011123683976696966271148645265019857521174115338295946800822212925645591$ |
| 19 | 10 | $10.1451341167354976175169321143318557683481157075965905059648288268398570919919$ |
| 19 | 11 | $2.06671885184718538198086393631999281774348781777506829696811068581647004548241$ |
| 19 | 12 | $-19.3181751726301113201378343065662713698842751568773277498294906059830199463367$ |
| 19 | 13 | $-2.20459095848568745392538733295190065442285247831480697987962586727806261956759$ |
| 19 | 14 | $-94.4903442242616921026778539228165760457636816261964976132284292545501448694318$ |
| 19 | 15 | $0.209546066302832136798736402007409928985281724724657089087474100530451814748044$ |
| 19 | 16 | $53.3297101482531945109088865121365545810704956343197836487003123751243322655358$ |
| 19 | 17 | $0.236902032122964803984454501561729753725940822901233327197818320544782164020975$ |
| 19 | 18 | $-14.6107482846167713580282219988933352861274999898685763677622695973343972958774$ |
| 19 | 19 | $1.79684718091453557460763862016450292589346327953666344792195973190572619823331$ |
| 19 | 20 | $81.3561558334182691035780657783985493385034153491311405794593278411809048096538$ |
| 19 | 21 | $-0.000443459443578150431661327536272699037369338710291547618535752170093931014363786$ |
| 20 | 0 | $-15.8762376220756503309769657524890791574158566643668084363133540122121533322121$ |
| 20 | 1 | $-0.0681028487194569427829736206533864009987429296286903065474150804121432254774686$ |
| 20 | 2 | $0.178548955783659234047420560646787559000472584418008526929848784062530151045488$ |
| 20 | 3 | $17.4865191073256481825850823772939122750080598749131011368060883790920910935857$ |
| 20 | 4 | $-0.146381593698615160094172047980090107416874168008240239484638601334401457743971$ |
| 20 | 5 | $174.881001122558629973410166031595107890392118191375593604401498853446244676603$ |
| 20 | 6 | $-201.086136186649172411332612771210625483297320487642134469352000144116770617227$ |
| 20 | 7 | $0.597709807184408047025121086130358236371169966468337817739876223861568753753738$ |
| 20 | 8 | $-24.008840032413742191115847894134873096681214346281161385961825252216141912578$ |
| 20 | 9 | $2.69293834261204759610952007123060200948732557957137523319992822505600290450308$ |
| 20 | 10 | $-14.8399398539905251353607130094027227231532928829523313581961670232327885717437$ |
| 20 | 11 | $-2.37640741895575664457986122749607987076009617327010585956714590407915518693009$ |
| 20 | 12 | $29.0522142268430932690632366799283079340833918112725439674281634916786486893565$ |
| 20 | 13 | $2.53493904351124867521514728933658167245927309524940471048012244409117177880212$ |
| 20 | 14 | $240.721780849612650081293689808775297725515081734585791032121879970185556044593$ |
| 20 | 15 | $-0.240945606186334424690565415684910772455353360394408347146753882907255340319936$ |
| 20 | 16 | $-22.2663743947467197140920905880533285099840876953456592733874331218169813551949$ |
| 20 | 17 | $-0.27240074101009620772702780657546839727901720110344358460639598368824065393421$ |
| 20 | 18 | $13.4706128035414202955715286683628805665731381749352567364560344796932551012278$ |
| 20 | 19 | $-2.06609668636765731301996201928448174589071907707649771246145907884648776560603$ |
| 20 | 20 | $-128.108726704637350409652844878075947612265000466813975017991966450907584214192$ |
| 20 | 21 | $0.000509909855800275120420538923312375483368083382223812747762970237091642663776777$ |
| 21 | 0 | $0.0471906373450658401765777920460873662699580521896343632490107667677246722850953$ |
| 21 | 1 | $0.000202429373544838738663389853826352009905187878101023792134434666278793746306073$ |
| 21 | 2 | $-0.000530720137938151460837193725522186004836307709728669700993209277012779550343593$ |
| 21 | 3 | $-0.0519770490505850045750408385495271320912297081008821396011490898547092711601375$ |
| 21 | 4 | $0.000435105650763180996700369359345286789996528912136668138511164714272348275013972$ |
| 21 | 5 | $-0.519817484404580048608347557357092991935631934056100668006893339252362123867459$ |
| 21 | 6 | $0.597709807184408047025121086130358236371169966468337817739876223861568753753738$ |
| 21 | 7 | $-0.00177663672085684948366482965241741476085026051281900627069812173755687451175248$ |
| 21 | 8 | $-5.48107056402360877806153295660635337031065649178960472961810364236388622560932$ |
| 21 | 9 | $-0.00800450835669800470345857526594346466192631497295251714029008974427281613436332$ |
| 21 | 10 | $5.19640881426367685662540058194896064287222485110145450113180899410773359489833$ |
| 21 | 11 | $0.00706364967327840906404129817765955105574458018914542927396397756386901716416162$ |
| 21 | 12 | $-11.922343611471982785254847824979514954969438453426643687383510369019013110769$ |
| 21 | 13 | $-0.00753487015890025818064309382923061361646478651573645595105634826573974490728811$ |
| 21 | 14 | $-0.0634232068674123037939617361259395031557272107404724054575629853982448702483017$ |
| 21 | 15 | $0.000716188368560069687812790244440207495132222564314766971532932624549763015521951$ |
| 21 | 16 | $-92.0575980599675724116016758265286636900066851412145541113330307754244363399098$ |
| 21 | 17 | $0.000809685826550007846344397321879391584314114151908661982004734595625123821081621$ |
| 21 | 18 | $12.2066091153076487735967114333998112178886389912943842182478012149200144253972$ |
| 21 | 19 | $0.00614127992835315122039040110651623257409122809182070327736296246211662025535063$ |
| 21 | 20 | $63.9710695472147497721250893647120143569125290564712665937418664267113168560327$ |
| 21 | 21 | $-0.00000151565954456907538264744769673626925020768642837065532721059147746140890269619$ |


### 12.3 Matrix $R_6$

The following table gives every entry; indices start at zero. The entries are exact rationals, with the coordinate and equation orders of Definitions 3.2 and 7.1.

| $i$ | $j$ | Entry |
| --- | --- | --- |
| 0 | 0 | $0.939425603988908562397760842100190210056030431914113667989859684525169523093959$ |
| 0 | 1 | $0.0040949885168888888825447495738270729888229973222444783811507872668375133888689$ |
| 0 | 2 | $-0.0107250809971177992710752975805587252737615031707424764397594612536990951913889$ |
| 0 | 3 | $-1.03461885134122824878466690384596841320577438873020992693054777286223523465541$ |
| 0 | 4 | $0.00878958495651729787341516759946150276798754600430587651930256580186361851450342$ |
| 0 | 5 | $-10.6268522556360420426229354579435970150705181490770033279906750378797436498511$ |
| 0 | 6 | $12.3270596316203403035590875672381710620409639950421064102059836293742948870501$ |
| 0 | 7 | $-0.241465167972212873417583856406401826028840029349547548938622349084329198143961$ |
| 0 | 8 | $-1.84030495642550355773426318900520814118766983282777782716859171126807843027364$ |
| 0 | 9 | $0.435366710675307489315533255040907450498238865389487193602950732784122428449548$ |
| 0 | 10 | $-0.117800290674872090903092275044179822817730833343821890779151921962695505708158$ |
| 0 | 11 | $0.142568380707318874589271041842608358142901150417004548292095369939838612364831$ |
| 0 | 12 | $0.113850448165781546027242696711443411396330459829440706495750576970714576338163$ |
| 0 | 13 | $-0.152433855545083830041032051469728837146671573786022507706033046024140915075445$ |
| 0 | 14 | $-0.0355626600874914554347677608136360900128504309236737027109944392013642330274907$ |
| 0 | 15 | $0.0161124704202050467791049101474823936069126147411561141141176311701070074102337$ |
| 0 | 16 | $-0.0324417900210611051610576086162254765779662985700065599281246586816267993680744$ |
| 0 | 17 | $0.0149448424639766447836927759924192427781645279281690790196773444883319553368587$ |
| 0 | 18 | $1.84397876840146748068175295547588425564876538785400020210435744481642860061346$ |
| 0 | 19 | $0.124247208526791957675764341987261936570780436223993842753613417613714633133386$ |
| 1 | 0 | $-0.79232997334944743244352626568350762323695295299657962226634076231207492706081$ |
| 1 | 1 | $-0.00345379360395969592038983758081810820575116737784455680926360973125601509382167$ |
| 1 | 2 | $0.00904574359537824699540142831440511821441835313904573765891633834783502705177269$ |
| 1 | 3 | $0.872617824582637072192483065181777250852040959095578736183169286857095328467446$ |
| 1 | 4 | $-0.007413308286232614690005960187476153920561946832322866425037532922629454073667$ |
| 1 | 5 | $8.96289554888056034063853516086314656132380930370194924316843982085266659330492$ |
| 1 | 6 | $-10.3968837850773651093478925129586670865464381823406213248535882624052479812308$ |
| 1 | 7 | $0.203656456979537590506765514467120705608375233858097426228124028214256360411602$ |
| 1 | 8 | $-0.012571728347026848669174017625784403044377125094505327523905468218636648292025$ |
| 1 | 9 | $0.136720720039543968513578862797960076074640369663425180236678591268564209521978$ |
| 1 | 10 | $1.53774193504551041553924627428138107549719910412231998649022111154142713718614$ |
| 1 | 11 | $0.361590641581124824043164432930494225461708709008624529225518487367568510169982$ |
| 1 | 12 | $-1.54154443957983655778132396291314580907370337204957211019271143613704878190388$ |
| 1 | 13 | $0.128565702476867736344617088410572513441533006760212150633502236196250309361534$ |
| 1 | 14 | $0.0299942447807609915592721054953078001054859538981517332136497322414221218934447$ |
| 1 | 15 | $-0.0135895734632175861940028320980256861277750977854173982042765643994183105047128$ |
| 1 | 16 | $0.0273620417770721091495639149318039822128238598411734780513501462328630864600518$ |
| 1 | 17 | $-0.01260477315171634423145459688961529470696001971932714133615248376562005309308$ |
| 1 | 18 | $0.0176986122018933333439234856772726121214327474405782857133460541000117249095826$ |
| 1 | 19 | $-0.104792531737232285864717112382771527912238539605755938774991252406697949967036$ |
| 2 | 0 | $0.867586012283922645286942895121150382488819399541444922121123353982651079822005$ |
| 2 | 1 | $0.00378183726591087433987966678642332273864104357869983248651842663350479692892058$ |
| 2 | 2 | $-0.00990491446496849799738995326121612650858368235834420961846221546709799314026207$ |
| 2 | 3 | $-0.955499658150159013037403003422437505740536480832605171326261275770985014416156$ |
| 2 | 4 | $0.00811742934158480956611634936786812574704043299604248891197537443140319715395937$ |
| 2 | 5 | $-9.81419745475293198566335229065935820639283862095312066526783180449182050876637$ |
| 2 | 6 | $11.3843868674350936019912230060520052869668597933867740298934930085843390993798$ |
| 2 | 7 | $-0.222999885565129979377058984657408619004729031220088713450096943605666136300576$ |
| 2 | 8 | $0.189277068277852374631871771199099643772529247704329082028743564534432828813596$ |
| 2 | 9 | $-0.149706546874984841719552690866189451577914714709652733447111385283559577750567$ |
| 2 | 10 | $1.63593934331242100819490371835184853815753000046668030302121645523308624405013$ |
| 2 | 11 | $0.131665916247583217559752019499872991847019591906654123726897235344239438373655$ |
| 2 | 12 | $-1.6317792103958419096770600216787039009722564620794983011592505887355841929538$ |
| 2 | 13 | $0.386582615137872112547240292752796611525026508183484699459691561238853177456393$ |
| 2 | 14 | $-0.0328431185189195725071193478161713988343435163885375473210417885339402239298943$ |
| 2 | 15 | $0.0148803203793383090782333730491256102300513117754583170356045336795767235225715$ |
| 2 | 16 | $-0.0299609070864296653842036690318907550578529649637264285725477207718319481087106$ |
| 2 | 17 | $0.0138019830654796736291120186021314735198046845892873309317197121772293762865911$ |
| 2 | 18 | $-0.193831829322525002111159382212526911049550359484109079725681313442928805041778$ |
| 2 | 19 | $0.114745797565510170704109716983593665186172648792767917383079138437605544214297$ |
| 3 | 0 | $-0.0324196724348836754849624487358516339974004063374185543541887648638194687279392$ |
| 3 | 1 | $-0.000141318467134003429046589423532972828679289391349452437605727370637443439215242$ |
| 3 | 2 | $0.000370123627978378844308624253103234119271343361587546578094131262057247044661436$ |
| 3 | 3 | $0.0357048010113999897671033881192112441958078202549533638206936927072333993035538$ |
| 3 | 4 | $-0.000303329464216132255945269577664910840857431940908661722767364325703370130381597$ |
| 3 | 5 | $26.0609072539910371404407311441340042480439283986628350187612283118818594604089$ |
| 3 | 6 | $-40.9343508452676368373398207709101451986012851899238369660756540042746874035404$ |
| 3 | 7 | $20.4001002885610874001269811941218614390300888078938780781199076097242800283338$ |
| 3 | 8 | $-0.0648496383164466899757019768784785580883597441679943931674065148421609095732791$ |
| 3 | 9 | $0.00559418563960924134591851503078598800507102403510855430682967639216179847087551$ |
| 3 | 10 | $-0.0231905981967158382886204285382689610199230445182364928131610526894385277606132$ |
| 3 | 11 | $-0.00492004921143030474860260429194751886637773398035940880968479417710162944218637$ |
| 3 | 12 | $0.0276554251066672036788494949618002398369633886527680685452641072788667638294857$ |
| 3 | 13 | $0.00526050774406649123395969848623651573759296034979057845392218235421606822451389$ |
| 3 | 14 | $-0.340105500003961242174780360207745222195048045986412362397347069512029499206993$ |
| 3 | 15 | $0.154092517125577623827228324007452658838803495744566133963098939712116905825019$ |
| 3 | 16 | $-0.31025888358720934265321405989170417482533059976234207962902610725901676027164$ |
| 3 | 17 | $0.142925841491789956414631364409606879923676244293752796572409768116710933764518$ |
| 3 | 18 | $0.0545198435145407552444359137509409479606996441989684842856445216483900489525205$ |
| 3 | 19 | $-0.00428778370983684502432783195068790989007937979969378481988841747633673878169756$ |
| 4 | 0 | $-0.044592749340255358728521501688275349473858050340053849048666959663878029476327$ |
| 4 | 1 | $-0.000194381328025849972471319519548671085903792478706031005800625124868889206885689$ |
| 4 | 2 | $0.000509099226727118958427709219346721812379307984269313655776053937713098498419204$ |
| 4 | 3 | $0.0491113920087566923502639759476183470375015647260716978195902880494827013477501$ |
| 4 | 4 | $-0.000417224905417292399757268727222934646666706076864929874936479484566779477155916$ |
| 4 | 5 | $-31.2135969439976695394326378086978485084464946081212540584635627804833159401936$ |
| 4 | 6 | $49.4209030718511341620324937660802835016971802327391496490762757874780944504817$ |
| 4 | 7 | $-25.1610448970618509094151952384066044628688232446937874344476854266752897729773$ |
| 4 | 8 | $-0.0891996571544601688571855691761380797751173984746251173408689823120683975614825$ |
| 4 | 9 | $0.00769471432788232250782443295123476554974378959101550549599282879296349205437743$ |
| 4 | 10 | $-0.0318983029367069502379204117287980512775399335963573676912602894193847058842989$ |
| 4 | 11 | $-0.00676745027784300129733104555960602925019046692247677568696761852765704921463321$ |
| 4 | 12 | $0.0380396021013726929381384150693340770597042476019021016717899465837162436069919$ |
| 4 | 13 | $0.00723574563268010783218239064131541046668362457423396204293727144936126466565354$ |
| 4 | 14 | $-0.467809764006126650161110493963375766154419575189844548867804958036762378658094$ |
| 4 | 15 | $0.211951832801254037268010890439684809366962520084043054910175617151560389806549$ |
| 4 | 16 | $-0.426756212734125848997087029115820007162549829765436889261910091990003416416202$ |
| 4 | 17 | $0.196592246164418318965615717009794243505983794511758017175190587462857708450159$ |
| 4 | 18 | $0.0749911869343224588691224667995698269174561150224781822583904277790990113078846$ |
| 4 | 19 | $-0.00589777902852122699887753287212669442170775287275925222426391002390237470198946$ |
| 5 | 0 | $-0.942272857645766440986875728318118915061028075895290331688237256787126175671943$ |
| 5 | 1 | $-0.00410739979350301932782058788399442086903950254909698920177807666499857381808712$ |
| 5 | 2 | $0.0107575870582252216058615454532666692018369092334056899265662989346235701471487$ |
| 5 | 3 | $1.03775462100242027031793884926869853917624561093977982543020338598383677031081$ |
| 5 | 4 | $-0.00881622482858746805010275421477807030614444069984349001402852078128384329495671$ |
| 5 | 5 | $10.6590606006260784789512704434212500970157576036279037324291528372646047554589$ |
| 5 | 6 | $-12.3644210421092655547502950899176514094630892541128779937469219835974773511089$ |
| 5 | 7 | $0.242197011536613745554232608433382493195640218705077125929956250921798703974904$ |
| 5 | 8 | $-2.08754294725122151130824298122429901548557344639641574411343595839758038980112$ |
| 5 | 9 | $0.162594156354387707240181965275548173524486179461867022167895721655766511199803$ |
| 5 | 10 | $-0.0561228469919697472373116078503119044464559047130821237959295098498965587508865$ |
| 5 | 11 | $-0.143000483410925846465141386677377384337509081005748607612034368567009098032992$ |
| 5 | 12 | $0.0599254093676207372679289801306345843890835391520127020224641554706234729406593$ |
| 5 | 13 | $0.1528958589765283170821485685944040529075130857087545093960399187578448605596$ |
| 5 | 14 | $0.0356704450079276875099751912922286095369536495205733602909351020395400616068364$ |
| 5 | 15 | $-0.0161613048251117762138048438683895371514860943782068174742093614294114638145816$ |
| 5 | 16 | $0.0325401160671900035628156307516522390564160012541100999214204026318078931756575$ |
| 5 | 17 | $-0.0149901379692045657408018186497995754410314312297207121083374427524668053088266$ |
| 5 | 18 | $2.08388576643579622108787503008377720035880638436315900627380100047746798430362$ |
| 5 | 19 | $0.472845775786824562468370029348190996193968584484148131787026485468309205275349$ |
| 6 | 0 | $0.0932924261335445318505107487910321404681296069302901026555750857263711010814771$ |
| 6 | 1 | $0.261166512171990053576417792488068329429483806408820581588048089492009607962109$ |
| 6 | 2 | $0.840473716841921595164235184274604744613032447898741054475778900325356116479517$ |
| 6 | 3 | $0.170568605901308617008032200909335564084964375779450480487525988148826217289693$ |
| 6 | 4 | $0.883386106048566974034720177447116042630695921605581441116589994766539153481645$ |
| 6 | 5 | $3.99414358619486722121903639027546287901957850789378347142771883900464068983161$ |
| 6 | 6 | $-7.0860773724401586172886798460748362222428866625787167301179541341277710422136$ |
| 6 | 7 | $-13.9584219821661384418190547495011738664848879042956778636901433574562836078573$ |
| 6 | 8 | $2.44363262072039277286027245602505388260924780986837113138543959263011485764112$ |
| 6 | 9 | $-0.375284940173849333266175731421841662000700660544633100659769113202955985797045$ |
| 6 | 10 | $0.243704527081243692304169515587531099975970182646554590708851102391383403908889$ |
| 6 | 11 | $0.0170725468640165048297948754345331446941511624705438506194990353616805617954327$ |
| 6 | 12 | $-0.244680461895306727724617464109508753696067166952590807423912388239430130510644$ |
| 6 | 13 | $0.0241750224052301943113188802522037979994442461963094647992653516722515272502138$ |
| 6 | 14 | $0.0928422259193539227275187920775473800122936696222310014127671067437779631174821$ |
| 6 | 15 | $-0.0420642779587162345119038046268916657872684274950517010042327776294537845380483$ |
| 6 | 16 | $0.0846946766904819900718676374967208920034792349025019993806814197387531797401529$ |
| 6 | 17 | $-0.0390159914066075968490522472976222005575430386738377385587003806615922894732937$ |
| 6 | 18 | $-2.44094707917025212338213486959353845142526945722786218160621455998364257762378$ |
| 6 | 19 | $-0.361142561968815363173385122577643350882045086847548687787995416704264407271749$ |
| 7 | 0 | $0.28911531201328894173305322927221468178934534322577224679600755013745929505792$ |
| 7 | 1 | $-0.254822185728450739080625000860419812962624330257342072852267436815001096480302$ |
| 7 | 2 | $0.809825122423473206087715792519936478160510785513173782406145124345684334020777$ |
| 7 | 3 | $-0.0503226057463418065114703529116273815542214849293661957954777230132474043218249$ |
| 7 | 4 | $-0.84853993467949213799040658660117571250728894931058343446233214357989217700551$ |
| 7 | 5 | $1.72720936878088346134193442412717929663958591290474631002395461746815806011704$ |
| 7 | 6 | $-2.11095505034059603464256174725500027975491329460298029825709867757558761968363$ |
| 7 | 7 | $-0.486302338559482550244200950974747172165120857864241449848079435141139699947755$ |
| 7 | 8 | $0.264172846647079877074341789988959237943165496979305670650154296380497071284997$ |
| 7 | 9 | $-0.0498906928448279418199276231514955716027594699901139368417597480239007851314549$ |
| 7 | 10 | $2.22313241648725107314163504715243150523584346557717728864006794577438411615258$ |
| 7 | 11 | $0.32585488126346148024014476948755782602046784410379616596728576635044347690267$ |
| 7 | 12 | $-2.222751959080265836894967333538878062511658542713047771236174352528097207546$ |
| 7 | 13 | $0.377767680027333883416417076756654885243467315817633994690566843892971354275258$ |
| 7 | 14 | $0.0304750992206164181952412110828339334677225075300885490773211298192729009798333$ |
| 7 | 15 | $-0.013807435482524740474630394000266921399577790105601229596119238537311492366126$ |
| 7 | 16 | $0.0278006979048788042660789760772556146056010116463969350399446085112908550344723$ |
| 7 | 17 | $-0.0128068472888608470101026292069534035501813748753196414044527462766948479538178$ |
| 7 | 18 | $-0.263392094860636899766328727985921891007051208357393038322456121716105288764928$ |
| 7 | 19 | $0.00640332295203015995460842524982426671974179624994479132047306201852056463284038$ |
| 8 | 0 | $0.219531601536570205314193822968587323798619019472548367146105282433025223537581$ |
| 8 | 1 | $-0.269867116779904925992406911428656223324965998223093413415947887263050940173284$ |
| 8 | 2 | $-0.807676880215490700788617487618322162245691562990234375867118929036965882863041$ |
| 8 | 3 | $0.0419444981944890514422848294974138760926197074014706439409427504708554341381491$ |
| 8 | 4 | $0.845620377237442576862202930744640989070369025587981337090045355558434550224499$ |
| 8 | 5 | $-5.37926387829643727392748196911329358375954395033538462147775458437951730321947$ |
| 8 | 6 | $6.44175184207362094510884407474862317498167478256298637055368547506195944913439$ |
| 8 | 7 | $0.286178730596092819863826905631264039030448626829804933962348920524514808211838$ |
| 8 | 8 | $-0.233476357690734101298397910591408240221768448234263303320657413060289527304976$ |
| 8 | 9 | $0.00529128586617228004396556565588867135541449056169459386925052928345251641341993$ |
| 8 | 10 | $-2.21487922771205801047702085514215627665157648370094085104609397043906447941838$ |
| 8 | 11 | $-0.362783230552579001891865026062098017860117021863742043716059825036173878695554$ |
| 8 | 12 | $2.21582057664863042257176699369285784839085133238903840088766253629190560104592$ |
| 8 | 13 | $-0.338570289703608061553256368387287000046772189672037937192977892994853247829352$ |
| 8 | 14 | $-0.0465434437382544072024913729061994117406527933006316392678680096478443188222332$ |
| 8 | 15 | $0.0210875637154847331631154325564727808313263266585421354565905935422339312167935$ |
| 8 | 16 | $-0.0424589337495768566864232470244471701315733823898276639595191321905137819440001$ |
| 8 | 17 | $0.0195594039559440045895513820705624147151920822302690331471083428210330250328474$ |
| 8 | 18 | $0.230995739317236240190422587428987357184130545189009405952069319651676700909549$ |
| 8 | 19 | $0.0275569389662614731006131752674391176101944586549387528864275642047371294150952$ |
| 9 | 0 | $-0.00138108917056925245957230008430883341149475862273927396347532846034023356823465$ |
| 9 | 1 | $-0.00000602021519348269930201502840324667963907860644514356234323641314019839027296376$ |
| 9 | 2 | $0.0000157673935601741972385713805680836470187832501879688618103818151209486552249251$ |
| 9 | 3 | $0.00152103677522402308211256665627082729305478393067334894573051597745756714703107$ |
| 9 | 4 | $-0.0000129219392634180074453186865046967252660689796731280686947243390363237693495123$ |
| 9 | 5 | $3.65945844799145805515720810724911910673871507209342528765480298175542109187796$ |
| 9 | 6 | $-0.287006841778405286492282131546480604980334052497241805747860961323199592161526$ |
| 9 | 7 | $7.26044601645726462932874092889536941981556245414943328950477334866162273585481$ |
| 9 | 8 | $-0.00276261684549925134327126601030110420612980733491877046677235020485945422530085$ |
| 9 | 9 | $0.000238314227897783260758064604667307054257401570051974476910897014475780954075224$ |
| 9 | 10 | $-0.000987927441057193984285600730497941433298912068002069738306894780092229596623683$ |
| 9 | 11 | $-0.000209595784726767099456979509182686390856789808093883428302457506496646733732244$ |
| 9 | 12 | $0.00117813059953096759375608355022732415102475507706949220654840602209295727675715$ |
| 9 | 13 | $0.000224099435045756594583326624269469812533847792257938350022541631983196312328428$ |
| 9 | 14 | $-0.0144886110077131968933077907680369862591977535564880715653163241473216520685739$ |
| 9 | 15 | $0.00656439410655186438186172343875299729870534893669013153362727373271658093600111$ |
| 9 | 16 | $-0.0132171349064631190205771140175129665001895115538438105325924324964164740149396$ |
| 9 | 17 | $0.0060886898926965331450809121454772860873119380418668988485293583096303669050948$ |
| 9 | 18 | $0.00232256404225858122072416200339404151044759294639579802984734479141727355354866$ |
| 9 | 19 | $-0.000182661057396342829887821370589045148144393569399825343168483105653372361932973$ |
| 10 | 0 | $0.00226574751160222839601365719547946847434334749130702569657102951699326844934577$ |
| 10 | 1 | $0.00000987647132756905791218110610273999164520283298222776130686704265158621685219617$ |
| 10 | 2 | $-0.000025867216603177557014025163625687456029129720313463435622540032956658259574573$ |
| 10 | 3 | $-0.0024953387239281809711547617609190945080579797832355950364895426809767390715434$ |
| 10 | 4 | $0.000021199103110117676827226966301641679090007100504112540259958918485432320200022$ |
| 10 | 5 | $10.7916337985501909267733703865891909012417115670444693736802815225977400484168$ |
| 10 | 6 | $-9.76926976053233645955519722161868512697969434401968556669435220142309510311158$ |
| 10 | 7 | $-7.18982209267611462734399430252714525182905879110250592721614648510984836409997$ |
| 10 | 8 | $0.00453221441206461158019854359988457462032476092841830934259668802568982727161362$ |
| 10 | 9 | $-0.000390966695232466436488115138887631832655869426902556185485744295832685336815225$ |
| 10 | 10 | $0.00162074556003960340978678050513202298936822497763176445928297770000692662934587$ |
| 10 | 11 | $0.000343852618503445331560382503152751306174090673169660459850355688978682718865042$ |
| 10 | 12 | $-0.00193278358205465436118007926801135136641404665850031323181488967256302515216312$ |
| 10 | 13 | $-0.000367646599601606091464444879781956152134761999236001520712953316000559026439612$ |
| 10 | 14 | $0.0237693083378302744904325995340396300990108604985965676914128171098622962157564$ |
| 10 | 15 | $-0.0107692247025337345883313869360648950338032249882823289402967206642870376997696$ |
| 10 | 16 | $0.0216833866798669071378014428705219259376214838975389235087619238186483706268788$ |
| 10 | 17 | $-0.00998880757830332976802336184309030265585200708367694125048850562083514230755745$ |
| 10 | 18 | $-0.00381028525270035893865111597849331416718396776480875109847022230602441427835518$ |
| 10 | 19 | $0.000299664818957207989468418705483429830230111100498437253332867623368725126646906$ |
| 11 | 0 | $0.397176001975563345165800841856995218881057441502821531669216380646491345441911$ |
| 11 | 1 | $0.263518934080231525138003953723308213546100397845077820481203603956531040864898$ |
| 11 | 2 | $-0.842611859226861097103558035393161456718841323951554966440992937416238858032903$ |
| 11 | 3 | $-0.161216196400751704049804482390473791408359402398992682542231988902915075181505$ |
| 11 | 4 | $-0.880474825770364112575898429870378264147599936003810328215868441324530635251484$ |
| 11 | 5 | $-14.7931813232209623905640673391276585998800471096010398213090033764464425870239$ |
| 11 | 6 | $12.811557183017875452869876871746379058976153571135638030263580499387693908036$ |
| 11 | 7 | $14.0879216663483781702146821684764328316330564722831870172872470085211341278383$ |
| 11 | 8 | $-2.47609870724330390887314361301218835074483981220691303759076081377115277466746$ |
| 11 | 9 | $0.42003699961983967821786783945166888702644410782990302534085317922476115889782$ |
| 11 | 10 | $-0.252590533975419164394284887372440410116306477432420723023801160646617737675814$ |
| 11 | 11 | $0.0197215455913243385898219781460369822301807144243262500977271251415678040123181$ |
| 11 | 12 | $0.252366497309465828815241799673312995032263668858030998797690688126091804886132$ |
| 11 | 13 | $-0.0632288655644001666775984703660591968565384581349274591261638908863522709820091$ |
| 11 | 14 | $-0.0860545787318330113173934390201845455791764907937964073483167198777471894222647$ |
| 11 | 15 | $0.0389889803217381120298884295679977040906177669937029925504308695561018024511493$ |
| 11 | 16 | $-0.0785026926191877257687476954025382959149388365027663834372763873817621494425643$ |
| 11 | 17 | $0.0361635524251312358925459441316262059610724003606983892180039314284588877967268$ |
| 11 | 18 | $2.47483115592409456067596796412557225790492649521465876704522423956267830620396$ |
| 11 | 19 | $0.3270652962889628649585829247254855818700231144115665316709304059632913604591$ |
| 12 | 0 | $-1.23443557236175327768759236017990074572347667621746432165369102058196442907882$ |
| 12 | 1 | $-0.00538094711512698472865399645908091174911861586189217162191760180008691121196184$ |
| 12 | 2 | $0.0140931026821998209746099935428952747501818550423823866313104329961423974465575$ |
| 12 | 3 | $1.35952257263231658830144762506685342013317523947416272279553382455282122374695$ |
| 12 | 4 | $-0.0115497983986699927800292448251191283339242137714820504641825114599005385409452$ |
| 12 | 5 | $13.9640269446443015526026930073142095626570145799394647693898792111851200402059$ |
| 12 | 6 | $-16.1981543267330183534513057170875499671933821939117901963431436404306033304703$ |
| 12 | 7 | $0.317293026255142105182249555563215194209661843002912487354175661939431771502191$ |
| 12 | 8 | $-0.0379266356037927150336873102110236547881335916564595599727415846409770367397788$ |
| 12 | 9 | $0.213008375263484144589505222590542051417729394473700461165234803576922020898097$ |
| 12 | 10 | $0.154780635960268994233898228600943795064125131357716729204361313759574231256894$ |
| 12 | 11 | $-0.187339454973174631964534609883909304963632195772731385768149272105399545976356$ |
| 12 | 12 | $0.0891710815289665811400584687258895820117514320549029932484725301326009447866091$ |
| 12 | 13 | $0.200303007410181279992954193019968970751914904919632603786431985432766849802005$ |
| 12 | 14 | $0.0467304834713950397355949114661391869555517565771662186404778019992061486108577$ |
| 12 | 15 | $-0.0211723063123607045934461507985255115867910353572132267133125223944877676399079$ |
| 12 | 16 | $0.0426295594489259890017352447041195303047586916770111439643167810217797091003938$ |
| 12 | 17 | $-0.0196380054817976393546334111376833772880574911188157699130796999469073980481523$ |
| 12 | 18 | $0.282965722229092886469606685810814299822365509651281772336512066111597936611538$ |
| 12 | 19 | $-0.163264843241308317958122247534464671974982754482619063685716346547389727316439$ |
| 13 | 0 | $-0.00538094711512698472865399645908091174911861586189217162191760180008691121196166$ |
| 13 | 1 | $-0.000023455733538524626180723519227257730438376455845512574551350671321973948618554$ |
| 13 | 2 | $0.0000614323192873351145528168652513417727592082918262156434763384499943856669612279$ |
| 13 | 3 | $0.00592620565134853079877541883298053806292427401529495703364318378219351974081501$ |
| 13 | 4 | $-0.000050345968445090098553207623724843426106231714301731336001811845866581749561277$ |
| 13 | 5 | $0.0608696737081061961956071636912858679742059066113980257378260909541205853354756$ |
| 13 | 6 | $-0.0706083118036337116257126081742996323743517957617716191749380530995716922361853$ |
| 13 | 7 | $0.00138309121391487230543260048087885213319888214204730994574778295839337329795677$ |
| 13 | 8 | $0.248868466640378735739784314560766096614077503061681293288200066374513321157777$ |
| 13 | 9 | $0.000928510833642794073640226898170859263023164743431568352298234394977144448009261$ |
| 13 | 10 | $-0.242220478329043687426708631094566655271317680948182917484334611089802859196563$ |
| 13 | 11 | $-0.000816619127281558151825699837595902584450866679540274467863603355450113519877063$ |
| 13 | 12 | $-0.258072020094760789391743922958321770562696458026547074021975318976468655593813$ |
| 13 | 13 | $0.000873127698202152259903608702795645279066863504820214969115787879924304405083237$ |
| 13 | 14 | $0.000203699784625295387308871011823527234686344985502303144738002577245629042403238$ |
| 13 | 15 | $-0.0000922908113820100432715302898734564567342217800326892667254063208244993582566238$ |
| 13 | 16 | $0.00018582371577073303519036961861406427224461037807189919810048157687442752828582$ |
| 13 | 17 | $-0.0000856027412932976035906420449604752412235067250672314463255943542846305531802061$ |
| 13 | 18 | $0.251428614385506575937406269743390759864074750667164692770687518558354779907744$ |
| 13 | 19 | $-0.000711677066758673957432712103411267747348046638733227741572331211682312496506887$ |
| 14 | 0 | $0.0140931026821998209746099935428952747501818550423823866313104329961423974465553$ |
| 14 | 1 | $0.0000614323192873351145528168652513417727592082918262156434763384499943856669612206$ |
| 14 | 2 | $-0.000160895835844256756534465085401516572894260466455348342628828721022538953968095$ |
| 14 | 3 | $-0.0155211755427774287354769020976263799698250862908181766611062456862290863618774$ |
| 14 | 4 | $0.000131859854362219025508429419309388797755272346618395376306542884866710360290728$ |
| 14 | 5 | $-0.159422225018484532770637901158488990888425612930856688557207600106473793917285$ |
| 14 | 6 | $0.184928446084887502521313793724686140840544179588357983674451422085316693254628$ |
| 14 | 7 | $-0.00362241926551450623469216629291644964440817546431889998474378847898090643135106$ |
| 14 | 8 | $0.80412880805689832010810026712646868604711422862523223277081372007944803895188$ |
| 14 | 9 | $-0.00243183927291841567907800388033839838807539230237948872506657489164881738103996$ |
| 14 | 10 | $0.769485869188662683241403697475940805400555516777349184290869845652938684582779$ |
| 14 | 11 | $0.00213878653084584552012717834959157684753430487050851406648177568689022618484153$ |
| 14 | 12 | $-0.769431898472157279648504724065780771509661558131504917620592492805551622389816$ |
| 14 | 13 | $-0.00228678670170229332035135788218888035432523982477054704657452229686702870211647$ |
| 14 | 14 | $-0.000533504961049692326274069874741439646297784507203189611275597709648853550185132$ |
| 14 | 15 | $0.000241716533093915976703057457737997236524244194501087962219896775607173616509509$ |
| 14 | 16 | $-0.000486686200610067359157504536380680613393140299032751106354644661085665841551758$ |
| 14 | 17 | $0.000224199977645712255928088833764206638801473181544947938245259931626930867012264$ |
| 14 | 18 | $-0.804196237913140607692292030289726509051282458368478595628287574604857541020317$ |
| 14 | 19 | $0.00186393543066071885496588587674707141235065559381956662753120191299221132331207$ |
| 15 | 0 | $1.35952257263231658830144762506685342013317523947416272279553382455282122374695$ |
| 15 | 1 | $0.00592620565134853079877541883298053806292427401529495703364318378219351974081522$ |
| 15 | 2 | $-0.0155211755427774287354769020976263799698250862908181766611062456862290863618798$ |
| 15 | 3 | $-1.49728480520095126307511355881860997251064347602168056375574080324509508145192$ |
| 15 | 4 | $0.012720154849639152632092681628196381720512094512999341563988853324800115002007$ |
| 15 | 5 | $-15.3790203888635164146333354256881868615590695424076420722381413440186251546245$ |
| 15 | 6 | $17.8395348734505302614324218632453504411718695225198848566542275492408884883271$ |
| 15 | 7 | $-0.349444751099793471307455456018049111020714171527130074314550280295002485342737$ |
| 15 | 8 | $0.302793646106839858272496576192238895520524904990761698835887900036693773795033$ |
| 15 | 9 | $-0.234592797562040084842771333967252080443558100060929922900137922059229533614126$ |
| 15 | 10 | $0.0838188056090692565973204010332479210720914019155457495874633875313262932551642$ |
| 15 | 11 | $0.206322811399045181104959616655264247605989512959801588791904349128963639274033$ |
| 15 | 12 | $0.172562500571189144012023133928373441691615532005718951407823489063895943267842$ |
| 15 | 13 | $-0.220599977866221812006793472521426015060108147109835785609606363782130151275898$ |
| 15 | 14 | $-0.0514657455859227544791982058950357296432660479174909658405508811887932352043856$ |
| 15 | 15 | $0.0233177243031560968332472041938016247137015165543479766505684669637843378848119$ |
| 15 | 16 | $-0.046949269471636781931960406925535141739421681356745796462440334071834621934282$ |
| 15 | 17 | $0.0216279507264208037592800143619184971515673708269982934322985431639115723342127$ |
| 15 | 18 | $-0.0476637918833380853338448363950311346894050596995303026874663463926735398109446$ |
| 15 | 19 | $0.179808687203635596293977065406040476212964434742367008649697211961637331478488$ |
| 16 | 0 | $-0.0115497983986699927800292448251191283339242137714820504641825114599005385409452$ |
| 16 | 1 | $-0.0000503459684450900985532076237248434261062317143017313360018118458665817495612786$ |
| 16 | 2 | $0.000131859854362219025508429419309388797755272346618395376306542884866710360290748$ |
| 16 | 3 | $0.0127201548496391526320926816281963817205120945129993415639888533248001150020069$ |
| 16 | 4 | $-0.000108063835842562290212270984666600243338546450906762201154196183274662116408889$ |
| 16 | 5 | $0.130652177930735726061577595522268419639093310043911729946201092651644243462738$ |
| 16 | 6 | $-0.151555432371714540958869183716466706485859556714536940267186267930280324780993$ |
| 16 | 7 | $0.00296870129847235059849934718740015667856949917766039429830305417133662827683999$ |
| 16 | 8 | $0.842472815978930518451353455199569566304581289463798432297998907154372604771668$ |
| 16 | 9 | $0.00199297869131765387966709735550225960507758404959647266910409897301416166015858$ |
| 16 | 10 | $-0.805960920192838455655883463553356061446464659068580668766690293317820253971684$ |
| 16 | 11 | $-0.00175281155655387760790549087474652801251521335819441063920206567600881938630749$ |
| 16 | 12 | $0.805891176983077849852560566661779607779214838575929533472026869698501411030247$ |
| 16 | 13 | $0.00187410295525486733020662342936120129722391811166091838515678083510580906555225$ |
| 16 | 14 | $0.000437226271869638700233812550221110286237851112689985895492088225062248382675222$ |
| 16 | 15 | $-0.000198095287447689190820497138045375527224479440212820318552412259858047073550647$ |
| 16 | 16 | $0.000398856634143499028161968422092945031483329113492851840882402845799626246478763$ |
| 16 | 17 | $-0.000183739847866495557256820150726122568384633664040492948639049543182444485576109$ |
| 16 | 18 | $-0.842389695332507743159524041880064319141943007817134866020502824563541628182826$ |
| 16 | 19 | $-0.00152756131405047512042576895278243926774853285306233999579880876168124901646845$ |
| 17 | 0 | $13.9640269446443015526026930073142095626570145799394647693898792111851200402058$ |
| 17 | 1 | $0.0608696737081061961956071636912858679742059066113980257378260909541205853354775$ |
| 17 | 2 | $-0.159422225018484532770637901158488990888425612930856688557207600106473793917309$ |
| 17 | 3 | $-15.3790203888635164146333354256881868615590695424076420722381413440186251546244$ |
| 17 | 4 | $0.130652177930735726061577595522268419639093310043911729946201092651644243462738$ |
| 17 | 5 | $-2660.02916044966404576619244101822477384841518318078577344689519598490298669418$ |
| 17 | 6 | $4127.94580558031042947274660253270021506721639896977305514817821941749794425476$ |
| 17 | 7 | $-1989.31448975356167562059880865440926022869837836174762647504350120009879401378$ |
| 17 | 8 | $5.25143456473828137371595837741919929263170725365456517373199295467078853754052$ |
| 17 | 9 | $-2.40956657294264095922846849272792417080136103907090045251697286711743628064684$ |
| 17 | 10 | $2.98945040675884062897823689788029507638372941895048619966973544322157717905567$ |
| 17 | 11 | $2.11919783876234708459313803084564173530277922030096851371805161446226842702148$ |
| 17 | 12 | $-3.77241547652366928463115260592995106876158625129869071640973703979782648093177$ |
| 17 | 13 | $-2.2658425074527766756679903258912990944730903610910320317035429354275604290783$ |
| 17 | 14 | $5.39991082652701756454837068079716978778101683062127226159008983608818040489596$ |
| 17 | 15 | $17.0195893332289033435199955123811524451603372739033774672862250528568089772498$ |
| 17 | 16 | $108.803597866605417317296434228041862941923433218318980009751129299812419014714$ |
| 17 | 17 | $-13.7460191838743018352717762734367389734066822187396104939193770491280575026955$ |
| 17 | 18 | $-13.0451086670596249755578699056055872125250120556855226494318590973875683087236$ |
| 17 | 19 | $1.84686404149300415438036367337164005778890704429535003968116124954606891875992$ |
| 18 | 0 | $-16.1981543267330183534513057170875499671933821939117901963431436404306033304703$ |
| 18 | 1 | $-0.0706083118036337116257126081742996323743517957617716191749380530995716922361876$ |
| 18 | 2 | $0.184928446084887502521313793724686140840544179588357983674451422085316693254657$ |
| 18 | 3 | $17.839534873450530261432421863245350441171869522519884856654227549240888488327$ |
| 18 | 4 | $-0.151555432371714540958869183716466706485859556714536940267186267930280324780993$ |
| 18 | 5 | $4127.94580558031042947274660253270021506721639896977305514817821941749794425476$ |
| 18 | 6 | $-6431.70682695773552488377173709696416768093078593969908500469401726023261064223$ |
| 18 | 7 | $3134.81995603361960152765596421771293398439892784743318961052848990920615257494$ |
| 18 | 8 | $-8.43422022126653562653770235139426702727617662556194155635832985138782185156201$ |
| 18 | 9 | $2.79507704788780005406317736899853515428756810187192432851800350426878583002319$ |
| 18 | 10 | $-3.56961304919340886335942846830068484191432217214969977057887804766756340362656$ |
| 18 | 11 | $-2.45825174766776204860582267407522470293039139933481009248630319063498028164651$ |
| 18 | 12 | $4.56860649556747618792950847675830144681982203342172680434887531969117747958846$ |
| 18 | 13 | $2.62835833540614017146499447820751431869994807735106360524709457613877999769591$ |
| 18 | 14 | $83.5565865550804725224108998458533008053192214852922828070598408459238603344202$ |
| 18 | 15 | $-26.7329849348231834665114017720140311039408390269407617207722233147376215906646$ |
| 18 | 16 | $-109.504355804569019391645045455709148285307985740783250170999332116842981082704$ |
| 18 | 17 | $21.7642549472560660519960451386526721327118539297864609580748225880548084424108$ |
| 18 | 18 | $10.976363688216731940687033932151313856300836976808897772707884674440610514031$ |
| 18 | 19 | $-2.14234682324723653844048640652007838150038066107790521326355140780310805613049$ |
| 19 | 0 | $0.317293026255142105182249555563215194209661843002912487354175661939431771502214$ |
| 19 | 1 | $0.00138309121391487230543260048087885213319888214204730994574778295839337329795691$ |
| 19 | 2 | $-0.00362241926551450623469216629291644964440817546431889998474378847898090643135187$ |
| 19 | 3 | $-0.349444751099793471307455456018049111020714171527130074314550280295002485342761$ |
| 19 | 4 | $0.00296870129847235059849934718740015667856949917766039429830305417133662827684021$ |
| 19 | 5 | $-1989.31448975356167562059880865440926022869837836174762647504350120009879401376$ |
| 19 | 6 | $3134.81995603361960152765596421771293398439892784743318961052848990920615257492$ |
| 19 | 7 | $-1576.02044109482282215021984563215114358528179081705384545427420586085780061716$ |
| 19 | 8 | $-13.2980789579351087293338355953023854497890935603814353658918111155397699491454$ |
| 19 | 9 | $-0.0547505868416724729483957332434873438670125465544614297530032904742301864220597$ |
| 19 | 10 | $-0.430557732596549185548108688119420720139141012195952536442043880437127251499499$ |
| 19 | 11 | $0.0481527784327395300466978165941273484792274512398241894618844331568140018337298$ |
| 19 | 12 | $0.30404568587040417175374227223030402583871888168808175472618547490182681242211$ |
| 19 | 13 | $-0.0514848638617793770683634472487566957036754911180004340505959595421419273941826$ |
| 19 | 14 | $78.3143220579021443474896656118192222495605674979531485807359134749265955382306$ |
| 19 | 15 | $13.3226877285641241312918355311534068685088718718222685075335385577173781411086$ |
| 19 | 16 | $-48.5853477310934926532859694642026531463144135699118473830787599406709870144558$ |
| 19 | 17 | $-11.0805623094919859064702375699893162868183654103456985472223656176273550719357$ |
| 19 | 18 | $13.4889160444841147442769181953671350676310454384940088731367508327012411811956$ |
| 19 | 19 | $0.0419647629677389187062228242236784634877388862143132351262270152724415054504211$ |


### 12.4 Matrix $R_{7S}$

The following table gives every entry; indices start at zero. The entries are exact rationals, with the coordinate and equation orders of Definitions 3.2 and 7.1.

| $i$ | $j$ | Entry |
| --- | --- | --- |
| 0 | 0 | $0.939390403470738214279010968692659873527298324642404629827506040827068891901822$ |
| 0 | 1 | $0.00409483507661955403045736983592628194791721676342861464858442893014794339238337$ |
| 0 | 2 | $-0.010724679125583838016868621780991112140726970930168335092693650153189794478052$ |
| 0 | 3 | $-1.0345800839076801510359570613620544790653228721446506877502302048440555021583$ |
| 0 | 4 | $0.00878925560851607460830407061481013780120028163060136498200499526280978182234148$ |
| 0 | 5 | $-10.3675655132383494272400391181406349783097079305940671055732332587824764319412$ |
| 0 | 6 | $11.9184389922531034711674485055085017509035967928124120082773115289729289263157$ |
| 0 | 7 | $-0.0359933876756498152331510013551489627223839527522234015670055243790135689516616$ |
| 0 | 8 | $-1.83928904034891537395473015298234086320141441322908182011258484662856280738518$ |
| 0 | 9 | $0.435372784710560340326389356843633695032057090485737544023105790010790065093722$ |
| 0 | 10 | $-0.117064277380034076221054135658291488883375679083339927250308468781555292040695$ |
| 0 | 11 | $0.142563038633551355328106337742193841812179993210216197854354856321733930285141$ |
| 0 | 12 | $0.112253596186102612760168896109230587115364663564780095216919482883589598959438$ |
| 0 | 13 | $-0.152428143809445470438629521434023079850037877099268862678544822701053549110524$ |
| 0 | 14 | $-0.0457810306720805834187155533713980647017054148902372052984449057704359070622841$ |
| 0 | 15 | $0.0143756333052603896682057420721374281490926156935878645018486895707585356864576$ |
| 0 | 16 | $-0.0381628110519595329186548533087054659418467955498306375937454838606523858774778$ |
| 0 | 17 | $0.0163895667676282824166210722135680559852934767251534155362304548151408115312517$ |
| 0 | 18 | $1.84381525249640060580956699768645799463640212942487121416344255128530577521445$ |
| 0 | 19 | $0.124242552952042034201209219517473063940090859999052441430598955166757930806634$ |
| 0 | 20 | $0.00832034906214336952469311131229316142736395723666302553553766776767681811897406$ |
| 0 | 21 | $9.86981456412037764527853588571955512524973434459563656140092089087623810866889\cdot10^{-81}$ |
| 1 | 0 | $-0.792300284542259963070935690049447651330802688308114401486056996923863085745937$ |
| 1 | 1 | $-0.00345366418942809640611504126859015334207034508916280960942274024562034595080994$ |
| 1 | 2 | $0.00904540464904716830627255702858753234479420160505331506426348075896542155865322$ |
| 1 | 3 | $0.872585127369084913758172050899734498622729781963940509237968783382838774172547$ |
| 1 | 4 | $-0.00741303050767098736140971008734618236634250558630454126290464197896525923756394$ |
| 1 | 5 | $8.74420802661003215668049905552597444933149971006890848877733064998561365713001$ |
| 1 | 6 | $-10.0522451261722375161421706973580445382725814746325356559638705316523999025787$ |
| 1 | 7 | $0.030357528873718728669650817988365199747351697735383481369721323135680752745819$ |
| 1 | 8 | $-0.0134285718846848817552416887425005616345881572490408174579149012891402994806166$ |
| 1 | 9 | $0.136715597079120513984630135544155625439014887888750927548587343305154240081105$ |
| 1 | 10 | $1.53712116700192329570326271352583042612658109539075217829158421444312669490066$ |
| 1 | 11 | $0.361595147190880271258042617208835091692382014087330160017008529532029472046892$ |
| 1 | 12 | $-1.54019762331133195813762045706662895350840170758915064315770749332593454363031$ |
| 1 | 13 | $0.128560885087042608707721043823048218925734599556204732276071545740169724043809$ |
| 1 | 14 | $0.0386126188793424812699817520131514730985738467199437402188869921942223365703473$ |
| 1 | 15 | $-0.0121246909869968518609596336736331978454237860214134339225778461241912858319829$ |
| 1 | 16 | $0.0321872630843219998840394719569932196489913713650490715306382115183034227138446$ |
| 1 | 17 | $-0.0138232819555525190649108234371760288565159413534057453268281544305852818808262$ |
| 1 | 18 | $0.0178365247222182290149345222439862306845265953767838326907628444593143574464375$ |
| 1 | 19 | $-0.104788605134208192880062133216924948624209959181049979342072615799566838497891$ |
| 1 | 20 | $-0.0070175455327955810993915514976092795613712387040690424978121003621429274914659$ |
| 1 | 21 | $-8.32439511691850423056450902149706946159193558534703872380404690115528696935507\cdot10^{-81}$ |
| 2 | 0 | $0.867553503613667048705268319909374347137167622859421450320654370768589218344193$ |
| 2 | 1 | $0.00378169555949917900023456391503265543187640016905012532392654576968029851665653$ |
| 2 | 2 | $-0.00990454332528471737094524306453967901907868240928005927553711658147942549888905$ |
| 2 | 3 | $-0.955463855333059221500333976728243667580473345242948755400834845381076434327525$ |
| 2 | 4 | $0.00811712517942676139495890282217120737841235648342200261166242992465049212596861$ |
| 2 | 5 | $-9.57473884310798178881874649859601339995946285598001938364993812409112136565188$ |
| 2 | 6 | $11.0070141946654535431122476022064732403506746145574797931367391384230668503307$ |
| 2 | 7 | $-0.033240907581730122825840959469227249964721962387663889825528799034812166136529$ |
| 2 | 8 | $0.19021529539659362282017093825423836156806620140781857143561341477242458964825$ |
| 2 | 9 | $-0.149700937332301400877133390407932214840259451045988863913407967585084023542873$ |
| 2 | 10 | $1.63661907232634727047886003239772328298632556636890703434980054385485132548921$ |
| 2 | 11 | $0.131660982691953469888038689572914320991276488216773265366011468987069187817871$ |
| 2 | 12 | $-1.63325394818814258679805510877849638624234227867345580286046046018130863980124$ |
| 2 | 13 | $0.386587890086654286552716102529151186502713283376902635654416746206853123382978$ |
| 2 | 14 | $-0.0422800716420619202323685788874257596987305241586257652733135438936301434592767$ |
| 2 | 15 | $0.0132763023707346826889792697033406921020310791830942704800250291950573046931453$ |
| 2 | 16 | $-0.0352444311902162011171981104175960559827856206559908298773453407965847054157513$ |
| 2 | 17 | $0.0151362266629850168588590412331181684827756204173730545138671436569567758216424$ |
| 2 | 18 | $-0.193982840867685784600441278688666958812854230848620130098437856308450738649562$ |
| 2 | 19 | $0.114741498011064320710082254726512992640797904371089334555979051378492494538774$ |
| 2 | 20 | $0.00768407677306660795639182447094435245829411718136892153534857582921809512731932$ |
| 2 | 21 | $9.11505181816194102499693868140910585217685857716053823410506485391115352590745\cdot10^{-81}$ |
| 3 | 0 | $-0.0289250071929450888816959366318440078942052829770763353379430699771277622638263$ |
| 3 | 1 | $-0.000126085101154467914143105194817775983858542362617848531922681625623348872548891$ |
| 3 | 2 | $0.000330226303891770140040768333661217222327922176717695367696474886638329287077821$ |
| 3 | 3 | $0.0318560166871446498670766755300393660983426971144041392018951670468060832643506$ |
| 3 | 4 | $-0.000270632189511056255308521091193842960629222100784967912256501954622828653228633$ |
| 3 | 5 | $0.319230328451071885744167299221100039360595375786217358826253451952366964860798$ |
| 3 | 6 | $-0.36698366547698805797826003515648092275096751062500728833761163024127183959614$ |
| 3 | 7 | $0.00110828149145454019418314502103554522054753682982774723791129223970421051414749$ |
| 3 | 8 | $-0.165708568415095123040042361467608221459117749786739373884288555119124725886349$ |
| 3 | 9 | $0.00499116270188644252510212099202203212134055840079803807532175665718112131248154$ |
| 3 | 10 | $-0.0962611156995458154054507720563071496862095788122408770010282169135807821825228$ |
| 3 | 11 | $-0.00438969453242028126478349787400541713074219138351082553048703380773152286047198$ |
| 3 | 12 | $0.186188975178257010695139818863992909827170766753819963581926045820939596677878$ |
| 3 | 13 | $0.00469345347770823537468377776613437236589532183732217211201087657751584738433037$ |
| 3 | 14 | $0.674362080796942245885867108233096215766180501135679255932760684647448321787347$ |
| 3 | 15 | $0.326523623597723070402100366301632262907970312457243830295282263874326034704581$ |
| 3 | 16 | $0.257717225410014349341369542468446661126688461143343182273867139666924049494255$ |
| 3 | 17 | $-0.000504655290166234888490723508684983433979640748729300030745473856398464446296932$ |
| 3 | 18 | $0.0707535065298396573562112726482665413353358408843206619828477459948110764991986$ |
| 3 | 19 | $-0.00382558383024786812193911648777974256006173403454480567193381342536643561571188$ |
| 3 | 20 | $-0.826034279596549262389077797400629939019120780250086672093114715620793851531634$ |
| 3 | 21 | $-9.79863356973691288604118330625714046125272134413117231621041448088708262714173\cdot10^{-79}$ |
| 4 | 0 | $-0.0489035494636960661645572224434400116096758581339445764138902945212123629878816$ |
| 4 | 1 | $-0.000213172254022690612174879602223609252165879985151031043533885219345099129485045$ |
| 4 | 2 | $0.000558314066401461981778079920562144817878162777603248461646875496793430208909743$ |
| 4 | 3 | $0.0538590112487880802893570540934827247897387903051217495557528912996535005523307$ |
| 4 | 4 | $-0.000457558215212832853393062585907807498530389747229382519126275167796928341779711$ |
| 4 | 5 | $0.53972315559273687791480319405607966700381991659870549332672480847588210732779$ |
| 4 | 6 | $-0.620459788213973704816060228901089012011019141757472019681258538818661387238997$ |
| 4 | 7 | $0.00187377304266549180741579174302638832987520934104198729003676080258936016098482$ |
| 4 | 8 | $0.0352136008313506473663917942380325902686294091167835571892456270401016315817657$ |
| 4 | 9 | $0.00843856564822538317391413973320732835922943362807932116786599069873869601900339$ |
| 4 | 10 | $0.0582369100419018169522926569549607630054786582335265167470155402322539278367493$ |
| 4 | 11 | $-0.00742166258645185642930218794257884626331551504622916684977528437849199036105183$ |
| 4 | 12 | $-0.157517454127280161917269434534373604676724555739034476211599379201779663606977$ |
| 4 | 13 | $0.00793522825324113802533891949776389225484075306988166992080053113926921755432162$ |
| 4 | 14 | $-1.71919342160567830482831284412193414120278252397325846908352743985491947039199$ |
| 4 | 15 | $-0.000748378407761387062943054638794885266468696487976941186275762054592729240478448$ |
| 4 | 16 | $-1.12737596062688611108891773632026497269549962066885011024585807909121891851974$ |
| 4 | 17 | $0.373519121967215003705329487070209236875851037654530089654068545938234919671494$ |
| 4 | 18 | $0.0549663571765441466296860986838676637547195513686098219416458631747252824117834$ |
| 4 | 19 | $-0.00646791984603803567418218323413121422269536006541867975680458000230214763001097$ |
| 4 | 20 | $1.01894414140673140358159648248032234929897742756234379882075762289829173539781$ |
| 4 | 21 | $1.20869805482543115515036240252833581180571798600346384112497476230483247511718\cdot10^{-78}$ |
| 5 | 0 | $-0.94223755044027177655196276255927298520182554334401041459116035987112484009865$ |
| 5 | 1 | $-0.00410724588817996854776758070138356062127226138044234965022351710081258112320088$ |
| 5 | 2 | $0.0107571839686808188651402295079220501784606392310705658327553470494915943225831$ |
| 5 | 3 | $1.03771573607077922286999894231532039341444491421257987038473058415886585890574$ |
| 5 | 4 | $-0.00881589448238341011662108671663589405644164354252401880323374662596423778725637$ |
| 5 | 5 | $10.3989880002292724890250729957175438281881934096908480980650144990564511049525$ |
| 5 | 6 | $-11.9545619368062847505955898978316526076538674846203022488630456828828180020337$ |
| 5 | 7 | $0.0361024780647631688058292482953122058412562285881964428750318589831209045631495$ |
| 5 | 8 | $-2.08856194241225432191997816312385078010107133434789570144465582270301444965944$ |
| 5 | 9 | $0.162588063909673785411101427427660351538448341082868682759257107198901849336748$ |
| 5 | 10 | $-0.0568610910292277314472598231943789487005971708265324692139842627143809872375592$ |
| 5 | 11 | $-0.142995125146159268641652715914464409849968621403066436108417600827199153402141$ |
| 5 | 12 | $0.0615271011585836040587467966997339254820491636950738356884840569615513560272416$ |
| 5 | 13 | $0.152890129929502962840353962970310582617220373642271074721734159484412368821351$ |
| 5 | 14 | $0.0459197858927625855447071289758214959726836121902796275486544043661308271842678$ |
| 5 | 15 | $-0.0144192036255968298638698729976612838998877804869127438409320812133658375465409$ |
| 5 | 16 | $0.0382784766276712110326402781294006269232066443122911455896264346750482548606429$ |
| 5 | 17 | $-0.0164392410086914384371373414521613475107071567849023094844095256716934806015011$ |
| 5 | 18 | $2.08404977793227201564075073289504225400353015710624509217255233986869481392125$ |
| 5 | 19 | $0.472850445471901237960342333046811188968815360963971918417233254434510833159385$ |
| 5 | 20 | $-0.00834556675281832097069639712043550824720025172764566215324628784626022333167385$ |
| 5 | 21 | $-9.89972844499702946177607444602543152130950268996481418460396995467610656790827\cdot10^{-81}$ |
| 6 | 0 | $0.0545667977179050655968012917341365855075269891117709853148854319343777927556921$ |
| 6 | 1 | $0.000237858547935487464409398481554900632346596960734781032937880791906703196156339$ |
| 6 | 2 | $-0.000622969315284687663214855481307536997571000257778339576255117858621910364896747$ |
| 6 | 3 | $-0.0600961239895422802754229824848624101982809904868921485217182031237912126836483$ |
| 6 | 4 | $0.000510545488977627938123012608939167772710169493749215761594506238272039035544739$ |
| 6 | 5 | $-0.602225494424723297745886020223797281626142181919004011377421925738730157690078$ |
| 6 | 6 | $0.692311787730249764533394509350812496052909889059034032388545297266180673111989$ |
| 6 | 7 | $-0.00209076428418134265912814342269186967728596500304522656210452226486680564525472$ |
| 6 | 8 | $-0.105793221707722544881751818272122053786873114616638176813289693818279433124464$ |
| 6 | 9 | $-0.00941578903383704492090607931550038829236423131520505076062577997822268627899702$ |
| 6 | 10 | $-0.0000337912469614664899532569805276693289041054085661850295141832718331000702489216$ |
| 6 | 11 | $0.00828112408049440146908526403966471537679120676778794121827916493690062644868244$ |
| 6 | 12 | $0.0957590860033796685191761728569595747501993910434629996558983126022235517514524$ |
| 6 | 13 | $-0.00885416293272240444682044919901927784449328959620947616551033293971606645617862$ |
| 6 | 14 | $1.89029376073138230713145388836859503081854308954299982648973920409158213350547$ |
| 6 | 15 | $0.000835043951627250749698047171929054163636792328324761768760340595032931938233902$ |
| 6 | 16 | $-0.350428820741384398099495539571309587950066849596175351933313873655148174949359$ |
| 6 | 17 | $0.00095202822084303920537379804319381197523808405591415480507633529587882985347489$ |
| 6 | 18 | $0.0200604209140092964739718285696530697539101681704931979418557721246960211072134$ |
| 6 | 19 | $0.00721693369427886316490224719358491866961100682757692817668749164557685989964256$ |
| 6 | 20 | $-1.70592864848985055296989525285815658683723126425065765888098263712375740251105$ |
| 6 | 21 | $0.311566645339197032761755822570745500669850013822273012062874097779931945706007$ |
| 7 | 0 | $0.0918896383125006802393261074576229912542588533541235744566622416635562651564187$ |
| 7 | 1 | $0.261160397371632883430664009137702088864001671728869951933738123291886091287994$ |
| 7 | 2 | $0.840489731961095037798758695902322323328318258738344501622443569630728362391886$ |
| 7 | 3 | $0.172113540080152852285245085970572277337320177685597699078632279348828230069724$ |
| 7 | 4 | $0.8833729810893613930335867399535019066961361154776554668045682238535032404297$ |
| 7 | 5 | $14.3270677389991949915766603533258416625631833175895363799204388289253987670246$ |
| 7 | 6 | $-23.3701574407377115991613605172514038281482968499751013049371733741088419260654$ |
| 7 | 7 | $-5.77009618612669380261690728347210748076732663061749155468340015774279278345933$ |
| 7 | 8 | $2.48411823779409345789828231482264540678270889603316370577562260703085298415189$ |
| 7 | 9 | $-0.375042881729253256324232830137721988420176552097780604133568214023707874479642$ |
| 7 | 10 | $0.273035643206541168887774094086302681352323171695796680760280728075654233557225$ |
| 7 | 11 | $0.0168596580655071005887112570827704657418785595999709602934569766523280022583204$ |
| 7 | 12 | $-0.308317153215104378420020431121474694426130159232354097696066365158643277574954$ |
| 7 | 13 | $0.0244026427246737401782467762530418590754028702618289272997454539103589867738962$ |
| 7 | 14 | $-0.314373535439780967443194158393781487189856890270436590151996380485721403757346$ |
| 7 | 15 | $-0.111279564511903075028774001845508175598239721373481593239563955644631677039826$ |
| 7 | 16 | $-0.143295678089022308882684745554512769652614691854066994668217180222683782853605$ |
| 7 | 17 | $0.0185582081583226692962972321461057973224731426588047314995353191642342687911659$ |
| 7 | 18 | $-2.44746340711362870922707776365597112434100024077118022054345402011427006629255$ |
| 7 | 19 | $-0.361328092861501291451561919346029043493623106255771671749787240842160701330163$ |
| 7 | 20 | $0.331577060164990277058308584361681144114248855835402894513460243080225225611411$ |
| 7 | 21 | $3.93325336846095998389994879922699571432754882270478740705091424080529803038648\cdot10^{-79}$ |
| 8 | 0 | $0.28809093980607102008103544788724888499436405567657206917350465892246702266745$ |
| 8 | 1 | $-0.254826651002132620802943273880213613157293986675410846408332307057584898019734$ |
| 8 | 2 | $0.809836817308993633377602843510088067325308472184490309494675381498045805891474$ |
| 8 | 3 | $-0.049194432539354999918831297756473610725675166131890271959807855802292356819389$ |
| 8 | 4 | $-0.848549519053714222072350751224602538442140219473812461593121312895168268973246$ |
| 8 | 5 | $9.27272706050645146570073453250898958105690175078427279807895549738880295085379$ |
| 8 | 6 | $-14.0022466568378529101014706842498864945995525435406024874905845186589158189899$ |
| 8 | 7 | $5.49314319359998358777166041563218643062493962555992842459510951698057779812106$ |
| 8 | 8 | $0.293737076033891687620716763501469563043516551597215891366532089656946861117128$ |
| 8 | 9 | $-0.049713932012258046640185708482321480081699790968682566267792684130817367121434$ |
| 8 | 10 | $2.24455117969199442443490076424484911354243708883213201628705443996557577878367$ |
| 8 | 11 | $0.325699421282165967808755693616368262087479258332564054855218992891829111872239$ |
| 8 | 12 | $-2.26922203600094997177153803583129841423748427379207547741040992882383400406221$ |
| 8 | 13 | $0.377933897558979208829523032251093708193382048558663223321452488324430314462576$ |
| 8 | 14 | $-0.266890262824641535510466346149525621916403202387798846589931312478658348089884$ |
| 8 | 15 | $-0.0643512274916032891963607463513055220394298210984779818153811808646557884980393$ |
| 8 | 16 | $-0.138687048457282616240901307253511387643982076076470980571991370994483907251376$ |
| 8 | 17 | $0.0292361537996758832203418920810892877933578220521008861923423532501737411714927$ |
| 8 | 18 | $-0.268150580169801717484698444404290899853314811355679454548816144142080439467144$ |
| 8 | 19 | $0.00626784081624545342567055338835986078709723983760380143741905132253385230951229$ |
| 8 | 20 | $0.242130933765372962560716248511367149416831887422799187092478001098160883402891$ |
| 8 | 21 | $2.87222014203082203905216246757336218398111657355107918655430516673846125214961\cdot10^{-79}$ |
| 9 | 0 | $0.221725563655587685581112058262665185805102938273400246136892600569257374696365$ |
| 9 | 1 | $-0.269857553223572505794691156722725155020456150326766140236160644003606844172028$ |
| 9 | 2 | $-0.80770192788433340404936019217917613035208229096955880586152769971704027622116$ |
| 9 | 3 | $0.0395282189725626789259722626215877928108496378950198866228640342177608885642483$ |
| 9 | 4 | $0.845640904692043135670237598126303743885226308581836960925692724912742037065507$ |
| 9 | 5 | $-21.5399717414885371873583543981934529485823946385804486939763112189017790039043$ |
| 9 | 6 | $31.910075901450799615780848192293811709614868795623178982422167314285371109018$ |
| 9 | 7 | $-12.5203742955886190481298082358052120362013839377285916195590628219527930644046$ |
| 9 | 8 | $-0.296795919560504546577339666437111514071662978186628362905653818701306244234727$ |
| 9 | 9 | $0.00491270611942419148824330806345266759864815669271208649802897677911992340586165$ |
| 9 | 10 | $-2.26075313445835402942958265453472594990347232420393577368874747794951534044561$ |
| 9 | 11 | $-0.362450272173210396608098088802875328325593757807343442446593686232652837336896$ |
| 9 | 12 | $2.31534845110034345114423362731230724718363090203513781126047258686403183245728$ |
| 9 | 13 | $-0.338926288202373318902370847056415542416175933659683098454946513837819789824303$ |
| 9 | 14 | $0.590342578000934662684222302461483320832819519775204863018176302969993549934588$ |
| 9 | 15 | $0.129340368934189899397219820383373047131171594716288731730981837735577123827116$ |
| 9 | 16 | $0.314118300799960821053015257448198095197167409014633621115001758290374356289154$ |
| 9 | 17 | $-0.0704867248906943277121793250739370912469139849790758273460051203826290855959277$ |
| 9 | 18 | $0.241187285357481194479062724207586562657845123531557921220116767281091698498765$ |
| 9 | 19 | $0.0278471095425625482786156915435291824736259084297487064552939183076002669666267$ |
| 9 | 20 | $-0.518586987015499429877694423497291362488814892628957562954788516192941806763217$ |
| 9 | 21 | $-6.15161378324476605076553001806279007645089167294879852492613797966628992189902\cdot10^{-79}$ |
| 10 | 0 | $-0.000136644844364511484808762434646234708970077284766093748754208520424785231584568$ |
| 10 | 1 | $-0.000000595639576129064532551022700102049182037436583690910863874595263502850096735267$ |
| 10 | 2 | $0.00000156002456972127006785954341729806419715317564036839392704349008380780878382337$ |
| 10 | 3 | $0.000150491248394567860669414735719842335178018838652006122250863489496168409841898$ |
| 10 | 4 | $-0.0000012784955650688630457552761782646320162426612475732423049807114868175618088927$ |
| 10 | 5 | $-5.50710875637216387874393987652517395337361664382731535582733746997991008065623$ |
| 10 | 6 | $14.1589633501905779160240103756366115315368474721447106343718176649416149697069$ |
| 10 | 7 | $-0.00360021001668607932812378067713881899670925653183367481417627449825511943112732$ |
| 10 | 8 | $-0.0386783096569566192960275494595981022531420506474421127738490997214708727960732$ |
| 10 | 9 | $0.0000235787893170714175259891823509632806257122281312465634928574460413542572118493$ |
| 10 | 10 | $-0.0270082139703610434330786925097627153954646701027604580129125760152716207844962$ |
| 10 | 11 | $-0.0000207373890069979579469889634930379868620918997468837231933723061269885151738985$ |
| 10 | 12 | $0.0576316571153482859084924659023714390846413693590694381143078640108920381710605$ |
| 10 | 13 | $0.0000221723789285674286349573011504042900334250114346405549252079670749488233288494$ |
| 10 | 14 | $0.346761562512775196419965519898038719175399607873266649879422568730639470317242$ |
| 10 | 15 | $0.0679668167292786915588680143865240780111581765696291680895108059169290459436361$ |
| 10 | 16 | $0.189038187800598544034356624619561789695840786819749206669529492823070904111905$ |
| 10 | 17 | $-0.0449866651321580770096339095326724563818999736783379287481024159196348814049596$ |
| 10 | 18 | $0.00810334372623824728595367396521856155324630882985022793654039882358983503366721$ |
| 10 | 19 | $-0.000018072469389570673237746973878525428498519526100307255282521643213448608401376$ |
| 10 | 20 | $-0.294149396674203988305537437609818243274944286877565045653142339868313170282807$ |
| 10 | 21 | $-3.48927668495484943950317714194158799744434071524025068271335730715705478335782\cdot10^{-79}$ |
| 11 | 0 | $0.00288075407288269772806400917944305457614527352615409704244258073633062713784842$ |
| 11 | 1 | $0.0000125573060797423433405675265938701922997277049565900448359880810779944892836215$ |
| 11 | 2 | $-0.0000328885231925280867117039696731112361714230271894686050302211439804378525957132$ |
| 11 | 3 | $-0.00317266471898039843229815991705091265723305985204753053040032410260343938359784$ |
| 11 | 4 | $0.0000269533133384074194895880681746025855431903289640442881149206299497726347336373$ |
| 11 | 5 | $6.26150026313119272546326613119147153371966608761025151277877978251108153246979$ |
| 11 | 6 | $-2.63004604032123706395543194238448384870590856997372217673311753456160224216681$ |
| 11 | 7 | $-10.7797264352437975307665745112563558863177020282347997360734716878796481096256$ |
| 11 | 8 | $-0.0132173837554519620822642669380037683518183353980227503637262099275676671111818$ |
| 11 | 9 | $-0.000497089324333392054061953139932654258717822618046218054466513719523662097040859$ |
| 11 | 10 | $-0.0112385255258143883093496251182681971958868280988327550831863860355786260156292$ |
| 11 | 11 | $0.000437186767789808828411579310835867301178369874041247254760337700129971989249281$ |
| 11 | 12 | $0.0259666479019830229638688920630516030277739359074884523032272731942547549273541$ |
| 11 | 13 | $-0.000467439303700197652704776327871597360328534699090710243872288700556565544148784$ |
| 11 | 14 | $0.202299775551560752618746849070894392692601436129543330248876330680997268481589$ |
| 11 | 15 | $0.0195759598881350650148166128275638262369146519083657430697504637636651702114778$ |
| 11 | 16 | $0.121638320700978550222850179719155735820929961013481897898630461267043221589197$ |
| 11 | 17 | $-0.0352303373105438371046293248971353405417437771403893951686367653062343548032329$ |
| 11 | 18 | $-0.000953413828161103176744928479524323724987717110425448577710938717983014085196236$ |
| 11 | 19 | $0.000381004786848547160394075575233810785570633412018359927096074848496537028041557$ |
| 11 | 20 | $-0.145369146005141491894162184130321283854060772878393099556523724912068851079319$ |
| 11 | 21 | $-1.72440663690819126246752060848669935387757336481450364246236436194534732765435\cdot10^{-79}$ |
| 12 | 0 | $0.397397034436177940963801324050537043429422984577068380407102014071978793776133$ |
| 12 | 1 | $0.26351989756832918098160583973776804029195554808582808199192677877127340188507$ |
| 12 | 2 | $-0.842614382674202768428129946980904932998305703845006396131576735378726536896635$ |
| 12 | 3 | $-0.161459626374918022776397069260988124932609829657489026095723502679491065463386$ |
| 12 | 4 | $-0.880472757715605469877607367532445457583411128791279495434863769154733193083917$ |
| 12 | 5 | $-16.4213047048017983405291523883061267234279722164897775148468194465468313666199$ |
| 12 | 6 | $15.3773837694381660963882433318937539081295832734835426810208124277010656967723$ |
| 12 | 7 | $12.7977152845551691857326872556569402159574387103587416777733029222919170164011$ |
| 12 | 8 | $-2.4824778869218396384356612631616318974059923144321303876291941542562531725571$ |
| 12 | 9 | $0.419998859301810826311154900941333491480745463190101625281438569487953531691206$ |
| 12 | 10 | $-0.257212137237502436682004573699212554730492214322342134292297456360488198338326$ |
| 12 | 11 | $0.0197550897483707003062843588048206332642507941239312125113560315828474392144176$ |
| 12 | 12 | $0.262393512269803628723930705361078936417863860964137799933226078486647994508889$ |
| 12 | 13 | $-0.0632647309166207535089399857372527893530785984046116821016542217167676144838045$ |
| 12 | 14 | $-0.0218909893535916476981349355060972803503227240889449414320274220159092146171417$ |
| 12 | 15 | $0.0498949953793902173087361550289730296238969338926660536985993360972557014211535$ |
| 12 | 16 | $-0.0425790352011973563234182541851419226249502929050171318775922681006799897932677$ |
| 12 | 17 | $0.0270917834755813695798157584263330369701856694880129076850711797838731392835686$ |
| 12 | 18 | $2.47585791134489967926318330843401119643801099381593874261659797032778278303038$ |
| 12 | 19 | $0.32709452975471955925424796353318601410352270005935246031828361069340834072838$ |
| 12 | 20 | $-0.0522454589298367077524557852183131628107022934839397526025591643360726935980887$ |
| 12 | 21 | $-6.19749228792596132553192554572722366331748974469698342045240547560357698757038\cdot10^{-80}$ |
| 13 | 0 | $-0.00184728543885551310853018440287092535032402812255227346784988744316529820263083$ |
| 13 | 1 | $-0.00000805238076055109344343477642512912132477308089394641514406448778224262048894256$ |
| 13 | 2 | $0.0000210897870703081177724441739264858687355337432794910870886616208892748782469154$ |
| 13 | 3 | $0.00203447333214332205563976360663273583217022122215723676218450552830157462255773$ |
| 13 | 4 | $-0.0000172838298581753103100521147539925093380234621169417480858066348067705109687938$ |
| 13 | 5 | $13.6070901400256602238907856459984508480442323429134808738722940266032372008323$ |
| 13 | 6 | $-21.4439728831827420549748387559384029778275415777620063286539219795986917882752$ |
| 13 | 7 | $10.7829386488206436873370661399216875757007435171940464827616985028009942623985$ |
| 13 | 8 | $0.0533141860667676208722936676722303122563902310338440165302685859187981114300597$ |
| 13 | 9 | $0.000318758855292605801556293572839000400574833573564430112867008160934094343836506$ |
| 13 | 10 | $0.0386251882934963045313406875308176223305557761999424240298087283196237732431667$ |
| 13 | 11 | $-0.000280346301616182966117811048426862082331132223417148745005280288354699482156013$ |
| 13 | 12 | $-0.0838010791714240385489672236860361170502956352414039265047575085733493384274237$ |
| 13 | 13 | $0.000299745760112753627610843316253957570764722931458699624349874053279719792456221$ |
| 13 | 14 | $-0.536249128447256461071139231381012043244237747030834464972520087401341322269047$ |
| 13 | 15 | $-0.0911473489274875090545058544296202833654718146149901215338973070041395758655177$ |
| 13 | 16 | $-0.300233047554035633863217754793749540792391096012309618565360893062640802092008$ |
| 13 | 17 | $0.075817581899816319729987676850216766084541101598884625885795449410217172557893$ |
| 13 | 18 | $-0.00858113931702759113967857006702997272979965694006176810327403345813079671791462$ |
| 13 | 19 | $-0.000244319569485245994128617720401299227694855956851349133022892686664847093996033$ |
| 13 | 20 | $0.43664299469431837821082499758269575889744150261065337916107550113101041270913$ |
| 13 | 21 | $5.17957282340862086233730905626344189579588933121738459854188078878529044913213\cdot10^{-79}$ |
| 14 | 0 | $-1.23438931774445251588460220467667558819868687204909787796568393415558160682734$ |
| 14 | 1 | $-0.00538074548965936340328007755249264261108528991800562576521107983300558381922496$ |
| 14 | 2 | $0.0140925746100300451828841852921000234490224689062771395883804581293759648295075$ |
| 14 | 3 | $1.35947163097305401268153810816228112888865166437019930469629639043918589239569$ |
| 14 | 4 | $-0.0115493656247636079155489644173661345437956210312883485750506273613893751389459$ |
| 14 | 5 | $13.6233157942366007842736242373737969322444732144040087087069832282083448815527$ |
| 14 | 6 | $-15.6612136145634615853563740101509272082852092172762689834388086557943718688856$ |
| 14 | 7 | $0.0472964734279840237243608585242139826735000217300082141087615265095069308625415$ |
| 14 | 8 | $-0.0392615821265930962536037373259528491141697572867891308732340717737007099742207$ |
| 14 | 9 | $0.213000393785065777859053313374089547747263807488885477743693733140787627669078$ |
| 14 | 10 | $0.153813490729160356541095266145991489802052118316868254876309962418409910680313$ |
| 14 | 11 | $-0.187332435315778872709750755758933462337856077404575243015646056160809157685513$ |
| 14 | 12 | $0.0912693965835509738941850769211429341611504850060752711709413174031770574984654$ |
| 14 | 13 | $0.200295502005152953017789619393551345833432548982484820006516344219573900289918$ |
| 14 | 14 | $0.0601577523127291868874640489262007840319757856304494450270453614116703319226678$ |
| 14 | 15 | $-0.0188900462707117252102725507221873651207051217986495245764115514112299574935201$ |
| 14 | 16 | $0.0501471657828215994454846445576914590752003687640107574044909250758695891455251$ |
| 14 | 17 | $-0.0215364198587430231925499208175922616191270113648860526548091857238258096334191$ |
| 14 | 18 | $0.283180587407351175626721080021366980819033312636581002902848338074959374796056$ |
| 14 | 19 | $-0.16325872566578483609717737579325686238017571612510698418187471484222018853011$ |
| 14 | 20 | $-0.0109332072844991272308834438583035220087089076343110106772651462575018547601458$ |
| 14 | 21 | $-1.29692549775428033857119041079154929127881985609166004879138040321175904503697\cdot10^{-80}$ |
| 15 | 0 | $-0.00538074548965936340328007755249264261108528991800562576521107983300558381922478$ |
| 15 | 1 | $-0.0000234548546461768810706603514032088411295048509523511347389324759708452133523911$ |
| 15 | 2 | $0.0000614300174025853925321426696603251462477965618328871755091461753457946993316641$ |
| 15 | 3 | $0.00592598359490379930453791574981541388857521074039663079658429877729543124586094$ |
| 15 | 4 | $-0.0000503440819687480335877613107878620218762369123277127861916672357974475653157551$ |
| 15 | 5 | $0.0593845020856048252340297308904236351483087306063947146450779891434131784052458$ |
| 15 | 6 | $-0.0682677687726068108230642800460685346338493530532570052574470736982170390580507$ |
| 15 | 7 | $0.000206166954311819808038605115461505505095951063833506619551332124732747782798131$ |
| 15 | 8 | $0.248862647562573833953950867644833150095514727223454159141820296048863580193755$ |
| 15 | 9 | $0.000928476042103866213909151804968726486131897282051259055338810638476010747525852$ |
| 15 | 10 | $-0.242224694148368535721391852626721822746123336597166449738120224792883874784594$ |
| 15 | 11 | $-0.000816588528353547171515054937043503165797470961186501428538051184432641423191086$ |
| 15 | 12 | $-0.258062873467271765130858285167818355582213891728272568908286139146300108725507$ |
| 15 | 13 | $0.000873094981883504889972985145087413294322597848364183854987100891413812952264868$ |
| 15 | 14 | $0.000262229711300673174575507249039166115213995949671837348660464243011088739214612$ |
| 15 | 15 | $-0.0000823423613680616577771497740852644995478338355895693547089037289314512949599906$ |
| 15 | 16 | $0.000218593220328708829853266987658657802183581650497932006025063724512848855519649$ |
| 15 | 17 | $-0.0000938779948534293390123592609350955829034897566356694710252864480337867213632186$ |
| 15 | 18 | $0.251429550990208332998033497501295280405384005349702825327977306716123445969317$ |
| 15 | 19 | $-0.000711650400036568994956025345962529189838292253522386465434753614999933727289266$ |
| 15 | 20 | $-0.0000476582265723709990285723119290336730493770870055667514842948989489947700054372$ |
| 15 | 21 | $-5.65334284909152649855919358553415020892081232085815642425540748189884826814271\cdot10^{-83}$ |
| 16 | 0 | $0.0140925746100300451828841852921000234490224689062771395883804581293759648295053$ |
| 16 | 1 | $0.0000614300174025853925321426696603251462477965618328871755091461753457946993316567$ |
| 16 | 2 | $-0.000160889807036047654351791514405052516557553012071155551597279176528467779648826$ |
| 16 | 3 | $-0.0155205939603515305902844670824548972159077464690811366794398995860904989175339$ |
| 16 | 4 | $0.000131854913539678413183069058823741778463423801539711626834886360564254184511507$ |
| 16 | 5 | $-0.15553244953309450603668849184424914019399648804217750798523683731892483594722$ |
| 16 | 6 | $0.178798388947615137624020521601339523062003937649594398073263763783849441537605$ |
| 16 | 7 | $-0.000539966662862158265710217373599865527213878691510206117743555108485842756230048$ |
| 16 | 8 | $0.804144048656604205803476790283336213390522069456803786797312656217207314780932$ |
| 16 | 9 | $-0.0024317481512775425168442007042608290893770816201864509862584788363115572589536$ |
| 16 | 10 | $0.769496910734577093744294812488415217291073275129526183585360132266975974366557$ |
| 16 | 11 | $0.00213870638996633163380994089561153144077666361444749075066045791821492372906532$ |
| 16 | 12 | $-0.769455854173196651119167003596343309634894475430269573550559680250798552735011$ |
| 16 | 13 | $-0.00228670101521844277756205308386255781630938601776081615317047948072673164614823$ |
| 16 | 14 | $-0.0006867992137099434789198068297239720547538451165376137880644318515039543291471$ |
| 16 | 15 | $0.000215660798931213997115670537893771188351259530531469020816897079512030968041224$ |
| 16 | 16 | $-0.000572511982335756994928821296507957861951967537899058752849984679761119253807745$ |
| 16 | 17 | $0.00024587348523628517935223558909056826008349562536289770546538963196248748077775$ |
| 16 | 18 | $-0.804198690950859076682703821711324512514258759140948194087836724039082194270032$ |
| 16 | 19 | $0.00186386558852237736802281669872308912505697252655141049007638408569131606637476$ |
| 16 | 20 | $0.000124820457507900672772800229770356374782579584405942893227634809660984948152352$ |
| 16 | 21 | $1.48065274691046219221681295738674825149379644289453148242245885788750841872504\cdot10^{-82}$ |
| 17 | 0 | $1.35947163097305401268153810816228112888865166437019930469629639043918589239569$ |
| 17 | 1 | $0.00592598359490379930453791574981541388857521074039663079658429877729543124586115$ |
| 17 | 2 | $-0.0155205939603515305902844670824548972159077464690811366794398995860904989175363$ |
| 17 | 3 | $-1.49722870155552381260247957288592677319091659542924744488773595913657053440988$ |
| 17 | 4 | $0.0127196782221765700269688653703073215304243775934374315297622784022588342431349$ |
| 17 | 5 | $-15.0037845239081838528674953567980649867857025792178100424390329064691817454253$ |
| 17 | 6 | $17.2481852439488770394949173010031277805856668105670753325771024604708916561844$ |
| 17 | 7 | $-0.052089088058461623048901337000157875381678227038321023411570444309770614679777$ |
| 17 | 8 | $0.30426386453835495674782307822500178128681296395622202940741284867572144183627$ |
| 17 | 9 | $-0.234584007309785779789367041738392815675282090989832537770391654557961025381585$ |
| 17 | 10 | $0.0848839529542565605136729619870550906235919404641161531817892914469036317043619$ |
| 17 | 11 | $0.206315080430418425275752475729884330269597448919455794314808087275074298972144$ |
| 17 | 12 | $0.17025156045809452291486552179997989393227324228325082892328973813135380020548$ |
| 17 | 13 | $-0.220591711928508078993781312578829905021607081953809977895718292056790608009861$ |
| 17 | 14 | $-0.0662536174581428976552849641786201330126680685569345921927742231314682055741559$ |
| 17 | 15 | $0.0208041998125241282882697932172786206762716811447037954982324203812838019312635$ |
| 17 | 16 | $-0.0552286448654784518585867972325355054209164003323348136557465124718685148697064$ |
| 17 | 17 | $0.02371873396003181391993906072180047406698201849661274402906058368171145827411$ |
| 17 | 18 | $-0.0479004296362148357852107551760000812588356290578977197630034794338278432233253$ |
| 17 | 19 | $0.179801949726038410488101184357429509789506878923756267764974188203555810821682$ |
| 17 | 20 | $0.0120410837368422302766397277767706719031888925592344185072844417241382643595232$ |
| 17 | 21 | $1.42834468537385810551061540251891929403463175053955159450565917431694144508432\cdot10^{-80}$ |
| 18 | 0 | $-0.0115493656247636079155489644173661345437956210312883485750506273613893751389459$ |
| 18 | 1 | $-0.0000503440819687480335877613107878620218762369123277127861916672357974475653157567$ |
| 18 | 2 | $0.000131854913539678413183069058823741778463423801539711626834886360564254184511527$ |
| 18 | 3 | $0.0127196782221765700269688653703073215304243775934374315297622784022588342431349$ |
| 18 | 4 | $-0.000108059786662934886165673813672470626094888177054578374012304672587450571514324$ |
| 18 | 5 | $0.127464368710478848242369375535366191479702002308197634457941641339392022340187$ |
| 18 | 6 | $-0.146531632736929473147617681698825358054869572486904753609047539684376346831077$ |
| 18 | 7 | $0.000442521866099613666827195298573527511425115976465095133199995619112300882622475$ |
| 18 | 8 | $0.842460325765948522868894390727888449693962987847681904612101725053771696625894$ |
| 18 | 9 | $0.00199290401389525985263581546390990421363241456584806917648273509607653913874791$ |
| 18 | 10 | $-0.805969969132039201873762961672606139849080534533115532143550765886308554507973$ |
| 18 | 11 | $-0.00175274587825558162128190696426300834710033252841976401489886616243178537919905$ |
| 18 | 12 | $0.805910809531264205761679198795761643327450632873378760220218855185380995538821$ |
| 18 | 13 | $0.00187403273213677321134529806717548906092943949051001170248620366304146805199116$ |
| 18 | 14 | $0.000562856358716087359154733748957361044367344132862423533462545127480795633920692$ |
| 18 | 15 | $-0.000176741687499209126818926655446043970658891013405088679782614537891266989351155$ |
| 18 | 16 | $0.000469193911795778296597475561116425277702374131299325680754419936298179954253603$ |
| 18 | 17 | $-0.0002015020574315568829374004902508722368811222154321780451307795423815136736221$ |
| 18 | 18 | $-0.842387684980937081941260653844924395350910533101563481403754797047716571345609$ |
| 18 | 19 | $-0.00152750407593650075460522836319370975353930624270329535636162219501869900624872$ |
| 18 | 20 | $-0.000102294799999355203834542343418098131770432052456010889896148787591757735197542$ |
| 18 | 21 | $-1.21344753606687090325216260530484499166946452627401373760856147427542737374225\cdot10^{-82}$ |
| 19 | 0 | $13.6233157942366007842736242373737969322444732144040087087069832282083448815527$ |
| 19 | 1 | $0.0593845020856048252340297308904236351483087306063947146450779891434131784052477$ |
| 19 | 2 | $-0.155532449533094506036688491844249140193996488042177507985236837318924835947244$ |
| 19 | 3 | $-15.0037845239081838528674953567980649867857025792178100424390329064691817454252$ |
| 19 | 4 | $0.127464368710478848242369375535366191479702002308197634457941641339392022340187$ |
| 19 | 5 | $-150.3534829421773067647787862570728463729736827890322095775687882741439045182$ |
| 19 | 6 | $172.844706062472358361667628788837572186877675091269884340907028799459560161575$ |
| 19 | 7 | $-0.521986689451033340780360398501512457201216817199696833765308908497975190809058$ |
| 19 | 8 | $15.0846402436140822423803991559286564738148967089222993862188271600107043605614$ |
| 19 | 9 | $-2.35077506514151215838243155201093469365120232170748656611661764008929880760471$ |
| 19 | 10 | $10.1134346386404544147518436021289970159345255791993967083988626182667856388376$ |
| 19 | 11 | $2.06749109711479117272508086477906965316455405125565576802834366854469493778271$ |
| 19 | 12 | $-19.2285878088255372099668228941460020949271781497168279473900990089545285867548$ |
| 19 | 13 | $-2.2105577525309170240607637195636758929043652942488762052546979752614995024158$ |
| 19 | 14 | $-93.5052467714169695053768675732268058224833547287555389023601381005943762808705$ |
| 19 | 15 | $0.20847966035859984502440605011755156819764135727788658086755463584115129546924$ |
| 19 | 16 | $53.4289682230561508503274551992446895127082394523675691229343103875172485422775$ |
| 19 | 17 | $0.237686315488404729217787050649481406948261672439569388908582582339084928012654$ |
| 19 | 18 | $-14.6278038948878680179876760148499831762361130879315094974311333215512278379733$ |
| 19 | 19 | $1.80180202788345324990899939547053427288705792368047530417953480642498970530727$ |
| 19 | 20 | $80.5339196155494046699162926960927041698209355637421188658439257266849412604028$ |
| 19 | 21 | $9.55314310482173593714552391044850077542392891442029107940412906311339658211511\cdot10^{-77}$ |
| 20 | 0 | $-15.6612136145634615853563740101509272082852092172762689834388086557943718688856$ |
| 20 | 1 | $-0.068267768772606810823064280046068534633849353053257005257447073698217039058053$ |
| 20 | 2 | $0.178798388947615137624020521601339523062003937649594398073263763783849441537632$ |
| 20 | 3 | $17.2481852439488770394949173010031277805856668105670753325771024604708916561844$ |
| 20 | 4 | $-0.146531632736929473147617681698825358054869572486904753609047539684376346831077$ |
| 20 | 5 | $172.844706062472358361667628788837572186877675091269884340907028799459560161575$ |
| 20 | 6 | $-198.700368153838240419650728081065547783383118476673847157008436038994297842046$ |
| 20 | 7 | $0.600070142315123956692693439182485682464542448032775874283122177121102573677171$ |
| 20 | 8 | $-23.930773397783787311419333668312860186625666162308765912466294589427888568392$ |
| 20 | 9 | $2.70242509320276589045600997700290513078918742678913623200622864676360931926645$ |
| 20 | 10 | $-14.7965927426198150761722409276047670823921921292225425802825973763884123333941$ |
| 20 | 11 | $-2.37676496729387722149162895360902137397016642711800867166565482620133263499147$ |
| 20 | 12 | $28.9266240409010577931621704635257769546049894362513768630658469523686855728973$ |
| 20 | 13 | $2.54123281678327857980907764350496705421936968894487066463712170527689721396007$ |
| 20 | 14 | $239.425291451690114674911860993710566778744898458973944372120088672193034593116$ |
| 20 | 15 | $-0.239665918670765942496772118789515792942557848912542978886081112720031316089374$ |
| 20 | 16 | $-22.2371999120955676909536693681533025303123021170650995696487246793716209441675$ |
| 20 | 17 | $-0.273241567350088922366429332061119196283084624809541405784513720743621044325781$ |
| 20 | 18 | $13.4705981791060215993691983948395367050826601274438541197051677304253255021652$ |
| 20 | 19 | $-2.07133174302355257838095448116570421867394176188488620562434226110417078708705$ |
| 20 | 20 | $-126.916715524088050284524040886787543863979693373708819254101848386934815423654$ |
| 20 | 21 | $-1.5055191049728371492549285077514983830932480034889319866874477661994258820838\cdot10^{-76}$ |
| 21 | 0 | $0.0472964734279840237243608585242139826735000217300082141087615265095069308625689$ |
| 21 | 1 | $0.000206166954311819808038605115461505505095951063833506619551332124732747782798257$ |
| 21 | 2 | $-0.000539966662862158265710217373599865527213878691510206117743555108485842756230444$ |
| 21 | 3 | $-0.0520890880584616230489013370001578753816782270383210234115704443097706146798071$ |
| 21 | 4 | $0.000442521866099613666827195298573527511425115976465095133199995619112300882622732$ |
| 21 | 5 | $-0.521986689451033340780360398501512457201216817199696833765308908497975190809362$ |
| 21 | 6 | $0.60007014231512395669269343918248568246454244803277587428312217712110257367752$ |
| 21 | 7 | $-0.00181219682199737017391692744598137867981148457670132087460149596938361224598656$ |
| 21 | 8 | $-5.50575506903401295326723661829965381713059625686425651994209493117806739198748$ |
| 21 | 9 | $-0.00816125619364042928330535776176375474573064932247479453351918913069763921772207$ |
| 21 | 10 | $5.21484360722291624774820898571903899401942133346769445815192044165697110012438$ |
| 21 | 11 | $0.0071777707581770669749322840986774437488066468264467283787926173232474748028804$ |
| 21 | 12 | $-11.9441981553727778940891527399673996938543855698385857206516017229192672782363$ |
| 21 | 13 | $-0.00767445955028316780634402357981496202451607459808871175380251357384315765993852$ |
| 21 | 14 | $-0.0630705701851841972837427651560735206064728887908930813825731005332805354121511$ |
| 21 | 15 | $0.00072378508032509340767559615726099491921009409579193298597940193252181923003798$ |
| 21 | 16 | $-92.4669732662375317004480018104516178905768093604019649164060256254778692098754$ |
| 21 | 17 | $0.000825182699607434711248135971860063733988569107426902677815028883616138399975098$ |
| 21 | 18 | $12.2347092033570247588569692307937197627688468585436377259295165407306637073025$ |
| 21 | 19 | $0.0062553700597860082290689859288720475622527317116367462521940049442113837231546$ |
| 21 | 20 | $63.8191049979981258208145617310727313746324580675782960835009009215429324454571$ |
| 21 | 21 | $7.57038830070559673029109929887581321823448964786712476160717932073326737755692\cdot10^{-77}$ |


### 12.5 Matrix $R_{7,8}$

The following table gives every entry; indices start at zero. The entries are exact rationals, with the coordinate and equation orders of Definitions 3.2 and 7.1.

| $i$ | $j$ | Entry |
| --- | --- | --- |
| 0 | 0 | $0.937990608960515335242243152984089614940184446592231117147881833244491846081883$ |
| 0 | 1 | $0.00402361277671262623542396204422925474951943492598166466754504594800801991775617$ |
| 0 | 2 | $-0.010548925239812754286879941519929023644751134569178849751786082073575013015466$ |
| 0 | 3 | $-1.03312832023080154777509068150839416457591860300126484782442845282624610432692$ |
| 0 | 4 | $0.00864843191960386189679059701918447864836702423652876077305924405207588585228099$ |
| 0 | 5 | $-10.3322172824172724269898016279106261795821219166329808483957218382938819373902$ |
| 0 | 6 | $11.8804537841486721458799039429520890333913664909697082243121553809177007228385$ |
| 0 | 7 | $-0.0353135421230408960444140336221897112744934924924633157635166972862225631989058$ |
| 0 | 8 | $-1.8060236352824147224864280551419142668231965990540394229702613734678276623549$ |
| 0 | 9 | $0.427871714739779209942745575539742641967738655093808295902052618093332041084538$ |
| 0 | 10 | $-0.114142860063807677600997907776013903522026771495065187691989952305065430907016$ |
| 0 | 11 | $0.140401516726175846578037764207869713227096886560069372181218814388636400836975$ |
| 0 | 12 | $0.109409216533628256002038765802721045078265554913667464804972362338914884425037$ |
| 0 | 13 | $-0.149767789680514800878941469159081742942911764270820165862101984119340314343893$ |
| 0 | 14 | $-0.0452699430257450600117486588504011410280917363824340096558020973277875870233649$ |
| 0 | 15 | $0.0142354077365801362469165130266095896944379894033251325410617460101121854713466$ |
| 0 | 16 | $-0.0373880955442275401565212207126439723529694841545679496247764694148468668139119$ |
| 0 | 17 | $0.0160938216612526752316304614430208091052207375272346991591764284492953848671636$ |
| 0 | 18 | $1.81047274861885279634545999611934526818209770914212592495740794494683047283665$ |
| 0 | 19 | $0.12206791905927214443692049444791498167710910908441839897112456651728518083421$ |
| 0 | 20 | $0.00820683489776320546356599032800915762270703493755352685986197036274572615634055$ |
| 0 | 21 | $-0.0000301261966180207104305477010147257752491235094242128128932411359898615465812154$ |
| 1 | 0 | $-0.79316672386233008711050342123210410466446325091624941034303200952619799503454$ |
| 1 | 1 | $-0.00340237496378826587478334635817642095420061674072126481000319611919433904082871$ |
| 1 | 2 | $0.00892019215629816382219759608755158520714004873671465596348981125631240624164274$ |
| 1 | 3 | $0.873615361666538296201301900496425831631261530734713987441315133178434436868518$ |
| 1 | 4 | $-0.00731313122614360223751129475877157557603738212181335575754178171475000724576726$ |
| 1 | 5 | $8.73694347666292104944602829477534819157552492459878519976619306417023409208987$ |
| 1 | 6 | $-10.0461353407512554993893254371481955602572318960407215078756525858356989896194$ |
| 1 | 7 | $0.0298612014300942747427921755286994031021193713748180024890513848181913121110493$ |
| 1 | 8 | $-0.0127816171147831170283501825379648163969183098203523176125891299752440869746161$ |
| 1 | 9 | $0.134537485115670499279471430551881025740387012196565932564426909313285403411806$ |
| 1 | 10 | $1.51418617186743038084162693124758228409891616750694410052383432280913236198775$ |
| 1 | 11 | $0.356232695574208254282923051924005038025767631731038455900792305728014752036565$ |
| 1 | 12 | $-1.51722661461205170781740462209732736005451258315137405031301903122908275280645$ |
| 1 | 13 | $0.126643940724140987887851385952075788704057131837472623043632819337561151623721$ |
| 1 | 14 | $0.0382803538288687011082607587668176808531136055366095611925346621788971501241871$ |
| 1 | 15 | $-0.0120374890850778555166200273074540968113741814918831551847879418160053752001638$ |
| 1 | 16 | $0.0316154479277042150455475643207814319254208479082000624836071314425420443134606$ |
| 1 | 17 | $-0.0136089675947040666445740417770859985109694177008205872491134286200683021684402$ |
| 1 | 18 | $0.0171217008027551368444818483296922271155144418378505718312664410040451238588589$ |
| 1 | 19 | $-0.103220875053569550706970285325749526626538708568020306597541451871783624065922$ |
| 1 | 20 | $-0.00693971590648611143598738697436565661750011011296081372924963224401013920776547$ |
| 1 | 21 | $0.0000254747717575003549048119154635617875822001953227201502295873012007084340854064$ |
| 2 | 0 | $0.867527716433815408208241438869998533314385811185971449736312116358384799406933$ |
| 2 | 1 | $0.00372135453239102128551985355348027929102754275708507449295178454740788247780995$ |
| 2 | 2 | $-0.00975647830234410009772085158385535589999453097056021743061075504397695787317451$ |
| 2 | 3 | $-0.955518577553966933444571753709040292571309183599380999861322768711738756257152$ |
| 2 | 4 | $0.00799875214343759491362917393640419826555741575907249158189001618789090288580346$ |
| 2 | 5 | $-9.55604968651746467952638630597417539087224815161003270010729733884497311426701$ |
| 2 | 6 | $10.9879809489583442123266012124488241705660602227880975408853973977712259326595$ |
| 2 | 7 | $-0.032660749760747995896438637217338233990688005551359200311815867084963673816447$ |
| 2 | 8 | $0.186672001075625118873633224165209196075381513151731059605089906854017188976984$ |
| 2 | 9 | $-0.147150647809330280147768516813886539297363604165606453298539919814813787975767$ |
| 2 | 10 | $1.61224269448435580920404116185679042130320845639278101798020001601394316775902$ |
| 2 | 11 | $0.129854399421210760028302257746856729239906326903986657562407091032655220139139$ |
| 2 | 12 | $-1.60892063798635333678553744050807953931058292639056702746856933122954914709065$ |
| 2 | 13 | $0.380733832613180040915689273495846626958211679935412978742487517241232564169311$ |
| 2 | 14 | $-0.0418692148098752786489689753658299024902190846691972415035386756499303998450954$ |
| 2 | 15 | $0.0131660281544881550891760768012345359678776541868007543912757709711128329909837$ |
| 2 | 16 | $-0.0345794604332316777274293696468867031472537508514312365203789007914138769133106$ |
| 2 | 17 | $0.0148848359686161096889916952846935339650156371529327066306296879907795724602774$ |
| 2 | 18 | $-0.190391443010458044809216465901205526310045362704311671373510341806446029606751$ |
| 2 | 19 | $0.112898041899027069638607366146838702489129502211880483237954830026880926800463$ |
| 2 | 20 | $0.00759032837854942761729208680658061062911337155728483963156758211544936978709957$ |
| 2 | 21 | $-0.0000278630833903879779151453244723387922091303782141011172819329705558489300048907$ |
| 3 | 0 | $-0.0292098928281199737344611757891401987397475100074811722376481421342749748498272$ |
| 3 | 1 | $-0.000125299013515579262995737769318653335343512412888598525500573530603570785471317$ |
| 3 | 2 | $0.00032850326299988701344686118961330972325174906568938302222871798185179240502218$ |
| 3 | 3 | $0.0321725689184460148427171301338201231846772017983681478280229809448265994542477$ |
| 3 | 4 | $-0.000269320147866805262061876949162287448659219869097777775053912990529346709713149$ |
| 3 | 5 | $0.321754777300720193646430324487440259393852391832039527432185824765598636152405$ |
| 3 | 6 | $-0.369968290161232493656293392247214327575049854204973833024484136777995613793316$ |
| 3 | 7 | $0.00109969627727770353326388116002988411561904750564416699271811030772779420551378$ |
| 3 | 8 | $-0.166330616512990071425626566933287486855000078227724319730163427038858299198423$ |
| 3 | 9 | $0.00495460210743236004989196032790942232896295084236274712095876717890306762179918$ |
| 3 | 10 | $-0.0964034457940661965399689246524006843891138410494760361919514225040670523774125$ |
| 3 | 11 | $-0.00437223274657510621127520339935177620193835400261361164519761615899517760290633$ |
| 3 | 12 | $0.186700928438989764575713587677575486065740089941661688944096161713953799238864$ |
| 3 | 13 | $0.00466390712644800338712209890434276696198199446436933263383387590014056258987869$ |
| 3 | 14 | $0.680884017168481149887172938978902903435026706812346528040360534391282767065956$ |
| 3 | 15 | $0.326326122300606522027349148090559494189904096200813551221801772544495548680457$ |
| 3 | 16 | $0.255163021740248794982584519418547317064128342746945072377701567810286152687767$ |
| 3 | 17 | $-0.000501176452545758039507109384306950450378202167987931405736272700891877020325212$ |
| 3 | 18 | $0.0710317981823641867204673742894994248161965896302233479923913014720225525302857$ |
| 3 | 19 | $-0.00380130760309462354025010595721579086012908570272164970005234323963884435016178$ |
| 3 | 20 | $-0.832135364468923982551968748808747900945364725082239997100545631623573637488618$ |
| 3 | 21 | $0.000000938157553097952384668411740183016806510646883393923505409647429834752183414166$ |
| 4 | 0 | $-0.0489833423080295746914834215389968323208983649864627053287848234357369763515259$ |
| 4 | 1 | $-0.000210119376541617840529795769021913162046186187711568247419993260808040734514484$ |
| 4 | 2 | $0.000550881438542539270976972802848930943652039042632307428953044167684484127866226$ |
| 4 | 3 | $0.0539515829631458585292373797526589298925289806228907341170949951549755633129549$ |
| 4 | 4 | $-0.000451634693459364817819092833280871180153789808163583181215734070980190429006087$ |
| 4 | 5 | $0.539564608761332348065640387197130281364201854096950313857154681953718299459485$ |
| 4 | 6 | $-0.620415949716802152574197844308614195671179546320251059030146299823446866342454$ |
| 4 | 7 | $0.00184412861429271351270595290204220705423237692613330224808939592099295003775806$ |
| 4 | 8 | $0.0360232529989074022836398595733550867585218995276445882313209302134243305402356$ |
| 4 | 9 | $0.00830858820525376019205118809129961286281403033962657456413018938811967625278823$ |
| 4 | 10 | $0.0581675598590308010979031765882017898124141276713977132162360451660547374859219$ |
| 4 | 11 | $-0.0073319876432305650113131035745885613703591408616156775597310486955893422740333$ |
| 4 | 12 | $-0.157289047564307560494766332213866398434585513680826542191601278608559890965076$ |
| 4 | 13 | $0.00782110912258232391005377464570666095709995630810309251359457223195171689269678$ |
| 4 | 14 | $-1.71695788163887907084172479737873490185111744727204846048450193240456088732635$ |
| 4 | 15 | $-0.000743395342548285609468118788643703283633518390145817624658570480485882526206255$ |
| 4 | 16 | $-1.11422872158480058730539059065916519000482990447727216319271514595500205551908$ |
| 4 | 17 | $0.36964598715715020004835985779031909102575240547618947125724969077105934833653$ |
| 4 | 18 | $0.0541213366994591685285295365665573419640157853374076738893563107481707725492296$ |
| 4 | 19 | $-0.00637457838808796965679940111567520003629769243781280904221256768157794544801949$ |
| 4 | 20 | $1.01894082938709656964190762732592410122199427697214887310503965605464713218976$ |
| 4 | 21 | $0.0000015732372875405089480020057081594429724240507078450074861825084123877661047449$ |
| 5 | 0 | $-0.940793688367863411159735442485946494992084518833698147862146564827340092963881$ |
| 5 | 1 | $-0.00403563689082400807185020467951837660902008263143518084827789522426306714493293$ |
| 5 | 2 | $0.0105804495160975056839909373745841756677033442938455583041655498574880744007813$ |
| 5 | 3 | $1.03621570798492454546500938502490267327666193818626515689828988943189596319871$ |
| 5 | 4 | $-0.00867427678541393511002686232097445417812697264242867859235603659656918761274893$ |
| 5 | 5 | $10.363093951351821334028196097595651585866977004342610322707779322278256441911$ |
| 5 | 6 | $-11.9159571836861183737644194842503258007617492001714673737555437338437103065126$ |
| 5 | 7 | $0.0354190726707670744285666786092985977067852933609303052272732718252947124170823$ |
| 5 | 8 | $-2.04961964865807100076811157776568750362290876339612983242420533349083284626525$ |
| 5 | 9 | $0.159578072349486604449212316493251506435168042852389813938795702300107900165168$ |
| 5 | 10 | $-0.0569989775873585317667124023396925789790890265511243374057269422075381112339364$ |
| 5 | 11 | $-0.140821090863204490011180134701737911360829872983136582377035509707592761875383$ |
| 5 | 12 | $0.0615924895892676004729768407124720123045736853451584965167468465010925205040408$ |
| 5 | 13 | $0.150215353870525961886531547757807742653223549708980066825794768111599028677064$ |
| 5 | 14 | $0.045405227157435794533901294399184256956697056704415331646611053986884698189231$ |
| 5 | 15 | $-0.0142779486510630988123494267498568097561797015036000474527612024004034550141682$ |
| 5 | 16 | $0.0374998256614577417623211311837859498209289778477010957464659550011752220110283$ |
| 5 | 17 | $-0.0161419162366708485000295625837843067186956039654312951497757480443408661138915$ |
| 5 | 18 | $2.04518416195942841719792994799190685623741679660206075594901816429352910545318$ |
| 5 | 19 | $0.464541621530405368466083302554002465652288726233875598371706913806271894243241$ |
| 5 | 20 | $-0.00823136010055486151797572368343126977494768929935371697701126683112922541680975$ |
| 5 | 21 | $0.000030216225367301341935270638928645849342468952106861908059645493325769591730576$ |
| 6 | 0 | $0.0545566290987255593852729490347068490082820505245240304124291459248591651545858$ |
| 6 | 1 | $0.000234026596640739366917409619042198529881238175438511230371666834390078962620914$ |
| 6 | 2 | $-0.00061356030241756421802409828465224072812544917688990174357053159071320059413026$ |
| 6 | 3 | $-0.060090152331785067227904153258442666341726722956430277813588372010641626758715$ |
| 6 | 4 | $0.00050302133946339821883386486006666862229930853159690673756667535324612504395472$ |
| 6 | 5 | $-0.600955852499382353899656358615617583722696127103925351403864149286465019591638$ |
| 6 | 6 | $0.69100639647622931436693497503542836777707597318625545883989700373450683438163$ |
| 6 | 7 | $-0.00205395214127358425293353871516865464834759445041949595368344981323140559641811$ |
| 6 | 8 | $-0.106011570462604296191887441529923426868315060873022354926992602460100786383752$ |
| 6 | 9 | $-0.00925393294311340037246816979233972466661838195644846171975455618635888592218989$ |
| 6 | 10 | $-0.000374565804486915014692029519826882029569472453202450048332742535092721390380418$ |
| 6 | 11 | $0.00816621552471313581155936735566776160150377295901839021318973604036908872554886$ |
| 6 | 12 | $0.0959370182455582313559178276386728606037407324944915078238629387286101699176005$ |
| 6 | 13 | $-0.00871098886756523359799477691377514392823717243182412717118664089478896105549696$ |
| 6 | 14 | $1.88462916742740880989082037553708575798223484267774385672547001840289275377404$ |
| 6 | 15 | $0.000827978289478187365360435069458175892579243140536280357994870273864262503250931$ |
| 6 | 16 | $-0.343821595304411031240061175556087229256603465154804545313972377718083635082442$ |
| 6 | 17 | $0.000936069775929875887825658395468366631353140851242570351187814663300435569901567$ |
| 6 | 18 | $0.0202889851361832197577899949003608339938118758748641155245164265443167345441419$ |
| 6 | 19 | $0.00709987298524254104856107906787190476755334158808922399907203104957383231705726$ |
| 6 | 20 | $-1.70224388202751810033127621498564800695815785300301312726530636237040724386493$ |
| 6 | 21 | $0.309383424394364355537267119659419587729193567639413101371349076475970650283602$ |
| 7 | 0 | $0.0928188626815868388001057165963402683303173984192192375156740530041839887495213$ |
| 7 | 1 | $0.261195976452191488730116305319324909690364369904144774571028195675244945041398$ |
| 7 | 2 | $0.839835276794583601480136452561645238312065070884815265686220232337037411704013$ |
| 7 | 3 | $0.171137960491505894763995562457755694077460295445635437011970106242212542027739$ |
| 7 | 4 | $0.882717809964104238886033445755417547109918215067429000865932347490213034964238$ |
| 7 | 5 | $14.3709629864522487606299102869406394974550918033628579968793796744117470930619$ |
| 7 | 6 | $-23.4582274395786888546905218638954136310696228602002204628700237865659628323414$ |
| 7 | 7 | $-5.74455363596372422389894743946644081670903677180873890786110115210959834895324$ |
| 7 | 8 | $2.43827820823476182681717858507125458758651130841947167300186533995767975244628$ |
| 7 | 9 | $-0.368069056121103529486629141206681344187847629739422315213727016272229628702648$ |
| 7 | 10 | $0.269322684686005745919166088969028061837547728418515459759433685606803036151816$ |
| 7 | 11 | $0.0167215182634504063747902721185412805122765328491874667545443380635677802218595$ |
| 7 | 12 | $-0.304941469562496958664372236028912614464219589653834151208723308703083707092674$ |
| 7 | 13 | $0.0238820483472116836644815972524742671463137620790807111133202947404737613563343$ |
| 7 | 14 | $-0.319642045123814142201468892688938025167573317235729682230528179281942614080829$ |
| 7 | 15 | $-0.111416545856670020442593708899700670191896353967046727493312482232613482689995$ |
| 7 | 16 | $-0.143275231628725887828733203928359784978293044892459931489808958272793129160352$ |
| 7 | 17 | $0.0188419635927045410278658179473408210430111513284361395548714539159090996258893$ |
| 7 | 18 | $-2.40130306763210833123737022307867506668465921459964006921395139889578397756333$ |
| 7 | 19 | $-0.354850355690189924300120553963877672019690513229249161196843590125501709824589$ |
| 7 | 20 | $0.335957663732980634591308247349248765009606302863568117742971495658986663368469$ |
| 7 | 21 | $-0.0000861849052136604055237325812194146842084594488326224907491211779788248830197265$ |
| 8 | 0 | $0.286860406995149851866764177877673755720394734893619707990781669326089194591315$ |
| 8 | 1 | $-0.254956013266776920858995266575850402146482528303351064541600353855163443910739$ |
| 8 | 2 | $0.809745629710173964321969526865242202226934423346922920841254105441812348448327$ |
| 8 | 3 | $-0.0477357216482264997623067356123193869423201814292270181574208078050052326913281$ |
| 8 | 4 | $-0.848508816923790529587385383370509092440353579954948178043170342679798496881648$ |
| 8 | 5 | $9.30679233096378416355161199988588384812211948413992151876448795806076882345375$ |
| 8 | 6 | $-14.048205100594659844923114954066093126855808261758631397657379005124928382519$ |
| 8 | 7 | $5.47357834935567383148398843843312570412736532281282530177629253810833066664875$ |
| 8 | 8 | $0.289456275954729759967124360574201206022164376777651237025604132576413453834854$ |
| 8 | 9 | $-0.0486610926578264341232758382338508922452103344875027849258172786555075748766432$ |
| 8 | 10 | $2.21076147351722213375558819578521083858984492764065335984148182388968827108005$ |
| 8 | 11 | $0.320988696078910606413347266975116094617940771163578334699086637838122063094648$ |
| 8 | 12 | $-2.23554246118254416816690076906932400309221566102988041304237351376117992516375$ |
| 8 | 13 | $0.371994933505158512620084594837337823655186486424241875596706483387974003769627$ |
| 8 | 14 | $-0.268669405221045619629290991146329123414047800187552752183743475842862590699627$ |
| 8 | 15 | $-0.0642765126612992206079481091040555951105656452630318272896900292737999202229221$ |
| 8 | 16 | $-0.137591723760219796153684614930909229564620760195585254404869373655401291012362$ |
| 8 | 17 | $0.0290878298041628770164367167006500874727676563570189088974744935590084120958118$ |
| 8 | 18 | $-0.263777604319031561574937583913462173832201096805836111521173611567278026765065$ |
| 8 | 19 | $0.00598777609378959319384160841753782726075412486833602634707588726902343104271059$ |
| 8 | 20 | $0.243690383663135124089754770483376068847331776105829297059122189594484702255348$ |
| 8 | 21 | $-0.00000434060891609980330117788898094408639035752140556693345269326169094570888753505$ |
| 9 | 0 | $0.223057741483440847604463362876987337708216613514277954964304486356089722333394$ |
| 9 | 1 | $-0.269751097317194663654229876744191893365923770920966654003118893960657719430055$ |
| 9 | 2 | $-0.807643303678112275822904810399356030941315320222400818003901928698901404253263$ |
| 9 | 3 | $0.037938407121456107315414027936695847359218553909744003924204240791142933192546$ |
| 9 | 4 | $0.845644525365596023758880779282592484169418935869389589980700804768348195793832$ |
| 9 | 5 | $-21.6319766474093128416121248669176571680976791300918498497584615798003771444746$ |
| 9 | 6 | $32.0402593028109955081717603392545060612577944979192788758988884348543353486082$ |
| 9 | 7 | $-12.4980453857310642485175477125668824950869784386766687347773464300892711128444$ |
| 9 | 8 | $-0.293535917938710986431631079300108318166776447822163271875245953365553754046002$ |
| 9 | 9 | $0.00460380836453500078035064288397347480022932968117661783874321600506481888449803$ |
| 9 | 10 | $-2.2274709361717503790716795720578590273228875845711593501140097505443384234681$ |
| 9 | 11 | $-0.357216438607693849551697326313820113834705831151501200046479417029807196086952$ |
| 9 | 12 | $2.2823437507177861379171200564583930474647975900017497158106638031148868009611$ |
| 9 | 13 | $-0.333627998121593348736726327403027522950173622035878108143239199345858560418198$ |
| 9 | 14 | $0.595142191527226711509088262018672199337738356254130295663574804516122598396631$ |
| 9 | 15 | $0.129327063745872932098859398423414155450143738120542539172789264891661798771976$ |
| 9 | 16 | $0.311954854060995644683761683550916772502517529473560203610173390086932246545601$ |
| 9 | 17 | $-0.0702037621043041003377230505974460501843682610745784759817849048667470580268801$ |
| 9 | 18 | $0.237670032175654803319046536694321915765809151786150810912656890930596438668752$ |
| 9 | 19 | $0.0275969794712109656280207441007136377975847947978139607422529462708627630310233$ |
| 9 | 20 | $-0.522784052997542579356115646461671777617865165342814708774222155398375461969835$ |
| 9 | 21 | $0.0000701354824349092598397297474476371431452732612729717360865048523936966012039018$ |
| 10 | 0 | $-0.000146863038291030931002262341725472541797955014552173427966678433090498507039518$ |
| 10 | 1 | $-0.00000062998498241841402073712256387953500909911879560928988125355104148040834865068$ |
| 10 | 2 | $0.00000165166601522879282711216373416823814902397090929839166026652726459022550464458$ |
| 10 | 3 | $0.000161758937247517443718580779744623973947302978634901817515918678098346884467669$ |
| 10 | 4 | $-0.00000135410203048165311928882033425186373127428812743406097016697251329078525628529$ |
| 10 | 5 | $-5.57253285539370869567157701653105142747399342821871315125282467956111459060483$ |
| 10 | 6 | $14.254074732246858201605507297702987458081136614934928717344514412393902755175$ |
| 10 | 7 | $-0.00362717930097706876750235737825083152340696569514240801149240717072191065796553$ |
| 10 | 8 | $-0.0390733597992103953118702919793468929303727826897939926825268128894540449997378$ |
| 10 | 9 | $0.0000249110095440050470309306318064384142877004274552706385249377147481864534190731$ |
| 10 | 10 | $-0.0271440946691446889573177160422681352310782734976698955251238466104748932367653$ |
| 10 | 11 | $-0.0000219829421852379890726544232984027454981974108126914312194520326922402033665204$ |
| 10 | 12 | $0.0579979830824310230475113077753451477563225465724358579847621099837332254857473$ |
| 10 | 13 | $0.0000234494380012906989819942028689034811501099340827818935623858157405416467168258$ |
| 10 | 14 | $0.350328857730087787207405483876444087521177224279615245784585300527073832108365$ |
| 10 | 15 | $0.0681377562766129314731008051494285264456925821065508271002214815455544338812979$ |
| 10 | 16 | $0.187996823635350663203978444244746430768713115633766449733437489948039740344632$ |
| 10 | 17 | $-0.044850970001969205468815299596313168887732773403213478106178457371696194022797$ |
| 10 | 18 | $0.00826587272436494746108455824620070346178010202952839146388171005116330563586121$ |
| 10 | 19 | $-0.0000191124146656174002440283038917115933951373451366416704950487088507178584919313$ |
| 10 | 20 | $-0.297322974966269354055584482969288507839967839648100024568873947324381821365629$ |
| 10 | 21 | $0.0000827433774496852777534783116213910407674047271437067330376041037713039390856815$ |
| 11 | 0 | $0.00285687099407889460960847540902845809521062853424414027083242503019947253059771$ |
| 11 | 1 | $0.000012254858975543774258707404906262078226575789838672362842547603178372873073086$ |
| 11 | 2 | $-0.0000321292326900006490722863064614117087900726019381327918200873671993542709542693$ |
| 11 | 3 | $-0.00314663526802225417736759444351986914930561398923658331128434597171947051343483$ |
| 11 | 4 | $0.0000263408333296249308790315309419414461729050111945280759570216286723525946324802$ |
| 11 | 5 | $6.25844467037834654313382022503332767598329377681109055286270678802973158275551$ |
| 11 | 6 | $-2.6370485195961756322726438436572034187212796167263331026840010586246465009698$ |
| 11 | 7 | $-10.7466151801064214336407493362146518077229397856565476309725015563088990176198$ |
| 11 | 8 | $-0.0131937520045045055768973264749451535006321095043740737446972014364524859202363$ |
| 11 | 9 | $-0.000484584422517948145609017821421803334141364554003218213967959041350532622141968$ |
| 11 | 10 | $-0.0111456085106552681175420018943223245565934850924092389082152710249639227750947$ |
| 11 | 11 | $0.000427625838497685004389607363393092633766640531166506549372975089867559765803205$ |
| 11 | 12 | $0.0257574686746668056635028950514116741853783199529427148666976587966688797261952$ |
| 11 | 13 | $-0.00045615302551881111872448268504970203346007828153043067514157142694460324144505$ |
| 11 | 14 | $0.200885674707520372124081282871258255183996281297330893562479900851498661578267$ |
| 11 | 15 | $0.0193542622186118427414141263177977956435298718552936260480492017308755754157181$ |
| 11 | 16 | $0.119481538054221484710959265530095914788242631021144734291293098168595399060021$ |
| 11 | 17 | $-0.0346543815083418293608048916613428652091617141342090164488226434636438900689586$ |
| 11 | 18 | $-0.000873740801044759617594936577928706326571384647453434470386218646781937299261379$ |
| 11 | 19 | $0.000371786555149492679521523727670418025675180053149095740893425046346601143527844$ |
| 11 | 20 | $-0.144458303742422698136238613930114376868760081787270731353629702189231994210955$ |
| 11 | 21 | $-0.0000295227897903955897065709447542978175410991713155683343089065209222604179705402$ |
| 12 | 0 | $0.396366670297531512557104479775558691577827167745226361918157970410444317716671$ |
| 12 | 1 | $0.26350728927586755848354708253355215060127650898176895882847146592158660507038$ |
| 12 | 2 | $-0.841927522558033471515503072412565509327705255906998787195771234714990174912905$ |
| 12 | 3 | $-0.160353416390001295778283339196932337694033365715679365477700615117408237474363$ |
| 12 | 4 | $-0.879861782614332749538192021860354912684379134361800728522941171185151703746873$ |
| 12 | 5 | $-16.4026599403545562850931636417942114197023338823211685454042562778490397229731$ |
| 12 | 6 | $15.3764869630957713368115056066440418469623737978675427322147499402275942744109$ |
| 12 | 7 | $12.7694058693353971642936493960237134411571368931083269323968631041605525373265$ |
| 12 | 8 | $-2.43560078599157428219112725817520231076471042398252363277994417380386600155074$ |
| 12 | 9 | $0.41227837458188393906111331075478803674401135035848107200259257299822421586603$ |
| 12 | 10 | $-0.252990520444957978337620850964730990755425737258160534630213048951542564642962$ |
| 12 | 11 | $0.019372060360486384649641595203746114950413213593476405312737867565610641887621$ |
| 12 | 12 | $0.258345299077471086811666774514570072332847985900156530412022782787972062173803$ |
| 12 | 13 | $-0.0621058696679640637822619158536394461372932888164323393083176769571294700071347$ |
| 12 | 14 | $-0.0195212529985658938902173327393603544741697832734138403781747209156065996963685$ |
| 12 | 15 | $0.0499419131145405207563434906342871596817491449225966892768936319724763331525072$ |
| 12 | 16 | $-0.0413338376501748361504175521150433354525182044218719509493800940476310505873846$ |
| 12 | 17 | $0.0266003590664345651820612752348444263619924439276378153190575372426211302916362$ |
| 12 | 18 | $2.42882464420727302771241179330438942536921430712128423220406133934366973522015$ |
| 12 | 19 | $0.321148955312089427436822521319805070051319484964360630618017507474591782460173$ |
| 12 | 20 | $-0.0540198102101897717400605584830883860584311893582922053953554897414184326648806$ |
| 12 | 21 | $0.0000124193577104649801084571763543726923521532624369193881206881573493559906709405$ |
| 13 | 0 | $-0.00181368941349691450704395019386303889016858809203522923178392569391619741445895$ |
| 13 | 1 | $-0.00000778001808058806067621481517714732245205633263907792774170783314727923570893805$ |
| 13 | 2 | $0.0000203972980629533925470775277613432006621305286902530723586464749765830592771661$ |
| 13 | 3 | $0.00199764675604053019482949807857542837503300880012862419271550318267911857437305$ |
| 13 | 4 | $-0.0000167225228761267970965625177537157370460673431367782955084930497700919389248272$ |
| 13 | 5 | $13.6709694553631983550615230133830689937135013763178614779089681167082839587814$ |
| 13 | 6 | $-21.5273399383841007147024925819828251896545941720365653622467489371602946623639$ |
| 13 | 7 | $10.7498571624111159790471090111693868057578597459159454474492859034096071861002$ |
| 13 | 8 | $0.0536693315445085827272230102841468817538160788017320610549446689612330802355814$ |
| 13 | 9 | $0.000307639245484966867019112991386089808670948313815357873651527251050514997485718$ |
| 13 | 10 | $0.0386670015932804348094058562049415774385924243602301995766464076348284968910605$ |
| 13 | 11 | $-0.000271478991465994901398760923678066134193129575094821838042949494668608679613308$ |
| 13 | 12 | $-0.0839605708073139266085280287014833241829111917435702548230495322189973360904135$ |
| 13 | 13 | $0.000289589524704736654164539649035676838276630696435509523109283785744326894099427$ |
| 13 | 14 | $-0.538524020621409215119597812191747038987120961134380160218193629854283287606439$ |
| 13 | 15 | $-0.0910679368376689860191760025211713719186533377749051268149510686341547383085815$ |
| 13 | 16 | $-0.297232422711447272465864022351446768064041266618554250790845552227741915190154$ |
| 13 | 17 | $0.0751789611513131519409794319722667494034914969989081067653825209845485001052984$ |
| 13 | 18 | $-0.00880613635510812606264014467484609775337186488403381937508871121558553789710571$ |
| 13 | 19 | $-0.000236029327383937237841815297957569522247934109273910580901127226472149994353323$ |
| 13 | 20 | $0.438937094520308644606936284011538214528086197167080255289987609399936344587482$ |
| 13 | 21 | $-0.0000452499136749037191701838204687442881249151092998400987340761529223255210827221$ |
| 14 | 0 | $-1.25346742352566585147332758979535460179290749548032856767924160492120810010186$ |
| 14 | 1 | $-0.00537688489875193446933212644339750176575685714350218797636293527920814187937773$ |
| 14 | 2 | $0.0140968726285718817646437761255570710375956192090075191316256875362610010661954$ |
| 14 | 3 | $1.38060304800515812836182478403821533477368463935229638579111324878858369113905$ |
| 14 | 4 | $-0.0115571814602882796207714656840981781120954759926890466282567212533904583969526$ |
| 14 | 5 | $13.8072787217468946393921245140310766806119054930221278806479456050745950367734$ |
| 14 | 6 | $-15.8762376220756503309769657524890791574158566643668084363133540122121533322119$ |
| 14 | 7 | $0.0471906373450658401765777920460873662699580521896343632490107667677246722851033$ |
| 14 | 8 | $-0.0382421248943918296063974724184030102384628011902128464140415579595358573800125$ |
| 14 | 9 | $0.212614006314305075468280406778434677701620936264701647835127981846604113274929$ |
| 14 | 10 | $0.152512507151548153061350049376742028704613238039154200808059307753240423079993$ |
| 14 | 11 | $-0.187623123034127897123577857984282598634971659384679455662213979263781161154146$ |
| 14 | 12 | $0.0925580700738612870759767003296301298166128581618701325346771011184426780035028$ |
| 14 | 13 | $0.200139578866371291818624448250553981725335994825341461919803091895582823508703$ |
| 14 | 14 | $0.0604957003892807615772629737417043075555260054610854405188984804519879204564019$ |
| 14 | 15 | $-0.0190232393458424914481290783389261563944613542678212562917570811570677416669854$ |
| 14 | 16 | $0.0499629306995834666547650450004702826325119122691529447323530657211431456175338$ |
| 14 | 17 | $-0.0215066984463392714197951099411254765389870747936387221673046915195654820900659$ |
| 14 | 18 | $0.282162930794761118583966073378964691916816493014255930526639163196022387607609$ |
| 14 | 19 | $-0.163123338908402915688321444874631055098548307643911369119604445470019806166432$ |
| 14 | 20 | $-0.0109670609666336192463038894577507318813698274970200522485821506223452252119198$ |
| 14 | 21 | $0.0000402586184708888126136943747734662281466505843303716642872926343191165256775946$ |
| 15 | 0 | $-0.00537688489875193446933212644339750176575685714350218797636293527920814187937743$ |
| 15 | 1 | $-0.0000230647328138038559745381689075313905247010039122038714466586527886799463734284$ |
| 15 | 2 | $0.0000604700689731531925991977418694658026145186460984463996356570900110792179501907$ |
| 15 | 3 | $0.00592224699315277201141884806668200075055977319471493072878675368947745177122243$ |
| 15 | 4 | $-0.0000495757873716192958023778814385931610772312688445486168468672348947641238330734$ |
| 15 | 5 | $0.0592278244000967115834749674213129930165045796141571660582810821417547922867012$ |
| 15 | 6 | $-0.0681028487194569427829736206533864009987429296286903065474150804121432254774666$ |
| 15 | 7 | $0.000202429373544838738663389853826352009905187878101023792134434666278793746306104$ |
| 15 | 8 | $0.248888733663260331605878274782856717556772080700936199750295916404323572272411$ |
| 15 | 9 | $0.000912030913894051712214747964426734101167175845025405036779023228967799223336559$ |
| 15 | 10 | $-0.242348889862560304320282634529225325337290223796669902697409478278260813291286$ |
| 15 | 11 | $-0.000804829800890491096170401186684634474609027208903120925795527374779202552550303$ |
| 15 | 12 | $-0.257939281511956069384553894111511732056492736612958886894348045775200743629686$ |
| 15 | 13 | $0.000858520500056002410681164884780777508436355177579941098464748864827928816836723$ |
| 15 | 14 | $0.000259502889151777694975687709585279465572102972265629166218886624308365002144997$ |
| 15 | 15 | $-0.0000816022550281377371425502475393520974291622739466757690554403576380314919728982$ |
| 15 | 16 | $0.00021432142753287838006725146802903969995143674529653050989549938498529415425708$ |
| 15 | 17 | $-0.0000922553230564795035900365191883839195943005833293145196126000795452950566674966$ |
| 15 | 18 | $0.251403977874348930680439218766827587256237136187473180476229735727671788684968$ |
| 15 | 19 | $-0.000699735311144786365782239778917559904404803857464091967807098400941239675592326$ |
| 15 | 20 | $-0.000047044401305078404996190547375547752527113218034227610048445247896041200783991$ |
| 15 | 21 | $0.000000172693724334596096199647260225933766903776413017816234336222385334213565214586$ |
| 16 | 0 | $0.0140968726285718817646437761255570710375956192090075191316256875362610010661964$ |
| 16 | 1 | $0.0000604700689731531925991977418694658026145186460984463996356570900110792179501985$ |
| 16 | 2 | $-0.00015853768049849132007589447997698578119184704051156607195973830377249893262677$ |
| 16 | 3 | $-0.0155266781992665961879660721269150971280500230207867028246683628883227050427324$ |
| 16 | 4 | $0.000129975547775087691538017617003398251855865300900502926448507483039498214023056$ |
| 16 | 5 | $-0.155280820095179237692529050268114697956976752760354214970595806782011219173344$ |
| 16 | 6 | $0.178548955783659234047420560646787559000472584418008526929848784062530151045485$ |
| 16 | 7 | $-0.000530720137938151460837193725522186004836307709728669700993209277012779550343682$ |
| 16 | 8 | $0.803440195210587999147217830219551142266802917436654182844886642168962485978082$ |
| 16 | 9 | $-0.00239112122884920454736885298975603798278599563312396468728949797206256461576147$ |
| 16 | 10 | $0.769420816196150168055929147187647426480581235396585995926975453279354759322821$ |
| 16 | 11 | $0.00211006621946949661537295473536549888893941355465302932899218255567229877707175$ |
| 16 | 12 | $-0.769380246376209318445999392862469737886179027657007025968640556024733080659544$ |
| 16 | 13 | $-0.00225083005610116156237588564931067370639145184736659893646927893800165271921209$ |
| 16 | 14 | $-0.000680352889080467964931445198369678653314966169649874543086864803631717418214325$ |
| 16 | 15 | $0.000213941086148767955467858668925661766547990744210744135268858545831875643438075$ |
| 16 | 16 | $-0.000561898184989225095488167488098856029523877300811658730200898552781751035082899$ |
| 16 | 17 | $0.000241870816081038479654639365756985119538254904029158135093339079171187484100364$ |
| 16 | 18 | $-0.803494070516926571743826681856468497491839368600467613389179373553877642630428$ |
| 16 | 19 | $0.00183453425927190427733554003884252468651697391760313313110743243552980882694996$ |
| 16 | 20 | $0.000123338874752376804307166538445914968917690565178868023003999201533029509995971$ |
| 16 | 21 | $-0.00000045276056332609620609526280847590727569173758375941660372529822507633654055522$ |
| 17 | 0 | $1.38060304800515812836182478403821533477368463935229638579111324878858369113905$ |
| 17 | 1 | $0.00592224699315277201141884806668200075055977319471493072878675368947745177122277$ |
| 17 | 2 | $-0.0155266781992665961879660721269150971280500230207867028246683628883227050427313$ |
| 17 | 3 | $-1.52063367614284441066642951443860239538490995023619129146627097619530172598022$ |
| 17 | 4 | $0.012729393401819024224676864831884893349144334425434362844617428285455264798927$ |
| 17 | 5 | $-15.2077116087175339920234843410647461408415611993728501240807399575697491171042$ |
| 17 | 6 | $17.4865191073256481825850823772939122750080598749131011368060883790920910935855$ |
| 17 | 7 | $-0.0519770490505850045750408385495271320912297081008821396011490898547092711601464$ |
| 17 | 8 | $0.303180805998650355440271222785041440027004058633111221793072065466050643439782$ |
| 17 | 9 | $-0.234178838362213826010826517833216444141972590442203698265273409349909733726528$ |
| 17 | 10 | $0.0864360276785266533859851222191086679250107894622673343975218886143036904409602$ |
| 17 | 11 | $0.206653201092832259455334913932532503164388694575332685894850960139068292412506$ |
| 17 | 12 | $0.168712573780079157371500494325251868013473499268423639675034421770020813331601$ |
| 17 | 13 | $-0.220439165329232169667407632240478013974653613629407782403883928644413850467271$ |
| 17 | 14 | $-0.0666316066784783845871028684545917289606078233692147920394903396769624174454968$ |
| 17 | 15 | $0.0209527122371712956857405706957762368693002533562466823859165077347343649498493$ |
| 17 | 16 | $-0.0550305282103751587767610936777095390941798967868813447251959504921519635308265$ |
| 17 | 17 | $0.0236880615086330742660278376000056432468435185707180490008384455358721258616997$ |
| 17 | 18 | $-0.0468188847241078799261071655393546433854134445674621166093490162140274606066525$ |
| 17 | 19 | $0.179668473763975825391857051188436152318243381626570707351809972513978235114333$ |
| 17 | 20 | $0.0120794186701755492199782733381752288622928356527555663395815490286399478299541$ |
| 17 | 21 | $-0.0000443419352798583357522550934938080462947420554262880081758243067838447539274452$ |
| 18 | 0 | $-0.0115571814602882796207714656840981781120954759926890466282567212533904583969517$ |
| 18 | 1 | $-0.0000495757873716192958023778814385931610772312688445486168468672348947641238330723$ |
| 18 | 2 | $0.000129975547775087691538017617003398251855865300900502926448507483039498214023037$ |
| 18 | 3 | $0.012729393401819024224676864831884893349144334425434362844617428285455264798926$ |
| 18 | 4 | $-0.000106559166037469979488777176984745801448241978936692976844317322014453791175841$ |
| 18 | 5 | $0.127305443017553350895291517044395293289706294689465829525919439359756432685111$ |
| 18 | 6 | $-0.146381593698615160094172047980090107416874168008240239484638601334401457743969$ |
| 18 | 7 | $0.000435105650763180996700369359345286789996528912136668138511164714272348275014044$ |
| 18 | 8 | $0.841794707519427501354972121927686753753508222705636984792799819246207040419251$ |
| 18 | 9 | $0.00196033706648857964206258960322220415974796547742952621538633536463000181739958$ |
| 18 | 10 | $-0.805946942981427959667845018622344568444819328712611846954861971622120816182872$ |
| 18 | 11 | $-0.00172991689959704007613196722226044904559782780331743785962234306253840074550775$ |
| 18 | 12 | $0.805888531630173162446807873298838733282693154910537258558845274951054559946106$ |
| 18 | 13 | $0.00184532073744553006742858220563285299169478386522841218099224077688364642996431$ |
| 18 | 14 | $0.000557780580367698853460890316351181740213658637296616075657269638116696931347198$ |
| 18 | 15 | $-0.000175397481383285153052891522942442850051243230266845520537990686343729875606921$ |
| 18 | 16 | $0.000460666663963820806136552144084230151080219126364539696602537186566790095021019$ |
| 18 | 17 | $-0.000198295393953613629964323079809176286302103273602739854291151512121240750607652$ |
| 18 | 18 | $-0.841723115311819819492633397740995631512340625761281878755667621560027358305757$ |
| 18 | 19 | $-0.00150402474989723087433666392688316049826047253887536067838865472531810122249312$ |
| 18 | 20 | $-0.00010111815536531495633692320795498847321368925380543505131320770023996236598823$ |
| 18 | 21 | $0.00000037119126534607425658510131081712963361299938673406776347810444413753958752253$ |
| 19 | 0 | $13.8072787217468946393921245140310766806119054930221278806479456050745950367734$ |
| 19 | 1 | $0.0592278244000967115834749674213129930165045796141571660582810821417547922867046$ |
| 19 | 2 | $-0.155280820095179237692529050268114697956976752760354214970595806782011219173333$ |
| 19 | 3 | $-15.2077116087175339920234843410647461408415611993728501240807399575697491171042$ |
| 19 | 4 | $0.127305443017553350895291517044395293289706294689465829525919439359756432685121$ |
| 19 | 5 | $-152.090865803103992029690977142549589538238413343288778732603131618716293782439$ |
| 19 | 6 | $174.8810011225586299734101660315951078903921181913755936044014988534462446766$ |
| 19 | 7 | $-0.519817484404580048608347557357092991935631934056100668006893339252362123867547$ |
| 19 | 8 | $15.1213928439423226402257052731349599104747080591720116392623769784847698882457$ |
| 19 | 9 | $-2.3420001112368397669696627114864526501985752117411533829594680082221292564559$ |
| 19 | 10 | $10.1451341167354976175169321143318557683481157075965905059648288268398570919918$ |
| 19 | 11 | $2.06671885184718538198086393631999281774348781777506829696811068581647004548239$ |
| 19 | 12 | $-19.3181751726301113201378343065662713698842751568773277498294906059830199463366$ |
| 19 | 13 | $-2.2045909584856874539253873329519006544228524783148069798796258672780626195676$ |
| 19 | 14 | $-94.4903442242616921026778539228165760457636816261964976132284292545501448694316$ |
| 19 | 15 | $0.209546066302832136798736402007409928985281724724657089087474100530451814748051$ |
| 19 | 16 | $53.3297101482531945109088865121365545810704956343197836487003123751243322655357$ |
| 19 | 17 | $0.236902032122964803984454501561729753725940822901233327197818320544782164020962$ |
| 19 | 18 | $-14.6107482846167713580282219988933352861274999898685763677622695973343972958774$ |
| 19 | 19 | $1.79684718091453557460763862016450292589346327953666344792195973190572619823331$ |
| 19 | 20 | $81.3561558334182691035780657783985493385034153491311405794593278411809048096536$ |
| 19 | 21 | $-0.000443459443578150431661327536272699037369338710291547618535752170093931014302899$ |
| 20 | 0 | $-15.8762376220756503309769657524890791574158566643668084363133540122121533322119$ |
| 20 | 1 | $-0.0681028487194569427829736206533864009987429296286903065474150804121432254774706$ |
| 20 | 2 | $0.178548955783659234047420560646787559000472584418008526929848784062530151045473$ |
| 20 | 3 | $17.4865191073256481825850823772939122750080598749131011368060883790920910935855$ |
| 20 | 4 | $-0.146381593698615160094172047980090107416874168008240239484638601334401457743981$ |
| 20 | 5 | $174.881001122558629973410166031595107890392118191375593604401498853446244676601$ |
| 20 | 6 | $-201.086136186649172411332612771210625483297320487642134469352000144116770617225$ |
| 20 | 7 | $0.597709807184408047025121086130358236371169966468337817739876223861568753753841$ |
| 20 | 8 | $-24.0088400324137421911158478941348730966812143462811613859618252522161419125779$ |
| 20 | 9 | $2.69293834261204759610952007123060200948732557957137523319992822505600290450306$ |
| 20 | 10 | $-14.8399398539905251353607130094027227231532928829523313581961670232327885717435$ |
| 20 | 11 | $-2.37640741895575664457986122749607987076009617327010585956714590407915518693007$ |
| 20 | 12 | $29.0522142268430932690632366799283079340833918112725439674281634916786486893563$ |
| 20 | 13 | $2.53493904351124867521514728933658167245927309524940471048012244409117177880214$ |
| 20 | 14 | $240.721780849612650081293689808775297725515081734585791032121879970185556044592$ |
| 20 | 15 | $-0.240945606186334424690565415684910772455353360394408347146753882907255340319959$ |
| 20 | 16 | $-22.2663743947467197140920905880533285099840876953456592733874331218169813551948$ |
| 20 | 17 | $-0.272400741010096207727027806575468397279017201103443584606395983688240653934203$ |
| 20 | 18 | $13.4706128035414202955715286683628805665731381749352567364560344796932551012277$ |
| 20 | 19 | $-2.06609668636765731301996201928448174589071907707649771246145907884648776560603$ |
| 20 | 20 | $-128.108726704637350409652844878075947612265000466813975017991966450907584214191$ |
| 20 | 21 | $0.000509909855800275120420538923312375483368083382223812747762970237091642663680901$ |
| 21 | 0 | $0.0471906373450658401765777920460873662699580521896343632490107667677246722851039$ |
| 21 | 1 | $0.000202429373544838738663389853826352009905187878101023792134434666278793746306118$ |
| 21 | 2 | $-0.000530720137938151460837193725522186004836307709728669700993209277012779550343651$ |
| 21 | 3 | $-0.0519770490505850045750408385495271320912297081008821396011490898547092711601471$ |
| 21 | 4 | $0.000435105650763180996700369359345286789996528912136668138511164714272348275014084$ |
| 21 | 5 | $-0.519817484404580048608347557357092991935631934056100668006893339252362123867553$ |
| 21 | 6 | $0.597709807184408047025121086130358236371169966468337817739876223861568753753847$ |
| 21 | 7 | $-0.00177663672085684948366482965241741476085026051281900627069812173755687451175312$ |
| 21 | 8 | $-5.48107056402360877806153295660635337031065649178960472961810364236388622560925$ |
| 21 | 9 | $-0.00800450835669800470345857526594346466192631497295251714029008974427281613437494$ |
| 21 | 10 | $5.19640881426367685662540058194896064287222485110145450113180899410773359489826$ |
| 21 | 11 | $0.00706364967327840906404129817765955105574458018914542927396397756386901716415744$ |
| 21 | 12 | $-11.9223436114719827852548478249795149549694384534266436873835103690190131107689$ |
| 21 | 13 | $-0.0075348701589002581806430938292306136164647865157364559510563482657397449073015$ |
| 21 | 14 | $-0.0634232068674123037939617361259395031557272107404724054575629853982448702480154$ |
| 21 | 15 | $0.000716188368560069687812790244440207495132222564314766971532932624549763015522084$ |
| 21 | 16 | $-92.0575980599675724116016758265286636900066851412145541113330307754244363399098$ |
| 21 | 17 | $0.000809685826550007846344397321879391584314114151908661982004734595625123821099756$ |
| 21 | 18 | $12.2066091153076487735967114333998112178886389912943842182478012149200144253971$ |
| 21 | 19 | $0.00614127992835315122039040110651623257409122809182070327736296246211662025533846$ |
| 21 | 20 | $63.9710695472147497721250893647120143569125290564712665937418664267113168560324$ |
| 21 | 21 | $-0.0000015156595445690753826474476967362692502076864283706553272105914774614088548208$ |


## 13. Root inclusion, selected values and nondegeneracy data

**Definition 13.1 (interval units).** Unless a column is explicitly rational, a pair of integers $(l,h)$ in §§13–16 denotes the closed interval $[l/2^{300},h/2^{300}]$. Rows labelled $q_i$ and inclusion are exact rational upper bounds. For each root, inclusion means $q_i+\sup|(RF(c))_i|/10^{-12}$. All first-moment and contact equations use the order of Definition 3.2.


### 13.1 Root $S$

| Row | $q_i$ upper bound | Inclusion upper bound | $(RF(c))_i$ lower integer | $(RF(c))_i$ upper integer |
| --- | --- | --- | --- | --- |
| 0 | $147695273044142366306383188497525864681139053547511915511988533983583210471398281/509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344$ | $1608664665010247790049374625379599720472028787198685826047256754514273960471398281/509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344$ | $-5843877567864421694971665577637547556476745903612915798536548965870040$ | $5843877567864421694971965747528295423163558934604695642141072882122763$ |
| 1 | $301103426255795022923860396120606238406941721428798212351458807103952890312341503/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $3047141538238172448542086858223016897876597849801463666043139775643524890312341503/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-2746038111982377425618193785955902077982728529607905136948482682761617$ | $2746038111982377425618226462102410659469656128372665453691680968539572$ |
| 2 | $255083650798701823383390625086687632186283781076796069117710934862789898366622827/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $2526392659740279915243581772849442201640829097972742660324703787149470398366622827/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $-4542618017883156183720139992984772773397927407543078032377078846961807$ | $4542618017883156183720382295525509138909090633791893182413985704573361$ |
| 3 | $668224121131082857252824926252490536352323645393199475507697520342464551013103495/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $22733750049386026397835004871408735781604517182231823820393288188478262551013103495/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-22065525928254943540581081428009902464052729055786001688159876806300344$ | $22065525928254943540582179945156245245252193536838624344885590668135798$ |
| 4 | $1743999518945731444773832807111991554781491769943184478498858157002837157905015641/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $38136948403853473437047441004683896546931143480300593384447123669455453157905015641/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-36392948884907741992271517057257950967455192285772565809394129972510490$ | $36392948884907741992273608197571904992149651710357408905948265512452616$ |
| 5 | $157929408945654297277076915575841731155712939448115060363080283641184536258480395/509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344$ | $1825016624626182152779489726556223334824630989327888467661318498941139786258480395/509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344$ | $-6668348862722111422009651243921526414675672199519093629192952861199821$ | $6668348862722111422009315732622171521696966933475059828318776852462018$ |
| 6 | $624503629432798933789708571542547372280378672636680481449457533811733093695838739/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $7240267117922365937551057020904865587635320258204603858498537348517025093695838739/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-6615763488489567003761348449362318215354941585567923377049079814705292$ | $6615763488489567003760969198307425118053648896018527615555737996732722$ |
| 7 | $199339472491455611868983188012690803733532658163962165392312592395778733350874903/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $1226017559658600228463332328318064537675389664387968805728945651410423733350874903/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $-2053356174334289233188649202728022000190509187818747689472361630639472$ | $2053356174334289233188698280610747467883714012448013280673266118029290$ |
| 8 | $382807347662176686389626832099490465431637848064391172622428444012666649078215137/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $2056879533083991884712979364207158279631963809279842598858851863596615649078215137/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-1674072185421815198323338101115178816475328114442914183563994059287816$ | $1674072185421815198323352532107667814200325961215451426236423419583949$ |
| 9 | $37711653318616285342649094079316085736677831381317251915605790535113009721358533/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $1017438319293734800670793902690028571580292370315177393027356756320361009721358533/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-979726665975118515328058108600484261852942195350504989467169403358613$ | $979726665975118515328144808610712485843614538933860141111750965785248$ |
| 10 | $152678202602177015999328044476854312506554258151371928082463569628716410024273445/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $2532926621244216873278625523173791154077017190738297937723872498455335410024273445/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-2380248418642039857279171901850523105145348610424436782020114316784393$ | $2380248418642039857279297478696936841570462932586926009641408928826619$ |
| 11 | $719777100415696581350653812416200065805679021251179017573439538178568442108130193/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $8122048919709429005660024588464335516599404377888448097898566105238896442108130193/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-7402271819293732424308925647804029352616480495453789175227554528147840$ | $7402271819293732424309370776048135450793725356637269080325126567060328$ |
| 12 | $54272638244297116323683889527273214414396830453193018604113439833557581923541611969/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $1502825921177901774569996296001152779921952880021811545352905986527699351923541611969/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-1448553282933604658246250513806528229922248783999424554837986730275453061$ | $1448553282933604658246312406473879565507556049568618526748792546694141770$ |
| 13 | $28223285667889990359725394944042406162436318179692632769113143758773035793013859/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $57633413408061142963440010242890325188147840586116680626093276979181035793013859/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-29410127740171152603714615298847919025711522406424047856980133220408$ | $29410127740171152603713783092176370062990715546082274380308293155972$ |
| 14 | $87397666288354725885030637369758556346183486740679008176415640532953658885595643/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $163321681064104383364509107566838472924557031307506329653534882108753658885595643/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-75924014775749657479477938316338670297190914914061079938089179625492$ | $75924014775749657479478470197079916578373544566827321477119241575800$ |
| 15 | $7570807025452912449459479331188842649550193905613085050289529469637748338705922961/254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672$ | $208300163002922124250246702559704845346199772368183346012760950985322125338705922961/254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672$ | $-1605834847819753694406228978317425969351511696952413490417852865081779020$ | $1605834847819753694406297785828128021573196627700562087699771372125475016$ |
| 16 | $90011366831720710415416959458756894767501388754055219951867394855057133354133703/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $157618813607394792536429658634967878340087602248082518273004475939382133354133703/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-67607446775674082121012699176210983572586213494027298321137081084325$ | $67607446775674082121011256927452282906314677944911003949897169412099$ |
| 17 | $16403028915257781928756969667989999763960633771910024934748570736587296285112670087/254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672$ | $467241229183609124780772397805923250231878568395237103713254733708758514285112670087/254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672$ | $-3606705602146810742816123425103466003743343476986616630228049303777369744$ | $3606705602146810742815905843967817268800279727004275917511832302691963446$ |
| 18 | $80341495136299910978679241366078617473032631780460500062556789926698946948628852735/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $2418384122357086494751925614803455970178864622906525378877782245924622999948628852735/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $-4676085254441573167546242870346494473797543619076830678147900298415391687$ | $4676085254441573167546492746874754705411663982252129757630450911995848106$ |
| 19 | $3279667663056360171481292609198642482987658178660517772535122390201115522067980247/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $461403355091680181300724555048441115571821993530250938779917645667784728522067980247/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-458123687428623821129213025490232823370003339939734254025063243762637485$ | $458123687428623821129243262439242473088834335351590421007382523277583613$ |
| 20 | $28593627557018563925537589278923538181214771587002548751649412027590175692490178935/509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344$ | $791014157404234713238655299486556965205863693287095983981923001406577501442490178935/509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344$ | $-3049682119388864597252340321056993610805226264340069653157463941979607845$ | $3049682119388864597252470840830533708098595686800373740921094357515949303$ |
| 21 | $61573559585213321312189250447674329218059371841143093045842938717353110025286525/63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168$ | $1663663441531891477126890829433668136886386695196903826550704852776962110025286525/63657374260452690195888927762793067532858387302060507832379389042324415617604272068231168$ | $-51266876222293700986070450527551801845386474347384343472155581249907488$ | $51266876222293700986068093619947303989796072351000365469046662375940990$ |

| Quantity | Lower integer | Upper integer |
| --- | --- | --- |
| lambda | $9220992843099234662135211792716178507707167848541756924617999884103072724605118404349863531$ | $9220992843103308734087880764888715399083986604863859861405331756604345005503827166949390205$ |
| s | $254552260093450615087745071181253967864442765747242165183476416580986963019125235267070826$ | $254552260096848169034614998585388697578158291295406505299754244448315497464494845343357898$ |
| T | $203009296513502221395964749012707107660363866807869699476711934124489750879114748072149942$ | $203009296576744680423993979498802066115230799428664642561838563423656727197608155352441195$ |
| k | $1902658797491144843531682233980752123403840373463728534059268100945280974386011375031233946$ | $1902658797516539966342184561747760210524731004462738675595505454827106568700354939223124175$ |
| minor | $19541639003240435032128042375771644312609930571391815614992049112920187265632199552041250$ | $19541639267939614319298452596280731233669897749430466046487525158343667697786145772811816$ |
| signed height 0 | $28398704591408350384749511236005103817234561751248369878746862291677709974491047928189786$ | $28398704591603081857911825244713338350638902682245164817965616336047862453467293458679135$ |
| signed height 1 | $10329855392387444646297074360399215127849751286518986345529479897177302847911040403993478$ | $10329855392575306433480466234666375187090127639066709845001242391129916546108832294162334$ |
| signed height 2 | $6645262691672502452939056169220994227633662613811279600781099785496404649432833639001381$ | $6645262691785719183598234934642861095385481323248244963197999377029427446500242528872205$ |
| signed height 3 | $753248028908779913708405052760650093579208397471370137420926221665194241750580906344550494$ | $753248028932515438301291666659444847960078632803863946962295086919984688917825909097032429$ |
| signed height 4 | $3922873535020561205551277741211711849983728853381744336396132760137141233961990361292712204$ | $3922873535044848775003352432450421325008177336112630955895783700476659791272969343772469660$ |
| signed height 5 | $13812633694968772926828944914219121819340986161779412867082042780403523692952510598440509$ | $13812633695081004925100515312597390413215682910966273861163231067930027136788199604531099$ |
| signed height 6 | $1029428681763467782449436298672401527454961905344811873233687312257421530710796766949471559$ | $1029428681792731545201162031906212685102934484181165865776138664534576149020613013082359182$ |
| angular curvature 0 | $852359734361588153234589437406124379023882402159137285444504663773430034592318678116906096$ | $852359734410293664977312736254823453789108717036833078613054872639103600941783785277281700$ |
| angular curvature 1 | $1056914400676878103169000311865919866169692850100759985819208081443284592388211542180767515$ | $1056914400729274939809778377260479169983237155093614450039776289446872393334341109713615116$ |
| angular curvature 2 | $965676964788958342815694825277465040335336833247234630999830282228079493430648446091337424$ | $965676964838159761342504551885627612317206160338964084091557785610407880233797656179165135$ |
| angular curvature 3 | $28827447043736760439142328002696807708008129212911009031491153015927362764124774466619216677$ | $28827447044292811885165517950654787345528555556153810896888831551690681310774794609671985127$ |
| angular curvature 4 | $14702149897089154061735181298148500939114221866252445655175479170454635300938270796896304889$ | $14702149897262146381185215638196271466690210965448621970540737966824796341691159789591814144$ |
| angular curvature 5 | $852359734361619634648552312166851545264259400152166048945494840297228622755887706438900022$ | $852359734410262183563349246869628413371843413059576476638140120193582354599546659841104362$ |
| angular curvature 6 | $14675537948582054478381408262099374072853224349497993496528989316377978760153579701173325524$ | $14675537949203026811643638735042968619536515980445725003119408821838024097580621967659808897$ |


### 13.2 Root $8$

| Row | $q_i$ upper bound | Inclusion upper bound | $(RF(c))_i$ lower integer | $(RF(c))_i$ upper integer |
| --- | --- | --- | --- | --- |
| 0 | $460428978104731592334004698568562616540071893188344376490865597697905808916500631/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $2075481488785645662696542087952481524242462291567998578944911464122837808916500631/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-1615052510680914070362447172595197274951500287377575751312646988478342$ | $1615052510680914070362537389383918907702390398379654202454045866424932$ |
| 1 | $97512315813987547901276029459259287214792493925390184515364814479702197510731101/509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344$ | $438850581361391068671698120710599423436411693610855977771964090419469447510731101/509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344$ | $-1365353062189614083081688365005360544886476798741863173026397103759069$ | $1365353062189614083081612966848281790355348880306913764192855514445222$ |
| 2 | $429269247641071085391032750654219604644736430410545495413958711177821196488832209/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $1924601967311994882649582303836789450131501413339853225995893053786732196488832209/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-1495332719670923797258464579017154818909399204889012905079661700798275$ | $1495332719670923797258549553182569845486764982929307730581934342608911$ |
| 3 | $61430410072312643361904087423091103872108485709787482469656433283560378704795967/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $5844873148836449488464068786260269078624736913389917268209448042460345378704795967/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-5783442738764136845101765598540137325808265763537649138601398684958239$ | $5783442738764136845102164698837177974752628427680129785739791609176785$ |
| 4 | $40288777414963353292658977230191423172985812487397951076217987679961072587449171/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $6005782757056267368619174725677452380096872103631731783595193408087859572587449171/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $-11930987959282608030653007501322193243676583905188337442919219793155255$ | $11930987959282608030653031496894521913847772582288667665037950840815797$ |
| 5 | $479620098771318339236247252216254176093953054333776322755271805247873616601015947/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $2109159075420017263790738709417601402150888057029989996661102542718965616601015947/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-1629538976648698924554491457201347226056935002696213673905830737471092$ | $1629538976648698924554400863862356705694396707822330617642065739233821$ |
| 6 | $113595830893327245862898207705026563322078126870859834124906938424341925781352213/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $13643682513137115966510777315121179796046033358094876807042095841169159925781352213/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-13530086682243788720647879107416153232723955231224016972917188902744818$ | $13530086682243788720647792304989259057443035519667650540973780578081657$ |
| 7 | $628866308691382717912105686774867573476949811018243773110282002222049765163256477/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $4892923006923520055604612498428153712128320941214473109075451440302138765163256477/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-4264056698232137337692506811653286138651371130196229335965169438080089$ | $4264056698232137337692234543813930342507575191426357579415480006181691$ |
| 8 | $270580103824159772704276539684764632148992560874502073512531450524974002535977979/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $1938895579591571896349785388888337401432335799342815426507010691493090002535977979/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $-3336630951534824247291017698407145538566686476936626705988958481936232$ | $3336630951534824247290876932625162610873469396855814432714135407581587$ |
| 9 | $730959331703411000744096948261354618073593283234318774486032983949099422322589055/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $7552952406152482041861316157964744030023740931386528790281597141708337422322589055/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-6821993074449071041116899014637074341982943064923965551633693587866978$ | $6821993074449071041117219209703389411950147648152210015795564157759238$ |
| 10 | $120186645688824006980267646497063398256557623904428548111618637281796408106497621/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $3330128240588875613522852035959013340783940130890589807827482004845361408106497621/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-3209941594900051606542393788847464740997604868659990890119160959298539$ | $3209941594900051606542584389461949942527382506986161259715863367563565$ |
| 11 | $93066731563106093346450883267267252122905451422587489984162028982025208654245003/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $2019119590524058454103578842812122190451041808046446128476958762470094208654245003/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-1926052858960952360756849413432239536109993593778693903813005796192996$ | $1926052858960952360757127959544854938328136356623858638492796733488069$ |
| 12 | $637825813551865637024982258424329521611602281005108846420234717358895722982983787/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $3235461602311083364996302439036335232895225878170837246009496211111253722982983787/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-2597635788759217727971129726268060760954652066739743281871640769136451$ | $2597635788759217727971320180612005711283623597165728399589261493752358$ |
| 13 | $246152502256336479664097764398050809093533283980988190519341009525111958944508951/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $5491289095637675069824436055845975013441375257843887565232501058401237958944508951/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-5245136593381338590160338291447924204347841973862899374713160048876126$ | $5245136593381338590160113981024403453915400627596170968693174367072303$ |
| 14 | $454625513013976006441302891279192971971222989510352483664402805843518860109717939/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $2524289711209218437479415932536321393843290411326916224037320496549735860109717939/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-2069664198195242431038113041257128421872067421816563740372917690706217$ | $2069664198195242431037988213107983152510767702243568557973463011948399$ |
| 15 | $28185841762765902625724218175370821553697387397701702292991516156297847319258397/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $51702254791977044269504444027882300721176448543120212019936124732819847319258397/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-23516413029211141643780225852511479167479061145418509726944608576522$ | $23516413029211141643779812235067844370549589377614840903148268771933$ |
| 16 | $87617217426367176494956312241378706780441848969449728494226781359870344178683687/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $156934750220274300179618622814715221632297052442129579977475940187783344178683687/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-69317532793907123684662310573336514851855203472679851483249158827913$ | $69317532793907123684662127486792790267575285096401091702326093798700$ |
| 17 | $250111250208309668199144422876975456505566761971733860442365903547270087980504393/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $1389759075449203398988419076755398856330431465744168927731877072399252087980504393/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $-2279295650481787461578412442274857467516258062647495816591110620683001$ | $2279295650481787461578549307756846799649729407544870134579022337703964$ |
| 18 | $45329030609501409950064219637226910663150090938901207969619480128578499307217407/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $78996592755229673755414461382141439939970780286557724499171044905627999307217407/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $-67335124291456527610700483489829058553641378695313033059103129554099$ | $67335124291456527610699014047564281277173948453873572587855002370105$ |
| 19 | $18165144550708527499370304391677148668488354135053936123724016183790060140488645/3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448$ | $1047778657952352565880846935554618944363103361795435951481690433860842146077988645/3978585891278293137243057985174566720803649206378781739523711815145275976100267004264448$ | $-527162118861641747651316035155426199395642883922115591863278805850650668$ | $527162118861641747651243346334285493061200661306075766092598839671192212$ |
| 20 | $12489256049627918372131468772067323478156423885670980517812821363039967378326754723/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $758424480685647766794207805405165302536302151892404270774846847777926257378326754723/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $-745935224636019848422001030110242756939883276437152681431770402711352567$ | $745935224636019848422076336633097979058145728006733290257034026414886290$ |
| 21 | $382752061209926950327409962499248252214938451259331468540582935533723682866892675/254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672$ | $57902362473003362306762859237208157532556107013994726133217866110277354307866892675/254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672$ | $-460156883294347482851453408308413054989125424890629015151503144610445901$ | $460156883294347482851483594197671274242729348501883157317418265397949045$ |

| Quantity | Lower integer | Upper integer |
| --- | --- | --- |
| lambda | $9370365491138635996834850166683139540836754610863306752926246067030153978911348848443627929$ | $9370365491138635996834850166683139540836754610863306752926246067030153978911348848443627930$ |
| s | $254559269721328772821783949725269505474738585131493994279138906650553064196969486888034235$ | $254559269725068179976966527367962712666291880406779799066615522769532032083198920995431082$ |
| T | $202889755706536974515425718527478338017689907691381092315886140308081600441311561368117280$ | $202889755774684809621572782620517734844784465138783590173972152645085470159767437597027537$ |
| k | $1902711191173073339383996262106195397060185145000678074798746302810419904967305644010875249$ | $1902711191201023654648919725888975137226861030742307857280234402889646433931332358749146190$ |
| minor | $19493429825419799641957318148116252344448806272675031774649782228585700491119592641736028$ | $19493430088909512130857160440348768600126566533842183051897521542898407572012104702034561$ |
| signed height 0 | $28406087954817414913276573968513896558687523465072931172026448301057851756234742394572256$ | $28406087955012225544111823586350813637559371157660902762235491165966973862072579965642769$ |
| signed height 1 | $10325052317898135862119211799740563715754563018850059519528331843831432014617488535375601$ | $10325052318085964155057871570347599222025414772561643647880611169498048264768238708543309$ |
| signed height 2 | $6647029426528354407500598371779999887605224512042813652436417263170589489570547357145841$ | $6647029426641574574329807186334745102285441389148356089759879803111939087441697605286005$ |
| signed height 3 | $751241333610246751416593046390185207638590233123004252244868503747268833243574161729141365$ | $751241333633955844719924943591140731600256047578959604300427003368907744237230979823287961$ |
| signed height 4 | $3924562614103572096524010884694544551041854696282942063845249369231473565777575800658444665$ | $3924562614127909041176030549199172549185178635271582823439350760743934421447020350387248067$ |
| signed height 5 | $13808758324157631643521199553548562136178668762533545165904304448889194476241329572285465$ | $13808758324269869615768966387734306065600847800794094292880994009807193436014876493919245$ |
| signed height 6 | $1022192445720387866006247262646801742113248679017226956234394208209372876838713436658616936$ | $1022192445749557714769309392362897309926812434267430975643295860215863105296275457062820291$ |
| angular curvature 0 | $867600116034373211060683546963730966010426034815617210125424212719450662955868436672213823$ | $867600116083409713923473890007125077743104903429027066619018160215579799522321916962464177$ |
| angular curvature 1 | $1072222397214384649098103824780949718388535821207245242550201722067750323623632812379299912$ | $1072222397267063759049114505501877306450513686309233938884848044332999571166764299439348290$ |
| angular curvature 2 | $980757074999649645334959843524750436598009509973472944116475869930401907972516691055568402$ | $980757075049174021947387572247814279912057359485378402213721184680554841808831520824223251$ |
| angular curvature 3 | $28816855383294285779441720604444678812892886679980235136372375214643151654288786933820059947$ | $28816855383840462286383659624925644393891738661005943131398334223581672457630692699495376142$ |
| angular curvature 4 | $14857477394521836432107682166829407275671831339609879294730907732753154096995347233556200811$ | $14857477394692304768444130970924394613374079141602235229481120401934847225488253932418939009$ |
| angular curvature 5 | $867600116034402118305114000455886529015070864933102122732462470811260202332018499463811687$ | $867600116083380806679042863101715645304642647577402891700588986571258527428106880611057160$ |
| angular curvature 6 | $14830558481501609780209392026476377797973608529826752795255455792184441278230761532072617574$ | $14830558482117911890958911322582601828347248402062853583556844736891452358565499157195452538$ |


## 14. Full contact-factor and Bernstein interval certificates

**Definition 14.1 (coefficient and control tables).** Cases are ordered lexicographically in $(\eta,\epsilon,\sigma)$ with the signs $-1,+1$. The polynomial in each case is precisely the cleared gap from Theorem 4.1 after its listed exact double factors have been removed. A quotient row $j$ encloses the coefficient of $x^j$. A control row $(d,j,k)$ encloses the $k$th Bernstein control on $y\in[j/2^d,(j+1)/2^d]$ after $x=2y-1$. All coefficient/control endpoints are integers with denominator $2^{300}$. The rational partition endpoints below certify the complete covering, including endpoints. No unlisted leaf or sampled-angle convention is implicit.


### 14.1.1 Root $S$, case $(0,-1,-1)$

Factored contact indices: $2$. Quotient degree: $2$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $635278186897448588011391793847592102925848336000622669406794450868043382866696168873949170$ | $635278186953631374185023795674526660126774628523781635860027131511110853026962881347439806$ |
| 1 | $5587023852615385895113293504387498449670932707827629301337973507325846815070430076242082687$ | $5587023852710657878016622188187877896186761695321170247250315872539607271402530836457025797$ |
| 2 | $18491177934580841626311891486036454214832013927191311851910040197763835466181125853210342186$ | $18491177934597137914122581420842709645105112467835094991153054665075129345051435865684966940$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 2 | 0 | $0$ | $1/4$ |
| 3 | 2 | $1/4$ | $3/8$ |
| 4 | 6 | $3/8$ | $7/16$ |
| 4 | 7 | $7/16$ | $1/2$ |
| 1 | 1 | $1/2$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 2 | 0 | 0 | $13539432268767632336306661091696168421571100567870764274066518776092271577645291185627265559$ | $13539432268935383393194311712129737855560954388531247325675108289260393383007968670790324059$ |
| 2 | 0 | 1 | $5690599264622909853023693757371688211436277510910124103824484820386168608887180771845302760$ | $5690599264822627049542521516158480222191637848765883961532667158513377467768038453299409416$ |
| 2 | 0 | 2 | $2464560744123397776318699294556321555009457935747311896559960914121024506674351821365925508$ | $2464560744359155184421376675397900000098599425959294345178489694035143888790967202229736508$ |
| 3 | 2 | 0 | $2464560744123397776318699294556321555009457935747311896559960914121024506674351821365925508$ | $2464560744359155184421376675397900000098599425959294345178489694035143888790967202229736508$ |
| 3 | 2 | 1 | $851541483873641737966202063148638226796048148165905792927698960988452455567937346126236882$ | $851541484127419251860804255017609889052080214555999537001400961796027099302431576694900054$ |
| 3 | 2 | 2 | $394220844535188301258198049618233287009639231033956680039814520216120121097843236712194642$ | $394220844808004438932893173439989130824630532392398165771378146124105893879610692765374033$ |
| 4 | 6 | 0 | $394220844535188301258198049618233287009639231033956680039814520216120121097843236712194642$ | $394220844808004438932893173439989130824630532392398165771378146124105893879610692765374033$ |
| 4 | 6 | 1 | $165560524865961582904196042853030817116434772467982123595872299829953953862796182005173522$ | $165560525148297032468937632651178751710905691310597480156366738288145291168200250800611023$ |
| 4 | 6 | 2 | $225824860424560514961317340557147944329980531514371814838024457533847715786829218754563999$ | $225824860716669905913147426563035710801948232538720153778121809593983584473218494237175621$ |
| 4 | 7 | 0 | $225824860424560514961317340557147944329980531514371814838024457533847715786829218754563999$ | $225824860716669905913147426563035710801948232538720153778121809593983584473218494237175621$ |
| 4 | 7 | 1 | $286089195983159447018438638261265071543526290560761506080176615237741477710862255503954477$ | $286089196285042779357357220474892669892990773766842827399876880899821877778236737673740219$ |
| 4 | 7 | 2 | $635278186769584029486683240434701795863822267219515445008423151031695168793975383709756551$ | $635278187081495932709732349087416967188800697304888860258398431347459067099683666511632425$ |
| 1 | 1 | 0 | $635278186769584029486683240434701795863822267219515445008423151031695168793975383709756551$ | $635278187081495932709732349087416967188800697304888860258398431347459067099683666511632425$ |
| 1 | 1 | 1 | $3428790113060980689232640057822195590426190080489546956434395437383324697458880409356173141$ | $3428790113453121159528733377987611345555280085609257123126570834928556581671259097214770077$ |
| 1 | 1 | 2 | $24713479973933218975290488361246143599820571820950890319770407921498789692304911288212931917$ | $24713479974421884300470315827730515369026871941748720377147797903584783441294270393602874669$ |


### 14.1.2 Root $S$, case $(0,-1,1)$

Factored contact indices: $\varnothing$. Quotient degree: $4$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $49192248378298230088798928431560308040859473785695065886708557056417736072180281911088450$ | $49192248394594517899488863237815738313958014429478205129723024367711614942490294385713204$ |
| 1 | $98871358964255766272872089218781684391168810809463073545574512420310712139523800072683749$ | $98871358980552054083619997107729819025852997997096798707226103736068021708716432930627379$ |
| 2 | $-645596463984147471991618382195231911180163911087379825223954742454126833188775434540670172$ | $-645596463967851184180784301064811696777741361428729203521164369665161802275300807714037883$ |
| 3 | $63277754459437753094306155133363681066189648973121180027357484554544904529096685244842358$ | $63277754475734040905054063022311815700873836160754905189009075870302214098289318102785988$ |
| 4 | $18457002316880415860066349401452591121702001638192413365235189005292217569243665585670022820$ | $18457002316896712147877039336258846551975100178836196504478203472603511448113975598144647574$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 2 | 0 | $0$ | $1/4$ |
| 3 | 2 | $1/4$ | $3/8$ |
| 3 | 3 | $3/8$ | $1/2$ |
| 2 | 2 | $1/2$ | $3/4$ |
| 2 | 3 | $3/4$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 2 | 0 | 0 | $17698448987818280523174855887558877883835970366732876902001707640288138236320064682007027731$ | $17698448987899761962228565654079705228053958372054361252513830130331205644112544599498796788$ |
| 2 | 0 | 1 | $8667435023154708373476006114023016622991572837388064277346352867163166141047753816839114767$ | $8667435023256560172293143322174050803264057844039919715486505979717000400788353713703826089$ |
| 2 | 0 | 2 | $4215862065735767289014294500381046169310892991775953138133504429941872043274540873553331327$ | $4215862065864779567515993209063737068968919431220023440261931162948306497998382108134660415$ |
| 2 | 0 | 3 | $2038582255776225681089288196948528318830361734072428958179241815941146540252713173795497794$ | $2038582255941734854167104579036637379196445236200644346972863587984543683777743125773258972$ |
| 2 | 0 | 4 | $984010378295877952254701191631811812692785070840403046626843825308643827312287138315810975$ | $984010378510785247758781654896802997472981122765016637281948879822851171668673584485621442$ |
| 3 | 2 | 0 | $984010378295877952254701191631811812692785070840403046626843825308643827312287138315810975$ | $984010378510785247758781654896802997472981122765016637281948879822851171668673584485621442$ |
| 3 | 2 | 1 | $456724439555704087837407688973453559623996739224390090850644829992392470842074120575967566$ | $456724439795310444554620192826885806611249066047202782436491525742004915614138813841802677$ |
| 3 | 2 | 2 | $210115483935328693192719010844045642640947056226251702174911990518196811892211518905660835$ | $210115484202859418085600157228784942761769529725326773490572388361676235087496403466424890$ |
| 3 | 2 | 3 | $100235359562226068639849405731881654386486772666351794242555156904513624878951385898665383$ | $100235359861352070290759575953006813865335746772292885652022170806507531781525955592738041$ |
| 3 | 2 | 4 | $55233579864184638951397299474679371572615083264243395404434136221722409098403842842779338$ | $55233580199086084936781161757318947206393685234584286724289558515998673983202289634244620$ |
| 3 | 3 | 0 | $55233579864184638951397299474679371572615083264243395404434136221722409098403842842779338$ | $55233580199086084936781161757318947206393685234584286724289558515998673983202289634244620$ |
| 3 | 3 | 1 | $10231800166143209262945193217477088758743393862134996566313115538931193317856299786893293$ | $10231800536820099582802747561631080547451623696875687796556946225489816184878623675751199$ |
| 3 | 3 | 2 | $30108365143162974438910585815236511385460298617818106822427907787031948770021346682116655$ | $30108365553795476669686500446033476126001283574492377779641939199640803894201739632451206$ |
| 3 | 3 | 3 | $43012788223032359251891903105675416164764992250845754523638320036404174751009104816247551$ | $43012788678309899964115133168293661226488632913917524476993222877951505398146456917847131$ |
| 3 | 3 | 4 | $49192248133853912927871748275935763877805113379960082728754116409350095436787764171107634$ | $49192248639038835060416043393440282477012374835213188287677465014779255577882812125693993$ |
| 2 | 2 | 0 | $49192248133853912927871748275935763877805113379960082728754116409350095436787764171107634$ | $49192248639038835060416043393440282477012374835213188287677465014779255577882812125693993$ |
| 2 | 2 | 1 | $61551167955497020279831438616456459303885355638188739138985709155241936808345082880827800$ | $61551168560496705253017863843733524978059858677804515909045949288434755937355522541387718$ |
| 2 | 2 | 2 | $47010235100948803083785240476262926464907307880764117564838838395428556999066006473464716$ | $47010235826812622653108794305572512079252912847877911983746267396158450999994784646885193$ |
| 2 | 2 | 3 | $7546879395029655147593979352490851610052079057623362476791617108327749416696054803591611$ | $7546880267390312015308016099186416805381162305929859704311761372809019815160891192226575$ |
| 2 | 2 | 4 | $1098701175467585961533265318333062866094875880505729453672521471103120905546709846830158138$ | $1098701176517678007336549669060982321679677993189719123793163490290964606939337609811492494$ |
| 2 | 3 | 0 | $1098701175467585961533265318333062866094875880505729453672521471103120905546709846830158138$ | $1098701176517678007336549669060982321679677993189719123793163490290964606939337609811492494$ |
| 2 | 3 | 1 | $2189855471540142267918936657313634880579699681953835544868251325097914061676723638856724665$ | $2189855472767965702657791322022778226553974824073508387882015219209120194063514328430758413$ |
| 2 | 3 | 2 | $4411627419391174028626470596398550984404202513673188482347758254374601181519121174579730824$ | $4411627420827963403938075406152756131576440236383034968339153183068780799496701659123948870$ |
| 2 | 3 | 3 | $8919557093650527628717874798675733808923940587000751245908719684742363656559377072958126267$ | $8919557095333119345174336061287323119270307616256057629886998440942524567795383369525144496$ |
| 2 | 3 | 4 | $18022747213753075444509303764823892930600845215660512650676012354841146476360695052055237069$ | $18022747215724926269605822385779064181657254111007597418777859768940649109023166702152466398$ |


### 14.1.3 Root $S$, case $(0,1,-1)$

Factored contact indices: $1$. Quotient degree: $2$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $630839214626325880918348356614466814300528041645695196107427102081439865185647274014968549$ | $630839214685509959095139209455465073115080415833733170434732476339716853625954279009107909$ |
| 1 | $-6040981718080072644073940421930621743324405386006039547170172331623971087784232331084737995$ | $-6040981717984634691191096436199846240498458167700749099311416176662136216354195419248454975$ |
| 2 | $18451825041478871352089317747479447003032896593809000090607739771698173460000775457123607659$ | $18451825041495167639900007682285702433305995134452783229850754239009467338871085469598232413$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 1 | 0 | $0$ | $1/2$ |
| 4 | 8 | $1/2$ | $9/16$ |
| 4 | 9 | $9/16$ | $5/8$ |
| 3 | 5 | $5/8$ | $3/4$ |
| 2 | 3 | $3/4$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 1 | 0 | 0 | $25123645974089831924198762540293760057831882803155444386026583050441749541540618150387031183$ | $25123645974260750243069087313671789249745480936292555947455659046973155280281272079692078317$ |
| 1 | 0 | 1 | $3651330073554627962261784647042746752863684975699641382590742645620296658777416515246429772$ | $3651330073789561545384221348092419126463355258633181307192211186943913712103398912944243171$ |
| 1 | 0 | 2 | $630839214498295352414124501271180450928383742052838469762642012497017236014990337229436020$ | $630839214813540487599363064798751436487224715426589896779517565924139482796611215794640438$ |
| 4 | 8 | 0 | $630839214498295352414124501271180450928383742052838469762642012497017236014990337229436020$ | $630839214813540487599363064798751436487224715426589896779517565924139482796611215794640438$ |
| 4 | 8 | 1 | $253277857116253776183166983049734663186471087846988105659129433356607308169687064977311801$ | $253277857441537855376255779387042975240208397525765970477930863296667704133262753650940097$ |
| 4 | 8 | 2 | $164026266007319564828605054632655234866947442919403367971362788148981340636895909242743951$ | $164026266342897217526586114011048614513598253600766782142762195653718852639775001969712137$ |
| 4 | 9 | 0 | $164026266007319564828605054632655234866947442919403367971362788148981340636895909242743951$ | $164026266342897217526586114011048614513598253600766782142762195653718852639775001969712137$ |
| 4 | 9 | 1 | $74774674898385353474043126215575806547423797991818630283596142941355373104104753508176102$ | $74774675244256579676916448635054253786988109675767593807593528010770001146287250288484177$ |
| 4 | 9 | 2 | $273832850062558506995876787602862737650289162342499519011575431666513365883825714291164622$ | $273832850418977936200684403294773993580784139726593143438842895352344076822660209069728598$ |
| 3 | 5 | 0 | $273832850062558506995876787602862737650289162342499519011575431666513365883825714291164622$ | $273832850418977936200684403294773993580784139726593143438842895352344076822660209069728598$ |
| 3 | 5 | 1 | $671949200390904814039544110377436599856019891043861296467534009116829351443267635857141663$ | $671949200768420649248220312614213473168376199828244242701341630035492228175406126632217440$ |
| 3 | 5 | 2 | $2223304615811680580588793792369475899751306656858285579586476322298281178252758023493344183$ | $2223304616211311339789506702076509354837592955833194293829512504656732088207594886044595808$ |
| 2 | 3 | 0 | $2223304615811680580588793792369475899751306656858285579586476322298281178252758023493344183$ | $2223304616211311339789506702076509354837592955833194293829512504656732088207594886044595808$ |
| 2 | 3 | 1 | $5326015446653232113687293156353554499541880188487134145824360948661184831871738798765749223$ | $5326015447097092720872079481001101118176026467843094396085854253899211808271972404869352544$ |
| 2 | 3 | 2 | $13041682537864501484808121957207494850090677868568232734714180517948631850490913438319056177$ | $13041682538356666011929654180497118489840958763466190305804884562894058363054121291093667383$ |


### 14.1.4 Root $S$, case $(0,1,1)$

Factored contact indices: $0,5$. Quotient degree: $0$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $18458884131901787219624121360523293177696440999328162854039689229140725531694354857901430783$ | $18458884131918083507434811295329548607969539539971945993282703696452019410564664870376055537$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 0 | 0 | $0$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 0 | 0 | 0 | $18458884131901787219624121360523293177696440999328162854039689229140725531694354857901430783$ | $18458884131918083507434811295329548607969539539971945993282703696452019410564664870376055537$ |


### 14.1.5 Root $S$, case $(1,-1,-1)$

Factored contact indices: $6$. Quotient degree: $6$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $528938695605580792362267748670232920167971864170246080298090200484107230719992563364712678$ | $528938695645342969541313729419793220341397680093078302974945534214263394196384512838771811$ |
| 1 | $2196870752581954024222325153043614555072371916816474249105323114964985791966078920464661335$ | $2196870752626735559625202860720769115541725140381346082786052628647049556445968754401223937$ |
| 2 | $3497920118493873663636989443220889634988761099072664025790412830937219725372291336123721592$ | $3497920118538946656153494153764560927838233413363667234667864959251951933582514171680642299$ |
| 3 | $4952157829493627329721273048033776494594264811233714555114910585034181730179945294759167938$ | $4952157829528057536041665297598353837761267399605310554267798152679912128767932734331010050$ |
| 4 | $5373629697855041725492583917339661433567131733617158472950509364106361597193036517382940602$ | $5373629697866163229519644619012686245743093037872136308649338358888405186290108574153704750$ |
| 5 | $814437459000147775188255770276611553606803208294420333674535319647255777319852761092240310$ | $814437459004954752595587727073053841457906548699796827975451875638866790962707928327001464$ |
| 6 | $852455684443398285702377612173023846771665272448535699007172686111505448919653272378352534$ | $852455684444110155816624266372790541713531034415573343831878426859522751434370953113382544$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 2 | 0 | $0$ | $1/4$ |
| 3 | 2 | $1/4$ | $3/8$ |
| 3 | 3 | $3/8$ | $1/2$ |
| 1 | 1 | $1/2$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 2 | 0 | 0 | $2289478155238146618931762836011631040734630880622150813016882424673365526028364272190491955$ | $2289478155418833881899222797215828332362815229399846052229258259567719966037501235470431821$ |
| 2 | 0 | 1 | $1249514688642843929268605399904247017231227314562184131008413887430794588376155126486072607$ | $1249514688849448714171685893886039311632733505682436531232658862060403413081556087385426874$ |
| 2 | 0 | 2 | $634979313608230875739569363235673260562884796863713289100664451735216429830519848112213399$ | $634979313845317190268721474165668482705133959301439314268592573951422216110617046268816964$ |
| 2 | 0 | 3 | $286827654753984014889609519426493122063473977866600198422542503891397698701024809236408713$ | $286827655026998512977702379651651905471507218401628969850039556055857779319870365248740912$ |
| 2 | 0 | 4 | $104716493655951745963890284666330577766251249897565977678709931360707582364629281865416353$ | $104716493971414704631116992621015167337560754930420211480625128203562205117862335225809380$ |
| 2 | 0 | 5 | $24606390472901638200955021726557875817013002487904392059390793378253845123568912024486426$ | $24606390838645216681471955062305210102530941481662598873017767983792846717357557237984484$ |
| 2 | 0 | 6 | $9683925642695856339995013963206681493057147473203662447167064790511138702608776317501980$ | $9683926068160760460829641869097009052769030552178572664700209909526903717359260967856013$ |
| 3 | 2 | 0 | $9683925642695856339995013963206681493057147473203662447167064790511138702608776317501980$ | $9683926068160760460829641869097009052769030552178572664700209909526903717359260967856013$ |
| 3 | 2 | 1 | $2222693227592965409515010081531084331079219965853297641055200496639785492128708464009757$ | $2222693682918532350508485272492908527888075087436559560541430872393932217360112832791778$ |
| 3 | 2 | 2 | $11058370400701155954528819993960864075421890557243146836717188551446189986673699144003904$ | $11058370888247562172438009767264247049324095252512943056205102371636814567487585127151649$ |
| 3 | 2 | 3 | $31589279716753198567435354119999978885747398226821737644475775810739683651839382932969803$ | $31589280239081688843126012215107896527870997609510528231376566221377700717617081561259350$ |
| 3 | 2 | 4 | $60915369997925276059424017915693600492436827098056001155426078856040028417129483817557393$ | $60915370557816705021552522784284980967267368714467925223542055293471231016763920135727834$ |
| 3 | 2 | 5 | $97554536386842465507576867311219087478432654097797578479147950989503301378994973213085567$ | $97554536987317664320405350986917960185871036969126362812856540366389367325021468094811665$ |
| 3 | 2 | 6 | $141367059463169034336566071182698888211172035207555508067308772247917971263863377705748315$ | $141367060107511176348325549750070133104181664510395616592908031668163724797236183850734349$ |
| 3 | 3 | 0 | $141367059463169034336566071182698888211172035207555508067308772247917971263863377705748315$ | $141367060107511176348325549750070133104181664510395616592908031668163724797236183850734349$ |
| 3 | 3 | 1 | $185179582539495603165555275054178688943911416317313437655469593506332641148731782198411063$ | $185179583227704688376245748513222306022492292051664870372959522969938082269450899606657032$ |
| 3 | 3 | 2 | $236165462303231551375380833401612803423394351537087719508069363889698707956603101788208384$ | $236165463038590753133233317836893672640509878879544940343748020500568660905622783159418567$ |
| 3 | 3 | 3 | $294184979334041146390714915101123680017057996848387392076775463434804640413904863061334268$ | $294184980120095980227929310648147531878734087130945602098861534488087075860598292921242459$ |
| 3 | 3 | 4 | $360440799648627845983819801974778856876834187287378891155342798913071298877041147774857797$ | $360440800489208535264928023288988021759806412677945178045321114610084595583976978472321153$ |
| 3 | 3 | 5 | $437402413817324594356245351262403864871082723196158737203216593844548011795421900598929292$ | $437402414716570434887022459587439622696032777017256465574345151536654473603786522485143363$ |
| 3 | 3 | 6 | $528938695144268932255121765127617060166615395065932603455025601530978843934482386583688195$ | $528938696106654829648459712962409080342754149197391779818010133167391780981894689619796347$ |
| 1 | 1 | 0 | $528938695144268932255121765127617060166615395065932603455025601530978843934482386583688195$ | $528938696106654829648459712962409080342754149197391779818010133167391780981894689619796347$ |
| 1 | 1 | 1 | $895083820452046283850627420588469841348746082545028068462261632276702172490724330522723808$ | $895083821666992408694208726462286910929639637917933036792670059690341010494327358158408282$ |
| 1 | 1 | 2 | $1494423620291785067869346909290733619351422945400027856732461067101691408577842005032757963$ | $1494423621830889909969442813186450448884445252091658721201585101479969109739537996646312596$ |
| 1 | 1 | 3 | $2574565986128287892127613169705983188850600575068095055281864117317566697183692373322715038$ | $2574565988084628968945975951944931416148993010823357001497650484110360626677063543329093809$ |
| 1 | 1 | 4 | $4741360789280334080110327440796756620925943041158335861573694618349800680198614415878735050$ | $4741360791775261502427869056813621436882077106478492587793434323908065397929501925277563830$ |
| 1 | 1 | 5 | $9094639457419992430054755236196223827053425330867165327639210175597577156787353576577850361$ | $9094639460612147370764941252512881039310980758100210514681792014639926983124347727177292209$ |
| 1 | 1 | 6 | $18216410235515332259736699930560878969869600060842208803205924996405155192680639481180014909$ | $18216410239612602195882905416158939199296524099241913267888359041060433850670198813231518935$ |


### 14.1.6 Root $S$, case $(1,-1,1)$

Factored contact indices: $4$. Quotient degree: $6$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $534418110431942276405733368249976059218286067825967174988653794965264119772385654944771470$ | $534418110473939197039502053929434917152817523434042326750013425232826869540868913717206540$ |
| 1 | $-2193212107391255907395984710324944682432622082346642214289023411975768364805849137118970109$ | $-2193212107343596935047983144951382283816929085549792728210487811551037843383910524881523529$ |
| 2 | $3504164138897509829043983128597666636127645755929016709310800614806053046405715673729325826$ | $3504164138945652603184657195137575530523679876500240590383940319198243212218599459368939071$ |
| 3 | $-4956642471975103745066353797405350145461509889345106640210753449054752339843346513173512520$ | $-4956642471938360407007890143516096237746316586387305640748985400970331030094396466641941812$ |
| 4 | $5368523845897076809397315474218920449756691655899240121884927469665823991281366044003981428$ | $5368523845908695363088814983863641796613545287647049654610346915868939589778067468077532474$ |
| 5 | $-819363547791563528539247261495548938247078663756560989127966913301225844763296652159613178$ | $-819363547786430147637424863769182461728656862420686420578237186397023151746373110360465756$ |
| 6 | $851105553136657711504627202036878147236181870443583460249468624924062373114008903538348170$ | $851105553137369581618873438910011154971112688386747405591528529653180298403036464938096641$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 1 | 0 | $0$ | $1/2$ |
| 2 | 2 | $1/2$ | $3/4$ |
| 2 | 3 | $3/4$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 1 | 0 | 0 | $18227429775431574116044957325340102275630707884455592255971560903279595555798156378100357991$ | $18227429775623579925933433441066507165402366011416389820963572964284936519353064608553870533$ |
| 1 | 0 | 1 | $9102594068327459293756774430472014777733914200609937037084967935706682025444813125081331074$ | $9102594068574562916106138564293529288669313925594450417462447496907116021183078871668146530$ |
| 1 | 0 | 2 | $4747455254890625741828271740450892271419523325520747849691156493036645641661534271686232151$ | $4747455255212166908051655866796626975511392388691489641550047312155035569286130288317239404$ |
| 1 | 0 | 3 | $2579689115307427854499871498975953265997098686926331530702007533339167648715854207622975873$ | $2579689115730185734216788112634741945989436938554367516273350427924439864914030367649674723$ |
| 1 | 0 | 4 | $1499099755222826240688919137987616601905717314208756525597278199718054313990198332524912396$ | $1499099755784217009052881590866252840991991708512015110287542157255925161961263799010447919$ |
| 1 | 0 | 5 | $899953461304424220947601961841565472701677372714345317978412138441185655451630482319461903$ | $899953462057266059571628102883899998044351413195070007510173619011373035226584030009265159$ |
| 1 | 0 | 6 | $534418109943162035925495033519689594282387568517750319371818441994526542235609259135097261$ | $534418110962719437519740388659721382088716022742259182366848778203564447077645309526880859$ |
| 2 | 2 | 0 | $534418109943162035925495033519689594282387568517750319371818441994526542235609259135097261$ | $534418110962719437519740388659721382088716022742259182366848778203564447077645309526880859$ |
| 2 | 2 | 1 | $351650434262530943414441569358751655072742666419452820068521593771196985627598647542914940$ | $351650435415446126493796531547632074110898327515853769795186357799660153003175949285688709$ |
| 2 | 2 | 2 | $227285494221184809583190667153857528559285298645609373018292836755419815350224692706004082$ | $227285495526273897325194117875086322881081858505481926632034861754941743575141851174196175$ |
| 2 | 2 | 3 | $130344274367991164512939209777743429229191553455551529661933307507940640045419719890423795$ | $130344275846876068982272240138588874017041611978484524680594785696006839089499796302497558$ |
| 2 | 2 | 4 | $52216608609526095790970815017283479215956927904131461935554482978135371553140727249798981$ | $52216610287074786979308799495850574850109162671458022650819928133884271565262865860127675$ |
| 2 | 2 | 5 | $2393661731970942525110394517581651087642871740599333826930647474448071804611771134913543$ | $2393663636808945631979112835942622262052497359203931010845110474334524327770192460009908$ |
| 2 | 2 | 6 | $17498935190769266100438512757889931685688673033161664498249306899267274295472740521090282$ | $17498937355873510025609417332419734818379484179721205050781530303981113754504156247062006$ |
| 2 | 3 | 0 | $17498935190769266100438512757889931685688673033161664498249306899267274295472740521090282$ | $17498937355873510025609417332419734818379484179721205050781530303981113754504156247062006$ |
| 2 | 3 | 1 | $32604208649567589675766630998198212283734474325723995169567966324086476786333709907267021$ | $32604211074938074419239721828896847374706471000238479090717950133627703181238120034114104$ |
| 2 | 3 | 2 | $112637702444719390092283287978516601608140133074380784620829120677412181516584604794505937$ | $112637705163333044553830017481759025075417109953527118810565607452470629272198721008336067$ |
| 2 | 3 | 3 | $294222918031668228735069048178097086500344937347338552014220275861632921981865314158129833$ | $294222921080853385514706541464560986486019269177586079500435699847133408404868339314645646$ |
| 2 | 3 | 4 | $641115693535119889266460128910339668075166013531760171686342159373081703242231559598000409$ | $641115696957150133156846451235340971855760698173611761272415801085102590008872602629954962$ |
| 2 | 3 | 5 | $1253235209538699348382762759298710525559610211958323236270959134536912323395303669765898163$ | $1253235213381469716073131329089743915250932497130990402124365214400859138311797582271776312$ |
| 2 | 3 | 6 | $2288993519142368023313227339284486401182251334251459411388147562006414169629321743910688977$ | $2288993523460164677275395584197113540984596222008333399216077959057840756247554434071485739$ |


### 14.1.7 Root $S$, case $(1,1,-1)$

Factored contact indices: $\varnothing$. Quotient degree: $8$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $122616553924813453626047053016152578355770111325932687984762551169783644673216372385207754$ | $122616553925525323740293289889285586090700929269096633326822455898901569962243933784956225$ |
| 1 | $-1043157987780053634298375071781064286641458047945058669537835944287752417258672983266569389$ | $-1043157987779341764183194960251675763385254145480904669316247941114615383251051355975052687$ |
| 2 | $2066506192872044456048050896091260970744456649011252359951217817729889827182370481724518674$ | $2066506192877086917179456892979858850231382419947586736201215186048381030286361488572444016$ |
| 3 | $88891711181659038232838180879364322555729277682667646818298312304456152218770690840144128$ | $88891711186570268734280067833002052983574708338070049498762435014864547312276665275062294$ |
| 4 | $2555690509451078975769239837757337836208384544954152424442485289536684198984361720709737700$ | $2555690509456121436905751650848712329086777522439074600494881427009502266112080639266749365$ |
| 5 | $-74027723626019127823090781057503310815636039981253364409217916951562433094607157436052697$ | $-74027723621107897321651085319633544399955502152695708363242113569946379835579778160841302$ |
| 6 | $7616697844403090471537712308456197926727934481671430224856632016401196220986354650836730145$ | $7616697844408132932669126841579214275691308828819734040863523958200245024009086903507610625$ |
| 7 | $1044882165917267192704961690071725059747224569344394427421484472481864942760776185168489317$ | $1044882165917979062820141688968635869589830708832881128718928256167348419432963083861341253$ |
| 8 | $850901021307430348781636151491748302186498753796823052535605205974815894517942532062962375$ | $850901021308142218895882805691514997128364515763860697360310946722833197032660212797992385$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 1 | 0 | $0$ | $1/2$ |
| 4 | 8 | $1/2$ | $9/16$ |
| 5 | 18 | $9/16$ | $19/32$ |
| 5 | 19 | $19/32$ | $5/8$ |
| 3 | 5 | $5/8$ | $3/4$ |
| 2 | 3 | $3/4$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 1 | 0 | 0 | $13195823956254358035713110535582368999434848771222239949232502244314718582685637142718647090$ | $13195823956282155360574177462876064253382674457138602667954025050332856842776166442623741257$ |
| 1 | 0 | 1 | $5608871959824745943345069724546070861584033463963074542029473908329962536174785635295089140$ | $5608871959866441930636672142069385065446731836183316999366439556512789888173012108656647312$ |
| 1 | 0 | 2 | $2807899325202517172312946126817029344226008594601798741343988287323897087189398216835527721$ | $2807899325265599742644302026889615904850551466613688195278789060543847632867111147847864317$ |
| 1 | 0 | 3 | $1680625948151648702000679188272221833721319328424068988087664270423888954290918334723354897$ | $1680625948247888325679565301709037258072560785395692100943437084647677293294907580263716263$ |
| 1 | 0 | 4 | $1117178759836029408241533374527462861809625362678625416192664340411365961027358717532324539$ | $1117178759984050275169192228410216979110719319938987360055084867024555237141137831599434567$ |
| 1 | 0 | 5 | $733624825050385600189471502048986202940769034801513751077469560141236182129697792765284075$ | $733624825279843575400277754399342918664214264537757123743638641013163822791218863221676706$ |
| 1 | 0 | 6 | $457209843293538228536332809530909089492310738717175343641978844337185744403204817506130985$ | $457209843651975518922811033849539795352832602697160494388571169931315379554998429556472603$ |
| 1 | 0 | 7 | $253011302115507945267053175106029180213570204620593945859307129100255203126130532333062607$ | $253011302679755256909483421803501490486239860152680792809038363643725986573045316242303818$ |
| 1 | 0 | 8 | $122616553477414543926801036449153219422710951441510886567262257442910309286142680904150415$ | $122616554372924233439539306456284945023760089153518434744322749625774905349317625266013282$ |
| 4 | 8 | 0 | $122616553477414543926801036449153219422710951441510886567262257442910309286142680904150415$ | $122616554372924233439539306456284945023760089153518434744322749625774905349317625266013282$ |
| 4 | 8 | 1 | $106317209897652868759269519117043724323853544794125504155756648485742197556144199475536391$ | $106317210834570355505796292037882876840950117778623139986233297873531020196351663893976965$ |
| 4 | 8 | 2 | $91171050576327707371879056406309290920119283161076033283167083959505111567350193574174807$ | $91171051556613184424293644755399898648829411584123428720562864750500233664607974745969996$ |
| 4 | 8 | 3 | $77181175810238121861397555421783526134004579665272124982379907307582773489658451761897834$ | $77181176835946746452998638804529481035209150359568520509302236443157895874211475989935428$ |
| 4 | 8 | 4 | $64359599437299165325950401920531972699912303432732501960320693640085327659888006986055191$ | $64359600510585778858888937305074558225510293808207272877069183175481960261293772638627924$ |
| 4 | 8 | 5 | $52727208494633919811805956403163856254581378117135258133348276738412758268767553190829620$ | $52727209617758009899467602397147564517607324832641361025356519617615818033331677920620105$ |
| 4 | 8 | 6 | $42314760569395533018021279375763387068060329716256136023672486992420333012244379448944490$ | $42314761744726450469179548982230471943486989544535708693513603125854740968196162424010092$ |
| 4 | 8 | 7 | $33164981122149585058982119497477513692550188103679067472336544836826121790735481073517700$ | $33164982352172029432086485739869003297783717936698973028526544325184860615466830422918888$ |
| 4 | 8 | 8 | $25335873780300230631346416960788858763012663911241464705726699871295986206272279519563029$ | $25335875067620018751063370968655592202557265550406970898734442260975859823361577069769021$ |
| 5 | 18 | 0 | $25335873780300230631346416960788858763012663911241464705726699871295986206272279519563029$ | $25335875067620018751063370968655592202557265550406970898734442260975859823361577069769021$ |
| 5 | 18 | 1 | $21421320109375553417528565692444531298243901815022663322421777388530918414040678742585693$ | $21421321425344013410551813583048886654944039357260969833838391228871359427308950393194087$ |
| 5 | 18 | 2 | $17836934464800024586561578759499508444968294073838728385298379203281869531070502170976387$ | $17836935810068610659057743315229195494950017969501152152741079380882078921412343378604488$ |
| 5 | 18 | 3 | $14589967299999163475527698686014118032556054516669336422654786515507072257615677486611833$ | $14589968675234469491940529952520572925332670829786994963984894097679228661698992920053039$ |
| 5 | 18 | 4 | $11688623953825900332901179966882167520549939519885006486873219847973996275281034005237245$ | $11688625359710020348235371383437492575563550227557172858696784536207990960361029091486402$ |
| 5 | 18 | 5 | $9142168097230143261265273548464473242434253534823515500248265268762004168808075173388248$ | $9142169534461040895940682842715565003852592601133414982891893978177916695972026934003791$ |
| 5 | 18 | 6 | $6961044132585279150723016234733095620525187042721544075089163827572467829077838702651034$ | $6961045601877166032876134825471766871613704542875033069838692562446348678791295444143514$ |
| 5 | 18 | 7 | $5157019428464448019771428552887442306934798824778603488072234441662246866627339902272490$ | $5157020930548171525847769573218045631538551791234689865572620653065193458057072932595711$ |
| 5 | 18 | 8 | $3743347470775262657152768435184619303047558017989974963747128770410943637891444444373222$ | $3743349006398703187766415034131383873294312682607227711008815742087036101391651650368202$ |
| 5 | 19 | 0 | $3743347470775262657152768435184619303047558017989974963747128770410943637891444444373222$ | $3743349006398703187766415034131383873294312682607227711008815742087036101391651650368202$ |
| 5 | 19 | 1 | $2329675513086077294534108317481796299160317211201346439422023099159640409155548986473954$ | $2329677082249234849685060495044722115050073573979765556445010831108878744726230368140693$ |
| 5 | 19 | 2 | $1306356301828537700248375763921803604976223815567029977788741142567254914134256871053961$ | $1306357905279292680550716669125119838636748108365184451583472918533719252129610315233477$ |
| 5 | 19 | 3 | $686643322910256663037828706761747221879746968082306803396934560013389509262433770233848$ | $686644961413522493274211504549559633721514622158326737339339496414142691224083742654374$ |
| 5 | 19 | 4 | $485276179573319741889962483316431500527766161538228088669587753000389296872795719007938$ | $485277853911440146871158656160059226947064049696214349507445184803412648015996841728879$ |
| 5 | 19 | 5 | $718643743529004907888763517788710260326113300354554237409272739720597151437781880457294$ | $718645454502160723580371445733735827629353375106877400875048634561586006300874370266007$ |
| 5 | 19 | 6 | $1404968222450947487043018819314085887418674542181706477458236018257385358536856743565638$ | $1404969970877573243935574296509330131079323543951242919933642964920970699180473546177231$ |
| 5 | 19 | 7 | $2564511224735422297605328652961936463627967395908461917416015957430378468761087987891090$ | $2564513011452632819436630544373274123564343307549903509640422634906920962814790105575424$ |
| 5 | 19 | 8 | $4219803100553247352139513563216969076272712129571803697245717557489795041682196922587857$ | $4219804926417274619376294527787607135773983661927836020043542295035637465753893150009215$ |
| 3 | 5 | 0 | $4219803100553247352139513563216969076272712129571803697245717557489795041682196922587857$ | $4219804926417274619376294527787607135773983661927836020043542295035637465753893150009215$ |
| 3 | 5 | 1 | $10840970603824547570276253204237099526851691064225170816564523957727461333366632661374925$ | $10840972586275841819134950461444939184612545079439566061656020935550503477510305327744379$ |
| 3 | 5 | 2 | $25394120083629451691962994070972142560397900077863919373834076932147903028201111446103036$ | $25394122236367724609911330163908495549045035949419646834409939418349629318143301266049099$ |
| 3 | 5 | 3 | $49321193950900312521284251010443351765309436324854970326693096496765107938775797062641440$ | $49321196288848773826441711296748793393204000017466596741387195376469857774857303464035571$ |
| 3 | 5 | 4 | $84644932510852540605996930399996206137012303301505988661853360313825130176728182473457551$ | $84644935050269735098442468180891830053305755673501301440955495464604718326715515972369430$ |
| 3 | 5 | 5 | $134203719200133995154555122192308599331153532545751937615925058642812035977050739375825320$ | $134203721958736150881204211882805121786603421431158934615033419497651759580438807961251997$ |
| 3 | 5 | 6 | $201981765514456304162558159719405465788962998696068897464182736193444823226478232297419289$ | $201981768511551213267213376027294168394078056962304135523447435803871852081183317587082105$ |
| 3 | 5 | 7 | $293555591164187716050634232570311932114488100394823292030454003566200343979948829613048408$ | $293555594420821273072434716053385401146550700798089860395177660365258706380755394512254116$ |
| 3 | 5 | 8 | $416690738714584281013427807646886318965457885813284270915254479121506005829554865401501942$ | $416690742253700917450820072607153438945685322815361975413730807453012304633128393295659073$ |
| 2 | 3 | 0 | $416690738714584281013427807646886318965457885813284270915254479121506005829554865401501942$ | $416690742253700917450820072607153438945685322815361975413730807453012304633128393295659073$ |
| 2 | 3 | 1 | $662961033815377410939014957800035092667397456650206228684855430232117329528766936978409010$ | $662961037919460206207590785714689514543954566849906205450837101628519501137874390862468987$ |
| 2 | 3 | 2 | $1035476616518831153163472116855855548471115762365954523728573214072929217612520762446613737$ | $1035476621279657833257017564932932810328871723610395996075235085909493673453824075862210682$ |
| 2 | 3 | 3 | $1596361827346993909243955020029214251638445188330682352850532777527360930817555014436430238$ | $1596361832871530495830715135430480277513748552111598276754978474465534678812764284766012497$ |
| 2 | 3 | 4 | $2442765372500118909121879839540308872290124512376986525281867191638040618475075016841857638$ | $2442765378913086672568091585688699869405383712899366536230546554093542720081153932388949649$ |
| 2 | 3 | 5 | $3725955192344062014290520658401324245913450921600303693981035791420971762317177124239648966$ | $3725955199790949107180628796072202738556157247615587798046778604552868156816661400386081049$ |
| 2 | 3 | 6 | $5680028336914532622473250667606598866742216484945748552901901063114565466842610755075553432$ | $5680028345565129677922643772163751160949143604825257058108948574587111782072020381473486522$ |
| 2 | 3 | 7 | $8664580073292827843369963740107591447513771165066545743861367266529941906887107380246189213$ | $8664580083345381421324895771677403778444405531312343857189501320242968943488861743222872373$ |
| 2 | 3 | 8 | $13229000281822162264829141301170701820913470463696226056687350988004743367631466481720874816$ | $13229000293508257409189966155973432231172163821940818242161035426732146954400087804234555365$ |


### 14.1.8 Root $S$, case $(1,1,1)$

Factored contact indices: $3$. Quotient degree: $6$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $2551964580350526205791200221888009138916053012795266833963518062679949036089051528042773137$ | $2551964580368998464931304464072609481652227968745440712813695660820692691498587000387587504$ |
| 1 | $1514803247139793484059574461935327090078439503037352628717645919259662175362982806932171509$ | $1514803247167151345921270245801494663239944838701501446298865982275094370101467616069290659$ |
| 2 | $3666049735020745364765170218368321798462363796809698077702522562390500145687957620793155015$ | $3666049735049921270840474442715351929075013381527685139950654897834124246381680588985049131$ |
| 3 | $3433133408419303131864515287496700835316004912849954033131053639882234597789124224769131333$ | $3433133408460750088565285278942991003874938985565206713816589238610154213990683611080915131$ |
| 4 | $8198032928708032129081828470693668209894927962195655166973133187590621197044164502054613983$ | $8198032928719897705753329928673933218933276032879442967354642041511272736973526631747995944$ |
| 5 | $1415887817876654010491621106537192659253381492212435068301612100891643176516244503015958719$ | $1415887817881082326567968326109945216011379259078807343158001277302574796691542276616874809$ |
| 6 | $851179895534683088022015080468211859062723856758582649871143292040443039196961255289271466$ | $851179895535394958136261317341344866797654674701746595213203196769560964485988816689019937$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 0 | 0 | $0$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 0 | 0 | 0 | $8903402666105003026605690140563780123209805545213687225236860606513690037234441402412733002$ | $8903402666238461773245659296834018911810346149754573685181884136902110689671431503092390955$ |
| 0 | 0 | 1 | $124180000634726299472153258209409109084573131835610008243450673524982245147167199487118807$ | $124180000862826930068066933787220966490637985700455545519951622646206583270394520044396086$ |
| 0 | 0 | 2 | $2321935291456745819861503882955060434168455351491846192471024895118851068265196960041082586$ | $2321935291854067387395705729944981726812972498621358496489291953692179697398118850420759309$ |
| 0 | 0 | 3 | $2607181323210402888190614131339132984926901087951036154905400290240238956723605241737158741$ | $2607181323910496376219516904468714450039166725476885130122386498225852675570693799519791777$ |
| 0 | 0 | 4 | $2902475971012763409220050036878286997989508044374202351732688471630774015634396680434480980$ | $2902475972255815954558862109701851513037638975059669029432654745602617571098487464110206108$ |
| 0 | 0 | 5 | $256067238668133954315688630009435838643107777991845302458724553958249416288167872225257892$ | $256067240895030599119538595440106074336934793474369136047209106666990841804945371797761865$ |
| 0 | 0 | 6 | $21631051611097295457119300167997296759339177567330329165781666752534457315961289593984621400$ | $21631051615135638117672518683047805211229152110528446211484614307324070071848673388489186877$ |


### 14.2.1 Root $8$, case $(0,-1,-1)$

Factored contact indices: $2$. Quotient degree: $2$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $642733332783279104940673532754674136555426528035394418082797664639473447085527419485915456$ | $642733332839748042328371070528283739058106040212340022308801383603837106276604014911214202$ |
| 1 | $5682227405628543905631079625589554339197371007034121582679015761459285887728399673021005047$ | $5682227405723761030282078112915466862530712636780478417180422349064647822070242604460330955$ |
| 2 | $18790115781626441272104670831392815197672892852453219281179533249235405907599226755032140278$ | $18790115781638663487962691794026533736569172636774899483635215844045427505570828004907238359$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 2 | 0 | $0$ | $1/4$ |
| 3 | 2 | $1/4$ | $3/8$ |
| 4 | 6 | $3/8$ | $7/16$ |
| 4 | 7 | $7/16$ | $1/2$ |
| 1 | 1 | $1/2$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 2 | 0 | 0 | $13750621708685959346763266251232022471697606743708135282081908564810231532614511570057724779$ | $13750621708849867624659983238965263136429907669953117923265001466189978724119032346797447514$ |
| 2 | 0 | 1 | $5776120669273763579189690260616144188212363177079215935934054583152339251761197485859356861$ | $5776120669467587246178167351497722253226139402921627886970340428838437725836979620396460114$ |
| 2 | 0 | 2 | $2499148575268178129642281977848469704145342823563601410081083913803298447807690090419024012$ | $2499148575494972739687024412536814804164664295083862721584483352498253603947633895222282304$ |
| 3 | 2 | 0 | $2499148575268178129642281977848469704145342823563601410081083913803298447807690090419024012$ | $2499148575494972739687024412536814804164664295083862721584483352498253603947633895222282304$ |
| 3 | 2 | 1 | $860662528265385404868577836464632462111832646805794147154598579128778045830936392698857588$ | $860662528508665486441452943056361079633926741164980138891554814328161543002961032635193399$ |
| 3 | 2 | 2 | $396558717614245259601415622042846169932878273326313089301834072531470513079134367168199931$ | $396558717874774701193549710702565713638762477044528773925827266410908701156464920354806892$ |
| 4 | 6 | 0 | $396558717614245259601415622042846169932878273326313089301834072531470513079134367168199931$ | $396558717874774701193549710702565713638762477044528773925827266410908701156464920354806892$ |
| 4 | 6 | 1 | $164506812288675186967834514831953023843401086586572560375451819232816746703233354402871102$ | $164506812557829308569598094525668030641180344984303091442963492452282280233216864214613638$ |
| 4 | 6 | 2 | $226050466051018259210888889361572615217562850666413582717499772953466197633570259684919465$ | $226050466328988032945063537630434937277491535373685213391899966056865664084512995651095984$ |
| 4 | 7 | 0 | $226050466051018259210888889361572615217562850666413582717499772953466197633570259684919465$ | $226050466328988032945063537630434937277491535373685213391899966056865664084512995651095984$ |
| 4 | 7 | 1 | $287594119813361331453943263891192206591724614746254605059547726674115648563907164966967829$ | $287594120100146757320528980735201843913802725763067335340836439661449047935809127087578329$ |
| 4 | 7 | 2 | $642733332663617548573633120161324535429525329645677178670025887414068316800481988296393385$ | $642733332959409598695411483121633340184007238602057261721573160829242236561649446100736273$ |
| 1 | 1 | 0 | $642733332663617548573633120161324535429525329645677178670025887414068316800481988296393385$ | $642733332959409598695411483121633340184007238602057261721573160829242236561649446100736273$ |
| 1 | 1 | 1 | $3483847035465667285531151970322383166131931048841057767553851173333689662693080574931797828$ | $3483847035833512329694471502213085310345643341313976672767466930171587745568371998205999831$ |
| 1 | 1 | 2 | $25115076519894158294593341651876256994507229620489657637617209708488716916184905916599342549$ | $25115076520346278548656223315331071017076452080800795567448576543559360760145922555218501748$ |


### 14.2.2 Root $8$, case $(0,-1,1)$

Factored contact indices: $\varnothing$. Quotient degree: $4$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $49384799349169278434970498026536115999383630726605775327041115175097949776529058144884419$ | $49384799361391494292991460660254654895663415048285977782723709985119547748130308019982500$ |
| 1 | $98873033369338073007591817342508659361107105674422234631473532325849633312497080708824975$ | $98873033385634360818339725231456793995791292862055959793125123641606942881689713566768605$ |
| 2 | $-660837494689552348341452231640136506885712515314394427415991416497231703529301318438398674$ | $-660837494673256060530618150509716292483289965655743805713201043708266672615826691611766383$ |
| 3 | $63279346371549936277100452875487103294042791449144189941154728893960299509561879652005396$ | $63279346387846224087848360764435237928726978636777915102806320209717609078754512509949026$ |
| 4 | $18755941113088083684103659830481376842811973686426772918970881327975613458318111247112182691$ | $18755941113100305899961680793115095381708253470748453121426563922785635056289712496987280772$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 2 | 0 | $0$ | $1/4$ |
| 3 | 2 | $1/4$ | $3/8$ |
| 3 | 3 | $3/8$ | $1/2$ |
| 2 | 2 | $1/2$ | $3/4$ |
| 2 | 3 | $3/4$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 2 | 0 | 0 | $17982336037974220029290990010871884420001126530340150391985999582802155152604894760741950805$ | $17982336038047553324439361833047637981465477023017428868923458327842677998599957153034666518$ |
| 2 | 0 | 1 | $8805663739152879579672665798937887048423226721382591633257885097212370609094143025109357160$ | $8805663739244546198608130576657579000253664837229189729429708528513024166587971015475251802$ |
| 2 | 0 | 2 | $4282531904693014591888381656543673795020324773564029097075640511236223408047687232256132272$ | $4282531904808786136543906205665619797703690254961264854645238658613522949850724988388999676$ |
| 2 | 0 | 3 | $2070425375031197763951586873702216709056827840273691899196606419803445426788987128797991220$ | $2070425375178882872236476502535476869649329283492706939545651249653776341382166244402823208$ |
| 2 | 0 | 4 | $999075310172007024132209479831573892472891430302482462813803500842244383786384414295160498$ | $999075310362215258423234299300560173281123772024346999195709078317488525194348987205340515$ |
| 3 | 2 | 0 | $999075310172007024132209479831573892472891430302482462813803500842244383786384414295160498$ | $999075310362215258423234299300560173281123772024346999195709078317488525194348987205340515$ |
| 3 | 2 | 1 | $463400277742411654222520782896252484180923225316877744622402041361643862285083057043745137$ | $463400277953881451516613197683101825097021016290167029020737992649344617100440358606599169$ |
| 3 | 2 | 2 | $212914361513472806342186433203634643233845151161054966805058374998937575347806047031157359$ | $212914361748856557233538971039450034834457125556036552533178216387065407076717101705031266$ |
| 3 | 2 | 3 | $101333956485762721524947434430977632374176646433876932260900086495151487783096096702425475$ | $101333956748062932166185723373781047142249830972059446616125096616113918124685991961714072$ |
| 3 | 2 | 4 | $55640852632853967695574711468356592636671421946811025603784765778716304471051040561609760$ | $55640852925471002828452874288376948004014728808450733158246495745334560184485494279081416$ |
| 3 | 3 | 0 | $55640852632853967695574711468356592636671421946811025603784765778716304471051040561609760$ | $55640852925471002828452874288376948004014728808450733158246495745334560184485494279081416$ |
| 3 | 3 | 1 | $9947748779945213866201988505735552899166197459745118946669445062281121159005984420794046$ | $9947749102879073490720025202972848865779626644842019700367894874555202244284996596448760$ |
| 3 | 3 | 2 | $30141946101837791024695541353150484283824253212791340176597092133196842099625822467894501$ | $30141946458488839882607574697833638281516716901601698701663812903947975315915110974500642$ |
| 3 | 3 | 3 | $43205234572104267095826294900676527825399300017417073907425296919894172173008389206971400$ | $43205234966270728518014942375241402234841595848944792050802112242357289339514302315670893$ |
| 3 | 3 | 4 | $49384799137317536895395095251206702850879320897694286467741654538208556330806641201116983$ | $49384799573243235832566863435584068044167724877197466642023170622008941193852724963749909$ |
| 2 | 2 | 0 | $49384799137317536895395095251206702850879320897694286467741654538208556330806641201116983$ | $49384799573243235832566863435584068044167724877197466642023170622008941193852724963749909$ |
| 2 | 2 | 1 | $61743928267744076494532695952267052901839362658248711588374369774837324646403145189408147$ | $61743928787188250461670705556269399662819982933702815824465287381312244902529570259907942$ |
| 2 | 2 | 2 | $46568161777957791007422483865343928888419300721409052026959696337934309299662390197974044$ | $46568162397895739807352761208694338705477241313846489975238440305584899934163340783701034$ |
| 2 | 2 | 3 | $5834979240541838960471227813581485426522999279751038412198395154183069903808028731552581$ | $5834979981513675354610911995962303719447191140237824248265651252633281318915271285452353$ |
| 2 | 2 | 4 | $1113768179796084609136564436025209929807802677927523708808471310148743007216945666239393083$ | $1113768180682959147336048089090870174608803365457264473886630187254365955105053627577190115$ |
| 2 | 3 | 0 | $1113768179796084609136564436025209929807802677927523708808471310148743007216945666239393083$ | $1113768180682959147336048089090870174608803365457264473886630187254365955105053627577190115$ |
| 2 | 3 | 1 | $2221701380351627379312657644236838374189082356575296379204744225143302944530083303747233585$ | $2221701381384404619317485266185778045498159539774291123524994723256098628891191983868927877$ |
| 2 | 3 | 2 | $4478300964000128871711795316711857706413538015312499733612051356316174058552212940229336051$ | $4478300965203677627733101469588325822262901938581953088528696584312515595078716765950652083$ |
| 2 | 3 | 3 | $9057790729882177475116862961678498133772821873733382810094773547592515750041440181134949804$ | $9057790731285695262815499630471310384807104094924638024140819037455525419715896239634390950$ |
| 2 | 3 | 4 | $18306640796706366808567224826770075916234334506833867954152971725895963260900752584857835583$ | $18306640798344143733544887729577222074391605383768511905693605594891138859869105701793877744$ |


### 14.2.3 Root $8$, case $(0,1,-1)$

Factored contact indices: $1$. Quotient degree: $2$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $638526802111052647318921276679193037284540924995309565404059819623660769083129499318725004$ | $638526802170480416682656214977090489656388617187323005220271035992251189700805234133212172$ |
| 1 | $-6136606098427840430351171714314804900554748969491066809865921170335808605629578566494203269$ | $-6136606098332541771184459180142653692884612226032175555159619184132289117999265013351699571$ |
| 2 | $18750762888524470997882097092835807985873775519070907519877232823169743901418876358945405751$ | $18750762888536693213740118055469526524770055303392587722332915417979765499390477608820503832$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 1 | 0 | $0$ | $1/2$ |
| 4 | 8 | $1/2$ | $9/16$ |
| 4 | 9 | $9/16$ | $5/8$ |
| 3 | 5 | $5/8$ | $3/4$ |
| 2 | 3 | $3/4$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 1 | 0 | 0 | $25525895788968065416385477549657654716042928670098392640440911826925693788501270871615830326$ | $25525895789135014060773945984761421914981192890070977537419107624307825294720861409447919273$ |
| 1 | 0 | 1 | $3706829851217451987469773637030725740995498881960271513175035823778023986296003979548224859$ | $3706829851444272177299619301854287082665111257983982239962065209071936834302352543826663737$ |
| 1 | 0 | 2 | $638526801991309556436166817239604751821844612893057905786392643800098085509613446426025143$ | $638526802290223507565410674416678775119084929289574664837938211815813873274321287025912033$ |
| 4 | 8 | 0 | $638526801991309556436166817239604751821844612893057905786392643800098085509613446426025143$ | $638526802290223507565410674416678775119084929289574664837938211815813873274321287025912033$ |
| 4 | 8 | 1 | $254988920838041752556965964765714628175137829259656204862812246302857347911314629785750178$ | $254988921145967423848634595986977736675831638202773717947422337158798503145817379925818070$ |
| 4 | 8 | 2 | $164431709817968808019672879367384004307708788111737433937313611667643858772685756253997178$ | $164431710135097171596547862173988050182110461231481954218358265907716968945289685463544480$ |
| 4 | 9 | 0 | $164431709817968808019672879367384004307708788111737433937313611667643858772685756253997178$ | $164431710135097171596547862173988050182110461231481954218358265907716968945289685463544480$ |
| 4 | 9 | 1 | $73874498797895863482379793969053380440279746963818663011814977032430369634056882722244179$ | $73874499124226919344461128360998363688389284260190190489294194656635434744761991001270889$ |
| 4 | 9 | 2 | $276297957911017778286994475646282256352128448301382822084398105259244128955097952299013144$ | $276297958246742498557063739164720029144200221404407609921681926811487736472210509176817671$ |
| 3 | 5 | 0 | $276297957911017778286994475646282256352128448301382822084398105259244128955097952299013144$ | $276297958246742498557063739164720029144200221404407609921681926811487736472210509176817671$ |
| 3 | 5 | 1 | $681144876137261607896223839000740008175825850976511140229564361712871647597180091452551075$ | $681144876491773656982268960772163360055822095692842448786457391121192339927107545527911234$ |
| 3 | 5 | 2 | $2257914474896284874873084270657435759116634223593571178367057669614608160077942003040176865$ | $2257914475270348141266231560846452098765572426443314020297040069054632287093909432430286287$ |
| 2 | 3 | 0 | $2257914474896284874873084270657435759116634223593571178367057669614608160077942003040176865$ | $2257914475270348141266231560846452098765572426443314020297040069054632287093909432430286287$ |
| 2 | 3 | 1 | $5411453672414331408826805133970827260998250968827691254642044285418081185039465826215428446$ | $5411453672827497109834156760995029576185073087944257163318205424921512181427513206235036392$ |
| 2 | 3 | 2 | $13252683592063495692251050270493170759348311593829538210886339107013990185355708739127031464$ | $13252683592518819381837111475010988684797087575293347236922599635283333450608736382244912455$ |


### 14.2.4 Root $8$, case $(0,1,1)$

Factored contact indices: $0,5$. Quotient degree: $0$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $18757822928109455043661431789552078898806413047562522407775381551824121420768800519343590654$ | $18757822928121677259519452752185797437702692831884202610231064146634143018740401769218688735$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 0 | 0 | $0$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 0 | 0 | 0 | $18757822928109455043661431789552078898806413047562522407775381551824121420768800519343590654$ | $18757822928121677259519452752185797437702692831884202610231064146634143018740401769218688735$ |


### 14.2.5 Root $8$, case $(1,-1,-1)$

Factored contact indices: $6$. Quotient degree: $6$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $532985354527719574947795602836480334725586734213811268779582432838968992968745569858900707$ | $532985354566069367155297930094620051733055256759770103691625231474660347849646814331487997$ |
| 1 | $2219502268067105850550812357804490110147056662366398244600237463017460887949657365959535030$ | $2219502268111610444390845020693830172097037748099045294835965288584730321029717121007522630$ |
| 2 | $3541363950532923475120652686386151352563250564687805985999755697800670342146410762462420478$ | $3541363950577503372475471254157785148566385607524632923277592763495582221755363779100516935$ |
| 3 | $5022718935215540686535619337721830751279902572097854943908614109195640632666015028664892896$ | $5022718935249080658933082710967941253103029794478780881264050336849622075944066296832892821$ |
| 4 | $5462477494568418297157774936002063946430944794902185270992091572335976745425814239788927453$ | $5462477494578254325128283939826176788880047262201421882703078826725494880028735423125582494$ |
| 5 | $823897805280607803188449241829054067230818860711449786304847523441456655912578476733616095$ | $823897805285306827201986645363255229931475610922386236528226815755170497657329445474631318$ |
| 6 | $864549210321499565046931442524069141281126823914865375983320537073169147198030291774530161$ | $864549210322050486143743760444713475803009184476214273620786425495520893928327387008692461$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 2 | 0 | $0$ | $1/4$ |
| 3 | 2 | $1/4$ | $3/8$ |
| 3 | 3 | $3/8$ | $1/2$ |
| 1 | 1 | $1/2$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 2 | 0 | 0 | $2335257001304562981747240290723738119869365764218455489126507798859262333107888000569732030$ | $2335257001480623210627915947167920536324719215786336208479384151536700167033822532208235866$ |
| 2 | 0 | 1 | $1275858247864266312061688269875962652591852706843869904856349300604712061300801439141963327$ | $1275858248065362296298418664542000264868591210259150692596171607413799041030847782554204698$ |
| 2 | 0 | 2 | $649415031326729917125338904923573786843372586138679207963319036013720069798152498257010390$ | $649415031557186157367421063054905244958195048473103770530184805695562522590020654061066185$ |
| 2 | 0 | 3 | $294182369212376245032142825790405239823973642358398272220723539628772669806880617685653685$ | $294182369477335321593568271269828319975227419464424158799620880529453343754175508959650908$ |
| 2 | 0 | 4 | $108045389970645984029599884679652499216997737004430449435622535782596428638548659652980859$ | $108045390276241869241097893322260702425431223626788019987221289362730174105274850499905651$ |
| 2 | 0 | 5 | $25793304559937150468373670027835183670396830708724674368517110319347395190294024227352683$ | $25793304913510211397133748452381767596120128270866848056044227490969264589769467194786374$ |
| 2 | 0 | 6 | $9901959438817607455764324248197983610567067742102341152777265707568593350748988018346032$ | $9901959849179907134975606794397495273125141691316201690561830504953605311588692486162001$ |
| 3 | 2 | 0 | $9901959438817607455764324248197983610567067742102341152777265707568593350748988018346032$ | $9901959849179907134975606794397495273125141691316201690561830504953605311588692486162001$ |
| 3 | 2 | 1 | $1956286878257835949459651358379383580652186258791174544907343401679192430976469913842707$ | $1956287317014755003896535965405359111627648401540878507820632011945775672498305131849814$ |
| 3 | 2 | 2 | $10600799390095387080309195686605812422430090607750868399878816308657349413381351613494763$ | $10600799859449941268268965939386888576709182305858186716503099740374258592739069926661353$ |
| 3 | 2 | 3 | $31144977781651243736725475034532856439200298822834096984362934737070942284042667693499309$ | $31144978283990410812255367983117831141598619441100071152168250639086927835302153550830233$ |
| 3 | 2 | 4 | $60628717579007004229410791827361418920415090415323063275835256284512034966007882513879462$ | $60628718116918305269154210294250597060682169655597480695463472925382078360521131742647130$ |
| 3 | 2 | 5 | $97534283807980273499278258668318999542111821514814713850682756934876798988227900802795061$ | $97534284384269926057752762244731085673157957048773766189033813661473712507102934913019274$ |
| 3 | 2 | 6 | $141709337359651201680120609889850951585040827613600793951994370021141814340819722355056156$ | $141709337977363979275648586065730334332619069449916841604826966141868818578903014313498860$ |
| 3 | 3 | 0 | $141709337359651201680120609889850951585040827613600793951994370021141814340819722355056156$ | $141709337977363979275648586065730334332619069449916841604826966141868818578903014313498860$ |
| 3 | 3 | 1 | $185884390911322129860962961111382903627969833712386874053305983107406829693411543907317251$ | $185884391570458032493544409886729582992080181851059917020620118622263924650703093713978446$ |
| 3 | 3 | 2 | $237328931785690716952780196713489227092131114810467383681081708629572096376375168722923842$ | $237328932489294518140737505578247591698526619260169782358636082846962502647721449344565474$ |
| 3 | 3 | 3 | $295890620873837113089365051028615275258275006400134068078410479920614194379827596596685978$ | $295890621625192142314825435371455397805551469506534351590822552110471540873813532456812140$ |
| 3 | 3 | 4 | $362782514932104013597389880118424255011864823336373471155083187662590112155051922390063916$ | $362782515734752015792216054356749176681142784149306101818429865939591013597983315142915606$ |
| 3 | 3 | 5 | $440506092947623197559075473324988484061204762581246990555383218849413547469759990729681607$ | $440506093805385898921449002168681890637266627956274234439315997480791159641158456503746413$ |
| 3 | 3 | 6 | $532985354088393213729607650818690625973263393551765772905560423615127587449682694820042945$ | $532985355005395728373485882112409760485378597421815599565647240698501753368709689370345812$ |
| 1 | 1 | 0 | $532985354088393213729607650818690625973263393551765772905560423615127587449682694820042945$ | $532985355005395728373485882112409760485378597421815599565647240698501753368709689370345812$ |
| 1 | 1 | 1 | $902902398651473278411736360793499193621497917433840902306269242677983747369373511181488296$ | $902902399805435046181633401887321239877826475283981060070972213569344128278914620836743408$ |
| 1 | 1 | 2 | $1508910373218566658435410419362514367073231508926240238905012839003089581932498499554832001$ | $1508910374675489505154643835770955213542084363683318240663418973264353666139137016395438472$ |
| 1 | 1 | 3 | $2602145224541580474132522317430226614614452610717677166781781621169202667185834825028323277$ | $2602145226386883052234059795293309813411310438259945548521630333507035926333103777233071071$ |
| 1 | 1 | 4 | $4797908065674314882114012437948574944349229013964000809399980561628204254829036088627476836$ | $4797908068018824772901446591658817347287982996660419461687179237418537567621968679459983113$ |
| 1 | 1 | 5 | $9212981476852013454704464944967811580882961974512088763019771228856323634803098311536513262$ | $9212981479839844283475535661227531171687695420919481132790072448565859844484164376923485864$ |
| 1 | 1 | 6 | $18467495016692413124423635115211435783286767153038605206094734356578531645076856211094329544$ | $18467495020511277609553111751441026040485960324318017266395040667505592997383581791029819932$ |


### 14.2.6 Root $8$, case $(1,-1,1)$

Factored contact indices: $4$. Quotient degree: $6$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $538491737348953134035120559323212114543956091201655754170323208402798609121541582354788800$ | $538491737389515717631628995431857315102480179510602559668411631272051202348845343912560716$ |
| 1 | $-2215860312055001825399042598996003547438556616999617552272943173194748982852354380381563995$ | $-2215860312007641705529954349655780260657113842883526439408012943860980565116401624495668993$ |
| 2 | $3547640437241983689435028702343365876872417651153646776897158253167241111563592199069979019$ | $3547640437289615903484044080695492761783531083526188271013108876407637467550755322470618697$ |
| 3 | $-5027243690153246381409876730959641917275919322590881658939389237841158267313577958895335082$ | $-5027243690117402287594652592500742896734931550499189378040814562644456066494397404068935055$ |
| 4 | $5457368682752600959165435746669270159795385335041481780351076358662610399004208132479049258$ | $5457368682762930263939978776365131851463968099900645429610933910218296721188379841571830174$ |
| 5 | $-828833639335020791430670656962437603626959240867523046227806398521858280849212094970313339$ | $-828833639329997149895499106101626965318532850291151247763418578824637371046335234632848034$ |
| 6 | $863199116512059980440780474216824942345881811132382687607977929096522327593426874348059631$ | $863199116512610901537592374810835589660829227669857885762797981499974697098033850246940392$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 1 | 0 | $0$ | $1/2$ |
| 2 | 2 | $1/2$ | $3/4$ |
| 2 | 3 | $3/4$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 1 | 0 | 0 | $18478637615310638906096471530810823216268219132203034064238781834659246449939903051449328790$ | $18478637615497941784832834214221400586352243771065316403495391208955725619201158792449162395$ |
| 1 | 0 | 1 | $9221019301327895039640540932076882585470049011905703508359301140989942251359506077344439384$ | $9221019301568514215504852398499582948942870395214588467963051368708793385111850761780624550$ |
| 1 | 0 | 2 | $4804061437017862340703163608951599242286750890461530178138481435172003408074895014419580278$ | $4804061437330173850758479857681239945105305584325580837378505779059134208461502527911743008$ |
| 1 | 0 | 3 | $2607312165140171140172922266321910329087426333657221495830465292508808824960075098683521624$ | $2607312165549471828992366785539841973038577457587079375279811221633162193007958102478777509$ |
| 1 | 0 | 4 | $1513621203593350863288708835103404929679595357511683439241917834252646218098204060869312488$ | $1513621204134772471548977888071516345242460982140278541684486853079105347969391368459821307$ |
| 1 | 0 | 5 | $907801789013048996197020321269082212377207327128242148264594346351094370875356260358954925$ | $907801789735860443957895391594617851951840686897873497520966512833043698589823333387933537$ |
| 1 | 0 | 6 | $538491736882310032950035129094934515414533666679248219015885827289927717667713693456137658$ | $538491737856158818716714425660134914231902604033010094822849012384922093802673232811211971$ |
| 2 | 2 | 0 | $538491736882310032950035129094934515414533666679248219015885827289927717667713693456137658$ | $538491737856158818716714425660134914231902604033010094822849012384922093802673232811211971$ |
| 2 | 2 | 1 | $353836710816940551326542533007860666933196836454751254391531567759344391063892410004729025$ | $353836711916308006096123942692893445371933562600578393473790262160861291409098182522851188$ |
| 2 | 2 | 2 | $228309025363961795664225767335830573536788598713866130199331050438857362963872434955205466$ | $228309026606259794063008842361255865404635074262532102491082221886285500163627615858281955$ |
| 2 | 2 | 3 | $130488407458754327719607132613343277504592881478136670953958150139188437664676517845528071$ | $130488408863942066679568515859095726963155393040514453378924742997437826182938937261016495$ |
| 2 | 2 | 4 | $51693620214661022243314016768834894235913741460920729684188973704696647650209135521263348$ | $51693621805635108443503160832326184607536616909946845835590487683927927064296940425506943$ |
| 2 | 2 | 5 | $1665621051433284073768780226103083669259511254409072124793908383469021831481211144106148$ | $1665622854478418749916762094850187108939435971558534946995250428294912125039780280272624$ |
| 2 | 2 | 6 | $17738206019178202425265835915369411425681349815587740402304325339544515155482128112091025$ | $17738208064487071689744953200929975822318337305257847845311998006507347284221723881135768$ |
| 2 | 3 | 0 | $17738206019178202425265835915369411425681349815587740402304325339544515155482128112091025$ | $17738208064487071689744953200929975822318337305257847845311998006507347284221723881135768$ |
| 2 | 3 | 1 | $33810790986923120776762891604635739182103188376766408679814742295620008479483045080075903$ | $33810793274495724629573144307009764535697238638957160743628745584719782443403667481998912$ |
| 2 | 3 | 2 | $115983960085640695649302239525900205261601095705635402794230641528998620946212803393202859$ | $115983962645669720202815925256645339461052222244744097428857477996777667701024714828959518$ |
| 2 | 3 | 3 | $301591509365438016257178292609384375285226230759180764872083394203719307502660786449506447$ | $301591512232024132500408929604098941953337775202526985033171162018649568976139132977839818$ |
| 2 | 3 | 4 | $655560073506777856190557516291733720556572578859183813431665355399772949131794837883360925$ | $655560076718449610309119439643992105951302181571393222734999936719733508789517301111764947$ |
| 2 | 3 | 5 | $1279579770144425827703555508527079979205115502178183507068796567625326282461433275485691611$ | $1279579773744728736909974247983675156350162727243480498417645153463356971145288461434398664$ |
| 2 | 3 | 6 | $2334762330386898473196701274707741407053704693524382287636466119471078990741764200035874678$ | $2334762334425061935213212399972016013462731361480189534792937134368214011054740248973287511$ |


### 14.2.7 Root $8$, case $(1,1,-1)$

Factored contact indices: $\varnothing$. Quotient degree: $8$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $122907978696384485867516398109825892605987206937152769804188260257641345878282947367638713$ | $122907978696935406964328298703836539920934623474627967959008312661093715382889923266519474$ |
| 1 | $-1043156775456650263527088997736800122411387649098489642247141188939648414844680428487944653$ | $-1043156775455938393411908887524454212061371677738184358912493200713864290984606245982634910$ |
| 2 | $2060135622707252770999644077991696285708970125691036931592176025662096400375688809752460887$ | $2060135622711068653873759421678841017744094774796975546131403675367515472592769881890094205$ |
| 3 | $88891073639584229196338749821838878784003807378952563355140377522862804486781589782202940$ | $88891073644495459697780631522717894583341945272521770723733062113854789557365810059458818$ |
| 4 | $2557836775447946292434284013197587130268440978853377278139801317298250308158446894247675562$ | $2557836775452988753570916526247205035618201876473902821400744018923492559492727521766169382$ |
| 5 | $-74028198510098871356054661755557793929988766368898096572274340504635518812046000286120330$ | $-74028198505187640854614971270446742142815521302173635838169975242435875575940375168571223$ |
| 6 | $7700270045182465956344910709778618377890324679913009149288237751491111983260914421481959570$ | $7700270045186281839219034589700181579401897905230917203584359974677088655396736739442548026$ |
| 7 | $1044880824555754235082272445726149295735118254143851559550470800807700075226961644992297250$ | $1044880824556466105197452443306017492671536462528489543960974569545830641751601098898942227$ |
| 8 | $862994547185531628126189981842793596695960305263152729511753056936479592796319551459140002$ | $862994547186082549223002299763437931217842665824501627149218945358831339526616646693302302$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 1 | 0 | $0$ | $1/2$ |
| 4 | 8 | $1/2$ | $9/16$ |
| 5 | 18 | $9/16$ | $19/32$ |
| 5 | 19 | $19/32$ | $5/8$ |
| 3 | 5 | $5/8$ | $3/4$ |
| 2 | 3 | $3/4$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 1 | 0 | 0 | $13287558044979745603143835964886686850118992087897075538402111955942194365721232336501679822$ | $13287558045004767873455573600037871845725226199745508782138539278101742796334723907058198182$ |
| 1 | 0 | 1 | $5626351323599926098359854737184046538909164826238295521557675582116879253145527635667626166$ | $5626351323637459503827463216493595355259475837356643766416998004511821860928197515006320627$ |
| 1 | 0 | 2 | $2808221949461513996383681895344429864654238936328822822181584579779423337242705691367621665$ | $2808221949518184606737661791016532546547002694957830058323200778587191759883791583676376962$ |
| 1 | 0 | 3 | $1678794838636505354150368172348845941845344777847920470706918207705107187475512969153645467$ | $1678794838722622776139034987945428155709323349555097559642754953119557321784685213630777682$ |
| 1 | 0 | 4 | $1116135162757207287577871197314218685467196052817464922193081746345305780012241580763344651$ | $1116135162888912047646838958241214740736760978146797038935644502164218962620107738412444079$ |
| 1 | 0 | 5 | $733233245509495583595079252163743307281963338692917311899470635118559553353214925067746675$ | $733233245712220928095073609063579983660654733037555471517563919037045516232629819028836994$ |
| 1 | 0 | 6 | $457273444643289769580408710377054120565878263939361095426652515376349967146439549377732151$ | $457273444957403052660235582740155370702557144627588588259437644278249408892357086004161882$ |
| 1 | 0 | 7 | $253302575383632370373256913772534384047615442036085891219657083785710734069176790040002580$ | $253302575873761104575962518698784840288401304230279096688493787839713415420656914902977733$ |
| 1 | 0 | 8 | $122907978311290711146782225116892512493459585116350072739716717807285487448507302712417909$ | $122907979082029181685062471696769920033462245295430665023479855111449573812665567921739990$ |
| 4 | 8 | 0 | $122907978311290711146782225116892512493459585116350072739716717807285487448507302712417909$ | $122907979082029181685062471696769920033462245295430665023479855111449573812665567921739990$ |
| 4 | 8 | 1 | $106608653677248003743472889034937278549190103001383095429724172059982331620923616796469825$ | $106608654483062691323699965821518055001594862928574611065353113520416593611666649549085273$ |
| 4 | 8 | 2 | $91458958296132104777361632764683261244984792214283921021716861712870019331724200755680255$ | $91458959138657295105983913337506121378465242772069511168256526987356615783538181553304718$ |
| 4 | 8 | 3 | $77461992442514825430427281233409187953434052583437819776361256253176370177251008995630957$ | $77461993323462864316763548726681973710196968875622013121679836733734507589989414446500778$ |
| 4 | 8 | 4 | $64629777417666151884730143992648748243426528590221753544903952775744831175879643216657389$ | $64629778338831279863595423466923509899649304474030664363719111958417023319871632160363770$ |
| 4 | 8 | 5 | $52983215207387515641103201132882048232278783658361057977184729590989739758364218274757992$ | $52983216170649897314785154976686780494044906873087500542601262036343045344922247112748767$ |
| 4 | 8 | 6 | $42553097218383842228902635691665126714471140463411075820461018178387229177752155230955922$ | $42553098225713800612534603817238849012060474137078776823275893924422825771206293575819825$ |
| 4 | 8 | 7 | $33382224372924758307102998729846673961081982435732770655770833939871168071448453797589486$ | $33382225426387225029309831064913478326650534713948597646858515451636527253348667489926870$ |
| 4 | 8 | 8 | $25528752280028765249718252233822128224217997995000271838702039570622707092753401917095670$ | $25528753381787958061078603023895550317894287479677380841130854146689466457091013019575945$ |
| 5 | 18 | 0 | $25528752280028765249718252233822128224217997995000271838702039570622707092753401917095670$ | $25528753381787958061078603023895550317894287479677380841130854146689466457091013019575945$ |
| 5 | 18 | 1 | $21602016233580768721025878985809855355786005774634022430167642385998476603405875976848762$ | $21602017359488324576962989003386586313516163862541772438267023494215936058962185784400483$ |
| 5 | 18 | 2 | $18004630375273544908437228354246059241485306951004224608538592668691146145960512424820009$ | $18004631525870518246595761160704482978301463292620904628075622133702215091233351453110528$ |
| 5 | 18 | 3 | $14743864156234406483704045587430169662829237576570144543263373255598359552079847253814033$ | $14743865332074262506972890283872350547260085629412329639029366006236468137122215546269337$ |
| 5 | 18 | 4 | $11827946695512470788268039116508288150145402765623121264699832439445715779419871971016626$ | $11827947897161377809059203737653994193347222634165869286267609784139681905541280348449921$ |
| 5 | 18 | 5 | $9266171316678165257805288146168628498339121826614927443514223449123942243865587022331730$ | $9266172544715294145702057485828427141614821721270441975049481834329891589302747613109122$ |
| 5 | 18 | 6 | $7069019226243404198088242086368791309297434999666316595149092877172843262227077671913631$ | $7069020481261235109808594790660145240707159872441121490942286611960730702203493872806885$ |
| 5 | 18 | 7 | $5248303222326138537891727802891358303389120873771678199726173318611153081312705756703446$ | $5248304504930775113205722583084740391812167615906052075949907059751159109720851950836070$ |
| 5 | 18 | 8 | $3817332522914556075656474254302811807126350067452710202047860615636107270798918569869205$ | $3817333833726047287717301400481257704703657411642407493654774623487236096637590677172612$ |
| 5 | 19 | 0 | $3817332522914556075656474254302811807126350067452710202047860615636107270798918569869205$ | $3817333833726047287717301400481257704703657411642407493654774623487236096637590677172612$ |
| 5 | 19 | 1 | $2386361823502973613421220705714265310863579261133742204369547912661061460285131383034964$ | $2386363162521319462228880217877775017595147207378762911359642187223313083554329403509154$ |
| 5 | 19 | 2 | $1345136428597074349147227892014605324246351774390444604435842065272660020171928924576666$ | $1345137796442323807854910060246214492273119055386543161761756866905038649870448778153052$ |
| 5 | 19 | 3 | $706965556185046081275224771770314173786838225744515347049138915668138520135758487662340$ | $706966953491193456419251464965621238511385415642922008443550108318472080368717631080241$ |
| 5 | 19 | 4 | $486654844125313477911842396331774792140601263244960841692497553223233852721152821686924$ | $486656271540620259742718575858493574669640679874102736566001860316772079137340798949732$ |
| 5 | 19 | 5 | $700671178410738323493138546792190205768249245121768462531117559191755626210539015712345$ | $700672636598062690720269080963140183735689556791277218010610590321969837194938841053774$ |
| 5 | 19 | 6 | $1367328641032470259205639757349828198758726183888596428512400857274875921290664510811179$ | $1367330130669604426615407717892780996458579863375628965534930915998787137044725959588378$ |
| 5 | 19 | 7 | $2506996666798725533878410292648596559879863537647390528228178564583951188935141495213186$ | $2506998188578741136106299243652796671207794063261567879015246463581366337476278127154025$ |
| 5 | 19 | 8 | $4142331699395347173046751236450473984531995941584825128500108367845374368425518770244190$ | $4142333254026948882733451669139359009717168332116947590718780598397791210520941831240910$ |
| 3 | 5 | 0 | $4142331699395347173046751236450473984531995941584825128500108367845374368425518770244190$ | $4142333254026948882733451669139359009717168332116947590718780598397791210520941831240910$ |
| 3 | 5 | 1 | $10683671829781833729720115011657983683140525557334563529587827580891067086387027870368205$ | $10683673515819779869242061371085608363754665407538466437532917137663490702699596647588451$ |
| 3 | 5 | 2 | $25155684069454182118322605322915238398244975975942549939573980329174326393882941620556161$ | $25155685898237747449930845468656604337954723586471038055918551072670720956688036048275809$ |
| 3 | 5 | 3 | $49008380814306345973113491530988874635466763849355943835044658563184300404932383305660708$ | $49008382798175319691392316659207342243282858111657294910977977784416843382492435232675522$ |
| 3 | 5 | 4 | $84277248732904733765148668690871680998348119163212420719421556054859478240386249163126347$ | $84277250885289945744978860636135350091979134506401464959894065861948221180012221211927096$ |
| 3 | 5 | 5 | $133820464572501821923508524352351841788854594289195764914408881631356258881504799104400093$ | $133820466908024100977230368215478234319331291523911933210674045159469556381378627161826577$ |
| 3 | 5 | 6 | $201652363859386456787522741375862943090827472063103728481546743800173301710943767801781706$ | $201652366393964832881133671597447538889291814676284528905880419375604557314605213944364699$ |
| 3 | 5 | 7 | $293394302553377077156674166843769515672727564435107796210985525883424183805899493760235886$ | $293394305304347120623533135620337562559568250204261397675673947762105012197280272213091194$ |
| 3 | 5 | 8 | $416877219968021680935029376872307628938539602593928380170649111737561272342731378928250856$ | $416877222954264961220566060929612821774858313793874446752466498524404203689812369479499073$ |
| 2 | 3 | 0 | $416877219968021680935029376872307628938539602593928380170649111737561272342731378928250856$ | $416877222954264961220566060929612821774858313793874446752466498524404203689812369479499073$ |
| 2 | 3 | 1 | $663843054797310888491739796929383855470163678911569548089976283445835449416395149264280797$ | $663843058254100642414631911548163340205438440973100544906051600049002586674876564012314831$ |
| 2 | 3 | 2 | $1037772804509216029685265355228986244737435538376476780930202670237654452257563556438553899$ | $1037772808512078535027231607312254800816073080398871364287632791076795916099368914535856129$ |
| 2 | 3 | 3 | $1601313983612121087748138660701003351972233030498413375234719342964637218277111816038975947$ | $1601313988248950615187463553385603335164343957559442162756505017251250453246557961142067066$ |
| 2 | 3 | 4 | $2452467440274082991586231986817268350574816712603925463991293381027823326472524158749829101$ | $2452467445647213144613113127846648557799675509067704383807980967474736370484836673649984230$ |
| 2 | 3 | 5 | $3743869369769230548400535345573658038542770333809948242205291095408836914375812537899246615$ | $3743869375997861428224585583099352378846858361593775903442282382726237016971579957730033710$ |
| 2 | 3 | 6 | $5711782208929394998358643099114115111982219173327999684337787689169928362135984491505656768$ | $5711782216152439075952426909855431136790839674598203952976463153157096005768403438533606075$ |
| 2 | 3 | 7 | $8719185875481141598912445724064691526996583948519572760734049445189666013728804165746004178$ | $8719185883860562631698260749806893047452739298047731193613482931451481780545265362108715423$ |
| 2 | 3 | 8 | $13320731888598315129280891273262284183735221603065771350517529816279708328695951130016443920$ | $13320731898323048067366871795841203894565870394208952378063601626943557254970879301158694322$ |


### 14.2.8 Root $8$, case $(1,1,1)$

Factored contact indices: $3$. Quotient degree: $6$.

| Power $j$ | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $2548901080282979708190951874569884764678422883090915332217509046156512525315274674747221029$ | $2548901080300290763277163485152610723319365949782306721453060435995625648928312687712883485$ |
| 1 | $1523100736959997772506496828167059435504528902490319633263050047759335094425856719219393712$ | $1523100736987452062122184399318733022905560580257663296880184455525627421660651010814720229$ |
| 2 | $3684564563862740042354458352701996925227306865034501243559493297865041481148898640541079884$ | $3684564563892010896172380039215744168115976579208797464569400689236746721331942684309904387$ |
| 3 | $3477014162853405779213594146406995514316230713927697754958396227128096037726046509451744381$ | $3477014162894669021788583037237689410809515364983699359840768659341454474663930190311241879$ |
| 4 | $8284607848505994202881909481723899578741830489561222914266581085617814692934804587382861001$ | $8284607848516646730394960245751901799672872547676655800205085248510372208436612205105305974$ |
| 5 | $1421859653626943653382017841588125477566563140581894835123830521238476692858145373064010506$ | $1421859653631350296725221219115899409329715790355476203324443596306669046853374902585338999$ |
| 6 | $863273458910085356958168352648158654172423797447381877229652596212902993676379226098982927$ | $863273458910636278054980253242169301487371213984857075384472648616355363180986201997863688$ |

| Depth $d$ | Index $j$ | Left endpoint | Right endpoint |
| --- | --- | --- | --- |
| 0 | 0 | $0$ | $1$ |

| $d$ | $j$ | Control $k$ | Lower integer | Upper integer |
| --- | --- | --- | --- | --- |
| 0 | 0 | 0 | $8959372398048327929749499405971618079775192299537182507227839314678520749897401025058843734$ | $8959372398179237462797375207200245565208263533652704838266742226233192116867805177390808935$ |
| 0 | 0 | 1 | $84785804161830261350461370783805420587981004253691337724977005052818155363558262347665254$ | $84785804385317987173533493341163635716999251648690500087236192768050911475813546546688795$ |
| 0 | 0 | 2 | $2327979080555992747991551130234849263944487779798655308178655179073627734530482155512719880$ | $2327979080943873598991260968084069218185590043628555303361998963509644473525639431946397332$ |
| 0 | 0 | 3 | $2605636277968227321814499290099652434461891685909226977663636825998656234974703656439348327$ | $2605636278647899513590473730844127154890386054130672124661361880729503322189633371451346239$ |
| 0 | 0 | 4 | $2900480342069837193497920377077685591082287515116766965083113785515492392340613414016528461$ | $2900480343267961756241301039909903817868404152536120779598880149700031781291536163993036526$ |
| 0 | 0 | 5 | $219773914336022105868706556846905459831810361668189990859344771956777670459011966546627045$ | $219773916463333988683877862987087025158250629981674369212815606850513764880343114860746265$ |
| 0 | 0 | 6 | $21803321503161346432836195921599826933614883227079751061322059556141168596753930404490057860$ | $21803321506973856131186873635241041252232801591303638450953868999369861806387285208852494221$ |


## 15. Exact implicit-derivative interval data

**Definition 15.1 (preconditioned tangent data).** Each branch row gives its exact Neumann norm upper bound and error upper bound $q\|Rb\|_\infty/(1-q)$. Tangent endpoint integers below have denominator $2^{300}$ and follow the variable orders of Definition 7.1. These enclose analytic implicit derivatives with respect to external $\lambda$ at fixed $t$.

| Branch | $q$ upper bound | Uniform tangent error upper bound |
| --- | --- | --- |
| six at seam | $28877750363898171320310318386719188730143778837398085516354449068975625313803451353/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $53982765953356490255578203898934052663677783838686844073190864603132157852829719726091026479227453489692238952245583476953887877913479787317956299241778308757590038948118733/1037378862807740036194665826152279967053044529699236051540081882177565424589867145305005809249224124134352583148878070988402607646054757322313608023699048589683733080353989438996480$ |
| seven at seam | $6171230839639511679701476098691946447814562414768992135620153335883313634325535109/1018517988167243043134222844204689080525734196832968125318070224677190649881668353091698688$ | $16820633026603290938084962207290041047471480454748345038868699183780042248525129861652424657173573042038038289747092305624986231669566259155539942134212594564327859652301069/2074757771869477240645640918211330598391755754386298428803802248277891356361873942161288805977574186098036002333220921007719338533384975024912554390386435536415135389963131975368704$ |
| seven at point | $12489256049627918372131468772067323478156423885670980517812821363040071734758763919/2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376$ | $16910809099301239807478227515608770959477202145252610447075636191923649838452596934214648607722897877551202753763081198048590364730139760621085953695270799943278486054717397/2074757771719964533883607174611726175002830290148025032653681335706496187190764445460888998091070900707308981172452084813792687254830935594893859078014461142378653617882699887804416$ |


### 15.1 Tangent: six at seam

| Coordinate index | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $3206988095471811962665834346535168992293741721213761422590107723764484621299106134965700$ | $3207200101973373865947514349548710248802376783994785673626386624991664479555250371934277$ |
| 1 | $1742101684623673048546647933136271088202615453753850573236630682033913993498577521646395$ | $1742313690981597982203840023782384339270178347799724779613128128596915057433799738316452$ |
| 2 | $2392562828806401302673433115515589362411740197881033568704352541499878736547316795066548$ | $2392774835229259543324101471988051127032472702914678334168150024764007604388077762774238$ |
| 3 | $17531689345161081136464689451943338940266303624392777489445582882120571640391024703545011$ | $17531901351480004820495480580672867666041503488751047168795095510375392063055420481857217$ |
| 4 | $24114602651455280103720994886077716126375776945025259118271924270638343611434966795697211$ | $24114814658209032781274442161567106140002455155519468655986234463101207659010765380169191$ |
| 5 | $-3752602016554272741079554675513357673395539171081324655499134990920777605293237485894776$ | $-3752390009950994471604487621613396180180166783732066480672694311521531018023040633758760$ |
| 6 | $-4343568575310304157794780893893456759800363521056643568583443942392567630503375251085382$ | $-4343356568649686715155852325735820435265904168916477840418172958249822558509512516199760$ |
| 7 | $1018765012844571398917222791782149578825727386376995108617452116895753824943150813462532$ | $1018977019354054708167375303904527231323042302531503296592597887093067306834403713214054$ |
| 8 | $-602038393853555767681094926753004555014962139594338937139861293965164911582205927219268$ | $-601826387319556344175747135520599073882862745187557605382522083797913180379215608800887$ |
| 9 | $746754495286560409029509678535007934849291236643025720503741623312676833013633124983701$ | $746966500496768849896484711127286962021175035278402393033704668516468513634241620004038$ |
| 10 | $-1225368897061352912108604669794632778836718601358763121750085562694880935924397895799192$ | $-1225156891819543989372247554598970016053287157666172938095777007317437149880776522967562$ |
| 11 | $4404820339663811260038059607170510552433993714974952678198846763542889098080439909317656$ | $4405032346368233260239675413777001359400868657975074814423519789056930790222666491561532$ |
| 12 | $967973681810635230352287134120772092309559237410254945999272546986375954143973700787768992$ | $967973893816887081152433805456067362908021786018268393000178881226515427865237339318304270$ |
| 13 | $-6247532424330267853981131181906123421837726220101023663767165868766244351082382919490$ | $-6035527197658259053696802739718313443770904205755540372715647607966448447738583290365$ |
| 14 | $10043353399880103565375052892905420066956267760415676418018197031219918643711904083501$ | $10255358765315386291502459931631022599163602097369850984242770606716251928626426335501$ |
| 15 | $1071683894365185607978779025267157346191541701851857463831378739254673606160999785526919884$ | $1071684106371546411737135258338812303102202700340542900275530648298424360069570162769861162$ |
| 16 | $1138874272926841201335507577382779215507254814487612566877735910553017836018972377059$ | $1350879645326780632776903038853636379303954504836263453073731960282871741678388700525$ |
| 17 | $-2904405315568570791879220836514387107901635964284786000831097279418900884504362582753687950$ | $-2904405103372936132259467463588040112183521560911969119585289586579694395614600790623996070$ |
| 18 | $3738709819054669267395340014785121307612398991339279124796271980551357124435649626706109445$ | $3738710031332749013271001628839582649027811956186483146095304119457636899023895186428535030$ |
| 19 | $-508363217450536253339242150959722918434793742800548795624211872320882089716810717211287529$ | $-508363005300180453948846782347183828077732208685611034019504945228677608581013700916846138$ |


### 15.2 Tangent: seven at seam

| Coordinate index | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $3273491123137294193200900776530976276696001638813585922192515899664610978124411220463302$ | $3273524154121584375449356955742764461169323442754945871504764549100354521990520411986770$ |
| 1 | $1686176690682412005457986846630755162299245086830608649026423365835438871813132371076234$ | $1686209721520121432885097001472600733299873852217058335077835411122773086079375674812064$ |
| 2 | $2453987091777993294298104652100920423628161421373024477228901501528570434453611239267343$ | $2454020122682482867732321188575051381639727015144242182770715950551238882444000914260135$ |
| 3 | $10938322213698809110118693594981666348339041829559721175257453911761004112411658584628262$ | $10938355245848759357454110777406997924491670089189455373406304206513242804917152183363158$ |
| 4 | $32247967183650078998877542073750250304403525430936418614865625420300162623061497497726772$ | $32248000217298662030477451946481321364031278892898406513309436203195470090917296517308588$ |
| 5 | $-3819127357866617889285364334752520214973729413054918516724949068714955490867038363921312$ | $-3819094326780123892908866049072315471827775483441831465992558156691321152469107274036287$ |
| 6 | $-35388296892989766831900056765868361633518769279055922041467994784886224279197691675115515$ | $-35388263858649637288878754605934914855570452614596503817743988376799639390650169058546801$ |
| 7 | $-1696810522327573479677047598876365006930889385657507238444335547143932345739876732528135$ | $-1696777490464126517119256917244368788747628349386512622482891034554339347922313738649400$ |
| 8 | $2951558562580091057410479039812525586954063439619040178545869351286098792253843607084697$ | $2951591594254612148452934294706056120626939030895327939689757970302519153398622646358616$ |
| 9 | $-4741342254451151126122761678158409287007154008065722392399924088179911947901912737982519$ | $-4741309221868821123009811161172744387211641542733735926003814389087679262010474101724736$ |
| 10 | $-1601074662261666329088257514175073084700838575812378343033343349472373785059230145853322$ | $-1601041631638274555604792351564584762852126753042046101805044513716296093665743501594439$ |
| 11 | $-2385624907923501448525226889308729482178414967406099800281787589489851877049636481415716$ | $-2385591877772279529579942943518676673057114928473706674187618044986268419290720622993900$ |
| 12 | $3987883348650494230231907969386427207420358751752258696309394075804727596549372993823498$ | $3987916379825855772388781501654941864342329923402678338816110745261932319497375933346051$ |
| 13 | $3485294826133004267416090404327648085186362502446194904029424934618817652690472613199387$ | $3485327857263336632826903844131352608155754862462209041248201479356557564247409132336511$ |
| 14 | $967886501762836775377119931944872483927944458919360290429215495898030685203042972323300092$ | $967886534793577897920537271860845406457783480432422823540792898020891239500690251590388121$ |
| 15 | $-6538455562871497021037886995757073561159714132872878525448535225419728904961623775156$ | $-6505425872892791426731103944395999859289486285013182913709318737892297280823419429734$ |
| 16 | $11129165766293469628766327765443727713740858696038389985390752416527359603844929186279$ | $11162195595222226331100475706078528695825852275673600446579849663177838252067543100495$ |
| 17 | $1071780096526735688805758023078969346473193632512691530689040197206097270360231208983122790$ | $1071780129557588285255210421004631499317819289332621795014923309402181989172791708901714542$ |
| 18 | $411838632000168251036503344322376835121682358645347991971042756564666662554805187329$ | $444868467837896997183602638532259816029912373670453420556949509750045830338048078542$ |
| 19 | $-2261578507613269513177099371999827332879989537395143192973786813530596804009011676944556550$ | $-2261578474364324057514239272346479341729364583946372541926362045409756274011862121501615562$ |
| 20 | $2725652849448409720128112045288216658491242771029568076194525218252201258374542229590548704$ | $2725652882805235382635020963001197744428887831958402434458363979343117111438781091925329354$ |
| 21 | $1044908265289902157486201958255356965350172289698022505363682193573713936027758445524621$ | $1044941470240138445434340222228039787468055431909152043425532694884546406206149333543843$ |


### 15.3 Tangent: seven at point

| Coordinate index | Lower integer | Upper integer |
| --- | --- | --- |
| 0 | $3187931645357525274435923842255264178432163144635448562721690674011715690859217615076601$ | $3187964853393756462119108925130200085224049788236831740235347397192457476806115058060640$ |
| 1 | $1618859883989065410818571024311216826984678396092694010393793517517984957578303688669958$ | $1618893091882526534654742458027627478598899272489047345248542339441597223257678945487253$ |
| 2 | $2401588942037486691953546842687197025534034419779076795914305651636640306043910885265283$ | $2401622149996983401374230107638141804546309348147723592550862968900313787739719249628780$ |
| 3 | $10857116314530186402089285982444959961568722464741261314520745133824086442189130871948150$ | $10857149523759289175343039656770001362973085758815999636948089687275497149094655712550571$ |
| 4 | $31647249130660915971385091952962441303332641315090423999729841069138568879794876416340843$ | $31647282341364831967900191808499271998307170449344122262759866490750902224530972925015673$ |
| 5 | $-3716345832562412232482408968979594700652979436584027096993977000931251599453937471338397$ | $-3716312624425740059914104219172702183867920130299552067890887477608032349524897459621251$ |
| 6 | $-34669758190333507104420720764274653927930848166405445773632834527733693409468505351483940$ | $-34669724978951757762665850074709912144553018571562929495989238277731711224154272680887065$ |
| 7 | $-1667663509351990153286688627791218498798288612208587552006506569546954250725239134612435$ | $-1667630300426145307664364470295332434376490594517770387370116800701554974342114127174988$ |
| 8 | $2861958444447344633312823686766994059935154136107284368821968253232383281572893390721626$ | $2861991653177209498531608421683519074143780820339383177484903704870888049156084962366346$ |
| 9 | $-4618121575940476058243527755049840907880115457122086638006609075729315039793031081087994$ | $-4618088366297784346202925910308705930484358107835280931102309575765285119145413074158617$ |
| 10 | $-1576284401227649748692704220077387082722440926527015498271421759818601007636305809763443$ | $-1576251193525706399262703266185105026872652416145754976138488795565029158491148632921938$ |
| 11 | $-2319494640915934131891554335536576640785554656380760318574218393476541240638590557921467$ | $-2319461433696937880079636850634934283523186449049817873813231683641939394338144463759200$ |
| 12 | $3914798504098010932539173295816131020113581139877425471949681554448552750297945562876639$ | $3914831712324612608817402594564773926839881551683646012421888692802068109774631934161743$ |
| 13 | $3404690949565925967227390370071068315046050337138996818952289696602993728800869131667999$ | $3404724157769520384895707066976614409364639234640338325652170752288334265560590936985772$ |
| 14 | $967858843123443795982132543415826705310513204056127553303692983144968701746360180238421848$ | $967858876331259152705276907964119988993157401280829134165751962947761227085631242438931170$ |
| 15 | $-6438981557741974700267115608396462754387674105930047692507408767298718828891476010565$ | $-6405774794642092631687200694241588280849486466774050460475644694637849652732270636142$ |
| 16 | $11108253393781779419667843469394249475663708870967341064505437966874111333280089261061$ | $11141460295806835455964825213231127190732138587886450465624527569409909969444452075988$ |
| 17 | $1071811114331595487356461897349353426486378243994910992999022622513312107226834512601465741$ | $1071811147539522585727373632032917811376680878636034281705301299747776909956199201330174927$ |
| 18 | $121060442985902325368608967350788014818043299727220863499705624929074391390896529460$ | $154267351977615666189836808985737107825774008701770501147626478095230674101220681845$ |
| 19 | $-2245682569790599026647694304603378528182778196864685260895517068179874759838875019998218920$ | $-2245682536363248084504342328451811066294998052787848441730689458862033383116528602939011637$ |
| 20 | $2708057057420581259822796714127382540675190687570816824009361801884943288928189689311334272$ | $2708057090956476124981629622781057416968145976349242598940513141229602122257242375362375051$ |
| 21 | $1036614487612797212712995516082815790267188810910713742655616333386689808579635677923577$ | $1036647869333344858452995301215924468552153700810329012799538101290382751274361052520987$ |

| Derivative | Lower integer | Upper integer |
| --- | --- | --- |
| unused gap lambda derivative | $-7982123725586623916390407470790231995745849368171506069794937549562112401736701769768423$ | $-7981999753083359037650817040259004106845320403626939175307260957499682490898986254123572$ |
| new weight lambda derivative | $3485294826133004267416090404327648085186362502446194904029424934618817652690472613199387$ | $3485327857263336632826903844131352608155754862462209041248201479356557564247409132336511$ |
| tau6 lambda derivative | $685730734153252967186540706136001783327111745631079741852470270915416914952438654859895$ | $687085310515079589668538546702299169759202119023108686699892765316630550588005461785240$ |
| tau7 lambda derivative | $772568532087617197358989680351919738976570664890139864080280168212987367709125858744998$ | $772801574279749856720674607390569635138628025805293330107037152114588407634536086389170$ |
| point tau lambda | $752651567914760999568652998287229667385852836225036161604789274272468014476915887749910$ | $752885959147976482422110665054273252440936666806552067118373519757686635703846866672344$ |


## 16. Geometry, feasibility and independent rational margins

**Definition 16.1 (strict geometry margins).** The following dyadic data have denominator $2^{300}$. The three wedge intervals are for pairs $(3,4),(3,6),(4,6)$ in that order, where the wedge is $u_iv_j-u_jv_i$. The minimum occupied weight includes six weights at the seam and all seven at the point. All prospective contact report coordinates are included in the signed report margin.

| Root $S$ quantity | Lower integer | Upper integer |
| --- | --- | --- |
| tau | $2030881419530145481615746253871162344670097513872853385363462414066953715303449925105935901$ | $2030881419557252014395350956313019527577246398987424939891315779967904398780323161347968138$ |
| tau max | $2034843021436192786679768401410701506245864639092177711448646267029664070645598991878008791$ | $2034843021436192786681746627092256322939990310504464903283610677524357808539064561570778081$ |
| saturated wedge 0 | $-1977555491826113055012458921292179631162787905554832851025103945546535640477208664446631829$ | $-1977555491810472865732429279447696343024886184799703220025285704656591511650446375327995063$ |
| saturated wedge 1 | $-915456996804114099173105463079038582402595927722688776716897916268877152099555614544338624$ | $-915456996785848740074693999645434188771009227890810809470976619437760666531734028814502652$ |
| saturated wedge 2 | $-1986212062859487130343652484556312538983821912194033723635745470724954172515059451393715523$ | $-1986212062840032164481071998760816957324022093025035485852209350563593840377371570836503690$ |

| Root $S$ lower-bound quantity | Lower integer |
| --- | --- |
| minimum live direction squared distance lower | $33498025406126975335947606239572251713648535255584624844743498089129406942676864703211532$ |
| minimum occupied weight lower | $78933165279748779993981549241666786700309149883135545241891537148360292974711007063543900$ |
| minimum signed report coordinate lower | $1270306059510620657091656886546139230064539777770278224842938362530387296435210071855359445$ |

| Root $8$ quantity | Lower integer | Upper integer |
| --- | --- | --- |
| tau | $2030937344089645934984631239561317189403715082589951308207504479782261517451679799358816844$ | $2030937344119479857922602824089190971970825622063106208874484332455072519907837226683167882$ |
| tau max | $2034843021436192786679768401410701506245864639092177711448646267029664070645598991878008791$ | $2034843021436192786681746627092256322939990310504464903283610677524357808539064561570778081$ |
| saturated wedge 0 | $-1976918756384351562543232338362106908263568314540185427221939089837432457254474404037513065$ | $-1976918756368684178569318909836585754542876713864361542887818140750389232323745469664493975$ |
| saturated wedge 1 | $-910363500042201641715242273029185730100187929389331780619856435695961609676235452044215141$ | $-910363500023924726179545175435325643206909294606665414139068419105891889536475507890070611$ |
| saturated wedge 2 | $-1988047867167755844483323507665413554196610814744597251876355825233265067592202412637022855$ | $-1988047867148293139996355783502280268711516529106876307941419485393134270165942186947632696$ |

| Root $8$ lower-bound quantity | Lower integer |
| --- | --- |
| minimum live direction squared distance lower | $33770385066923971728431475678989400912761262880861477390353248419626771185679415779204749$ |
| minimum occupied weight lower | $252597565596036988451715605137508003868558720300717195655227259899598298020248275759763$ |
| minimum signed report coordinate lower | $1273565051810826062108159712292155828317730391909385636638622233660217171286025926163436262$ |

**Definition 16.2 (additional rational margins).** The next intervals are explicit rational endpoints, not integer pairs in the preceding scale. They enclose the same selected expressions by outward arithmetic with denominator dividing $2^{340}$; the reduced fractions retain their exact values. They supply additional margins for the minor, response, inverse map and strict weak feasible interior. They assert no source-root identity off root.

| Quantity | Lower rational | Upper rational |
| --- | --- | --- |
| S minor | $21486259309863860860877478729840986902221837365493360964723962429444611933206006231185145537690697325/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $10743129800451843174942739912247300081097976946363885349849899037064099109207437785102261999729572895/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ |
| S s | $279883169849471788458259086190279089936932908024012809549176146147223470892612674178248181453878779341/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $279883169853083084955907152670429257461662830639169927440636465625216875190425111816302144251588072849/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ |
| S T | $111605541032136668475024184372722619465950211249365439381608604338000047602053498448834285039659072583/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ | $111605541065852710069907534992381104874601518788485776010303744903759911659253750520765773430840934803/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ |
| S tau | $558244433852029969375874033283305630919465144749317596820502473963198633587726016400110452272015989419/559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944$ | $279122216929616462707897982946817868754751463667140319119429468000677688135819960826951885971658837739/279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472$ |
| 8 minor | $669789148696392231464633526992212702603927600699031359263053252202380639540878310568821439560560479/69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368$ | $21433253047994554087768774793913067512682318009246784878885203397172255122501313180508683297464319491/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ |
| 8 s | $279890877016830333566815313870734868600838086586131093165037360019479963183825832127234847364219636493/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $139945438510408622951589801161183640865548769962541945659728259704752839360947228001451389198330426969/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ |
| 8 T | $223079645557040559423074532939103104224286371905095104952629578913665315120141613692435981377838064511/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $6971238925932115165961295200586524308869765602614671040430439792903272126692149254797107729557991467/69992023193056381579920071267763883691301421788582797965624659405118495974380029543152421664737722368$ |
| 8 tau | $1116519612555784948463275283832691148329716590585455717537741117521963106661645566231358691331333566637/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ | $1116519612571689238965392736631361831033628188487815647697282026168811233103155276355437295461970495949/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ |
| unused gap derivative | $-8776439062481175125128095861447539036155409124612472681349537513006425057293938938058913610499424125/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $-2194075082392079361127093524485195294836150461850738887950053579102449068025407540362851375872093527/559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944$ |
| new weight derivative | $3832122103009420030075562380709237193237171990748101736858035908110364853412083599246210816874846917/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $1916079295111999920656408729677062219348866039400386633078153769276656793271827942532680799892831367/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ |
| Tss six | $-198386815981999992349745834641678593959306590176094187538101325465282901851375369718642516975276180052706873/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $-98994376012398256414299839738177412172001978358734233644112137056674183081354521756675302128316316949127917/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ |
| Tss seven | $-176084887672779284610563078287443677833050768816744637860569014236867675384290199324843421017974406239423029/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $-44007885304363861974631481433785856609986277878892785607342976207953453997801350076737959878114723001359819/559936185544451052639360570142111069530411374308662383724997275240947967795040236345219373317901778944$ |
| six branch tau response | $753955673598307270121287166884876087346315862573334662340734030767866351271798621794326888480466985/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $755471530311980424641238314155018754832611265050449605533539070820287594760431219505465491832148757/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ |
| seven branch tau response | $424723743910065266550742136385700273693262372070435194343440264272943718889923704476823167051864985/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ | $424852456674111805629354655985788939482716172939023446833375423005512123978491516748629299998359319/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ |
| point response tau response | $827548548571150639703584609689469252341117799694711231805886678392323259465584529550962094421019097/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $827807468487453634143470785125129678768618221403044611320755177762831127767436223199705975749833923/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ |
| point inverse map determinant | $51810979076036344245349802950524615718634608369502824827526206172586710944648774572321720724135/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ | $103654378955393788499900973884913011701436121537180887180843668834540672711588691144017806510961/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ |
| t0 | $593104635733763526973176776069569227322155432680959952771736093957393225415037251461653112326411153712445/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ | $593104635733763526976972197900947764097153184575167866761094121474123719840726252701673073225499987792627/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ |
| tau max | $1118666781383971196101166446269169457047073498171896103458986445325597749711582541800095045882443858365/1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888$ | $2237333562767942392204685560564435285104675746957976353850288155076078279608472818243475201720990493253/2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776$ |


## 17. Source correspondences

**Convention 17.1 (reference meanings).** CG supplies the original source and complete-output minimax correspondence; JR separately supplies the sharp acquired-cost and unaveraged real face; FA supplies the whole-fibre path, rigidity, capacity and endpoint-constructor interfaces; RC supplies the normalized contact dictionary and explicitly scoped previous contact results. These citations retain the exact conditional roles stated in §§1–2. The self-contained data and proofs of the present selected transition are §§3–8 and §§10–16.

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[FA]: FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md
[RC]: FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md

## 追加锚（本行以下为增补区）
