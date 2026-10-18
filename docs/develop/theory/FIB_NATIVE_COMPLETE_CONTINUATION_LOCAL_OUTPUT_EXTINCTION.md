# Complete continuation: a local output-extinction event

## 1. Conditional original experiment and statement

**Definition 1.1 (the original experiment).** Let $e_0,e_1,e_2,e_3,e_{13}$ be the standard basis of $\mathbb C^5$ and put

$$
E=\left((e_0+e_{13})/\sqrt2,(e_1+e_3)/\sqrt2,e_2\right),\qquad P=EE^*.
$$

There is one normalized unknown specimen at the already reached old live cut. Its twelve possible states are $E\rho_{y,e,n}E^*$, where

$$
p_y=(y/128,(64-y)/128,1/2),\quad a_y=(\sqrt{p_{yi}})_{i=0}^2,\quad
U_{e,n}=\operatorname{diag}(e,n,1),\quad
\rho_{y,e,n}=U_{e,n}a_ya_y^TU_{e,n}^*,
$$

$y\in\{5,16,27\}$ and $e,n\in\{\pm1\}$. Relative continuation time is $a\in[0,1]$, with absolute first-event clock $6+a$. Write $P_f=|f\rangle\langle f|$. The ideal complete stopped output has live block $EU_{e,n}\xi_y\xi_y^TU_{e,n}^*E^*$, where

$$
\xi_y=\left(\sqrt{y/128},\sqrt{y(58-y)/(128(y+6))},\sqrt{y/(2(y+6))}\right)^T,
$$

and the five separate Borel failure measures have densities $w_\ell f_y(a)P_f$ in original label order $(0,1,2,3,13)$, where

$$
w=(0,1/4,1/2,1/4,0),\qquad f_y(a)=\frac{6y}{(y+6a)^2}.
$$

The error is the maximum over all twelve histories of HALF the full stopped classical-quantum trace norm. It includes live coherences, every failure component, singular-time, wrong-support, abort and zero-target components. No source prior, conditioning on survival, acceptance division, postselection, copies, retries, history access or auxiliary specimen is supplied. Denote its original common-CPTP minimax value by $E_*$. These definitions agree with [CG, Definitions 4.2 and 13.1][CG].

**Assumption 1.2 (separate retained interfaces).** The following antecedents are retained separately.

1. The same isolated consistent source $u_*$ of CG.112–.114 exists in the nine-coordinate radius-$10^{-24}$ box of CG Proposition 13.2. At this root the positive-pivot factors in Definition 2.1 have the stipulated ranks and dictionary, and $D^*D+T^*T+S^*S+M=I_3$. A surrounding comparison box is not asserted to consist of roots or TP points.
2. CG §§13–17 supplies the original full HALF stopped-cq minimax identification $E_*=\mathcal F(x_*)$ and its precise averaged-live/preaverage consequences. It does not by itself assert the additional unaveraged equality face used below.
3. JR §§34–42 supplies the sharp worst-history JOINT acquisition cost and the unaveraged supported real equality face for error and cost optimizers. In the weak range $0\le s<s_0$, its high acquisition effect on the supported qutrit is $(1-\delta)D^*D$, every high branch has zero supported later failure, and every nonzero low live product has real coefficients up to a common phase on the null cone. The supported live map is $\Lambda_*$ and the total failure effect is $M$. This is an equality consequence for the original complex class, not an imposed real-processor restriction.
4. FA §§67–70, 77–78 and RC §75 supplies full-complex multi-Kraus actual-label double rigidity, the physical rank-two capacity, the original-law reduction of Definition 3.1, and the coherent one-high completion. Each supported nonzero low actual label has one supported live ray, one entire dimension-two fibre and its attached failure effect. No unobserved Kraus index is made into an actual label.

The necessary comparison class consists of finite original instruments, convergent countable instruments, and only the expressly stipulated measurable extension: finite-dimensional joint fibres, measurable Kraus fields, integrable effect/live-Choi fields and full-output TP decoders almost everywhere, as in CG Convention 21.3 and FA Convention 67.1. No unrestricted disintegration or infinite-dimensional implementation is assumed. All future-accessible input-bearing specimen, storage, controller, environmental and entangled shares count jointly in each acquired quantum fibre. A supported-zero full encoder remains allowed and counts if generated.

**Definition 1.3 (resource and optimization conventions).** An actual acquisition has CP encoders with total effect $I_5$ and full-output TP decoders. Its classical label is generated before continuation. A binary report is processing of this label; independent report coins, if generated, are part of the actual alphabet. The contrast is JR.20's $\mathsf V=2|\operatorname{Re}F_{01}|/\kappa$, where $F$ is the supported plus effect and $\kappa=h_0a+h_1b>0$. The JOINT cost $\mathsf W$ is the worst, over the twelve histories, of the probability of acquiring a joint fibre of dimension at least three. Its original sharp value in the weak range is

$$
\mathsf C(s)=(1-\delta)\sum_{j=0}^2h_j^2p_{27,j}.
$$

Every whole decoder fibre has a positive first-event rate $R_\alpha(a)$ with integrable operator norm. Survivor controls and terminal processing on survivors are TP. Its activity is $\sup_\alpha\int_0^1\|R_\alpha(a)\|\,da$, with the stipulated essential-supremum version. No forced terminal absorption, singular first-event mass or positive-carrier action after failure is admitted. Put $t=e^A-1$. At fixed $(s,A)$ optimize actual acquired-label TV between histories $(5,+,+)$ and $(27,+,+)$ among instruments with error $E_*$, contrast at least $s$, sharp cost $\mathsf C(s)$ and activity at most $A$; call the value $\mathcal T_A(s)$. A label's acquired mass includes both its live and eventual failure mass before an absolute value is taken.

**Theorem 1.4 (the complete selected local event).** Under Assumption 1.2, fix

$$
t=1000,\quad A=\log1001,\quad
I=[190.449003333,190.449005333].
$$

There is one event $\lambda_e$ selected by the event box and equations of §4, with

$$
190.44900433290<\lambda_e<190.44900433292.
$$

There are two analytic signed contact sections on the entire interval $I$, with the common exact event embeddings specified in §5. The seven-contact section is physical for $\lambda\le\lambda_e$ and has $p_4>0$ for $\lambda<\lambda_e$, $p_4=0$ at the event and $p_4<0$ afterwards. The six-contact section, retaining the unused stationary direction $x_4$, is physical for $\lambda\ge\lambda_e$. Its cleared unused gap is negative before, zero at and positive after the event. Signed negative weights are auxiliary and never physical acquisitions.

Choose the physical section on each side and define

$$
k(\lambda)=\sum_i p_i|u_i|,\qquad
s(\lambda)=\frac{s_0}{\sqrt\alpha}k(\lambda),\qquad
V(\lambda)=\frac{H_{\rm high}+\sum_i p_i|H_{\eta_i}(u_i,v_i)|}{2}.
$$

These represented strengths are continuous and strictly increasing through the event, analytic on each open side, and lie strictly in the weak feasible interior $0<s(\lambda)<s_{\max}(1000)<s_0$. At every represented strength,

$$
\mathcal T_{\log1001}(s(\lambda))=V(\lambda)
=\frac{H_{\rm high}+Y(\lambda)\cdot B(1000)-\lambda k(\lambda)}2.
$$

The minimum original TOTAL actual alphabet among these optimizers is $7$ supported low plus one high, hence $8$, before the event; it is $6$ supported low plus one high, hence $7$, at and after the event. Three distinct saturated physical failure lines are necessary before, and two after, the event. The event itself has

$$
\begin{aligned}
0.12520584446759&<s(\lambda_e)<0.12520584446760,\\
0.08594665979087&<V(\lambda_e)<0.08594665979089.
\end{aligned}
$$

One common original complex CP/TP chronological instrument at each chosen parameter simultaneously attains this value, count, contrast, minimax error, sharp JOINT cost, all five Borel/passive-reference maps and whole-fibre activity. The value as a function of strength is analytic on each side, continuous and $C^1$ through the event, with

$$
\frac{d\mathcal T_{\log1001}}{ds}=-\frac{\lambda\sqrt\alpha}{2s_0}.
$$

Proof. Sections 2–10 give the source, finite comparisons, global equality, fractional actual-label necessity and same-instrument construction. The theorem quantifies only the selected local interval and its represented strengths. It asserts no next-event property or connection to earlier multiplier ranges. $\square$

## 2. Original source and exact comparison coefficients

**Definition 2.1 (source reconstruction).** Write $u=(\lambda_{\rm CG},\alpha_1,\alpha_2,\beta_1,\beta_2,z_{\rm CG},\eta_0,\eta_1,\eta_2)$. Its source box has radius $10^{-24}$ in every coordinate and centers

| Coordinate | Exact rational center |
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

For the all-positive histories write $\rho_y=a_ya_y^T$ and $B_y^{\rm ideal}=\xi_y\xi_y^T$. Reconstruct the source by

$$
\begin{aligned}
v_5&=(\alpha_1,\alpha_2,-1)^T,&v_{27}&=(\beta_1,\beta_2,1)^T,\\
R_y^{\rm src}&=v_yv_y^T/(v_y^Tv_y),&
A_5^{\rm src}&=\lambda_{\rm CG}R_5^{\rm src},\quad
A_{27}^{\rm src}=(1-\lambda_{\rm CG})R_{27}^{\rm src},\\
\zeta&=(z_{\rm CG},59\lambda_{\rm CG}/128,\lambda_{\rm CG}/2),&
N^{\rm src}&=A_5^{\rm src}\odot\rho_5+A_{27}^{\rm src}\odot\rho_{27},\\
S_0&=\operatorname{diag}\zeta-N^{\rm src},\\
S_{ij}&=\begin{pmatrix}
\zeta_j-\sum_{y=5,27}(A_y^{\rm src})_{ii}p_{yj}&-N^{\rm src}_{ij}\\
-N^{\rm src}_{ij}&\zeta_i-\sum_{y=5,27}(A_y^{\rm src})_{jj}p_{yi}
\end{pmatrix},\\
H^{\rm src}&=1000\eta_0\operatorname{adj}S_0,&
Q^{01}&=\eta_1\operatorname{adj}S_{01},\quad Q^{02}=\eta_2\operatorname{adj}S_{02}.
\end{aligned}
$$

Here $\odot$ is entrywise multiplication. The original nine equations are $\Psi=(\nabla_x\mathcal L,g)=0$, with $x$ the first six coordinates,

$$
\begin{aligned}
\mathcal F(x)&=\sum_{y=5,27}\operatorname{tr}(A_y^{\rm src}B_y^{\rm ideal})-\sum_i\zeta_i+6\lambda_{\rm CG}/11,\\
g(x)&=(1000\det S_0,\det S_{01},\det S_{02}),\qquad
\mathcal L=\mathcal F+\sum_{j=0}^2\eta_jg_j.
\end{aligned}
$$

All radicals are positive. With positive pivots define

$$
\begin{aligned}
(h_0,h_1,h_2)^T&=H^{\rm src}e_0/\sqrt{H^{\rm src}_{00}},\\
(a,b)^T&=Q^{01}e_0/\sqrt{Q^{01}_{00}},\quad
(c,d)^T=Q^{02}e_0/\sqrt{Q^{02}_{00}},\\
m_1&=1-H^{\rm src}_{11}-Q^{01}_{00},\quad
m_2=1-H^{\rm src}_{22}-Q^{02}_{00},\\
D&=\operatorname{diag}(h_0,h_1,h_2),\quad
T=ae_0e_1^T+be_1e_0^T,\quad S=ce_0e_2^T+de_2e_0^T,\quad
M=\operatorname{diag}(0,m_1,m_2).
\end{aligned}
$$

At $u_*$ the retained rank identities identify these factors with the source Kraus dictionary. Off root the formulas are merely comparison expressions; one must not replace their adjugate entries by factor squares using an unproved off-root rank identity.

**Definition 2.2 (law coefficients).** Put

$$
\begin{gathered}
\theta=ab/(h_0h_1),\quad\omega=cd/(h_0h_2),\quad
\delta=\theta+\omega,\quad s_0=\sqrt\delta,\quad
\alpha=\theta/\delta,\quad\beta=\omega/\delta,\\
\Delta=\rho_{27}-\rho_5,\quad K=(D,T,S),\quad
N_{ij}=\operatorname{tr}(K_i\Delta K_j^T),\quad
G=\operatorname{diag}(s_0,1,1)N\operatorname{diag}(s_0,1,1),\\
H_{\rm high}=(1-\delta)N_{00},\quad
V_f=m_2h_1^2/b^2,\quad W_f=m_1h_2^2/d^2,\quad
\mu=\alpha V_f+\beta W_f.
\end{gathered}
$$

All amplitudes and $m_1,m_2,\theta,\omega$ are positive, $0<\delta<1$, $\alpha+\beta=1$ and $H_{\rm high}>0$. In particular $\Delta_{11}=-11/64$, $\Delta_{22}=0$ and
$\Delta_{12}=\sqrt{37}/16-\sqrt{59}/16<0$. Appendix 12 gives exact nine-coordinate dyadic enclosures for these derived source inputs. The optimization multiplier $\lambda$ is distinct from $\lambda_{\rm CG}$.

## 3. The same fractional law and eight full moments

**Definition 3.1 (original fractional atom).** An atom is $(u,v,\xi)$ with $u^2+v^2=1$ and $0\le\xi\le1$. Set

$$
\begin{gathered}
z=u/\sqrt\alpha,\quad w=v/\sqrt\beta,\quad h=(1,z,w)^T,\quad
L_h=s_0D+zT+wS,\quad n_h=(0,dw/h_2,-bz/h_1)^T,\\
\ell_h=h^TGh,\quad f_h=n_h^T\Delta n_h,\quad
c_h=\frac{h_1^2h_2^2\delta+a^2h_2^2z^2+c^2h_1^2w^2}
{h_0^2\delta+b^2z^2+d^2w^2}>0,\quad b_{\rm label}=t c_h\xi,\\
H_0=\ell_h,\qquad H_1=\ell_h+t c_h f_h,\\
\Gamma_\xi=(1,u,v,u^2,uv,\xi c_h,\xi c_hu^2,\xi c_huv),\\
B(t)=(1,0,0,\alpha,0,\mu/t,\alpha V_f/t,0).
\end{gathered}
$$

A single nonnegative coefficient law satisfies $\sum p\Gamma_\xi=B(t)$. Its contrast variable is $k=\sum p|u|$. The $p$ are coefficient weights, not acquired probabilities. Source amplitude $b$, label parameter $b_{\rm label}$, and relative clock $a$ are different quantities. For an existing actual atom the live matrix and failure effect are $\sqrt p L_h$ and $p b_{\rm label}n_hn_h^T$.

**Proposition 3.2 (all physical covariances and original objective).** The eight moments give

$$
\sum p h h^T=I_3,\qquad \sum p b_{\rm label}n_hn_h^T=M,
$$

including both cross-covariances. Under Assumption 1.2 every original competitor has this same-law representation, with

$$
k\ge\sqrt\alpha\,s/s_0,\qquad
T_{\rm actual}=\frac{H_{\rm high}+\sum p|\ell_h+t c_h\xi f_h|}{2}.
$$

Its endpoint bound is

$$
|\ell_h+t c_h\xi f_h|\le(1-\xi)|H_0|+\xi|H_1|.
$$

Proof. The first five rows give $\sum p=1$, $\sum pu=\sum pv=\sum puv=0$ and $\sum pu^2=\alpha$; the circle supplies $\sum pv^2=\beta$. Division by the positive square roots recovers every entry of $\sum phh^T$. The final three rows give $\sum pb_{\rm label}=\mu$, $\sum pb_{\rm label}z^2=V_f$ and $\sum pb_{\rm label}zw=0$. As $\alpha z^2+\beta w^2=1$, the remaining squared moment is $W_f$. Congruence by $n_h$ gives $M_{11}=d^2W_f/h_2^2=m_1$, $M_{22}=b^2V_f/h_1^2=m_2$ and the off-diagonal zero. The contrast and objective are the retained full-class reduction, with the high contribution positive. The final inequality is convexity of the absolute value within each existing atom. It is only an upper bound: endpoint splitting neither refines the acquired alphabet physically nor proves its minimum count. $\square$

## 4. Exact event and both selected systems

**Definition 4.1 (contact dictionary and charts).** For $r=1+x^2$ write $(u,v)=(U/r,V/r)$. The chart numerator pairs at bases $0,\pi,3\pi/2$ are

$$
(U,V)=(1-x^2,2x),\quad(-1+x^2,-2x),\quad(2x,-1+x^2),
$$

respectively; $\phi=\mathrm{base}+2\arctan x$. The seven indexed contacts have

| $i$ | endpoint $\eta_i$ | height sign $\epsilon_i$ | report sign $\sigma_i$ | base |
| --- | --- | --- | --- | --- |
| 0 | 0 | $+1$ | $+1$ | $0$ |
| 1 | 0 | $+1$ | $-1$ | $\pi$ |
| 2 | 0 | $-1$ | $-1$ | $\pi$ |
| 3 | 0 | $+1$ | $+1$ | $0$ |
| 4 | 1 | $+1$ | $+1$ | $0$ |
| 5 | 1 | $-1$ | $-1$ | $\pi$ |
| 6 | 1 | $-1$ | $+1$ | $3\pi/2$ |

Let $Z=U/\sqrt\alpha$, $W=V/\sqrt\beta$ and define the polynomials

$$
\begin{aligned}
D_c&=h_0^2\delta r^2+b^2Z^2+d^2W^2,\\
N_c&=h_1^2h_2^2\delta r^2+a^2h_2^2Z^2+c^2h_1^2W^2,\\
L_c&=G_{00}r^2+G_{11}Z^2+G_{22}W^2+2G_{01}rZ+2G_{02}rW+2G_{12}ZW,\\
F_c&=-\frac{11}{64}(d/h_2)^2W^2-\frac{2\Delta_{12}db}{h_1h_2}ZW.
\end{aligned}
$$

For pure and saturated sheets use respectively

$$
\begin{array}{c|c|c|c|c}
\eta&\Gamma_{\rm num}&d_\eta&H_{\rm num}&W_{\rm num}\\\hline
0&(r^2,rU,rV,U^2,UV,0,0,0)&r^2&L_c&rU\\
1&(D_cr^2,D_crU,D_crV,D_cU^2,D_cUV,N_cr^2,N_cU^2,N_cUV)&D_cr^2&D_cL_c+1000N_cF_c&D_crU
\end{array}
$$

Thus $\Gamma_\eta=\Gamma_{\rm num}/d_\eta$ and $H_\eta=H_{\rm num}/d_\eta$. Every clearing denominator is positive, as $r>0$ and $D_c>0$. For each indicated contact put

$$
P_i(x)=Y\cdot\Gamma_{{\rm num},i}(x)-\epsilon_iH_{{\rm num},i}(x)-\lambda\sigma_iW_{{\rm num},i}(x).
$$

A prime denotes ordinary formal polynomial differentiation in $x$, including all coefficient dependence when other derivatives are taken.

**Definition 4.2 (variables and equation order).** Let $O=(0,1,2,3,5,6)$. Use the following square systems, with moments in rows $0,\ldots,7$ and all contact value rows before all contact derivative rows.

| Section | Ordered variables | Ordered equations |
| --- | --- | --- |
| event $\mathsf e$ | $(x_0,\ldots,x_6,p_0,p_1,p_2,p_3,p_5,p_6,Y_0,\ldots,Y_7,\lambda)$ | $\sum_{i\in O}p_i\Gamma_i-B(1000)$; $P_i(x_i)$ for $i=0,\ldots,6$; $P'_i(x_i)$ for $i=0,\ldots,6$ |
| seven $\mathsf7$ | $(x_0,\ldots,x_6,p_0,\ldots,p_6,Y_0,\ldots,Y_7)$ | $\sum_{i=0}^6p_i\Gamma_i-B(1000)$; all seven $P_i(x_i)$; all seven $P'_i(x_i)$ |
| six $\mathsf6$ | $((x_i)_{i\in O},(p_i)_{i\in O},Y_0,\ldots,Y_7,x_4)$ | $\sum_{i\in O}p_i\Gamma_i-B(1000)$; $P_i(x_i)$ for $i\in O$; $P'_i(x_i)$ for $i\in O$; $P'_4(x_4)$ |

The event has 22 variables and $p_4=0$ identically, omitted before any inverse. Seven has 22 variables and signed $p_4$. Six has 21 variables, and $P_4(x_4)$ is not one of its equations. On the two branches $\lambda$ ranges over the entire closed interval $I$.

The exact event center $c^{\mathsf e}$ is listed in Appendix 13. Seven's center is obtained by inserting $p_4=0$ and removing the final multiplier. Six's center is the corresponding $O$-sublist followed by $Y$ and then $x_4$. Event radii are $10^{-10}$ on angles and weights, $10^{-7}$ on $Y$ and $10^{-6}$ on its multiplier. Branch radii are $10^{-8}$ on every angle and weight, including unused $x_4$, and $10^{-4}$ on $Y$. The fixed branch multiplier center is exactly $190.449004333$ and its halfwidth is $10^{-6}$. These are rational boxes, not floating-point prescriptions.

## 5. Uniform roots, shared embeddings and the transverse signs

**Definition 5.1 (directed arithmetic).** All decimal strings denote exact terminating rational numbers. For the finite comparisons use $D_{150}=2^{150}$ and intervals with integer endpoints divided by $D_{150}$. Embed a rational by floor and ceiling at this scale. Addition and negation use endpoint operations; products use the minimum and maximum of the four endpoint products, rounded outwards. Inversion is allowed only when zero is excluded, with reversed reciprocal endpoints rounded outwards. A square uses zero as lower endpoint when its argument interval crosses zero. For a nonnegative interval $[a/D_{150},b/D_{150}]$, take integer-square-root endpoints $\lfloor\sqrt{aD_{150}}\rfloor$ and $\lceil\sqrt{bD_{150}}\rceil$, again divided by $D_{150}$. Every direction is certified by integer comparisons. The source table has denominator $2^{224}$ and is embedded outwards; the preconditioners in Appendix 14 are exact rationals with denominator $2^{151}$ and need no approximate inverse interpretation.

For each system $F$ of Definition 4.2 and its box $\mathcal B=c+[-r,r]$, formally differentiate the stated equations, retaining every contact derivative as an interval expression. Let $R$ be the corresponding Appendix 14 matrix and

$$
E_{\rm def}=I-RJ(\mathcal B,I),\quad
q=\max_i\sum_j\sup|(E_{\rm def})_{ij}|\frac{r_j}{r_i},\quad
\iota=\max_i\left(\frac{\sup|(RF(c,I))_i|}{r_i}
+\sum_j\sup|(E_{\rm def})_{ij}|\frac{r_j}{r_i}\right).
$$

There is no external multiplier interval for the event system. For branch center residuals first combine the affine expression $F(c,\lambda_0)+(\lambda-\lambda_0)F_\lambda(c)$, then take its interval range; separately widening its canceling summands is unnecessary. Derivatives, matrix products and coefficient convolutions use their displayed index order. The bounds below can equivalently be established with finer directed dyadic arithmetic.

**Proposition 5.2 (finite rational comparisons).** With all source coordinates varying in Appendix 12, all three systems satisfy

| System | Strict bound for $q$ | Strict bound for $\iota$ |
| --- | --- | --- |
| $\mathsf e$ | $0.000060$ | $0.000060$ |
| $\mathsf7$ | $0.010$ | $0.040$ |
| $\mathsf6$ | $0.000172$ | $0.00925$ |

Starting with $w^{(0)}=r$, apply eight times

$$
w_i^{(j+1)}=\sup|(RF(c,I))_i|+\sum_k\sup|(E_{\rm def})_{ik}|w_k^{(j)}.
$$

The resulting root enclosures are the exact intervals in Appendix 15. Embedding the event root into either branch box has coordinate margin greater than $9.99\cdot10^{-9}$ and multiplier margin greater than $9.999\cdot10^{-7}$. Its multiplier lies strictly between the two endpoints asserted in Theorem 1.4. The implicit branch derivatives satisfy throughout $I$

$$
-0.000216<\frac{dp_4^{\mathsf7}}{d\lambda}<-0.000215,\qquad
0.000015<\frac d{d\lambda}P_4^{\mathsf6}(x_4)<0.000040.
$$

Proof. This is finite interval substitution into Definitions 2.2, 4.1–4.2 and 5.1. Appendices 12–15 give every input, preconditioner and refined enclosure. In particular the exact $q,\iota$ pairs are included in Appendix 14; comparison with the rational thresholds above is by cross multiplication. Matrix $R$ multiplies precisely the row order in Definition 4.2. One must not interleave value and derivative rows without permuting its columns.

For an explicit derivative comparison choose the rational decimal vector $v$ in Appendix 17 and bound

$$
\|X'-v\|_r\le\frac{\|R(Jv+F_\lambda)\|_r}{1-q},\qquad
\|z\|_r=\max_i|z_i|/r_i.
$$

The right side is less than $28$ on seven and $0.352$ on six. This bounds each coordinate error by $28r_i$ or $0.352r_i$. On six use stationarity, not a vanishing unused value, to obtain

$$
\frac d{d\lambda}P_4(x_4)=\Gamma_{{\rm num},4}(x_4)\cdot Y'-W_{{\rm num},4}(x_4).
$$

Direct outward evaluation gives the displayed strict signs. This derivative concerns the cleared polynomial; away from the event it is not identified with the derivative of $P_4/d_1$. To reproduce the refined intervals use the fixed defect matrix from the broad box in every width iteration. Strict containment margins follow by subtracting each embedded refined event endpoint from its branch-box endpoint, including the multiplier endpoints. No root sampling is used. $\square$

**Theorem 5.3 (sectionwise existence and identical event).** For every fixed admissible source and every multiplier in $I$, each branch has one and only one root in its stated box. The event system has one and only one root in its box. The branches are analytic, and their roots at $\lambda_e$ are the exact embeddings of the same event.

Proof. For each fixed parameter section $T(X)=X-RF(X)$ maps the closed box strictly into itself because $\iota<1$, and is a contraction in $\|\cdot\|_r$ because $q<1$. The contraction mapping theorem gives a unique fixed point in that box. The bound $\|I-RJ\|_r<1$ makes $RJ$ invertible. Since both factors are square, $R$ and $J$ are invertible, so a fixed point has $F=0$, not merely $RF=0$. Analyticity of the rational/radical equations with positive denominators and the analytic implicit-function theorem gives local analytic sections. Uniqueness identifies them on overlaps, producing the section on the whole interval, with analytic extensions about its endpoints.

Every exact fixed point satisfies the mean-value defect bound with $w^{(0)}=r$, so induction justifies all eight refinement steps. The event equations include all contact values and derivatives with $p_4=0$. Inserting that zero gives a seven root; retaining its stationary $x_4$ and removing the unused value equation gives a six root. Proposition 5.2 places both embeddings strictly inside their branch boxes and their multiplier inside $I$. Uniqueness therefore identifies precisely the same root in each branch. At this event $p_4^{\mathsf7}=P_4^{\mathsf6}(x_4)=0$. The two derivative signs show that each has its unique zero there and yield all the signs stated in Theorem 1.4. $\square$

## 6. Every half-circle, exact deflation and the unused constant

**Definition 6.1 (complete circle cases).** For each of the event, seven and six refined boxes take the eight cases ordered as

$$
(\eta,\epsilon,\sigma)=(0,+,+),(0,+,-),(0,-,+),(0,-,-),
(1,+,+),(1,+,-),(1,-,+),(1,-,-).
$$

Use base $0$ for $\sigma=+$ and base $\pi$ for $\sigma=-$, with $x\in[-1,1]$. These two closed report half-circles include both axes and cover the circle. The polynomial is the corresponding $Y\cdot\Gamma_{\rm num}-\epsilon H_{\rm num}-\lambda\sigma W_{\rm num}$. Remove the successive exact double factors indexed by

$$
[0,3],\ [1],\ [],\ [2],\ [4],\ [],\ [6],\ [5],
$$

respectively. In the seventh case the contact root in this base-zero chart is $\widehat x_6=(x_6-1)/(x_6+1)$; its denominator is positive on the box. The quotient degrees are $(0,2,4,2,6,8,6,6)$. In the six-box fifth case the meaning of this quotient is the identity

$$
P_4(x)=P_4(x_4)+(x-x_4)^2Q_4(x),
$$

with the unused constant retained. All other indicated occupied factors have zero value and derivative and are genuinely divisible.

**Proposition 6.2 (all 24 cases and 147 covering leaves).** Every quotient of Definition 6.1 is strictly positive throughout its closed chart. In each box the eight leaf counts are $(1,7,10,7,3,8,6,7)$, totaling $49$; all three boxes have $147$ leaves. Every retained Bernstein control is greater than $1/8000$. The exact power-coefficient enclosures, every leaf and every control are in Appendix 16.

Proof. Synthetic division of a polynomial $\sum_{j=0}^ma_jx^j$ by $(x-c)^2$ is obtained in descending order by

$$
b_{m-2}=a_m,\quad b_{m-3}=a_{m-1}+2cb_{m-2},\quad
b_{j-2}=a_j+2cb_{j-1}-c^2b_j,
$$

with absent higher coefficients zero. It also gives the exact residual constant and linear term. At an actual root the equations $P(c)=P'(c)=0$ prove that both remainders vanish. An interval remainder containing zero is never taken to prove this fact. Contact separation in Proposition 7.1 makes successive exact divisions legitimate. The chart change for contact 6 has nonzero derivative and positive clearing factor, so preserves its double multiplicity.

For the six unused contact only the linear Taylor term vanishes. Algebra gives $P_4=P_4(x_4)+(x-x_4)^2Q_4$ exactly, irrespective of the unused value. Thus the fifth coefficient table encloses $Q_4$, while $P_4(x_4)$ remains a separate term. The method does not delete that term.

For completeness, on a listed dyadic leaf $(l,d)$ put $L=l/2^d$, $H=(l+1)/2^d$, $y=(x+1)/2$ and $x=2(L+(H-L)t)-1$, $0\le t\le1$. If the substituted polynomial is $\sum_{j=0}^na_jt^j$, its degree-$n$ Bernstein controls are

$$
b_k=\sum_{j=0}^k\frac{\binom kj}{\binom nj}a_j,\qquad 0\le k\le n.
$$

The nonnegative Bernstein basis sums to one. Outward evaluation of the enclosed power coefficients by this formula gives the complete integer endpoint arrays in Appendix 16. Their lower endpoints all exceed $D_{150}/8000$ by integer cross multiplication. For each case the leaf intervals, in their listed order, abut exactly and run from $0$ to $1$ in $y$; this verifies coverage including the endpoints. Consequently the quotient is positive on every closed leaf. This is whole-arc positivity of exact polynomials at the roots, without a sampled gap argument. $\square$

**Theorem 6.3 (global dual inequalities and exact zero sets).** At the event, throughout the seven section, and on the physical six side,

$$
Y\cdot\Gamma_\eta(u,v)\ge |H_\eta(u,v)|+\lambda|u|\qquad(\eta=0,1)
$$

on the entire circle. The zero sets on seven are exactly the seven contacts of Definition 4.1. At the event all seven are zeros, with $p_4=0$. On six above the event they are exactly the six occupied contacts; at the event contact 4 is an additional zero. On six below the event the unused direction violates the inequality, so that section is not a physical optimum there.

Proof. Positive quotients and exact occupied double factors give nonnegativity of each polynomial on its assigned half-circle, with zeros only at its listed contacts. On the physical six side the unused constant is nonnegative by Theorem 5.3 and strictly positive above the event; the identity of Definition 6.1 handles its entire half-circle. On a report half-circle the other report sign has gap larger by $2\lambda|u|$. The two height signs handle the absolute height, including sign-changing points. At a report axis both signs agree, and positive quotients exclude additional zeros there. Dividing by the strictly positive clearing denominators proves the normalized inequalities. The negative unused value below the event proves the last statement. Strict signs at the contacts and separation exclude any merging of the pure and saturated zero sets. $\square$

## 7. Geometry, all-constraint response and strict weak feasibility

**Proposition 7.1 (strict geometry and feasibility margins).** On all refined boxes the following comparisons hold, with each old index in $O$ and every indicated pair treated simultaneously:

| Quantity | Strict comparison |
| --- | --- |
| Six old weights | $p_i>0.0442721$ |
| Signed contact height | $\epsilon_iH_i>0.0033319$ |
| Signed report | $\sigma_i u_i>0.7964$ |
| Every pairwise circle squared separation | $\|(u_i,v_i)-(u_j,v_j)\|^2>0.08907$ |
| Each prospective saturated failure-line squared wedge | $\det((u_i,v_i),(u_j,v_j))^2>0.0009307$ for $i,j\in\{4,5,6\}$ |
| Seven-column moment minor, rows $(0,1,2,3,4,5,7)$ | $-0.0008500501<\det\Gamma_{\rm minor}<-0.0008500499$ |
| Pure-column contrast tangent below | $Dk[\dot z]>0.0001701047$ |
| Seven root tube | $s_{\max}(1000)-s>2.12\cdot10^{-10}$ |
| Six root tube | $s_{\max}(1000)-s>3.61\cdot10^{-10}$ |

At the event,

$$
3.61503476520\cdot10^{-10}<s_{\max}(1000)-s(\lambda_e)
<3.61503476528\cdot10^{-10}.
$$

All occupied angular contact curvatures are strictly positive. Seven-column independence holds even on six when the unused stationary column is included, so every occupied subcollection is independent.

Proof. Substitute Appendix 15 into Definition 4.1. The coefficients, source intervals and all exact arithmetic conventions are canonical in §§2, 4–5 and the appendices. Signed heights and reports use the indicated sign metadata. Separation is computed for all 21 pairs; prospective saturated wedges use all three pairs. For the minor use interval Gaussian elimination: at each stage the pivot interval excludes zero, eliminate below it and multiply the resulting pivots with the row-permutation sign. This gives the stated interval without an assumption that interval determinant expansion is sharp. Exact double factors, separated contacts, positive quotient values and positive clearing denominators imply positive second derivative of the normalized angular gap at every contact.

For the contrast tangent use the explicit expression in Theorem 7.2. For feasibility use the scalar formula of FA Theorem 78.3, with every symbol evaluated from the same source:

$$
\begin{gathered}
u_f=V_f/\mu,\quad c_f=c_h\big|_{z^2=u_f},\quad
\nu=\mu/c_f,\quad t_0=W_f/c_f<265,\quad q=\nu/1000,\\
s_{\max}(1000)=s_0\left(q\sqrt{u_f}+\sqrt{(1-q)(1-qu_f)}\right).
\end{gathered}
$$

Capacity depends only on $z^2$ since $\alpha z^2+\beta w^2=1$. Appendix 17 gives exact enclosing geometry values at the event; direct substitution on the branch boxes gives the table. The small but strict slack is retained: none of these points is identified with the maximum-contrast boundary. Every comparison is uniform over the boxes, not merely at the decimal centers. $\square$

**Theorem 7.2 (strict strength order using all eight moments).** On both positive-weight physical open sides $dk/d\lambda>0$. The selected strengths join continuously and strictly at the common event.

Proof. Let $z=(p,\phi)$ collect occupied weights and angles and $\mathcal M(z)=\sum p_i\Gamma_i$. At a contact root set

$$
\mathcal L(z,Y,\lambda)=Y\cdot(\mathcal M(z)-B)-\sum_i p_i(|H_i|+\lambda|u_i|).
$$

Signs are fixed locally by Proposition 7.1. The contact-system Jacobian is nonsingular by §5, so $M_0=D_z\mathcal M$ has rank eight on the positive sides. For six, its twenty-equation occupied subsystem is nonsingular: the augmented system is block triangular in the final unused $x_4$, with nonzero last diagonal $P_4''(x_4)$. The angular part of $\mathcal L_{zz}$ is $\operatorname{diag}(p_i\gamma_i)$, where $\gamma_i>0$ is normalized angular gap curvature. Its weight and mixed blocks vanish by the contact value and derivative equations. If its quadratic form vanishes on $\ker M_0$, all angle variations vanish because every occupied $p_i>0$. Moment-column independence then forces all weight variations to vanish. Thus the Hessian restricted to $\ker M_0$ is positive definite.

It remains essential to show that contrast has a nonzero tangent preserving all eight moments. Use the three pure columns $0,1,2$ and write $A_i=\sqrt{p_i}(1,u_i,v_i)^T$, $J=\operatorname{diag}(1,-1,-1)$ and $S_{ij}=A_i^TJA_j$. The $S_{ij}$ are nonzero by positive weights and distinct circle points. Let $\Omega$ be skew with

$$
\Omega_{10}=1/S_{01},\quad \Omega_{20}=-1/S_{02},\quad
\Omega_{21}=1/S_{12}.
$$

Set $\dot A=A\Omega$ on these three columns and leave all other columns fixed. Skewness gives $d(AA^T)=0$; the three chosen identities make $d(A_i^TJA_i)=0$ individually. The positive first coordinates therefore give a legitimate tangent in $(p,\phi)$ preserving all first and second pure moments. The last three moments are zero on these pure columns, and every saturated coordinate was left fixed. Hence this tangent preserves the full eight-moment map, not only the contrast-free or even-moment constraints.

Put $a=x_0$ and $\rho_j=(x_0-x_j)/(1+x_0x_j)$, $j=1,2$. Substituting the charts and the signs $(+,-,-)$ into $d\sum p_i|u_i|$ gives

$$
Dk[\dot z]=\frac{2(1-a^2)}{1+a^2}(\rho_1-\rho_2)
\left(\rho_1+\rho_2-\frac{2a}{1-a^2}\right)>0.0001701047.
$$

For example the derivative can be obtained directly from $p_i=A_{0i}^2$ and $p_iu_i=A_{0i}A_{1i}$, so $d(p_i|u_i|)=\sigma_i d(A_{0i}A_{1i})$; expansion with the stated $\Omega$ yields the displayed rational expression. Its denominators exclude zero on the boxes.

Differentiate the contact KKT equations and restrict to $\ker M_0$. If $q_T$ is the restriction of $Dk$ and $H_T$ the restricted Hessian, then $H_Tz'_T=q_T$, so

$$
k_\lambda=q_T^TH_T^{-1}q_T>0.
$$

This argument is used only on positive-weight sides; it never divides by the vanishing $p_4$ at the event. Exact event embeddings give continuity there. Strict order on the two adjacent open sides and their shared limit gives strict order across the entire selected physical curve. $\square$

## 8. Global equality and minimum original actual labels

**Theorem 8.1 (global original-class bound and equality).** At every physical parameter of Theorem 1.4, the displayed contact law maximizes actual-label height TV over the entire class of Definition 1.3 at its represented strength. This includes originally fractional, complex and multi-Kraus competitors under the retained interfaces.

Proof. Take any admitted original competitor and its same fractional law of Proposition 3.2. Apply Theorem 6.3 separately at the two endpoints of each existing atom, multiply by $1-\xi$ and $\xi$, and use endpoint convexity. Because $\Gamma_\xi=(1-\xi)\Gamma_0+\xi\Gamma_1$, integration gives

$$
\begin{aligned}
\sum p|\ell_h+1000c_h\xi f_h|
&\le\sum p\big((1-\xi)|H_0|+\xi|H_1|\big)\\
&\le Y\cdot B(1000)-\lambda k\\
&\le Y\cdot B(1000)-\lambda\sqrt\alpha\,s/s_0.
\end{aligned}
$$

Every step concerns the same original law, including both covariance constraints and the attached failure mass. The last direction uses $\lambda>0$ and the original contrast inequality. It yields a bound for every original admitted time law and acquired label, not just for stationary contact candidates or endpoint-only competitors. Nonnegative slack integration is legitimate under exactly the convergence and measurability assumptions in Assumption 1.2.

On the physical selected law every weight is nonnegative, every occupied gap vanishes and every indicated height/report sign is strict. It satisfies all eight moments, and its deterministic reports give $s=s_0k/\sqrt\alpha$. Thus every inequality is equality. Theorem 9.2 constructs this same law as one common original instrument, proving attainment and the asserted global optimum. No finite-dimensional relaxation or separate optimization of marginal objectives is used. $\square$

**Theorem 8.2 (fractional actual-label necessity and sharp count).** Every optimizer at a selected strength has at least the actual counts of Theorem 1.4; the common constructor attains them. Proportional subdivisions and supported-zero labels cannot reduce these minima.

Proof. Equality in Theorem 8.1 forces the contrast inequality active and every integrated nonnegative endpoint dual slack zero. A strictly fractional actual atom, $0<\xi<1$, would require both endpoint gaps to vanish at the same circle direction. The complete pure and saturated zero sets are disjoint by §§6–7. Such an optimal actual atom is therefore impossible. This conclusion does not presume an acquired endpoint refinement; it constrains each existing fractional label itself.

Every supported optimal actual atom is consequently one of the certified endpoint rays. Merge only proportional copies of the same endpoint for the mathematical moment comparison. Before the event all seven columns are independent and their uniquely determined weights are positive. The same seven independent columns remain at the event, but their unique moment solution has $p_4=0$. An alternative optimal law cannot place positive mass at this extra zero without changing the eight moments. After the event the unused gap is strictly positive, and the six remaining independent columns give the unique merged nonnegative law. Hence the necessary supported low counts are seven before and six at/after.

The actual-label rigidity in Assumption 1.2 excludes hiding two distinct necessary rays in one arbitrary complex multi-Kraus low label. Three saturated failure lines are pairwise distinct before the event by the wedge bounds; exactly two remain afterwards. Subdividing a ray creates more labels, while a supported-zero label supplies none of the required positive endpoint moments. The positive compulsory high acquisition has effect $(1-\delta)D^*D$ on the supported input and requires at least one additional actual label. It cannot be replaced by a low label while retaining sharp cost and equality. The single counted high completion of §9 realizes this lower bound. Hidden terminal Kraus multiplicity, coefficient rank, supported low count, total actual alphabet, five failure labels and jointly acquired quantum dimension remain different notions. Neither full-instrument nor time-law uniqueness follows from uniqueness of the merged coefficient law. $\square$

**Proposition 8.3 (value regularity).** The local value in strength is continuous and $C^1$ across the event and analytic on each side, with the derivative stated in Theorem 1.4.

Proof. On each positive-weight physical side, differentiate the matching identity $2V-H_{\rm high}=Y\cdot B-\lambda k$. Differentiated moments and stationary contact equalities give $Y'\cdot B=k$. Thus $2V'=-\lambda k'$. The strictly positive $k'$ permits inversion to strength, yielding $V_s=-\lambda\sqrt\alpha/(2s_0)$. Both analytic branches have the identical event law and dual vector. Their value and first strength derivative have the same limit. This proves the asserted $C^1$ gluing. No assertion about matching second derivatives at the event is needed or made. $\square$

## 9. One common original chronological instrument

**Proposition 9.1 (physical capacity and whole qubit).** For any occupied atom let $L=L_h$, $K=\sqrt p L$ and $N=p b_{\rm label}n_hn_h^T$. The matrix $L$ has rank two, $N$ is supported on its row space and

$$
n_h^T(L^*L)^+n_h=1/c_h.
$$

If $J:\mathbb C^2\to\operatorname{ran}L^*$ is an isometry, define

$$
Q=J^*(K^*K+N)J,\quad
C=Q^{1/2}J^*E^*,\quad
B=KJQ^{-1/2},\quad
F=Q^{-1/2}J^*NJQ^{-1/2}.
$$

Then $Q\succ0$, $BC=KE^*$, $C^*FC=ENE^*$ and

$$
B^*B+F=I_2,\quad I_2-F\succ0,\qquad
\frac{f_{\max}}{1-f_{\max}}=\frac{b_{\rm label}}{c_h},
$$

where $f_{\max}$ is the only possible nonzero eigenvalue of $F$. Thus the actual capacity is $b_{\rm label}\le1000c_h$, with equality at each saturated contact. At a pure contact $F=0$. All zero weights, in particular $p_4=0$ at the event, are omitted before inverses.

Proof. The ellipse makes $\det L=0$, whereas its lower diagonal $2\times2$ minor is $\delta h_1h_2>0$. Its kernel is spanned by $(s_0,-bz/h_1,-dw/h_2)^T$, orthogonal to $n_h$. Solve $L^*x=n_h$ as

$$
x=(x_0,A_1-B_1x_0,C_1-D_1x_0)^T,
$$

where $A_1=dw/(s_0h_1h_2)$, $C_1=-bz/(s_0h_1h_2)$, $B_1=az/(s_0h_1)$ and $D_1=cw/(s_0h_2)$. The ellipse gives $A_1D_1-B_1C_1=h_0/(h_1h_2)$. Minimizing the squared norm in $x_0$ gives

$$
\min\|x\|^2=
\frac{A_1^2+C_1^2+(A_1D_1-B_1C_1)^2}{1+B_1^2+D_1^2}=1/c_h.
$$

This uses the actual live effect, not a bare projector after whitening. On its row space $K^*K$ is strictly positive, giving $Q\succ0$. The stated identities follow by multiplication, since $JJ^*$ fixes both $K^*$ and $N$. The rank-one generalized Rayleigh quotient for $N$ relative to $K^*K$ is $b_{\rm label}/c_h$. Congruence by $Q^{-1/2}$ then gives $f_{\max}/(1-f_{\max})$ as displayed. This includes the pure and axis cases without singular inverses. $\square$

**Theorem 9.2 (all common maps, clocks and resources).** At each physical selected parameter the following construction is one common original instrument on $M_5(\mathbb C)$, fixed before the unknown history. It realizes all conclusions of Theorem 1.4 simultaneously.

Proof. For every occupied low endpoint use Proposition 9.1, give it report $\operatorname{sgn}z_i=\sigma_i$ and count its entire qubit. Use the same relative-clock functions for all of them,

$$
g(a)=\frac2{(1+a)^2},\quad G_{\rm time}(a)=\frac{2a}{1+a},\quad
Z_i(a)=\sqrt{I_2-G_{\rm time}(a)F_i},\quad
R_i(a)=g(a)F_i[I_2-G_{\rm time}(a)F_i]^{-1}.
$$

On the current survivor matrix $Y$, the separate CP jump density into original failure label $\ell$ is

$$
\mathcal J_{i,\ell}(a)(Y)=w_\ell g(a)
\operatorname{tr}(F_iZ_i(a)^{-1}YZ_i(a)^{-1})P_f.
$$

The no-jump propagator from $a$ to $b$ is $\operatorname{Ad}_{Z_i(b)Z_i(a)^{-1}}$. Pullback to the initial fibre changes the jump density to $w_\ell g(a)\operatorname{tr}(F_iY)P_f$. The total loss effect is precisely $R_i(a)$, and at every cut the integrated jumps plus survivor effect are

$$
G_{\rm time}(a)F_i+I_2-G_{\rm time}(a)F_i=I_2.
$$

All expressions act on the whole qubit, and its survivor effect is at least $I_2/1001$ at every cut. Other survivor controls can be identity TP controls. Terminal survivors alone receive the isometry $EB_i(I_2-F_i)^{-1/2}$; its cumulative live matrix is $EB_i$. The whole-fibre activity is

$$
\int_0^1\|R_i(a)\|\,da=-\log(1-f_{\max,i})
=\log(1+b_{{\rm label},i}/c_{h_i})\in\{0,\log1001\}.
$$

There is no terminal absorption atom, singular first-event mass or positive-carrier operation after failure. The acquired record and failure time are retained; the absolute FIRST clock is $6+a$. The sufficient common density $g$ remains distinct from the ideal history-dependent $f_y$. Necessity did not require competing decoders to use $g$.

For the single high outcome choose fixed isometries $W_\perp:\mathbb C^2\to P^\perp$ and $J_0:\mathbb C^2\to\mathbb C^3$. Its encoder and hidden terminal decoder Kraus operators are

$$
C_H=\begin{pmatrix}\sqrt{1-\delta}\,DE^*\\W_\perp^*\end{pmatrix}:
\mathbb C^5\longrightarrow\mathbb C^3\oplus\mathbb C^2,\qquad
E[I_3\ 0],\quad EJ_0[0\ I_2].
$$

Give this one outcome report $+$ and rate zero. Both Kraus effects sum to $I_5$ on its entire dimension-five fibre. Its supported-zero complement is included in this same acquired label and dimension; it is neither a free later share nor a second acquired Kraus index.

The same eight moments imply

$$
\sum_iK_i^*K_i=\delta D^*D+T^*T+S^*S,\qquad\sum_iN_i=M.
$$

Root TP and $W_\perp W_\perp^*=I_5-P$ therefore give

$$
\sum_iC_i^*C_i+C_H^*C_H=I_5.
$$

Every acquisition is CP/TNI, their sum is TP and each full decoder is TP. For every complex $X\in M_5$ the forgotten-acquisition maps of this same construction are

$$
\begin{aligned}
\Phi^L(X)&=E[\Lambda_*(E^*XE)+J_0W_\perp^*XW_\perp J_0^*]E^*,\\
\Lambda_*(Y)&=DYD^*+TYT^*+SYS^*,\\
\Phi^f_\ell(\mathcal B)(X)&=w_\ell\left(\int_{\mathcal B}g(a)\,da\right)
\operatorname{tr}(EME^*X)P_f.
\end{aligned}
$$

The live identity follows from the full coefficient Gram, including its cross entries, so retains complex coherences. The failure identity follows from the summed attached effects and holds separately for every Borel set and all five labels, including zero labels $0$ and $13$. Tensoring the composed Kraus operators with the identity gives the passive-reference statement on any joint matrix $X$:

$$
(\Phi^f_\ell(\mathcal B)\otimes\mathrm{id}_R)(X)=
w_\ell\left(\int_{\mathcal B}g(a)\,da\right)P_f\otimes
\operatorname{Tr}_5[(EME^*\otimes I_R)X].
$$

This reference operator is conditional on the failure effect; it is not replaced by an unconditional reference marginal. Live maps likewise retain their Kraus amplification.

Every original input lies in $P$, so the complement has zero input mass on all twelve histories. The supported maps are exactly the inherited complete-output attainer: the HALF error is $E_*$ on the eight $y=5,27$ histories and smaller on the four $y=16$ histories, not twelve equal errors. Reports give actual contrast $s_0\sum p_i|z_i|=s_0k/\sqrt\alpha=s$. For each acquired low label, its height difference is $p_i(\ell_i+b_{{\rm label},i}f_i)$; live and eventual failure contributions are added inside that label. Thus its actual acquired TV is exactly the value in §8.

Only the one high fibre has dimension at least three. Its history probability is

$$
(1-\delta)\sum_jh_j^2p_{yj}>0.
$$

It is independent of both signs and strictly increases from $y=5$ to $16$ to $27$, because its slope in $y$ is $(1-\delta)(h_0^2-h_1^2)/128>0$. Its worst-history value is the retained sharp weak JOINT cost. All later-accessible input-dependent shares are already in the counted qubits or dimension-five high fibre. This constructs the sole-specimen, no-copy, no-retry, no-postselection witness with positive finite-budget survival, TP controls and no action on a failed carrier. It is an ordinary mathematical instrument existence statement; it supplies no physical access, actuator or permission. $\square$

## 10. Mathematical attribution and exact scope

**Definition 10.1 (provenance of the argument).** The source-dependent synthesis of §§4–9 is `repo-derived`: the selected zero-weight extinction, both local sections, their exact-circle certificate, response, fractional actual-label necessity and simultaneous original-class transfer. It does not constitute a new numerical experiment, an independent source isolation or a worldwide priority assertion. The contraction mapping principle, analytic implicit-function theorem, finite moment duality, positive Bernstein basis, rank-one Schur complement and Kraus/Stinespring operator methods are standard tools used inside these proofs, not additional novelty claims.

The following sources give contextual method comparisons. Their general theorems supply no unproved local numerical inequality or original actual-label conclusion here.

| Mathematical reference | Precise use and excluded transfer |
| --- | --- |
| di Dio–Schmuedgen, *The multidimensional truncated Moment Problem: The Moment Cone*, [arXiv:1809.00584v1](https://arxiv.org/abs/1809.00584v1), Theorems 19 and 52 | Finite moment representation and its connected-image refinement are standard background. The full lifted original law includes $|u|$ and absolute height; no universal seven/eight-low bound follows from the present exposed zeros. |
| Dette–Melas, *A note on the de la Garza phenomenon for locally optimal designs*, [arXiv:1105.3575v1](https://arxiv.org/abs/1105.3575v1), §3 Theorem 1 | Ordinary Chebyshev-system and information-entry hypotheses must be checked. Three zero pure-sheet coordinates do not meet an ordinary determinant premise, and Loewner dominance has no established capacity/absolute-height preservation here. |
| Mädler–Schmüdgen, *On the Truncated Matricial Moment Problem. I*, [arXiv:2310.00957v1](https://arxiv.org/abs/2310.00957v1), Theorem 5.1, Corollary 5.3 | Rank-one matrix masses and node counts are distinct from actual acquired labels. Restoring both endpoint components, absolute functions and physical covariance is a separate bridge. |
| Kye, *Faces for two qubit separable states and the convex hulls of trigonometric moment curves*, [arXiv:1302.2226v1](https://arxiv.org/abs/1302.2226v1), §4, Theorems 5.1–5.2 | Auxiliary PPT/trigonometric moment-face structure does not preserve the original contrast, absolute acquisition height or fractional capacity. Its rank/length is not used as a count proof. |
| Watrous, *Simpler semidefinite programs for completely bounded norms*, [arXiv:1207.5726v2](https://arxiv.org/abs/1207.5726v2), Theorem 6 and §3.2 | Common linear maps and passive-reference norms are contextual methods; this task retains the original twelve-input HALF stopped-cq objective. |
| [Arithmetic holographic RT II, §§57–60][RTII] | All-product witnesses, common-channel attainment and separately physical implementation are methodological parallels. Their fixed MC encoding, finite LOSR free class and diamond/trace objectives do not restrict the present general complex instrument class. Entangled-input tensorization obstructions prohibit an unsupported product-input resource reduction. |

The bibliography is contextual attribution, not a claim of a new literature search or independent authentication of retrieval provenance. The local derivation is fully determined by the canonical mathematics and rational tables in this volume and the separately named original interfaces.

**Definition 10.2 (unresolved original mathematics).** The local theorem leaves the full original programme open: the complete evaluated finite-$(s,A)$ frontier at every weak feasible point and the separate strong branch; all jointly oriented failure allocations and live decompositions; selected roots, weights, contact ranges, universal necessity, global order, connected coverage, degeneracies, gluing and one common original attainer at every point. The maximum minimum TOTAL actual alphabet remains in $\{8,9,10\}$. Universal or dense seven-original-fractional-low, universal eight-low, exclusion of actual affine coexistence, matching higher-count necessity and exact strong optimal counts remain separate open questions.

There is no connection proved below multiplier $1/4$, across the gap $(23/5,190.449003333)$, or from this selected interval to any further event. The interval is not a maximal continuation range, next-event isolation, all-budget atlas or transverse-budget cover. Other contact, sign, collision, weight, rank, capacity and count events require their own proof. Regularity of this local branch does not exclude affine regions elsewhere. Positive-level stationary directions outside its optimal zero set are not inventoried.

All remaining original $K(s)$, physical orientations, source-coefficient evaluations, coefficient gluing, transition-root isolation, multiplicities, sign intervals, next terms, critical five-label/static-contact interpolation and uniform JOINT limits beyond their published scopes remain unresolved. Previously supplied connected intervals and finite rectangles retain their own scopes.

**Definition 10.3 (source, kernel and native boundaries).** Root isolation, source approval, ranks and TP, original minimax, sharp JOINT cost, unaveraged equality face, full-class rigidity and capacity remain the separate assumptions in §1. The finite tables prove expression inequalities and selected roots conditional on that interface; a zero-containing interval does not certify the original source equations. This is ordinary conditional mathematical exposition, not a Lean/kernel assertion or a final-source/publication approval.

Actual quantum access, calibration, coherent storage, all accessible shares, acquisition duration, whole-fibre actuation, FIRST clock realization, archive/source/epoch/controller interfaces, domain permissions and a quantum-native interpretation of counts require additional bridges. Mathematical CP/TP existence, compatible modeling and empirical physical realization are distinct. The original through-2027 programme is not completed by this local theorem.

## 11. Exact table conventions

**Definition 11.1 (canonical finite mathematical data).** Appendices 12–17 are part of this source. They are rational tables, not executable algorithms, external artifacts or scientific-log references. A row $(a,b)$ denotes the closed interval $[a/D,b/D]$ with its stated denominator. Power coefficients are ordered from constant upwards; Bernstein controls are ordered $0,\ldots,n$. Preconditioner rows and columns use Definition 4.2 exactly. Every matrix row, root enclosure, polynomial coefficient and covering leaf needed by §§5–7 is specified here. Auxiliary decimal derivative vectors are exact decimal rationals; their role is only residual enclosure, not approximate proof authority.

For Appendix 16 the common denominator is $D_{150}=2^{150}$. Each leaf $(l,d)$ is the closed interval $[l/2^d,(l+1)/2^d]$ in $y=(x+1)/2$. It has its own complete array of outward Bernstein-control pairs. Equal leaf subdivisions across the three boxes are listed in each case so that the full set of 24 polynomials and 147 leaves is explicit. Appendix 15 uses the same denominator for all root endpoints. All strict comparisons use rational cross multiplication; no decimal display or Boolean diagnostic is a premise.

## 12. Exact derived-source enclosure
**Definition 12.1 (all nine dyadic source rows).** Divide each endpoint integer by $2^{224}$. These are comparison enclosures for the positive-pivot expressions of Definition 2.1 at the retained source; they assert neither independent root isolation nor TP at every point of their rectangular product. Every local finite comparison permits all nine entries to vary.

| Entry | Lower integer | Upper integer |
| --- | --- | --- |
| $h0$ | $26537788820506109500788498850443291999899441414357450708533697655768$ | $26537788820506109500793183315073538792668688684001205079732940054331$ |
| $h1$ | $19041394653590742992836842417055357808127410672381937576282066738318$ | $19041394653590742992839410055472468226237891451663919566364482743060$ |
| $h2$ | $21824004785988993361054584934895991870094398276315525145506200547608$ | $21824004785988993361057348440025413753058042469208985303844669006803$ |
| $a$ | $1770311394972945197641994965733434776804318798358636960993665423441$ | $1770311394972945197642330191383860313598676849494811590399527112584$ |
| $b$ | $3935965654294995608601979521892857651473674590095072143984588712921$ | $3935965654294995608602313422828891500221393677289956783118602628225$ |
| $c$ | $417790356983612701857377130657326048451791786364520663159403140999$ | $417790356983612701857967962172137068830255220590298423542851403047$ |
| $d$ | $2663205433690388662341049091689729175826547547021472884789707223172$ | $2663205433690388662342459064972096088182130849082266016544667607076$ |
| $m1$ | $13395056598782546673904842458375183527737029361412185934273944851861$ | $13395056598782546673906662453967195540019733666091401589339664139139$ |
| $m2$ | $9286998735773460367948153511490550124076700197961256553923028397389$ | $9286998735773460367951141007906400979909044212876537994791222399466$ |

## 13. Exact event center and branch embeddings
**Definition 13.1 (event center).** The following coordinates are exact rational decimals in event variable order. Their full precision selects a box; only the uniform contraction, not these digits by themselves, establishes a root. Branch centers and all radii are obtained by Definition 4.2.

| Coordinate | Exact center |
| --- | --- |
| $x_0$ | $0.1610355654714851316734406001956472595436365841457915452$ |
| $x_1$ | $-0.16129628698563407891684801303224262575669494233224816$ |
| $x_2$ | $0.1610470960140449125049511993201952204845287115378781705$ |
| $x_3$ | $-0.1610069900430626376196691972213427578799928216409351808$ |
| $x_4$ | $0.3197253360410397152229667347475154553695412916842876872$ |
| $x_5$ | $0.336624691694423402462509255882430688286595757611962929$ |
| $x_6$ | $0.4962746368261979945460037097745884870192616761877192394$ |
| $p_0$ | $0.2704692537619323766818705581167753660149439603905562718$ |
| $p_1$ | $0.2703266367111945486153373857076123706209207200644478793$ |
| $p_2$ | $0.1854254646139546622810891454406813026492408366281931952$ |
| $p_3$ | $0.1852328531412053364278799555661413906062918418228786831$ |
| $p_5$ | $0.04427219453854515709794476423948400161449889528635981508$ |
| $p_6$ | $0.04427359723316791889587819092930556849410374580756415559$ |
| $Y_0$ | $90.42718098123930331314242675501909306188424296808213684$ |
| $Y_1$ | $0.003305326114147188526040501685636921037482384054962535825$ |
| $Y_2$ | $0.007323534457863090409372680376905072470158234818987308295$ |
| $Y_3$ | $100.2844120085434085801810787119291944193489380120898283$ |
| $Y_4$ | $0.004966496757194354087847490247417146948890602275186671041$ |
| $Y_5$ | $-109.3246861632478614155141401666846314280854190525934095$ |
| $Y_6$ | $154.958743454870264483477214820967274260130520195617824$ |
| $Y_7$ | $-15.30793462474966578553934848809023933676274153270938846$ |
| $\lambda$ | $190.4490043329089398061046399271659928938474741811315199$ |

**Definition 13.2 (strict embedding margins).** For both event embeddings, rational lower bounds for the minimum coordinate margin and multiplier margin, respectively, are

$$
123794003924466554961708497907945091958741653937186232753770898262915719203/12379400392853802748991242240000000000000000000000000000000000000000000000000000000
$$

$$
2787339300295902814733037069408613708252206059/2787593149816327892691964784081045188247552000000000
$$


## 14. Exact preconditioning matrices and defect bounds
**Definition 14.1 (rational preconditioners).** In each table $R_{ij}=A_{ij}/2^{151}$, with zero-based row index $i$. Each row lists the entire ordered integer vector $(A_{i0},\ldots,A_{i,n-1})$. Column order is the equation order, and row order is the variable order, of Definition 4.2.

### 14.1. Matrix $\mathsf e$

| $i$ | Integer row |
| --- | --- |
| $0$ | $(2432353991280485626153251654428915540505129465,248406174956666072425815644729683810270009,-693640974772139313714278860373058717084327,-2698486671404148105501512815499240536277424759,580251666792504493313886028887011973662677,-24616356168054964265397997669627896776649243545,29785666648887946689134169318927921577749393997,-1413878291442177870489055574039624398031549,-105207960967046816288257760223697727213447507,3217579504901730378085675205161124554413721,-688201596646651553863546262242409294934899,102680148518918618407956325282000856687678731,40541943475516494015601320979381063174910973,-39545600236852121435812083402239643932341349,623632289594912155959033115446531537710447,25378797929238901380155517167614687385986497,10674567334340757762424344630180675962050791,-7342273965002493627773170674824128246041753,7346682264698630388117858307582581693918055,-5,330301772059489209487008565659414612799197,-235885446928633456387708147803000550343693)$ |
| $1$ | $(-2421628008324220844553256817261995934470003993,-247310775023774834059120183910629512696123,690582217165375489192235212826981892714911,2686587119715146309467949963135604429481248201,-577692923488416438240758929503338419894365,21492481699047088263727420908967581924556884335,-24900419172171902687336452548284287073713257797,1165788592957481443381682627609473329190701,-16185846793112848694481151443200861267584851,96055191423996332928713865699655391171729991,-89203630707428462547612574089968664924369991,9338241307674551058997074630099843267763347,102431992023656096994047083019702760191525983,-99918554750150320378231618423364295114067773,1573024227744945903153309208244059942235721,10678961587528872775979757491039697530908879,25293606109861806678106897302749745375755793,7309896644229634139716098376097877488551925,-7314285504589402880055805657568228594473403,-13,835869152168444416647233743424222902919271,-595026083829576916118891321573660242911941)$ |
| $2$ | $(2428595866512202645347386443534332648203606541,248022373338132838464851102961641664175011,-692569260154557395921603040755163584598739,-2694317356562211808791718220652294638605612599,579355145082002715125984382437220598340213,-24443610885294096711033987774963927692488170355,29527262345104976246278442385795968784057743411,-1400888737676720541626031966142628672092899,12938062841015871066104356723322482378381463,121160396571114371016546793799693972759101939,-118477846475505430182556032292280664949499695,-15619296227443481982944461856088970367574965,34099833417678100009879614367761545392103401,-33261635123178764224460912822719418809635251,524654483053665337898711137944151806486331,-10709688639611632590483027418639624653709277,10658074522836467943067289093903805278755607,28683496992536424076915788397556914307314761,7335331224232212672638394631825697433101845,-5,277757032164844915139896228475694841009623,-198445925638044641214637117390180533318691)$ |
| $3$ | $(-2432624338056317235679757709648307767548123891,-248433784346062956827885546186186426986021,693718070294332762759763426388583967363175,2698786597802133923022478528885376217253898737,-580316159529931094573568304674694128495945,24950404918915006072451538068516752079930165459,-30311318539713439874357944187921752748015637141,1440609572966543562959562646985292792043659,-117004514171059661150176206110317200200939421,-14190403163699232320817265803541932891626139,10564931306108967488769953070250321802402921,120627814559616634677774472693903523572327549,-56236260603324191291716641995557987230670295,54854647494965265354156330598711711728111263,-864760045797018139650470862424377048771933,10727453503879855800940380857946299972252927,-10675753771377696257917354896645951471332065,7343090030468626136147638450295183812142603,28757560430364000922859083983114175840563265,7,-458313052698357982826138629822918109922969,327094901104547269602326457354707039695497)$ |
| $4$ | $(-7917309325761683540394547659961332549562701,-808561801699913462483478918388478723857,2257800541359240254919512000371016587501,8783570880529064958951945872485452027498361,-1888718479815686143210351476279578371915,-95728998030589140257018477420052965029332129211,150953881433076345959899784937484947957137834543,-7680114575779858757581956699157880904216377,-1049089998304987551613553691963888962018465157,-406328334428692858809523649510590417388728995,1059805190947901575753485361782694942233013251,395609319189536583771438374060041635672533783,9129782881648438505826655139807308147825582507,-9022549709362617149875850464504249357898290773,72696969764288547180005231122288624755148969,34913967742289159651590152028901336618639,-34745703876818066818025628014858593356773,23899092954314725223908864513833304914923,-23913441964537902915573452516172017552473,80477273204265217721570143985744686394201905,37006651928050930708817580429414780815312747,-26367629880214115252971432893324419211413611)$ |
| $5$ | $(82851971757542342680723532501616264001399,8461326544707021598233239476963445099,-23627121157134150481292188773074749885,-91917106757024857921630771880192610228953,19764801867769673763035820283545385925,93642788570618759847125267579669404812502744805,-147635737718102424260376543244969594354150576135,7510977067775467446077118892330776544783503,-6590538019732761759895090560463741505337775,5413719684520350283686575451244381278546239,-4220327322571164711376610923722202935681025,5397151836421133013646876781003345678335463,7774056939538651771265169675284263972264519,-112842341330028376605003165663971449015867205,-70883518167775158035122417752826733310351057,-365362896724993408728647924119949175633,363602072094003123063886517224353006161,-250095947122200347324344834371728066717,250246104671546256166106311178033059621,-1,36280162681215915344963257438545976769038209,25772405802244740515648727843542787375950365)$ |
| $6$ | $(92750282360593756389276305461195568527123,9472199749427961852234160536200793141,-26449849200195310751741612951701812479,-102898427455373300253105656255836956786767,22126099296613705012600615348187858209,-105147709742611570369256042701355443489749622561,165773525021358140278287532801918506150556973275,-8433730341553375465268509078148090051933797,-7377908438018133295848300486663107899003543,6060495823442312356865590273493285055657945,-4724529085947383369720589000715101595473825,6041948617314285407974511178874135150567533,8702822153577080349461475225283156108487083,-126323596007183191743221816594611962848959589,-79351959620420684985519893028442643858403069,-409012738160319342518219383931192401557,407041548187454486907573533967314013943,-279974866268524065124783518917640733397,280142963118360474617632739264863490467,-1,40614547337885401190887842935270530616523889,28851430592093307841602662758738533441890283)$ |
| $7$ | $(102947466935387795680214087610971658999475797,751558780909361560648946920412880601944720247,2273367535071166263781107439278304490674336535,677359419645902143333842042838757281940288227,2394488217451303329799471742969373149087434629,24534976754183140755604537737648998319264271069,-28142143210534362986954722630388089227143486581,-9141017890057746715470625060679433624692126477,137735338351627288184864225912619358347728675,13412585705931925718207101427161444696225297,-12726815397785116747480012940677767140296391,-138420689750394671809213147968943289396144833,10236526383343385641311116445844640779231011,-1520333826474273234954720399559320476331579,5867307652864164071465277410803918368926315,-22950007067470535617931946755004448219140269,457308393741448093841675116983139222761327,1841689805690785165782802484889421993153769,-21561861012061410111127938280540692173634027,-1,-2829044211531143265205721370304186906146313,-2135732176058054774471842641831064295687271)$ |
| $8$ | $(111333195425542889601922798670389779224251089,-751194243176596592798812956477917741549578801,2271732962670623717421302822523469644595565435,667674944868004779372121007493169872482148135,-2392655782083586553574416814629634902110720335,22787658707079564347225883471898382760890847835,-25428709518766560966375172167144464188164840029,9131091505798086425898000701655004535215642659,4228014849782628892306824044995361343035231,134420055057920673951926735966256785565999477,-128222814952427893920503843987803645184411217,-10421868122713420260215769767161857021854895,88323395098795350931013366636792100124486399,-94612570419155631076096552256398458570313043,-4347950575396813843634144072535620255468633,-491135479367184129137266666787975024769931,22820118814282148423601911229096504867427211,21488558769536415678328152911882903976080399,-1817321917453290534576170269167921712834323,-11,3630360308503554456328946737462169113456033,1561091640764095482376470665576815183816761)$ |
| $9$ | $(1315145161247734302008051660947321483236039991,-752107370026999963262416181124622214026421443,-2271571087294875485590946101882835316345583547,-666744667502801137765126490401497424559040939,2392441240002733810222157256357605841860984081,-42620699521717644029784130620599580474634515995,38841264661500474021555802550630605106462598217,-28859127195947645622194116910683472699959414367,83431760007090067068314034977971079496569,-136627245072882873328438630526502934103721311,129567016787733823647923873723259660314766467,6972877547415973146416368483349871783404539,-102035361656502588370846455658548811735261417,107027984805300895176513036523122765140884135,3489744469412300321463288054459555173564861,-2652406526196207320799549037246831536610551,-25955871401888106171481328771040289730595487,-19332084076980197899698846527562543348515593,3970025880777264465705236997343875394159491,13,-3411911685305488809933231547844232983411873,-1245950758042887517399939694597328812973669)$ |
| $10$ | $(1325069562029833771437917017092024788842160401,751742832294257831375365512547756286206791187,-2273529410446980149005328634073467500078913099,-678289697262472648580210214182415054802840505,-2394273675370399205530274770141625990542798193,-44966812628422043023990482423311526364149441763,42491914886398034807708009197389108390168566033,28869053580175792282711793675534134835230453333,-142046802983968997999748823653059558749354929,-11205380886411234232175079487428704206417911,11382602021354685900756862082027461804158221,141869695084819775546193851181485081230256305,3475461433160802206639913113467800354363415,-10895389139410825482188183481135149018900835,-5009295386486354804974474229733138391442831,26093549072034785175085340656224163804179573,2678444194858855994573672202575380775890777,-3998164498930934329766034020373389024134897,19409157049421795739660608491492662381516013,-1,2610694800836937020803254479735091903727429,1820661771120349973038918684802067902910337)$ |
| $11$ | $(4103617639137064620563623432164578435013,419085365498976183214899975893416483,-1170239754323497317929078018618937417,-4552609342840580440540979036611761875641,978940969591522553506521087162834431,20124224390638016412484330438749490473267662801,-13868511588235203180696300543250770259461568899,23519776133503201504639377271714770756880258713,-326426124934725698968381220495287803225885,268138888268451218192369672321845891718825,-209030748180350852538337413459892503706177,267318290908072854165993236039812050915683,385045238508006195498620469708531685753541,-5589025979396883826210827267056085923877771,-3510825988089674938818603502115184266016285,-18096245581215873305626470454424668921,18009032804315611320282474389340460829,-12387129938187107537089560559218618541,12394567168555515520027268759481459201,-1,1796938714190740474705259370225712412146495,1276494654959311184349032224575497501741429)$ |
| $12$ | $(-4103844218307086748852819275150696614333,-419108504924611408859122410826061361,1170304369182856081909457959681915447,4552860707804867129695993731421955518301,-978995021537565679266493763772725961,20140652298239022628367569634009477616799954033,-13893815230362467330099178764829253319019435709,-23519776133471716420538283796738624968394202851,326444147486639483102434759128578634877989,-268153692827070067307609341045875819598463,209042289305012109032580145352837449174869,-267333050035740895328836812448667112864555,-385066497304879532241154885430684061130599,5589334559136724151928017704865773081682969,3511019827696350649544802219922848204717185,18097244745884218688369327420167198949,-18010027152416172014797370611401780585,12387813886824089588193181274333097191,-12395251528512894099015839463826368325,1,-1797037926694608440184663905033839889487587,-1276565132742814347892639238525987479807587)$ |
| $13$ | $(93841923469724249472034941670165123234620473887,9583684506140567403104133419464701900734231,-26761155449992671848242872145618698719411941,-104109508981736708902326011080738698427886194511,22386516396676987519944456111906340253382131,-1049609641454325372506438440624821703282965660879493,1654446343221019604853055072170545725543429292191143,-84166104112896403339658067857792614213616810015,-5416260354019246378369787286059511614728489353459,-2065073915878549581713759147630553065903011623829,5533447696978137647454028851351918837655641822343,1950517825448804968613165279964405717698380342773,49662425932529956925456923709597851944354210429533,-48443294779579228086417337855711032618255096207853,763014126201542733193052254058540433831639491857,-413826687083049587665581736523109245608048153,411832296800860433713679189855306683566677689,-283270080747905424158901381511708320361646015,283440156042982288412722931370223462879059761,-6114131,405073540946504026797429731637936375545660622059,-288619211243465370123734338224859805343516096561)$ |
| $14$ | $(-14473350421988451354983420364988305258361511,-1478102952950901777552203758048770968369,4127404535242727953454132734954069837851,16056932232851797591140625157957805779327103,-3452698799819696718843109757318427557441,138748909072720132348005026944091872875628637,-165052886826401034828753357466755395641755285,7793298330853978345142337882755056472631,713991051360444164471264528733497250490730029,-713626643616106813835402832348256363180886877,-714574258042145461557612178366083435593356467,714209855112200027957494352766652780430550309,124682824435497911294623349421546414249347,-121628640798245919689725232972385207154053,1911193042490922100923881144604561692433,63824977522545373852171676135437397561627,-63517380359464713263890541007627547645587,43689078304667464156815384100472555877309,-43715309217805951513086904114242520184473,-1,1019242776716627120135583230859314529799,-722996582039298066292697546126009138541)$ |
| $15$ | $(40414511022196251338326899964333374146442787,4127365560998289375021437046581466079031,-11525115555083264348272589185749256482719,-44836409385995565347671503386757471661139745,9641107942059089817000513073425957342061,-385735096806385035545767025995199118498690913,458205132637010548335709318167364393352786427,-21625262658492363497882350499157307915023,2160051065852074279975981696367124678661977321,2158115337159618336289160214623805658221195259,-2158141278137670799156551256205853455958918579,-2160025141424200519526849660752423405484571169,-428615054619572118081374143399897450005031,418111618215699556245282354978051646671301,-6572861770381575393033540807958777451735,-178221018794482579764058892774512735606337,177362103023409123784683949731179299056159,-121994747948001192773341670144935298915021,122067993568210056837425711587545903220363,1,-3502333023784819081778973626829866093447,2486444943180170528284471005932072360299)$ |
| $16$ | $(418580578933189983433366726416834100918381396881,42747889861703834442332739758288554006880891,-119367757256046285600835624021902792183143911,-464378999606557603098397592177908781768580438745,99854741326156392193541423685732513859215031,-1167542435311823966990985951328585922812484723113465,1839172154266899623124499434813635329205701118083231,-93550489708138011596023629868966778287709820559,-6007566951015854178223683121109864050138281589019,-2289673549828361864366685912719147854724806565235,6137559506158408162352437731495170651537114388747,2162522097235907557926211908349449379245435674623,55097086560932907528575288369521998287510429136853,-53744543254864264863578200350033309595149615764077,846512415675427670089658324368895815834901999907,-1845868113660310503280012147073029902080854309,1836972163873914074569377283936127388210461013,-1263522208516582244096830656276139067071451413,1264280826976571926761520625373759732341891557,-6783213,449401516112563665714282695956564091840497080925,-320203435628591724438945678941596094480342020917)$ |
| $17$ | $(-33806694399196749956359944740418255008037011,-3452536791000776485751371695594102336751,9640746594017704517952891195388570011099,37505607558561299050716169332679461910110977,-8064776280179482870693369194479897277421,317025797172774613956244912154410849119746817,-374394300416558752445870457642754923127460315,17637036565542135242792850325806849364489,2274805494497595012247215975380795213426988613,-2272973417316965982415865304691256326676402575,2273011821181408900815609942731084563070721355,-2274843874202408228696084967837686015126717733,625683061396573014919520451053145291976493,-610338926690943334653876326580957895537357,9602641907502196464603904053165159161385,149081687876652466533739138526437628592487,-148363205770772826643648555781047426179723,102048473626713768883666860170035734482393,-102109743508146321782388394744395583159785,-1,5108693193893866453643241396148921727675,-3632465823646227225817240041136749780185)$ |
| $18$ | $(1045444135536800173128960209091090096572913687783,106766852099052257170988232989456459030695511,-298132135307230018530348237398942943726579555,-1159829973579849314108893989744336685651880878379,249396553445054616153139506476630917283463735,1381914051088047667807359527633392174956699119823701,-2182577863270699661160435682226677683217903797386605,111082341410896286568371602226080624869840953009,7821321450799236211535915114660214966004375862029,2998624517441271931234090026294604877448561110595,-8001545627902066540966590319962679214747342819305,-2845541486195354560284502411928602568257309103387,-71467875585742177754287255903964254253130352149515,69750633184431581332238897544765084618147792883891,-902121852641276728187987287391858499842252903139,-4610228212974562409547936582592366248888319103,4588009746560013436761216292170742365081323713,-3155764862241734178424542190382195617467265515,3157659582780544790026243415426042543033126521,8798683,-537730090746871814865594395443309710914745440191,383138154851797644432383219096180407405065074309)$ |
| $19$ | $(-1198957973311405829777843823941831370418954159025,-122444580497637875104580463001429939838399869,341910092157547505415750583420134673749493061,1330140317631698851351422218256723667003777830609,-286018139186171566229942110902135238933850511,-1842373484686546863407231343498053163707757027611331,2909098938770630810939926604728681878267294145749257,-148050531987818021222791419854334140260549247249,-10559859928593896773606444357506109155550249138197,-4045311279594304785584531567917146916974966220615,10791673319971412087297574846398546599705716574411,3826848069063789696223180485571760253441021257577,96539843605831720067109697673837324290844370941479,-94034189784400769818830578049612141222987820438407,1298141955501837567396841601144694552669663159927,5287197743849741289267677057458292084081250993,-5261716700380215783460693958354851740926002029,3619159852609354674544674686457917722995499047,-3621332795399859432485737704112191616740700445,-11885389,716168791707434677378340772482585616286493308553,-510277585930274115522113806931075743780469723209)$ |
| $20$ | $(78365973716326997955930596893145082585700795,8003190262359544826372590498268539833885,-22347836948249906210550421130895018412593,-86940279384987831617916868351617052586906049,18694641911384826275222397806228909389463,-10081196655443486756703351025372497964787399591,15603084921212681539425054849137335534961125405,-790538390157532946283361952107921483088655,-8684147419511080454395293005342137782335523603,8674389081716634455986974102610992457236225167,-27418812290905059968338524291087659431576205633,27428570500133461982101788896052722114455817033,-3329419942064153698054483950457124328288797,255969836900506748384727128124185830464481902693,-162995677541342842325268034260196181088226521233,-345580419539771635942146991327564518977749,343914934320777617284962766693367513150581,-236554568381945102870354318684261970644565,236696595693496532005918327127047416567247,1,3598312309607645966365980443483050302271695,-2563853110673291041523905439102916437844429)$ |
| $21$ | $(496246568828656507438464461903712761596969751269,50679593694003508749089061838961241656271345,-141515977922483182399543278350089179682464321,-550542707399758007844352207534625406668323999573,118382398176880736361999561956746620120752881,-2214015317988677984757034513337297655327688099890349,3488733156121150158482033001056887221341149477021309,-177468726697196413977980904029715642945895341687,-11409227897291613682165882811502245636017960000065,-4349665406193347845746302256804820951946698109287,11654647213059937836058644851407224455817516470885,4106858503216843781744766498480085156272767151023,104618449539363900748585856794059685116430452470099,-102050237951873142580853454098465621876260314455561,1607359244030255554773741702083180282991538512081,-2188361725354345892046023245287666711493520663,2177815166865876516428803143525256886345828883,-1497963814310736146989631700056661807262156379,1498863191460031207480549532538156990809070697,-12879979,853324473982648741284443272074920435035489910715,-608002840633781140141196969456143694473162571819)$ |

The exact outward defect and inclusion upper bounds in this row convention are

$$
q\le 17061824216715267411179853351230773210645929/285449538541191976211657193889899027276549324800,\qquad\iota\le 17071876451777013781784577079742737210645929/285449538541191976211657193889899027276549324800.
$$

### 14.2. Matrix $\mathsf7$

| $i$ | Integer row |
| --- | --- |
| $0$ | $(2432060359090262499460348346857276723925601063,248376187524952553063629082535902922761123,-693557238885266321927074051141455598654339,-2698160911850050579754269420636451602574339357,580181619189065996044095343989715968463457,-23306309494013684165511627230701111821503292447,27721361478705958648984019319628444216724361373,-1308868938861459442130645658516670204267079,-98457049652734272546813158181758986642184083,5791303657690675745348589223638676677374945,-7584329050930495027471183125322835947451231,100250094725143335254203567219117867954467461,-21361445696672509717466248012792095597972703,20838162119025579133914110477419082562289635,-327452201340754438372786788586956599947479,25380092796514956144320417374866388406719013,10673278707518212817416835367470498565799097,-7341387610466939025954980719606548069950405,7345795377998073836262761141091436662918501,-10220977343108293079120766386121,-174615641976180071396860208945410686658455,123873626419850932985539686424326944026921)$ |
| $1$ | $(-2422012976499830687914078169538839003711727183,-247350090218983689831796935250434958684673,690691999582549637180750075214039624688919,2687014208656365097688279730293346927277890753,-577784759802686579335692964670271490650861,23210025942751441820756681666683406372542656677,-27606838365139653521214802604280384994293581751,1303461709990548726741224839224367846010607,-7335025599201554872835981690328802199111775,99429487310621932693644660317377135268546497,-98244838358750673240540520466856299699050607,6152305273448116918545318179258418519296401,21273196810580121011824172575138345987183163,-20752075033847472890626252342302825731477999,326099423423603596024228587599293305013787,10680659230741110377136742296663051437216205,25291916648235642193833865793028165033062275,7311058704448478811912554794528894468521851,-7315448262506921239926810490689117783512209,10178752211059019273388266001989,173894265899040173286196920662191629003531,-123361876901442715405145611624123731152947)$ |
| $2$ | $(2428332947084195194622381097732667484685766745,247995522472812202260560805959679847026317,-692494282709261597719804915712416492758175,-2694025670165140830999741486524112980666291399,579292424179995341498887999187794271073089,-23270589896224788234150899573570341512577346681,27678875306348433131893273522021583765352573967,-1306862946790233979393587866619797950818555,18982855613604700591337295371563924779596499,123464919387804086341037396872261080454792359,-124652666355913372378776321602520601347383701,-17795176034714202786589212889023051066522993,-21328706826167470859465186224217304879750127,20806225240741905830222078763760559802574745,-326950343209591177558839095050915158837373,-10708529210305797429324286942135465092032363,10656920681269290422374709963260627323283489,28684290637893436478836028434271671039421259,7334537102359784747348496152600034755137293,-10205312520679006666756598658431,-174348023437061004090155120731824983527135,123683775851123603463288255048377087441295)$ |
| $3$ | $(-2432256253368494128346465561771946223724030937,-248396193391091218689940328108752021996627,693613102587092126908475918589403545566959,2698378239632399028989640327956947335964475299,-580228350866226259279426664486190352058807,23308186738819534633382229895977351138734668769,-27723594341092850359856339284595578211457505779,1308974363850243099402920471628845306998001,-125467166313298494089417590241013237542133713,-17416713094494503254894975173955601965794061,19209620157345171718488166358720693178269593,123674025505947436252817822355047305164660357,21363166289243801597624007068976627597740159,-20839840562865488183288627429210210307486811,327478576513719327095859304639156802613571,10725830313929914658212554901540601483045695,-10674138404203587016072043422903206831819231,7341978934535533686063073423510754448546337,28758672193387840846507951272143490318276817,10221800608440476151695808645727,174629706678573287996122264095049066929131,-123883604023633961969124127862808599552801)$ |
| $4$ | $(-29437113084914880168817023138460522416992125,-3006289664006072725552680186551573037347,8394661257323258379736114679102332179751,32657934490217599622280379100236919720775257,-7022388186223237334870557575957434058361,282094342602548190555702509261581809517491889,-335533141546582832595613126129289073548246993,15842256061855531149118841122528717309691,-554327191268718228894538299328332101370273963,-217704469132559237579637144521823308976155329,554399740021635747918221580900641905127242013,217514810127325078186848762754033568056387061,4592988785852175768740412461097405064654146349,-4597126478057635866167193415918452296521667925,2993605202512564751243337117555281892918733,129812588401962207007918996390639257500031,-129186971505809248010405101483654691060915,88858508982261782730200589363274787645149,-88911859618249827888499175106892842618317,80477273206567368249904857273891701662923941,2113506495952674512177569140262689840875,-1499338587940992156501847265125429100255)$ |
| $5$ | $(21117184945436162156436037802149284432456887,2156610080996823407897508842128644733415,-6022044818519587730795546511717823751881,-23427692809975366848730722401774818192287421,5037622733566183470293335371591464122515,-202364898609991216243654668666279484415144001,240700077651070704239539471199764488126478049,-11364696335749607033240971410479512072333,-490191863760981982081523159518319374595983929,-178954931367665285163545219694563067759824293,489783552170443213443340317726410624178121025,179473981107541831395047815911953115212870765,4442221448958336002682428815968052166943473411,-4438431312808319571152714728325838119126887959,-2752609717869272833260958407517686354623559,-93123141155850445615374373608446328858743,92674344857454572042994835034692516336171,-63744075828457367095679887077821781102487,63782347751801435376882800200559218055201,2125504304699005163194049362289105,72449906207865103088318467313198813800319327,1075574569926144598012304355171409912335)$ |
| $6$ | $(-23525453789618320032572749072040020478055023,-2402556540268472471444416859559982480925,6708817366668591162886238264628875774647,26099459090903313903439117345997684278345707,-5612128753631863523257566973807717351417,225443215238736317609012773130131894972211341,-268150256228245618917979262394969586148007771,12660761326405342145791849913626170897635,535629317658789964917278277592796039305525399,213077111490496657509194209362477800533972303,-559412165381014346849264740087336644622236113,-189418591209282313196699262134859865191272989,-4970474962195252132724811627821418693813905207,4730623528852774594717006978582500107020717955,-155852113031137221847373680848115737445856181,103743191134188840820360842972053393365133,-103243212722481683995286222200793807476705,71013646664777015908250115121646913741965,-71056283235727650243570119567639668534291,-2378261878642273272833509909039897,1689068850321061654607081142712309357883,57788527731566327963403737949041671220693253)$ |
| $7$ | $(-39999442341246081819821247837032613715247675,751544182337327974137720728592141709324344093,2273408299628401059248578593950703563308166409,835946669192836745637319727275215271776405025,2394454116665536020571442170955126812706054407,662295853499845840679697309516698343323758369963,-1033093418073825578638952949910998191854218245223,-9089896920020178019291980570398059220659652337,3424234364657228528522572399175236788278403731,1266360747573639252372966279906175711488851227,-3369920401367593539288757191945242801410292969,-1321426813699741565501332801696170335024368565,-30125758270023651035254823990847084456280594799,29394685148389133229917667462282129751225890933,-457142515446154308450076449569411473039866305,-22319635867668118169991675795047332244819443,-170024804354387875119534525576214908370843,2273187595189632537605027186209878289674753,-21993617872692578262596460139570780413616637,-14414506260211759068727740344311567,-248634463995846698990014430820425438237404439,173003265985339141770730751487703606323293107)$ |
| $8$ | $(56416014587142168871037939986213802750966017,-751199851639378850066417213584533557962596229,2271748623551806923427047781702100560029119023,728600813822467743589520127541379289956906909,-2392668882884633135351143357003320660488317073,267801906144263474521605411344393473088236385451,-411509746000813863482153718435301025612608218311,9150731101857888232641242772652272727813039929,1266831468580312033384014528585266543919445759,615776253205859048946537641473162276404320307,-1417985624117871054029840512202775692414488537,-464907813783212714402420218328924148399265903,-11489288771219664217326604030023311483008056045,11198788179539774636923176214611183349986162065,-182226537204138482478760287123999521722763519,-248960189605700074781256703219022059263809,22579110660549385581270137968027773419711099,21654331098973061886992080358451248014771817,-1983193776549096971269607307477559315130247,-5497369507970773411648804098029609,-90802885976179927180592295458398644363198933,68845792531142110296790877474139324320542571)$ |
| $9$ | $(1461573038188027391425634632055215766821896719,-752092415958246240098990931288077246736093163,-2271612844529084825691595956009356271502373507,-829193750022099299817371720896821814702541603,2392476171192833690152624287127118704469696565,-695911992422016888045902957735609737452659967119,1068264582390431727024556827643788708164549329685,-28911493036857459593801536167153282392296015475,-3366446683675349157299632823418133548369662859,-1420086539064682547117095339654528965570963065,3568513208479935928959176279189883839072590729,1218786942040511075166861680918446912710483467,30767815269260502354704929856400328888247925569,-30005018373125011731282996558908656148914093829,477774538327214404124699761888049342687415179,-3298128192635278347766200596809069057657971,-25313261716955782286201553119468743225960229,-19774089472828964848741844905087160433748159,4412296656529676124714188854797556288642867,14721716274710292725103852521199179,248379231904804389633867232192081010040337113,-180649841335281337805446581557321763297108337)$ |
| $10$ | $(1376471778412983737293754480423692020916472229,751748081788368669760398585778558412947625631,-2273544068956229209786402616381207581435937323,-735316016740605522592660464370160539235830527,-2394261413083808975599082228574520153465811303,-274298966454549266642760659629563590337531036781,403861902852335360625800698997750215798523337549,28850671012991283452499396346269570399598979579,-1323837545771584436706850732344875624947676885,-461752460631837899628027892197367643468463275,1218594370498606174116591790811685116733053611,567266348104971737394941096914788134541808987,10840064606911495170067508207417400221205751823,-10581464019740451132773862194872230520252903687,161484203737794986936800530066008048101561339,25866874168893571054758044900784197425087131,2904026664293640847821360788780240666572931,-4153326599718993639951397972343029469183593,19564412309483288564633350347067950327223895,5186730164163386609124759354026507,90999757844219349120953568809664213053426199,-61157493728565881038495785450431651441774605)$ |
| $11$ | $(106910113545320042587362599806433214108434493,10918284289703321103123676779285838654237,-30487846603942204112296462898310502287665,-118607537173759042374674447713726122100727465,25504006326411347131994570910850068413281,-476981895534994419153716236932065394565279126473,751603902783390349739979121260214923870380106385,-38233416440556616253003494980780792792784935,-2457975382937012650369798007668885213351748731,-937080982929395475242984580185795962275018387,2510847903504121544836578097665057691578246573,884771274008249527588994654298807575540801499,22538735827088720655531467187266982121915629227,-21985446777468380622440453198399152059856909663,346285435694990228058942451841124799166979201,-471455149936522958413598073757407575048483,469183025912028219989630042735302098400579,-322717559290797758025308188528509650397585,322911318811813734533165122628397835931069,10784284523722792212377858206357285,183838079970921778830696577140233888062137789,-130986603868517845603790776109947262041808681)$ |
| $12$ | $(-107805851802129727439132158794635445853490831,-11009762304389738670777301159831616249681,30743286708393662851264741417698039643049,119601281404959180841089135438069210904897301,-25717689704072447594860012428434957008397,501120784850456679360118230658739133843070112917,-771798519941058513434205602439608249092934974707,23558331353260351403613120713415017586477189343,2478337263115371365620602402763915376784630819,945236352316583354729129925364876073492856907,-2532190258397615268666764670944493727429154223,-891950905451713332844562377638858200931116787,-22728054988701464637284102802031802951814384503,22164905030768334925259142447091454638741678459,-352710879629113391503681279716574834576190455,475405201060458933814713000351611371588307,-473114040217579574285206812993436904988563,325421423821623175845021664961709489081463,-325616806742043287211161444926040587601869,-10874869537908475670761083698635027,-183588471036784159768026267638937738269238023,133365587588776933446628949523836240946710393)$ |
| $13$ | $(929734821821326322698517680538936783157667,94949942171413839428502969089090110341,-265134996961377691831704851363596515087,-1031460483801792012010603970109729733179113,221793448638735467609199696531321766877,15974309916992152959881302645609973014257197901,-7328704010459795829516772427020214096604614265,-23520110094791388232911256167735790332837085203,-21143483968954464984043098247859204185671961,-8453370470166904403634053593623957866078663,22140801400396717869533844013910317683702137,7460968780934616063579320790364774750111355,196486326683995199819145474087030343607552379,-186449188363559728243334321695359962272790403,6535754519407105666198500879558441531532949,-4099970108406983680610383880065698833685,4080210772684953066547446179923340804641,-2806486145564861898406814913523881465609,2808171158959156662212962868727516901757,94014343494572856622552790774211,-191248711135132418036496057751891452759925,-2420707172893509277789851389066142663638135)$ |
| $14$ | $(-141720645694401842273142408296658264748281682909,-14473338846046157137256845585784265330699991,40414860327567277949009408505013011639385193,157226816014475875534474151314102424846421948383,-33808253723708999978193488529001668323250345,1358101667953956591362226910484992709921003047059,-1615374895448602060279329018200062729399949709205,76270208694235844258512467108800201409560973,-430392699334271948545634291284820188921880427,-337507714528792727451812332203469876612864373,1119994059057110912729217567459107030810661875,1039076417672389771167074160390034539921995693,1244770865074557859242244279037982335431010945,-1214278165241592474249358362818852578682301473,19081244112470850590903493759905451601959235,624963589092732465563394299501510214811017311,-621951648713029265982874456149428293817269583,427796205204958027894504830870452836168185621,-428053053953780014144635493746091584653911265,595595213448974784083764254951285,10175175725681184522193269924533851154122031,-7218344830592605555877826779140618002622183)$ |
| $15$ | $(-14473338846045728962949033797819947844909155,-1478101770748121873555708837396880505221,4127401234099796758653064010789869647075,16056919390343211334291650477855006614554893,-3452696038313751684840897652139373260273,138697262712612494079312851468872865439221053,-164971505108989856799428293946701031551182743,7789158515906364645742357776066963267697,713990785217259472054338920873878620187573371,-713626745080800895625629690243833543070057537,-714573986174059041038561005519283155504796293,714209950912933003628754720676475004857871995,127123260183008517863529174101213992431383,-124009167844177773489063798844874076696731,1948687929628716766047617206975339658683,63824926460876056690700687808188537997847,-63517329571278319088887678865290789089453,43689043375369497942554447615139396006691,-43715274240078045690850254560887177484107,60825656678979410028470222419,1039148286223625588312518522975788638727,-737179471126952954002124031286459959891)$ |
| $16$ | $(40414860327533024004384465467867612776118405,4127401234096428454098277945470572092187,-11525215167432149106779401778744886649045,-44836796910097692762517677531187004310566421,9641191270803459962403976483736424891999,-387293530536863879573413887702964877759104233,460660833545280684300056562389333413092351849,-21750181961322416466493117370905607401281,2160043034956870650160154636747669817893811299,2158112275453301497348043573469202651139818695,-2158133074493102089120342801300146613863350087,-2160022250628382833523755704128576736691867539,-354974678567738845859132162476277238958367,346278992778882166706738206367845590932089,-5441450057628582493546017539891450311057,-178222559212228944785422126625290270478423,177363636017441365910490421431719450028641,-121995802315343207874193367800646226003681,122069048568509020497670662062890338669261,-169847499955622467991727149687,-2901682417170596439406187263434392863073,2058474943399826775457721636815281107423)$ |
| $17$ | $(157226816014471879240934574626435461645707489797,16056919390343268424199358716250248945993671,-44836796910134515752989491296118308088578219,-174429572719803892617893865116916671856317240959,37507337494427865509251112805679130775648643,-1506696501628902988342866957155377857205592308993,1792118926897655672744765118761325775593895810859,-84615209103776150020323245832871976930405741,1229543020105746321316552251745972750998991051,1126009813048884345807778637968911850213343687,-489794240334080941017409534585974252784486957,-400512232624331763864576067935366403084823077,-1380965764192701452521521402960626245132030847,1347136747376332660836699077030635259697550313,-21168992299596833017607568063649447737968671,-693343124119780892929248858576243944262926151,690001636409180913459553760361883388523730341,-474602941003309957850290787350844402459856653,474887892506155138224006314176974716226724919,-660761447883674695813483877168579,-11288478639776564711229633607830079606203397,8008130142561365587507836028818518139258679)$ |
| $18$ | $(-33808253723714138069887229984573478152740363,-3452696038314379673825688274487038906101,9641191270813165246714377010927621236593,37507337494434716298176101413108210548302001,-8065148265775978302752959703950390188039,323982758812681371249027287420300169498993543,-385356728066346868077875117739782202375347861,18194685428230581128235275197460560191601,2274841344999956195984895356757030350964124149,-2272959749636094564216742076613087091063902243,2272975199513815247721303912625020438662192273,-2274856778926873700118451450771806483444351393,296947061087079394242656553220622320392059,-289672856770339906072821572385941934528617,4551937645766357556554571638510085037843,149088564184843272099137013454821267368465,-148370049026659373589629758434160811168881,102053180540935628127715361770679044224033,-102114453335798619963725318638174422679701,142082573743910386936096877885,2427345154487939877452345149087259961519,-1721976585007723671820526991061796688073)$ |
| $19$ | $(1358101667955620762171922059706306671361381158387,138697262712786618297822978574361976327493891,-387293530537668847272100049075881751045873749,-1506696501630786955297238824198374794685265642573,323982758813026765190662129711516274703600321,-13014618522687390694428795922844261311489614678491,15480054646470242610637918693340088636096551217809,-730893492161508083062369671401211934986377439,632997610968199541324546076437039195471252553581,258140777779597044270832733326114461415018510195,-658596643041607278524087523060448050609107910845,-258036954667113081339215066000866707649508911917,-5553573436631572974559045631354460616945764778995,5454419195737298355627431764345633011042144711689,110586358383048697173121495529011367392065868959,-5988993971917885810414874717554058902708981031,5960130701965721845724439429597893287351737425,-4099549059951297058039514558464973741461534407,4102010428325451292132960991566246415349643055,-2657261548451268470921413094939864923,-97508183863496532974410355277824287018365613,69173027798088715898070876326241320248591633)$ |
| $20$ | $(-1615374895451205360070824689023113043008225588335,-164971505109260462961965343940149682570990367,460660833546413918968065094534893692152094749,1792118926900587239505583160357019494975145073869,-385356728066906349173415854013157050475372063,15480054646476179961039575486445291105729461117577,-18412532909824765919349458423824230121076053833783,869350967121365491809264211082230426856634561,-985999143706463554796247168318535198740724927459,-395363059205773402715537125085747387570420459789,1011873063610510284075650956347906148094726723219,380647158101767037296875413108860811378054541449,8751039627371883667960388742884171613919572598921,-8400457159246231865642981797849097328485599086259,-50646391280337254070852770597439302572176347545,7123524504475470284824964692986673423073622941,-7089193494665750903050381427972608328111479527,4876150873210136449547765414512387563993604067,-4879078513148953261503076453983582422846029031,4187178107235556829791672662941860975,115979734699880326343006418254537785775762353,-82276883325295833446045909137868572886789807)$ |
| $21$ | $(76270208769312498289308451156180583288931097,7789158523573853245451169568285908318493,-21750181982750656605518733117952774295085,-84615209187069469018027440915504911135896607,18194685446137629939632163202751208604457,-730893492880067351936726821199054472593481361,869350967975713106167666383963958291597163449,-41046558258929610283819066896059701935179,-8635963590339831844689612438841383170178231433,8692758732736642441781633408393036034154170571,-27468032583059617278173944525667206837074075867,27411226279268544013433264679562394741318158457,-445157521379737441720171724307749803196190421,256400818845741228929285781685849571457560247371,-163002465794115661363780619851929921860961065717,-336338457648282648333567256595971738117239,334717513337790997343692470396577417591915,-230228317455860646886635553041566552477531,230366547542396658752397391881378459174291,-212997987343392833147692306317739,-5475888277704569016733337095462425621779,3884614923224843240084717414829123473641)$ |

The exact outward defect and inclusion upper bounds in this row convention are

$$
q\le 3563243542187586162990464200938617622292755/356811923176489970264571492362373784095686656,\qquad\iota\le 14092680620792408142634624446054733872292755/356811923176489970264571492362373784095686656.
$$

### 14.3. Matrix $\mathsf6$

| $i$ | Integer row |
| --- | --- |
| $0$ | $(2432161684852380146128046279487056318797041295,248386535502706305029617138005378306087815,-693586134227250093843670893808295944197357,-2698273324031633822112295715310614186351367569,580205791017085746572861892683007806157833,-23758376679055942843883972807932038783298038093,28433706043098586374797002573476801088854074257,-1345105267959610670619618159358232482793263,-100786634952868099658710679544556934196848787,4903170237795227188031048640499552788652135,-5204632977698665600586050913591313925013039,101088650785638398122284076218660990565817611,1104927480109068821706661618190543121959,745333200633645348024852218636258024197,25379645967391068042868266457074446375859117,10673723383200391800913818356586465569403137,-7341693471171386819613498994493354192058747,7346101422341201433934125260187982816006419,-380174982571085352822295044454359790127,-271012702510368018063750739253396594691,-236466652103644348740650346071)$ |
| $1$ | $(-2422113883662674208757993077133793178419232501,-247360395446938505235091715087135409132037,690720775551446048583703040486697472103289,2687126156438210120426708059179423834098518155,-577808831771506050626854454151879336058169,23660225537646228978858658714766603485610522431,-28316240075606849333610813179445221286371170237,1339548338748918968519491823427016969527763,-5015064334384071295471927684465788005548783,100313951653708739133433966257482797941398701,-100614703377910379809655789134958173163647463,5317213474657029448999465293258049565071377,-1100362778790782564676872587519248866325,-742254063310363558119400872917785730707,10681104213914442009268630562966988202754385,25291473809607670816528502205590074024287967,7311363301574292161590058987536251373368131,-7315753042512775155036234612728493395136881,378604395111394933592866832636120566283,269893088723312064843835798297543721747,235484607289526422839632319387)$ |
| $2$ | $(2428434117552937775149950315316469163017060459,248005854591100918197953727980204084135835,-692523133765810410638734055208891371223245,-2694137910062136495276311397339130175923267435,579316558961908697403937732210990484510329,-23721964236351907583473027878065146819079511703,28390128120829597755587579712889924475860349363,-1343043739549564272124298981232347137633529,16656840670672035934315459197730579399057565,122578147134443533714265239161452898931517237,-122276617440401381386618999961826419279387811,-16957905157753504051265484272302215150734611,1103234051761477379856400561714232839589,744190891845868814355959258158144910569,-10708975354612721528481092709321958428247963,10657364675434872968189609430730326107998249,28683985245955819394938804169235094003590883,7334842677654799659980075688487384823088139,-379592320718497507922107226713615695455,-270597344397499149184155987810209824847,-236098513119182561609643909811)$ |
| $3$ | $(-2432357587292059383186966353775895177130152601,-248406542202339925324819400213741288735801,693642000256500129302223186977039287779023,2698490660868404525434265753107968594493894969,-580252524641205968345330501486808178974139,23760290336352364751217359004178646862491382167,-28435996282443183337949296253763426507993587115,1345213611662772546144007465741350980462859,-123137393372907652429589094225596769890404529,-16528508138440504563154026980614063037817711,16829732407602107822571991278150001547426407,122835401902583520243024901304431970989900861,-1105016478299637802354899788107972458373,-745393234714941893216496458626539123119,10726277179044393832138500828805507982600231,-10674583115702889387471339057548314227391021,7342284819876046442965414635716088677955083,28758366124393890544450184590558273380964387,380205604386677418947297960670411432867,271034531671617501539800721561998822501,236474821041614259046279608573)$ |
| $4$ | $(45976553592749267818247823963428444715549,4695393786199123346454563852664192969,-13111258296261230672471484230472859837,-51007015220603888936740711542214055313857,10967964345799195814434008594271557609,93807309085132762003605685215554066297712738427,-147894980808777069728788222616896787554522825473,7524164531280655793112466203715210269060737,-5742733567472162806508515437437068847984461,5736937498238565660591232944158809147405741,-5086368555668709178082085507592820323530415,5091976678623690441751252602997443730694497,-105259124755829061844184089009862822000089889,-71002958881519638109862925234546465368686281,-202748666494111116085324356571580192833,201771542776967147577936347833137829321,-138784261441471545570942771040349621133,138867587680497619473146420433224480423,36216753281842304424751451135219615731321909,25817585679435474954808301359776661844717249,897155504966742457453805634641)$ |
| $5$ | $(51469364316598774092694687618847157039345,5256351650482025543093235600451119981,-14677658008492990196884341188325298163,-57100814316613338374656130139043324707457,12278305108587913858385995006445895933,-104963533991177808309638093588557646082766595127,165483310204257382168007704618380921958847486487,-8418967374083367065867131036644819564943585,-6428816937079444706358425026374749227966869,6422328412473788379568235834834395869012791,-5694036112719809466752125229198073788116691,5700314237138163755346803526443344674107839,-117834413883542921537330060880697535056126801,-79485669895224332112179322791850000311201887,-226971013854210247742972035483308927077,225877153293154001971936406357542215101,-155364792569617248330091725040027171665,155458073775788113491219416855789007269,40543562428725218960268625909834760241079491,28902008101261812547547497237387988750553363,-1006971439664230222452034063595)$ |
| $6$ | $(102898911053368197448051695177929218927679603,751558775950552158579057793102306645692966639,2273367548917977984472695363014578861068731569,677413288203247898458417748406267567167141127,2394488205868026523868744656838201062225649709,24751609922766813625965812080605953658626257553,-28483502781009393910978141822056021643697382979,-9141000525402564762981475541687382514876941993,138851688889202551157721286119742520261556055,13838184296694784295321149561352002780627381,-13867179303127319660563060769770574364405475,-138822530588257372296743190887512517806083701,8464902600352679136097861907560796053967939,5710033525960393570531487526747391783389839,-22949792944405136718605757299244316534602063,457095302623250176251474225877021703203511,1841836375881114291484386469379620041939575,-21562007670247793710073688565034682832095765,-2912538839202636609254572159478829933993363,-2076241358263920400242447938772307191687137,247587808312669393825477639729)$ |
| $7$ | $(110914242726889309252627737940067773943718395,-751194285962490908959578498694632938253476847,2271733082144500455498456174798226181314799665,668139736702305275456724754974932319940720983,-2392655882027097208515548335935193963185107887,24656825670904497692577059377579279519719450999,-28374048111519334971716138788143882444168139571,9131241332530695570982718231648028501630449067,13860175790628239992989921109924363197411905,138092229687810523736846466121249869270703207,-138062169435964964076656689680621391984817215,-13889054721173089024073289450541562035482059,-8457370009824046910316715363319609685784499,-5704952387227803366679010501332025383071085,-489287970269864589431766979998537695213833,22818280209037546664279734844291950594251767,21489823415015930898548637597082541317602739,-1818587322230325225543183772270110143514681,2909947083158409507758823084892792889546691,2074393791111342775887637512980276086422737,246410438750028975297716813827)$ |
| $8$ | $(1315629155211911508512297993497116897942924463,-752107320598712012220425823981216814936206425,-2271571225316743719914609098994371095937576953,-667281617003604693656211111037498961796719535,2392441355462205235502184310778532015169317837,-44780049566372089782032038780267109799137894351,42243859049728090930778637384282202639540542317,-28859300282872219442616248433935515290637537439,-11044095935609509886107070048315016789709065,-140869514813645279793716241439492268137064139,140933904259342899004729732414146155757586975,10978335423092998726253302030761413536496501,7497424158744006619623301318232946779937617,5057417116999298006521439406541599260681717,-2654540856048474063331996172083003422541277,-25953747358186199941213575603171241322356813,-19333545055227987836136591449006187225506653,3971487736199069284299382966244869006876051,-2579656268626538369512328297622979452043281,-1838941669355804241686697557668382098582971,-456765263570070426472303902989)$ |
| $9$ | $(1325053076545471858062368776750728983170486797,751742830610662180582488177252591573784472229,-2273529405745771828496552793775341461881159969,-678271408041430542771699439599765096533502835,-2394273679303103151406141100564155831918531769,-44893262266289547610931396073825429004104999499,42376017952500621574403843435793527295574085855,28869059475748941276770206007570467476180158649,-141667784448424461565104860333270326157240969,-11060883482506747559942730881517242939934299,10995430570455785819343707342187524020997015,141733263810966837965835027923322235617442785,-7505244593147950838464291695411815358840159,-5062692421957404697841753560919536267003755,26093621770169061005137890335528766467524517,2678371847077108550793240736945111582964177,-3998114736048539679423864054471275440736773,19409107256658771754457295409335243067478371,2582347063786657794147360410630410401761221,1840859837835872557905708261697194983431277,-458100279320132908589195496685)$ |
| $10$ | $(2277196216432892482682167915425063249565,232560558034773925740031859455169713,-649394211598691707631592964639734467,-2526352517957874229851531722348666906675,543237909714074341090510826962080147,20132373011271395761506293723874535327064019267,-13881351771737401959388954984632946369573250089,23519776786671832814749539754978984216283056867,-284434785017903171170295358975724684837355,284147708543353383424002912213348750033639,-251925346989366532767047795662104905971995,252203114576599809250477478197278245785095,-5213432970436416587041691267854395603684009,-3516741828227267806496544560161505697025011,-10042042304749641995239525681811671169,9993645852894914203098417605492051327,-6873916604932719417161772048257429281,6878043703547350773752327806219525125,1793798077645945212846838050778325918088449,1278732392184129226217047579998808964353387,210363709112307052509185467077)$ |
| $11$ | $(-2277321936241456523226228011059865176123,-232573397215637988697342483518425293,649430064740265089308810531593471805,2526492000451980991182299230712390710953,-543267902707502940012978701606433863,20132503227719044492729686148823254960710721991,-13880974337962781477776224059626227637711578463,-23519776786676400007366198826598370731385295251,284450489221005543946996765484678390405493,-284163396896561272300318269851775751781347,251939256282761064043762996265423930059869,-252217039206059388136196745859829997030817,5213720814311700035147680981594456648683721,3516935994452812838918235808321697468747683,10042596716789631155967732882057224689,-9994197582821609383363219428259189201,6874296098655390573932959383766967171,-6878423439490739815591129045521437473,-1793897116761846099472277324959006173075533,-1278802993511619918081247858235590743937295,210503586715199340676812185001)$ |
| $12$ | $(-141726550133565547898502601215059789509677283221,-14473941841807953773810408377354589098191285,40416544112473683925001854625840058422091085,157233366479762814075678681639774723156542278533,-33809662260738797566787500958645096606039675,1384444457154059084568172115008277760027061341763,-1656884527907062360689479437815511642264878092227,78381766467952300704193113501147715571679349,-294643464451526561375032735831273164101619235,-285754541027192653070939617470187264255903485,981324776942335219978310336328054779303491043,990212208402213856186654039666516802428525319,-64386163501765655944756773692055960425795,-43431941175499757118725025722619756036235,624989626650441186891708726000701921375063187,-621977560785716432873573475481156212987764763,427814028272699726898708739080613110264450373,-428070887722485413430283737296240025586038639,22153497879052014509459470088457279180005,15792410351822461946761573069728341092361,13779013995900034779196529422261)$ |
| $13$ | $(-14473941841806069806856036510311592160711611,-1478163352191807804332436414944247407779,4127573192033737764619638156880150487889,16057588362058677873593338698400308760449257,-3452839886329382761497030005405175252687,141387541975544842066135068221276305185322397,-169210710857735638344543410339126105522182123,8004803110257076040301101887503817847785,714004648720807490570817357471106188466910495,-713621459744900974712939572819441726237448591,-714588147889859936994552218734774593690863809,714204960614910112863627065371467834416104521,-6575490513819423148539471567952865331,-4435523125664217077388649215372337815,63827585568112711933745411185073960977733,-63519975863252517983886347572278470895637,43690863570985875046776678587664909423735,-43717095528539408347718672419623315994599,2262444401522106739688682713315562455,1612813045672884424539663507522717443,1372505199544321259782972671)$ |
| $14$ | $(40416544112443711723455029468337834416732645,4127573192031225808680475667489487904583,-11525695336934942505080419073497160574515,-44838664924027516949627376512630346243232467,9641592947123737102645092281761701713619,-394805775072226400839947404676954455016948291,472498247846092339053643511230639979686578205,-22352340609982726845246780801654388463247,2160004322979937072582892146899957605625210861,2158097516860660089759112353833143017414600799,-2158093529798390174265854598051457331483158429,-2160008315889498060323196939389335079794289855,18361176610890894685614332821426242973,12385604283145081856828764099102954903,-178229984413092354971822307219041308569277,177371025433400933958337918427268478597679,-122000884967850524879073814269494254579967,122074134272639463387017013924390012701381,-6317572984300755251446949149190047355,-4503564427575113215794368292638153181,-3824488613986563829291209473)$ |
| $15$ | $(157233366479758817782139104952107759955827819947,16057588362060333480916877611862336372173817,-44838664924059772747482531205942263506142025,-174436839895277539249500221701015723262310924193,37508900144607358194790671597058408597530173,-1535921551025045911009728271760934439527379213909,1838170278931765755605887006498717481657249714401,-86957800078897554607182695842619607396622453,1078940968637263527941491040328767419826103291,1068594136959971992395184109263429208465474367,-335952648665548558462837012815284730833892011,-346301612830928875166521436276315608498552905,71430887385306966543582685492950710704901,48183987526253806202913754049436240399471,-693372010541201117362753136090920139556282295,690030383615805028061128829139362992095938257,-474622714157593225045781544808755357055521897,474907677532233332430733947721990266408390523,-24577392503682986521856962210543846653369,-17520315298063255782761553810277295487595,-15286662479007092574226383594461)$ |
| $16$ | $(-33809662260748502851097901485836292950631931,-3452839886330838554143590084483854704377,9641592947133727836494034000929109715405,37508900144619347075409401660059298199673547,-8065484280173900926028937670754905688157,330266978706754400148719686257270785939803313,-395259083360209194011461206204715687680772957,18698409360736412996248564646447301313059,2274873728740190911041538282559983331703547547,-2272947403626717942359974888443322450572879107,2272942119179961934553858245800859510415977743,-2274868435757654479210470446778908022088628963,-15359679891671952740584041776145402535,-10360932804259687074403861462879361867,149094775590075771111956925703801569217919,-148376230496737108687322227899789471830741,102057432333575442899658593054911202046599,-102118707681213372460009851991280653802439,5284840987594169966999971962442143209,3767367933368529391887815443668261841,3397575677183679136820555543)$ |
| $17$ | $(1384444457154053375577401291168753526883183543783,141387541975561969038447539739849004616955791,-394805775072517559369259420492690345354715989,-1535921551025085873945124038637604071534523799773,330266978706657347305615680985358822493880747,-130543569796590043240598434591614102594087381565005,200676220988225202032735278432390043183061968636925,-10151656376290503598831544739372407743732268091,27349321760817225454334566678731545577081373151,27242820826990777844224397218393065540955206805,-39920496903739374344955794094141482094247803987,-40028177133048056170014555045351865647454694213,37176891087678171558211219946837066401656037879,195911534201322716429204824473102998791539076825,-6105161125982494080248237151239622224644095401,6075738001754361859180739377904502741310514731,-4179067080773655705391053598930113080633135225,4181576191742541344535280881475951864556158755,45200430680160460449901126210113987461889939595,-32206094288857588291197771888191169177120175233,-1252962942593160686580837076337747)$ |
| $18$ | $(-1656884527907025252249469082858604126829672405353,-169210710857753050766394423049675016611009407,472498247846434878499892941602093968319246085,1838170278931782882578199478017290181088883108343,-395259083360086450709888493654944675087400299,200676220988196657078881159234768877463672978734197,-310235268124620087295352243699446990610185755361207,15714111779198002631731156960533900242251796269,-31649257173142937940241596573302298609007808253,-31525758010918004991293068525163805484871303397,36994540234755828434831245492125502968166012195,37119972752679474269163261964571985789335957859,135758778112092493766870770702721891322507750291,-185097479992522976685047623618873588093292144797,7306574819775681826876951217577012075303919899,-7271361619965193665534254415922820598201342589,5001451341322560120171549359168032947928395933,-5004454211623133443617798361569426313961051567,-71262217125477999072274295922048358077775193599,50775453998394210583691197744686491973832429629,1926764030975752322738047298716873)$ |
| $19$ | $(78381766467798443402919411025969632344172693,8004803110242346844112376381531296336581,-22352340609955552049177659325519038698389,-86957800078729424828981933768630941309421303,18698409360694309189313738829956081876961,-10151656040857380701291855771568223249181249623,15714111250363368992808190654919361034176431163,-796186199940615313930290879873330326141045,-8684510511403859451657443271446302753871057161,8674250656201515189411057944761793409700185807,-27418441388688300295483881809427829556492060985,27428701198463091741084665393081987601968230531,255966589212412982590471530393170145846763160539,-162995626388062777512079599047459120003391608937,-345650062681012800336124459776657325158249,343984242158004710421432398178808373576465,-236602239661706182772987267231190714738611,236744296649135990920867175736493667723943,3625468839173826305524519363713500987233869,-2583202449728482501695078926320690496868481,-711110555834545717557339446159)$ |
| $20$ | $(-51223470419888037767565598971971383464332939,-5231239532002087528096127266042767223587,14607535778359964729868949541433048642631,56828016270106530430577813299662474283152489,-12219645740952678631279883890670875302589,97482421550558443604627652576657157027520309801,-153498883711448171688558433707825845841923662649,7807124531288912250894995849504616215667539,-53436038528821410656524254374968693751130921,-26744227216187955838306790403712067720658745,42734119010424055267163975828664745099944337,37214345596395762028777428294697450973540607,-116888044298676379498907942199362223045018403,-67573135321566649566894771780596626094544025,225886664308438544994081447339384358706645,-224798029422068475580443749334012038913267,154622540389715262923335806469236608461133,-154715375729532951824222383910941511368991,-37460779097454073466424704174702022950969477,26691213477269492117928524659401910874776255,80477273204370548601291843824966787898747279)$ |

The exact outward defect and inclusion upper bounds in this row convention are

$$
q\le 244615547739199772210510230440236309044939/1427247692705959881058285969449495136382746624,\qquad\iota\le 6597879253483587786559139317592040527554170411/713623846352979940529142984724747568191373312000.
$$


## 15. Refined enclosures of every exact section root
**Definition 15.1 (root endpoint tables).** Each pair is divided by $D_{150}=2^{150}$. Row indices are zero-based coordinates in Definition 4.2, including the event multiplier and six unused $x_4$. These intervals enclose the roots uniformly over their full parameter sections after eight fixed-defect image refinements.

### 15.1. Event section

| Coordinate index | Integer endpoint pair |
| --- | --- |
| $0$ | $(229837639262776694634710979475523375162083478,229837639262776694644564342178750450512366549)$ |
| $1$ | $(-230209753442284583874077686208957634279111448,-230209753442284583858199473855639384233529051)$ |
| $2$ | $(229854096203040789699306723620436902784545481,229854096203040789708475365742034876676687980)$ |
| $3$ | $(-229796855048492605700211442187562586204551939,-229796855048492605688705294952411754923887006)$ |
| $4$ | $(456327248164211610565760623886733544468862009,456327248164211611504578270523195911606863392)$ |
| $5$ | $(480446814528720897719479693101385819199828982,480446814528720897771081870996477472926098555)$ |
| $6$ | $(708306830358679276407978779638517259838045794,708306830358679276465779590025414253336955549)$ |
| $7$ | $(386026618379620744290996872857302872122980970,386026618379620744298946163040888647251502341)$ |
| $8$ | $(385823068523014650365918972799115479176680193,385823068523014650381567956300023109299929760)$ |
| $9$ | $(264648066539197401667903513393964904056486669,264648066539197401686834057336965089339477880)$ |
| $10$ | $(264373162259127229481323425203027236253635066,264373162259127229491531500707492893844765587)$ |
| $11$ | $(63187387506167973694393245775286312261391061,63187387506167973698486193225943320010758514)$ |
| $12$ | $(63189389498831881527287624726964691349869128,63189389498831881531382413532015717798016079)$ |
| $13$ | $(129061985413378050271292287922330174111035167237,129061985413378055495352271199520755846750599056)$ |
| $14$ | $(4717519070057331002435328940331026092842245,4717519070057331002529438448839623059636786)$ |
| $15$ | $(10452497657437688553422750019687549673589046,10452497657437688553704808702627983373296609)$ |
| $16$ | $(143130695653567432853197188154693585099983997546,143130695653567438649658594671028081277741523253)$ |
| $17$ | $(7088421037537273727149133430099817492867573,7088421037537273727443636345116495490738568)$ |
| $18$ | $(-156033406082298691593611750388758896432822588897,-156033406082298684145926872976146499467630619902)$ |
| $19$ | $(221164509060578342215669151801165522667667624055,221164509060578352267959024918735595520683366100)$ |
| $20$ | $(-21848214373267634295115549437022625218237748511,-21848214373267634259121837817842657532198804058)$ |
| $21$ | $(271817902012291634928136029306269014941335219983,271817902012291645933782289141985391972870478448)$ |
### 15.2. Seven section

| Coordinate index | Integer endpoint pair |
| --- | --- |
| $0$ | $(229837639261929910288768187027129794198377978,229837639263623478990507134627144031476072049)$ |
| $1$ | $(-230209753443394076209039625112725687502488305,-230209753441175091523237534951871331010152194)$ |
| $2$ | $(229854096202281953754171723145878308167510560,229854096203799625653610366216593471293722901)$ |
| $3$ | $(-229796855049553942651151584302685704537712257,-229796855047431268737765152837288636590726688)$ |
| $4$ | $(456327248102265314646533654039775509384971810,456327248226157907423805240370153946690753591)$ |
| $5$ | $(480446814468173162676502682996558325223724052,480446814589268632814058881101304966902203485)$ |
| $6$ | $(708306830290694552300509261276194116420629229,708306830426664000573249108387737396754372114)$ |
| $7$ | $(386026617968143028866098509965983801926518905,386026618791098459723844525932207717447964406)$ |
| $8$ | $(385823068364933115151370918596230703123667934,385823068681096185596116010502907885352942019)$ |
| $9$ | $(264648066117700398519525405360308543683902465,264648066960694404835212165370621449712062084)$ |
| $10$ | $(264373162111162366293092123867280561599245415,264373162407092092679762802043239568499155238)$ |
| $11$ | $(-307742928331807662028679870380284210,307742928331807662028679870380284210)$ |
| $12$ | $(63187387195834767139876343029371979120315739,63187387816501180253003095971857653151833836)$ |
| $13$ | $(63189389496143766643819717786908184416089402,63189389501519996414850320472072224731795805)$ |
| $14$ | $(129061984735818130667057486725837355393413328146,129061986090937975099587072396013574564372438147)$ |
| $15$ | $(4717519070047426531435638170262231095380124,4717519070067235473529129218908418057098907)$ |
| $16$ | $(10452497657406839889362978377195862157747415,10452497657468537217764580345119670889138240)$ |
| $17$ | $(143130694901823065217677807594350825150362330502,143130696405311806285177975231370841227363190297)$ |
| $18$ | $(7088421037501361514395525135414182444219154,7088421037573185940197244639802130539386987)$ |
| $19$ | $(-156033406981666795915062991992094175102509034650,-156033405182930579824475631372811220797944174149)$ |
| $20$ | $(221164507862731877673399924054006664723024069412,221164510258424816810228252665894453465326920743)$ |
| $21$ | $(-21848214373276145953283581102906637304297686408,-21848214373259122600953806151958645446138866161)$ |
### 15.3. Six section

| Coordinate index | Integer endpoint pair |
| --- | --- |
| $0$ | $(229837639262221748835530009020132462728867983,229837639263331640443745312634141362945582044)$ |
| $1$ | $(-230209753443683946976096208623700999076347659,-230209753440885220756180951440896019436292840)$ |
| $2$ | $(229854096202573357975236639729467394175878091,229854096203508221432545449633004385285355370)$ |
| $3$ | $(-229796855049262055332046848942754697311330091,-229796855047723156056869888197219643817108854)$ |
| $4$ | $(480446814528614007152262258201812948386646682,480446814528827788338299305896050343739280855)$ |
| $5$ | $(708306830358559615643591102841639531480821611,708306830358798937230167266822291981694179732)$ |
| $6$ | $(386026618379478982487455223810783008225296965,386026618379762506102487812087408511149186346)$ |
| $7$ | $(385823068521807487643246639995354941120965802,385823068524221813104240289103783647355644151)$ |
| $8$ | $(264648066537803050079492461999774344068997131,264648066540591753275245108731155649326967418)$ |
| $9$ | $(264373162259077605234295272361909660634913044,264373162259176853738559653548610469463487609)$ |
| $10$ | $(63187387506162679442825082259101616528024302,63187387506173267950054356742128015744125273)$ |
| $11$ | $(63189389498826586983363121576143024267773361,63189389498837176075306916682837384880111846)$ |
| $12$ | $(129061984735801170788573288211910251126366232821,129061986090954934978071270909940678831419533472)$ |
| $13$ | $(4717519070045843753345756055922111307739676,4717519070068818251619011333248537844739355)$ |
| $14$ | $(10452497657402253870015410847537501267293671,10452497657473123237112147874778031779591984)$ |
| $15$ | $(143130694901841932441706516951887860054422936652,143130696405292939061149265873833806323302584147)$ |
| $16$ | $(7088421037497579139513500491483424881233528,7088421037576968315079269283732888102372613)$ |
| $17$ | $(-156033407057383412760946643073726528356718661224,-156033405107213962978591980291178867543734547575)$ |
| $18$ | $(221164507743419899299331769191313447420472438850,221164510377736795184296407528587670767878551305)$ |
| $19$ | $(-21848214373268640822706676908217495981367838800,-21848214373266627731530710346647786769068713769)$ |
| $20$ | $(456327248039643781080370324973822417894917127,456327248288779440989968569436107038180808274)$ |

## 16. Complete quotient and Bernstein tables
**Definition 16.1 (power and leaf controls).** Every integer pair in this appendix has denominator $D_{150}=2^{150}$. The coefficient row gives the whole vector of ascending power-coefficient intervals in $x$. The subsequent rows give every leaf $(l,d)$ and its whole ordered Bernstein-control interval vector. The exact identities and the unused constant have the meanings in Definition 6.1.

### 16.1. Event box

**Definition 16.21 (case 1, event).** The signs are $(0,1,1)$, the double-factor index list is $(0,3)$, and the quotient degree is $0$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(544006524806291958486364255332446079498514454051,544006524806291980512532020139045271958311742470)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,0)$ | $((544006524806291958486364255332446079498514454051,544006524806291980512532020139045271958311742470))$ |

**Definition 16.22 (case 2, event).** The signs are $(0,1,-1)$, the double-factor index list is $(1)$, and the quotient degree is $2$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(14249452959493108175464479488025170328943088146,14249452959493131941495938299673727986684192115)$ |
| $1$ | $(-175491654854190010970983414308394228884224092154,-175491654854190003853399906466812297665823680874)$ |
| $2$ | $(544001514311139542975600053178005220637446867683,544001514311139565001767817984604413097244156102)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,1)$ | $((733742622124822655004464439132842688632213636703,733742622124822707914247170592672369968152440371),(101995280386588084517204913994041161092857434524,101995280386588163011947164181261000497793732251),(14249452959493057005545442033244854190948100028,14249452959493183111414975754454044124679180233))$ |
| $(8,4)$ | $((14249452959493057005545442033244854190948100028,14249452959493183111414975754454044124679180233),(3281224531106178566588008038145315828209433216,3281224531106310623848452201103174578039861231),(813019763830855486624324873952109037930873711,813019763830993839434550803761748986044982168))$ |
| $(36,6)$ | $((813019763830855486624324873952109037930873711,813019763830993839434550803761748986044982168),(195968572012024716633404082903807340361233835,195968572012164643331075454426392588046262403),(110168859012666156579592718787151366070350665,110168859012807678674638989841626437212820134))$ |
| $(37,6)$ | $((110168859012666156579592718787151366070350665,110168859012807678674638989841626437212820134),(24369146013307596525781354670495391779467496,24369146013450714018202525256860286379377864),(469820911833421246409079417485485140767341033,469820911833565980808804945422684382711213090))$ |
| $(19,5)$ | $((469820911833421246409079417485485140767341033,469820911833565980808804945422684382711213090),(1360724443473648546175675543115464638743088108,1360724443473796514390009785754332575374883543),(4376633890391764685690709376472027029833862010,4376633890391915973759370165088341756699663981))$ |
| $(5,3)$ | $((4376633890391764685690709376472027029833862010,4376633890391915973759370165088341756699663981),(16440271678064229243750844709898276594196957616,16440271678064393811236811682424378481998785733),(62504004110182915237785983366949852448400482452,62504004110183094461324741823798191025875667241))$ |
| $(3,2)$ | $((62504004110182915237785983366949852448400482452,62504004110183094461324741823798191025875667241),(154631468974420287225856260681053004156807532125,154631468974420495761500602106545816113629430257),(382759312416442544957826551289657461024576298719,382759312416442788312118416885444544475694232299))$ |

**Definition 16.23 (case 3, event).** The signs are $(0,-1,1)$, the double-factor index list is $()$, and the quotient degree is $4$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(393282860891526929737488730357353887419610021,393282860891548955905253536956546347216898440)$ |
| $1$ | $(69357566488072383934654838600693628250950582,69357566488072383935912679362236858642598490)$ |
| $2$ | $(-28065000421695559514825609231153522691233723178,-28065000421695537473782476605742055917042752407)$ |
| $3$ | $(44546745501545523434267180856237624089005703,44546745501545523435525021617780854480653611)$ |
| $4$ | $(544005206314042162956881675489392560642252764022,544005206314042184983049440295991753102050052441)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((516219584441248512464422117287616374125315398764,516219584441248578557803295207749312279884242189),(251258606115025392960622698338702187366115806606,251258606115025475577349170738868360059326860888),(121123986006554472692496523916469188048534584909,121123986006554578257487186421139064081394085823),(57816465412377401834769734833320164460568258829,57816465412377539526214492975312909917506841775),(27337111023663465746973576619744939930354151132,27337111023663648872968831140640867707964181874))$ |
| $(2,3)$ | $((27337111023663465746973576619744939930354151132,27337111023663648872968831140640867707964181874),(12097433829306497703075497512957327665247097283,12097433829306703546346000223304846603192851923),(5064798186315313351660076123563165164578098030,5064798186315545239229927208757353487007668009),(1989337431086073362668718142873680344364318719,1989337431086335137800329689404759626946011772),(746205237179165605093148307080540810631724546,746205237179461713326962133809654076100147876))$ |
| $(12,5)$ | $((746205237179165605093148307080540810631724546,746205237179461713326962133809654076100147876),(435422188702438665699255848132255927198576003,435422188702743357208620244910877688388681902),(239159675308357490768850148239992624170501531,239159675308671043400042728746944320003202950),(124216973146303140754926906406745707891656836,124216973146625841764819498889144424898277654),(65694219057704438606772130404574202245294499,65694219058036584998923425456253682753296412))$ |
| $(13,5)$ | $((65694219057704438606772130404574202245294499,65694219058036584998923425456253682753296412),(7171464969105736458617354402402696598932162,7171464969447328233027352023362940608315170),(5068658953962682176231044231306601585052183,5068658954314016336458435015381351423277982),(34485937853704098708899207663344941086907143,34485937854065482005189544551084594877575244),(78824299201806571502198161239640956526846496,78824299202178320767576507296733576375421116))$ |
| $(7,4)$ | $((78824299201806571502198161239640956526846496,78824299202178320767576507296733576375421116),(167501021898011517088796068392232987406725202,167501021898403998292350432788031539371112861),(315862074387660687717917136121855722038941483,315862074388075168191747771119112454540999045),(391115436938566766954171896757495091802290978,391115436939004594692615135620063565118792941),(393282860891306638302815822933164508701119319,393282860891769247339926444380735725935388009))$ |
| $(8,4)$ | $((393282860891306638302815822933164508701119319,393282860891769247339926444380735725935388009),(395450284844046509651459749108833925599947659,395450284844533899987237753141407886751983078),(324531770198620173112492840824533389634254844,324531770199133778780993006161801097807379319),(180549068295604512191170570714276312808386506,180549068296145853266166121531766213932470192),(96337701548340610333393351717103587752238265,96337701548911298305858322100917701555329347))$ |
| $(18,5)$ | $((96337701548340610333393351717103587752238265,96337701548911298305858322100917701555329347),(54232018174708659404504742218517225224164145,54232018175294020825704422385493445366758925),(27069168590014648241502395498201950638520049,27069168590615085984180293969865782052630573),(31453593095926212275123863173537875574042930,31453593096542140639173589710236519916453498),(92290592686158749432397005630969329148566615,92290592686790594480954919010292692986560668))$ |
| $(19,5)$ | $((92290592686158749432397005630969329148566615,92290592686790594480954919010292692986560668),(153127592276391286589670148088400782723090301,153127592277039048322736248310348866056667837),(270417166950944796870594965327927764936614791,270417166951608901351305611170090474333059251),(469064617703534678202199317735994604906973912,469064617704215563256933616993204551844067878),(782276106219924091007801374468109849291098366,782276106220622206562273831730863358342850447))$ |
| $(5,3)$ | $((782276106219924091007801374468109849291098366,782276106220622206562273831730863358342850447),(2035122060285481742230209601396570826827596182,2035122060286248779783634690681498584337980724),(5120992618571831897036581097509806274984339324,5120992618572675055400390892264849474137494081),(12165082128967816822519278688760363179804892689,12165082128968744074862370657355940651943421223),(27417605276526505984820984245981228217341621026,27417605276527526164709439082986014527512675880))$ |
| $(3,2)$ | $((27417605276526505984820984245981228217341621026,27417605276527526164709439082986014527512675880),(57922651571643884309424395360422958292415077700,57922651571645090344403575934246162278651185194),(121261432415412079581303838338745920898353234261,121261432415413506805638067427662240820843004565),(251435665288255647529600768147614009443575008694,251435665288257338160731834339484189432143443819),(516447393065226779068261744471778152376640116594,516447393065228783583444387464461431959485941131))$ |

**Definition 16.24 (case 4, event).** The signs are $(0,-1,-1)$, the double-factor index list is $(2)$, and the quotient degree is $2$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(14242747879531750505333030457474724190974695763,14242747879531774263575789405567881927087788261)$ |
| $1$ | $(175159251613668414215487900182828635841050830122,175159251613668421316979555656520398483487228102)$ |
| $2$ | $(544029086885474807791655807178611760801625308452,544029086885474829817823571985210953261422596871)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((383112583151338136980009281979566086509112776113,383112583151338189865911461207950199347459555010),(154887852612017825624969471032667768838664185208,154887852612017891299328446532774418567518707810),(62670393794066216217843611880422391368621921416,62670393794066300187201324853901376102933509827))$ |
| $(2,3)$ | $((62670393794066216217843611880422391368621921416,62670393794066300187201324853901376102933509827),(16561664385090411514280682304299702633600789520,16561664385090504631137764014464854870640910836),(4454752906456782297696240676840248948681239402,4454752906456885938688176424104018217187224149))$ |
| $(12,5)$ | $((4454752906456782297696240676840248948681239402,4454752906456885938688176424104018217187224149),(1428025036798374993550130269975385527451351872,1428025036798481265575779526513809053823802478),(526410787786353657340175359901974296852813203,526410787786462646439255956990830176637812826))$ |
| $(26,6)$ | $((526410787786353657340175359901974296852813203,526410787786462646439255956990830176637812826),(75603663280342989235197904865268681553543869,75603663280453336870994172229340738044818000),(156074943935928813114259324026426113912111750,156074943936040540796700719484658870996181178))$ |
| $(27,6)$ | $((156074943935928813114259324026426113912111750,156074943936040540796700719484658870996181178),(236546224591514636993320743187583546270679631,236546224591627744722407266739977003947544356),(848295910408696952856421036546604026287084728,848295910408811462142082146012102708443265539))$ |
| $(7,4)$ | $((848295910408696952856421036546604026287084728,848295910408811462142082146012102708443265539),(3295294653677426216308822209982685946352705114,3295294653677546331820781663100605526426150271),(14242747879531699351505845370584576628943720945,14242747879531825417402974492458029489118763079))$ |
| $(1,1)$ | $((14242747879531699351505845370584576628943720945,14242747879531825417402974492458029489118763079),(101822373686365884433082030655399702089671847587,101822373686366058102060517127317421190659665549),(733431086378674877306314023118826588352025282681,733431086378675120604541631747387766153623164890))$ |

**Definition 16.25 (case 5, event).** The signs are $(1,1,1)$, the double-factor index list is $(4)$, and the quotient degree is $6$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(5464341552010613754281142322821600906135450748,5464341552010623159961297630618486788283714229)$ |
| $1$ | $(27021808585481022932720906515197172101333951964,27021808585481028370306455791702952586789917782)$ |
| $2$ | $(58801239083710901925840584218078850487630337308,58801239083710911135368442037631596681243438362)$ |
| $3$ | $(103992599296583318932220125203227844088252230886,103992599296583323677867328962987161342178296715)$ |
| $4$ | $(165094669398203443754200418703787274824621516943,165094669398203450954289002656140692166144052049)$ |
| $5$ | $(14821306139855250450549474557000951031098288878,14821306139855251130078777441261070096786807396)$ |
| $6$ | $(22035493105741857872745495305414154897493839541,22035493105741858889143591108601139352077271588)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((105560029117747214128815078354150697090126122647,105560029117747251823271827157565947767064004500),(64136031016065585175429596150688418871964070469,64136031016065629235717370057830785886943093389),(38040546127229905392174710025900184618858086047,38040546127229957296431266348492287296547636404),(21968056457411955040535963967140068072640128582,21968056457412016646081913044876487402513155439),(12369379576471243782811355966256702340988386796,12369379576471317433832271731060059225191054451),(6840253761212323687922212644100540912628501090,6840253761212412358452398797416022464856034884),(3854227718419318766485712239178214842808126949,3854227718419426254574844289231345370289718491))$ |
| $(1,2)$ | $((3854227718419318766485712239178214842808126949,3854227718419426254574844289231345370289718491),(868201675626313845049211834255888772987752809,868201675626440150697289781046668275723402097),(425275405299224097065354346567398061706890234,425275405299373018322053698321350846925788876),(998997614222173533151318014619373764213194712,998997614222349692081686086342361332678500582),(1940727439158858105620132694574624502276336816,1940727439159067142471230645310616530270079276),(3212524169887075243553202848906493649662565620,3212524169887324062103623578958583654079610148),(5464341552010469917134478899200312687882613368,5464341552010766997107961054239775006536551730))$ |
| $(1,1)$ | $((5464341552010469917134478899200312687882613368,5464341552010766997107961054239775006536551730),(9967976316257259264297030999787950764322708863,9967976316257652867116636004802157711450434893),(18391693686084758754052406684223388404098080133,18391693686085282798613089121897437330953960895),(35935123626322128147872209325189277459294585127,35935123626322829160630089741153712284482797988),(78804207395012087864868777641160079505909812525,78804207395013029978458966609735802400278587879),(176681415233386793040488668986048573227786031219,176681415233388065138394166596409078386103512517),(397231457161585565457951637944266516698036980431,397231457161587291481621404510204430652032133958))$ |

**Definition 16.26 (case 6, event).** The signs are $(1,1,-1)$, the double-factor index list is $()$, and the quotient degree is $8$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(558786381300436182181257002431059271063802233,558786381300437198579352805618043725647234280)$ |
| $1$ | $(-730695263728591666677601492066723128728174874,-730695263728591666073839497835243374256603624)$ |
| $2$ | $(-5802348656013909353984695979682740140145844206,-5802348656013902494750831701056138714508173019)$ |
| $3$ | $(62200502739423281002689236813518824894365654,62200502739423281054375078239352218394164537)$ |
| $4$ | $(9179787017594049650801353476850625759574977670,9179787017594056494378936758617547817962779315)$ |
| $5$ | $(-51886415168830606433857360286633167291757045,-51886415168830606382176343332524865395337419)$ |
| $6$ | $(157868229368039399342745350412160929022329923877,157868229368039406201979233286757252092482798359)$ |
| $7$ | $(731891667064467769141715784408834271849823303,731891667064467769745477584237191071899581291)$ |
| $8$ | $(22035295162681198466183933521617924445742582300,22035295162681199482582030045108701624111373432)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((183828238782694705509583361612069023307923637089,183828238782694728105735775026176409744971755329),(112310334255823602101308828249195990059287534036,112310334255823630346499347183422318119929120829),(67750024516098312521616057641669055147454331348,67750024516098348016574192589194046410466996694),(40319406171012131342145518701971597730002101494,40319406171012176182018149698250502961751550433),(23667644678642689485890962594766354294068734912,23667644678642746421761395156033372377176374583),(13712342613988338928264753703338313791974942641,13712342613988411583407504330610240040990238706),(7860446580535375390354984717649109694257875707,7860446580535468550937572148222035311496634118),(4487256761553769797722506191096208980895594483,4487256761553889805606724319750509981998899318),(2588178477348302709594531903389018108868803203,2588178477348457996801185100285174472383899180))$ |
| $(1,2)$ | $((2588178477348302709594531903389018108868803203,2588178477348457996801185100285174472383899180),(689100193142835621466557615681827236842011923,689100193143026187995645880819838962768899042),(264133443713507037843087566820346206150710586,264133443713741315715415270360693273036633565),(308683549365097517951335536513981473775603425,308683549365386029346717523997247823073967623),(438260967437197254684878530784078973700038533,438260967437553146406875441026771659351292465),(540232849555340503797262144840030084471742377,540232849555780223401378124521228646506204901),(598316604837542983492181732072294573101819468,598316604838087136641505273993671389565740258),(604454835283136449266900716574460553447432380,604454835283810889790674153343515349700132144),(558786381300018080374098376925281514590759277,558786381300855300386511431123821482120257181))$ |
| $(4,3)$ | $((558786381300018080374098376925281514590759277,558786381300855300386511431123821482120257181),(535952154308458895927697207100691995162422725,535952154309377505684430070013974548330319700),(500166256209721752814415706238266220933514670,500166256210729875344015808511743157611815506),(451446042054793798440838784160348378039307381,451446042055900386557471980186259929366104178),(390321131795197519198264841594605488566636604,390321131796412442384140006397510326372085481),(317832505455717283789638513417216067690743982,317832505457051424454314141304685237220494518),(236908100028038617988021372384495922530811312,236908100029503978157051918004564941906691953),(155120491975582379860703658413359061907878809,155120491977192199470160000464333900649231798),(89168481160633283522390297651944576881676180,89168481162402171635374349252537157039454822))$ |
| $(20,5)$ | $((89168481160633283522390297651944576881676180,89168481162402171635374349252537157039454822),(72680478456896009437811957461590955625125522,72680478458704664676677936449587971137010578),(57182200580502931715046389346844982843370482,57182200582352267146238165292165928837546533),(42934566279302249012135857778771331834219335,42934566281193199094707160164154546447177386),(30234143611293971924807840846525398872975240,30234143613227493022986769264286405050817785),(19417526491433759435452750979101962275460483,19417526493410830343825420236739787624633100),(10866132112807432693285511694864643700000427,10866132114829055174920150194752440566051487),(5011440104957605300987830788050588855107659,5011440107024804638829170178024170505052148),(2340699422635825113191324115704747744857911,2340699424749650675063874487562972357964227))$ |
| $(42,6)$ | $((2340699422635825113191324115704747744857911,2340699424749650675063874487562972357964227),(1005329081474935019293070779531827189733037,1005329083612073693181226642332373284420267),(465946571696056726520111001975960068268917,465946573856770854379999878668542189354161),(783458012643133716701396765167765130975019,783458014827688651099118484197478437307053),(2022255106485667862412749305163348896833505,2022255108694332001837080700376943160716958),(4250393478492223858179456730286001910967232,4250393480725268682779834014210400761599975),(7539778325591832269051384930099607495084182,7539778327849532376806454276171015588895737),(11966357576295739595029977979415750335479511,11966357578578372738352073257176756103674222),(17610322785092937952287709061089090233709414,17610322787400785075068685001218920504938273))$ |
| $(43,6)$ | $((17610322785092937952287709061089090233709414,17610322787400785075068685001218920504938273),(23254287993890136309545440142762430131939318,23254287996223197411785296745261084906202323),(30115639160780625698082309256792967088003796,30115639163139181723672901252339673193951939),(38274567840253398234070789586035360903459042,38274567842637733318383492566445983567189965),(47815509212775191649854383421387346495122288,47815509215185593156785927004644643962852109),(58827342979186018975167073084585107645745667,58827342981622777534626729509702137681609463),(71403601989568477835145222369786915917361890,71403601992031887380988778798368750474266722),(85642688829704271966072489527699600052415932,85642688832194629774488501661916253061490435),(101648100608272361752259497635354989168129939,101648100610789968480613392519294894720138805))$ |
| $(11,4)$ | $((101648100608272361752259497635354989168129939,101648100610789968480613392519294894720138805),(165669747722544720897007530065976545630985967,165669747725171323305112955948809461354732288),(257952593851733810525911417692481381784401437,257952593854474219131615207279622253132120284),(385120453951293095234851037444906561130593667,385120453954152336951319789324549223771227746),(555101340838373741514609261792489243114735448,555101340841357069594419657582096837376042680),(777357647282730767515654417394744514154617590,777357647285843671963721102669223500837329069),(1063149918335341663380888995374835875753571636,1063149918338589881859036007482799125034273628),(1425838197736702389080568506682674306143707024,1425838197740091918327701327446585990356568185),(1881226245652706349179802697105732331010785853,1881226245656243456972849685338608277032421560))$ |
| $(3,2)$ | $((1881226245652706349179802697105732331010785853,1881226245656243456972849685338608277032421560),(3702778437316722189576739458797964430479101169,3702778437320849611553443116906697423735835062),(7007526925215029780366551086333710041578511540,7007526925219847800957765155326553312096189652),(12806912359964807013716261310111210808197791295,12806912359970433263786303658391723476718849760),(22737966797084977598075577978944464522360796177,22737966797091550116923237326586801810869529191),(39415792658536281220098137231136833546498226882,39415792658543962071205524806313827622358450265),(66961642652041217222420092782595330434107046420,66961642652050196766040559114390655734511689286),(111793390757869202865169773650035340821676330432,111793390757879704810698225635728131826561051590),(183851259764501510670590664617644363682124511597,183851259764513798055482038000956613073503004467))$ |

**Definition 16.27 (case 7, event).** The signs are $(1,-1,1)$, the double-factor index list is $(6)$, and the quotient degree is $6$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(4938249216952485719621327803364810150002132954,4938249216952495361641410070794618066715392767)$ |
| $1$ | $(-29297302087487272689949069858490325017447230085,-29297302087487267000292155243659660599288033517)$ |
| $2$ | $(61775917632355703676370556698616123881837557068,61775917632355712929529759195615244074259138824)$ |
| $3$ | $(-108300672345320565904143501437910456510002238330,-108300672345320561118038904830722960305022351555)$ |
| $4$ | $(163370686080127685956798201182582862725939239499,163370686080127693163630048223950480792466686935)$ |
| $5$ | $(-14836631183447093894063705869592247557450035104,-14836631183447093207518596525318876840842212026)$ |
| $6$ | $(22035441017797764280532090629315944823136947419,22035441017797765296930186432502929277720379466)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,1)$ | $((404554899563488560959171832913581239326068474038,404554899563488599239887681088856301296061101511),(181616616108039689264528677346542419439499903262,181616616108039740364032962044542585741924451310),(81731664535958877506848441978117607680132424159,81731664535958947356066936869329931061079269486),(37357117404433246514235902724322132007527189885,37357117404433344084436631193190233449528536259),(18822411088271891528287338384432414999725655609,18822411088272030556782495583392432952976737065),(9821132898200267924816393230217669982620858237,9821132898200469771486548827633422503552544155),(4938249216952341215112030224487541982465645301,4938249216952639866150707649671886234251880254))$ |
| $(4,3)$ | $((4938249216952341215112030224487541982465645301,4938249216952639866150707649671886234251880254),(3717528296640359537685939473055009982426842067,3717528296640682389816747355181502166926714279),(2754207033129858916120260105902766545947387860,2754207033130208093480293659303460235859268867),(1963675526151057561528882169324712376562483423,1963675526151435385541376510846489880627605311),(1303868324934206927742396173251624864136860009,1303868324934615936662603584932061912688172600),(772849611936244201543696561191146015482463198,772849611936687172101658651857312185604755726),(411778132909680575198636960106568223067722886,411778132910160546586995792254963050745617438))$ |
| $(20,5)$ | $((411778132909680575198636960106568223067722886,411778132910160546586995792254963050745617438),(321510263153039668612372059835423774964037808,321510263153528890208330077354375767030832866),(241864095519611205766959660250273142875331261,241864095520109867520056992045813520330065706),(173482735411778174041553724272417770433922462,173482735412286470002308631339162597383445063),(117177626369796896774226024133532735591101270,117177626370315025187837286769057669688148784),(73931445511317431965609359393126502344383332,73931445511845595367948741526873904294982697),(44902312385538305890327652831962293030705560,44902312386076711206283025516131427579927671))$ |
| $(21,5)$ | $((44902312385538305890327652831962293030705560,44902312386076711206283025516131427579927671),(15873179259759179815045946270798083717027788,15873179260307827044617309505388950864872645),(1061093866680392473099197888875898336390182,1061093867239488541174422726087762827928680),(1624175755500470139111330466958959225729651,1624175756070226359594395081747989845076647),(18895986906966407361697390007065247061404371,18895986907547039535851503188034717617472457),(54389740587528400574893641625888873152389253,54389740588120129092035025428162454942994125),(109803823618128916617374543324183072299411753,109803823618731966557977456931711950462756648))$ |
| $(11,4)$ | $((109803823618128916617374543324183072299411753,109803823618731966557977456931711950462756648),(220631989679329948702336346720771470593456753,220631989679955641489862319938810941502281695),(411141473140685072104436750435242161111652225,411141473141334308060782819999596965318770165),(694919368569734021533071418473621022259817809,694919368570407738509398918150716011041142044),(1088515547405892858171847100986879908311813824,1088515547406592033198262043370673905290109061),(1611619370561704162293524794891192420901886988,1611619370562429813305917971901974448066650888),(2287320459560684659973323088549733396737197171,2287320459561437847621247141671648139038431869))$ |
| $(3,2)$ | $((2287320459560684659973323088549733396737197171,2287320459561437847621247141671648139038431869),(4990124815556606650692516263183897300078437901,4990124815557469984882563820750342902925555796),(10134485425043235738341639033885716615343470932,10134485425044226189466652359643008037936506191),(19198138065525642391734681055898380891790527988,19198138065526779663861860785679595522801801045),(34529285230918278405114775394897395857343608092,34529285230919585398802210517428892450923233954),(59613625776700946652576823481153258836219874550,59613625776702450010671878331319936747664600823),(99685688330977860909373433979777195804418566768,99685688330979591661674212491271291157606807547))$ |

**Definition 16.28 (case 8, event).** The signs are $(1,-1,-1)$, the double-factor index list is $(5)$, and the quotient degree is $6$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(4930754621946240991113702054164688102749143380,4930754621946250632584806164924450845363480639)$ |
| $1$ | $(29295581854904762598459350703153471897237809122,29295581854904768287446412849664623036824357681)$ |
| $2$ | $(61764138493619546312864178530466113943963244468,61764138493619555565600250036606436774679857912)$ |
| $3$ | $(108288194714120162197703997005606483300562894267,108288194714120166983373185698419545239353794757)$ |
| $4$ | $(163373858007891913931061777834293259345922256732,163373858007891921137834059260862847902112328462)$ |
| $5$ | $(14831446358128894771517273937165926461934771979,14831446358128895458003879617614517327134797621)$ |
| $6$ | $(22036384436213685603327124573522460312877062383,22036384436213686619725221097013237491245853515)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((99689912632517556109543304826747836102198756904,99689912632517594388063714913481091353666045160),(59612861145169290080232442135669408102475106935,59612861145169334767867644262960742873806198597),(34525376413829805024571302125718626198138846260,34525376413829857604008210140248783927863105922),(19192330548121399023603860280605175429730876267,19192330548121461357564302414513604983770963932),(10127605627501589827919713952159814076972949248,10127605627501664267015335980049562250968662277),(4982703804080025144389321669475449187488812383,4982703804080114670314381653029476406701202286),(2279675912251231760451228769509500547914055838,2279675912251340180394503647897963158121832285))$ |
| $(4,4)$ | $((2279675912251231760451228769509500547914055838,2279675912251340180394503647897963158121832285),(1603918939294033414466705544518013388020366702,1603918939294146557914534146615084845976989785),(1080779087061383274706701030946427243746013835,1080779087061501379608381915450242321062652909),(687163399840695822224942499684701799257178335,687163399840819139428126082754132703803091163),(403379502709560846983626310716017491606806309,403379502709689640993736376089452313958153141),(212874789631087929420104656896660631800145838,212874789631222479209778529922687032500319395),(102059673684704007667271523146421535733913992,102059673684844607539696159766010288451667583))$ |
| $(20,6)$ | $((102059673684704007667271523146421535733913992,102059673684844607539696159766010288451667583),(74355894698108027229063239708861761717356030,74355894698250139622175567226841102439504630),(51632715532267609029022988775621847934574857,51632715532411252336772191938302450015415548),(33677798891548798975477238861073518071456678,33677798891693991831352340392772041007870300),(20290381773740757655250668604836558332994996,20290381773887518935652935805462302229907589),(11281102862859273582904824935050690618035899,11281102863007622410572809007137074731905329),(6471850444932564800966453891659777971824512,6471850445082520548454608591332731861226099))$ |
| $(21,6)$ | $((6471850444932564800966453891659777971824512,6471850445082520548454608591332731861226099),(1662598027005856019028082848268865325613126,1662598027157418686336408175528388990546869),(1053372102033922527497184431272907748149450,1053372102187111487180134142244930747190669),(4466060956044982368900504680615768284678611,4466060956199817243328435085018730478520079),(11733802477079683113729988748045451126844776,11733802477236183778567777360158693828882344),(22700832070976903460671111720398307065237613,22700832071135090048410355233967376799254824),(37222351100141843187820882102895571219739927,37222351100301736091366620284466524613765429))$ |
| $(11,5)$ | $((37222351100141843187820882102895571219739927,37222351100301736091366620284466524613765429),(66265389158471722642120422867890099528744555,66265389158635028177279150385464820242786639),(109526384957872479617254553273462260702187090,109526384958039279355646429193224975248360351),(165846949397585712337999341361381935699129979,165846949397756089934552069331920951423509841),(234244148681914156299715389867577154747325889,234244148682088197550051800413233738131667157),(313906294360800562707323947687623304714342144,313906294360978355606894409891568596035326908),(404190046841273031377622071583021602257960636,404190046841454666182642316207555232464698684))$ |
| $(3,3)$ | $((404190046841273031377622071583021602257960636,404190046841454666182642316207555232464698684),(765325056763162906058814567164614792432434605,765325056763359908485633941471501778182185788),(1296405775510429776943040119951842343832544371,1296405775510643591091110316137876780311065285),(1956258469132872032305310362680782122556331026,1956258469133104246963066220406981507984750909),(2746806711094137305060843741764524420996764856,2746806711094389669305785966952575577271691482),(3710105377991743364735791104522328463851251598,3710105377992017805383310299866056528675448841),(4930754621946096491274711072681611546043462195,4930754621946395132423797146407527402069161953))$ |
| $(1,1)$ | $((4930754621946096491274711072681611546043462195,4930754621946395132423797146407527402069161953),(9813351597763508997430390945318743874812304581,9813351597763904440585744532573410895644014402),(18813557806488874573409632504379540832984728638,18813557806489400804155092136787133141058158905),(37345782983828195135664187540418709295675674695,37345782983828898765733947303695288690192489405),(81716027399346931267758198092479422115923975920,81716027399347876538738416269133079933539645612),(181593789582824816999222978914130195356646029237,181593789582826092933464013953217513833095270572),(404520358486824360187738924513024225835466529696,404520358486826090902876294850453836146495123222))$ |

### 16.2. Seven box

**Definition 16.31 (case 1, seven).** The signs are $(0,1,1)$, the double-factor index list is $(0,3)$, and the quotient degree is $0$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(544006521949869939590636832741525452499063267169,544006527662973930311528462724191501750797506402)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,0)$ | $((544006521949869939590636832741525452499063267169,544006527662973930311528462724191501750797506402))$ |

**Definition 16.32 (case 2, seven).** The signs are $(0,1,-1)$, the double-factor index list is $(1)$, and the quotient degree is $2$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(14249449877532984582060696131990314601342312026,14249456041473543010148444617018613919438701837)$ |
| $1$ | $(-175491655776580303122850836859424328372738980152,-175491653931883563489555047485724606006479865360)$ |
| $2$ | $(544001511454717524079872630587084593637995680801,544001517167821514800764260569750642889729920034)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,1)$ | $((733742615264134072151488374204799514245817858187,733742628985875360933763542046193585181907602023),(101995270208022405789298695205336707169718448077,101995290565216055109113387716246688540671988542),(14249436606628263506981646792958493731614718768,14249469312378264085227493956050434789166295095))$ |
| $(8,4)$ | $((14249436606628263506981646792958493731614718768,14249469312378264085227493956050434789166295095),(3281207406453995721692015741411217051851752604,3281241655773540207241757236025903070228083415),(813001822759689250150394542787137147682468952,813037704916027498017962087403725146441901735))$ |
| $(36,6)$ | $((813001822759689250150394542787137147682468952,813037704916027498017962087403725146441901735),(195950426836112632264989243131117171640148039,195986717201649320712013300248180665495356315),(110150506942533596488834559282796994072432283,110187211096471841453685861305283296745812770))$ |
| $(37,6)$ | $((110150506942533596488834559282796994072432283,110187211096471841453685861305283296745812770),(24350587048954560712679875434476816504716527,24387704991294362195358422362385927996269225),(469802143185373107045775807393856437411605929,469839680495317580984652331632135671443727555))$ |
| $(19,5)$ | $((469802143185373107045775807393856437411605929,469839680495317580984652331632135671443727555),(1360705255458210199711967671312615679225384732,1360743631503364018563240150171635158338644215),(4376614271851037620815161998462174114937584163,4376653508948213248332313361561723094021568375))$ |
| $(5,3)$ | $((4376614271851037620815161998462174114937584163,4376653508948213248332313361561723094021568375),(16440250337422347305227939307060407857786381886,16440293018727610167408606207122074836753265015),(62503980868913502244632756027351428703009909659,62504027351495851761532665338291841760093081657))$ |
| $(3,2)$ | $((62503980868913502244632756027351428703009909659,62504027351495851761532665338291841760093081657),(154631441931895812123442389467933470393456965205,154631496017032334949780783600631375606772714942),(382759280858557503022220180555286660493402940951,382759343974524196838219967005408570175884828235))$ |

**Definition 16.33 (case 3, seven).** The signs are $(0,-1,1)$, the double-factor index list is $()$, and the quotient degree is $4$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(393280004209577130741046145211124094933846089,393285717313567851632676127877173346668085322)$ |
| $1$ | $(69357566487938862181028078726338983121970482,69357566488205905689539439236591503771578590)$ |
| $2$ | $(-28065003280304133994333972744824680025720735448,-28064997563086962994274113092070898582555740137)$ |
| $3$ | $(44546745501412001680640420981882978960025603,44546745501679045189151781492135499609633711)$ |
| $4$ | $(544005203457620144061154252898471933642801577140,544005209170724134782045882881137982894535816373)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((516219575869535702246682635078129650708633475480,516219593012961388775542777417236035696566165473),(251258595400319397462631090578287382397004758239,251258616829601505623706268502170363631920620731),(121123972315641079896788883132675552224220200047,121123999697273022875743062209263497810932537898),(57816447554957151826452797394307596171555324942,57816483269570349994171037919378075762614520744),(27337087273825274532741758822351446072960755390,27337134773258154865385942693447858946887661632))$ |
| $(2,3)$ | $((27337087273825274532741758822351446072960755390,27337134773258154865385942693447858946887661632),(12097407133259335885886239536373371023663470614,12097460525102057300993395080482750539024232076),(5064768112581409933186982041998247462883762226,5064828259793579174797579733506443439308592031),(1989303481236204334783852021622066869865458034,1989371380678303972597965035135657830230878042),(746166834674755438555598958025476714644579499,746243639424956331686386097991559139963007191))$ |
| $(12,5)$ | $((746166834674755438555598958025476714644579499,746243639424956331686386097991559139963007191),(435382673034393214498535692126329175839359865,435461704111619421458491363705534467396039478),(239119010443015784327402236025906039396479335,239200339914652983811098864496177727254686962),(124175121829545590977804050392654922035250743,124258824203880841201893523998194629354135846),(65651142771367298821826610740276002939018932,65737295084764086211577323385370747750516790))$ |
| $(13,5)$ | $((65651142771367298821826610740276002939018932,65737295084764086211577323385370747750516790),(7127163713189006665849171087897083842787122,7215765965647331221261122772546866146897734),(5023094210302615703492477416390363011552092,5114223438185963849834062044882200840210738),(34439069840092790306842005239456019628658685,34532805607841076677998122376162325886586462),(78776086828406416284463244916046795341483748,78872511315711032409472342479252679583100021))$ |
| $(7,4)$ | $((78776086828406416284463244916046795341483748,78872511315711032409472342479252679583100021),(167450120805033668239705724269228346767133875,167551922731450943872420782685433386976127139),(315808320215754725692035051036510374575657884,315915828300050226948609861978855008969705595),(391058654867344675109975148089514811946070561,391172218750295783267791890062441051940436309),(393222864941974145945730175823904591481898795,393342856581170836427992097264392850120031483))$ |
| $(8,4)$ | $((393222864941974145945730175823904591481898795,393342856581170836427992097264392850120031483),(395387075016603616781485203558294371017727028,395513494412045889588192304466344648299626658),(324465160514272609035055161974069492718970819,324598379623550439589410690786662201688086293),(180478861617151752158644211466892889189157056,180619274714667710029672486553546844517122591),(96263688882807218588136749956468492456324731,96411713954577246475275842720477738873559038))$ |
| $(18,5)$ | $((96263688882807218588136749956468492456324731,96411713954577246475275842720477738873559038),(54156102515634951802883019201256294089908569,54307933574532014698077520803943186051777261),(26991297689156765844105160695232147422737766,27147039231684849422214588987420196111845522),(31373713223068432266288724178359043958317197,31533472709683193843474316140093664314616755),(92208648585527944060399274235852537664183742,92372536527811761280661028670228350161888352))$ |
| $(19,5)$ | $((92208648585527944060399274235852537664183742,92372536527811761280661028670228350161888352),(153043583947987455854509824293346031370050287,153211600345940328717847741200363036009159949),(270331039138994813020547360925206122246203947,270503294504199119170961439107958939500931910),(468976313626708008549477448716648364260181601,469152921521872845958806448801280820139001625),(782185567527747256868745667098140873843552137,782366644653883492523204154227673301666110942))$ |
| $(5,3)$ | $((782185567527747256868745667098140873843552137,782366644653883492523204154227673301666110942),(2035022583131904250145818540624110912177034280,2035221537181926078780794975933243227774548210),(5120883269349278088068301503590885231620802527,5121101967539359381463228929367942768107619095),(12164961873643562493992711639548423283795265642,12165202384041190340847074587161827842200801754),(27417472969484779879014449832431340511113026041,27417737583325567048701267251949399615271354881))$ |
| $(3,2)$ | $((27417472969484779879014449832431340511113026041,27417737583325567048701267251949399615271354881),(57922495161167214649057926218197174965748546840,57922807981894320464409652581524543161412461136),(121261247319037381335490714831664526120957256776,121261617511593256873999425939074433503463049263),(251435446030855459227076022744310317516039975174,251435884545527561011622069745675079963161188814),(516447133100482886616399197833765968542972619790,516447653029972676035306934102473615793153437935))$ |

**Definition 16.34 (case 4, seven).** The signs are $(0,-1,-1)$, the double-factor index list is $(2)$, and the quotient degree is $2$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(14242744798389794609747494476440473318830907603,14242750960693954996149226401612422546380860120)$ |
| $1$ | $(175159250693052842028945233444532964536002102972,175159252534367715743868850375451477187014886360)$ |
| $2$ | $(544029084029052788895928384587691133802174121570,544029089742156779616820014570357183053908360803)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((383112576293074867761807028688680129933990142813,383112590009797892584024007527436641064287117951),(154887844095259688460633329764634779541036488154,154887861128863427072027027827453943459953778756),(62670382904707706383441726987512212598626363888,62670404683468156464235051770060541619097529762))$ |
| $(2,3)$ | $((62670382904707706383441726987512212598626363888,62670404683468156464235051770060541619097529762),(16561652309431715344845925598950929127421301755,16561676460770521160339063741363840698669405265),(4454739465971523612245648247120341518852122220,4454766346957684582494326623314463719110553318))$ |
| $(12,5)$ | $((4454739465971523612245648247120341518852122220,4454766346957684582494326623314463719110553318),(1428011255106475679095578909162694616709827336,1428038818504475438033142343802119474220840332),(526396653729915202570229823500716205982275114,526424921856566213950161246205232975635456880))$ |
| $(26,6)$ | $((526396653729915202570229823500716205982275114,526424921856566213950161246205232975635456880),(75589353041634964307555280669727000618499003,75617973532611601908670697406789726342765154),(156060454725476590201060800912654918108408558,156089433159981969961730944087210913626155811))$ |
| $(27,6)$ | $((156060454725476590201060800912654918108408558,156089433159981969961730944087210913626155811),(236531556409318216094566321155582835598318113,236560892787352338014791190767632100909546468),(848281060465281706144251904472427875941913334,848310760366047686162402232926917724769019509))$ |
| $(7,4)$ | $((848281060465281706144251904472427875941913334,848310760366047686162402232926917724769019509),(3295279076689135666342994237739808037316294217,3295310230680829078752846401564060220206911673),(14242731530866939453040617580189862164349645749,14242764228216810152856103297863033700862121974))$ |
| $(1,1)$ | $((14242731530866939453040617580189862164349645749,14242764228216810152856103297863033700862121974),(101822351164289369746621604319790295180616458002,101822396208504658745682158468254821546103804387),(733431054826764588936130975647081861999057391825,733431117930949286955328228209003792445253847603))$ |

**Definition 16.35 (case 5, seven).** The signs are $(1,1,1)$, the double-factor index list is $(4)$, and the quotient degree is $6$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(5464340340918256506378599667604285383164426988,5464342763028889026674804868362604436037236168)$ |
| $1$ | $(27021807891370496626522967900532352983402214601,27021809279601991724355547606961569639515647326)$ |
| $2$ | $(58801237905930159927511833969086106052797104156,58801240261516189193083727771141337029848453976)$ |
| $3$ | $(103992598697505810733777740663544962292227144235,103992599895712216166857407753938276302707979338)$ |
| $4$ | $(165094668469476654217614610123708308957173913057,165094670327011646891763354596757535155976736016)$ |
| $5$ | $(14821306054579555968635612586175281323425195159,14821306225137511993263205788819735170982965198)$ |
| $6$ | $(22035492975375663633829315994614414850593048414,22035493236118321877352588254057356466169477012)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((105560024291249014400858198605293534130521900753,105560033944219183659938154340066236488977349177),(64136025375332082021999686052659091880237643112,64136036656752957131836970624414831269369537652),(38040539482997037498265089391366982995566430740,38040552771404195717340175763932745963883686885),(21968048571824432987817087890524210636378154911,21968064342933320957400549166463818667344678137),(12369370149288254185313103823816219028630852005,12369389003583623956341179054338310289291529874),(6840242411494824617241344568787263998362413549,6840265110856700434929875536357973543911901233),(3854213959661954681535427768536633737722812646,3854241477102234562787217871250768134760493602))$ |
| $(1,2)$ | $((3854213959661954681535427768536633737722812646,3854241477102234562787217871250768134760493602),(868185507829084745829510968286003477083211743,868217843347768690644560206143562725609085971),(425256341956774442489436622813697986072448394,425294468565760467770548393909488652685899349),(998975063262834169448822375219005456840495701,999020165105894063785761693276505619545635125),(1940700678076561196086696134156246447649408347,1940754200165942097163548512898780319110036935),(3212492314317888702842121235530994648905549027,3212556025381549467638073674811401618386292239),(5464303515716779565107404666612147881232331281,5464379588230365967945999869354741937969331996))$ |
| $(1,1)$ | $((5464303515716779565107404666612147881232331281,5464379588230365967945999869354741937969331996),(9967925918514561289637971528774454345885895789,9968026713927998968561852258441422577135411510),(18391626581942596436207971709762380934822026593,18391760790158468488511308778050979297528628838),(35935033855840588007955861107727110213028032016,35935213396742972869687670950906391463908431659),(78804086743008714127271994042633010828964033907,78804328046974788742024206192615175298438163647),(176681252314228229120381286427843909452890738290,176681578152551514599227954369248948024758654110),(397231236098657728235755194936323777565790255515,397231678224625636251866122608980348478231286129))$ |

**Definition 16.36 (case 6, seven).** The signs are $(1,1,-1)$, the double-factor index list is $()$, and the quotient degree is $8$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(558786250923973193972259857057208766860781586,558786511666631437495532116500150382437210184)$ |
| $1$ | $(-730695263728739163627303709112713489166093876,-730695263728444169124137280789253237871531163)$ |
| $2$ | $(-5802349542940950009993095648507424047028699606,-5802347769165119070839516341611593228949093317)$ |
| $3$ | $(62200502739373208072405950637899408127578076,62200502739473353984658364414972733028906401)$ |
| $4$ | $(9179786132400478620937910470073755404433638849,9179787902787627524242379765214071610681382198)$ |
| $5$ | $(-51886415168880679364140646462253772713330547,-51886415168780533451893057156905539415381479)$ |
| $6$ | $(157868228481190615918834035054736926271626699340,157868230254966446857987632957602478734221508924)$ |
| $7$ | $(731891667064320272192013567362844132079310109,731891667064615266695179801283181428952059560)$ |
| $8$ | $(22035295032315004227267754210818184399385266888,22035295293057662470791027190564918738747054571)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((183828235862982258032915056116426655410583633738,183828241702407175582404080525844249958810598798),(112310330606170693414138106381068049316588154119,112310337905451840350999389059432137516203299438),(67750019929798894362625515489881545837091200611,67750029102360718151558714750588032706296575641),(40319400377564613624627577580052800319875762532,40319411964417868655435563050331813640555502394),(23667637322934257858577729113132891090510148685,23667652034309060370786590307757829223817555398),(13712333228435384323443243531205120317987377955,13712351999501460490689432138693130192503125909),(7860434547648169903803305876416024601040769593,7860458613386232528166107854245142281450245365),(4487241263374956983867224987193684624962005483,4487272259700198555932853630991455060617533372),(2588158426686961167908305549362431771558035428,2588198527981229362723764554527544196722613308))$ |
| $(1,2)$ | $((2588158426686961167908305549362431771558035428,2588198527981229362723764554527544196722613308),(689075589998965351949386111531178918154065373,689124796262260169514675478063633332827693244),(264103200896186639967628125091013187424889373,264163686510355755329751548389498825870565109),(308646310449840636236336275866265961177457232,308720788263386908903087851100616342568852282),(438215038000016165092811097077519317733986672,438306896860273134986638380810347646399181915),(540176110202382991372221020456312641888868617,540289588896372810673858084697662859235600541),(598246400952061387257134282256246188004415494,598386808712601258297153779412796147923457310),(604367836883738543018232962369579478881823570,604541833672940046746524073056652590855999120),(558678404367097304384496099644430955853819066,558894358223507327083295873912928193444152649))$ |
| $(4,3)$ | $((558678404367097304384496099644430955853819066,558894358223507327083295873912928193444152649),(535833688108776685067627668281856694339816814,536070620498790967251681774341065994738229414),(500036254738376467152050351209661979349461416,500296257671631730391918051572308585946209108),(451303352552107006353886528283861616049343651,451588731547794385386670569142117967744457567),(390164483579615886855402139295211592014274919,390477780000677237504313209347380573747945612),(317660497552595069347824906322871566292682432,318004513348158076386857139144286020993679737),(236719187459252294177748010403701753022343217,237097012585402015198740960214217003375588846),(154912970559014438681012089260124718467132467,155328013379827860044871646179517218412823864),(88940470650658576558516097301693581176751245,89396491657236314758597292802422749818674068))$ |
| $(20,5)$ | $((88940470650658576558516097301693581176751245,89396491657236314758597292802422749818674068),(72447345673569611027892099312085796854155939,72913611226588428437028704458149132670136619),(56943828008473270083158096896549631110612479,57420573138626955232184801154975847794637619),(42690833652225445500890636217734351423459943,43178298892192531141461646889187834000197213),(29984927845976365762217272487848328989903919,30483359362135096450257028790428984728406399),(19162701620354317790488260261629320172484983,19672351347737849056958711760568291982716985),(10605569214978818811517074017955789546872135,11126694995553102542896055371595082897307869),(4745007235083584756546891021140237777670990,5277872959432580927263579510936493808738775),(2068261538521567104918566854960759556158464,2613137291026668232724410525085007761512567))$ |
| $(42,6)$ | $((2068261538521567104918566854960759556158464,2613137291026668232724410525085007761512567),(729888690240558279104404771871020445402201,1280769456823711885454826032159264737899463),(187469912792853554125707396440299721568093,744423214549407768458568257935297474622081),(501910938410071864900081676640859221065754,1065005070660053884568527995724666352243278),(1737603077612534368101239455411560406971756,2306907118974364486834383942530515920572360),(3962601559428171843492371706096350554583834,4538185381001571627447710391035935445713899),(7248811179898651914629858590894283781692701,7830745454558104125583958054378414198271381),(11672179461945165713132436673516828683211392,12260535673745301127018401240514202622792554),(17312897549707297694604766486006086447021702,17907748003401601749411032660408010376468796))$ |
| $(43,6)$ | $((17312897549707297694604766486006086447021702,17907748003401601749411032660408010376468796),(22953615637469429676077096298495344210832013,23554960333057902371803664080301818130145038),(29811683530947179840519177840851314836933942,30419594773183306615154483733953645212976348),(37967292374280132643535671645116099513209284,38581843288616253597123484332328201282154105),(47504876932826265864717162211662432020508593,48126141474932282407255376989398655207513316),(58513316487500820423563725576011896848497620,59141369452896221752264486030336333110231988),(71086143463588253347062897229814057792720836,71721060497388855686988591433525753270784512),(85321760017140697597010983595940120909741599,85963617623921506924906700190640428894161384),(101323662822117336549060482126402627824438135,101972538375892963543153615936446489568292998))$ |
| $(11,4)$ | $((101323662822117336549060482126402627824438135,101972538375892963543153615936446489568292998),(165331274042023892357258476248252655483224278,166008221383778790016141278919670732264819455),(257599465284717563399079064999485783904822781,258305722398685502574389853721957135773421789),(384752023683586085716282085308904677081440023,385488884198135538154526772968337993721645251),(554716932956222101297812277565493904493887905,555485748698842466789063409915555393769649215),(776956555435142624624357465888185887782664528,777758739107803937541314379370969591036172802),(1062731404333294922683047657491047169849234350,1063568432314033168299202551416612748888393207),(1425401490086166072297917946913035373380614147,1426274905363041531288081235651348943099659733),(1880770538018246380687268101797384289895180830,1881681953262133249701737380862739679020044574))$ |
| $(3,2)$ | $((1880770538018246380687268101797384289895180830,1881681953262133249701737380862739679020044574),(3702246729746567614244668721334779955953447560,3703310144858500123356361961708302622701583939),(7006906316342235388193747188269947029742704466,7008147534056200683807425918180338233729016348),(12806187718572629364505688631769848168439073876,12807637001322705215457293972682782854506962232),(22737120368789956186083434495696145250046872863,22738813225344453850627342479926114799081101942),(39414803601389792127497898376695530556305818627,39416781715648625919705235890917643935782174137),(66960486487823049523092989489566880570522955835,66962798816231316441361642417025582570367341764),(111792038723300412940460495367886347338585874390,111794742792423796052736823925759003812372631336),(183849678043548271552548640072757510874223884778,183852841485467037173524062549868937821213381920))$ |

**Definition 16.37 (case 7, seven).** The signs are $(1,-1,1)$, the double-factor index list is $(6)$, and the quotient degree is $6$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(4938247964906055889081155435294990302959659838,4938250468925798840831589630237650630173612690)$ |
| $1$ | $(-29297302832246038983740070313282270625851409795,-29297301342740710906363082533631321830952220565)$ |
| $2$ | $(61775916423143589501812855251191013856171149233,61775918841595094681083369705338631805674343563)$ |
| $3$ | $(-108300672976932953791399362044011212533107408154,-108300671713762431666140240578438873346904838044)$ |
| $4$ | $(163370685147059566659686634050283472993412879546,163370687013277561149428543346748039688693020362)$ |
| $5$ | $(-14836631273105800797033314417485110757472530443,-14836631093795300337615123036004063399331247882)$ |
| $6$ | $(22035440887431570041615911318516204776236156292,22035441148174228285139183577959146391812584890)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,1)$ | $((404554894572839225002315002203359940505968151400,404554904554257476528655433035062062432784909897),(181616609447185940333344878403665646717712723689,181616622768904247614500910691131827897495955771),(81731655434613644894957640032370831429071813223,81731673637266402380297962598008180761478253323),(37357104698893050084041769531223624305102594887,37357130109914685700378777080194246282802203639),(18822392998962175228952477275841945786436342408,18822429177514508409854400402430535676421172452),(9821106661901152504866965594840175571220420098,9821159134428493873396304945178064104713456894),(4938210443338601890755604107472025873296432635,4938287990493252839157140958060615059836839728))$ |
| $(4,3)$ | $((4938210443338601890755604107472025873296432635,4938287990493252839157140958060615059836839728),(3717486388697964237227763735629988448815435769,3717570204509442580597349961281252798617685437),(2754161716463481090573307750890052306665184831,2754252349722555665926242181385329445325474795),(1963626500941849637963648178553056700186954894,1963724551286289138083702778523216617025173158),(1303815263426284597053764103648900775361451657,1303921386367910303226340263896702994569946998),(772792155653946316526118834352210439225001046,772907068144132487420768483893215283912057021),(411715889573776974789268449997252348592437093,411840376171056767039315162710751859638314908))$ |
| $(20,5)$ | $((411715889573776974789268449997252348592437093,411840376171056767039315162710751859638314908),(321446823053734639355055853908512825934296104,321573703177787836943951832415136003569879380),(241799434139452862595267938128631568620148032,241928756825187787812595905795834165400453094),(173416827705133866047538391397206493162724657,173548643043820698963565003543440069732954982),(117110446750807144021868452341177862753580059,117244805914170133114808441183744986750907691),(73862967841555866138418519384999101705202810,73999923106453532604996788201394893979702678),(44832509961369844342388308362125785459609296,44972114735078721565222371147554159698799034))$ |
| $(21,5)$ | $((44832509961369844342388308362125785459609296,44972114735078721565222371147554159698799034),(15802052081183822546358097339252469214015782,15944306363703910525447954093713425417895389),(988615230063056837747608249684597771206003,1133572428670888955710772968382049627293114),(1550318391997359161756556926877746573196346,1698033044387480987103154322724400606451299),(18820722969883183788623976613289642191531013,18971250769451892543139181774423237388896672),(54313041639376594328508375571869152335875343,54466439461109213511455199115343393174422419),(109725660617372795223456442398863451429090264,109881986544350025866121257403201980392220747))$ |
| $(11,4)$ | $((109725660617372795223456442398863451429090264,109881986544350025866121257403201980392220747),(220550898573365197013352576052852049615520107,220713080710831650575453373978919154827817402),(411057337763368760223503381180499803597432315,411225608443647240830185654342390054992504378),(694832067922545120390282366551784108757714312,695006669142721452422878506955351580319819319),(1088424955445882166360273926269455267890382930,1088606139291906814529031656533177097913684157),(1611525355979539048033271909778865789602966820,1611713385070139189621050450978323004568646943),(2287222885548291310638945244762162922973681015,2287418033499688014221312583290192674449882482))$ |
| $(3,2)$ | $((2287222885548291310638945244762162922973681015,2287418033499688014221312583290192674449882482),(4990013003823300361061638584695351456456537792,4990236627217883312622361112537671353974824638),(10134357186659835506407137548210725776469479449,10134613663357141803155303047652730245120130844),(19197990859643531641374253506965709824018268151,19198285271342707423252310740597185294456988638),(34529116105285820865109817861237181100604380416,34529454356493219067138476888151278655437034732),(59613431297527749980514279883574626157171764266,59613820255828957116972137767614361112713006505),(99685464500109916275447553176805111782682286344,99685912161820312290940496215911186168831465187))$ |

**Definition 16.38 (case 8, seven).** The signs are $(1,-1,-1)$, the double-factor index list is $(5)$, and the quotient degree is $6$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(4930753369989145838218357791504708342205981377,4930755873830217689264113666792653335999929714)$ |
| $1$ | $(29295581110276199204600859163953980636650306060,29295582599545538753752202603900969752192964273)$ |
| $2$ | $(61764137284505281704201259315798581945631658558,61764139702761083051472154791268840459695851677)$ |
| $3$ | $(108288194082661382416441010861042682541749877164,108288195345633200370551294779403326266115719125)$ |
| $4$ | $(163373857074837469129910978749916646580621967500,163373858941028114040085125705669012268141748421)$ |
| $5$ | $(14831446268490100486782412745112215407170896425,14831446447774603193991132769302631791417672944)$ |
| $6$ | $(22036384305847491364410945262722720266519746971,22036384566590149607934218242469454605881534654)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((99689907642226045718446910967335729325252998064,99689917622781882280931329636091082084147984817),(59612855319853989799859063768386783297795207567,59612866970437946257668800101176418392044553049),(34525369560925214446242318214852886748914680050,34525383266675624555970420943396330224271300792),(19192322425887513026129425998234662775006797681,19192338670289164228977440926615246659124538237),(10127595931120665673161970034383752354222483544,10127615323812103395352718546435720751236035154),(4982692147212216384211078543139770011946752070,4982715460875029859111583807245129063824579137),(2279661802012117170067060147697301990441630525,2279690022416310817076672159300956429164432854))$ |
| $(4,4)$ | $((2279661802012117170067060147697301990441630525,2279690022416310817076672159300956429164432854),(1603904215712092366531055548836684985065350138,1603933662801631056567944247314913270499396283),(1080763719331339442670480518463662624737232872,1080794454716848451947105278531771302631316571),(687147355492513898653933628815650319492622903,687179444114124990664508931861803726064479071),(403362747510702515954385250580668837635915238,403396257833543673423662423113213851729167088),(212857287482343908277585399674069889890597631,212892291704876804911162866258819949380556852),(102041386509104850579477668248594243457535754,102077960785304716921073081030874516219345140))$ |
| $(20,6)$ | $((102041386509104850579477668248594243457535754,102077960785304716921073081030874516219345140),(74337411265795086154950735392225331849270284,74374378055411694923550634723888157929042212),(51614033463430293604092060003426626573020798,51651397526087096708678799143554828962951692),(33658915775474016285588260709584702116300821,33696681932599364960739805848190974589834467),(20271295168378970063009524795263433968488636,20309468304074004969904424309235830029410489),(11261810294383797532365676494206008497837330,11300395356303856822783110160855736144371106),(6452349407291989187672256532370461278169462,6491351407541777366510952142499659824828340))$ |
| $(21,6)$ | $((6452349407291989187672256532370461278169462,6491351407541777366510952142499659824828340),(1642888520200180842978836570534914058501595,1682307458779697910238794124143583505285573),(1033451620011736684235844947921245089817167,1073292509025687144815792235811524751239424),(4445926960530147205458822390487489945938738,4486194876532601917377035216952450452801915),(11713452397123750798669026116406533406258344,11754152482013315835582244912297953527505742),(22680263302504654919459509379101647782432171,22721400764433401231700723214417773304753555),(37201561005489824190571212261315559694759856,37243141119786220900230097699226520602704180))$ |
| $(11,5)$ | $((37201561005489824190571212261315559694759856,37243141119786220900230097699226520602704180),(66244156411460162732794618025743383519415226,66286621830491860237288846668844015198605431),(109504699007847561876302902268246397488686031,109548070832928436663991180369217219877317931),(165824799425187738603023585650766414564969374,165869099295042852536318119407663021184112293),(234221523591694124569250378104356516648957603,234266773697226657605903895325016249484357960),(313883182773612685420078084239391191423776022,313929405873118984623835810931844881423882395),(404166437086435424136478228821922289978936904,404213656521283710450617216993542342705294838))$ |
| $(3,3)$ | $((404166437086435424136478228821922289978936904,404213656521283710450617216993542342705294838),(765299454337726379002078807152046684199580432,765350659113942613757742841240332187830944611),(1296377993683484179716838400642113858905703374,1296433557262959898006460312765023302426802507),(1956228302515197017062934594319442283826091233,1956288635676423682268984080552794931459859849),(2746773933631338639806985333064755460724593706,2746839488483156577628036870024141278433242778),(3710069740719995782105489409400682530329034278,3710141015190128663778937808569389548341740588),(4930715850478665388606656342213540793387688113,4930793393340698138875815116083820884818223108))$ |
| $(1,1)$ | $((4930715850478665388606656342213540793387688113,4930793393340698138875815116083820884818223108),(9813300289513343814611324073464973845622303454,9813402905942976039263324346141546230724153190),(18813489571268221667858597508347305993124331011,18813626041642812162786455479706200641717838637),(37345691804383103405833885855584844483783381340,37345874163215131191309414590075777310302948531),(81715904987906807371900544273006065530724695157,81716149810750216132151535431816477720331769110),(181593624461969524299573669678648915874142505117,181593954703692133760609074548726551284936603779),(404520134664302667181204841824588834609653145622,404520582309467309670411224624269589590342709241))$ |

### 16.3. Six box

**Definition 16.41 (case 1, six).** The signs are $(0,1,1)$, the double-factor index list is $(0,3)$, and the quotient degree is $0$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(544006521949871845353403253703021043016289137546,544006527662972024548762041762695911233571636025)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,0)$ | $((544006521949871845353403253703021043016289137546,544006527662972024548762041762695911233571636025))$ |

**Definition 16.42 (case 2, six).** The signs are $(0,1,-1)$, the double-factor index list is $(1)$, and the quotient degree is $2$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(14249449877430016911656849181974364929953695178,14249456041576510681676383760979536342653282228)$ |
| $1$ | $(-175491655776800676021626377930735374213214357878,-175491653931663190593100135848000248722416053854)$ |
| $2$ | $(544001511454719429842639051548580184155221551178,544001517167819609037997839608255052372504049657)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,1)$ | $((733742615263812637347396036578554797807591300210,733742628986196795741300601299969962928371689763),(101995270207592690298585008004932058328480071614,101995290565645770602111481827389654411942111658),(14249436606092173092413030979889503004590394196,14249469312914354500920201963064398268016583210))$ |
| $(8,4)$ | $((14249436606092173092413030979889503004590394196,14249469312914354500920201963064398268016583210),(3281207405904608441641533851759183589104184518,3281241656322927488271291980023741250025892154),(813001822197034882161271904075429551043311578,813037705478681866841098240862069425355576874))$ |
| $(36,6)$ | $((813001822197034882161271904075429551043311578,813037705478681866841098240862069425355576874),(195950426270141492291206417154491041528093343,195986717767620461483549806071651469187998054),(110150506373247545626843129011462868101958654,110187211665757893077171136523670087602942720))$ |
| $(37,6)$ | $((110150506373247545626843129011462868101958654,110187211665757893077171136523670087602942720),(24350586476353598962479840868434694675823965,24387705563895324670792466975688706017887386),(469802142609459095503818751503316857338772822,469839681071231593215583562670143899015355538))$ |
| $(19,5)$ | $((469802142609459095503818751503316857338772822,469839681071231593215583562670143899015355538),(1360705254875670088586496572773081182664670536,1360743632085904130305165754059054285010291842),(4376614271261878854491983189154486852346902435,4376653509537372015199427006417710969335322090))$ |
| $(5,3)$ | $((4376614271261878854491983189154486852346902435,4376653509537372015199427006417710969335322090),(16440250336806713918113929654680109531075830029,16440293019343243554776472015852337706635443082),(62503980868271513346900816841991993719506104572,62504027352137840659228382000802905217217067177))$ |
| $(3,2)$ | $((62503980868271513346900816841991993719506104572,62504027352137840659228382000802905217217067177),(154631441931201112204474591216615762096366653658,154631496017727034868132201970704040238380315367),(382759280857810568522708128478384576512032590538,382759343975271131336535481842668938352669575971))$ |

**Definition 16.43 (case 3, six).** The signs are $(0,-1,1)$, the double-factor index list is $()$, and the quotient degree is $4$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(393280004211482893507467106706714612159716466,393285717311662088866255166381582829442214945)$ |
| $1$ | $(69357566487922125392568894379160746215091742,69357566488222642477998623583769740678457330)$ |
| $2$ | $(-28065003280300319303244951057604818751693713798,-28064997563090777685363134779290759856582761787)$ |
| $3$ | $(44546745501395264892181236634704742053146863,44546745501695781977610965839313736516512451)$ |
| $4$ | $(544005203457622049823920673859967524160027447517,544005209170722229019279461919642392377309945996)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((516219575869543294989727580319646336543298480404,516219593012953796032497832175719349861901160549),(251258595400328888391437272130183239690336014394,251258616829592014694900086950274506338589364576),(121123972315653102305411391407581908878995274420,121123999697261000467120553934357141156157463525),(57816447554972576706267886075531879585301678357,57816483269554925114355949238153792348868167329),(27337087273845329682619746173970657545282359405,27337134773238099715507955341828647474566057616))$ |
| $(2,3)$ | $((27337087273845329682619746173970657545282359405,27337134773238099715507955341828647474566057616),(12097407133281706170795676223190046525272699929,12097460525079687016083958393666075037415002760),(5064768112606402302845447630031637318681609731,5064828259768586805139114145473053583510744525),(1989303481264170339845684149487618142512480461,1989371380650337967536132907270106557583855614),(746166834706098674997699668815675355018810978,746243639393613095244285387201360499588775712))$ |
| $(12,5)$ | $((746166834706098674997699668815675355018810978,746243639393613095244285387201360499588775712),(435382673066580758785703548647689658145393607,435461704079431877171323507184173985090005737),(239119010476072861208193615971708735564192472,239200339881595906930307484550375031086973825),(124175121863498238408940400276133936622918494,124258824169928193770757174114715614766468096),(65651142806242397047826501878528712783540823,65737295049888987985577432247118037905994900))$ |
| $(13,5)$ | $((65651142806242397047826501878528712783540823,65737295049888987985577432247118037905994900),(7127163748986555686712603480923488944163153,7215765929849782200397690379520461045521704),(5023094247049495763738022381287840206681790,5114223401439083789588517079984723645081041),(34439069877816723938785358897185218033065885,34532805570117143046054768718433127482179263),(78776086867135997387849284175341175999542820,78872511276981451306086303219958298925040949))$ |
| $(7,4)$ | $((78776086867135997387849284175341175999542820,78872511276981451306086303219958298925040949),(167450120845774544285977134731653091932496691,167551922690710067826149372223008641810764322),(315808320258621272280171340336999328425821923,315915828257183680360473572678366055119541555),(391058654912458238778389270165184314089337575,391172218705182219599377767986771549797169295),(393222864989463509446381426656606111360994404,393342856533681472927340846431691330240935874))$ |
| $(8,4)$ | $((393222864989463509446381426656606111360994404,393342856533681472927340846431691330240935874),(395387075066468780114373583148027908632651233,395513494362180726255303924876611110684702454),(324465160566642354952139966302686517512449239,324598379571180693672325886458045176894607873),(180478861672162299625431078560980000438339181,180619274659657162562885619459459733267940466),(96263688940602688057790555629900053676403518,96411713896781777005622037047046177653480251))$ |
| $(18,5)$ | $((96263688940602688057790555629900053676403518,96411713896781777005622037047046177653480251),(54156102574822882273970294164360080295435686,54307933515344084226990245840839399846250143),(26991297749773187429917123901476749492511453,27147039171068427836402625781175594042071834),(31373713285150362766073999304624023300891126,31533472647601263343689041013828684972042825),(92208648649113418038995945666337965868093244,92372536464226287302064357239742921957978850))$ |
| $(19,5)$ | $((92208648649113418038995945666337965868093244,92372536464226287302064357239742921957978850),(153043584013076473311917892028051908435295363,153211600280851311260439673465657158943914874),(270331039205625408521604909348332519761319926,270503294437568523669903890684832541985815931),(468976313694919233424612022919715863993685472,469152921453661621083671874598213320405497755),(782185567597579208293606328863900107394168771,782366644584051541098343492461914068115494308))$ |
| $(5,3)$ | $((782185567597579208293606328863900107394168771,782366644584051541098343492461914068115494308),(2035022583208219107769583552640637080996101968,2035221537105611221157029963916717058955480521),(5120883269432717406701355854382188441287919216,5121101967455920062830174578576639558440502405),(12164961873734834762539617385877236829023333789,12165202383949918072300168840833014296972733607),(27417472969584667964859752431179963026206166170,27417737583225678962855964653200777100178214753))$ |
| $(3,2)$ | $((27417472969584667964859752431179963026206166170,27417737583225678962855964653200777100178214753),(57922495161284334369500022521785415420571830931,57922807981777200743967556277936302706589177045),(121261247319174864160067786667621579052727166922,121261617511455774049422354103117380571693139117),(251435446031017031653166119141121900178702738001,251435884545365988585531973348863497300498425987),(516447133100672989279393136330967795314530823354,516447653029782573372312995605271789021595234371))$ |

**Definition 16.44 (case 4, six).** The signs are $(0,-1,-1)$, the double-factor index list is $(2)$, and the quotient degree is $2$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(14242744798501054274570785014961907332395416321,14242750960582695330198235189384995880149859236)$ |
| $1$ | $(175159250693275590295959305274617845357599652790,175159252534144967474521862670406633261092444902)$ |
| $2$ | $(544029084029054694658694805549186724319399991947,544029089742154873854053593608861592536682490426)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((383112576293410781458743727893741998390702963366,383112590009461978888292523523628743059232696872),(154887844095652242105706757407965663461761631350,154887861128470873427575586416637039214805812124),(62670382905157376417343488309486009612670297321,62670404683018486430372047711860733504549549983))$ |
| $(2,3)$ | $((62670382905157376417343488309486009612670297321,62670404683018486430372047711860733504549549983),(16561652309909943573161853760246182688124630307,16561676460292292931770278359472580649421418912),(4454739466478429145148644557830526033541462789,4454766346450779049046858607638277327835943493))$ |
| $(12,5)$ | $((4454739466478429145148644557830526033541462789,4454766346450779049046858607638277327835943493),(1428011255620550538145342257226611869895670909,1428038817990400578366003669679701497439574639),(526396654251166832152566540799208348122535248,526424921335314583677545581755741262889621763))$ |
| $(26,6)$ | $((526396654251166832152566540799208348122535248,526424921335314583677545581755741262889621763),(75589353566474979156178682585506587235967417,75617973007771586333316537793761145614645325),(156060455253906851412422470415932486817563641,156089432631551707987186706340434927301272881))$ |
| $(27,6)$ | $((156060455253906851412422470415932486817563641,156089432631551707987186706340434927301272881),(236531556941338723668666258246358386399159866,236560892255331829641056874887108708987900437),(848281061000894321177541692120911946448920145,848310759830435070293026255942436389636131987))$ |
| $(7,4)$ | $((848281061000894321177541692120911946448920145,848310759830435070293026255942436389636131987),(3295279077239116711213043427619126186647961261,3295310230130848032900903780163747112229058190),(14242731531431318705290651499823382994337627251,14242764227652430899478368704523520218207648306))$ |
| $(1,1)$ | $((14242731531431318705290651499823382994337627251,14242764227652430899478368704523520218207648306),(101822351164968934657911516077457437455854955167,101822396207825093832098088099401705066036369236),(733431054827561245269227186204278216236772275030,733431117930152630618771401103141482450547580592))$ |

**Definition 16.45 (case 5, six).** The signs are $(1,1,1)$, the double-factor index list is $(4)$, and the quotient degree is $6$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(5464340331590270429955077273944304001279380339,5464342772356875311985792460559287524925126664)$ |
| $1$ | $(27021807879681745873355324256956594125470591884,27021809291290742741014153989532649571090659978)$ |
| $2$ | $(58801237888410390860362975341120959745788964842,58801240279035958424410808206232870069033245281)$ |
| $3$ | $(103992598680322873873063319008837910535822453830,103992599912895153199620924344279683842685811034)$ |
| $4$ | $(165094668464135146365146438766096145620781169424,165094670332353154767481643526858717425463355198)$ |
| $5$ | $(14821306051604177014073852715734453283381039990,14821306228112890971274324822547569395302555175)$ |
| $6$ | $(22035492973746363535092138009039253506712839541,22035493237747621976089766239633092909936305461)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((105560024225583384278647226233840760065483327959,105560034009884813719475514451755009984683946900),(64136025297641799677616205975877712136342112001,64136036734443239453174182562942303739740715711),(38040539390693587622685479998164195717035655827,38040552863707645602051495320429985891957154546),(21968048461688745522743047971113246529245542663,21968064453069008458294550582496717223697825190),(12369370017284629722240063251758513216507359896,12369389135587248478000691513849003703400634219),(6840242252518447403052995671660173468292799085,6840265269833077727847931047956155070759257534),(3854213767194535416581608981202088480134144096,3854241669569653925141778946879510498623319684))$ |
| $(1,2)$ | $((3854213767194535416581608981202088480134144096,3854241669569653925141778946879510498623319684),(868185281870623430110222290744003491975489107,868218069306230122435626845802865926487381834),(425256075988981776354516489926173263872739941,425294734533553267176083109542425414856882820),(998974749353947306714255329132458991358180464,999020479014781076668657500159528136581447192),(1940700306536986542112496477570405376024686854,1940754571705516918846356608307542697666648153),(3212491873263974505093568967568395085650215736,3212556466435463852316510913061092799174186883),(5464302990517260482156865295264041550364680461,5464380113429885259784004439239549975839826664))$ |
| $(1,1)$ | $((5464302990517260482156865295264041550364680461,5464380113429885259784004439239549975839826664),(9967925225023832436283457950655334479793609910,9968027407418728074718991491596464329171106226),(18391625661635596446738945956837254429578282731,18391761710465468785643335429653006983134789993),(35935032628211346805518469282910708840758005727,35935214624372214454196108451964150215616984226),(78804085096713466027898183318924297352003393297,78804329693270037327577239489000831643288788819),(176681250094474029247116606097902881276956408228,176681580372305715108090863237501721857380189256),(397231233089207272144148103526915406588283243123,397231681234076093198778435434458084969390255518))$ |

**Definition 16.46 (case 6, six).** The signs are $(1,1,-1)$, the double-factor index list is $()$, and the quotient degree is $8$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(558786249294673095235081871482047422980572713,558786513295931536232710102075886826204038633)$ |
| $1$ | $(-730695263728614420907055192249365985849323411,-730695263728568911844385797652600543228551530)$ |
| $2$ | $(-5802349545864048435644066656228997264312219811,-5802347766242020645188545333905003228211699714)$ |
| $3$ | $(62200502739377164445831328794650767853416722,62200502739469397611232986258220416035694750)$ |
| $4$ | $(9179786129815864245805245824662689409056840752,9179787905372241899375044410630789824494980646)$ |
| $5$ | $(-51886415168876722990715268305501469216656885,-51886415168784489825318435313656912637758114)$ |
| $6$ | $(157868228478267517493183064047015353056585367099,157868230257889545283638603965309068737201090491)$ |
| $7$ | $(731891667064445014912262084226191436933044607,731891667064490523974931284419833925132003226)$ |
| $8$ | $(22035295030685704128530576225243023055591907829,22035295294686962569528205176140655182600732834)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((183828235851293104007193441274462318794601080250,183828241714096329608125695367785422592568661857),(112310330591559250881986087828618419563637956862,112310337920063282883151407611864394325428872865),(67750019911301815174079943594607801368798772426,67750029120857797340104286645848501362776650704),(40319400353861324580556740949173935442451161965,40319411988121157699506399681200352474228505619),(23667637292203677039347047572202059710117081713,23667652065039641190017271848680523831827724214),(13712333188151936093624661354556630473540626969,13712352039784908720508014315335171424141732811),(7860434494290010072843982247527524741711896164,7860458666744392359125431483128545297252033559),(4487241192004590817430797206888021481307962834,4487272331070564722369281411293135749082413204),(2588158330345343705888986947947445616822923066,2588198624322846824743083155939481037818158568))$ |
| $(1,2)$ | $((2588158330345343705888986947947445616822923066,2588198624322846824743083155939481037818158568),(689075468686096594347176689006869752337883298,689124917575128927116884900585826326553903932),(264103047653021626676741211765221283771737092,264163839753520768620638461713926452195015016),(308646116295784181381561231531825135618580535,308720982417443363757862895434319672926778641),(438214791327023175043611223152052190189532267,438307143533266125035838254735592207195981705),(540175795982541089429666176059963287742780926,540289903116214712616412929094185942130126660),(598245999699745301013930160325615976302708075,598387209964917344540357901343867656047653698),(604367323294332471679095420079917841440054187,604542347262346118085661615346889315811903698),(558677745528823791110413274079765805096001166,558895017061780840357378699478168444088590125))$ |
| $(4,3)$ | $((558677745528823791110413274079765805096001166,558895017061780840357378699478168444088590125),(535832956646069450826072201079689786923974655,536071351961498201493237241543808008226933339),(500035442423291147733269276641000293381598361,500297069986717049810699126141511939493385660),(451302450205804030542660915608309439711520021,451589633894097361197896181818144928221161271),(390163480960599780952563474990353674679539964,390478782619693343407151873652613261981122641),(317659383231613339973767969602654383662863686,318005627669139805760914075864745462058576524),(236717948679237303812058097196745460004665625,237098251365417005564430873421251358522312281),(154911593078252800171826739324114246112174085,155329390860589498554056996115410611659786972),(88938938567148843468217637633704806552092346,89398023740746047848895752470068638467623503))$ |
| $(20,5)$ | $((88938938567148843468217637633704806552092346,89398023740746047848895752470068638467623503),(72445774939372854292315362211102446662071911,72915181960785185172605441558733145169582636),(56942217629714399299951977799888947667827088,57422183517385826015390920251178825225939384),(42689182609087369341364105363329060578212617,43179949935330607300988177743075138277265980),(29983235092013889199252236411943226723018685,30485052116097573013222064865753910201279835),(19160966081789668521605090109266858293103177,19674086886302498325841881912286477572306919),(10603789789978305019882497031768203434234207,11128474420553616334530632357072381780182464),(4743182793014872696136364435201336968999254,5279697401501292987674106096097179822669162),(2066390919191052960116685587395590504254525,2615007910357182377526291791802109179621468))$ |
| $(42,6)$ | $((2066390919191052960116685587395590504254525,2615007910357182377526291791802109179621468),(727994982279143092106846163492717271882161,1282663164785127072452384639654573858097621),(185552826152136371028620176780124039632352,746340301190124951555655476677071365190176),(499970179346492973100756785736477258362125,1066945829723632776367852885674756385880940),(1735638348639711037523135524595146927945302,2308871847947187817412487872356263635282456),(3960612559268612013886329094993876288130291,4540174381161131457053753001110884885955635),(7246797603434837617237182471162520874796948,7832759031021918422976634173045306215254679),(11670141000169997905339837713648867205342764,12262574135520468934811000199279458108701061),(17310833889673894075083615947940841250222070,17909811663435005368932183197332223127240518))$ |
| $(43,6)$ | $((17310833889673894075083615947940841250222070,17909811663435005368932183197332223127240518),(22951526779177790244827394182232815295101376,23557049191349541803053366195384988145779974),(29809569161450422296212295408330417054314171,30421709142680064159461366165256366289412504),(37965152176691591426127640751721572498314787,38583983486204794814531515224465240119083843),(47502710586269289970587930402834347050614394,48128307821489258301384608796929444271163986),(58511123667057924201140725595659154059320211,59143562273339117974687486009351473124704173),(71083923840249611840421387751267353054827727,71723280120727497193630100910694046032576873),(85319513257751977893806086242584547950689634,85965864383310226628111597542576274824352693),(101321388589326856476526468298135195237978589,101974812608683443615687629763252370360620286))$ |
| $(11,4)$ | $((101321388589326856476526468298135195237978589,101974812608683443615687629763252370360620286),(165328889915626370807407996520337784387134409,166010605510176311565991758645956752505690660),(257596965867086085607660461770275611799122994,258308221816316980365808456949363002562629407),(384749403308463384252109286673513892902594328,385491504573258239618699571601740615609110354),(554714185675193182238582224888924102971308824,555488495979871385848293462589944438663427250),(776953675003418598153331342543162768151601769,777761619539527964012340502713610182308079707),(1062728384194772582047423120891635989840555626,1063571452452555508934827088013429887023879377),(1425398323357725919913936074474888766810521730,1426278072091481683672063108086679542938848212),(1880767217473249857907461652216899986353666535,1881685273807129772481543830440174682598193399))$ |
| $(3,2)$ | $((1880767217473249857907461652216899986353666535,1881685273807129772481543830440174682598193399),(3702242793935345609881563963184944864526245754,3703314080669722127719466719854155241235574150),(7006901649638570963887868260693124823869684186,7008152200759865108113304845752063539782976545),(12806182183365085673820227275876088651082634888,12807642536530248906142755328570093661133660650),(22737113801257167294919804942027560593936421543,22738819792877242741790972033586562546980307371),(39414795806455738384543999119254411293290396965,39416789510582679662659135148348436994269355955),(66960477233131576167409611249176349021127871023,66962808070922789797045020657402838145985420979),(111792027732016428487576916782813826172506387372,111794753783707780505620402510814151905632591171),(183849664985754875901193362788186611518127034276,183852854543260432824879339834416673139086446561))$ |

**Definition 16.47 (case 7, six).** The signs are $(1,-1,1)$, the double-factor index list is $(6)$, and the quotient degree is $6$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(4938247966752146790736374936303395538635502454,4938250467079707725291407358153351297012113157)$ |
| $1$ | $(-29297302824484015466576513699322799806004107046,-29297301350502734163287780290363766323116224728)$ |
| $2$ | $(61775916433547756874018601560902930296907218270,61775918831190927145373463130213707646950639941)$ |
| $3$ | $(-108300672964634209269258722566146858247329416070,-108300671726061176021281329442655388892204433422)$ |
| $4$ | $(163370685145473227941611779238252720666435217812,163370687014863899844772127055680525474060550007)$ |
| $5$ | $(-14836631272330692862716963864588921381434733788,-14836631094570408249661408558482545032660719711)$ |
| $6$ | $(22035440885802269942878733332941043432355947419,22035441149803528383876361563534882835579413339)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,1)$ | $((404554894602709719983476007359901790182315263816,404554904524386980697865559237641046688370973348),(181616609485926598056637489929057324239184266146,181616622730163589256666303990440103018916954665),(81731655483630728411620862558034626481658483718,81731673588249318375940212427349152121552318205),(37357104758648745800773920211560905376262554972,37357130050158989598591424616402564469693490592),(18822393067497906198651112656015442543859654808,18822429108978777128624238614411268864418594634),(9821106731860776274351022251796556360499623995,9821159064468869846654142374274618163334712982),(4938210495862192806732575078629608990623047736,4938287937969661709295207215827137845024567710))$ |
| $(4,3)$ | $((4938210495862192806732575078629608990623047736,4938287937969661709295207215827137845024567710),(3717486436862546939827963285337872148153903671,3717570156344859674955473426215267765447031392),(2754161759090310226465954193986881481527475515,2754252307095726337153937204208970834792853598),(1963626536672433241316218524572345774563147413,1963724515555705351462693414180661513664889360),(1303815290698531676664678339743595075878704853,1303921359095663049531956386779844780716679802),(772792172675258373092429125980639299508698029,772907051122820265651961670369489910547419600),(411715894290685669964935003026339384954532721,411840371454147915361712597297251635101704574))$ |
| $(20,5)$ | $((411715894290685669964935003026339384954532721,411840371454147915361712597297251635101704574),(321446824694542494183061472287764406315991394,321573701536979827789150329029192066240275818),(241799432575818105928985134724730419040940161,241928758388822392315947163469764784549068635),(173416822804638635505291367208219625309088489,173548647944315779497400027686901895214717335),(117110438376838883131691986582897239118375746,117244814288138246143683847904725680991611701),(73862955853185348584174854363822590933457625,73999935094823904439586653572172841617326430),(44832494213225728197388411396113140673897567,44972130483222694128709243153990522140039047))$ |
| $(21,5)$ | $((44832494213225728197388411396113140673897567,44972130483222694128709243153990522140039047),(15802032573266107810601968428403690414337510,15944325871621483817831832735808202662751663),(988591817000401584546214712059438080135516,1133595841733404900174206231996403082462166),(1550290923976305853869591092197843590855026,1698060512408397119337162107302268447348080),(18820691292522713511881117743994496320967232,18971282446812227777734267842283389116189757),(54313005593599211012934928832347128088042504,54466475506886463920791525724303829085788287),(109725620039272042738049737134492534480646831,109882027122450647585611600360901943230371884))$ |
| $(11,4)$ | $((109725620039272042738049737134492534480646831,109882027122450647585611600360901943230371884),(220550848930617706188279353738783347265855484,220713130353579014915251749634098171519539079),(411057278400348706534752959198245258553180355,411225667806667172331943165925605096508646544),(694831998144994998825620255730772633051149353,695006738920271456132507166095729557191519998),(1088424874518793064935664203351684855804220283,1088606220218995802480591664127567046600819144),(1611525263124916773266123887797467814685466930,1611713477924761355363926451554771863469041973),(2287222779942802149691552906078501516630385885,2287418139105177070677310428121121754256791255))$ |
| $(3,2)$ | $((2287222779942802149691552906078501516630385885,2287418139105177070677310428121121754256791255),(4990012847214343655393268979202636324410061705,4990236783826839931930846334386521317407788383),(10134356965874071850614494393690783021208494454,10134613884142905392065169266878242063271208748),(19197990558605892391326659358207262050897465935,19198285572380346628347408809198059765325629585),(34529115704416823246669708967533288337328996096,34529454757362216666254386246739352815444451443),(59613430773017560148535090008560050307753532186,59613820780339146960451538762081295660840785291),(99685463823043702509006217974608992719868699628,99685912838886526106769911779813284785318268006))$ |

**Definition 16.48 (case 8, six).** The signs are $(1,-1,-1)$, the double-factor index list is $(5)$, and the quotient degree is $6$.

| Power coefficient index | Integer endpoint pair |
| --- | --- |
| $0$ | $(4930753371816592441692802941326885364019754613,4930755872002770872962269786991994244559339099)$ |
| $1$ | $(29295581118006226055322333909177757984760983718,29295582591815511644245087425698091689149820358)$ |
| $2$ | $(61764137294865352273481199142983732874733146562,61764139692401012320102048251583584501926071351)$ |
| $3$ | $(108288194094916258810321907133408626713921912474,108288195333378323811105417313254116761172244403)$ |
| $4$ | $(163373857073245007319445515168226316984901967685,163373858942620575828011277262758413194046043923)$ |
| $5$ | $(14831446269259686111583050224753655368549192173,14831446447005017547107211187086276345331894574)$ |
| $6$ | $(22036384304218191265673767277147558922726387912,22036384568219449706671396228045191049735212917)$ |

| Leaf $(l,d)$ | Ordered Bernstein integer endpoint pairs |
| --- | --- |
| $(0,2)$ | $((99689907671946290297835568603646009350727297437,99689917593061637750519700262039142923034578925),(59612855353983990868829378896204338258296054556,59612866936307945200045561318633620962525706963),(34525369599812076744337729780411498914001563173,34525383227788762238595496235245590595099716232),(19192322469759559314864867354823789484272106991,19192338626417117895487755780426679532133828937),(10127595979995003256619270919622542798449046072,10127615274937765745332953095893798827077468487),(4982692200755396260011333564408306083527118441,4982715407331849897372941860717689348415663454),(2279661859328427996677195369700451307062341526,2279689965099999886486435021574674362784564249))$ |
| $(4,4)$ | $((2279661859328427996677195369700451307062341526,2279689965099999886486435021574674362784564249),(1603904273971685930843660821023487612946147297,1603933604542037383764808311788920616376789448),(1080763778478233785839738719878172789983524987,1080794395569953995860275626755235275783433761),(687147415461941712784743755022622025167537370,687179384144697059255316856265435892045687038),(403362808228284167412153689398227164634064715,403396197115961900376305871625424322447516950),(212857348863189791873343572240496176887300787,212892230324030795448008200196448207647617732),(102041448456840859343694500167848043419821011,102077898837568578029149681519873973740595290))$ |
| $(20,6)$ | $((102041448456840859343694500167848043419821011,102077898837568578029149681519873973740595290),(74337473355253626211282232149686010052951067,74374315965953023674435051850730415263839680),(51614095688587983266942529449341655078536382,51651335300929274789060369228611974342888868),(33658978130128028529040721701477775082398448,33696619577945219397380724896352501385471072),(20271357646143225762129662163346662794844622,20309405826309614888336992566239435804923539),(11261872888685083622072880801790883351039286,11300332762002435288439782185760654655017923),(6452412111366000221773785854115621700641263,6491288703467629825691155173464483258176585))$ |
| $(21,6)$ | $((6452412111366000221773785854115621700641263,6491288703467629825691155173464483258176585),(1642951334046916821474690906440360050243240,1682244644932824362942528161168311861335246),(1033514536866892160933282372645616193252531,1073229592170393037342484517054750217558186),(4445989973438324353052968490036575079327958,4486131863624285076893085659672123649267766),(11713515498934500967777035766381041472622782,11754089380202424911087844478629205747537058),(22680326485868443597817850540781787361422118,22721337581069470734833440570455229000306145),(37201624262853917844992109018420470517046600,37243077862421984363309196944573057413989352))$ |
| $(11,5)$ | $((37201624262853917844992109018420470517046600,37243077862421984363309196944573057413989352),(66244219816824866339340625973697836828295565,66286558425127011620260709692808714241355765),(109504762531001941302222917741926952206845114,109548007309773910096132863570211591712378657),(165824863034295267548172553964561078823260318,165869035685935174312360242652164601878372624),(234221587253226874037392382140315651376674551,234266710035693756714739725620348761086240130),(313883246452283013438482528736973670979706812,313929342194448503028933740353884713869902859),(404166500745125068609955502630971652596419236,404213592862593910235990252607716624418752381))$ |
| $(3,3)$ | $((404166500745125068609955502630971652596419236,404213592862593910235990252607716624418752381),(765299517916493289295847398206963579063268929,765350595535175539064216301623044266614150471),(1296378056588436162307864530540394897749001217,1296433494358007742178242310963107233052537260),(1956228364035282190590807467723202566353592671,1956288574156338326365138088944332031854973345),(2746773992920193205707046674462623088546462415,2746839429194301819790671140093966202942810992),(3710069796775132604907988434217202690434962787,3710140959134991638931775071815183181731180793),(4930715902117605607557511905921954850285488758,4930793341701757707097560822396924758293605084))$ |
| $(1,1)$ | $((4930715902117605607557511905921954850285488758,4930793341701757707097560822396924758293605084),(9813300323487497618155605792740963489687592639,9813402871968821979760703824723891064543302249),(18813489568657927283931007070762733056482106096,18813626044253106236818755928819250935177871266),(37345691734749228644171981911828126159718307215,37345874232849005570054817185175278934902741714),(81715904803180442198959852609753621961160387653,81716149995476580820289384351040948420971629966),(181593624087211337486768543666892626609703493046,181593955078450319942895848372500609727750680128),(404520133983702626927737895157844342598516152403,404520582990067349079987388094597859401017819359))$ |


## 17. Derivative residual vectors and event value enclosures
**Definition 17.1 (exact auxiliary derivative centers).** The following ordered vectors are rational decimals in their branch variable order. With $J,F_\lambda,R,r$ as in §5 their residual error bounds are $\|R(Jv+F_\lambda)\|_r/(1-q)<28$ for seven and $<0.352$ for six. They are auxiliary centers for interval residual bounds, not asserted exact derivatives.

### 17.1. Seven derivative vector

| Coordinate index | Rational decimal |
| --- | --- |
| $0$ | $5.91706237693798e-07$ |
| $1$ | $7.75759873824071e-07$ |
| $2$ | $5.29816112608327e-07$ |
| $3$ | $-7.417374969033873e-07$ |
| $4$ | $4.3365143682001e-05$ |
| $5$ | $-4.238685825776797e-05$ |
| $6$ | $4.759368740405433e-05$ |
| $7$ | $0.00028805621692388773$ |
| $8$ | $0.0001106651094205946$ |
| $9$ | $-0.00029507080983464626$ |
| $10$ | $-0.00010358200864759012$ |
| $11$ | $-0.0002154374866487511$ |
| $12$ | $0.00021725078256047388$ |
| $13$ | $-1.8818037739688034e-06$ |
| $14$ | $0.4746885600037451$ |
| $15$ | $-2.3327051294994303e-11$ |
| $16$ | $-7.038947336548688e-10$ |
| $17$ | $0.5266610982030049$ |
| $18$ | $3.142237482806716e-09$ |
| $19$ | $-0.6300447238478494$ |
| $20$ | $0.8391331009538007$ |
| $21$ | $4.223233120114861e-06$ |
### 17.2. Six derivative vector

| Coordinate index | Rational decimal |
| --- | --- |
| $0$ | $3.8752192996296013e-07$ |
| $1$ | $9.791006507392678e-07$ |
| $2$ | $3.259447407975676e-07$ |
| $3$ | $-5.375367428157699e-07$ |
| $4$ | $7.43086613599398e-08$ |
| $5$ | $8.318630407029519e-08$ |
| $6$ | $9.784628264662919e-08$ |
| $7$ | $8.442430134185002e-07$ |
| $8$ | $-9.753094421202827e-07$ |
| $9$ | $3.322034926017845e-08$ |
| $10$ | $3.6804716561343755e-09$ |
| $11$ | $-3.680674861159477e-09$ |
| $12$ | $0.4747004582001957$ |
| $13$ | $1.1917861664248418e-09$ |
| $14$ | $-4.0969356083916385e-09$ |
| $15$ | $0.5266478981816878$ |
| $16$ | $5.980618866024553e-09$ |
| $17$ | $-0.68312879707561$ |
| $18$ | $0.9227802938286296$ |
| $19$ | $-3.1824407261457255e-08$ |
| $20$ | $8.726742674793994e-05$ |

**Definition 17.2 (exact event strength, value and slack enclosures).** The following rational endpoint pairs enclose the event values; their defining expressions are in §§1, 7–8. The denominator is displayed in each fraction.

| Expression | Lower endpoint | Upper endpoint |
| --- | --- | --- |
| $s(\lambda_e)$ | $1687771444630936411526176733702935552786289265827121467098127956911/13479973333575319897333507543509815336818572211270286240551805124608$ | $3375542889261872823236462514870913685808307893321355821395090342493/26959946667150639794667015087019630673637144422540572481103610249216$ |
| $V(\lambda_e)$ | $2317117364181823826932774164490819666675568317510028545774161190247/26959946667150639794667015087019630673637144422540572481103610249216$ | $579279341045455956824889866168926728182610018587358364211006333795/6739986666787659948666753771754907668409286105635143120275902562304$ |
| $s_{\max}(1000)-s(\lambda_e)$ | $609132152936116595578327914308171440583911899767723547757/1684996666696914987166688442938726917102321526408785780068975640576$ | $9746114447169013422019212810392493887755012219098650793483/26959946667150639794667015087019630673637144422540572481103610249216$ |

[CG]: FIB_NATIVE_COMPLETE_CONTINUATION_DISTINGUISHABILITY_GAP.md
[JR]: FIB_NATIVE_COMPLETE_CONTINUATION_JOINT_RECORD_PAYLOAD.md
[FA]: FIB_NATIVE_COMPLETE_CONTINUATION_FINITE_ACTIVITY_FRONTIER.md
[RC]: FIB_NATIVE_COMPLETE_CONTINUATION_RESIDUAL_CONTACT_CURVE.md
[RTII]: https://github.com/the-omega-institute/trureturing/blob/727a29a1f336ad8fcef684f692e6f87dbca08253/docs/develop/theory/ARITHMETIC_HOLOGRAPHIC_RT_II.md

## 追加锚（本行以下为增补区）
