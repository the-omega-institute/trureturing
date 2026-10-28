# Native critical height projection and cutoff overlap bounds

This companion evaluates the projection of the canonical homogeneous response onto the entire closed space of odd height multipliers. Its squared norm is an explicit one-dimensional quadrature, and the existing strict affine gap splits into a height contribution and an orthogonal remainder. An independent canonical dilation comparison gives a strict cutoff-overlap maximum, an exact source pairing and strict integrated clock bounds. These are ordinary conditional mathematical results under the supplied analytic antecedents. Neither canonical absolute sign is evaluated.

Write P for [Native full-state weak binding](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md), through §108, R for [Native exact-critical energy response and scale alternatives](FIB_NATIVE_EXACT_CRITICAL_ENERGY_RESPONSE_AND_SCALE_ALTERNATIVES.md), including §§14–15, N for *Strict nonaffine response at the native critical scale*, and A for *Actual critical solvability and conditional microscopic disappearance*, including §§10–12. The response, strict nonaffinity, actual solvability, matching energy, exact parameter images, admission neighbourhood and actual negative-response occurrence retain their existing credit. A also supplies the microscopic-weak-zero/Coulomb equivalence and the conditional positive-response full-mass macroscopic selection. The complete original sign, occurrence, actual-scale and every-ground-state target remains active.

## 1. The unchanged native problem and its exact microscopic dictionary

**Definition 1.1 (fixed data and complete domains).** Fix any one original admitted signed $\kappa\ne0$, $H$, $I=(l,u)$, $k_0\in I$ and $a,\varepsilon>0$. Every original probability, interval and denominator restriction is retained. In particular $k-\alpha_\kappa$ has a positive margin on $\overline I$. Set

$$
\begin{aligned}
\alpha_\kappa&=\kappa+\kappa^2/H,&d_0&=k_0-\alpha_\kappa>0,&\nu&=\varepsilon/d_0,\\
L_I&=u-l,&\lambda&=\varepsilon^2\pi^2/L_I^2,&
\phi(k)&=(2/L_I)^{1/2}\sin\bigl(\pi(k-l)/L_I\bigr),\\
c_j&=c_\kappa^{(j)}(k_0)\quad(j=0,1,2),&
j_0&=\varepsilon^4|\det(c_0,c_1,c_2)|>0.
\end{aligned}
\tag{1.1}
$$

The entire original rational vector $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$ satisfies, exactly on $I$,

$$
\begin{aligned}
c_\kappa(k_0+h)&=c_0+h c_1+\frac{h^2}{2(1+h/d_0)}c_2,\\
(A_\kappa(k),B_\kappa(k))
 &=\frac{k-2\kappa}{2H(k-\alpha_\kappa)}(H+\kappa-k,-k),\\
\det(c_\kappa,c_\kappa',c_\kappa'')(k)
 &=-\frac{H^2-\kappa^2}{2H^3(k-\alpha_\kappa)^3}\ne0.
\end{aligned}
\tag{1.2}
$$

The third component is retained in the vector identity, with its original jets. None of the jets is independently variable. On the all-real cover $\mathcal C=I\times\mathbb R^3$, $q=(\theta,v,x)$, use raw measure $dY=dk\,dq$ and the complex Hilbert space $L^2(dY)$. Both height faces are Dirichlet. Put

$$
B=-\varepsilon^2\partial_k^2-(c_\kappa(k)\cdot\partial_q)^2,
\qquad S=B-\lambda\ge0.
\tag{1.3}
$$

With phase Fourier factor $(2\pi)^{-3/2}$ and $B_\eta=-\varepsilon^2\partial_k^2+|\eta\cdot c_\kappa(k)|^2$, the entire domains, including underlying $L^2$ membership, are

$$
\begin{aligned}
\mathcal Q
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H_0^1(I)\text{ a.e.},\quad
 \int_{\mathbb R^3}\!\int_I
 (\varepsilon^2|\partial_k\widehat\psi|^2+
 |\eta\cdot c_\kappa|^2|\widehat\psi|^2)dk\,d\eta<\infty\right\},\\
D(S)=D(B)
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H^2(I)\cap H_0^1(I)\text{ a.e.},\quad
 \int_{\mathbb R^3}\|B_\eta\widehat\psi(\cdot,\eta)\|_2^2d\eta<\infty\right\}.
\end{aligned}
\tag{1.4}
$$

Here $\mathcal Q=D(S^{1/2})=D(B^{1/2})$. Every real phase frequency and every complex competitor in these domains is allowed; there is no ordinary phase $H^1$, reality, parity or product-state restriction.

**Definition 1.2 (same source, heat clock and actual critical path).** Let $p_t^B$ be the killed heat kernel of $B$ in raw measure, with pole $o=(k_0,0)$. For $\tau>0$ retain

$$
\begin{aligned}
W_\tau&=\int_\tau^\infty e^{\lambda t}p_t^B(o,\cdot)dt,&
\rho_\tau&=e^{\lambda\tau}p_\tau^B(o,\cdot),&SW_\tau&=\rho_\tau,\\
\int\rho_\tau dY&=e^{\lambda\tau}\mathbb P_{k_0}(\zeta>\tau),&
\int\phi(k)\rho_\tau(k,q)dk\,dq&=\phi(k_0),\\
\mathfrak e_{g,\tau}[\psi]
 &=a\|S^{1/2}\psi\|_2^2-g\int W_\tau|\psi|^2dY,&
E_\tau(g)&=\inf_{\psi\in\mathcal Q,\ \|\psi\|_2=1}\mathfrak e_{g,\tau}[\psi].
\end{aligned}
\tag{1.5}
$$

The two displayed source charges differ; neither is divided by survival probability. The field clock is $B$, independently of $a$. P Propositions 70.2 and 75.2 supply, at each positive $g,\tau$, boundedness of $W_\tau$, operator domain exactly $D(S)$ for $aS-gW_\tau$, essential spectrum $[0,\infty)$ and a finite negative attained bottom. No uniform bound at zero cutoff is asserted.

The actual path and units are

$$
\tau=s^2,\quad g_s=\chi_cs^3,\quad E_s=E_{s^2}(\chi_cs^3),\quad
\epsilon_c(s)=s^2E_s<0,\quad r_s=-\epsilon_c(s)/s^8=-E_s/s^6>0.
\tag{1.6}
$$

Statements about actual states below apply to every prescribed $s_n\downarrow0$ and every choice of actual normalized complex ground states $\psi_{s_n}\in D(S)$. A datum is fixed before its own limit. Occurrence across datasets permits distinct fixed admitted datasets.

**Definition 1.3 (unitary chart, shear and complete field).** For $\xi=(r,y,z,w)$ set

$$
\begin{aligned}
\Xi_s\xi&=(k_0+\varepsilon sr,
 s c_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w),\\
I_s&=((l-k_0)/(\varepsilon s),(u-k_0)/(\varepsilon s)),&\Omega_s&=I_s\times\mathbb R^3,\\
\mathcal U_s\psi&=(j_0s^7)^{1/2}\psi\circ\Xi_s,&\mathcal Q_s&=\mathcal U_s\mathcal Q,\\
X&=\partial_r,&Y_s&=\partial_y+r\partial_z+\frac{r^2}{2(1+\beta_sr)}\partial_w,&\beta_s&=\nu s,\\
b_s[F]&=\|XF\|_2^2+\|Y_sF\|_2^2,&U_s&=s^5W_{s^2}\circ\Xi_s.
\end{aligned}
\tag{1.7}
$$

The raw Jacobian is $j_0s^7$ and $\mathcal U_s$ is unitary. If $A_s$ is the Friedrichs operator of $b_s$, then $D(A_s)=\mathcal U_sD(S)$ and

$$
\begin{aligned}
C_s&=A_s-\lambda s^2=s^2\mathcal U_sS\mathcal U_s^{-1}\ge0,\\
q_s^c[F]&=a b_s[F]-\chi_c\int U_s|F|^2-a\lambda s^2\|F\|_2^2,\\
q_s^c[\mathcal U_s\psi]&=s^2\mathfrak e_{g_s,s^2}[\psi],\qquad
\inf_{\|F\|_2=1}q_s^c[F]=\epsilon_c(s).
\end{aligned}
\tag{1.8}
$$

Write $\mathbf z=(y,z,w)$ and

$$
L_s=\begin{pmatrix}1&\beta_s&0\\0&1&2\beta_s\\0&0&1\end{pmatrix},\quad
\mathscr L_s(r,\mathbf z)=(r,L_s\mathbf z),\quad
\mathcal T_sF=F\circ\mathscr L_s,\quad \widetilde U_s=U_s\circ\mathscr L_s.
\tag{1.9}
$$

This determinant-one phase shear fixes the pole and both moving faces. With $Y=\partial_y+r\partial_z+(r^2/2)\partial_w$, P §97 gives the exact closed-form identity

$$
\widetilde b_s[f]:=b_s[\mathcal T_s^{-1}f]
 =\int_{\Omega_s}(|Xf|^2+(1+\beta_sr)^{-2}|Yf|^2)d\xi.
\tag{1.10}
$$

The denominator is positive on the whole actual interval. Zero extension is used for comparisons on $\mathbb R^4$, preserving both deaths. The complete heat/source correspondence is

$$
\begin{aligned}
P_s(t;\eta,\xi)&=j_0s^7p_{s^2t}^B(\Xi_s\eta,\Xi_s\xi),\\
U_s&=j_0^{-1}\int_1^\infty e^{\lambda s^2t}P_s(t;0,\cdot)dt,\\
(A_s-\lambda s^2)U_s&=s^7\rho_{s^2}\circ\Xi_s.
\end{aligned}
\tag{1.11}
$$

All infinite-time native heat and field limits used here retain their supplied integrated time and spatial tail estimates. A compact positive-time heat limit alone is not an infinite-time interchange.

## 2. Canonical mode, complete coefficients and the response completion

**Definition 2.1 (standing conditional antecedents).** The Engel product, dilation and Haar measure are

$$
\begin{aligned}
(r,y,z,w)(r',y',z',w')
 &=(r+r',y+y',z+z'+ry',w+w'+rz'+r^2y'/2),\\
\delta_R(r,y,z,w)&=(Rr,Ry,R^2z,R^3w),\qquad d\xi=dr\,dy\,dz\,dw,
\qquad Q=7.
\end{aligned}
\tag{2.1}
$$

Let $b[f]=\|Xf\|_2^2+\|Yf\|_2^2$, let $\mathcal Q_E$ be the complex compact smooth core closure in $\|f\|_2^2+b[f]$, and let $\mathcal E=-X^2-Y^2$ be its Friedrichs operator. Write $P_t=e^{-t\mathcal E}$ and $k_t(\xi)=p_E(t;0,\xi)$. The canonical heat supplied in P is conservative, symmetric, strictly positive and continuous. Its proper control distance $d_E$ is homogeneous and

$$
p_E(t;\eta,\xi)\le Ct^{-7/2}e^{-c d_E(\eta,\xi)^2/t},\qquad
V=j_0^{-1}\int_1^\infty k_tdt>0,\qquad
\mathcal EV=j_0^{-1}k_1,\qquad V\le C(1+N)^{-5},
\tag{2.2}
$$

where $N=\max(|r|,|y|,|z|^{1/2},|w|^{1/3})$. In particular $V$ is bounded, smooth and has a positive minimum on every compact set. The source $j_0^{-1}k_1$ has Lebesgue mass $1/j_0$, corresponding to unit native raw-source mass. P also supplies $j_0s^7\rho_{s^2}\circ\Xi_s\to k_1$ in $L^1$ and locally uniformly, local form compactness, complete integrated-field convergence $\|U_s-V\|_\infty\to0$, the supported-strip core approximation, and the both-face native tail estimates.

Retain P's compact zero-energy reconstruction on its specified multiplier right sides, its simple attained threshold mode, and R's compact horizontal-energy gap:

$$
\begin{aligned}
C_*&=\sup_{0\ne f\in\mathcal Q_E}\frac{\int V|f|^2}{b[f]}\in(0,\infty),&
\chi&=\chi_c=a/C_*,&\gamma&=\chi/a,\\
h[f]&=a b[f]-\chi\int V|f|^2\ge0,&H_c&=a\mathcal E-\chi V,\\
p&=\Phi_c>0,&\|p\|_2&=1,&p&\in D(\mathcal E),&\ker H_c&=\mathbb Cp,\\
\mathcal Ep&=\gamma Vp,&\mu&=\int Vp^2>0,&b[p]&=\gamma\mu,\\
h[v]&\ge a\theta b[v]\quad\text{if }b(p,v)=0,&\theta&>0.
\end{aligned}
\tag{2.3}
$$

The gap is in horizontal energy. It is not a positive $L^2$ gap or an all-$L^2$ inverse. The weighted and parity antecedents from P §106 are

$$
rp\in\mathcal Q_E,\quad h[rp]=a,\quad
\int r^2(p^2+|Xp|^2+|Yp|^2)d\xi<\infty,\qquad
\sigma(r,y,z,w)=(-r,y,-z,w),\quad p\circ\sigma=p,\quad V\circ\sigma=V.
\tag{2.4}
$$

Here $X$ reverses parity and $Y$ preserves it. All these heat, localization, hypoellipticity, reconstruction, compactness and mode assertions remain conditional at their supplied scopes. No linked external supplier is reauthenticated in this volume.

**Definition 2.2 (one common bridge and all coefficient terms).** For a height bridge $H_v$ with generator $\partial_r^2$, from $0$ to $r$ in time $t$, put

$$
\begin{aligned}
u(h)&=(1,h,h^2/2),& M_j&=\int_0^tH_v^j u(H_v)u(H_v)^{\mathsf T}dv\quad(j=0,1,2),\\
h_t(r)&=(4\pi t)^{-1/2}e^{-r^2/(4t)},&
\gamma_M(\mathbf z)&=(4\pi)^{-3/2}(\det M)^{-1/2}e^{-\mathbf z^{\mathsf T}M^{-1}\mathbf z/4},\\
p_0(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[\gamma_{M_0}(\mathbf z)]=k_t(r,\mathbf z),\\
p_1(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[-2D\gamma_{M_0}(\mathbf z)[M_1]],\\
p_2(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[3D\gamma_{M_0}(\mathbf z)[M_2]
                   +2D^2\gamma_{M_0}(\mathbf z)[M_1,M_1]],\\
V_j&=j_0^{-1}\int_1^\infty p_j(t;\cdot)dt\quad(j=1,2),&
V_{\rm t}&=j_0^{-1}\int_1^\infty t k_tdt>0.
\end{aligned}
\tag{2.5}
$$

In the first line $u(h)$ is the displayed vector; $D$ differentiates in the positive definite matrix at fixed $\mathbf z$. Every matrix comes from this same bridge. P §107 supplies absolute convergence, the parity of $V_1$ as odd and $V_2,V_{\rm t}$ as even, and

$$
\begin{gathered}
\widetilde U_s=V+\beta_sV_1+\beta_s^2V_2+\lambda s^2V_{\rm t}+\mathcal R_s,
\qquad \|\mathcal R_s\|_\infty\le Cs^{5/2},\\
|V_1|\le C(1+|r|)^{-4},\qquad |V_2|+V_{\rm t}\le C(1+|r|)^{-3}.
\end{gathered}
\tag{2.6}
$$

This is a full-space expansion including all real phases, both moving faces, zero extension and the original infinite-time tail. R additionally supplies $V_j^2\le K_jV$, $V_{\rm t}^2\le K_{\rm t}V$ and $\int V^{1/2}|v|^2\le\Gamma b[v]$. These fields use the heat clock of $B$; $a$ does not enter it.

Define the jointly realized finite numbers

$$
\begin{aligned}
A&=\int r^2|Yp|^2,&B_1&=\int rV_1p^2,&C_2&=\int V_2p^2,&T&=\int V_{\rm t}p^2>0,\\
K_{\rm base}&=3aA-\chi C_2,&D_{\rm clock}&=a+\chi T,\\
t_0&=2A+\gamma B_1,&
C_{108}&=\nu^2\{a(1-A)-\chi(C_2+2B_1)\}-\lambda(a+\chi T).
\end{aligned}
\tag{2.7}
$$

Thus $A=A_2$, $C_2+2B_1=J_2$ and $T=J_{\rm t}$ in P §108. The complete original affine coefficient includes every rational kinetic, $V_1$, $V_2$, source, time-weighted field and threshold term.

**Definition 2.3 (real odd homogeneous response).** Let $\dot{\mathcal H}_-$ be the completion of the real $\sigma$-odd compact smooth core in $\sqrt b$. On this space $a\theta b\le h\le ab$. The potential form extends by $\int V|v|^2\le C_*b[v]$. R's continuous functional and unique Riesz vector satisfy

$$
\ell(v)=2a\int r(Yp)(Yv)+\chi\int V_1pv,\quad
h(\Psi,v)=\ell(v),\quad
D_{\rm resp}=h[\Psi]
 =\sup_{0\ne v\text{ real odd compact smooth}}\frac{\ell(v)^2}{h[v]}<\infty.
\tag{2.8}
$$

Continuity follows, for example, from

$$
|\ell(v)|\le(2a\sqrt A+\chi\sqrt{C_*S_1})\sqrt{b[v]},\qquad
S_1=\int(V_1^2/V)p^2<\infty.
\tag{2.9}
$$

Every odd canonical form vector belongs to this completion by parity averaging core approximants. No global $L^2$, canonical form-domain or native-domain representative of $\Psi$ is assumed. Actual competitors remain unrestricted complex vectors; the completion organizes the response only.

R's response coefficient and canonical normalization are

$$
\begin{aligned}
C_{\rm resp}&=\nu^2(K_{\rm base}-D_{\rm resp})-\lambda D_{\rm clock},\\
W&=j_0V,&W_j&=j_0V_j,&W_{\rm t}&=j_0V_{\rm t},&\overline C&=j_0C_*,\\
G_{108}&=1-A-\gamma(C_2+2B_1),&G_{\rm resp}&=3A-\gamma C_2-D_{\rm resp}/a,\\
\overline D&=1+\gamma T,&\mathscr R&=\lambda/\nu^2=\pi^2d_0^2/L_I^2>0,\\
\frac{C_{108}}{a\nu^2}&=G_{108}-\mathscr R\overline D,&
\frac{C_{\rm resp}}{a\nu^2}&=G_{\rm resp}-\mathscr R\overline D.
\end{aligned}
\tag{2.10}
$$

Since $\gamma=j_0/\overline C$, $p,\Psi,G_{108},G_{\rm resp},\overline D$ are canonical for this precise source. No constituent is independently optimized.

## 3. Height marginals, force and its two-sided tail

**Lemma 3.1 (regularity, positivity and integrability).** Write $\xi=(r,\mathbf z)$ and define, initially almost everywhere in height,

$$
\begin{aligned}
\rho(r)&=\int_{\mathbb R^3}p(r,\mathbf z)^2d\mathbf z,&
m_Y(r)&=\int_{\mathbb R^3}|Yp(r,\mathbf z)|^2d\mathbf z,\\
v_1(r)&=\int_{\mathbb R^3}V_1(r,\mathbf z)p(r,\mathbf z)^2d\mathbf z,&
f(r)&=2r m_Y(r)+\gamma v_1(r),\\
J(r)&=\int_r^\infty f(t)dt.
\end{aligned}
\tag{3.1}
$$

The function $\rho$ has an even continuous representative in $W^{1,1}(\mathbb R)$, $\int\rho=1$, and a positive lower bound on each compact height interval. In particular $\int_K\rho^{-1}<\infty$ for compact intervals $K$, whereas each unbounded half-line has infinite integral of $\rho^{-1}$. The functions $m_Y$ and $v_1$ are respectively even and odd. Both $f$ and $rf$ are integrable and $f$ is odd. Moreover $J$ is even, locally absolutely continuous, integrable, tends to zero at both infinities, and

$$
J'=-f,\qquad
\int_{\mathbb R}|J|\le\int_{\mathbb R}|r f(r)|dr<\infty,\qquad
\int_{\mathbb R}J(r)dr=\int_{\mathbb R}r f(r)dr=t_0.
\tag{3.2}
$$

Proof. The distributional derivative $Xp=\partial_rp$ is in $L^2$, so $p\in H^1(\mathbb R;L^2(\mathbb R^3))$. Its Hilbert-valued continuous representative gives the continuous finite marginal $\rho$. The Hilbert-space product rule gives

$$
\rho'(r)=2\int p(r,\mathbf z)Xp(r,\mathbf z)d\mathbf z,
\qquad \|\rho'\|_1\le2\|p\|_2\|Xp\|_2,
\tag{3.3}
$$

and Fubini gives $\int\rho=1$.

To prove a lower bound rather than infer it from almost everywhere positivity, use boundedness and nonnegativity of $V$. The positive Dyson expansion gives $p=e^{-tH_c}p\ge P_{at}p$ almost everywhere for fixed $t>0$. Choose a compact input set $K_0$ with $0<\int_{K_0}p<\infty$, which exists because $p>0$ and is locally $L^1$. Fix a compact height interval $K$ and a compact phase box $Z$ of positive volume. The continuous strictly positive heat kernel has a positive minimum on $K_0\times(K\times Z)$. Therefore $p\ge c_K>0$ almost everywhere on $K\times Z$, and $\rho\ge c_K^2|Z|$ almost everywhere on $K$. Continuity extends this inequality to all of $K$. This also proves local integrability of $1/\rho$. For any $A<B$, Cauchy–Schwarz and $\int\rho=1$ give

$$
(B-A)^2\le\left(\int_A^B\rho\right)\left(\int_A^B\rho^{-1}\right)
 \le\int_A^B\rho^{-1}.
\tag{3.4}
$$

Letting either endpoint tend to its corresponding infinity proves the asserted divergence on both tails.

The involution $\sigma$ has a phase part of absolute determinant one. Its action on $p,Yp,V_1$ proves all marginal parities. The weighted mode gives $\int r^2m_Y=A<\infty$, and $\int m_Y=\|Yp\|_2^2<\infty$, so $\int|r|m_Y<\infty$ by Cauchy–Schwarz. Boundedness of $V_1$ and $p,rp\in L^2$ give

$$
\int |v_1|\le\|V_1\|_\infty,\qquad
\int |r v_1|\le\|V_1\|_\infty\|rp\|_2\|p\|_2.
\tag{3.5}
$$

Thus $f,rf\in L^1$, and oddness gives $\int f=0$. Consequently, for $r<0$, $J(r)=-\int_{-\infty}^r f(t)dt$; this and the defining positive-side tail show its two zero limits, evenness and $J'=-f$. On each half-line absolute Fubini bounds its $L^1$ norm by the corresponding part of $\int|rf|$. The same absolute justification without absolute values gives $\int J=\int rf$. Substitution in (3.1) yields $2A+\gamma B_1=t_0$. $\square$

## 4. The entire height-multiplier completion

**Theorem 4.1 (isometry, derivative-range density and local representatives).** Let $\mathscr F_o=C_c^\infty(\mathbb R;\mathbb R)_{\rm odd}$ and equip it with

$$
\|F\|_\rho^2=\int_{\mathbb R}\rho(r)|F'(r)|^2dr.
\tag{4.1}
$$

Let $\mathscr W_o$ be its completion and let $L^2_{\rm even}(\rho dr)$ be the real even weighted $L^2$ space. Differentiation extends to an onto isometry

$$
\partial_r:\mathscr W_o\longrightarrow L^2_{\rm even}(\rho dr).
\tag{4.2}
$$

Every element has the unique odd locally absolutely continuous representative $F(r)=\int_0^r q(t)dt$ with $q\in L^2_{\rm even}(\rho dr)$. Define

$$
\mathcal H_h=\overline{\{pF:F\in\mathscr F_o\}}^{\,h}\subset\dot{\mathcal H}_-.
\tag{4.3}
$$

Then $F\mapsto pF$ extends onto $\mathcal H_h$ as an isometry with squared norm multiplied by $a$. For real odd compact smooth $F,G$,

$$
h(pF,pG)=a\int\rho F'G',\qquad
\ell(pF)=a\int f F=a\int J F'.
\tag{4.4}
$$

The image of any $F\in\mathscr W_o$ has local $L^2$ representative $pF$. These statements assert no global $L^2$ or native-domain membership of that product.

Proof. Bounded smooth height multipliers with bounded derivatives preserve $\mathcal Q_E$, by the horizontal product rule and core approximation. Hence $pF\in\mathcal Q_E$ is odd. Multiplying core approximants and averaging parity puts it in $\dot{\mathcal H}_-$. Test the critical weak equation $h(p,\cdot)=0$ with $F^2p$. Using $XF=F'$ and $YF=0$ cancels all terms except

$$
h[pF]=a\int p^2|F'|^2=a\int\rho|F'|^2.
\tag{4.5}
$$

Polarization proves the first identity in (4.4). Also $Y(pF)=F Yp$, so the exact functional (2.8) gives $\ell(pF)/a=\int fF$. Integration by parts with $J'=-f$ and compact $F$ gives $\int JF'$. All terms are absolutely integrable by Lemma 3.1. No phase averaging replaces the original joint realization.

To prove the range in (4.2) is dense, let an even $q\in L^2(\rho dr)$ be orthogonal to every derivative $F'$, $F\in\mathscr F_o$. The even function $w=\rho q$ is locally integrable by Cauchy–Schwarz. Its distributional derivative annihilates odd tests by the assumed orthogonality, and annihilates even tests because their derivatives are odd while $w$ is even. Every test splits into these parities. Thus $w'=0$ as a distribution, and $w=c$ for a constant. If $c\ne0$, then $\int\rho q^2=c^2\int\rho^{-1}=\infty$ by (3.4), a contradiction. Therefore the orthogonal complement is zero. Differentiation is an isometry on the core and has dense range, so its completed range is the whole even Hilbert space.

For an even $q$ in this range, local positivity of $\rho$ gives $q\in L^1_{\rm loc}$, and $F(r)=\int_0^r q$ is odd and locally absolutely continuous. If $F_n'\to q$ in $L^2(\rho dr)$, with $F_n\in\mathscr F_o$, then $F_n(0)=0$ and

$$
\sup_{|r|\le R}|F_n(r)-F(r)|
 \le\left(\int_{-R}^R\rho|F_n'-q|^2\right)^{1/2}
       \left(\int_{-R}^R\rho^{-1}\right)^{1/2}\longrightarrow0.
\tag{4.6}
$$

Conversely every odd locally absolutely continuous $F$ with finite (4.1) has even derivative in $L^2(\rho dr)$ and is recovered this way. This describes the entire completion, without an extra unweighted integral constraint on its derivative.

Equation (4.5) and the equivalence $a\theta b\le h\le ab$ on odd vectors extend the product map into the homogeneous completion, with closed image exactly (4.3). For local representatives, the form bound $\int V|u|^2\le C_*b[u]$ and positive minimum of $V$ on each compact set show that $h$-Cauchy odd core sequences are Cauchy in local $L^2$. The global $L^2$ limits of the two horizontal derivative sequences are the distributional derivatives of this local limit, by compact testing. If its local representative is zero, both derivative limits vanish and its homogeneous norm is zero; thus this realization is injective. Meanwhile (4.6) and $p\in L^2$ give $pF_n\to pF$ in $L^2$ on every bounded height strip, hence on every compact set. Thus the local representative of the image is exactly $pF$. All isometries concern homogeneous energy and its completion. $\square$

## 5. Exact dual norm, quadrature and the height projection

**Theorem 5.1 (finite exact quadrature and projection).** Define

$$
I_h=\int_{\mathbb R}\frac{J(r)^2}{\rho(r)}dr.
\tag{5.1}
$$

Then $0\le I_h\le D_{\rm resp}/a<\infty$. The $h$-orthogonal projection $U_h$ of $\Psi$ onto the entire closed subspace $\mathcal H_h$ is the image of

$$
F_*(r)=\int_0^r\frac{J(t)}{\rho(t)}dt.
\tag{5.2}
$$

Its local representative is $pF_*$, and

$$
\begin{aligned}
h(U_h,pF)&=\ell(pF)\quad(F\in\mathscr W_o),&h[U_h]&=a I_h,\\
\sup_{0\ne F\in\mathscr F_o}\frac{\ell(pF)^2}{h[pF]}&=a I_h,&
\sup_{F\in\mathscr W_o}\{2\ell(pF)-h[pF]\}&=a I_h.
\end{aligned}
\tag{5.3}
$$

In the second supremum the unique maximizer is $F_*$ as an element of the completion. If $I_h>0$, equality in the quotient for a nonzero completed multiplier holds exactly when $F'=cJ/\rho$ almost everywhere for a real $c\ne0$. If $I_h=0$, the restricted functional is zero and every nonzero quotient is zero. There is no claim that a maximizing compact smooth multiplier exists.

Proof. By the Riesz equation for $\Psi$ and (4.5),

$$
\left|\int JF'\right|=|\ell(pF)/a|
 \le\sqrt{D_{\rm resp}/a}\left(\int\rho|F'|^2\right)^{1/2}.
\tag{5.4}
$$

Theorem 4.1 makes this a bounded functional on all of $L^2_{\rm even}(\rho dr)$. Let $q$ be its weighted Riesz representative. For every odd compact smooth $F$,

$$
\int(\rho q-J)F'=0.
\tag{5.5}
$$

Both $\rho q$ and $J$ are even and locally integrable. The parity-distribution argument from Theorem 4.1 gives $\rho q-J=c$ for some constant. Since $J(r)\to0$ at both ends and $\int\rho q^2<\infty$, $c\ne0$ would give

$$
\int\rho q^2=\int\frac{(J+c)^2}{\rho}=\infty,
\tag{5.6}
$$

using the divergent reciprocal-weight tails. Therefore $q=J/\rho$. This proves finiteness in (5.1), and (5.4) gives its stated upper bound. Thus the quadrature is the actual dual norm, rather than a candidate variational expression whose finiteness or density is unproved.

Choose $F_n\in\mathscr F_o$ with $F_n'\to J/\rho$ in the weighted space. Their image limit is an element $U_h\in\mathcal H_h$, with squared $h$ norm $aI_h$. Equation (4.4) passes by continuity to $h(U_h,pF)=\ell(pF)=h(\Psi,pF)$, first on the core and then on the entire closed subspace. Consequently $\Psi-U_h$ is orthogonal to $\mathcal H_h$, proving the projection assertion. Equation (4.6) identifies its local representative with (5.2).

Finally the completed scalar identity is

$$
2\ell(pF)-h[pF]
 =a I_h-a\int\rho\left|F'-J/\rho\right|^2.
\tag{5.7}
$$

It proves the maximization and its uniqueness. Cauchy–Schwarz in $L^2(\rho dr)$ gives the quotient, its equality conditions and its zero case. Derivative-range density proves that the supremum over the compact core has the same value as the completed supremum. The products $pF_*$ and $U_h$ have only the local/homogeneous meaning just proved; they are not used as native or global $L^2$ trials. $\square$

## 6. Decomposing the existing strict affine gap

**Theorem 6.1 (height contribution and orthogonal remainder).** Put

$$
\delta_h=\frac{h[\Psi-U_h]}a\ge0.
\tag{6.1}
$$

Then

$$
\begin{aligned}
D_{\rm resp}/a&=I_h+\delta_h,&
G_{\rm resp}&=3A-\gamma C_2-I_h-\delta_h,\\
I_h-t_0^2&=\frac{h[U_h-t_0rp]}a
 =\int\frac{(J-t_0\rho)^2}{\rho}\ge0,\\
\Delta_{\rm aff}/a&=(I_h-t_0^2)+\delta_h>0,&
\Delta_{\rm aff}&=h[\Psi-t_0rp]=D_{\rm resp}-a t_0^2.
\end{aligned}
\tag{6.2}
$$

Equality $I_h=t_0^2$ holds exactly when $J=t_0\rho$ almost everywhere, equivalently $U_h=t_0rp$ in the homogeneous space. Equality $\delta_h=0$ holds exactly when $\Psi\in\mathcal H_h$. Neither summand in the strict last decomposition is individually proved positive. In particular

$$
G_{\rm resp}\le3A-\gamma C_2-I_h.
\tag{6.3}
$$

Proof. Orthogonality from Theorem 5.1 gives $D_{\rm resp}=h[U_h]+h[\Psi-U_h]$. Substitution in (2.10) proves the first line. To include the whole affine line in the subspace, take an even smooth cutoff $\eta$, one on $[-1,1]$ and zero outside $[-2,2]$, and let $F_R(r)=r\eta(r/R)$. Its derivative is uniformly bounded and tends pointwise to one, so $F_R'\to1$ in $L^2(\rho dr)$ by dominated convergence and $\int\rho=1$. The products $pF_R$ converge in the canonical form norm to $rp$: use $rp\in\mathcal Q_E$, cutoff tails in its derivatives, and the product rule, whose extra term $r\eta_R'p$ is bounded in absolute value by a constant times $p$ on a tail. Thus the image of the constant derivative $1$ is $rp\in\mathcal H_h$.

Equations (3.2) and (5.3) yield $h(U_h,rp)=a\int J=a t_0$, and $h[rp]=a$. Pythagoras for projection onto this line gives the second line of (6.2). Expanding the displayed integral gives the same expression because $\int J=t_0$ and $\int\rho=1$; its equality criterion follows from positivity of $\rho$. The vector $\Psi-U_h$ is orthogonal both to $U_h$ and to $rp$. This yields the affine-gap decomposition. N's strict nonaffinity theorem proves $\Psi\ne trp$ for every real $t$, so the existing $\Delta_{\rm aff}$ is strictly positive. That result excludes simultaneous vanishing of the two summands and gives no separate strictness. Equation (6.3) follows from $\delta_h\ge0$. $\square$

The credited complete affine relations are

$$
\begin{aligned}
C_{\rm aff}(t)&=\nu^2\{a t^2-2a t_0t+K_{\rm base}\}-\lambda D_{\rm clock},\\
C_{\rm aff}(t)-C_{\rm resp}
 &=\nu^2\{\Delta_{\rm aff}+a(t-t_0)^2\},\\
C_{108}-C_{\rm resp}
 &=\nu^2\{\Delta_{\rm aff}+a(t_0-1)^2\}>0,\\
G_{\rm resp}&=G_{108}-(t_0-1)^2-\Delta_{\rm aff}/a.
\end{aligned}
\tag{6.4}
$$

N also proves, for every fixed complex slope $z_0$, $C_{\rm aff}^{\mathbb C}(z_0)-C_{\rm resp}=\nu^2\{\Delta_{\rm aff}+a|z_0-t_0|^2\}>0$. These comparisons evaluate neither absolute sign. Equation (6.2) adds the exact entire-height projection and leaves its orthogonal energy explicit. The new bound is an upper bound on $G_{\rm resp}$ and cannot prove its positivity.

## 7. Exact auxiliary cutoff scaling on the full canonical domain

**Theorem 7.1 (full-domain unitary scaling and all equality cases).** For every auxiliary $\alpha>0$ keep the same canonical heat, source and density and set

$$
V^{[\alpha]}=j_0^{-1}\int_\alpha^\infty k_tdt,\qquad
C_*^{[\alpha]}=\sup_{0\ne f\in\mathcal Q_E}
       \frac{\int V^{[\alpha]}|f|^2}{b[f]},\qquad
\chi^{[\alpha]}=a/C_*^{[\alpha]}.
\tag{7.1}
$$

For $R>0$ let $\mathcal D_Rf(\xi)=R^{-7/2}f(\delta_{1/R}\xi)$. This unitary maps $\mathcal Q_E$ bijectively to itself, and with $R=\sqrt\alpha$,

$$
\begin{aligned}
b[\mathcal D_R f]&=R^{-2}b[f],&
k_t(\delta_R\xi)&=R^{-7}k_{t/R^2}(\xi),\\
V^{[\alpha]}(\xi)&=\alpha^{-5/2}V(\delta_{1/\sqrt\alpha}\xi),&
\mathcal EV^{[\alpha]}&=j_0^{-1}k_\alpha,\\
\int V^{[\alpha]}|\mathcal D_{\sqrt\alpha}f|^2
 &=\alpha^{-5/2}\int V|f|^2,&
C_*^{[\alpha]}&=\alpha^{-3/2}C_*,\\
\chi^{[\alpha]}&=\alpha^{3/2}\chi,&
h^{[\alpha]}[\mathcal D_{\sqrt\alpha}f]&=\alpha^{-1}h[f],
\end{aligned}
\tag{7.2}
$$

where $h^{[\alpha]}=ab-\chi^{[\alpha]}\int V^{[\alpha]}|\cdot|^2$. The identity holds for every complex $f\in\mathcal Q_E$ and every norm. Its closed operator $H^{[\alpha]}=a\mathcal E-\chi^{[\alpha]}V^{[\alpha]}$ has domain $D(\mathcal E)$ and

$$
\mathcal D_{\sqrt\alpha}^{-1}H^{[\alpha]}\mathcal D_{\sqrt\alpha}
 =\alpha^{-1}H_c,\qquad
\ker H^{[\alpha]}=\mathbb C p^{[\alpha]},\quad
p^{[\alpha]}=\mathcal D_{\sqrt\alpha}p.
\tag{7.3}
$$

Equality in $\int V^{[\alpha]}|f|^2\le C_*^{[\alpha]}b[f]$ holds precisely for $f\in\mathbb C p^{[\alpha]}$, including zero.

Proof. The homogeneous degree one of $X,Y$ and Haar Jacobian $R^7$ give the unitarity and form scaling on the compact smooth core. That core is mapped bijectively to itself. Passing to its form closure, and then applying the inverse dilation, proves the full-domain bijection and the first identity for every complex form vector. Form representation gives $\mathcal D_R^{-1}\mathcal E\mathcal D_R=R^{-2}\mathcal E$, including its operator domain, and spectral calculus gives the heat conjugacy. Comparing its kernels under the same change of Haar density and retaining the source at the identity proves $k_t(\delta_R\xi)=R^{-7}k_{t/R^2}(\xi)$.

Change time $t=\alpha u$ in (7.1). The factor $\alpha$ from time and $\alpha^{-7/2}$ from the kernel give exactly $\alpha^{-5/2}V(\delta_{1/\sqrt\alpha}\xi)$. Applying the heat equation against compact smooth tests and using $t^{-7/2}$ at infinity proves its source identity. Since the heat is conservative, this source has Lebesgue mass $1/j_0$ for every $\alpha$. It has not been divided by any additional charge.

Change variables $\xi=\delta_{\sqrt\alpha}\eta$ in the potential pairing; the Jacobian cancels the squared amplitude factor and gives the displayed pairing identity. Divide by the kinetic scaling and take the supremum over the entire domain, using its bijection, to obtain the exact best constant and threshold. Substitution proves the form identity. The field $V^{[\alpha]}$ is bounded for each fixed positive $\alpha$, so bounded perturbation gives operator domain $D(\mathcal E)$. Form representation proves (7.3). Since $h\ge0$ and its form-null space is $\mathbb Cp$, the bijection gives both the stated kernel and every equality case. This uses the full complex domain, without a height-product restriction. $\square$

## 8. Strict overlap maximum, source pairing and integrated clock

**Theorem 8.1 (strict maximum for the original fixed mode).** Hold $p$, the original cutoff one and all original data fixed, and define for $\alpha,t>0$

$$
\mathcal S(\alpha)=\int V^{[\alpha]}p^2,\qquad
\mathcal K(t)=j_0^{-1}\int k_t p^2.
\tag{8.1}
$$

Then

$$
\alpha^{3/2}\mathcal S(\alpha)\le\mu\quad(\alpha>0),
\qquad\text{equality if and only if }\alpha=1.
\tag{8.2}
$$

The exact source pairing and strict clock bounds are

$$
\begin{aligned}
\mathcal K(1)&=\frac32\mu,
&\int(\mathcal EV)p^2&=j_0^{-1}\int k_1p^2=\frac32\int Vp^2,\\
\mu&<T<3\mu,&
1+b_p&<\overline D<1+3b_p,
\qquad b_p:=b[p]=\gamma\mu>0.
\end{aligned}
\tag{8.3}
$$

The source pairing is with the weight $p^2$ and is distinct from the source's raw charge $1/j_0$.

Proof. Apply the nonnegative form in Theorem 7.1 to the original $p$, without changing that vector. Since $ab[p]=\chi\mu$,

$$
0\le h^{[\alpha]}[p]
 =\chi\{\mu-\alpha^{3/2}\mathcal S(\alpha)\}.
\tag{8.4}
$$

If equality holds, the full equality case in Theorem 7.1 puts $p$ in $\mathbb C p^{[\alpha]}$. Both are positive normalized functions, so $p=p^{[\alpha]}$. No nonzero $L^2$ vector can be fixed by $\mathcal D_R$ for $R\ne1$. Indeed for $R>1$, if $g=\mathcal D_Rg$, its squared mass in a control ball $B_E(0,L)$ equals that in $B_E(0,L/R)$. Iteration makes the latter converge to zero: these balls shrink to the identity, which has Haar measure zero, and $|g|^2$ is integrable. Thus the mass in every finite ball is zero. Proper finite control balls exhaust the group, contradicting $g\ne0$. For $R<1$ apply the inverse dilation. Consequently equality forces $\sqrt\alpha=1$, and equality holds there by definition. This proves the sharp equality assertion on the whole positive auxiliary parameter axis.

For $t>0$, $\mathcal K(t)>0$. On a compact positive time interval the canonical bound gives a common supremum bound for $k_t$, and continuity of its kernel and $p^2\in L^1$ give continuity of $\mathcal K$ by dominated convergence. Tonelli yields

$$
\mathcal S(\alpha)=\int_\alpha^\infty\mathcal K(t)dt,
\qquad \mathcal S'(\alpha)=-\mathcal K(\alpha).
\tag{8.5}
$$

The differentiable function $\alpha^{3/2}\mathcal S(\alpha)$ has its maximum at the interior point $1$. Its derivative there vanishes, giving $\mathcal K(1)=3\mu/2$. The source identity from (2.2) proves the second version of the same equality in (8.3); it is an ordinary integrable pairing of the smooth source function with $p^2$.

For the whole time-weighted field, Tonelli gives the exact layer identity

$$
T=\int_1^\infty t\mathcal K(t)dt
 =\mu+\int_1^\infty\mathcal S(\alpha)d\alpha.
\tag{8.6}
$$

These quantities are finite also directly from $\sup k_t\le Ct^{-7/2}$ on $t\ge1$. Strict positivity of $\mathcal K$ on $t>1$ gives $T>\mu$. For $\alpha>1$, (8.2) gives the strict inequality $\mathcal S(\alpha)<\mu\alpha^{-3/2}$. The difference is positive and continuous, so its integral is strictly positive on, for example, any fixed nondegenerate compact interval in $(1,\infty)$. Since $\int_1^\infty\alpha^{-3/2}d\alpha=2$, (8.6) gives $T<3\mu$. Multiplication by $\gamma>0$ and addition of one give the strict bounds for $\overline D$.

Every heat integral and pairing contains the same $j_0^{-1}$. The unitary change of scale changes neither the canonical heat generator nor the original native field clock $B$. The auxiliary $\alpha$ family supplies a comparison; it does not substitute a new native cutoff or a new critical path. $\square$

## 9. Consequences for complete coefficients, with their directions retained

**Corollary 9.1 (strict clock constraints).** For every original admitted fixed datum satisfying the standing antecedents, and for either $X={\rm resp}$ or $X=108$,

$$
G_X-\mathscr R(1+3b_p)
 <\frac{C_X}{a\nu^2}
 <G_X-\mathscr R(1+b_p).
\tag{9.1}
$$

In particular $C_{\rm resp}\ge0$ requires $G_{\rm resp}>\mathscr R(1+b_p)>0$. If $G_{\rm resp}>0$, its crossing ratio satisfies

$$
\frac{G_{\rm resp}}{1+3b_p}
 <Q_{\rm resp}:=\frac{G_{\rm resp}}{\overline D}
 <\frac{G_{\rm resp}}{1+b_p}.
\tag{9.2}
$$

Combining the height projection with the clock gives

$$
\frac{C_{\rm resp}}{a\nu^2}
 <3A-\gamma C_2-I_h-\mathscr R(1+b_p).
\tag{9.3}
$$

Proof. In (2.10), subtract $\mathscr R\overline D$ with $\mathscr R>0$ and apply both strict inequalities in (8.3). This proves (9.1); its upper inequality proves the necessary positivity condition. Division of a positive $G_{\rm resp}$ by the positive strict denominator bounds gives (9.2). Equation (6.3) and the strict upper bound in (9.1) give (9.3). Each step uses quantities of the same source and mode. $\square$

Neither (6.3) nor (9.3) supplies a lower bound on $G_{\rm resp}$. The unevaluated orthogonal energy $\delta_h$ remains in its exact identity. The strict affine gap compares $I_h+\delta_h$ with $t_0^2$ and gives no comparison with $3A-\gamma C_2$. Thus these deductions prove neither $G_{\rm resp}>0$ nor $G_{\rm resp}\le0$, and leave $G_{108}$ unevaluated. The source definitions fix those constants; this is an unresolved comparison, not a proof that the mathematical problem is logically underdetermined. Arbitrary scalar assignments or unrelated potentials are not admitted counterexamples.

## 10. Credited actual energy, solvability and every-state consequences

**Proposition 10.1 (existing actual-state results at their full scopes).** R §§6–11 already supply corrected-core upper recovery, the full original complex-domain lower estimate $q_s^c[F]\ge-Cs^2\|F\|_2^2$, the actual unit-profile lower implication and the matching law

$$
E_s\longrightarrow\min(0,C_{\rm resp}).
\tag{10.1}
$$

P §100 supplies the separate macroscopic upper direction $E_s\le-cs^6$, hence $r_s\ge c>0$. P §105 proves for every prescribed sequence and every actual normalized complex ground-state choice that

$$
r_{s_n}\to\infty
\quad\Longleftrightarrow\quad
\operatorname{dist}_{L^2}(\mathcal U_{s_n}\psi_{s_n},\mathcal O_c)\to0,
\qquad \mathcal O_c=\{e^{i\theta}p:\theta\in\mathbb R\}.
\tag{10.2}
$$

A's actual solvability theorem adds: whenever along such an actual subsequence $E_s\to L$ and $\mathcal U_s\psi_s\rightharpoonup cp$ globally, then

$$
c(L-C_{\rm resp})=0.
\tag{10.3}
$$

These results have the following existing sign-conditional consequences:

$$
\begin{array}{ll}
C_{\rm resp}<0:&E_s\to C_{\rm resp},\quad
\epsilon_c(s)=C_{\rm resp}s^2+o(s^2),\quad
r_s\sim(-C_{\rm resp})s^{-6}\to\infty;\\[2pt]
C_{\rm resp}>0:&0<c\le r_s\le B_*<\infty,\quad
-E_s=\Theta(s^6),\quad-\epsilon_c(s)=\Theta(s^8);\\[2pt]
C_{\rm resp}=0:&E_s\to0,\quad c\le r_s=o(s^{-6}).
\end{array}
\tag{10.4}
$$

On the negative branch every actual normalized complex choice converges to $\mathcal O_c$ under $\mathcal U_s$. On an actually occurring positive-response datum, A further proves, for every such choice, with $F_s=\mathcal U_s\psi_s$ and $f_s=\mathcal T_sF_s$,

$$
\begin{gathered}
F_s\rightharpoonup0,\quad f_s\rightharpoonup0\quad\text{globally in }L^2,
\qquad F_s,f_s\to0\quad\text{in }L^2(K)\text{ for every compact }K,\\
\int U_s|F_s|^2\to0,\quad \int V|F_s|^2\to0,\quad
\|XF_s\|_2^2+\|Y_sF_s\|_2^2\to0,\quad b[f_s]\to0,\\
\operatorname{dist}(F_s,\mathcal O_c)\to\sqrt2,\qquad
\operatorname{dist}(f_s,\mathcal O_c)\to\sqrt2,\qquad
\|F_s\|_2=\|f_s\|_2=1,\\
\int_{\Xi_s(K)\cap\mathcal C}|\psi_s|^2dY\to0,\quad
s^5\int W_{s^2}|\psi_s|^2dY\to0,\quad
s^2(\|S^{1/2}\psi_s\|_2^2+\lambda)\to0.
\end{gathered}
\tag{10.5}
$$

All limits are sequencewise for every prescribed sequence and every actual choice. The weak/local zero limit preserves norm one. A Theorems 10.2 and 11.1 additionally establish, for each prescribed actual sequence and normalized complex ground-state choice, equivalence of microscopic weak zero with the source-centred, full-mass macroscopic Coulomb orbit limit, together with its exact energy and $r_s$ limits. A Corollary 12.1 therefore supplies the positive-response macroscopic coefficient, mass-carrying scale and normalized profile, conditionally on occurrence. It also applies on any actual weak-zero subsequence at response zero, without asserting the existence of such a subsequence. At response zero, (10.3) is vacuous; selection of actual weak-zero subsequences, possible nonzero microscopic core limits and the complete bounded/divergent/mixed $r_s$ and every-choice profile alternatives remain unresolved.

Proof and credit. These are the existing results of P, R and A, rather than new consequences of the projection or cutoff comparison alone. Their essential lower and actual-equation steps are retained as follows. R's recovery uses compact odd approximants of $\Psi$ with each fixed before its $s$-limit. Its lower estimate localizes an arbitrary complex vector, uses the horizontal-energy gap on its complement to $p$, and retains the nonnegative native $C_s$ outside the inner strip. Its actual unit-profile lower implication completes the full complex response square. A hypothetical energy cluster strictly below $\min(0,C_{\rm resp})$ is negative; (10.2) would give a unit profile and that lower implication would contradict the cluster. This is the matching lower argument behind (10.1), not an inference from a trial upper direction.

For the domain bridge in A, the actual energy identity and bounded $U_s$ give $b_s[F_s]\le C$. On the entire native interval $1+\beta_sr=(k-\alpha_\kappa)/d_0$ lies between positive fixed bounds. Equation (1.10) therefore gives $b[f_s]\le\max(1,((u-\alpha_\kappa)/d_0)^2)b_s[F_s]$. Transported native core approximants and zero extension put $f_s$ in $\mathcal Q_E$, with both traces retained. The actual bilinear equation is $\widetilde q_s^c(k,f_s)=s^2E_s\langle k,f_s\rangle$ for native form tests.

To record the checked solvability mechanism, fix a small strip parameter $\delta>0$, then $R=\delta/s$, $u_s=\eta_R f_s$, $\alpha_s=\int Vp u_s/\mu$ and $v_s=u_s-\alpha_sp$, with $\eta_R$ an even cutoff. On a subsequence with weak limit $cp$, $\alpha_s\to c$, $\langle p,u_s\rangle\to c$. Testing the actual equation with $\eta_R^2f_s$ and applying R's supported complement coercivity gives $b[v_s]\le M_\delta s^2$. Both boundary edges in the test $\eta_Rp$ are controlled by

$$
h(\eta_Rp,f_s)=a\int\eta_R'\{pXf_s-(Xp)f_s\}=o_\delta(s^2),
\tag{10.6}
$$

because $\|\eta_R'p\|_2+\|\eta_R'Xp\|_2=o(R^{-2})$, using $rp,rXp\in L^2$. No boundary mass smallness for $f_s$ is required. The complete rational and field expansion gives

$$
\widetilde q_s^c(\eta_Rp,f_s)
 =-\beta_s\ell(v_s)+\alpha_s\beta_s^2K_{\rm base}
 -\chi\lambda s^2\alpha_sT-a\lambda s^2\langle p,u_s\rangle+o_\delta(s^2).
\tag{10.7}
$$

For each fixed real odd compact smooth $z$, its actual test gives

$$
\widetilde q_s^c(\beta_sz,f_s)
 =\beta_s h(z,v_s)-c\beta_s^2\ell(z)+o_{\delta,z}(s^2).
\tag{10.8}
$$

The kinetic remainder on that fixed support is $O_z(s^3)$; higher field and clock terms carry the extra $\beta_s$. Equation (2.6)'s full residual is $o(s^2)$ in (10.7). Complex polarization and parity give $h(z,v_s)-\ell(v_s)=h(z-\Psi,(v_s)_-)$, and hence, after adding the tests and taking $s\to0$ at fixed $\delta,z$,

$$
\left|c\{L-\nu^2(K_{\rm base}-\ell(z))+\lambda D_{\rm clock}\}\right|
 \le\nu\sqrt{aM_\delta}\,\|z-\Psi\|_h.
\tag{10.9}
$$

Only after this limit let compact odd $z$ approach $\Psi$ in $h$. Continuity $\ell(z)\to D_{\rm resp}$ proves (10.3). No native test $\Psi$, unit microscopic limiting norm, positive $L^2$ gap or uniform-in-$\delta$ limit enters.

For positive response, an unbounded $r_s$ subsequence would give unit-orbit convergence by (10.2) and positive lower unscaled energy by R's unit-profile lower implication, contradicting negativity. This proves the eventual upper bound in (10.4); P's macroscopic direction gives its lower bound. Equation (10.3) forces every weak coefficient $c$ to vanish because every energy cluster is nonpositive. The native local compactness and complete integrated-field convergence then give local mass and potential disappearance. The actual energy identity gives $b_s[F_s]\to0$, and the global form comparison gives $b[f_s]\to0$. The exact unit-vector formula $\operatorname{dist}(F_s,\mathcal O_c)^2=2-2|\langle p,F_s\rangle|$ gives distance $\sqrt2$. These are A's existing actual-equation consequences, with no assertion of positive-response occurrence. $\square$

## 11. Current exact ratio images, admission and actual occurrence credit

**Proposition 11.1 (existing R14–15 parameter results).** For fixed admitted $H,I,\kappa$, varying only the interior pole gives exactly

$$
\mathscr R\in\left(\frac{\pi^2(l-\alpha_\kappa)^2}{L_I^2},
                       \frac{\pi^2(u-\alpha_\kappa)^2}{L_I^2}\right).
\tag{11.1}
$$

For $0<H<1/2$, $0<l<u<H$ and an explicit fixed radius $0<b<\min\{l/4,(H-u)/2,H/4\}$, varying the pole and respectively $0<\kappa\le b$ or $-b\le\kappa<0$ gives exactly

$$
\begin{aligned}
\mathscr R_+&=\left(\frac{\pi^2(l-b-b^2/H)^2}{L_I^2},\frac{\pi^2u^2}{L_I^2}\right),\\
\mathscr R_-&=\left(\frac{\pi^2l^2}{L_I^2},\frac{\pi^2(u+b-b^2/H)^2}{L_I^2}\right).
\end{aligned}
\tag{11.2}
$$

Every interior value is attained and neither endpoint is. At fixed $k_0$ instead, the two exact images are

$$
\left[\frac{\pi^2(k_0-b-b^2/H)^2}{L_I^2},\frac{\pi^2k_0^2}{L_I^2}\right),
\qquad
\left(\frac{\pi^2k_0^2}{L_I^2},\frac{\pi^2(k_0+b-b^2/H)^2}{L_I^2}\right].
\tag{11.3}
$$

The included endpoints use $\kappa=b,-b$; the excluded endpoints require $\kappa=0$. R14 proves the larger-height-interval admission neighbourhood for this explicit window, including positive margins of the five original probabilities, denominator margin, determinant lower bound, bounded coefficient derivatives and invertibility of the scalar-fibre numerator map. Its original means are $X=Y=H+\kappa$ and $Z=1-2H$; its full rational third component remains present.

Across distinct fixed admitted datasets in that window, R15 proves that for each prescribed sign of $\kappa$ and fixed $H,a,\varepsilon$, the full ratio image is $(0,\infty)$. Thus, with $Q_{\rm resp}=G_{\rm resp}/\overline D$,

$$
C_{\rm resp}=a\nu^2\overline D(Q_{\rm resp}-\mathscr R).
\tag{11.4}
$$

On an open image $(A_0,B_0)$ in (11.1) or (11.2), negative, positive and zero response occur exactly when $B_0>Q_{\rm resp}$, $A_0<Q_{\rm resp}$ and $A_0<Q_{\rm resp}<B_0$, respectively. Across the full positive-axis image negative response always occurs for each sign; positive and zero response each occur if and only if $G_{\rm resp}>0$. Actual negative-response unit-orbit selection is already nonempty, even at fixed $H,\kappa,k_0,a,\varepsilon$ in the explicit window, by choosing one sufficiently narrow admitted symmetric interval and fixing it before $s\downarrow0$. For $C_{108}$ the same full image gives negative occurrence for each sign, and positive and zero occurrence each if and only if $G_{108}>0$.

Proof and credit. These are R Propositions 14.1 and 15.1 and Corollary 15.2, together with the inherited affine identity. Their parameter reasoning is independent of the present projection. The pole map is strictly increasing since $k_0-\alpha_\kappa>0$, and $\alpha_\kappa'=1+2\kappa/H>0$ on the explicit window. These facts and continuity give all endpoint inclusions above. Strict inequalities in the window allow a slightly enlarged compact parameter-height rectangle. On it all five original probabilities $(k-2\kappa,H+\kappa-k,1-2H,H+\kappa-k,k)$ have positive margins, the denominator remains positive and (1.2)'s determinant is nonzero. The quadratic numerator map is invertible because a zero polynomial would give a vector orthogonal to $c,c',c''$. Compactness supplies the required uniform coefficient and inverse bounds. This is the already established admission neighbourhood; the underlying analytic suppliers retain their conditional scopes.

For completeness the full-image construction takes any $\mathscr R_*>0$, sets $x=\sqrt{\mathscr R_*}/\pi$, $t=\min\{x/2,1/2\}$ and $L_I=H/[2(x+1)]$, chooses $\kappa=\pm\delta$ sufficiently small of the prescribed sign, and sets

$$
l=\alpha_\kappa+(x-t)L_I,\quad k_0=\alpha_\kappa+xL_I,\quad
u=\alpha_\kappa+(x+1-t)L_I.
\tag{11.5}
$$

At $\delta=0$ these endpoints satisfy $0<l<k_0<u<H/2$. By continuity a sufficiently small positive $\delta$ gives $2\delta<\min\{l/4,(H-u)/2,H/4\}$. Take $b=2\delta$. Then every explicit admission condition holds and $\mathscr R=\mathscr R_*$ exactly. Each datum is fixed before its limit. The occurrence statements follow from (11.4) and its affine counterpart. Narrowing a fixed symmetric interval makes $\mathscr R=\pi^2d_0^2/(4h^2)$ arbitrarily large; choosing one such interval gives a negative response and the credited negative branch of (10.4). These are existing exact-image and actual negative-occurrence results. The unevaluated canonical signs remain the only sign predicates in the positive/zero occurrence dictionary at this scope. $\square$

## 12. Unchanged target, attribution and realization boundaries

**Definition 12.1 (entire original decision still required).** The target is to determine the complete $C_{108}$ and $C_{\rm resp}$ signs throughout the original admitted signed-$\kappa$, interval, interior-pole and jointly realized rational-field family; determine actual occurrence or exclusion of every sign; and decide actual exact-critical $r_s$ and every normalized complex ground-state scale/profile behavior, including finer analysis at any response-zero datum. The original path, full complex domains, both deaths, all real phase frequencies, source and heat clock are exactly those of §1.

The new exact identity is $G_{\rm resp}=3A-\gamma C_2-I_h-\delta_h$. A sign decision still requires a same-realization comparison of $\gamma C_2+I_h+\delta_h$ with $3A$, or a genuine faithful alternative proof. Neither the nonnegative residual nor the strict affine margin decides that comparison. Neither canonical $G_{108}$ nor $G_{\rm resp}$ is evaluated here. The ratio images and negative occurrence in §11 are already resolved credit; positive and zero response occurrence across those datasets is equivalent to the unevaluated predicate $G_{\rm resp}>0$. If $G_{\rm resp}\le0$ were proved, the positive ratio and clock would make every complete response negative. If $G_{\rm resp}>0$ were proved, the existing image would provide positive and zero response datasets, while the finer actual decision at zero would still require proof.

At response zero the actual solvability identity supplies no selection. A Theorems 10.2 and 11.1 settle the exact Coulomb energy and full-mass macroscopic profile on every actual microscopic-weak-zero subsequence, with the converse implication, but do not establish that any or every actual choice has such a subsequence. Outside the specified weak-zero case, nonzero microscopic core limits, bounded/divergent/mixed $r_s$ alternatives and the complete every-choice decision at zero remain unresolved. On the conditional positive branch, A Corollary 12.1 supplies the exact Coulomb coefficient of $E_s$ at order $s^6$, the corresponding coefficient of $\epsilon_c(s)$ at order $s^8$, the finite positive $r_s$ limit and the source-centred unit-mass macroscopic orbit at phase scale $g_s^{-1}$ with the original height factor $\phi$. These matching results retain A's fixed-datum, full-complex-domain and analytic hypotheses; they follow from its actual-equation transfer and derived fixed-cutoff variational error, beyond the one-sided macroscopic trial. Positive-response occurrence remains conditional on the unevaluated canonical sign. A centered crossover and any uniform transition across response zero remain unproved. These implications and a strict relative improvement do not complete the original goal.

**Definition 12.2 (source credit and evidence scope).** P §§70–75 supply the native field, charges, domains and positive-cutoff attainment; §§78 and 81 supply the chart, Jacobian and conjugacy. P §§82–88 supply heat, geometry, complete tails, compactness, reconstruction and the simple mode; §§89–91 distinguish tangent onset and the weak disk from actual unit selection. P §§92–96 supply observation, infinite-fibre, quantum and preparation boundaries. P §97 supplies the exact shear; §98 the earlier lower error; §100 the one-sided macroscopic estimate; §§102–105 the actual compact-charge shell, bounded-$r_s$ defect, finite-native weighted resolvent and actual equivalence; §§106–108 the weighted mode, parity, complete field expansion and specified full affine coefficient.

R §§4–5 supply coefficient multipliers, the compact energy gap and homogeneous Riesz response; §§6–7 supply corrected recovery and the complete affine polynomial; §§8–11 supply local coercivity, the improved full-domain lower bound, actual unit-profile lower implication, matching energy and conditional alternatives; §§12–13 supply canonical normalization and boundaries. Current R14–15 separately supply the exact ratio images, enlarged admission neighbourhood and actual negative occurrence. N supplies strict nonaffinity, the positive affine gap and fixed complex-slope refinement. A §§4–6 supply actual solvability and conditional complete microscopic disappearance. A Theorem 10.2 supplies microscopic-weak-zero transfer to the exact Coulomb energy and source-centred full-mass macroscopic profile; Theorem 11.1 supplies its converse; Corollary 12.1 applies these results to every actual choice at positive response and to any actual weak-zero subsequence at response zero. Its transfer reuses P §§71–73 for the full-complex fixed-cutoff Coulomb energy and near-minimizer profile, P §§87 and 104 for compact reconstruction, finite-native heat, short-field convergence and the fixed-cutoff multiplier, and P §90 for actual local compactness. The removed short field has vanishing actual resolvent vector; the auxiliary fixed-cutoff state has a derived variational deficit small relative to $g_s^2$, which supplies the matching and full-mass conclusions. The auxiliary kinetic estimate is not an actual-state kinetic conclusion, and the macroscopic profile convergence is in $L^2$ phase orbit. All these results are credited, with their original lower, actual-equation and conditional analytic hypotheses, rather than counted as new content of this volume.

The additional results in this volume are the full height-multiplier isometry and derivative-range characterization, marginal and force-tail control, finite exact response quadrature and local representative, orthogonal decomposition of the affine gap, full-domain auxiliary cutoff scaling with all equality cases, strict original-mode overlap maximum, source pairing and strict integrated clock bounds. They develop the supplied height-projection and cutoff research proposal with explicit proofs. Author approval, prior assessment and publication records are not mathematical premises. Hilbert-valued Sobolev regularity, weak product testing, Cauchy–Schwarz, distributional differentiation, Riesz representation, density, orthogonal projection, Haar changes of variables, spectral calculus, Tonelli and dominated convergence are mature intermediate tools. The Colin de Verdière–Hillairet–Trélat, Coulhon–Sikora and Fischer–Ruzhansky correspondences remain exactly at their supplied conditional scopes. This is ordinary symbolic reference mathematics, with no new external authentication, executed numerical evidence, Lean/kernel/frozen certification or worldwide originality/absence claim.

**Definition 12.3 (source transport and interpretive limits).** With $J_\kappa=\operatorname{diag}(1,1,\kappa)$ and original real lift $D=\kappa x$, retain

$$
\psi^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1/2}\psi(k,q),\qquad
W_\tau^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1}W_\tau(k,q),\qquad
g_{\rm orig}=|\kappa|g.
\tag{12.1}
$$

The long-time tensor $M=\int_I\phi^2c_\kappa c_\kappa^{\mathsf T}dk>0$ transports to $J_\kappa M J_\kappa^{\mathsf T}$ with signed cross terms. Wavefunctions and raw unit-source kernels have different absolute-Jacobian factors. All results fix signed $\kappa\ne0$ and retain positive native cutoffs. No uniform $\kappa\to0$, actual frozen zero leaf, wrapped cover, torus or cutoff-free native theorem follows. The auxiliary canonical $\alpha$ comparison changes no native datum, path or $B$ heat clock.

The homogeneous response and height projection have only their proved energy/local meanings, without global $L^2$ or native membership of $\Psi$, $U_h$ or $pF_*$. Four canonical coordinates, homogeneous dimension seven, three real phases, rank-three long-time tensor, retained coordinate counts and physical Euclidean space are distinct predicates. No physical dimension or physical $SO(3)$ is selected. Pairing weights, spectral energy and actual source charges remain distinct.

Analytic amplitudes supply no native execution, preparation, actuator, lawful transport, density acquisition, resource or clock bridge. The spectral $E_s$ differs from acquired mass and ML error. No full-channel acquisition, autonomous reduced quantum evolution, generic neural-network, empirical machine-learning, implementation migration, native efficiency/capacity/impossibility or wider-programme completion claim is made. The entire original decision target remains Definition 12.1.

## 追加锚（本行以下为增补区）
