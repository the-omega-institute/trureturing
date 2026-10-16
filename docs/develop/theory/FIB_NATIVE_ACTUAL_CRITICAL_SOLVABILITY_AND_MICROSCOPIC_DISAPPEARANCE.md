# Actual critical solvability and conditional microscopic disappearance

This companion proves an additional constraint from the actual native eigen-equation: if the unscaled spectral energies tend to $L$ and the unitary microscopic states tend weakly to $cp$, then $c(L-C_{\rm resp})=0$. At a fixed admitted datum with positive response, this forces zero microscopic weak profile, zero local mass, vanishing rescaled horizontal and potential energies, and distance $\sqrt2$ from the unit critical orbit. The states retain norm one. All assertions are ordinary conditional mathematics under the precise analytic antecedents below.

Write P for [Native full-state weak binding](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md), R for [Native exact-critical energy response and scale alternatives](FIB_NATIVE_EXACT_CRITICAL_ENERGY_RESPONSE_AND_SCALE_ALTERNATIVES.md), including its current §§14–15, and N for *Strict nonaffine response at the native critical scale*. Their existing matching energy theorem, negative branch, response construction, strict affine gap, exact parameter images and negative-response occurrence receive their original credit. The complete original sign, occurrence and every-ground-state decision remains the target; positive and zero response occurrence still depend on an unevaluated canonical sign.

## 1. The unchanged original complex problem

**Definition 1.1 (fixed native data and full rational vector).** Fix one original admitted signed $\kappa\ne0$, $H$, $I=(l,u)$, $k_0\in I$ and $a,\varepsilon>0$, with every original probability, interval and denominator condition. In particular $k-\alpha_\kappa$ has a positive margin on $\overline I$. Put

$$
\begin{aligned}
\alpha_\kappa&=\kappa+\kappa^2/H,&d_0&=k_0-\alpha_\kappa>0,&\nu&=\varepsilon/d_0,\\
L_I&=u-l,&\lambda&=\varepsilon^2\pi^2/L_I^2,&
\phi(k)&=(2/L_I)^{1/2}\sin\frac{\pi(k-l)}{L_I},\\
c_j&=c_\kappa^{(j)}(k_0)\quad(j=0,1,2),&
j_0&=\varepsilon^4|\det(c_0,c_1,c_2)|>0.
\end{aligned}
\tag{1.1}
$$

The entire original vector $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$ is retained through its exact rational identity

$$
c_\kappa(k_0+h)=c_0+h c_1+\frac{h^2}{2(1+h/d_0)}c_2,
\qquad k_0+h\in I.
\tag{1.2}
$$

This specifies the original third component as well: writing $b_j=b_\kappa^{(j)}(k_0)$, it is exactly $b_0+h b_1+h^2b_2/[2(1+h/d_0)]$. All jets are those of the same original vector, not independently adjustable parameters. In particular no third direction or rational denominator is discarded. The original retained components and determinant are

$$
\begin{aligned}
(A_\kappa(k),B_\kappa(k))
 &=\frac{k-2\kappa}{2H(k-\alpha_\kappa)}(H+\kappa-k,-k),\\
\det(c_\kappa,c_\kappa',c_\kappa'')(k)
 &=-\frac{H^2-\kappa^2}{2H^3(k-\alpha_\kappa)^3}\ne0.
\end{aligned}
\tag{1.3}
$$

Use raw $dY=dk\,dq$ on $\mathcal C=I\times\mathbb R^3$, $q=(\theta,v,x)$. Both actual height faces are Dirichlet. The operators are

$$
B=-\varepsilon^2\partial_k^2-(c_\kappa(k)\cdot\partial_q)^2,
\qquad S=B-\lambda\ge0.
\tag{1.4}
$$

For the unitary phase Fourier transform with factor $(2\pi)^{-3/2}$, write $B_\eta=-\varepsilon^2\partial_k^2+|\eta\cdot c_\kappa(k)|^2$. Including underlying complex $L^2(dY)$ membership, the complete domains are

$$
\begin{aligned}
\mathcal Q
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H_0^1(I)\text{ a.e.},\quad
 \int_{\mathbb R^3}\!\int_I
 \bigl(\varepsilon^2|\partial_k\widehat\psi|^2
       +|\eta\cdot c_\kappa|^2|\widehat\psi|^2\bigr)dk\,d\eta<\infty\right\},\\
D(S)=D(B)
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H^2(I)\cap H_0^1(I)\text{ a.e.},\quad
 \int_{\mathbb R^3}\|B_\eta\widehat\psi(\cdot,\eta)\|_{L^2(I)}^2d\eta<\infty\right\}.
\end{aligned}
\tag{1.5}
$$

Here $\mathcal Q=D(S^{1/2})=D(B^{1/2})$. Every real phase frequency is admitted. These domains impose no ordinary phase $H^1$ condition and no reality, parity or affine restriction on actual states.

**Definition 1.2 (field, source, energy and actual choices).** Let $p_t^B$ be the killed heat kernel of $B$ in raw measure and $o=(k_0,0)$. For $g,\tau>0$ set

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
\tag{1.6}
$$

The raw and $\phi$-weighted charges differ; neither is divided by a survival probability. The field clock is $B$, independently of $a$. P Propositions 70.2 and 75.2 supply, at each fixed positive $g,\tau$, a bounded multiplier $W_\tau$, operator $aS-gW_\tau$ on exactly $D(S)$, essential spectrum $[0,\infty)$ and a finite negative attained bottom. This is a positive-cutoff antecedent, not uniform boundedness at zero cutoff.

On the exact critical path considered here,

$$
\tau=s^2,\qquad g_s=\chi_cs^3,\qquad
E_s=E_{s^2}(\chi_cs^3),\qquad
\epsilon_c(s)=s^2E_s<0,\qquad
r_s=-\epsilon_c(s)/s^8=-E_s/s^6>0.
\tag{1.7}
$$

For every prescribed sequence $s_n\downarrow0$, each $\psi_{s_n}$ may be any actual normalized complex ground state in $D(S)$. No subsequent statement replaces these states by Rayleigh trials or by the larger coarse near-minimizer class.

## 2. Unitary microscopic coordinates, both moving deaths and the canonical source

**Definition 2.1 (exact dictionary).** For $\xi=(r,y,z,w)$ put

$$
\begin{aligned}
\Xi_s\xi&=(k_0+\varepsilon sr,
    s c_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w),\\
I_s&=((l-k_0)/(\varepsilon s),(u-k_0)/(\varepsilon s)),&
\Omega_s&=I_s\times\mathbb R^3,\\
\mathcal U_s\psi&=(j_0s^7)^{1/2}\psi\circ\Xi_s,&
\mathcal Q_s&=\mathcal U_s\mathcal Q,\\
X&=\partial_r,&Y_s&=\partial_y+r\partial_z+
              \frac{r^2}{2(1+\beta_sr)}\partial_w,&\beta_s&=\nu s,\\
b_s[F]&=\|XF\|_2^2+\|Y_sF\|_2^2,&U_s&=s^5W_{s^2}\circ\Xi_s.
\end{aligned}
\tag{2.1}
$$

The exact raw Jacobian is $j_0s^7$, and $\mathcal U_s$ is unitary onto $L^2(\Omega_s,d\xi)$. If $A_s$ is the Friedrichs operator of $b_s$, then $D(A_s)=\mathcal U_sD(S)$ and

$$
\begin{aligned}
C_s&=A_s-\lambda s^2=s^2\mathcal U_sS\mathcal U_s^{-1}\ge0,\\
q_s^c[F]&=a b_s[F]-\chi_c\int U_s|F|^2-a\lambda s^2\|F\|_2^2,\\
q_s^c[\mathcal U_s\psi]&=s^2\mathfrak e_{g_s,s^2}[\psi],\qquad
\inf_{\|F\|_2=1}q_s^c[F]=\epsilon_c(s).
\end{aligned}
\tag{2.2}
$$

Vectors are compared on $\mathbb R^4$ by zero extension. Native derivative vectors are taken on $\Omega_s$ and then extended by zero. Both original Dirichlet deaths remain in the Friedrichs domain. The source and complete integrated field obey

$$
\begin{aligned}
P_s(t;\eta,\xi)&=j_0s^7p_{s^2t}^B(\Xi_s\eta,\Xi_s\xi),\\
U_s&=j_0^{-1}\int_1^\infty e^{\lambda s^2t}P_s(t;0,\cdot)dt,\\
(A_s-\lambda s^2)U_s&=s^7\rho_{s^2}\circ\Xi_s.
\end{aligned}
\tag{2.3}
$$

For the three phase coordinates $\mathbf z=(y,z,w)$ define

$$
L_s=\begin{pmatrix}1&\beta_s&0\\0&1&2\beta_s\\0&0&1\end{pmatrix},\qquad
\mathscr L_s(r,\mathbf z)=(r,L_s\mathbf z),\qquad
\mathcal T_sF=F\circ\mathscr L_s,\qquad
\widetilde U_s=U_s\circ\mathscr L_s.
\tag{2.4}
$$

This determinant-one phase shear fixes the source and both moving faces. P §97 gives the exact closed-form identity, with $Y=\partial_y+r\partial_z+(r^2/2)\partial_w$,

$$
\widetilde b_s[f]:=b_s[\mathcal T_s^{-1}f]
 =\int_{\Omega_s}\left(|Xf|^2+(1+\beta_sr)^{-2}|Yf|^2\right)d\xi.
\tag{2.5}
$$

The denominator is positive throughout the actual interval. This changes coordinates in the original operator, not its competitor class.

**Definition 2.2 (canonical forms and conditional analytic inputs).** On $\mathbb R^4$ use the Engel product and dilation

$$
\begin{aligned}
(r,y,z,w)(r',y',z',w')
 &=(r+r',y+y',z+z'+ry',w+w'+rz'+r^2y'/2),\\
\delta_R\xi&=(Rr,Ry,R^2z,R^3w),\qquad Q=7.
\end{aligned}
\tag{2.6}
$$

Unit Lebesgue measure is Haar measure. Let $b[f]=\|Xf\|_2^2+\|Yf\|_2^2$, let $\mathcal Q_E$ be the complex compact smooth core closure in $\|f\|_2^2+b[f]$, and let $\mathcal E=-X^2-Y^2$ be its Friedrichs operator. Put

$$
\begin{aligned}
P_t&=e^{-t\mathcal E},&k_t&=p_E(t;0,\cdot),&
V&=j_0^{-1}\int_1^\infty k_tdt,&\mathcal EV&=j_0^{-1}k_1,\\
C_*&=\sup_{0\ne f\in\mathcal Q_E}\frac{\int V|f|^2}{b[f]}\in(0,\infty),&
\chi&=\chi_c=a/C_*,\\
h[f]&=a b[f]-\chi\int V|f|^2\ge0,&H_c&=a\mathcal E-\chi V,\\
p&=\Phi_c>0,&\|p\|_2&=1,&p&\in D(\mathcal E),&\ker H_c&=\mathbb Cp,\\
\mathcal Ep&=(\chi/a)Vp,&\mu&=\int Vp^2>0,&a b[p]&=\chi\mu.
\end{aligned}
\tag{2.7}
$$

The canonical heat has mass one; its potential source has Lebesgue mass $1/j_0$. P Proposition 81.2 also supplies $j_0s^7\rho_{s^2}\circ\Xi_s\to k_1$ in $L^1$ and locally uniformly. Thus this limiting source is the original unit raw source in a different density, not a surviving-charge normalization.

Retain the following analytic antecedents at their supplied scopes in P §§82–88, 97 and 104–107 and R §§4–5. The canonical heat is conservative, symmetric, positive and satisfies

$$
p_E(t;\eta,\xi)\le Ct^{-7/2}e^{-c d_E(\eta,\xi)^2/t},\qquad
0<V\le C(1+N)^{-5},\qquad
N=\max(|r|,|y|,|z|^{1/2},|w|^{1/3}).
\tag{2.8}
$$

The native all-height estimates retain both deaths and give

$$
\|U_s-V\|_\infty\to0,\qquad \sup_{s\le s_0}\|U_s\|_\infty<\infty,
\qquad
\sup_{\substack{\xi\in\Omega_s\\|r|\ge R}}\widetilde U_s(\xi)
 \le CR^{-5}+Cs^5\quad(R\ge1,\ sR\le c_0).
\tag{2.9}
$$

The integrated convergence in (2.9) concerns the whole field, including its original infinite-time tail. More explicitly, P §§81–82 and 104 supply local positive-time kernel convergence on compact endpoint sets and the complete tail bound

$$
\sup_{\xi\in\Omega_s}j_0^{-1}\int_M^\infty
 e^{\lambda s^2t}P_s(t;0,\xi)dt\le CM^{-5/2}+Cs^5\quad(M\ge1),
\qquad
\sup_\xi j_0^{-1}\int_M^\infty k_t(\xi)dt\le CM^{-5/2}.
\tag{2.9a}
$$

The integrated limit takes $s\downarrow0$ on a fixed finite positive-time window first and then $M\to\infty$; the spatial-tail step similarly fixes the compact box before its exhaustion. These are inherited estimates, including both deaths, not an exchange of infinite time justified by local convergence alone. Canonical local form compactness, native varying-domain local compactness and the supported height-strip core approximation are retained. P §§87–88 supply compact zero-energy reconstruction on the specified $V^{1/2}$ multiplier right sides with range in $D(\mathcal E)$ and the simple mode (2.7). They assert no bounded inverse of $\mathcal E$ on all $L^2$.

The weighted and parity statements of P Theorem 106.1 are

$$
\begin{gathered}
rp\in\mathcal Q_E,\qquad h[rp]=a,\qquad
\int r^2(p^2+|Xp|^2+|Yp|^2)d\xi<\infty,\\
\sigma(r,y,z,w)=(-r,y,-z,w),\qquad p\circ\sigma=p,\quad V\circ\sigma=V.
\end{gathered}
\tag{2.10}
$$

Fix smooth real even $\eta,\zeta$ with $0\le\eta,\zeta\le1$, $\eta=1$ on $[-1,1]$, $\eta=0$ outside $[-2,2]$ and $\eta^2+\zeta^2=1$. Write $\eta_R(r)=\eta(r/R)$ and similarly for $\zeta_R$. The supplied weighted estimate is

$$
\int|\eta_R'|^2p^2=o(R^{-4}).
\tag{2.11}
$$

A canonical form vector with supported height strictly between both moving faces is native admissible by the supported-strip core approximation and equivalence of the horizontal norms on that strip. No separate phase derivative is part of this assertion. All heat, localization, hypoellipticity, tail, compactness, reconstruction and weighted-mode statements above remain conditional antecedents; no external supplier is reauthenticated here.

## 3. Complete coefficient fields and the inherited homogeneous response

**Definition 3.1 (jointly realized fields).** Let $H_v$ be the height bridge with generator $\partial_r^2$ from zero to $r$ in time $t$. On this single bridge put

$$
\begin{aligned}
u(h)&=(1,h,h^2/2),&S_t&=\sup_{0\le v\le t}|H_v|,\\
M_j&=\int_0^tH_v^j u(H_v)u(H_v)^{\mathsf T}dv\quad(j=0,1,2),\\
\gamma_M(\mathbf z)&=(4\pi)^{-3/2}(\det M)^{-1/2}
 e^{-\mathbf z^{\mathsf T}M^{-1}\mathbf z/4},&
h_t(r)&=(4\pi t)^{-1/2}e^{-r^2/(4t)},\\
p_0(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[\gamma_{M_0}(\mathbf z)]=k_t(r,\mathbf z),\\
p_1(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[-2D\gamma_{M_0}(\mathbf z)[M_1]],\\
p_2(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[
 3D\gamma_{M_0}(\mathbf z)[M_2]+2D^2\gamma_{M_0}(\mathbf z)[M_1,M_1]],\\
V_j&=j_0^{-1}\int_1^\infty p_j(t;\cdot)dt\quad(j=1,2),&
V_{\rm t}&=j_0^{-1}\int_1^\infty t p_0(t;\cdot)dt>0.
\end{aligned}
\tag{3.1}
$$

Here $u(h)$ is the vector in the first line and $D$ differentiates in the positive matrix. P §107 supplies absolute convergence and the full-space complete-field expansion

$$
\begin{gathered}
\widetilde U_s=V+\beta_sV_1+\beta_s^2V_2+\lambda s^2V_{\rm t}+\mathcal R_s,
\qquad \|\mathcal R_s\|_\infty\le Cs^{5/2},\\
|V_1|\le C(1+|r|)^{-4},\qquad |V_2|+V_{\rm t}\le C(1+|r|)^{-3},\\
V_j\circ\sigma=(-1)^jV_j,\qquad V_{\rm t}\circ\sigma=V_{\rm t}.
\end{gathered}
\tag{3.2}
$$

The expansion includes every real phase, both moving deaths, zero extension and the original infinite-time tail. Its source-weighted moment antecedent is, for every fixed $m\in\mathbb N_0$, $t>0$ and $L\ge0$,

$$
h_t(r)\mathbb E_{0,r}^t[
 (\det M_0)^{-1/2}S_t^m\mathbf1_{\{S_t>L\}}]
 \le C_m t^{(m-7)/2}e^{-c_mL^2/t},
\tag{3.3}
$$

with its stated full-moment version at $L=0$. No local heat theorem alone is being extended to (3.2). The clock in all these fields is $B$, not $aB$.

**Definition 3.2 (response and all complete terms).** Forms and inner products are conjugate linear in their first slot. R Theorems 4.1, 5.1 and 5.3 supply

$$
\begin{gathered}
V_1^2\le K_1V,\quad V_2^2\le K_2V,\quad V_{\rm t}^2\le K_{\rm t}V,
\qquad \int V^{1/2}|u|^2\le\Gamma b[u]\quad(u\in\mathcal Q_E),\\
h[v]\ge a\theta b[v]\quad\text{when }b(p,v)=0,\qquad\theta>0.
\end{gathered}
\tag{3.4}
$$

The latter is a horizontal-energy gap, not a positive $L^2$ spectral gap. Let $\dot{\mathcal H}_-$ be the completion of the real $\sigma$-odd compact smooth core in $\sqrt b$. Define

$$
\ell(u)=2a\int r(Yp)(Yu)+\chi\int V_1pu,
\qquad h(\Psi,u)=\ell(u),\qquad
D_{\rm resp}=h[\Psi]=\ell(\Psi).
\tag{3.5}
$$

R's unique real Riesz vector $\Psi\in\dot{\mathcal H}_-$ has no asserted $L^2$, canonical form-domain or native-domain representative. For complex pairings use the complexification and extend $\ell$ complex linearly. The odd part of a canonical vector belongs to that completion by parity averaging core approximants. The even part is annihilated by $\ell$ and is $h$-orthogonal to the odd part.

For completeness, the continuity needed below follows directly from (3.4): for $L\in\{V_1,V_2,V_{\rm t}\}$,

$$
\left|\int Lp v\right|
 \le\left(\int (L^2/V)p^2\right)^{1/2}
          \left(\int V|v|^2\right)^{1/2}
 \le C\sqrt{b[v]},\qquad
\left|\int r(Yp)(Yv)\right|\le\sqrt A\sqrt{b[v]}.
\tag{3.6}
$$

The full coefficients are

$$
\begin{aligned}
A&=\int r^2|Yp|^2,&B_1&=\int rV_1p^2,&C_2&=\int V_2p^2,&T&=\int V_{\rm t}p^2>0,\\
K_{\rm base}&=3aA-\chi C_2,&D_{\rm clock}&=a+\chi T,\\
C_{\rm resp}&=\nu^2(K_{\rm base}-D_{\rm resp})-\lambda D_{\rm clock},\\
C_{108}&=\nu^2\{a(1-A)-\chi(C_2+2B_1)\}-\lambda(a+\chi T).
\end{aligned}
\tag{3.7}
$$

Thus $A=A_2$, $C_2+2B_1=J_2$ and $T=J_{\rm t}$ of P §108. Every kinetic, $V_1$, $V_2$, raw-source, time-weighted field and threshold term is present. These are quantities of one realization, not separately optimized extrema.

## 4. Localization and the actual bilinear equation

**Lemma 4.1 (supported complement coercivity).** Fix sufficiently small $\delta>0$ such that $|r|\le3\delta/s$ lies between both original faces and $3\nu\delta<1/4$. Put $R=\delta/s$. For every complex canonical vector $u$ supported in $|r|\le2R$, define

$$
\alpha(u)=\frac{b(p,u)}{b[p]}=\frac{\int Vp u}{\mu},\qquad v=u-\alpha(u)p.
\tag{4.1}
$$

There are $c_1,C>0$ uniform over sufficiently small fixed $\delta$ such that, for sufficiently small $s$ (allowed to depend on $\delta$),

$$
\widetilde q_s^c[u]\ge c_1 b[v]-Cs^2\|u\|_2^2,
\qquad \widetilde q_s^c=q_s^c\circ\mathcal T_s^{-1}.
\tag{4.2}
$$

Proof. This is the local estimate of R Lemma 8.1; its full complex argument will also specify the extension used in the solvability proof. Choose even $\rho\in C_c^\infty(\mathbb R)$, $0\le\rho\le1$, one on $[-2,2]$ and zero outside $[-3,3]$. Define

$$
d_{s,\delta}(r)=
\begin{cases}
\rho(sr/\delta)((1+\beta_sr)^{-2}-1),&|r|<3\delta/s,\\
0,&|r|\ge3\delta/s.
\end{cases}
\tag{4.3}
$$

Evaluate the rational expression only in its nonsingular branch. Define an estimating form on $\mathcal Q_E$ by

$$
\widehat q_{s,\delta}[u]
 =h[u]+a\int d_{s,\delta}|Yu|^2
 -\chi\int(\beta_sV_1+\beta_s^2V_2+\lambda s^2V_{\rm t}+\mathcal R_s)|u|^2
 -a\lambda s^2\|u\|_2^2.
\tag{4.4}
$$

It agrees exactly with the native sheared form on supported $u$ in the lemma. It is an estimating extension, not a replacement native operator. Uniformly in small fixed $\delta$,

$$
|d_{s,\delta}|\le C\delta,\quad
|d_{s,\delta}|\le C|\beta_sr|\rho(sr/\delta),\quad
|d_{s,\delta}+2\beta_sr\rho(sr/\delta)|
 \le C\beta_s^2r^2\rho(sr/\delta).
\tag{4.5}
$$

The weak equation for $p$ proves (4.1). Also $Vp\in L^2$, so $|\alpha(u)|\le C\|u\|_2$, $\|v\|_2\le C\|u\|_2$, $b(p,v)=0$ and $h[u]=h[v]\ge a\theta b[v]$. These identities hold for complex $u$.

Decompose the kinetic perturbation on $u=\alpha p+v$ using (4.5). Its base linear integral vanishes by parity; its remaining base term is bounded by $Cs^2|\alpha|^2 A$. Its cross term is bounded by $Cs|\alpha|\sqrt{b[v]}$ using $rYp\in L^2$, and its $v$ diagonal is bounded below by $-C\delta b[v]$. In the $V_1$ term the base is zero by parity, the cross is bounded by $Cs|\alpha|\sqrt{b[v]}$ by (3.6), and the diagonal by $Cs b[v]$ by (3.4). For $V_2,V_{\rm t}$ the respective bounds are $Cs^2|\alpha|^2$, $Cs^2|\alpha|\sqrt{b[v]}$ and $Cs^2 b[v]$. Keep the residual on $u$, bounded by $Cs^{5/2}\|u\|_2^2$, and keep the threshold subtraction exactly. Therefore

$$
\widehat q_{s,\delta}[u]
 \ge(a\theta-C\delta-Cs)b[v]
       -Cs|\alpha|\sqrt{b[v]}-Cs^2(|\alpha|^2+\|u\|_2^2).
\tag{4.6}
$$

Choose $\delta$ small, then $s$ small. Young's scalar inequality and $|\alpha|\le C\|u\|_2$ prove (4.2). $\square$

**Lemma 4.2 (global bounds and canonical extension of actual states).** On the actual path, $-C\le E_s<0$ for small $s$. For every actual choice, put $F_s=\mathcal U_s\psi_s$ and $f_s=\mathcal T_sF_s$. Their zero extensions satisfy

$$
\|F_s\|_2=\|f_s\|_2=1,\qquad
b_s[F_s]\le C,\qquad f_s\in\mathcal Q_E,\qquad
b[f_s]\le C.
\tag{4.7}
$$

The original equation is $(aS-\chi_cs^3W_{s^2})\psi_s=E_s\psi_s$ in $D(S)$. Its exact transported bilinear equation is

$$
\widetilde q_s^c(k,f_s)=s^2E_s\langle k,f_s\rangle
\quad\text{for every sheared native form test }k.
\tag{4.8}
$$

Proof. The lower energy bound is R Theorem 9.1, not new content here. To check its needed scope, apply the horizontal IMS identity with $\eta_R,\zeta_R$, $R=\delta/s$, to any sheared native $f$. The inner term is bounded below by (4.2). In the outer term retain the exact nonnegative free threshold form $a\mathcal T_s C_s\mathcal T_s^{-1}$; (2.9) bounds its potential below by $-C_\delta s^5\|\zeta_Rf\|_2^2$. The IMS error is at most $C_\delta s^2\|f\|_2^2$. Thus $q_s^c[F]\ge-Cs^2\|F\|_2^2$ on the entire original complex domain after fixing $\delta$. Infimizing and using negative attainment gives $-C\le E_s<0$. Dropping the threshold subtraction from $A_s$ would not justify the outer estimate.

For actual unit vectors, exact conjugacy gives

$$
a b_s[F_s]=s^2E_s+\chi\int U_s|F_s|^2+a\lambda s^2\le C.
\tag{4.9}
$$

On the whole actual interval,

$$
1+\beta_sr=(k-\alpha_\kappa)/d_0>0,\qquad
1+\beta_sr\le w_{\max}:=(u-\alpha_\kappa)/d_0<\infty.
\tag{4.10}
$$

Equation (2.5) implies

$$
b[f_s]\le\max(1,w_{\max}^2)b_s[F_s].
\tag{4.11}
$$

This also verifies canonical domain membership: approximate by the transported native compact smooth core, extend those core vectors by zero, and use (4.11) on their differences. They are Cauchy in the canonical form norm and converge in $L^2$ to $f_s$. Both Dirichlet traces enter through that core; no boundary distribution or additional phase regularity is inserted. Finally the actual eigenvector belongs to the transported operator domain $D(S)$. Form representation therefore gives (4.8) for every form test, without requiring the test to be an operator-domain vector. $\square$

## 5. Actual eigenstate solvability at a microscopic weak limit

**Theorem 5.1 (actual solvability identity).** Fix any datum of Definition 1.1 satisfying the stated conditional analytic antecedents. For every prescribed $s_n\downarrow0$ and every actual normalized complex ground-state choice in $D(S)$, suppose along a subsequence that

$$
E_{s_n}\to L,\qquad F_{s_n}\rightharpoonup cp
\quad\text{globally in }L^2(\mathbb R^4).
\tag{5.1}
$$

Then

$$
\boxed{c(L-C_{\rm resp})=0.}
\tag{5.2}
$$

Every subsequence has a further subsequence to which (5.1) applies, with $L\in[-C,0]$ and $|c|\le1$. If an entire weakly convergent actual sequence has $c\ne0$, then its energies tend to $C_{\rm resp}\le0$.

Proof. Actual states have zero excess in the coarse native near-minimizer condition. P Theorem 90.1 therefore supplies weak subsequential limits $cp$, $|c|\le1$, local strong convergence and potential convergence along them. Lemma 4.2 supplies bounded unscaled energies, so a further convergent energy subsequence always exists. This uses the disk theorem only for its actual weak-limit and compactness conclusions; it does not infer unit limiting norm.

Work on a subsequence (5.1), suppressing its indices. The unitaries $\mathcal T_s$ and their adjoints converge strongly to the identity. Indeed this holds on compact continuous functions by $L_s\to I$ and determinant one, and then on all $L^2$ by density. Hence $f_s\rightharpoonup cp$ as well. Uniform derivative bounds in (4.7) and testing distributional derivatives against compact smooth functions give

$$
Xf_s\rightharpoonup cXp,\qquad Yf_s\rightharpoonup cYp
\quad\text{in global }L^2.
\tag{5.3}
$$

Every derivative cluster is identified by those tests, so the assertion holds along the entire weakly convergent subsequence.

Fix one sufficiently small $\delta>0$ as in Lemma 4.1, before taking any $s$-limit. Put $R=\delta/s$ and

$$
u_s=\eta_R f_s,\qquad
\alpha_s=\frac{\int Vp u_s}{\mu},\qquad
v_s=u_s-\alpha_sp.
\tag{5.4}
$$

The vector $u_s$ belongs to the supported canonical and native form domains. Multiplying any fixed $L^2$ test by $\eta_R$ converges strongly to that test, so

$$
u_s\rightharpoonup cp,\quad \alpha_s\to c,\quad
\langle p,u_s\rangle\to c,\quad b(p,v_s)=0.
\tag{5.5}
$$

Test (4.8) with $\eta_R^2 f_s$ and take real parts. The height product rule, $Y\eta_R=0$, and the real coefficients give the exact identity

$$
\widetilde q_s^c[u_s]
 =s^2E_s\|u_s\|_2^2+a\int|\eta_R'|^2|f_s|^2
 \le C_\delta s^2.
\tag{5.6}
$$

Apply (4.2) to obtain a finite fixed-$\delta$ bound

$$
b[v_s]\le M_\delta s^2.
\tag{5.7}
$$

No tightness, unit microscopic profile or $\delta$-uniform little-oh has been assumed.

First control the entire canonical boundary pairing in the test $\eta_Rp$. Since $h(p,\eta_Rf_s)=0$, the product rule gives

$$
h(\eta_Rp,f_s)
 =a\int\eta_R'\{p Xf_s-(Xp)f_s\}.
\tag{5.8}
$$

Both cutoff edges are present. The weighted mode estimates imply

$$
\begin{aligned}
\|\eta_R'p\|_2&\le CR^{-2}\|rp\,\mathbf1_{|r|\ge R}\|_2=o(R^{-2}),\\
\|\eta_R'Xp\|_2&\le CR^{-2}\|rXp\,\mathbf1_{|r|\ge R}\|_2=o(R^{-2}).
\end{aligned}
\tag{5.9}
$$

Cauchy–Schwarz with (4.7) thus proves $h(\eta_Rp,f_s)=o_\delta(s^2)$. This estimate requires no small mass of $f_s$ in the boundary annulus. Both moving original faces remain outside the test support.

Next evaluate every perturbation term in this first test. Write $d=d_{s,\delta}$. Parity and dominated convergence using $rYp\in L^2$ give

$$
\int d|Yp|^2=3\beta_s^2A+o_\delta(s^2),\qquad
\|(d/\beta_s+2r)Yp\|_2\to0.
\tag{5.10}
$$

For the first identity subtract the exactly odd term $-2\beta_sr\rho(sr/\delta)$; the remaining coefficient divided by $\beta_s^2$ tends to $3r^2$ and is dominated by $Cr^2$. For the second, the coefficient tends pointwise to zero and is bounded by $C|r|$, including outside the auxiliary support.

Since $Yu_s=\eta_RYf_s$, the rational kinetic perturbation in $\widetilde q_s^c(\eta_Rp,f_s)$ is exactly $a\int d(Yp)(Yu_s)$. Inserting (5.4), (5.7) and (5.10) gives

$$
3a\alpha_s\beta_s^2A-2a\beta_s\int r(Yp)(Yv_s)+o_\delta(s^2).
\tag{5.11}
$$

The estimating extension is evaluated separately on $p,v_s$ only to compute this expression; their sum $u_s$ retains exact native agreement.

For the complete potential paired with $p u_s$, the $V_1$ base is zero by parity and its complement gives $-\chi\beta_s\int V_1p v_s$. The $V_2$ base is $-\chi\alpha_s\beta_s^2C_2$, with complement $O_\delta(s^3)$ by (3.6) and (5.7). The field-clock term is $-\chi\lambda s^2\alpha_sT$, again with complement $O_\delta(s^3)$. The residual costs $Cs^{5/2}\|p\|_2\|u_s\|_2=o(s^2)$. Retaining the threshold subtraction exactly, (5.8)–(5.11) yield

$$
\begin{aligned}
\widetilde q_s^c(\eta_Rp,f_s)
 ={}&-\beta_s\ell(v_s)+\alpha_s\beta_s^2K_{\rm base}
      -\chi\lambda s^2\alpha_sT\\
 &-a\lambda s^2\langle p,u_s\rangle+o_\delta(s^2).
\end{aligned}
\tag{5.12}
$$

This is an unnormalized polarized equation, so no Rayleigh norm correction is missing.

Now fix a real odd $z\in C_c^\infty(\mathbb R^4)$, independent of $s$. For sufficiently small $s$, its support and derivative supports lie where $\eta_R=1$ and between both faces. Thus $h(z,f_s)=h(z,u_s)=h(z,v_s)$. On this fixed support, $(1+\beta_sr)^{-2}-1=-2\beta_sr+O_z(s^2)$. Pairing the actual equation with $\beta_sz$ gives the expansion

$$
\widetilde q_s^c(\beta_sz,f_s)
 =\beta_s h(z,v_s)-c\beta_s^2\ell(z)+o_{\delta,z}(s^2).
\tag{5.13}
$$

Indeed the leading perturbations are $-2a\beta_s^2\int r(Yz)(Yf_s)-\chi\beta_s^2\int V_1z f_s$, tending after division by $\beta_s^2$ to $-c\ell(z)$ by (5.3). Uniform canonical derivatives bound the kinetic Taylor remainder by $O_z(s^3)$. All $V_2$, field-clock, threshold and residual pairings in this test carry the extra factor $\beta_s$ and are $o_z(s^2)$. This calculation is for fixed $z$, not for growing response approximants.

Add (5.12) and (5.13), and apply (4.8) to $\eta_Rp+\beta_sz$. After division by $s^2$ its right side tends to

$$
E_s\{\langle p,u_s\rangle+\beta_s\langle z,f_s\rangle\}\to Lc.
\tag{5.14}
$$

The only left-side term not already assigned a limit is
$\beta_s\{h(z,v_s)-\ell(v_s)\}/s^2$. Let $(v_s)_-$ be the odd part. The complexified Riesz equation and parity give

$$
h(z,v_s)-\ell(v_s)=h(z-\Psi,(v_s)_-),\qquad
h[(v_s)_-]\le a b[v_s].
\tag{5.15}
$$

The odd part belongs to the homogeneous completion by parity averaging core approximants. Consequently (5.7) and Cauchy–Schwarz imply

$$
\left|\frac{\beta_s}{s^2}\{h(z,v_s)-\ell(v_s)\}\right|
 \le\nu\sqrt{aM_\delta}\,\|z-\Psi\|_h.
\tag{5.16}
$$

Take the $s$-limit at this fixed compact $z$. Equations (5.12)–(5.16) give

$$
\left|c\{L-\nu^2(K_{\rm base}-\ell(z))+\lambda D_{\rm clock}\}\right|
 \le\nu\sqrt{aM_\delta}\,\|z-\Psi\|_h.
\tag{5.17}
$$

Choose real odd compact $z_m\to\Psi$ in $h$. For each $m$ the $s$-limit in (5.17) has already been taken. Now let $m\to\infty$, keeping $\delta$ fixed. Continuity gives $\ell(z_m)\to D_{\rm resp}$ and the right side tends to zero, proving (5.2). The order is fixed original datum and fixed $\delta$, then $s\to0$ for each fixed compact test, then homogeneous approximation. There is no simultaneous unbounded-test limit, native or $L^2$ test $\Psi$, positive $L^2$ gap, or $\delta$-uniform little-oh.

Finally, on an entire actual sequence with weak limit $cp\ne0$, every convergent energy subsubsequence must have limit $C_{\rm resp}$ by (5.2). Boundedness of the energies forces the whole energy sequence to tend to that value; negativity makes it nonpositive. This proves the last assertion. $\square$

## 6. Complete microscopic disappearance on the conditional positive branch

**Theorem 6.1 (every actual choice has zero microscopic profile).** Suppose an actually admitted fixed datum satisfying the stated antecedents has $C_{\rm resp}>0$. For every prescribed sequence $s_n\downarrow0$ and every actual normalized complex ground-state choice in $D(S)$, the zero-extended vectors $F_s=\mathcal U_s\psi_s$ and $f_s=\mathcal T_sF_s$ satisfy

$$
\begin{aligned}
F_s&\rightharpoonup0&&\text{globally in }L^2,\qquad
&F_s&\to0&&\text{in }L^2(K)\text{ for every compact }K,\\
f_s&\rightharpoonup0&&\text{globally in }L^2,
&f_s&\to0&&\text{in }L^2(K)\text{ for every compact }K,\\
\int U_s|F_s|^2&\to0,&\int V|F_s|^2&\to0,\\
\|XF_s\|_2^2&\to0,&\|Y_sF_s\|_2^2&\to0,&b[f_s]&\to0,\\
\operatorname{dist}_{L^2}(F_s,\mathcal O_c)&\to\sqrt2,&
\operatorname{dist}_{L^2}(f_s,\mathcal O_c)&\to\sqrt2,&
\mathcal O_c&=\{e^{i\theta}p:\theta\in\mathbb R\}.
\end{aligned}
\tag{6.1}
$$

Every vector still has norm one. In native variables the exact consequences include

$$
\begin{aligned}
\int_{\Xi_s(K)\cap\mathcal C}|\psi_s|^2dY&\to0
       &&\text{for every fixed compact }K\subset\mathbb R^4,\\
s^5\int W_{s^2}|\psi_s|^2dY&\to0,&
s^2\bigl(\|S^{1/2}\psi_s\|_2^2+\lambda\bigr)&\to0.
\end{aligned}
\tag{6.2}
$$

The limits hold for every chosen actual family as $s\downarrow0$, in the sequencewise sense just stated. They assert no replacement mass-carrying scale or normalized replacement profile.

Proof. Every weak actual cluster has the form $cp$. Pass further to a convergent energy subsequence by Lemma 4.2. The limit $L$ is nonpositive. Theorem 5.1 and $C_{\rm resp}>0$ force $c=0$. If a fixed global $L^2$ pairing did not tend to zero, a witnessing subsequence would have a weakly convergent further subsequence with a nonzero pairing, a contradiction. The inherited native local compactness gives the same argument for every compact local $L^2$ norm. Hence the global weak and local strong assertions hold for the entire prescribed actual sequence.

For the potential, (2.9) and the unit norm reduce the problem to $V$. On a fixed compact set use local strong convergence. On its complement use the decaying supremum of $V$ from (2.8) and $\|F_s\|_2=1$. Take $s\to0$ first, then exhaust by compacts. This proves both potential limits in (6.1), equivalently $\|U_s^{1/2}F_s\|_2\to0$ and $\|V^{1/2}F_s\|_2\to0$. Equation (4.9), bounded $E_s$ and these limits imply $b_s[F_s]\to0$. Its two terms are nonnegative, so they vanish separately. Equation (4.11) gives $b[f_s]\to0$.

For unit vectors, the exact identity

$$
\operatorname{dist}(F_s,\mathcal O_c)^2=2-2|\langle p,F_s\rangle|
\tag{6.3}
$$

and the weak limit give distance $\sqrt2$. Strong convergence of $\mathcal T_s^*$ gives the sheared weak limit. For each compact $K$, the images $\mathscr L_s(K)$ lie in one fixed larger compact for small $s$; the determinant-one change of variables bounds the local norm of $f_s$ by that of $F_s$ there. This proves its local strong limit, and (6.3) applies to $f_s$ as well.

Finally unitarity, (2.1) and (2.2) give (6.2) exactly. A failure for any chosen family at small $s$ would supply a prescribed sequence contradicting the statements proved above. Since all norms remain one, the weak/local limit zero is not global strong convergence to zero. Nor does division of $b_s[F_s]=o(1)$ by $s^2$ prove vanishing unscaled native kinetic energy. The local disappearance refers to fixed microscopic compacts, not every fixed unscaled source neighbourhood. $\square$

## 7. Existing actual energy, negative branch and strict nonaffine credit

**Proposition 7.1 (credited results and the precise added information).** R Theorems 6.1, 9.1, 10.1 and 11.1 already establish corrected-core upper recovery, the whole-domain $O(s^2)$ lower error, the actual unit-profile lower implication and the matching limit

$$
E_s\longrightarrow\min(0,C_{\rm resp}).
\tag{7.1}
$$

P Proposition 100.1 gives only the independent macroscopic upper direction $E_s\le-c_0s^6$, hence $r_s\ge c_0>0$. P Theorem 105.1 supplies, for every prescribed sequence and every actual normalized complex choice in $D(S)$,

$$
r_{s_n}\to\infty
\quad\Longleftrightarrow\quad
\operatorname{dist}(F_{s_n},\mathcal O_c)\to0.
\tag{7.2}
$$

Under these credited results, R Theorem 11.2 gives

$$
\begin{array}{ll}
C_{\rm resp}<0:&
E_s\to C_{\rm resp},\quad
\epsilon_c(s)=C_{\rm resp}s^2+o(s^2),\quad
r_s\sim(-C_{\rm resp})s^{-6}\to\infty;\\[2pt]
C_{\rm resp}>0:&
0<c_0\le r_s\le B_*<\infty,\quad
-E_s=\Theta(s^6),\quad-\epsilon_c(s)=\Theta(s^8);\\[2pt]
C_{\rm resp}=0:&E_s\to0,\quad c_0\le r_s=o(s^{-6}).
\end{array}
\tag{7.3}
$$

The negative case gives global unit-orbit convergence for every actual choice by (7.2). In the positive case Theorem 6.1 adds zero microscopic weak profile and the exact orbit-distance limit $\sqrt2$ to the previously proved bounded-$r_s$ defect. At response zero, (5.2) degenerates to $c(0-0)=0$ and selects no branch.

These are credited implications, with the original lower arguments retained. R's upper construction uses compact odd response approximants, each fixed before its $s$-limit, rather than an $L^2$ trial $\Psi$. Its matching argument uses the full-domain lower bound, actual negative attainment and (7.2), not only trial recovery. In fact a hypothetical energy limit strictly below $\min(0,C_{\rm resp})$ is negative, so (7.2) supplies a unit profile and R's unit-profile lower implication forces a contradiction. Positive-response boundedness of $r_s$ follows because an unbounded subsequence would likewise give a unit profile and a strictly positive lower energy, contradicting native negativity. The macroscopic direction independently supplies its positive lower bound. These are existing R proofs, not new matching or negative-branch content of this companion.

N Theorems 6.1, 7.1 and 8.1 already prove strict real nonaffinity and the fixed complex-affine refinement. In their notation,

$$
\begin{gathered}
t_0=2A+(\chi/a)B_1,\qquad
\Delta_{\rm aff}=h[\Psi-t_0rp]=D_{\rm resp}-a t_0^2>0,\\
C_{\rm aff}(t)=\nu^2\{a t^2-2a t_0t+K_{\rm base}\}-\lambda D_{\rm clock},\\
C_{\rm resp}=\min_{t\in\mathbb R}C_{\rm aff}(t)-\nu^2\Delta_{\rm aff},\\
C_{108}-C_{\rm resp}=\nu^2\{\Delta_{\rm aff}+a(t_0-1)^2\}>0,\\
C_{\rm aff}^{\mathbb C}(z_0)-C_{\rm resp}
 =\nu^2\{\Delta_{\rm aff}+a|z_0-t_0|^2\}>0
 \quad(z_0\in\mathbb C\text{ fixed}).
\end{gathered}
\tag{7.4}
$$

Strictness evaluates neither absolute sign. The clock terms remain in every full coefficient and cancel only in these exact differences. A nonpositive affine coefficient forces negative response, including an affine zero boundary. Nonnegative response forces all these affine coefficients to be strictly positive. None of these inherited comparisons imposes an affine competitor class on actual ground states or provides a uniform conclusion for slopes diverging with $s$.

## 8. Current DEV14–15 ratio, admission and occurrence credit

**Definition 8.1 (canonical sign and the already established ratio maps).** R Proposition 12.1 gives canonical quantities

$$
\begin{aligned}
W&=j_0V,&W_j&=j_0V_j,&W_{\rm t}&=j_0V_{\rm t},&\overline C&=j_0C_*,\\
G_{108}&=1-A-(\chi/a)(C_2+2B_1),&
G_{\rm resp}&=(K_{\rm base}-D_{\rm resp})/a,&
\overline D&=1+(\chi/a)T>1.
\end{aligned}
\tag{8.1}
$$

These, the mode and the energy-space response are canonical after the displayed normalization. With $\mathscr R=\lambda/\nu^2$,

$$
\frac{C_{108}}a=\nu^2(G_{108}-\mathscr R\overline D),\qquad
\frac{C_{\rm resp}}a=\nu^2(G_{\rm resp}-\mathscr R\overline D),\qquad
G_{\rm resp}=G_{108}-(t_0-1)^2-\Delta_{\rm aff}/a.
\tag{8.2}
$$

Current R Proposition 14.1, credited separately, already proves the exact fixed-interval pole image

$$
\mathscr R=\pi^2(k_0-\alpha_\kappa)^2/L_I^2,\qquad
\left(\frac{\pi^2(l-\alpha_\kappa)^2}{L_I^2},
      \frac{\pi^2(u-\alpha_\kappa)^2}{L_I^2}\right).
\tag{8.3}
$$

It also proves the exact signed-window images. For $0<H<1/2$, $0<l<u<H$ and an explicit fixed radius
$0<b<\min\{l/4,(H-u)/2,H/4\}$, varying $k_0\in I$ and respectively $0<\kappa\le b$ or $-b\le\kappa<0$ gives exactly

$$
\begin{aligned}
\mathscr R_+&=\left(\frac{\pi^2(l-b-b^2/H)^2}{L_I^2},
                         \frac{\pi^2u^2}{L_I^2}\right),\\
\mathscr R_-&=\left(\frac{\pi^2l^2}{L_I^2},
                         \frac{\pi^2(u+b-b^2/H)^2}{L_I^2}\right).
\end{aligned}
\tag{8.4}
$$

Every interior value is attained and neither endpoint is. With $k_0$ fixed instead, the exact images are

$$
\left[\frac{\pi^2(k_0-b-b^2/H)^2}{L_I^2},\frac{\pi^2k_0^2}{L_I^2}\right),
\qquad
\left(\frac{\pi^2k_0^2}{L_I^2},\frac{\pi^2(k_0+b-b^2/H)^2}{L_I^2}\right].
\tag{8.5}
$$

The included endpoints use $\kappa=b,-b$; the excluded endpoints require $\kappa=0$. R14 also verifies the required larger-height-interval admission neighbourhood: positive margins for all five original probabilities, a denominator margin, nonzero determinant and bounded derivatives on a slightly enlarged compact rectangle, and uniform invertibility of the quadratic scalar-fibre numerator map. The original means are $X=Y=H+\kappa$, $Z=1-2H$ and the original rational third component remains present. The heat and other analytic suppliers keep their conditional scopes; there is no unexplained further shrink of this explicit admission window.

Current R Proposition 15.1, credited separately, proves that across distinct datasets in that explicit window, for each prescribed sign of $\kappa\ne0$ and fixed $H,a,\varepsilon$, the exact ratio image is $(0,\infty)$. For reference its construction is: given $\mathscr R_*>0$, put $x=\sqrt{\mathscr R_*}/\pi$, $t=\min\{x/2,1/2\}$ and $L_I=H/[2(x+1)]$; choose $\kappa=\pm\delta$ of the prescribed sign sufficiently small and set

$$
l=\alpha_\kappa+(x-t)L_I,\qquad
k_0=\alpha_\kappa+xL_I,\qquad
u=\alpha_\kappa+(x+1-t)L_I.
\tag{8.6}
$$

Continuity from $\delta=0$ gives $2\delta<\min\{l/4,(H-u)/2,H/4\}$, so $b=2\delta$ is admitted and (8.3) equals $\mathscr R_*$. Each constructed dataset is fixed before its own $s$-limit. This is the existing full-image result, not authorization to vary a datum with $s$.

Current R Corollary 15.2, credited separately, sets $Q_{\rm resp}=G_{\rm resp}/\overline D$ and gives

$$
C_{\rm resp}=a\nu^2\overline D(Q_{\rm resp}-\mathscr R).
\tag{8.7}
$$

On any open image $(A,B)$ in (8.3)–(8.4), negative, positive and zero response occur exactly when $B>Q_{\rm resp}$, $A<Q_{\rm resp}$ and $A<Q_{\rm resp}<B$, respectively. Across the datasets of R15.1, negative response always occurs for each sign; positive and zero response each occur if and only if $G_{\rm resp}>0$. In particular negative response and actual unit-orbit selection already occur at fixed $H,\kappa,k_0,a,\varepsilon$ in the explicit window by taking one sufficiently narrow fixed symmetric interval about $k_0$. Its ratio tends to infinity as the interval narrows; choose an admitted interval with $\mathscr R>Q_{\rm resp}$ and fix it before $s\downarrow0$. The negative branch of (7.3) and every-ground-state orbit convergence then apply.

For the affine coefficient, put $Q_{108}=G_{108}/\overline D$. Equation (8.2) gives $C_{108}=a\nu^2\overline D(Q_{108}-\mathscr R)$. The same established full ratio image therefore gives negative $C_{108}$ occurrence for each sign; across those datasets positive and zero $C_{108}$ each occur if and only if $G_{108}>0$. This is a direct algebraic consequence of current R14–15 and the inherited complete affine formula, with no evaluation of $G_{108}$.

The ratio maps, their admission scope and this actual negative-response occurrence are resolved current DEV credit. Older blanket statements leaving them open are superseded at precisely these scopes. Neither R14–15 nor the present theorem evaluates $G_{\rm resp}>0$. Thus Theorem 6.1 remains conditional, while the negative branch is known to be nonempty.

## 9. The full target, source correspondence and unresolved boundaries

**Definition 9.1 (unchanged decision target).** The entire original target remains to determine the complete $C_{108}$ and $C_{\rm resp}$ signs throughout the original admitted signed-$\kappa$, interval, interior-pole and jointly realized rational-field family; characterize actual occurrence or exclusion of all signs; and decide the actual exact-critical energy scale and every normalized complex ground-state profile, including the finer response-zero case. The original complex domains, exact path, both deaths, source, clock and all quantifiers remain those of §§1–3.

The remaining absolute comparisons are $G_{108}$ and $G_{\rm resp}$ against the original ratio times $\overline D$. Their canonical values have not been evaluated here. A negative clock contribution, strict relative affine improvement or separately optimized constituent bound cannot supply those comparisons. The exact ratio maps and negative-response occurrence are already available by §8; they are not missing premises. Actual positive and zero response occurrence across the proved datasets is equivalent to the unevaluated inequality $G_{\rm resp}>0$.

At response zero, (7.3) leaves bounded, divergent or mixed subsequential behavior of $r_s$ undecided. The new solvability identity is then vacuous. The sequencewise equivalence (7.2) remains available but does not select its divergent branch. At positive response the added conclusion is complete disappearance at the stated microscopic scale, alongside the existing $\Theta(s^6)$ unscaled energy order; the exact finer coefficient, a scale carrying the escaped unit mass, its normalized profile and a centered crossover remain unproved. A macroscopic Coulomb trial supplies an upper energy direction, not these matching conclusions. No such stronger result is inferred from a local zero limit.

**Definition 9.2 (attribution and proof boundary).** P §§70–75 supply the native field, charges, complete domains and positive-cutoff negative attainment; §§78 and 81 supply the chart, $j_0$ and exact conjugacy. P §§82–88 supply heat, integrated tails, local compactness, reconstruction and the attained simple critical mode; §§89–91 distinguish tangent onset and the coarse native weak disk from actual selection. P §§92–96 supply the observation, infinite-fibre, interacting quantum and analytic-preparation boundaries. P §97 supplies the exact shear; §98 the older $O(s^{2/3})$ lower error; §100 the one-sided macroscopic bound; §§102–105 the compact-charge shell, bounded-$r$ defect, global native weighted resolvent and actual scale/no-loss equivalence; §§106–108 the weighted mode, parity, complete-field expansion and full specified affine coefficient.

R §§4–5 supply coefficient multipliers, the compact horizontal-energy gap and homogeneous Riesz response. R §§6–7 supply corrected-core recovery and complete affine coefficients; §§8–11 supply local coercivity, the improved full-domain lower estimate, actual unit-profile lower implication, matching energy and conditional scale alternatives. R §§12–13 supply canonical normalization and interpretation boundaries. Current R14 and R15 receive the separate parameter/admission and actual negative-occurrence credit in §8. N supplies strict nonaffinity, the positive affine projection margin and the fixed complex-affine refinement. These existing results are not new content of this companion.

The added result is the actual bilinear solvability identity and its complete conditional positive-response disappearance consequences, proved in §§4–6. The independent supplied proof is a fallible mathematical source; its approval and historical conduct statements are not premises. The proof here checks canonical extension, complex polarization, both cutoff boundary pairings, every coefficient term and the fixed-test-before-homogeneous-limit order. Hilbert-space weak compactness, form representation, Cauchy–Schwarz, IMS, parity, density and dominated convergence are mature intermediate tools. The Colin de Verdière–Hillairet–Trélat heat/localization and hypoelliptic correspondences, Coulhon–Sikora Gaussian implication and Fischer–Ruzhansky Young inequality retain their supplied conditional scopes. No external mathematical or numeric supplier is newly authenticated, and no worldwide originality or literature-absence claim is made.

**Definition 9.3 (native and interpretive limits).** Under $J_\kappa=\operatorname{diag}(1,1,\kappa)$ and the original real lift $D=\kappa x$, retain exactly

$$
\psi^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1/2}\psi(k,q),\qquad
W_\tau^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1}W_\tau(k,q),\qquad
g_{\rm orig}=|\kappa|g.
\tag{9.1}
$$

The transported long-time tensor is $J_\kappa M J_\kappa^{\mathsf T}$, including signed cross terms, with $M=\int_I\phi^2c_\kappa c_\kappa^{\mathsf T}dk>0$. Wavefunctions and unit raw-source kernels have different absolute-Jacobian powers. No conclusion is uniform as $\kappa\to0$, on the actual frozen zero leaf, on a wrapped cover or torus, or at zero cutoff. Canonical auxiliary kernels supply no native cutoff-free realization.

Global weak, local strong, unit-orbit and global strong convergence are distinct. The positive branch retains norm one and has weak/local limit zero. The homogeneous response is used only in its energy completion, not as a native or $L^2$ state. Four canonical coordinates, homogeneous dimension seven, three real phases, a rank-three long-time tensor, retained coordinate counts and physical Euclidean space are distinct. No physical three-space or physical $SO(3)$ is selected.

Analytic spectral amplitudes supply no native preparation, actuation, lawful transport realization, density acquisition, resource permission or clock bridge. The spectral $E_s$ here differs from acquired mass and from ML error. These theorems imply no full-channel acquisition result, native feasibility, efficiency, capacity or impossibility claim, autonomous reduced quantum evolution, general neural-network or empirical machine-learning result, ML implementation migration, or completion of a wider programme. They are ordinary conditional symbolic mathematics, without executed mathematics, numerical validation or Lean/kernel/frozen certification.

## 追加锚（本行以下为增补区）
