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

## 10. The mass-carrying macroscopic limit of actual weak-zero states

**Definition 10.1 (fixed native Coulomb normalization).** Let L denote [Native long-time phase diffusion](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md). Fix throughout one admitted datum of Definition 1.1 and all its supplied analytic antecedents in §§1–3. With the full original rational vector, define

$$
\begin{aligned}
M&=\int_I\phi(k)^2c_\kappa(k)c_\kappa(k)^{\mathsf T}dk>0,
&d(\mathbf z)&=\sqrt{\mathbf z^{\mathsf T}M^{-1}\mathbf z},\\
\beta_C&=\frac{\phi(k_0)\int_I\phi(k)^3dk}{4\pi\sqrt{\det M}}>0,
&e_C&=-\frac{\beta_C^2}{4a},
&\varrho&=\frac{\beta_C}{2a},\\
h_C(\mathbf z)&=(\det M)^{-1/4}
 \left(\frac{\varrho^3}{\pi}\right)^{1/2}e^{-\varrho d(\mathbf z)},
&(\mathcal D_gv)(k,\mathbf z)&=g^{-3/2}v(k,\mathbf z/g).
\end{aligned}
\tag{10.1}
$$

Here $\mathcal D_g$ is unitary from native $L^2(dk\,dq)$ to $L^2(dk\,d\mathbf z)$. The matrix is exactly L (36.1), with all signed cross terms. The constants $\beta_C,e_C,h_C$ are respectively $\beta,e_*,h_*$ of P (71.1), (72.1) and (72.4) at the fixed cutoff one. Indeed the raw-source tail coefficient is $\phi(k_0)\phi(k)/(4\pi\sqrt{\det M})$; its expectation in the height state $\phi$ gives $\beta_C$. The unitary substitution $\mathbf z=M^{1/2}y$ gives the normalized Coulomb state in (10.1), so $\|h_C\|_2=1$. Neither the field clock nor its source is changed by the kinetic constant $a$.

**Theorem 10.2 (actual weak-zero energy and full-mass profile).** For every prescribed sequence $s_n\downarrow0$ and every actual normalized complex ground-state choice $\psi_{s_n}\in D(S)$, use exactly (1.7) and put $F_s=\mathcal U_s\psi_s$, zero extended to $\mathbb R^4$. If

$$
F_{s_n}\rightharpoonup0\quad\text{globally in }L^2(\mathbb R^4),
\tag{10.2}
$$

then, along that sequence,

$$
\begin{aligned}
\frac{E_s}{g_s^2}&\longrightarrow e_C,
&r_s=-\frac{E_s}{s^6}&\longrightarrow-\chi_c^2e_C
 =\frac{\chi_c^2\beta_C^2}{4a}>0,\\
\inf_{\theta\in\mathbb R}
\|\mathcal D_{g_s}\psi_s-e^{i\theta}\phi h_C\|_{L^2(dk\,d\mathbf z)}
 &\longrightarrow0.
\end{aligned}
\tag{10.3}
$$

In particular the macroscopic limit carries the entire unit mass, with the fixed source as centre. No translating centres or subsequence-dependent Coulomb coefficients occur.

Proof. Suppress the prescribed sequence index. Put

$$
\begin{aligned}
D_{s^2}&=W_{s^2}-W_1\ge0,
&m_s&=-E_s/a>0,
&h_s&=s^2m_s,\\
C_s&=s^2\mathcal U_sS\mathcal U_s^{-1},
&Q_s(t)&=e^{-tC_s},
&R_s(h)&=(C_s+h)^{-1},\\
U_s^{<}&=s^5D_{s^2}\circ\Xi_s,
&U_s^{>}&=s^5W_1\circ\Xi_s,
&U_s&=U_s^{<}+U_s^{>}.
\end{aligned}
\tag{10.4}
$$

These are exactly P (75.2) and (104.1). All common-space operators mean restriction to $\Omega_s$ followed by zero extension; before extension their realization has both original Dirichlet faces. Since $W_{s^2}\ge W_1$, the common-domain variational principle and P Theorem 72.1 give $E_s\le E_1(g_s)\le-cg_s^2$ for small $s$, with fixed $c>0$. Lemma 4.2 gives $E_s\ge-C$. Consequently

$$
c_1s^8\le h_s\le C_1s^2\longrightarrow0.
\tag{10.5}
$$

Only an upper energy comparison has been used at this point, not a matching branch assumption.

The actual states have zero excess in the native condition of P Theorem 90.1. Its local compactness conclusion therefore turns (10.2) into $F_s\to0$ in $L^2(K)$ for each compact $K\subset\mathbb R^4$. The short-field convergence proved in P (104.6) is

$$
\|U_s^{<}-V\|_2\longrightarrow0,
\qquad V\in L^2(\mathbb R^4),
\qquad \sup_s\|U_s^{<}\|_\infty<\infty.
\tag{10.6}
$$

It follows that

$$
\|U_s^{<}F_s\|_1\longrightarrow0.
\tag{10.7}
$$

In detail, the contribution of $U_s^{<}-V$ is at most its $L^2$ norm, since $\|F_s\|_2=1$. On a fixed compact $K$, the contribution of $V$ is at most $\|V\|_{L^2(K)}\|F_s\|_{L^2(K)}$. Outside $K$ it is at most $\|V\mathbf1_{K^c}\|_2$. First let $s\to0$ and then exhaust by compact boxes. This uses local strong convergence and an $L^2$ multiplier tail, rather than treating weak convergence as convergence of products.

We next show that the removed short-time field produces a vanishing actual resolvent vector. Retain the compact reconstruction and finite-time operator of P (104.1) and (104.9):

$$
K_{\rm rec}=\mathcal E^{-1}V,
\qquad J_s=\int_0^{s^{-2}}Q_s(t)U_s^{<}dt,
\qquad\|J_s-K_{\rm rec}\|_{2\to2}=d_s\longrightarrow0.
\tag{10.8}
$$

The inverse in this formula is only the bounded compact reconstruction on these specified right sides, supplied by P Theorem 87.2; it is not an inverse on arbitrary $L^2$ inputs. Hence $\|J_sF_s\|_2\to0$ by (10.2). The early-time spectral-weight error is bounded by P (104.10):

$$
\left\|\int_0^{s^{-2}}(e^{-h_st}-1)
 Q_s(t)U_s^{<}F_sdt\right\|_2\le Ch_s^{3/4}\longrightarrow0.
\tag{10.9}
$$

For the remaining entire time interval use P (104.4), which gives $\|Q_s(t)\|_{1\to2}\le Cs^2t^{-3/4}$ for $t\ge s^{-2}$. Applied to this particular input, it yields

$$
\begin{aligned}
\left\|\int_{s^{-2}}^\infty e^{-h_st}
 Q_s(t)(U_s^{<}F_s)dt\right\|_2
 &\le Cs^2\int_{s^{-2}}^\infty e^{-h_st}t^{-3/4}dt
          \|U_s^{<}F_s\|_1\\
 &\le Cs^2h_s^{-1/4}\|U_s^{<}F_s\|_1\longrightarrow0.
\end{aligned}
\tag{10.10}
$$

The factor $s^2h_s^{-1/4}$ is bounded by (10.5); its product tends to zero by (10.7). The heat estimate acts on complex inputs by its positive-kernel norm bound. The Laplace resolvent formula, (10.8)–(10.10), now prove

$$
\|R_s(h_s)U_s^{<}F_s\|_2\longrightarrow0.
\tag{10.11}
$$

The time split is original field time one; the parameter $h_s=-s^2E_s/a$ comes solely from the actual eigen-equation. No clock of the field has been multiplied by $a$. In particular (10.10) controls the complete long-time contribution even when $h_s$ has order $s^8$.

Define the exact auxiliary native vector

$$
v_s=\frac{g_s}{a}(S+m_s)^{-1}W_1\psi_s\in D(S).
\tag{10.12}
$$

Here $W_1$ is bounded, $m_s>0$, and the resolvent is that of the original free operator with its complete domain. The actual equation gives the exact identities

$$
\begin{aligned}
\psi_s-v_s&=\frac{g_s}{a}(S+m_s)^{-1}D_{s^2}\psi_s,\\
\mathcal U_s(\psi_s-v_s)&=
 \frac{\chi_c}{a}R_s(h_s)U_s^{<}F_s,\\
(aS-E_s)v_s&=g_sW_1\psi_s.
\end{aligned}
\tag{10.13}
$$

Thus $\|\psi_s-v_s\|_2\to0$ and $\|v_s\|_2\to1$. This is an eigen-equation construction, not an arbitrary nearby vector.

The needed variational precision follows from the fixed-cutoff multiplier bound P (104.12), valid on every complex native form vector:

$$
\|W_1u\|_2\le C\|S^{1/2}u\|_2\qquad(u\in\mathcal Q).
\tag{10.14}
$$

For clarity, its consequence used here is uniform in $m>0$:

$$
\|S^{1/2}(S+m)^{-1}W_1\|_{2\to2}\le C.
\tag{10.15}
$$

Indeed the adjoint is $W_1(S+m)^{-1}S^{1/2}$. The commuting spectral multiplier $(S+m)^{-1}S^{1/2}$ maps $L^2$ into $\mathcal Q$, so (10.14) bounds this adjoint by $C\|S(S+m)^{-1}\|\le C$. This uses spectral calculus at positive $m$, without a positive gap for $S$. From (10.12), (10.14) and (10.15), with $T[u]=\|S^{1/2}u\|_2^2$, we obtain

$$
T[v_s]\le Cg_s^2,
\qquad\|W_1v_s\|_2\le Cg_s.
\tag{10.16}
$$

These are bounds for the auxiliary state, not a transfer of kinetic energy from $L^2$ proximity.

Let $\mathfrak e_{g,1}[u]=aT[u]-g\int W_1|u|^2$, on the original $\mathcal Q$. Pair the last equation in (10.13) with $v_s$, take real parts and subtract its fixed-cutoff potential. Exactly,

$$
\mathfrak e_{g_s,1}[v_s]
 =E_s\|v_s\|_2^2+
   g_s\operatorname{Re}\langle W_1v_s,\psi_s-v_s\rangle
 =E_s\|v_s\|_2^2+o(g_s^2).
\tag{10.17}
$$

The last bound is (10.16) times the proved $L^2$ error in (10.13). Normalize $\widehat v_s=v_s/\|v_s\|_2$, which is defined for small $s$. The exact factor $\|v_s\|_2^2$ multiplying $E_s$ in (10.17) cancels under this normalization. Therefore

$$
E_s\le E_1(g_s)\le
 \mathfrak e_{g_s,1}[\widehat v_s]=E_s+o(g_s^2).
\tag{10.18}
$$

The first inequality is the original variational comparison; the second tests the fixed-cutoff infimum with a normalized original-domain vector. This supplies the missing lower direction. P Theorem 72.1 gives $E_1(g_s)/g_s^2\to e_C$, hence $E_s/g_s^2\to e_C$. Since $g_s^2=\chi_c^2s^6$, the asserted $r_s$ limit follows as well.

Moreover (10.18) proves the precise fixed-cutoff deficit

$$
0\le\mathfrak e_{g_s,1}[\widehat v_s]-E_1(g_s)=o(g_s^2).
\tag{10.19}
$$

Thus P Theorem 73.1 applies to $\widehat v_s$ with fixed $\tau=1$, the same fixed original datum, and the sequence $g_s\downarrow0$. It gives phase-orbit convergence of $\mathcal D_{g_s}\widehat v_s$ to $\phi h_C$. Finally

$$
\|\widehat v_s-\psi_s\|_2
 \le |1-\|v_s\|_2|+\|v_s-\psi_s\|_2\longrightarrow0,
\tag{10.20}
$$

and unitarity of $\mathcal D_{g_s}$ transfers this $L^2$ conclusion to the actual states, proving (10.3). The unit norm of $\phi h_C$ gives full macroscopic mass. The sole reference near-minimizer application is (10.19), whose variational error has been derived from the actual equation. $\square$

## 11. The converse microscopic implication

**Theorem 11.1 (macroscopic orbit implies microscopic weak zero).** Fix the same datum and a prescribed sequence as in Theorem 10.2. If its actual normalized complex choices satisfy the macroscopic orbit convergence in (10.3), then $F_s=\mathcal U_s\psi_s\rightharpoonup0$ globally in $L^2(\mathbb R^4)$. In fact $F_s\to0$ in $L^2(K)$ for every compact $K$. Consequently, for these actual choices, microscopic weak zero and the stated unit-mass macroscopic orbit convergence are equivalent, and either implies both energy limits in (10.3).

Proof. Choose phases $\theta_s$ realizing the orbit limit to an error tending to zero, and put

$$
w_s(k,q)=\phi(k)g_s^{3/2}h_C(g_sq),\qquad\|w_s\|_2=1.
\tag{11.1}
$$

Macroscopic unitarity gives $\|\psi_s-e^{i\theta_s}w_s\|_2\to0$. Both $\phi$ and $h_C$ are bounded. At every $\xi\in\Omega_s$, the exact microscopic Jacobian gives

$$
\begin{aligned}
|(\mathcal U_sw_s)(\xi)|
 &=(j_0s^7)^{1/2}g_s^{3/2}
  |\phi(k_0+\varepsilon sr)h_C(g_s\mathbf q_s(\xi))|
 \le Cs^8,\\
\mathbf q_s(\xi)&=s c_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w.
\end{aligned}
\tag{11.2}
$$

Here $\mathbf q_s(\xi)$ is exactly the phase component of $\Xi_s\xi$. The same bound holds for the zero extension. Therefore $\|\mathcal U_sw_s\|_{L^2(K)}\le Cs^8|K|^{1/2}\to0$ for every compact $K$. Its global norm is one, so approximation of any $L^2$ test by compactly supported tests proves global weak convergence to zero, also after the varying constant phases. Microscopic unitarity transfers the vanishing norm error from $\psi_s-e^{i\theta_s}w_s$, proving both conclusions for $F_s$. The equivalence and energy consequences now follow from Theorem 10.2. No form or operator convergence is inferred from this norm comparison. $\square$

## 12. Positive response and the remaining zero-response case

**Corollary 12.1 (conditional positive-response macroscopic selection).** If the fixed admitted datum satisfies $C_{\rm resp}>0$, then for every prescribed sequence $s_n\downarrow0$ and every actual normalized complex ground-state choice in $D(S)$,

$$
\begin{aligned}
E_s&=e_Cg_s^2+o(g_s^2)
    =\chi_c^2e_Cs^6+o(s^6),
&\epsilon_c(s)&=\chi_c^2e_Cs^8+o(s^8),\\
r_s&\longrightarrow\frac{\chi_c^2\beta_C^2}{4a},
&\inf_\theta\|\mathcal D_{g_s}\psi_s-e^{i\theta}\phi h_C\|_2
 &\longrightarrow0.
\end{aligned}
\tag{12.1}
$$

The same conclusions hold on any actual weak-zero subsequence at $C_{\rm resp}=0$, without asserting that all, or any, actual choices have such a subsequence.

Proof. For positive response Theorem 6.1 supplies microscopic weak zero for every such actual sequence and choice. Apply Theorem 10.2. The identity $\epsilon_c(s)=s^2E_s$ gives its stated coefficient. At response zero, apply Theorem 10.2 only on the specified weak-zero subsequence. $\square$

**Definition 12.2 (correspondence and unresolved alternatives).** The source-specific implication in Theorem 10.2 combines the actual weak-zero resolvent removal (10.7)–(10.13) with the derived variational error (10.17)–(10.19) to obtain the full-mass energy/profile conclusion. The full-complex fixed-cutoff multiplier, Coulomb energy and near-minimizer profile are reused from P §§71–73 and (104.12); the finite-native heat, short-field and compact reconstruction inputs are reused from P §§87 and 104. The actual bounded-energy and local compactness inputs are Lemma 4.2 and P Theorem 90.1. The positive-response disappearance input is Theorem 6.1. Spectral calculus, Hölder, compact-operator weak-to-strong continuity and the variational principle are classical intermediate tools. This source-specific composition makes no assertion of worldwide novelty. The conditional heat and localization correspondences retain precisely their supplied hypotheses in §2.2.

The original full response sign and its positive or zero occurrence are not evaluated by these implications. At zero response, selection of a weak-zero subsequence, nonzero microscopic core limits, divergent or mixed scale alternatives and the complete every-choice decision remain unresolved. No statement here supplies a centered crossover, cutoff-free native realization, uniform limit in $\kappa$, physical-space identification, or analytic-state preparation from a resource, cone, observation or completely positive realization. The full original rational family, both Dirichlet faces, raw unit source, density $j_0$ and all-real complex domains are exactly those of §§1–2. Estimate (10.16) concerns the auxiliary vectors and is not asserted for the actual states; their macroscopic conclusion is an $L^2$ phase-orbit statement.

## 追加锚（本行以下为增补区）

## 13. A quantitative local amplitude of the actual reference state

**Definition 13.1 (fixed datum, reference state and positive constant).** Fix one admitted datum of Definition 1.1 before any limit. Retain all the supplied analytic antecedents of §§1–3 and 10, including P §§70–73 and L Lemma 41.2 at this datum, with its parameter applicability conditions in L Definition 35.1. No parameter, interval, source or clock varies except the explicitly displayed $g$ or $s$. Use precisely $M,d,\beta_C,\varrho,e_C,h_C,\mathcal D_g$ of (10.1), and set

$$
\begin{aligned}
h_0&=h_C(0)=(\det M)^{-1/4}(\varrho^3/\pi)^{1/2},
&c_*&=\frac{e^{-4}h_0}{24\sqrt\pi}
 =\frac{e^{-4}\varrho^{3/2}}{24\pi(\det M)^{1/4}}>0,\\
e_1(g)&=E_1(g),
&\mathbb B_\varrho&=\{\mathbf z:\varrho d(\mathbf z)\le1\},\\
V_\varrho&=|\mathbb B_\varrho|
 =\frac{4\pi}{3}\sqrt{\det M}\,\varrho^{-3},
&\mathbb B_g&=\{q:gq\in\mathbb B_\varrho\}.
\end{aligned}
\tag{13.1}
$$

Positivity and finiteness follow from $M>0$, $a>0$, $\phi(k_0)>0$ and $\int_I\phi^3>0$ in (10.1). In particular this constant is specified by the original fixed data, independently of a microscopic compact set, a ground-state choice or a response sign. Let $v_g\ge0$ be any normalized actual ground state of $H_{g,1}=aS-gW_1$ in $D(S)$. Such a choice exists by P Theorem 72.1 and the positive-semigroup argument of P (102.5): that argument uses only the strictly positive native heat kernel and a bounded nonnegative multiplier, so applies at cutoff one as well. It also shows $v_g>0$ almost everywhere. The reference problem uses fixed cutoff one, not the varying cutoff $s^2$.

**Theorem 13.2 (uniform reference lower amplitude).** There is $g_0>0$, depending only on the fixed datum and its antecedents, such that for every $0<g<g_0$ and every $v_g$ just specified,

$$
v_g(k,q)\ge c_*g^{3/2}\phi(k)
\quad\text{for almost every }(k,q)\in I\times\mathbb B_g.
\tag{13.2}
$$

The height range is the whole original interval, with both Dirichlet faces retained.

Proof. Put $f_g=\mathcal D_gv_g\ge0$. Its fixed-cutoff variational deficit is exactly zero. P Theorems 72.1 and 73.1, applied with $\tau=1$ fixed, give

$$
e_1(g)/g^2\longrightarrow e_C=-a\varrho^2,
\qquad \|f_g-\phi h_C\|_2\longrightarrow0.
\tag{13.3}
$$

For the second assertion, apply the pointwise modulus inequality to P's phase-orbit conclusion, since $|e^{i\theta}\phi h_C|=\phi h_C$. Both conclusions are uniform over nonnegative actual reference choices: a failure of uniformity supplies $g_n\downarrow0$ and failing choices, contradicting the same sequencewise theorems. Thus, since $\phi\mathbf1_{\mathbb B_\varrho}\in L^2(dk\,d\mathbf z)$ and $\int_I\phi^2=1$,

$$
\begin{aligned}
I_g&:=\int_{I\times\mathbb B_\varrho}\phi(k)f_g(k,\mathbf z)dk\,d\mathbf z
 \longrightarrow\int_{\mathbb B_\varrho}h_C(\mathbf z)d\mathbf z,\\
I_g&\ge\tfrac12 e^{-1}h_0V_\varrho
\quad\text{for all sufficiently small }g\text{ and all these choices}.
\end{aligned}
\tag{13.4}
$$

Here $h_C\ge e^{-1}h_0$ on the indicated ball. This step extracts an integral on a fixed macroscopic set, without inferring point values from $L^2$ convergence.

Write $\mathscr K_T(Y,Y')=e^{\lambda T}p_T^B(Y,Y')$, the raw kernel of $e^{-TS}$. L Lemma 41.2, with its complete height factors, implies for every $T\ge1$ and all interior heights and phase endpoints

$$
\left|\mathscr K_T((k,q),(k',q'))
 -\phi(k)\phi(k')\frac{e^{-d(q'-q)^2/(4T)}}{(4\pi T)^{3/2}\sqrt{\det M}}\right|
 \le C\phi(k)\phi(k')T^{-5/2}.
\tag{13.5}
$$

Only the spatial exponential, which is at most one, has been discarded from that error. For $q,q'\in\mathbb B_g$, the triangle inequality for $d$ gives $d(q'-q)\le2/(\varrho g)$. Choose the native heat time and the Hamiltonian semigroup time to be

$$
T_g=(\varrho g)^{-2},\qquad t_g=T_g/a,
\qquad \gamma_0=\frac{e^{-1}}{(4\pi)^{3/2}\sqrt{\det M}}.
\tag{13.6}
$$

The Gaussian in (13.5) is at least $\gamma_0(\varrho g)^3$ on these endpoints. Take $g$ small enough that $T_g\ge1$ and $C/T_g\le\gamma_0/2$. Equation (13.5) then gives, uniformly over the entire height interval,

$$
\mathscr K_{T_g}((k,q),(k',q'))
 \ge\tfrac12\gamma_0(\varrho g)^3\phi(k)\phi(k')
\quad(q,q'\in\mathbb B_g).
\tag{13.7}
$$

The relative height factor in the error is essential for this conclusion near either absorbing face.

For completeness, the bounded nonnegative multiplier $W_1$ of P Proposition 70.2 gives the order inequality

$$
e^{-tH_{g,1}}f\ge e^{-taS}f\qquad(f\ge0,\ f\in L^2,\ t\ge0).
\tag{13.8}
$$

Indeed its bounded-perturbation Dyson expansion has zeroth term $e^{-taS}$ and subsequent terms consisting of positive free semigroups and $gW_1$. The $n$th term has operator norm at most $(tg\|W_1\|_\infty)^n/n!$, because $S\ge0$. The series converges in operator norm at every finite $t$, and the positive cone of $L^2$ is closed. This proves (13.8) on the entire complex Hilbert space as an order assertion for nonnegative inputs. It remains valid at each finite $t=t_g$; no uniform series limit as $g\to0$ is required.

The actual eigen-equation gives $v_g=e^{t_ge_1(g)}e^{-t_gH_{g,1}}v_g$. Equation (13.3) yields $t_ge_1(g)\to-1$, so $e^{t_ge_1(g)}\ge e^{-2}$ for small $g$. Positivity permits restricting the input to $I\times\mathbb B_g$. This restriction of $v_g$ is in $L^1\cap L^2$, since that set has finite measure at each $g>0$. The raw kernel integral is consequently legitimate, without assuming $v_g\in L^1$ globally. Combining (13.7)–(13.8), for almost every $(k,q)\in I\times\mathbb B_g$,

$$
\begin{aligned}
v_g(k,q)
&\ge e^{-2}\tfrac12\gamma_0(\varrho g)^3\phi(k)
 \int_{I\times\mathbb B_g}\phi(k')v_g(k',q')dk'\,dq'\\
&=e^{-2}\tfrac12\gamma_0\varrho^3g^{3/2}\phi(k)I_g\\
&\ge\frac{e^{-3}\gamma_0\varrho^3h_0V_\varrho}{4}
 g^{3/2}\phi(k)=c_*g^{3/2}\phi(k).
\end{aligned}
\tag{13.9}
$$

The equality uses exactly $\mathbf z'=gq'$ and $v_g(k',q')=g^{3/2}f_g(k',gq')$. Substitution of (13.1) and (13.6) gives $e^{-3}\gamma_0\varrho^3h_0V_\varrho/4=e^{-4}h_0/(24\sqrt\pi)$. All thresholds used above depend only on the fixed datum, and are uniform over the reference choices. The kernel of $e^{-t_gaS}$ is $\mathscr K_{a t_g}=\mathscr K_{T_g}$: this is a time chosen for a semigroup estimate, leaving the defining field clock of $W_1$ equal to $B$. $\square$

**Corollary 13.3 (reference amplitude on every fixed microscopic compact set).** For every compact Lebesgue measurable $K\subset\mathbb R^4$, there is $s_K>0$ such that for $0<s<s_K$, $g_s=\chi_cs^3$, and every nonnegative normalized actual reference choice,

$$
v_{g_s}(\Xi_s\xi)\ge c_*g_s^{3/2}\phi(k_0+\varepsilon sr)
\quad\text{for almost every }\xi\in K.
\tag{13.10}
$$

Proof. The phase component of $\Xi_s\xi$ is exactly $\mathbf q_s(\xi)$ in (11.2). For a fixed compact $K$, its coordinates are bounded, so $\sup_Kd(\mathbf q_s(\xi))\le L_Ks$ for $0<s\le1$, with $L_K<\infty$ from the fixed jets and $M^{-1}$. Hence $\sup_K\varrho g_sd(\mathbf q_s(\xi))\le\varrho\chi_cL_Ks^4\to0$. Also $K\subset\Omega_s$ for small $s$ because $k_0$ is interior. Apply Theorem 13.2 once $g_s<g_0$ and these two inclusions hold. The nonzero Jacobian $j_0s^7$ in (2.1) preserves almost everywhere assertions under $\Xi_s$. $\square$

## 14. An actual microscopic charge lowers the energy at scale $g_s^2$

**Definition 14.1 (short field and positive actual charge).** For $0<s<1$, retain every actual normalized complex ground-state choice $\psi_s\in D(S)$ from (1.7), and put

$$
\begin{aligned}
u_s&=|\psi_s|,&F_s^+&=\mathcal U_su_s=|F_s|,\\
D_s&=W_{s^2}-W_1\ge0,&U_s^{<}&=s^5D_s\circ\Xi_s,\\
A_s(K)&=\int_K\phi(k_0+\varepsilon sr)U_s^{<}(\xi)F_s^+(\xi)d\xi.
\end{aligned}
\tag{14.1}
$$

The symbol $A_s(K)$ here is a scalar charge, distinct from the Friedrichs operator $A_s$ of (2.2). Its domain is each fixed compact Lebesgue measurable $K\subset\mathbb R^4$ of positive measure, with $s$ small enough that $K\subset\Omega_s$. P (102.5) gives $u_s>0$ almost everywhere, $u_s\in D(S)$, $\|u_s\|_2=1$, and $(aS-g_sW_{s^2})u_s=E_su_s$. Thus taking the modulus preserves an actual ground state in the original full complex problem. For each fixed $s>0$, $D_s$ is a bounded nonnegative real multiplier by P Proposition 70.2; no uniform bound for this unscaled multiplier as $s\downarrow0$ is asserted.

**Theorem 14.2 (quantitative finite-native energy comparison).** With the strictly positive explicit constant $c_*$ of (13.1), for every $K$ in Definition 14.1 there is $s_K>0$ such that for every $0<s<s_K$ and every actual normalized complex ground-state choice,

$$
\frac{e_1(g_s)-E_s}{g_s^2}
 \ge c_*\sqrt{j_0\chi_c}\,A_s(K)\ge0.
\tag{14.2}
$$

Neither a response sign nor a bound on $r_s$ is a hypothesis.

Proof. Choose any nonnegative normalized actual reference ground state $v_{g_s}$. Its common operator domain with $u_s$ is exactly $D(S)$, and both potentials are bounded at this fixed $s$. Selfadjointness and the two actual eigen-equations therefore give the exact finite pairing

$$
\begin{aligned}
O_s&:=\langle v_{g_s},u_s\rangle\in(0,1],\\
(e_1(g_s)-E_s)O_s
 &=g_s\int_{\mathcal C}D_s v_{g_s}u_s\,dY.
\end{aligned}
\tag{14.3}
$$

Strict positivity gives $O_s>0$, and Cauchy–Schwarz gives $O_s\le1$. The integral is finite by boundedness of $D_s$ and the two $L^2$ norms. This identity uses selfadjoint operator pairings, without additional phase derivatives or boundary integration. Its nonnegative right side also proves $e_1(g_s)-E_s\ge0$. Restrict it to $\Xi_s(K)$, apply (13.10), divide by $g_s^2O_s$, and use $O_s\le1$. The result is

$$
\frac{e_1(g_s)-E_s}{g_s^2}
 \ge c_*g_s^{1/2}\int_{\Xi_s(K)}\phi(k)D_su_s\,dY.
\tag{14.4}
$$

The exact source/coordinate normalization is

$$
\begin{aligned}
\int_{\Xi_s(K)}\phi(k)D_su_s\,dY
 &=j_0s^7s^{-5}(j_0s^7)^{-1/2}A_s(K)
 =\sqrt{j_0}s^{-3/2}A_s(K),\\
g_s^{1/2}s^{-3/2}&=\sqrt{\chi_c}.
\end{aligned}
\tag{14.5}
$$

Substitution proves (14.2). All smallness conditions come from Corollary 13.3 and the inclusion of $K$, hence are independent of the actual ground-state choice. The signed rational fields, $j_0$, unit raw source, both height faces and the $B$ clock remain those of §§1–2. $\square$

## 15. A strict core margin and the three equivalent Coulomb endpoints

**Theorem 15.1 (quantitative exclusion of a core at the Coulomb endpoint).** Retain the same fixed datum. Define

$$
m_{\rm core}=\int_{\mathbb R^4}Vp\,d\xi\in(0,\infty),\qquad
\eta_*=c_*\sqrt{j_0\chi_c}\,\phi(k_0)m_{\rm core}>0,
\qquad r_C=-\chi_c^2e_C>0.
\tag{15.1}
$$

For every prescribed sequence $s_n\downarrow0$ and every actual normalized complex choice with $F_{s_n}\rightharpoonup cp$ globally in $L^2$, one has

$$
\liminf_{n\to\infty}\frac{e_1(g_{s_n})-E_{s_n}}{g_{s_n}^2}
 \ge\eta_*|c|,
\qquad
\liminf_{n\to\infty}r_{s_n}
 \ge r_C+\chi_c^2\eta_*|c|.
\tag{15.2}
$$

In particular, if also $r_{s_n}\to R<\infty$ and $c\ne0$, then $R\ge r_C+\chi_c^2\eta_*|c|>r_C$.

Proof. N Lemma 5.1 supplies exactly $0<m_{\rm core}<\infty$; its integrability follows from $V\in L^2$, $p\in L^2$ and Cauchy–Schwarz, and its strict positivity from $V,p>0$. Every other factor in $\eta_*$ is strictly positive by (1.1), (2.7) and (13.1).

Actual states have zero variational excess, so the necessity and local compactness assertions of P Theorem 90.1 apply on the exact path. On the given weakly convergent subsequence they yield $F_s\to cp$ in $L^2(K)$ for each compact $K$. Consequently $F_s^+=|F_s|\to|c|p$ there. By (2.9) and boundedness of $W_1$,

$$
U_s^{<}=U_s-s^5W_1\circ\Xi_s\longrightarrow V
\quad\text{uniformly on every fixed compact set},\qquad
\phi(k_0+\varepsilon sr)\longrightarrow\phi(k_0)
\quad\text{uniformly there}.
\tag{15.3}
$$

All factors in the first product other than $F_s^+$ are locally uniformly bounded. Cauchy–Schwarz on $K$ and its finite measure therefore justify the full product limit

$$
A_s(K)\longrightarrow\phi(k_0)|c|\int_KVp\,d\xi.
\tag{15.4}
$$

Apply (14.2) first on each fixed compact box. Only after taking its $s$-limit exhaust $\mathbb R^4$ by increasing boxes; positivity and $Vp\in L^1$ give the first inequality in (15.2). No global product convergence or uniform-in-$K$ threshold is needed. Finally the exact identity

$$
\frac{e_1(g_s)-E_s}{g_s^2}
 =\frac{e_1(g_s)}{g_s^2}+\frac{r_s}{\chi_c^2},
\qquad e_1(g_s)/g_s^2\longrightarrow e_C
\tag{15.5}
$$

gives the second inequality, also if the lower limit is infinite. The statement for finite $R$ follows directly. $\square$

**Theorem 15.2 (actual energy, microscopic and full-mass macroscopic equivalence).** For every prescribed sequence $s_n\downarrow0$, and for every actual normalized complex ground-state choice in the unchanged $D(S)$, the following three assertions are equivalent along that same sequence:

$$
\begin{aligned}
&r_{s_n}\longrightarrow r_C;\\
&F_{s_n}\rightharpoonup0\quad\text{in }L^2(\mathbb R^4);\\
&\inf_{\theta\in\mathbb R}
 \|\mathcal D_{g_{s_n}}\psi_{s_n}-e^{i\theta}\phi h_C\|_2
 \longrightarrow0.
\end{aligned}
\tag{15.6}
$$

Whenever they hold, $F_{s_n}\to0$ in $L^2(K)$ for every compact $K$, and the energy limits in (10.3) hold. These are sequencewise equivalences, without a response-sign hypothesis or an assertion that any of the three occurs at a given response-zero datum.

Proof. Suppose $r_{s_n}\to r_C$. Equations (13.3) and (15.5) make the energy defect tend to zero. Every subsequence of the unit vectors $F_{s_n}$ has a weakly convergent further subsequence; P Theorem 90.1 identifies its limit as $cp$. Theorem 15.1 forces $c=0$. Thus all weak cluster points are zero, and the full sequence converges weakly to zero: otherwise some fixed $L^2$ test has a pairing bounded away from zero on a subsequence, contradicting a further weak limit zero. This proves the new first-to-second implication using the quantitative finite-$s$ comparison. The second assertion implies the first and third by Theorem 10.2; the third implies the second by Theorem 11.1. The local conclusion is P Theorem 90.1, or Theorem 11.1 after the macroscopic implication. No form convergence is deduced from an $L^2$ norm comparison. $\square$

## 16. Analytic correspondence and unresolved selection

**Definition 16.1 (suppliers and scope of the quantitative comparison).** Theorems 13.2, 14.2 and 15.1 are repository-derived source-specific deductions. P Proposition 70.2 supplies positive-cutoff bounded multipliers and the common full operator domain; P Theorems 72.1 and 73.1 supply the actual fixed-cutoff energy and unit-mass macroscopic profile. L Lemma 41.2 supplies the all-height, all-real-phase, large-time native kernel error, with its original parameter conditions. P (102.5) supplies positivity and modulus preservation for actual complex ground states. P Theorem 90.1 supplies only its necessity/local-compactness part here; its construction of general near-minimizers is not used. N Lemma 5.1 supplies the finite positive canonical core charge. Theorems 10.2 and 11.1 own the other directions in (15.6). The Jacobian, field split, canonical mode and Coulomb normalization are exactly (2.1), (2.7), (10.1) and (10.4). Spectral calculus, the norm-convergent bounded-perturbation series, Cauchy–Schwarz and monotone convergence are classical intermediate tools. No literature-wide novelty or additional certification of the supplied conditional heat, localization and reconstruction antecedents is asserted.

The finite estimate (14.2) makes no sign assumption and does not require bounded actual $r_s$. Its coefficient comes from the original reference ground state through a proved heat-kernel lower bound, rather than from shrinking-core values inferred from macroscopic $L^2$ convergence. Its spectral pairing is on the exact common $D(S)$, without an ordinary phase-$H^1$ restriction, an $L^2$ representative of the homogeneous response, or a positive $L^2$ gap at the canonical threshold. Neither this pairing nor (15.6) transfers actual kinetic energies from $L^2$ proximity. All signed nonzero-$\kappa$ data and jointly realized rational components remain fixed; no zero-cutoff, wrapped-phase, or uniform-in-$\kappa$ statement is made.

The canonical absolute response sign and the actual occurrence of positive or zero response remain unresolved. At response zero, the existence and selection of actual endpoints are not decided: nonzero cores cannot occur at $r_C$ by (15.2), but actual selection away from $r_C$, deeper finite mixed/core branches and possible divergent behavior remain unresolved. No finer energy coefficient, centered crossover, analytic-state preparation, physical-space correspondence or physical spatial dimension follows. Resource, cone, observation and completely positive realization statements supply no additional native preparation premise here. The equivalence (15.6) and the strict charge margin are partial constraints on the original every-actual-choice selection problem, not a decision of that complete problem.

## 追加锚（本行以下为增补区）


## 17. The original Coulomb column and the two comparison maps

**Definition 17.1 (fixed datum, separated spectral parameter and comparison spaces).** Retain Definitions 1.1–3.2, 10.1 and 13.1, including all their analytic antecedents and the parameter applicability conditions of L Definition 35.1, the original signed nonzero $\kappa$, jointly realized rational vector, both height faces, every real phase and the full complex domains (1.5). Fix this one datum before taking any limit. In §§17–19 prescribe any sequence $s_n\downarrow0$ and any actual normalized complex ground-state choices $\psi_s\in D(S)$ on $g_s=\chi_cs^3$, and assume along this sequence that

$$
r_s\longrightarrow R<\infty,\qquad F_s=\mathcal U_s\psi_s\rightharpoonup cp,
\qquad c\ne0.
\tag{17.1}
$$

Write $\chi=\chi_c$. Theorem 15.1 gives $R>r_C=-\chi^2e_C$. Thus

$$
t_s=-E_s/g_s^2=r_s/\chi^2\longrightarrow t=R/\chi^2>-e_C>0,
\qquad m_s=g_s^2t_s/a,\qquad h_s=s^2m_s.
\tag{17.2}
$$

On complex $L^2(\mathbb R^3,d\mathbf z)$ put

$$
H_0=-a\nabla\cdot M\nabla,\qquad U_C(\mathbf z)=\beta_C/d(\mathbf z),
\qquad H_C=H_0-U_C,
\tag{17.3}
$$

where $H_C$ is the original Friedrichs form operator on $H^1$, with $M,d,\beta_C,e_C$ exactly as in (10.1). Let $\iota h(k,\mathbf z)=\phi(k)h(\mathbf z)$, let $\Pi_s$ be restriction to $\Omega_s$ followed by zero extension, and define

$$
\begin{aligned}
\mathcal M_sh&=\mathcal U_s\mathcal D_{g_s}^{-1}\iota h,
&\mathcal N_sf&=\mathcal D_{g_s}\mathcal U_s^{-1}\Pi_sf,\\
\phi_s(\xi)&=\mathbf1_{\Omega_s}(\xi)\phi(k_0+\varepsilon sr),
&\mathbf q_s(\xi)&=s c_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w.
\end{aligned}
\tag{17.4}
$$

In (17.4), extend $\phi$ by zero outside $I$ when evaluating $\phi_s$. The output of $\mathcal M_s$ is zero extended. The maps $\iota$ and $\mathcal M_s$ are isometries; $\|\mathcal N_sf\|_2=\|\Pi_sf\|_2\le\|f\|_2$. These facts follow from $\|\phi\|_2=1$ and the two exact unitaries (2.1), (10.1). In particular,

$$
(\mathcal M_sh)(\xi)=\sqrt{j_0}s^{7/2}g_s^{3/2}
 \phi_s(\xi)h(g_s\mathbf q_s(\xi)).
\tag{17.5}
$$

These are comparison maps in $L^2$ only. No native form membership or kinetic-energy correspondence for their inputs or outputs is part of this definition.

For $b>0$, $\eta\ge0$, and the original Gaussian $\Gamma_{M,u}$ of L (36.2), set

$$
\begin{aligned}
Y_b^{[\eta]}(\mathbf z)&=\frac1a\int_\eta^\infty
 e^{-bu/a}\Gamma_{M,u}(\mathbf z)du,&Y_b&=Y_b^{[0]},\\
Y_b(\mathbf z)&=\frac{e^{-\sqrt{b/a}\,d(\mathbf z)}}
 {4\pi a\sqrt{\det M}\,d(\mathbf z)},&
Q&=\sqrt{j_0\chi}\,\phi(k_0)m_{\rm core}>0.
\end{aligned}
\tag{17.6}
$$

Here $m_{\rm core}=\int Vp$ is the finite positive charge of (15.1), and $Q$ denotes a scalar source charge in §§17–20. The factor $1/a$ is inside $Y_b$, not inside the native field clock. The singular source $\delta_0$ used below is a distribution on the macroscopic phase space, never an $L^2$ vector or an additional native interaction.

**Proposition 17.2 (the uniquely fixed $L^2$ Coulomb column).** Let $t=R/\chi^2$ as above. The operator $(H_0+t)^{-1}U_C$, initially on smooth functions supported away from zero, has a bounded extension $T_t$ to all complex $L^2$. The operator $I-T_t$ has a bounded inverse there. The real function

$$
\zeta_R=Q(I-T_t)^{-1}Y_t\in L^2(\mathbb R^3)
\tag{17.7}
$$

is strictly positive almost everywhere and is the unique $L^2$ distributional solution, on all of $\mathbb R^3$, of

$$
(H_C+R/\chi^2)\zeta_R=Q\delta_0.
\tag{17.8}
$$

It is the column determined by the original Friedrichs operator; there is no boundary parameter at the origin.

Proof. The linear change $\mathbf z=M^{1/2}y$ reduces the needed Hardy bound to the classical three-dimensional inequality. It gives

$$
\|U_Cv\|_2\le C\|H_0^{1/2}v\|_2\qquad(v\in H^1).
\tag{17.9}
$$

Consequently $U_C(H_0+t)^{-1}$ is bounded; define $T_t$ as its adjoint. This agrees with the stated initial product. Fourier interpolation in (17.9) gives, for every $\epsilon>0$, $\|U_Cv\|_2\le\epsilon\|H_0v\|_2+C_\epsilon\|v\|_2$ on $H^2$. Thus the form realization $H_C$ has operator domain $H^2$. One direct justification is to choose $L$ so large that $\|U_C(H_0+L)^{-1}\|<1$, by (17.9) and spectral calculus. The factorization of $H_0-U_C+L$ then gives its inverse into $H^2$; symmetry and the same factorization at nonreal parameters give the selfadjoint operator on $H^2$, whose form is the Friedrichs form (17.3).

P (72.3) gives $\inf\sigma(H_C)=e_C$, so $H_C+t\ge(t+e_C)I>0$. For $v=(H_C+t)^{-1}f$, put $x=\|H_0^{1/2}v\|_2$ and $y=\|v\|_2$. The spectral bound gives $y\le(t+e_C)^{-1}\|f\|_2$, while its real energy identity and (17.9) give

$$
x^2\le y\|f\|_2+Cxy.
\tag{17.10}
$$

Young's inequality therefore bounds $x$, and hence $\|U_Cv\|_2$, by a fixed multiple of $\|f\|_2$. Write $A=U_C(H_0+t)^{-1}$ and $B=U_C(H_C+t)^{-1}$. Both are bounded. The two resolvent identities, with the products justified by the common $H^2$ domain and the preceding bounds, give $B=A+AB=A+BA$. Hence $(I-A)^{-1}=I+B$. Taking adjoints proves bounded invertibility of $I-T_t$, with

$$
(I-T_t)^{-1}=I+B^*,\qquad
B^*=[(H_C+t)^{-1}U_C]_{\rm ext}.
\tag{17.11}
$$

For a smooth compact test $v$, integration of $-\partial_u(e^{-tu/a}\Gamma_{M,u})$ from zero to infinity gives $v(0)$ after pairing with $v$. This follows from the Gaussian approximate identity at zero and exponential decay at infinity, and proves the distributional identity below. Evaluating the Gaussian integral radially after $\mathbf z=M^{1/2}y$ gives the formula in (17.6); integrating its square with radial measure $4\pi\sqrt{\det M}r^2dr$ gives

$$
(H_0+t)Y_t=\delta_0\quad\text{in distributions},\qquad
\|Y_t\|_2^2=\frac1{8\pi a^2\sqrt{\det M}\sqrt{t/a}}<\infty.
\tag{17.12}
$$

For any $f\in L^2$ and any smooth compact test $v$, $U_Cv\in L^2$. The adjoint definition therefore gives $(H_0+t)T_tf=U_Cf$ distributionally. Here $U_Cf$ is locally integrable by Cauchy–Schwarz. Applying this to (17.7) proves (17.8). Conversely an $L^2$ homogeneous solution $u$ satisfies $(H_0+t)(u-T_tu)=0$ distributionally. Fourier transformation and $a\eta^{\mathsf T}M\eta+t>0$ force $u=T_tu$, and invertibility forces $u=0$. This proves uniqueness without imposing a punctured-space boundary condition.

Finally $(H_C+t)^{-1}$ preserves nonnegativity. Indeed conjugation first makes its solution real for real input; testing its form equation against the negative part gives $-\mathfrak h_t[v_-]=\langle v_-,f\rangle\ge0$ for $f\ge0$, whereas $\mathfrak h_t[v_-]\ge(t+e_C)\|v_-\|_2^2$. Thus $v_-=0$. Positive annular approximations extend this order property to the bounded $B^*$ in (17.11). It follows that $\zeta_R=Q(Y_t+B^*Y_t)\ge QY_t>0$ almost everywhere. All inverses here belong to the auxiliary original Coulomb operator on the entire phase space. No $H^1$ property of $\zeta_R$, and no native-domain assertion for it, has been used. $\square$

## 18. Complete output of the actual short-field source

**Theorem 18.1 (core and free-column reconstruction before the long field).** Under (17.1), put $D_s=W_{s^2}-W_1$ and

$$
w_s=\frac{g_s}{a}(S+m_s)^{-1}D_s\psi_s.
\tag{18.1}
$$

Then, in the complete zero-extended $L^2(\mathbb R^4)$ norm,

$$
\|\mathcal U_sw_s-cp-c\mathcal M_s(QY_t)\|_2\longrightarrow0.
\tag{18.2}
$$

Proof. Use $V_s=U_s^{<}=s^5D_s\circ\Xi_s$, zero extended. P (104.6) gives $V_s\to V$ in $L^2$ and a uniform supremum bound. P Theorem 90.1, only in its necessity and local-compactness directions for actual states of zero excess, gives $F_s\to cp$ in $L^2(K)$ on every fixed compact $K$. Consequently

$$
V_sF_s\longrightarrow cVp\text{ in }L^1,\qquad
\mu_s:=\phi_sV_sF_s\longrightarrow c\phi(k_0)Vp\text{ in }L^1.
\tag{18.3}
$$

For the first claim, bound $(V_s-V)F_s$ by $\|V_s-V\|_2$, use local strong convergence for $V(F_s-cp)$ on a compact box, and bound its complement by $(1+|c|)\|V\mathbf1_{K^c}\|_2$. For the second, $\phi_s$ is uniformly bounded, converges pointwise to $\phi(k_0)$, and $Vp\in L^1$. Dominated convergence completes the argument. These are convergences of complex products, without taking moduli of the actual states. The exact Jacobian also gives

$$
\|D_s\psi_s\|_1=\sqrt{j_0}s^{-3/2}\|V_sF_s\|_1\le Cs^{-3/2}.
\tag{18.4}
$$

At each fixed $s$, the source is also in $L^2$, since $D_s$ is a bounded multiplier. The resolvent integral in (18.1) is thus legitimate on the whole complex native Hilbert space.

Split its native free heat time $T$ at $T=1$. For $0<T<1$ set $T=s^2u$ and retain $Q_s(u)=e^{-uC_s}$ of (10.4). Exact conjugacy gives the early output

$$
\mathcal U_sw_s^{\rm early}
 =\frac\chi a\int_0^{s^{-2}}e^{-h_su}Q_s(u)V_sF_sdu.
\tag{18.5}
$$

P (104.9)–(104.10) bound its difference from $(\chi/a)K_{\rm rec}F_s$ by $C(d_s+h_s^{3/4})\to0$. The compact operator $K_{\rm rec}$ sends $F_s\rightharpoonup cp$ to strong convergence, and $(\chi/a)K_{\rm rec}p=p$ by (2.7) and the supplied reconstruction. Therefore (18.5) converges strongly to $cp$ in the full output norm.

For the remaining native time define $G_T$ by its kernel

$$
G_T((k,q),(k',q'))=\phi(k)\phi(k')\Gamma_{M,T}(q-q'),
\qquad \mathscr E_T=e^{-TS}-G_T.
\tag{18.6}
$$

The spatial factor of L (41.2), with both height factors intact, yields

$$
\|\mathscr E_T(\cdot,(k',q'))\|_2\le C\phi(k')T^{-7/4},
\qquad \|\mathscr E_T\|_{1\to2}\le CT^{-7/4}\quad(T\ge1).
\tag{18.7}
$$

In detail, the squared kernel bound is $C\phi(k)^2\phi(k')^2T^{-5}$ times $\exp[-2c\min(|q-q'|^2/T,|q-q'|)]$. Its phase integral is at most $CT^{3/2}$: on $|q-q'|\le T$ use the Gaussian integral, and on the complement use the exponential in $|q-q'|$. Integrate $\phi(k)^2$ to one, take the square root and then apply Minkowski to get (18.7). Thus (18.4) gives

$$
\left\|\frac{g_s}{a}\int_1^\infty
 e^{-m_sT}\mathscr E_TD_s\psi_s\,dT\right\|_2
 \le Cg_ss^{-3/2}\int_1^\infty T^{-7/4}dT=O(s^{3/2})\longrightarrow0.
\tag{18.8}
$$

This bound is over all output heights and all phase points; no output compact restriction precedes it.

The Gaussian part can be evaluated exactly. Substitute $\mathbf z=g_sq$, $u=g_s^2T$, and then $Y'=\Xi_s\xi$ in its input integral. Since $\Gamma_{M,T}(\mathbf z/g_s-q')=g_s^3\Gamma_{M,u}(\mathbf z-g_sq')$, (18.4)'s Jacobian calculation gives

$$
\mathcal D_{g_s}w_s^{\rm late,G}(k,\mathbf z)
 =\phi(k)\sqrt{j_0\chi}
 \int_{\mathbb R^4}\mu_s(\xi)
 Y_{t_s}^{[g_s^2]}(\mathbf z-g_s\mathbf q_s(\xi))d\xi.
\tag{18.9}
$$

In particular the prefactor before the $u$ integral is $g_s^{1/2}\sqrt{j_0}s^{-3/2}/a=\sqrt{j_0\chi}/a$; the $1/a$ is exactly the one in (17.6). This keeps the raw source density and field clock unchanged.

The Gaussian $L^2$ norm is $\|\Gamma_{M,u}\|_2=C_Mu^{-3/4}$. It follows that $\|Y_b-Y_b^{[g_s^2]}\|_2\le Cg_s^{1/2}$ for $b>0$. Also $Y_{t_s}\to Y_t$ in $L^2$ by dominated Bochner integration, since $t_s\to t>0$, using $u^{-3/4}$ near zero and exponential decay at infinity. These columns have uniformly bounded $L^2$ norms for small $s$. For every fixed $\xi$, $g_s\mathbf q_s(\xi)\to0$, so translation continuity in $L^2$ gives

$$
Y_{t_s}^{[g_s^2]}(\cdot-g_s\mathbf q_s(\xi))\longrightarrow Y_t
\quad\text{in }L^2(\mathbb R^3).
\tag{18.10}
$$

Replace $\mu_s$ in (18.9) by $c\phi(k_0)Vp$ using (18.3) and the uniform column norm. For this fixed integrable density, (18.10) and dominated integration give convergence in full $L^2(dk\,d\mathbf z)$ to $c\iota(QY_t)$. The two changes of coordinates are isometries, so (18.8), (18.5) and this last convergence prove (18.2). In particular neither local kernel convergence alone nor weak convergence of the sources has been substituted for a complete-output estimate. $\square$

## 19. Bounded native inversion and the complete two-scale norm

**Theorem 19.1 (actual finite-$R$ reconstruction and exact mass law).** For every fixed datum, prescribed sequence and actual complex choices in (17.1), with the unique column (17.7),

$$
\|F_s-cp-c\mathcal M_s\zeta_R\|_2\longrightarrow0,
\qquad 1=|c|^2(1+\|\zeta_R\|_2^2).
\tag{19.1}
$$

The convergence in the first assertion is in the complete $L^2(\mathbb R^4)$ norm. The microscopic and macroscopic components share exactly the same complex factor $c$.

Proof. Put

$$
\mathsf T_s=g_s(aS+g_s^2t_s)^{-1}W_1,
\qquad \widetilde{\mathsf T}_s=\mathcal U_s\mathsf T_s\mathcal U_s^{-1}
\quad\text{on }L^2(\Omega_s).
\tag{19.2}
$$

At each fixed $s$, all multipliers in the actual equation are bounded and its domain is exactly $D(S)$. It gives the exact identity

$$
(I-\mathsf T_s)\psi_s=w_s.
\tag{19.3}
$$

We first prove a bounded inverse uniformly for this fixed separated parameter. P Theorem 72.1 at cutoff one gives $e_1(g_s)/g_s^2\to e_C$. By (17.2), there is $d>0$ such that

$$
H_{g_s,1}+g_s^2t_s=aS-g_sW_1+g_s^2t_s\ge dg_s^2I
\tag{19.4}
$$

for all sufficiently small $s$. For $u=(H_{g_s,1}+g_s^2t_s)^{-1}f$, set $x=\|S^{1/2}u\|_2$ and $y=\|u\|_2$. Then $y\le d^{-1}g_s^{-2}\|f\|_2$. P (104.12) and the real part of the actual operator pairing give

$$
a x^2\le y\|f\|_2+Cg_sxy,
\qquad x\le Cg_s^{-1}\|f\|_2,
\qquad \|W_1u\|_2\le Cg_s^{-1}\|f\|_2.
\tag{19.5}
$$

The second inequality follows from the first by Young's inequality and the bound for $y$. The adjoint product has the same bound. Bounded-perturbation resolvent identities now give, on the entire native complex $L^2$ space,

$$
(I-\mathsf T_s)^{-1}
 =I+g_s(H_{g_s,1}+g_s^2t_s)^{-1}W_1,
\qquad \sup_{s\text{ small}}\|(I-\mathsf T_s)^{-1}\|<\infty.
\tag{19.6}
$$

In addition P (104.13) gives $\|\mathsf T_s\|\le Cg_sm_s^{-1/2}\le C$. Thus both the inverse bound and all approximation arguments below apply to arbitrary $L^2$ comparison vectors. The gap (19.4) is for the actual fixed-cutoff native Hamiltonian at a parameter below its bottom, not a positive $L^2$ gap for the canonical critical operator.

Next we determine its action on every fixed macroscopic input. Set

$$
\mathsf A_g=g^{-2}\mathcal D_gaS\mathcal D_g^{-1}.
\tag{19.7}
$$

At phase Fourier frequency $\eta$, its fibre is $ag^{-2}(B_{g\eta}-\lambda)$. L (36.4), (36.7) give convergence of the first eigenvalue to $a\eta^{\mathsf T}M\eta$ and of its height projection to $|\phi\rangle\langle\phi|$ for each fixed $\eta$. The complementary eigenvalues are at least $3a\lambda/g^2$, by min-max for the nonnegative scalar phase potential. Consequently the fibres of $(\mathsf A_{g_s}+t_s)^{-1}$ converge in operator norm to $|\phi\rangle\langle\phi|/(a\eta^{\mathsf T}M\eta+t)$. They are bounded by $1/\inf_s t_s$ for small $s$. Plancherel and dominated convergence prove on the full macroscopic complex space

$$
(\mathsf A_{g_s}+t_s)^{-1}\longrightarrow
 \iota(H_0+t)^{-1}\iota^*\quad\text{strongly}.
\tag{19.8}
$$

For $h\in C_c^\infty(\mathbb R^3\setminus\{0\})$, P (70.3), with its uniform height error, gives

$$
g_s^{-1}W_1(k,\mathbf z/g_s)\phi(k)h(\mathbf z)
 \longrightarrow\frac{\phi(k_0)\phi(k)^2}{4\pi\sqrt{\det M}}
 \frac{h(\mathbf z)}{d(\mathbf z)}
 \quad\text{in }L^2(dk\,d\mathbf z).
\tag{19.9}
$$

Apply (19.8) to this convergent input. Its height projection integrates $\phi^3$ and gives precisely $U_Ch$. Hence

$$
\mathcal D_{g_s}\mathsf T_s\mathcal D_{g_s}^{-1}\iota h
 \longrightarrow\iota T_th.
\tag{19.10}
$$

The uniform bound on $\mathsf T_s$, boundedness of $T_t$, and density of these annular tests extend (19.10) to every fixed $h\in L^2$, including the singular column $\zeta_R$. Equivalently,

$$
\|\widetilde{\mathsf T}_s\mathcal M_sh-\mathcal M_sT_th\|_2\longrightarrow0
\qquad(h\in L^2\text{ fixed}).
\tag{19.11}
$$

We also need the action on the fixed microscopic core. For a compactly supported $f\in L^2(\mathbb R^4)$ put $f_s=\mathcal U_s^{-1}\Pi_sf$. Boundedness of $W_1$ and the exact support volume give

$$
\|W_1f_s\|_2\le C\|f\|_2,
\qquad \|W_1f_s\|_1\le C_f s^{7/2}\|f\|_2.
\tag{19.12}
$$

In the Laplace integral for $\mathsf T_sf_s=(g_s/a)\int_0^\infty e^{-m_sT}e^{-TS}W_1f_s\,dT$, the interval $(0,1)$ contributes at most $Cg_s\|f\|_2$ by contraction. L (41.2) gives $\|e^{-TS}\|_{1\to2}\le CT^{-3/4}$ for $T\ge1$, since its squared Gaussian column has integral $O(T^{3/2})$. Thus the remaining interval contributes at most

$$
C_fg_ss^{7/2}m_s^{-1/4}\|f\|_2
 \le C_fg_s^{1/2}s^{7/2}\|f\|_2\longrightarrow0.
\tag{19.13}
$$

The uniform $L^2$ bound on $\mathsf T_s$ and compact-support approximation extend this conclusion to every fixed $f\in L^2$, in particular

$$
\|\widetilde{\mathsf T}_s\Pi_sp\|_2\longrightarrow0.
\tag{19.14}
$$

This argument requires no ordinary phase derivatives of $p$ or of the comparison approximants.

Take the $L^2(\Omega_s)$ comparison vector $A_s=c(\Pi_sp+\mathcal M_s\zeta_R)$; this symbol is unrelated to the Friedrichs operator in (2.2). By (19.11), (19.14) and $(I-T_t)\zeta_R=QY_t$,

$$
(I-\widetilde{\mathsf T}_s)A_s
 =c\Pi_sp+c\mathcal M_s(QY_t)+o_{L^2}(1)
 =\mathcal U_sw_s+o_{L^2}(1),
\tag{19.15}
$$

where the last equality uses Theorem 18.1 and $\|\Pi_sp-p\|_2\to0$. Subtract (19.3), apply the uniformly bounded inverse (19.6), and then replace $\Pi_sp$ by $p$ in full $L^2$. This proves the first assertion in (19.1). The argument acts entirely on $L^2$ and has not placed $A_s$ in a native form or operator domain.

For a bounded $h\in L^2(\mathbb R^3)$, (17.5) gives $|\mathcal M_sh|\le C_hs^8$ on every fixed microscopic compact set. Approximation by bounded $L^2$ functions and the isometry extend local strong convergence to zero to every $h\in L^2$. Their bounded global norms then give

$$
\mathcal M_sh\rightharpoonup0\quad\text{in }L^2(\mathbb R^4)
\qquad(h\in L^2\text{ fixed}).
\tag{19.16}
$$

In particular $\langle p,\mathcal M_s\zeta_R\rangle\to0$. Squaring the already proved complete-norm reconstruction, using $\|F_s\|_2=\|p\|_2=1$ and $\|\mathcal M_s\zeta_R\|_2=\|\zeta_R\|_2$, proves the exact second assertion in (19.1). Both components inherit the same complex factor from the linear actual equation and its source limit (18.3). $\square$

## 20. Every actual finite-$R$ choice, the two masses and absence of a third mass scale

**Theorem 20.1 (conditional phase-orbit rigidity for every actual choice).** Fix one original datum and all the preceding analytic antecedents. For any prescribed sequence $s_n\downarrow0$ and any actual normalized complex ground-state choices in the unchanged $D(S)$, assume only

$$
r_{s_n}\longrightarrow R\in(r_C,\infty).
\tag{20.1}
$$

With the unique column (17.7) and $\alpha_R=(1+\|\zeta_R\|_2^2)^{-1/2}$, one has

$$
\inf_{\theta\in\mathbb R}
 \|F_{s_n}-e^{i\theta}\alpha_R(p+\mathcal M_{s_n}\zeta_R)\|_2
 \longrightarrow0.
\tag{20.2}
$$

In particular any microscopic weak cluster is $cp$ with $|c|=\alpha_R\in(0,1)$, and the datum necessarily has $C_{\rm resp}=0$.

Proof. Every subsequence of the unit vectors $F_s$ has a weakly convergent further subsequence. P Theorem 90.1 identifies its limit as $cp$, and its local compactness gives local strong convergence. If $c=0$, Theorem 10.2 would force $r_s\to r_C$ on that further subsequence, contradicting (20.1). Therefore $c\ne0$. Theorem 19.1 applies and fixes $|c|=\alpha_R$. It also gives convergence to the moving vector in (20.2) with the constant phase $c/|c|$ on this further subsequence. A failure of (20.2) supplies a subsequence with distance bounded below, contradicting that conclusion on a further subsequence. Strict positivity and nonzero norm of $\zeta_R$ give $0<\alpha_R<1$. Finally $E_s=-r_ss^6\to0$, and Theorem 5.1 on any of the nonzero-core subsequences gives $c(0-C_{\rm resp})=0$. This proves the claimed response restriction without asserting that such a datum or $R$ occurs. $\square$

**Corollary 20.2 (exact two masses, common phase and complete accounting).** Under (17.1), the core-subtracted macroscopic state satisfies

$$
\|\mathcal D_{g_s}\psi_s-c\mathcal N_sp-c\iota\zeta_R\|_2\longrightarrow0.
\tag{20.3}
$$

For $K_A=\{\xi:N(\xi)\le A\}$ and every fixed $A,\delta>0$,

$$
\begin{aligned}
\int_{K_A}|F_s|^2d\xi&\longrightarrow |c|^2\int_{K_A}p^2d\xi,\\
\int_{d(\mathbf z)>\delta}|\mathcal D_{g_s}\psi_s(k,\mathbf z)|^2dk\,d\mathbf z
 &\longrightarrow |c|^2\int_{d(\mathbf z)>\delta}|\zeta_R(\mathbf z)|^2d\mathbf z.
\end{aligned}
\tag{20.4}
$$

Consequently the two actual mass fractions are

$$
\mathfrak m_{\rm micro}=|c|^2=\frac1{1+\|\zeta_R\|_2^2},
\qquad
\mathfrak m_{\rm macro}=|c|^2\|\zeta_R\|_2^2
 =\frac{\|\zeta_R\|_2^2}{1+\|\zeta_R\|_2^2},
\qquad \mathfrak m_{\rm micro}+\mathfrak m_{\rm macro}=1.
\tag{20.5}
$$

The first mass is obtained by $s\to0$ followed by $A\to\infty$; the second by $s\to0$ followed by $\delta\downarrow0$. There is no remaining $L^2$ mass at an intermediate or third scale. More explicitly,

$$
\lim_{A\to\infty}\lim_{\delta\downarrow0}\limsup_{n\to\infty}
 \int_{\substack{\xi\in\Omega_{s_n}\setminus K_A\\
 d(g_{s_n}\mathbf q_{s_n}(\xi))\le\delta}}
 |F_{s_n}(\xi)|^2d\xi=0.
\tag{20.6}
$$

The same mass statements hold for the whole sequence in Theorem 20.1, with $|c|^2=\alpha_R^2$, without prescribing a weak limit or a limiting phase. Its two comparison components have a common phase as in (20.2).

Proof. Apply $\mathcal D_{g_s}\mathcal U_s^{-1}$ to the restriction of (19.1) to $\Omega_s$, using the exact maps (17.4), to get (20.3). Formula (19.16)'s local strong conclusion and (19.1) give the first limit in (20.4). For the second, observe that for every fixed compactly supported $f\in L^2(\mathbb R^4)$ the support of $\mathcal N_sf$ has $\mathbf z=g_s\mathbf q_s(\xi)$ with $\xi$ in that fixed compact. This phase support lies in $d(\mathbf z)<\delta$ for small $s$, since $\sup_{\operatorname{supp}f}d(g_s\mathbf q_s)=O(s^4)$. Compact-support approximation and $\|\mathcal N_s\|\le1$ therefore give

$$
\|\mathbf1_{\{d(\mathbf z)>\delta\}}\mathcal N_sp\|_2\longrightarrow0
\qquad(\delta>0\text{ fixed}).
\tag{20.7}
$$

Combining (20.3) with (20.7) proves the second limit. Monotone convergence, $\|p\|_2=1$, $\zeta_R\in L^2$ and the exact law (19.1) give (20.5). Moreover (20.3) and the same compact-support argument show that the limsup mass outside $d(\mathbf z)\le L$ is $|c|^2\int_{d>L}|\zeta_R|^2$, tending to zero as $L\to\infty$; there is no additional mass beyond the macroscopic scale.

For fixed $A,\delta$, $K_A\subset\Omega_s$ and $d(g_s\mathbf q_s)<\delta$ on $K_A$ for all sufficiently small $s$. The two regions in (20.4) are then disjoint under the exact coordinate dictionary, and their complement is exactly the integration region in (20.6). Its limiting mass is

$$
1-|c|^2\int_{K_A}p^2
  -|c|^2\int_{d(\mathbf z)>\delta}|\zeta_R|^2.
\tag{20.8}
$$

First let $\delta\downarrow0$ and then $A\to\infty$. Equation (19.1) makes the result zero, proving (20.6). This is full-mass accounting for the actual states, not merely for the comparison vectors. Under (20.1), the phase-orbit conclusion (20.2) gives (20.3) with varying unit phases and the same modulus $\alpha_R$; every norm and mass argument above is phase invariant, so all the asserted whole-sequence limits follow. $\square$

**Definition 20.3 (correspondence and unresolved selection).** Theorems 18.1 and 19.1 and their consequences are repository-derived deductions from the source-specific actual equation. P (104.6), (104.9)–(104.10) supply the compact early reconstruction and its global operator-norm convergence; P (104.12)–(104.13) supply the multiplier bounds on the full complex native domain; P (70.3), Theorem 72.1 and L (36.4), (36.7), (41.2) supply the fixed-cutoff tail, genuine reference spectral bottom, scalar-fibre limit and full-output spatial error. Proposition 17.2 uses only the original Coulomb Friedrichs operator and P (72.3); Hardy, Fourier transformation, spectral calculus, resolvent identities, positivity, density and dominated integration are classical intermediate tools. Theorems 5.1, 10.2 and 15.1 retain the response-solvability, weak-zero endpoint and strict nonzero-core margin credit. Neither the conditional heat antecedents nor an external threshold theorem is newly authenticated by these deductions.

All limits fix the original datum, $R>r_C$ and the prescribed sequence as specified. Constants may depend on that datum and the fixed gap $R-r_C$; no uniformity through $R=r_C$, in varying data or as $\kappa\to0$ is asserted. The source coefficient in (17.6) uses the raw $j_0s^7$ Jacobian, the unchanged unit source and the height weight $\phi(k_0)$, without survival normalization. Both original Dirichlet faces and the full rational third component remain in every native heat and spectral comparison. The field heat clock remains $B$, independently of the kinetic $a$.

The comparison formulas determine shapes and all $L^2$ mass only. They imply no native form-domain membership, kinetic-energy transfer, native point interaction, cutoff-free realization, analytic-state preparation or physical-space/dimension correspondence. Absolute response sign, positive/zero occurrence, occurrence of a finite mixed branch, actual selection of $R$ or of divergent $r_s$, finer signed energy coefficients and centered crossover remain unresolved. Thus conditional rigidity at an actually occurring finite $R>r_C$ leaves the original every-ground-state decision and the full target of Definition 9.1 unresolved. Entire-height response residuals and resource, cone, observation or completely positive realizations supply no additional native analytic preparation premise.

## 追加锚（本行以下为增补区）

## 21. At most one native eigenvalue below the Coulomb energy order

**Theorem 21.1 (deep spectral count and the actual ground-state complement).** Fix one admitted original datum of Definitions 1.1–2.2 and all its inherited analytic antecedents before taking $s\downarrow0$. In particular retain P Theorems 87.2, 88.1 and 104.2 and R Theorem 9.1 on its entire complex domain. Define the selfadjoint operators

$$
\begin{aligned}
H_s&=aS-\chi_cs^3W_{s^2},&D(H_s)&=D(S),\\
\mathscr H_s&=aC_s-\chi_cU_s
 =s^2\mathcal U_sH_s\mathcal U_s^{-1},&
D(\mathscr H_s)&=D(A_s)=\mathcal U_sD(S)
 \quad\text{in }L^2(\Omega_s).
\end{aligned}
\tag{21.1}
$$

There are constants $C>0,s_0>0$, depending only on this fixed datum and its antecedent constants, such that for every $0<s<s_0$,

$$
\operatorname{rank}_{\mathbb C}
 \mathbf1_{(-\infty,-Cs^6)}(H_s)\le1,
\qquad
\operatorname{rank}_{\mathbb C}
 \mathbf1_{(-\infty,-Cs^8)}(\mathscr H_s)\le1.
\tag{21.2}
$$

For every actual normalized complex ground state $\psi_s$ of $H_s$ and every $u$ in the entire original complex form domain $\mathcal Q$,

$$
\langle\psi_s,u\rangle=0
\quad\Longrightarrow\quad
\mathfrak e_{\chi_cs^3,s^2}[u]\ge-Cs^6\|u\|_2^2.
\tag{21.3}
$$

Equivalently, with $F_s=\mathcal U_s\psi_s$, for every $F\in\mathcal Q_s=\mathcal U_s\mathcal Q$ on the actual moving domain $\Omega_s=I_s\times\mathbb R^3$,

$$
\langle F_s,F\rangle=0
\quad\Longrightarrow\quad
q_s^c[F]\ge-Cs^8\|F\|_2^2.
\tag{21.4}
$$

The spectral intervals in (21.2) are open at their displayed thresholds; (21.3)–(21.4) are non-strict inequalities, including threshold equality. Multiplicities are complex dimensions. The constants are independent of every eigenvector or ground-state choice and require no assumption on the response sign.

Proof. Work first in the common complex space $\mathscr L=L^2(\mathbb R^4,d\xi)$ used in P §104. Native vectors and the output of their resolvents are zero extended from $\Omega_s$ only for these comparisons. Put $t_c=\chi_c/a$, $K=K_{\rm rec}=\mathcal E^{-1}V$ with the precise reconstruction meaning of P (104.1), and $L=I-t_cK$. P Theorem 87.2 makes $K$ compact, with range in $D(\mathcal E)$ and $\mathcal EKf=Vf$. Moreover

$$
\ker L=\mathbb Cp.
\tag{21.5}
$$

Indeed $Lf=0$ implies $f\in D(\mathcal E)$ and $a\mathcal Ef=\chi_cVf$, so P Theorem 88.1 gives $f\in\mathbb Cp$. Conversely $\mathcal E(p-t_cKp)=0$; both terms belong to $D(\mathcal E)$, and injectivity of $\mathcal E$ from P Theorem 87.2 gives $Lp=0$.

There is therefore a number $\gamma>0$ such that

$$
\|Lw\|_2\ge\gamma\|w\|_2
\quad(w\in\mathscr L,\ \langle p,w\rangle=0).
\tag{21.6}
$$

For completeness, if not, take unit vectors $w_n\perp p$ with $Lw_n\to0$. Compactness of $K$ gives a subsequence on which $Kw_n$ converges. The identity $w_n=Lw_n+t_cKw_n$ makes that subsequence converge strongly to a unit vector $w\perp p$ with $Lw=0$, contradicting (21.5). No selfadjointness of $K$ or positive spectral gap above zero for $H_c$ is used. For the orthogonal projection $\Pi f=\langle p,f\rangle p$, (21.5)–(21.6) imply

$$
\|(I-\Pi)f\|_2\le\gamma^{-1}\|Lf\|_2.
\tag{21.7}
$$

Let $z<0$ be any eigenvalue of $H_s$ and $\psi\in D(S)$ any corresponding unit complex eigenvector. R Theorem 9.1 and (2.2), applied to every native form vector, give $H_s\ge-C_R I$ for fixed $C_R>0$ and sufficiently small $s$. Thus $-C_R\le z<0$. Write $F=\mathcal U_s\psi$, zero extended, and $h=-s^2z/a>0$. The exact operator conjugacy (21.1) gives

$$
(C_s+h)F=t_cU_sF,
\qquad F=t_cR_s(h)U_sF,
\qquad 0<h\le A_0s^2,\quad A_0=C_R/a.
\tag{21.8}
$$

These equations hold before extension in $D(C_s)=\mathcal U_sD(S)$ and then as $L^2$ equalities after extension. In particular they apply to every negative eigenvector, without invoking the ground-sequence conclusion of P Theorem 105.1. The coefficient is exactly $s^2(\chi_cs^3)s^{-5}/a=t_c$, with no change of the field heat clock.

Let $C_0,d_s$ be the fixed-data constant and vanishing error of P (104.2). For $s$ small enough that $A_0s^2\le1$, that full-output operator-norm estimate gives, uniformly over all the above eigenvectors whose $h\ge Ms^8$,

$$
\|LF\|_2\le t_c\left[d_s+C_0(A_0s^2)^{3/4}
              +C_0M^{-1/4}+C_0M^{-1/2}\right]
 =:\Delta_s(M).
\tag{21.9}
$$

Choose once and for all $M\ge1$ with $t_cC_0(M^{-1/4}+M^{-1/2})<\gamma/4$, then decrease $s_0$ so that $t_c[d_s+C_0(A_0s^2)^{3/4}]<\gamma/4$ for every $0<s<s_0$. Set $C=aM$. If $z<-Cs^6$, then $h>Ms^8$, so (21.7)–(21.9) give $\|(I-\Pi)F\|_2<1/2$ and hence $|\langle p,F\rangle|^2>3/4$.

P Proposition 70.2 gives discrete spectrum of finite multiplicity below zero at each positive cutoff. If the first projection in (21.2) had rank at least two, its range would contain two orthonormal eigenvectors, including the case of a repeated eigenvalue. Their unitary images $F_1,F_2$ remain orthonormal after zero extension. Complex Bessel's inequality would give

$$
1=\|p\|_2^2\ge
 |\langle p,F_1\rangle|^2+|\langle p,F_2\rangle|^2
 >\frac32,
\tag{21.10}
$$

a contradiction. This proves the first count. The same argument also applies when an eigenvalue equals the threshold, since $h=Ms^8$ still satisfies (21.9); only the asserted open interval is needed. Thus no threshold eigenvector has been silently counted as strictly below it.

To prove (21.3), put $T=-Cs^6$. Negative ground-state attainment is P Proposition 75.2. If its energy $E_s\ge T$, the spectral theorem gives $\mathfrak e_{\chi_cs^3,s^2}[u]\ge T\|u\|_2^2$ for every $u\in\mathcal Q$. If $E_s<T$, (21.2) forces $\mathbf1_{(-\infty,T)}(H_s)$ to have range exactly $\mathbb C\psi_s$ and forces that ground eigenvalue to be simple. For $u\perp\psi_s$, its scalar spectral measure consequently has no mass below $T$. The closed-form spectral representation on the entire form domain gives

$$
\mathfrak e_{\chi_cs^3,s^2}[u]
 =\int_{[T,\infty)}x\,d\langle u,\mathbf1_{(-\infty,x]}(H_s)u\rangle
 \ge T\|u\|_2^2.
\tag{21.11}
$$

At $E_s=T$ the first case applies, regardless of degeneracy; the same is true above $T$. This proves the assertion for every ground-state choice without any independent simplicity assumption on the finite native bottom. Finally the exact unitary conjugacy in (21.1) transports the first spectral projection to the second in (21.2), multiplying energies by $s^2$. Formula (2.2) transports (21.3) to (21.4). Both the operator domain $\mathcal U_sD(S)$ and the form domain $\mathcal Q_s$ retain the two moving Dirichlet faces; zero extension has not replaced them by a fixed-domain operator. $\square$

**Definition 21.2 (source correspondence and remaining scalar).** Theorem 21.1 is a source-specific `repo-derived` consequence of P (104.2), the compact reconstruction and simple complex kernel of P §§87–88, and the full-domain lower bound R (9.1)–(9.2). The latter is essential for the uniform upper bound on $h$ in (21.8); the displayed local coercivity (4.2) alone is not used as a global lower bound. Compactness, complex Bessel's inequality and selfadjoint spectral and closed-form calculus are classical intermediate tools; see [Teschl, *Mathematical Methods in Quantum Mechanics*](../../../Library/Fourier/teschl2009mathematical.md), equation (1.11), §2.3 and §3.1 in the [author-hosted first edition](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf). Its complex Hilbert-space Bessel inequality applies to the orthonormal pair in (21.10); the semibounded closed-form and selfadjoint spectral representations apply to (21.11) on $\mathcal Q$. The count concerns the finite native operator, not just the fixed-domain zero mode or a separate long-scale trial branch.

All constants fix the original signed nonzero $\kappa$, jointly realized rational fields, all-real phase cover, both height deaths and raw source before $s\downarrow0$. The density $j_0$ and the distinction between field multiplier $U_s$ and chart unitary $\mathcal U_s$ remain exactly (2.1)–(2.3); the field clock is $B$, independently of $a$. No uniformity in varying admitted data or as $\kappa\to0$ is asserted. The complement in (21.3) is orthogonal to an actual ground state; it is not the complement of an arbitrarily chosen core or trial state.

The possible single eigenvalue below $-Cs^6$ is not bounded from below by this count. In particular it gives no $E_s\ge-Cs^6$ conclusion, evaluates no signed core scalar or absolute response sign, assumes no finite-$R$ occurrence, and selects neither $r_s$ nor the actual critical ground-state orbit. The original ground energy/scale selection of Definition 9.1, including response-zero selection, remains unresolved. No analytic-state preparation or physical-space/dimension conclusion follows.

## 追加锚（本行以下为增补区）

## 22. A conditional quantitative lower bound at zero response

**Theorem 22.1 (actual zero-response energy and the entire complex form).** Fix one admitted original datum of Definitions 1.1–2.2, including its signed nonzero $\kappa$, jointly realized rational fields, interval, interior pole, $a,\varepsilon$, raw unit source and density $j_0$, before taking $s\downarrow0$. Retain the analytic antecedents of those definitions, P §§104 and 106–107, R §§4–5, 8 and 16–20, and the mode and derivative bounds of [Entire-height response escape](FIB_NATIVE_ENTIRE_HEIGHT_RESPONSE_ESCAPE.md), Theorem 3.1. Let $\Psi$ be the particular real odd response of (3.5), with its canonical $\mathcal Q_E\cap L^2$ representative supplied by R Theorem 16.2. Suppose that this fixed datum satisfies

$$
C_{\rm resp}=\nu^2(K_{\rm base}-D_{\rm resp})
              -\lambda D_{\rm clock}=0.
\tag{22.1}
$$

There exist $C,c,s_0>0$, depending only on this datum and its antecedent constants, such that for every $0<s<s_0$ and every complex $F\in\mathcal Q_s=\mathcal U_s\mathcal Q$,

$$
q_s^c[F]\ge-Cs^4\|F\|_2^2.
\tag{22.2}
$$

Consequently, along exactly $\tau=s^2$, $g_s=\chi_cs^3$,

$$
-Cs^2\le E_s\le-cs^6,\qquad
cs^8\le-\epsilon_c(s)\le Cs^4,\qquad
c\le r_s\le Cs^{-4}.
\tag{22.3}
$$

The upper energy direction in (22.3) is P (100.3), applied at $g_s$; it is not a new identification of the minimizing branch. Constants are independent of every actual normalized complex ground-state choice. The operator remains $aS-g_sW_{s^2}$ on $D(S)$ and the field heat clock remains $B$, independently of $a$. No reality, parity or separate phase $H^1$ restriction is imposed on $F$.

Proof. Write $\chi=\chi_c$, $\beta=\beta_s=\nu s$, $\nabla_H=(X,Y)$, and $\mathfrak d=d_E(0,\cdot)$ for the same homogeneous control metric as R §16. We establish the estimates consumed by the actual-energy argument before passing to arbitrary form vectors.

**Particular weighted response.** Put $U_h=pF_*$ and $v=\Psi-U_h$, with exactly the height projection of R (16.2). R (16.3) supplies

$$
|F_*|\le C|r|,\quad |F_*'|=|q_*|\le C,\quad
p\le C(1+\mathfrak d)^{-5},\quad
|\nabla_Hp|\le C(1+\mathfrak d)^{-6},\quad
\mathfrak d\ge c_r|r|.
\tag{22.4}
$$

The control balls have volume $v_dR^7$. Let $\vartheta_R$ be the even compact spatial cutoff of R §20, equal to one on $\mathbb B_{2R}$ and supported in $\mathbb B_{3R}$. R (20.4) and its $\operatorname{Err}_R=O(R^{-3})$ bound give $h[(1-\vartheta_R)v]\le CR^{-3}$. This vector is odd, so R (16.1) gives $b[(1-\vartheta_R)v]\le CR^{-3}$. Outside $\mathbb B_{3R}$ its horizontal derivatives equal those of $v$. Moreover

$$
XU_h=F_*Xp+pq_*,\qquad YU_h=F_*Yp,
\qquad |\nabla_HU_h|\le C(1+\mathfrak d)^{-5}.
$$

Integrating these pointwise bounds, and using R Lemma 20.1 for $v$ and the same decay for $U_h$, proves, for $R\ge1$,

$$
\int_{\mathfrak d>R}|\nabla_H\Psi|^2\le CR^{-3},
\qquad \|\mathbf1_{\mathfrak d>R}\Psi\|_2\le CR^{-1/2}.
\tag{22.5}
$$

Dyadic summation of $\mathfrak d^2|\nabla_H\Psi|^2$ bounds its integral over $\mathfrak d>1$ by $C\sum_{j\ge0}2^{2j}2^{-3j}<\infty$. Local form membership handles the remaining ball. Together with (22.4), this proves

$$
\begin{gathered}
rX\Psi,rY\Psi\in L^2,\qquad r^2Yp\in L^2,\qquad p\in L^{14/9},\\
\|\mathbf1_{|r|>R}p\|_2+
\|\mathbf1_{|r|>R}rYp\|_2\le CR^{-3/2},\qquad
\|\mathbf1_{|r|>R}Y\Psi\|_2\le CR^{-3/2}.
\end{gathered}
\tag{22.6}
$$

For instance $r^4|Yp|^2\le C\mathfrak d^4(1+\mathfrak d)^{-12}$ is integrable in homogeneous dimension seven, and $5(14/9)>7$ proves the stated integrability of $p$. The Engel Sobolev inequality yields

$$
\|w\|_{14/5}\le C\sqrt{b[w]},\qquad
|\langle p,w\rangle|\le C\sqrt{b[w]}
\quad(w\in\mathcal Q_E).
\tag{22.7}
$$

Here the first inequality is the $s=1$ case of Bahouri–Barilari–Gallagher–Léautaud, [arXiv:2206.10396v1](https://arxiv.org/pdf/2206.10396v1), Theorem 5.1. Their fields, group law, Haar measure and $Q=7$ coincide with (2.6), and their homogeneous norm is $\sqrt b$. Its core inequality extends by form closure to this complex domain, either directly in the complex-valued spaces or by real and imaginary parts; Hölder and (22.6) give the second inequality. These steps prove only the weighted horizontal derivatives needed here. Neither $r\Psi\in L^2$ nor $\Psi\in D(\mathcal E)$ or an uncut native response membership is used.

**Complete cubic field and global remainder.** Use the single bridge and matrix notation of (3.1), and additionally define

$$
\begin{aligned}
M_3&=\int_0^t H_v^3u(H_v)u(H_v)^{\mathsf T}dv,\\
p_3(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t\big[
 -4D\gamma_{M_0}[M_3]-6D^2\gamma_{M_0}[M_1,M_2]
 -\tfrac43D^3\gamma_{M_0}[M_1,M_1,M_1]\big],\\
V_3&=j_0^{-1}\int_1^\infty p_3(t;\cdot)dt,
\qquad V_{1t}=j_0^{-1}\int_1^\infty t p_1(t;\cdot)dt,\\
\mathcal W_3&=\nu^3V_3+\nu\lambda V_{1t}.
\end{aligned}
\tag{22.8}
$$

These integrals converge absolutely, and

$$
\mathcal W_3\circ\sigma=-\mathcal W_3,\qquad
|\mathcal W_3(r,\mathbf z)|\le C(1+|r|)^{-2},
\tag{22.9}
$$

$$
\left\|\widetilde U_s-\left(V+\beta V_1+\beta^2V_2
 +\lambda s^2V_{\rm t}+s^3\mathcal W_3\right)\right\|_\infty
 \le Cs^4.
\tag{22.10}
$$

To prove these claims, fix $\ell>0$ small enough that $(-\ell/s,\ell/s)\Subset I_s$ and $\nu\ell<1/4$, and put $L_s=\ell/s$, $T_s=s^{-2}$. On $S_t<L_s$ define

$$
M(\nu\vartheta)=\int_0^t(1+\nu\vartheta H_v)^{-2}
 u(H_v)u(H_v)^{\mathsf T}dv,\qquad 0\le\vartheta\le s.
$$

The proof of P (107.6) applies also to derivative order four: differentiation of the scalar denominator gives the matrix-order bound $\|M_0^{-1/2}\partial_\vartheta^jM(\nu\vartheta)M_0^{-1/2}\|\le C_jS_t^j$. The covariance is uniformly comparable to $M_0$. Matrix Gaussian differentiation therefore gives, uniformly in $\mathbf z$,

$$
|\partial_\vartheta^j\gamma_{M(\nu\vartheta)}|
 \le C_jS_t^j(\det M_0)^{-1/2}\quad(0\le j\le4).
$$

Indeed each derivative is a polynomial of fixed degree in $M_0^{-1/2}\mathbf z$ times a uniformly decreasing Gaussian; the matrix-order bounds control its coefficients. For $t\le T_s$, $\vartheta\sqrt t\le1$, whence $|\partial_\vartheta^k e^{\lambda\vartheta^2t}|\le C_kt^{k/2}$ for $k\le4$. P (107.5), equivalently (3.3), and the product rule now give

$$
h_t(r)\mathbb E_{0,r}^t\left[
 \mathbf1_{S_t<L_s}\sup_{0\le\vartheta\le s}
 |\partial_\vartheta^4(e^{\lambda\vartheta^2t}
                       \gamma_{M(\nu\vartheta)})|\right]
 \le C\sum_{j=0}^4t^{(4-j)/2}t^{(j-7)/2}
 \le Ct^{-3/2}.
\tag{22.11}
$$

Taylor's theorem is applied on each path before averaging. Its integrated remainder on $1\le t\le T_s$ is at most $Cs^4\int_1^{T_s}t^{-3/2}dt\le Cs^4$. The expansion $M(\beta)=M_0-2\beta M_1+3\beta^2M_2-4\beta^3M_3+\cdots$ gives exactly (22.8); the retained combined-clock coefficients are

$$
p_0+\nu s p_1+s^2(\nu^2p_2+\lambda t p_0)
             +s^3(\nu^3p_3+\nu\lambda t p_1).
\tag{22.12}
$$

In particular the cubic time-field cross term has not been omitted. The same moment estimate at zero parameter bounds $|p_3|+|tp_1|$ by $Ct^{-2}e^{-cr^2/t}$, proving convergence and (22.9)'s decay. Reflection of the bridge, with the phase transformation in $\sigma$, proves its odd parity, exactly as for P (107.8).

It remains to compare the auxiliary strip with the complete native field. On every bridge surviving in the original $I_s$, $1+\beta H_v$ has positive fixed lower and upper bounds: these are the bounds for $(k-\alpha_\kappa)/d_0$ on the original interval. Thus the surviving covariance is comparable to $M_0$, even on paths leaving the auxiliary strip. The supremum of its Gaussian is at most $C(\det M_0)^{-1/2}$. P (107.5) bounds the cost of deleting those paths on $[1,T_s]$ by

$$
C\int_1^{T_s}t^{-7/2}e^{-cL_s^2/t}dt
 \le CL_s^{-5}=O(s^5).
\tag{22.13}
$$

For each coefficient $t^kp_j$ in (22.12), $j+2k\le3$, the same estimate bounds removal of the auxiliary indicator by $CL_s^{j+2k-5}$ after integration. Its prefactor $s^{j+2k}$ makes this $O(s^5)$. The integral of that coefficient over $t>T_s$ is at most $CT_s^{(j+2k-5)/2}$, again $O(s^5)$ after its prefactor. Finally (2.9a) bounds the original complete native integral over $t>T_s$ by $Cs^5$. All factors $j_0^{-1}$ are unchanged. These bounds are uniform over every real phase and every height endpoint, including zero extension outside $I_s$: there a bridge with $S_t<L_s$ cannot end, and the omitted coefficient paths satisfy the same estimates. This proves (22.10). Only the stated fixed-order bridge moments, surviving-path covariance and native long tail were used; no infinite-time derivative exchange or global conclusion from a local heat expansion is needed.

**Supported complex lower bound.** Choose $\delta>0$ small enough that $|r|\le3\delta/s$ lies between both moving faces and $3\nu\delta<1/4$, and set $R=\delta/s$. Further smallness of this fixed $\delta$ will be specified below. Let $\rho$ be the even cutoff of R Lemma 8.1 and let $d=d_{s,\delta}$ be exactly its (8.1): $d=\rho(r/R)((1+\beta r)^{-2}-1)$ on $|r|<3R$, and $d=0$ elsewhere. The rational expression is evaluated only on that safe strip. On $\mathcal Q_E$ define the estimating form

$$
\begin{aligned}
\mathfrak q_{s,\delta}[z]={}&h[z]+a\int d|Yz|^2
 -\chi\int(\beta V_1+\beta^2V_2+\lambda s^2V_{\rm t}
                         +s^3\mathcal W_3)|z|^2
 -a\lambda s^2\|z\|_2^2.
\end{aligned}
\tag{22.14}
$$

For every $u\in\mathcal Q_E$ supported in $|r|\le2R$, native strip admissibility and (22.10) imply

$$
|\widetilde q_s^c[u]-\mathfrak q_{s,\delta}[u]|
 \le Cs^4\|u\|_2^2.
\tag{22.15}
$$

Put $t_s=p+\beta\Psi$, $c=b(p,u)/b[p]=\mu^{-1}\int Vpu$, and $w=u-ct_s$. By R Theorem 16.2 these are canonical form vectors. Oddness gives $b(p,\Psi)=0$, so $b(p,w)=0$ and $|c|\le C\|u\|_2$, using $Vp\in L^2$. The estimating form is used on $t_s,w$ on the canonical space; exact native agreement is claimed only on their supported sum $u$.

Define $I_\Psi=\int r(Yp)(Y\Psi)$ and $J_\Psi=\int V_1p\Psi$. The response equation gives $D_{\rm resp}=2aI_\Psi+\chi J_\Psi$ and $h[t_s]=\beta^2D_{\rm resp}$. Taylor expansion of the safe rational coefficient through cubic order and parity give

$$
a\int d|Yt_s|^2
 =3a\beta^2A-4a\beta^2I_\Psi+O_\delta(s^4).
\tag{22.16}
$$

Here are the required tail and remainder bounds for this expansion. The $p$ diagonal's odd linear and cubic terms vanish with the even cutoff; its quadratic cutoff loss is $O(\beta^2R^{-3})$ by (22.6), and its fourth-order remainder is bounded by $C\beta^4\|r^2Yp\|_2^2$. For the leading kinetic cross term the omitted tail is bounded by

$$
\int_{|r|>2R}|rYp\,Y\Psi|
 \le\|\mathbf1_{|r|>2R}rYp\|_2
       \|\mathbf1_{|r|>2R}Y\Psi\|_2
 \le CR^{-3}.
\tag{22.17}
$$

Its coefficient is $\beta^2$, making the loss $O_\delta(s^5)$. The quadratic-coefficient cross term vanishes by parity, and the remaining cross term is bounded by $C\beta^4\|r^2Yp\|_2\|rY\Psi\|_2$. In the response diagonal the linear coefficient vanishes by parity; the remainder is bounded by $C\beta^4\|rY\Psi\|_2^2$. These are finite by (22.6), establishing (22.16) without an unproved weighted response norm.

The complete potential expansion on $t_s$ has its quadratic part $-\chi\beta^2(C_2+2J_\Psi)-\chi\lambda s^2T$. Every cubic base contribution vanishes: $V_1\Psi^2$, $V_2p\Psi$, $V_{\rm t}p\Psi$ and $\mathcal W_3p^2$ are odd. Boundedness of the fields and $p,\Psi\in L^2$ bound the remaining terms by $Cs^4$. The exact threshold is $-a\lambda s^2\|t_s\|_2^2=-a\lambda s^2+O(s^4)$, since $\langle p,\Psi\rangle=0$. Thus

$$
\mathfrak q_{s,\delta}[t_s]
 =\beta^2(K_{\rm base}-D_{\rm resp})
       -\lambda s^2D_{\rm clock}+O_\delta(s^4)
 =O_\delta(s^4),
\tag{22.18}
$$

where the last equality uses exactly (22.1).

We next bound the cross and complement terms for arbitrary complex $w$ with $b(p,w)=0$. The complexified response equation gives $h(t_s,w)=\beta\ell(w)$; its first-order kinetic and $V_1$ contributions cancel those in (22.14). The remaining kinetic coefficients satisfy

$$
\|(d+2\beta r)Yp\|_2\le C_\delta s^2,
\qquad \|\beta dY\Psi\|_2\le Cs^2.
\tag{22.19}
$$

For the first bound, on $|r|<3R$ write $d+2\beta r=\rho(r/R)(d_{\rm rat}(r)+2\beta r)+2\beta r(1-\rho(r/R))$, where $d_{\rm rat}(r)=(1+\beta r)^{-2}-1$ is evaluated only there. Outside that strip $d+2\beta r=2\beta r$. The first term is bounded by $C\beta^2r^2$ on the strip, and the remaining terms have norm at most $C\beta R^{-3/2}$ after multiplication by $Yp$, by (22.6). For the second bound use $|d|\le C|\beta r|$ and $rY\Psi\in L^2$.

R Theorem 4.1 bounds each $L\in\{V_1,V_2,V_{\rm t}\}$ by $C\sqrt V$, with $\int\sqrt V|z|^2\le\Gamma b[z]$. Cauchy–Schwarz with this positive weight bounds $|\int L\Psi w|$ by $C\sqrt{b[\Psi]}\sqrt{b[w]}$; (3.6) gives the analogous bound with $p$. Equation (22.7) bounds the threshold cross term containing $p$. Keep the threshold term containing $\beta\Psi$ and the bounded cubic-field cross term as $L^2$ terms. Together with (22.19) this gives

$$
|\mathfrak q_{s,\delta}(t_s,w)|
 \le C_\delta s^2\sqrt{b[w]}+Cs^3\|w\|_2,
\tag{22.20}
$$

$$
\mathfrak q_{s,\delta}[w]
 \ge(a\theta-C\delta-Cs)b[w]-Cs^2\|w\|_2^2.
\tag{22.21}
$$

The second inequality uses the energy-complement gap (3.4), $|d|\le C\delta$, the same multiplier bounds, and boundedness of $\mathcal W_3$. In particular its negative $L^2$ term is retained.

To absorb that term use the support relation, not a positive global $L^2$ gap. Let $\kappa_R(r)$ equal one on $[-2R,2R]$, vanish outside $[-4R,4R]$, and have $|\kappa_R'|\le C/R$. Hilbert-valued one-dimensional Dirichlet Poincaré for $\kappa_Rw$ gives

$$
\begin{aligned}
\|\kappa_Rw\|_2
 &\le CR\|X(\kappa_Rw)\|_2\\
 &\le CR\sqrt{b[w]}+C\|\mathbf1_{2R<|r|<4R}w\|_2.
\end{aligned}
$$

The extra cutoff derivative has been included in the last term. Outside the support of $u$, $w=-ct_s$. The same relation bounds $(1-\kappa_R)w$, so (22.5)–(22.6) yield

$$
\begin{aligned}
\|w\|_2&\le CR\sqrt{b[w]}
      +C|c|\|\mathbf1_{|r|>2R}t_s\|_2\\
 &\le C\frac\delta s\sqrt{b[w]}
      +C(R^{-3/2}+sR^{-1/2})|c|\\
 &\le C\frac\delta s\sqrt{b[w]}+C_\delta s^{3/2}|c|,\\
s^2\|w\|_2^2&\le C\delta^2 b[w]+C_\delta s^5|c|^2.
\end{aligned}
\tag{22.22}
$$

This auxiliary height cutoff is canonical; its support need not lie inside the native domain. Its Poincaré estimate requires only $Xw\in L^2$, as follows by the $\mathcal Q_E$ core closure and Fubini, with values in $L^2(\mathbb R^3;\mathbb C)$.

Use complex polarization on $u=ct_s+w$. First fix $\delta>0$ small enough to absorb $C\delta+C\delta^2$ in (22.21) into $a\theta$, then take $s$ sufficiently small. In the cross term (22.20), (22.22) bounds $s^3\|w\|_2$ by $C\delta s^2\sqrt{b[w]}+C_\delta s^{9/2}|c|$. Young's inequality absorbs $C_\delta s^2|c|\sqrt{b[w]}$ and leaves $C_\delta s^4|c|^2$; the $s^5$ and $s^{9/2}$ terms are smaller. Combining (22.18)–(22.22) and then (22.15) proves

$$
\widetilde q_s^c[u]\ge-C_\delta s^4\|u\|_2^2
\quad\bigl(u\in\mathcal Q_E,
             \operatorname{supp}u\subset\{|r|\le2\delta/s\}\bigr).
\tag{22.23}
$$

All pairings extend from the core by the displayed bounds. Only $p$ and $\Psi$ have prescribed parities; neither $u$ nor $w$ is restricted to a real or parity subspace.

**Actual far-height mass.** We claim that, for the same fixed $\delta$, every actual unit complex ground state satisfies

$$
\int_{|r|>\delta/s}|F_s|^2
 \le C_\delta(s^3+r_s^{-1/2}),\qquad F_s=\mathcal U_s\psi_s.
\tag{22.24}
$$

This claim does not require (22.1). Use exactly P (104.1)'s $Q_s(t)=e^{-tC_s}$, kernel $q_s(t;\eta,\xi)$, resolvent $R_s(h)$, and split $U_s=U_s^{<}+U_s^{>}$ at $T_s=s^{-2}$. We prove, for every $h>0$,

$$
\|\mathbf1_{|r|>R}R_s(h)U_s\|_{2\to2}
 \le C_\delta s^{3/2}+Cs^2h^{-1/4}+Cs^4h^{-1/2},
\qquad R=\delta/s.
\tag{22.25}
$$

For $0<t\le T_s$, P (104.4), symmetry and the semigroup column identity give $\sup_{\eta,\xi}q_s(t;\eta,\xi)\le Ct^{-7/2}$. Explicitly the uniform diagonal estimate at time $t$ is the squared column norm at time $t/2$, and Cauchy–Schwarz at the two endpoints gives this supremum. If $|\eta_r|\le R/2$, integrate first over all output phases. The height coordinate of the original scaled killed diffusion has generator $\partial_r^2$; its killing only decreases its endpoint measure. Hence

$$
\int_{|\xi_r|>R}q_s(t;\eta,\xi)d\xi
 \le e^{\lambda s^2t}
       \mathbb P(|\eta_r+\sqrt2B_t|>R)
 \le Ce^{-cR^2/t}.
$$

The shifted factor is bounded on this time interval; the shifted heat is not assumed to be Markov in raw measure. Positivity and the supremum bound imply

$$
\|\mathbf1_{|\xi_r|>R}q_s(t;\eta,\cdot)\|_2
 \le Ct^{-7/4}e^{-cR^2/t}.
\tag{22.26}
$$

Split the input $U_s^{<}f$ at $|\eta_r|=R/2$ in the resolvent integral over $0<t<T_s$. For the inner input, P (104.6) gives $\|U_s^{<}f\|_1\le C\|f\|_2$, so (22.26) bounds its full-output contribution by

$$
C\|f\|_2\int_0^{T_s}t^{-7/4}e^{-cR^2/t}dt
 \le CR^{-3/2}\|f\|_2.
$$

For the outer input, $0\le U_s^{<}\le U_s$ and (2.9)'s native height bound give multiplier norm $C_\delta s^5$. The same height bound applies before shear because the phase shear is bijective at each height. Since $Q_s(t)$ is an $L^2$ contraction, this contribution is at most $C_\delta s^5T_s\|f\|_2=C_\delta s^3\|f\|_2$. For the rest of the short-potential resolvent integral retain P (104.11)'s $Cs^2h^{-1/4}$ bound. For the entire long potential use P (104.14)'s $Cs^4h^{-1/2}$ bound; its multiplier is the actual fixed-cutoff $W_1$, not an $L^2$ Coulomb surrogate. These estimates prove (22.25), including time zero, all output phases and both moving deaths.

The actual eigen-equation on $D(C_s)=\mathcal U_sD(S)$ is

$$
F_s=\frac\chi a R_s(h_s)U_sF_s,
\qquad h_s=-\epsilon_c(s)/a=r_ss^8/a>0.
\tag{22.27}
$$

Substitution in (22.25) gives $\|\mathbf1_{|r|>\delta/s}F_s\|_2\le C_\delta s^{3/2}+Cr_s^{-1/4}+Cr_s^{-1/2}$. P (100.3) gives $r_s\ge c_0>0$, so squaring and absorbing $r_s^{-1}$ into $C r_s^{-1/2}$ proves (22.24). All constants are uniform over actual ground-state choices; no rate for P (104.2)'s $d_s$ or norm-to-energy transfer has entered.

**Native energy closure.** For any actual unit ground state put $f_s=\mathcal T_sF_s$. The shear preserves heights and norms, so (22.24) holds for $f_s$. Use the original quadratic height partition $\eta_R^2+\zeta_R^2=1$ of (2.11). The full complex closed-domain IMS identity R (9.3) gives

$$
\epsilon_c(s)=\widetilde q_s^c[\eta_Rf_s]
 +\widetilde q_s^c[\zeta_Rf_s]
 -a\int(|\eta_R'|^2+|\zeta_R'|^2)|f_s|^2.
\tag{22.28}
$$

The inner vector is a canonical form vector supported in $|r|\le2R$ and is bounded below by (22.23). In the outer vector retain the exact nonnegative native free threshold form $aC_s$, with both faces, rather than discarding its threshold subtraction. By (2.9) the outer potential then costs at most $C_\delta s^5$. The derivative term is supported where $|r|>R$ and is at most $C_\delta s^2\int_{|r|>R}|f_s|^2$. Thus (22.24) gives

$$
-\epsilon_c(s)\le Cs^4+Cs^2r_s^{-1/2},
\qquad -E_s\le Cs^2+Cr_s^{-1/2}.
\tag{22.29}
$$

Set $x_s=(-E_s)/s^2>0$. Since $r_s=x_ss^{-4}$, (22.29) implies $x_s\le C+Cx_s^{-1/2}$. If $x_s\ge1$, its right side is at most $2C$; otherwise $x_s<1$. Hence $x_s$ is uniformly bounded and $E_s\ge-Cs^2$. At each $s>0$ the bottom is attained by the original-domain operator, by P Proposition 75.2. It is the infimum over the entire original complex form domain. Therefore this bound on its actual attained value implies (22.2) for every $F\in\mathcal Q_s$ by homogeneity, including vectors of arbitrary kinetic size. Combining with P (100.3) proves (22.3). Actual minimizers were used in (22.27)–(22.29), not replaced by trials. $\square$

**Definition 22.2 (attribution, quantifiers and unresolved selection).** Theorem 22.1 is a `repo-derived` conditional actual-energy estimate. P (100.3) owns its macroscopic one-sided upper direction; P §104 owns the exact native short/long split and complete complex reconstruction bounds. P §§106–107 own the weighted mode, parity and fixed-order bridge moments; R §§4–5 and 8 own the coefficient multipliers, horizontal-energy complement gap, response equation and safe estimating coefficient; R §§16 and 19–20 own the particular canonical $L^2$/form representative and exterior loss. Entire-height response escape, Theorem 3.1, owns the full mode and first-horizontal-derivative decay. The particular weighted-response consequence, complete cubic-field estimate, supported response-corrected lower bound and actual far-height estimate above are consumed in the native energy closure, not separate replacements for that closure. The earlier nonassertion of response membership in Definition 3.2 is used only at its original scope; the stronger particular membership here is precisely R Theorem 16.2.

The Sobolev interface is the identical Engel/Haar/$Q=7$ case of Bahouri–Barilari–Gallagher–Léautaud, Theorem 5.1 cited in (22.7). Colin de Verdière–Hillairet–Trélat, [DOI 10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf), Theorem A and Theorem 3.2, have the compact positive-time/interior-endpoint and local-realization scopes described in P §§104 and 107. The original smooth interior rational fields, zero drift, constant density and step-three flag meet those local hypotheses. They do not supply (22.10)'s global integrated remainder; (22.11)–(22.13) supply it. No one-dimensional threshold power law or positive canonical $L^2$ gap is imported. The inherited global heat, reconstruction and attainment statements remain ordinary conditional antecedents.

Every constant and limit fixes the same original datum before $s\downarrow0$; no uniformity over varying data, vanishing $\kappa$, or a moving zero-response locus is asserted. The full real phase cover, both original Dirichlet faces, raw unit source, $j_0$ density and original rational third field remain unchanged. The canonical estimating vectors do not assert uncut native response membership, and the actual all-form conclusion uses only the original operator and form domains. No physical-space/dimension or analytic-state preparation conclusion follows.

The premise $C_{\rm resp}=0$ has not been shown to occur. Absolute canonical response sign and positive/zero occurrence remain unresolved. The interval $cs^6\le-E_s\le Cs^2$ does not give a sharp order, signed fourth-order coefficient, centered crossover, or a matching Coulomb lower bound. The range $c\le r_s\le Cs^{-4}$ still permits bounded, divergent and mixed subsequential behavior; it selects no actual ground-state orbit. Indeed when $-E_s\asymp s^2$, (22.24) allows transition mass of order $s^2$, whose IMS cost is of order $s^4$, the same as a prospective fourth-order rescaled energy. Theorem 21.1's count still leaves a possible unique deep ground channel. Thus the original every-actual-choice selection target of Definition 9.1 remains unresolved.

## 追加锚（本行以下为增补区）


## 23. The complete fourth-order field at fixed original data

Throughout §§23–28 fix one admitted original datum of Definitions 1.1–2.2 and retain every analytic antecedent of Theorem 22.1. In particular the signed nonzero $\kappa$, the jointly realized rational vector, both height faces, $a,\varepsilon$, the raw unit source and $j_0$ are fixed before $s\downarrow0$. The heat clock remains $B$, independently of $a$. All actual states have the full complex domains (1.5). The additional premise is $C_{\rm resp}=0$; its occurrence is not asserted. Write $\chi=\chi_c$ and

$$
v=\nu\Psi,\qquad t_s=p+sv,
\tag{23.0}
$$

using exactly the particular real odd $\mathcal Q_E\cap L^2$ representative of R Theorem 16.2. No new representative of the first response is chosen.

**Definition 23.1 (same-bridge fourth-order coefficients).** Reuse $p_0,p_1,p_2,V_1,V_2,V_{\rm t}$ of (3.1) and $p_3,V_3,V_{1t},\mathcal W_3$ of (22.8). On precisely that height bridge, with $u(h)=(1,h,h^2/2)$, define

$$
\begin{aligned}
M_4&=\int_0^t H_u^4u(H_u)u(H_u)^{\mathsf T}\,du,\\
p_4(t;\xi)&=h_t(r)\mathbb E_{0,r}^t\bigl[
 5D\gamma_{M_0}[M_4]+8D^2\gamma_{M_0}[M_1,M_3]
 +\tfrac92D^2\gamma_{M_0}[M_2,M_2]\\
&\hspace{31mm}+6D^3\gamma_{M_0}[M_1,M_1,M_2]
 +\tfrac23D^4\gamma_{M_0}[M_1,M_1,M_1,M_1]\bigr],\\
V_4&=j_0^{-1}\int_1^\infty p_4(t;\cdot)\,dt,\qquad
V_{2t}=j_0^{-1}\int_1^\infty t p_2(t;\cdot)\,dt,\qquad
V_{tt}=j_0^{-1}\int_1^\infty t^2p_0(t;\cdot)\,dt,\\
\mathcal V_1&=\nu V_1,\qquad
\mathcal V_2=\nu^2V_2+\lambda V_{\rm t},\qquad
\mathcal V_3=\mathcal W_3,\\
\mathcal V_4&=\nu^4V_4+\nu^2\lambda V_{2t}+\tfrac12\lambda^2V_{tt}.
\end{aligned}
\tag{23.1}
$$

Matrix derivatives keep the terminal phase fixed. Every integral uses the original $B$ clock, threshold $\lambda$ and factor $j_0^{-1}$.

**Lemma 23.2 (global complete-field remainder).** The new integrals converge absolutely. Each $\mathcal V_j$ is real, bounded and satisfies $\mathcal V_j\circ\sigma=(-1)^j\mathcal V_j$. Moreover $|\mathcal V_4(r,\mathbf z)|\le C(1+|r|)^{-1}$, and on all of $\mathbb R^4$, with the original zero extension,

$$
\left\|\widetilde U_s-
 \left(V+s\mathcal V_1+s^2\mathcal V_2+s^3\mathcal V_3+s^4\mathcal V_4\right)
\right\|_\infty\le Cs^5(1+|\log s|)=o(s^4).
\tag{23.2}
$$

Proof. Choose the same sufficiently small fixed $\ell>0$ as in the proof of (22.10), so $(-\ell/s,\ell/s)\Subset I_s$ and $\nu\ell<1/4$. Put $L_s=\ell/s$ and $T_s=s^{-2}$. On $S_t<L_s$ use

$$
M(\beta)=\int_0^t(1+\beta H_u)^{-2}u(H_u)u(H_u)^{\mathsf T}\,du.
$$

For $|\beta|L_s\le1/4$ this covariance is uniformly comparable to $M_0$. Differentiating the scalar denominator, then conjugating by $M_0^{-1/2}$, gives

$$
\|M_0^{-1/2}M^{(j)}(\beta)M_0^{-1/2}\|\le C_jS_t^j,
\qquad
|\partial_\beta^j\gamma_{M(\beta)}(\mathbf z)|
 \le C_jS_t^j(\det M_0)^{-1/2}\quad(0\le j\le5).
\tag{23.3}
$$

For $j=0$ only the second inequality is intended. Each Gaussian derivative is a polynomial of bounded degree in $M_0^{-1/2}\mathbf z$ times a uniformly decreasing Gaussian. The matrix bound controls its coefficients and therefore its supremum over all real phases. This proves (23.3) directly, extending the finite-order calculation of P (107.6).

For $t\le T_s$, $0\le\vartheta\le s$ and $k\le5$, differentiation gives $|\partial_\vartheta^ke^{\lambda\vartheta^2t}|\le C_kt^{k/2}$, since $\vartheta\sqrt t\le1$. Leibniz, (23.3) and the full-moment estimate (3.3), at orders at most five, imply

$$
h_t(r)\mathbb E_{0,r}^t\left[
 \mathbf1_{S_t<L_s}\sup_{0\le\vartheta\le s}
 \left|\partial_\vartheta^5
       \left(e^{\lambda\vartheta^2t}\gamma_{M(\nu\vartheta)}(\mathbf z)\right)\right|
 \right]
 \le C\sum_{j=0}^5t^{(5-j)/2}t^{(j-7)/2}=Ct^{-1}.
\tag{23.4}
$$

Taylor's theorem is applied on each safe path before averaging. Its integrated remainder on $[1,T_s]$ is at most $Cs^5\int_1^{s^{-2}}t^{-1}dt$. Expanding
$M(\beta)=M_0-2\beta M_1+3\beta^2M_2-4\beta^3M_3+5\beta^4M_4+\cdots$
in the matrix Taylor formula gives the five fourth-order coefficients $5,8,9/2,6,2/3$ in (23.1). For example the second derivative contributes $8D^2\gamma[M_1,M_3]+(9/2)D^2\gamma[M_2,M_2]$, the third contributes $6D^3\gamma[M_1,M_1,M_2]$, and the fourth contributes $(2/3)D^4\gamma[M_1,M_1,M_1,M_1]$. Multiplication by $e^{\lambda s^2t}$ adds exactly $\nu^2\lambda tp_2+(\lambda^2/2)t^2p_0$ at fourth order, as well as the lower-order clock terms already retained.

The moment estimate with the endpoint retained gives

$$
|p_4(t;\xi)|+|tp_2(t;\xi)|+|t^2p_0(t;\xi)|
 \le Ct^{-3/2}e^{-cr^2/t}.
\tag{23.5}
$$

Its integral on $t\ge1$ proves convergence, boundedness and the height decay. Bridge reflection $H\mapsto-H$, with the phase map in $\sigma$, proves the parities exactly as in P (107.8).

We check the entire native comparison. On every path surviving in the original $I_s$, $1+\nu sH_u$ has fixed positive lower and upper bounds inherited from $(k-\alpha_\kappa)/d_0$. Thus its Gaussian has supremum at most $C(\det M_0)^{-1/2}$, including surviving paths that leave the safe strip. By (3.3), deleting these paths on $[1,T_s]$ costs at most

$$
C\int_1^{T_s}t^{-7/2}e^{-cL_s^2/t}dt\le CL_s^{-5}=O(s^5).
$$

For a retained coefficient $t^kp_j$, put $m=j+2k\le4$. Removing its safe-path indicator costs at most $CL_s^{m-5}$ after integration: its integrand is bounded by $Ct^{(m-7)/2}e^{-cL_s^2/t}$, and the substitution $t=L_s^2u$ proves this bound. Its full canonical tail past $T_s$ is at most $CT_s^{(m-5)/2}$. Multiplication by $s^m$ makes both errors $O(s^5)$. The original native tail past $T_s$ is $O(s^5)$ by (2.9a). Both original deaths are retained in the surviving-path part. Outside $I_s$ a safe path cannot have that endpoint; (3.3) then gives the same deleted-coefficient estimates for zero extension. These bounds, including all phases and the unchanged $j_0^{-1}$, prove (23.2). No infinite-time differentiation or local-to-global heat inference is used. $\square$

## 24. The second homogeneous response and the quartic scalar

Let $\dot{\mathcal H}$ be the completion of the complex compact smooth core in $\sqrt b$ and $\dot{\mathcal H}_0=\{z:b(p,z)=0\}$. The Sobolev inequality (22.7) realizes this completion in $L^{14/5}$. The form $h$ extends continuously, is nonnegative and has $h(p,z)=0$ there. Indeed $\int V|z|^2\le C_*b[z]$ extends by density, and its polarized version gives continuity. R Theorem 5.1 and projection along $p$ extend the complement gap to $\dot{\mathcal H}_0$.

All forms are conjugate linear in the first slot; write $\mathfrak a_j[f]=\mathfrak a_j(f,f)$. On pairs for which the integrals are finite define

$$
\begin{aligned}
\mathfrak a_1(f,z)&=-2a\nu\int r\,\overline{Yf}Yz
                   -\chi\int\mathcal V_1\bar fz,\\
\mathfrak a_2(f,z)&=3a\nu^2\int r^2\overline{Yf}Yz
                   -\chi\int\mathcal V_2\bar fz-a\lambda\langle f,z\rangle,\\
\mathfrak a_3(f,z)&=-4a\nu^3\int r^3\overline{Yf}Yz
                   -\chi\int\mathcal V_3\bar fz,\\
\mathfrak a_4(f,z)&=5a\nu^4\int r^4\overline{Yf}Yz
                   -\chi\int\mathcal V_4\bar fz,\\
\mathcal F_2(z)&=\mathfrak a_2(p,z)+\mathfrak a_1(v,z).
\end{aligned}
\tag{24.1}
$$

These are not bounded forms on arbitrary pairs of canonical or actual states. Only their indicated fixed-vector pairings are used.

**Lemma 24.1 (second response in homogeneous energy).** There is a unique $\Upsilon\in\dot{\mathcal H}_0$ such that

$$
h(\Upsilon,z)=-\mathcal F_2(z)\quad(z\in\dot{\mathcal H}),
\qquad b(p,\Upsilon)=0.
\tag{24.2}
$$

It is real and even. No $L^2$ representative or native-domain membership of $\Upsilon$ is asserted.

Proof. The kinetic terms of $\mathcal F_2$ are continuous in $\sqrt b$ because $r^2Yp,rYv\in L^2$ by (22.6). For $L\in\{V_1,V_2,V_{\rm t}\}$, (3.4) gives $|L|\le C\sqrt V$ and $\int\sqrt V|z|^2\le\Gamma b[z]$. Weighted Cauchy–Schwarz therefore bounds the pairings with $p$ or $v$ by $C\sqrt{b[z]}$. The full unweighted threshold term is continuous because
$|\langle p,z\rangle|\le\|p\|_{14/9}\|z\|_{14/5}\le C\sqrt{b[z]}$,
using (22.6)–(22.7). These estimates define the complex linear $\mathcal F_2$ on the completion.

The first response equation (3.5), with R Theorem 16.2's representative, says on this completion

$$
h(v,z)=-\mathfrak a_1(p,z).
\tag{24.3}
$$

Parity extends it from the odd completion to all $z$. In particular $\mathfrak a_1(p,v)=-h[v]$ is real. Hermitian symmetry and $\|p\|_2=1$ give the exact compatibility

$$
\begin{aligned}
\mathcal F_2(p)
 &=\mathfrak a_2[p]-h[v]\\
 &=\nu^2(K_{\rm base}-D_{\rm resp})-\lambda D_{\rm clock}
 =C_{\rm resp}=0.
\end{aligned}
\tag{24.4}
$$

Thus the threshold contribution $-a\lambda\langle p,z\rangle$ is included in compatibility. On $\dot{\mathcal H}_0$ the bounds $a\theta b\le h\le ab$ and Riesz representation give a unique solution of (24.2). Since both sides annihilate $p$, it solves the equation on the whole completion. Complex conjugation and reflection commute with $h$, while $\mathcal F_2$ is real on real vectors and annihilates odd vectors. Uniqueness gives reality and evenness. $\square$

**Definition 24.2 (the same-source coefficient).** Set

$$
\begin{aligned}
D_4&=\mathfrak a_4[p]+2\operatorname{Re}\mathfrak a_3(p,v)+\mathfrak a_2[v]\\
 &=5a\nu^4\int r^4|Yp|^2
   -8a\nu^3\int r^3(Yp)(Yv)
   +3a\nu^2\int r^2|Yv|^2\\
 &\quad-\chi\int\bigl(\mathcal V_4p^2+2\mathcal V_3pv+\mathcal V_2v^2\bigr)
   -a\lambda\|v\|_2^2,\\
C_4&=D_4-h[\Upsilon].
\end{aligned}
\tag{24.5}
$$

All kinetic integrals are absolutely finite: their majorants are respectively $|r^2Yp|^2$, $|r^2Yp|\,|rYv|$ and $|rYv|^2$, from (22.6). Boundedness of the fields and $p,v\in L^2$ prove finiteness of the potential and threshold integrals. Thus $C_4$ is a defined real scalar of the same original datum. In particular (23.1)'s $\nu^2\lambda V_{2t}$ and $\lambda^2V_{tt}/2$, and the last threshold term in (24.5), are retained.

Real core density and (24.2) give

$$
\inf_{z\in C_c^\infty(\mathbb R^4;\mathbb R)}
 \{h[z]+2\mathcal F_2(z)\}=-h[\Upsilon].
\tag{24.6}
$$

Indeed the expression equals $h[z-\Upsilon]-h[\Upsilon]$. Approximate $\Upsilon$ in energy by real core vectors. Their possible $p$ coordinates do not affect either $h$ or $\mathcal F_2$; no $L^2$ approximation of $\Upsilon$ is used.

## 25. A retained estimate for every actual complex choice

Fix $\delta>0$ sufficiently small as in Theorem 22.1 and R Lemma 8.1, and put $R=\delta/s$. It remains fixed throughout each small-$s$ argument. Let $d=d_{s,\delta}$ be exactly R (8.1), including its even cutoff $\rho$. On $\mathcal Q_E$ use the estimating form

$$
\widehat q_s[z]=h[z]+a\int d|Yz|^2
 -\chi\int(\widetilde U_s-V)|z|^2-a\lambda s^2\|z\|_2^2.
\tag{25.1}
$$

On vectors supported in $|r|\le2R$ it agrees exactly with the original sheared form. The rational expression in $d$ is evaluated only on $|r|<3R$. This introduces no replacement native operator.

**Lemma 25.1 (retained complement estimate).** For a supported complex $u$ put $c=b(p,u)/b[p]$ and $w=u-ct_s$. There are $k>0$ and $C_\delta<\infty$ such that, for sufficiently small $s$,

$$
\widehat q_s[u]\ge k b[w]-C_\delta s^4\|u\|_2^2,
\qquad b(p,w)=0.
\tag{25.2}
$$

For every actual normalized complex ground state define

$$
F_s=\mathcal U_s\psi_s,\qquad f_s=\mathcal T_sF_s,\qquad
u_s=\eta_R f_s,\qquad
c_s=b(p,u_s)/b[p],\qquad w_s=u_s-c_st_s.
\tag{25.3}
$$

Then, uniformly over all actual choices,

$$
b(p,w_s)=0,\qquad
b[w_s]\le C_\delta\bigl(s^4+s^2r_s^{-1/2}\bigr).
\tag{25.4}
$$

Proof. Let $\mathfrak q=\mathfrak q_{s,\delta}$ of (22.14). Equations (22.18), (22.20), (22.21) and their proofs give

$$
|\mathfrak q[t_s]|\le C_\delta s^4,\qquad
|\mathfrak q(t_s,w)|\le C_\delta s^2\sqrt{b[w]}+Cs^3\|w\|_2,
\qquad
\mathfrak q[w]\ge(a\theta-C\delta-Cs)b[w]-Cs^2\|w\|_2^2.
\tag{25.5}
$$

The identity $c=\mu^{-1}\int Vpu$ gives $|c|\le C\|u\|_2$. Since $u$ is supported in $|r|\le2R$, $w=-ct_s$ outside that strip. The Hilbert-valued height Poincaré argument (22.22), including its auxiliary cutoff derivative, gives

$$
\|w\|_2\le C\delta s^{-1}\sqrt{b[w]}+C_\delta s^{3/2}|c|.
\tag{25.6}
$$

Consequently $Cs^2\|w\|_2^2\le C\delta^2b[w]+C_\delta s^5|c|^2$, and $s^3\|w\|_2\le C\delta s^2\sqrt{b[w]}+C_\delta s^{9/2}|c|$. Choose $\delta$ so $C\delta+C\delta^2$ leaves a positive part of $a\theta$, and then take $s$ small. In the polarization of $\mathfrak q[ct_s+w]$, Young's inequality absorbs the cross term into less than half this positive part, at cost $C_\delta s^4|c|^2$. Retain the rest as $kb[w]$. Equation (22.10) bounds $|\widehat q_s[u]-\mathfrak q[u]|$ by $Cs^4\|u\|_2^2$. This proves (25.2), without a global $L^2$ gap.

The actual closed-form eigen-equation tested with $\eta_R^2 f_s$ gives exactly

$$
\widehat q_s[u_s]=\epsilon_c(s)\|u_s\|_2^2
                  +a\int|\eta_R'|^2|f_s|^2.
\tag{25.7}
$$

Height multiplication preserves the full complex closed domain by the supported-strip core closure; $Y\eta_R=0$ and the $X$ product rule gives the displayed derivative term. Native negativity, $\|u_s\|_2\le1$ and (22.24), which is unchanged by the height-preserving shear, bound the right side above by $C_\delta s^2(s^3+r_s^{-1/2})$. Apply (25.2) and absorb $s^5$ into $s^4$ to obtain (25.4). All constants are independent of the actual normalized complex choice. $\square$

**Corollary 25.2 (negative fourth-order subsequences and the weak threshold pairing).** On any actual sequence with

$$
\epsilon_c(s)/s^4\longrightarrow L<0,
\tag{25.8}
$$

one has

$$
r_s\asymp s^{-4},\quad b[w_s]=O_\delta(s^4),\quad
\|w_s\|_2=O_\delta(s),\quad
w_s/s\rightharpoonup0\text{ in }L^2,\quad
\langle v,w_s\rangle=o_\delta(s).
\tag{25.9}
$$

Proof. The scale relation is (1.7). Insert it in (25.4), then (25.6); $c_s$ is bounded. The vectors $w_s/s$ are bounded in $L^2$, while $\|X(w_s/s)\|_2=O_\delta(s)\to0$. Every weak $L^2$ cluster point therefore has distributional $\partial_r$ equal to zero. An $L^2(\mathbb R_r\times\mathbb R^3)$ function independent of $r$ is zero, by Fubini. Weak compactness and uniqueness of this cluster point prove weak convergence along the entire sequence. Pair it with the fixed $v\in L^2$ to obtain the last assertion. No estimate of $\langle v,z\rangle$ by $\sqrt{b[z]}$ is asserted or used. $\square$

## 26. Fourth-order pairings and both moving cutoffs

Keep the same fixed $\delta$. Put $\vartheta_s=\eta_{R/4}$ and $e_s=(1-\vartheta_s)t_s$. The vector $\vartheta_st_s$ is supported in $|r|\le R/2$ and is native admissible. The vector $e_s$ is used only in canonical estimating pairings. The decay (22.4) and ball volume $v_dR^7$ imply $\|\mathbf1_{|r|>R}\nabla_Hp\|_2\le CR^{-5/2}$. Combining (22.5)–(22.6) with the cutoff product rule gives

$$
\sqrt{b[e_s]}\le C(R^{-5/2}+sR^{-3/2})=O_\delta(s^{5/2}),
\qquad
\|e_s\|_2\le C(R^{-3/2}+sR^{-1/2})=O_\delta(s^{3/2}).
\tag{26.1}
$$

For example the extra $X$ derivative costs $R^{-1}$ times the indicated $L^2$ tail; $Y\vartheta_s=0$.

**Lemma 26.1 (all consumed scalar and cutoff errors).** One has

$$
\widehat q_s[t_s]=s^4D_4+o_\delta(s^4),\qquad
\widehat q_s(e_s,t_s)=o_\delta(s^4),\qquad
\widehat q_s[e_s]=O_\delta(s^5).
\tag{26.2}
$$

On every sequence (25.8), additionally,

$$
\widehat q_s(t_s,w_s)=s^2\mathcal F_2(w_s)+o_\delta(s^4),
\qquad
\widehat q_s(e_s,w_s)=o_\delta(s^4).
\tag{26.3}
$$

Proof. Decompose $d$ into its even and odd parts in $r$. They satisfy $|d_{\rm even}|\le Cs^2r^2$, $|d_{\rm odd}|\le Cs|r|$ everywhere and $|d|\le C\delta$. On $|r|\le2R$ its Taylor coefficients are $-2\nu sr,3\nu^2s^2r^2,-4\nu^3s^3r^3,5\nu^4s^4r^4$.

For the $t_s$ diagonal, all odd products vanish by reflection. The omitted quadratic $p$ tail is $O(s^2R^{-3})$ by (22.6); the omitted leading $p,v$ cross tail has the same bound by (22.17). Both are $O_\delta(s^5)$. After subtracting these lower-order contributions, the normalized fourth-order kinetic terms are dominated, respectively, by constant multiples of

$$
r^4|Yp|^2,\qquad |r^2Yp|\,|rYv|,\qquad r^2|Yv|^2.
\tag{26.4}
$$

These are integrable by (22.6). To include the expanding transition and exterior explicitly, on $|r|\ge2R$ one has $s^{-1}\le |r|/(2\delta)$. Thus each lost quadratic or linear coefficient, after division by $s^4$ and inclusion of its $s$ cross factor, has the same respective majorant in (26.4), with a fixed $\delta$-dependent constant. On each fixed height strip ordinary Taylor convergence gives the quartic coefficients. Dominated convergence therefore gives $5a\nu^4\int r^4|Yp|^2-8a\nu^3\int r^3YpYv+3a\nu^2\int r^2|Yv|^2$ at fourth order.

The full second-order coefficient on $t_s$ is
$h[v]+2\mathfrak a_1(p,v)+\mathfrak a_2[p]=C_{\rm resp}=0$.
The first- and third-order integrals vanish by parity. By (23.2), the fourth-order field coefficient is exactly $-\chi\int(\mathcal V_4p^2+2\mathcal V_3pv+\mathcal V_2v^2)$; all higher products are $o(s^4)$ by boundedness and $p,v\in L^2$. The threshold is exactly $-a\lambda s^2-a\lambda s^4\|v\|_2^2$, since $\langle p,v\rangle=0$. The complete-field remainder costs $O(s^5(1+|\log s|))\|t_s\|_2^2$. These calculations prove the first formula of (26.2), with precisely (24.5).

For the boundary pairing, $h(p,z)=0$ and parity remove the $p$ terms and the mixed $p,v$ term, leaving

$$
h(e_s,t_s)=s^2h((1-\vartheta_s)v,v)=O(s^2R^{-3}).
\tag{26.5}
$$

For its rate use (24.3) on $(1-\vartheta_s)v$. In its kinetic right side $Y\vartheta_s=0$; the two tail norms $\|\mathbf1_{|r|>R/4}rYp\|_2$ and $\|\mathbf1_{|r|>R/4}Yv\|_2$ are $O(R^{-3/2})$. The field right side is at most $CR^{-4}\|\mathbf1_{|r|>R/4}p\|_2\|\mathbf1_{|r|>R/4}v\|_2=O(R^{-6})$. This proves (26.5), including the derivative implicit in $h$.

The rational part of $\widehat q_s(e_s,t_s)$ is $a\int d(1-\vartheta_s)|Yt_s|^2$. The even/odd bounds above and parity bound its three terms by

$$
Cs^2\int_{|r|>R/4}r^2|Yp|^2
 +Cs^2\int_{|r|>R/4}|rYp\,Yv|
 +Cs^4\int_{|r|>R/4}r^2|Yv|^2
 =O_\delta(s^5)+o_\delta(s^4).
\tag{26.6}
$$

For the field part, the first-order base term and every third-order product are odd and integrate to zero. The second-order tails containing $\mathcal V_1pv$ and $\mathcal V_2p^2$ are $O(R^{-6})$: use (3.2)'s height decays $R^{-4},R^{-3}$ and the $L^2$ tails $R^{-3/2},R^{-1/2}$ of $p,v$. The fourth-order field tails tend to zero by integrability of $\mathcal V_4p^2,\mathcal V_3pv,\mathcal V_2v^2$, and hence cost $o(s^4)$. Higher products and the remainder (23.2) also cost $o(s^4)$. The threshold term is bounded by $Cs^2(R^{-3}+s^2R^{-1})=O_\delta(s^5)$, its odd cross term vanishing. Together with (26.5)–(26.6) this proves $\widehat q_s(e_s,t_s)=o_\delta(s^4)$.

For $\widehat q_s[e_s]$, nonnegativity of $h$ and $h\le ab$, together with $|d|\le C\delta$, bound the kinetic and $h$ terms in absolute value by $Cb[e_s]=O_\delta(s^5)$. The first two field coefficients are bounded energy multipliers by (3.4) and cost $C(s+s^2)b[e_s]$. Boundedness of the cubic and higher fields costs $Cs^3\|e_s\|_2^2=O_\delta(s^6)$. The threshold costs $Cs^2\|e_s\|_2^2=O_\delta(s^5)$. This proves the last formula of (26.2).

For the actual cross term, first-order cancellation by (24.3) leaves the second-order kinetic terms in $s^2\mathcal F_2(w_s)$. The remaining kinetic errors have coefficient norms

$$
\left\|\frac{d+2\nu sr-3\nu^2s^2r^2}{s^2}Yp\right\|_2\longrightarrow0,
\qquad
\left\|\frac{d+2\nu sr}{s}Yv\right\|_2\longrightarrow0.
\tag{26.7}
$$

For the first limit, on $|r|<2R$ the divided Taylor remainder is bounded by $C\delta r^2|Yp|$ and converges pointwise to zero. On the transition and exterior separate the lost linear term, whose norm is at most $Cs^{-1}\|\mathbf1_{|r|>2R}rYp\|_2=O_\delta(s^{1/2})$. The remaining terms there are bounded by $C_\delta r^2|Yp|$ with tail norm tending to zero. For the second limit, $|d|\le Cs|r|$ gives majorant $C|rYv|$, and the multiplier tends pointwise to zero. Equation (25.9) therefore makes the resulting pairings with $Yw_s$ equal to $o_\delta(s^4)$.

The second-order field terms are exactly $-\chi s^2\int(\mathcal V_2p+\mathcal V_1v)w_s$. The next two terms are $s^3$ times pairings with $\mathcal V_3p$ and $\mathcal V_2v$. Their magnitudes are $O_\delta(s^5)$: for the first use boundedness of $\mathcal V_3$, $p\in L^{14/9}$ and Sobolev (22.7); for the second use the energy multiplier bound and weighted Cauchy–Schwarz. The remaining fields have coefficient $O(s^4)$ in $L^2$ when multiplied by $p$ or $v$, and cost $O_\delta(s^5)$ by $\|w_s\|_2=O_\delta(s)$. The full remainder (23.2) is smaller. Retain $-a\lambda s^2\langle p,w_s\rangle$ inside $s^2\mathcal F_2(w_s)$. Its other threshold term is $-a\lambda s^3\langle v,w_s\rangle=o_\delta(s^4)$ by Corollary 25.2. This is the weak unweighted pairing step; $v$ has not been assigned fictitious homogeneous dual membership. These bounds prove the first formula of (26.3).

Finally, continuity of $h$ and $|d|\le C\delta$ bound the $h$ and rational parts of $\widehat q_s(e_s,w_s)$ by $C\sqrt{b[e_s]}\sqrt{b[w_s]}=O_\delta(s^{9/2})$. The first two field coefficients cost $C(s+s^2)\sqrt{b[e_s]}\sqrt{b[w_s]}$ by (3.4). The bounded cubic and higher fields cost $Cs^3\|e_s\|_2\|w_s\|_2=O_\delta(s^{11/2})$, and the threshold costs $Cs^2\|e_s\|_2\|w_s\|_2=O_\delta(s^{9/2})$. Equation (23.2) handles its remainder. This proves the second formula of (26.3). All these actual pairings allow arbitrary complex $w_s$; parity was applied only to the fixed $p,v$ and their even cutoff products. $\square$

## 27. The actual fourth-order spectral bottom

**Theorem 27.1 (complete conditional actual fourth-order law).** At each fixed admitted original datum satisfying the antecedents of Theorem 22.1 and $C_{\rm resp}=0$, the scalar (24.5) satisfies

$$
\lim_{s\downarrow0}\frac{\epsilon_c(s)}{s^4}
 =\lim_{s\downarrow0}\frac{E_s}{s^2}=\min\{0,C_4\}.
\tag{27.1}
$$

If $C_4<0$, then $E_s=C_4s^2+o(s^2)$, $r_s\sim(-C_4)s^{-4}$, and for every prescribed sequence and every actual normalized complex ground-state choice,

$$
\operatorname{dist}_{L^2}(\mathcal U_s\psi_s,\mathbb T p)\longrightarrow0.
\tag{27.2}
$$

Here $\mathbb T p=\{e^{i\theta}p:\theta\in\mathbb R\}$. If $C_4\ge0$, then $E_s=o(s^2)$ and $r_s=o(s^{-4})$. No finer scale or profile selection is asserted in this case.

Proof. First construct a native recovery upper bound. For each fixed real $z\in C_c^\infty$, put $k_s=\vartheta_st_s+s^2z$. For all small $s$ this has height support strictly between both native faces. The supported-strip closure makes $\mathcal T_s^{-1}k_s\in\mathcal Q_s$, with no separate phase regularity imposed, and $\|k_s\|_2\to1$. Lemma 26.1 gives $\widehat q_s[\vartheta_st_s]=s^4D_4+o_\delta(s^4)$. For fixed $z$, (24.3), rational Taylor expansion on its fixed support and (23.2) give $\widehat q_s(t_s,z)=s^2\mathcal F_2(z)+o(s^2)$ and $\widehat q_s[z]\to h[z]$. Since $\vartheta_s=1$ on the support of $z$ and its derivatives for small $s$, $\widehat q_s(e_s,z)=0$ exactly. Exact supported agreement therefore yields

$$
q_s^c[\mathcal T_s^{-1}k_s]
 =s^4\{D_4+h[z]+2\mathcal F_2(z)\}+o_\delta(s^4).
\tag{27.3}
$$

Normalization adds no fourth-order contribution: the numerator is $O(s^4)$ and the norm tends to one. Take $s\downarrow0$ for each fixed $z$, then the real energy-core infimum (24.6), to get

$$
\limsup_{s\downarrow0}\epsilon_c(s)/s^4\le C_4.
\tag{27.4}
$$

Only compact approximants of $\Upsilon$ have been used. This step by itself is a trial upper bound.

Now let an arbitrary sequence satisfy $\epsilon_c(s)/s^4\to L<0$, and choose any actual normalized complex ground states. Then $r_s\to\infty$, so P Theorem 105.1 gives distance to $\mathbb T p$ tending to zero. Multiplying each actual state by a single constant phase gives $F_s\to p$ in $L^2$. Since $\mathcal T_s$ is unitary and strongly continuous at the identity, $f_s=\mathcal T_sF_s\to p$ as well. Hence $u_s\to p$, and $c_s\to1$ by the fixed $Vp\in L^2$ coordinate. No actual state is assumed real or even.

By (25.9), $w_s/s^2$ is bounded in $\dot{\mathcal H}_0$. Let $W$ be a weak energy cluster point. Test the native eigen-equation with any fixed complex compact smooth $z$. For small $s$, $\eta_R=1$ on its support and derivative support, so $\widehat q_s(z,u_s)=\epsilon_c(s)\langle z,f_s\rangle$. Insert $u_s=c_st_s+w_s$ and divide by $s^2$ to obtain

$$
h(z,w_s/s^2)+c_s\overline{\mathcal F_2(z)}\longrightarrow0.
\tag{27.5}
$$

For clarity, the fixed-support rational perturbation paired with $w_s$ is $O_z(s)\sqrt{b[w_s]}=O_z(s^3)$. The first two field perturbations have the same or smaller bound by (3.4); the bounded higher fields and threshold are $O_z(s^2)\|w_s\|_2=O_z(s^3)$. The eigenvalue side is $O_z(s^4)$. The fixed-test expansion on $t_s$ has remainder $o_z(s^2)$ by (24.3) and (23.2). These are all the discarded terms in (27.5). After passage to the weak limit and conjugation, density gives $h(W,z)=-\mathcal F_2(z)$ and $b(p,W)=0$. Lemma 24.1 gives $W=\Upsilon$. Uniqueness of the cluster point yields

$$
w_s/s^2\rightharpoonup\Upsilon\quad\text{in }\dot{\mathcal H}_0.
\tag{27.6}
$$

This asserts only homogeneous energy weak convergence.

Use the native-admissible $\vartheta_st_s$ itself as test in the actual equation. Its support is inside the region where $\eta_R=1$, including derivative supports. The exact identity, with conjugate-linear first slots, is

$$
\begin{aligned}
\epsilon_c(s)\langle\vartheta_st_s,f_s\rangle
 &=\widehat q_s(\vartheta_st_s,u_s)\\
 &=c_s\widehat q_s(t_s-e_s,t_s)+\widehat q_s(t_s-e_s,w_s).
\end{aligned}
\tag{27.7}
$$

Every cutoff error needed here has been proved in Lemma 26.1. Substitution gives

$$
\epsilon_c(s)\langle\vartheta_st_s,f_s\rangle
 =c_ss^4D_4+s^2\mathcal F_2(w_s)+o_\delta(s^4).
\tag{27.8}
$$

The left inner product tends to one, $c_s\to1$, and continuity of $\mathcal F_2$ on energy space with (27.6) gives
$\mathcal F_2(w_s/s^2)\to\mathcal F_2(\Upsilon)=-h[\Upsilon]$.
Divide (27.8) by $s^4$. Every strictly negative actual fourth-order cluster point is therefore $L=C_4$. The IMS error was used with its actual sign in (25.7) to bound the remainder; it has not been discarded at order $s^4$ in (27.8). No norm-to-energy inference has been used.

Theorem 22.1 gives the compact interval $-C\le\epsilon_c(s)/s^4<0$. If $C_4<0$, (27.4) excludes zero cluster points; all cluster points then equal $C_4$. If $C_4\ge0$, the preceding identification excludes every negative cluster point, leaving only zero. This proves the whole limit (27.1). The scale consequences follow from (1.7): $r_s=-E_s/s^6$. In the negative case $r_s\to\infty$, so P Theorem 105.1 supplies (27.2) for every prescribed sequence and every actual choice. In the nonnegative case the dictionary gives only the two stated little-o consequences. $\square$

## 28. Attribution and unresolved original scope

Theorem 27.1 is a `repo-derived` ordinary conditional increment beyond Theorem 22.1's order bound. Its same-source quartic field, complete remainder, energy-continuous second forcing, retained actual remainder, weak unweighted pairing and actual scalar eigen-equation are proved in §§23–27. It reuses the first response equation, finite-strip Poincaré estimate and actual far-height estimate of §22; R §§4–5, 8, 16 and 19–20 supply the energy multipliers, complement gap, particular first-response membership and exterior loss. Entire-height response escape Theorem 3.1 owns the mode and first-horizontal-derivative decay. P §§104–107 own the full complex native reconstruction, actual every-choice orbit criterion and bridge moments. The cubic field is reused from (22.8), with no second definition. Taylor's theorem, Riesz representation, weak compactness, polarization and dominated convergence are mature tools; no literature-wide novelty is claimed.

No new external perturbation theorem is invoked. The Sobolev interface remains exactly (22.7): the Engel group and horizontal fields (2.6), Haar measure, homogeneous dimension seven and order one in Bahouri–Barilari–Gallagher–Léautaud, Theorem 5.1, give $L^{14/5}$ and dual exponent $14/9$. The global fifth-order integrated remainder was proved using the inherited fixed-order moments, not inferred from the local heat theorem. All heat, kernel, local compactness, reconstruction and attainment antecedents remain ordinary conditional premises at their supplied scopes. No positive $L^2$ threshold gap, arbitrary $L^2$ inverse, or $L^2$ second response has been introduced.

The original datum and each applicable $\delta$ are fixed before $s\downarrow0$. Recovery takes the small-$s$ limit for a fixed compact correction first and only then takes its energy-core infimum. The signed nonzero $\kappa$, same jointly realized rational fields, all-real phase cover, both Dirichlet faces, raw unit source, $j_0$, full complex domains and original $B$ clock remain unchanged. Canonical estimating extensions are never replacement native operators.

Zero-response occurrence, the absolute sign of $C_4$, finer nonnegative-$C_4$ selection, centered crossover, analytic/native $L^2$ preparation and physical three-dimensional realization remain unresolved. The nonnegative branch still permits bounded, divergent or mixed subsequential $r_s$. The complete original every-ground-state decision of Definition 9.1, original A and the full target are not settled by this conditional theorem. This ordinary proof makes no Lean/kernel, independent-review, publication or lifecycle claim.

## 追加锚（本行以下为增补区）
