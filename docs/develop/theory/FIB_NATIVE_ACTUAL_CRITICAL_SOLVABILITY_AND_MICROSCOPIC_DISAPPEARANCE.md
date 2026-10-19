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


## 29. The actual adjoint row and its late-return comparison

**Definition 29.1 (fixed data, common space and factor order).** Fix one admitted original datum of Definitions 1.1–2.2 before taking $s\downarrow0$. Retain the conditional analytic antecedents there, P §§76, 87–88, 97 and 104–107, R (8.3), and the mode decay of Entire-height response escape, Theorem 3.1. In particular these include the original positive-cutoff negative attainment, the both-face all-height heat bounds, the specified compact reconstruction and simple critical mode, and the common-bridge inverse-determinant moments. The signed nonzero $\kappa$, the jointly realized rational vector (1.2), its positive denominator margin on $\overline I$, both original Dirichlet faces, all real phase frequencies, raw unit source and $j_0$ remain fixed. Every native form and operator domain is exactly (1.5), transported by the original $\mathcal U_s$ and determinant-one $\mathcal T_s$. No actual state is restricted by parity or reality.

Work on complex $L^2(\mathbb R^4,d\xi)$ by restriction to $\Omega_s$ followed by zero extension. In §§29–35 suppress tildes only on the sheared free operator, heat and field: thus $C_s$ here denotes $\mathcal T_s C_s\mathcal T_s^{-1}$ from (2.2), and its free form is (2.5). Put

$$
\begin{aligned}
\gamma&=\chi_c/a,&T&=s^{-2},&Q_s(t)&=e^{-tC_s},&R_s(h)&=(C_s+h)^{-1},\\
q_s(t;\eta,\xi)&=\text{the kernel of }Q_s(t),&
F_s&=j_0^{-1}\int_1^Tq_s(u;0,\cdot)\,du,\\
U_s^{>}&=s^5W_1\circ\Xi_s\circ\mathscr L_s,&
\widetilde U_s&=F_s+U_s^{>},\\
H_s&=\int_0^TQ_s(t)\,dt,&
\mathcal N_s&=F_sH_s,&\mathcal B_s(h)&=R_s(h)\widetilde U_s.
\end{aligned}
\tag{29.1}
$$

A field in an operator product denotes multiplication. In particular multiplication is after the return in $\mathcal N_s$, and $`\mathcal B_s(h)^*=\widetilde U_sR_s(h)`$. P (104.9)'s sheared product is $H_sF_s$, whose adjoint is $\mathcal N_s$. The split is at original heat time one. Both integrals in (29.1) use the $B$ clock, with shifted factor $e^{\lambda s^2t}$; $a$ enters only through $\gamma$ and the actual spectral parameter

$$
h_s=-\epsilon_c(s)/a=r_ss^8/a.
\tag{29.2}
$$

At zero parameter write $\mathcal N_0=K_{\rm rec}^*$, with precisely P (104.1)'s bounded specified reconstruction. The expression $\mathcal N_0g=V\int_0^\infty P_tg\,dt$ is used only where that integral or its bounded-adjoint interpretation is justified. It is not an inverse on arbitrary $L^2$ right sides.

**Theorem 29.2 (late comparison at the actual spectral parameter).** For $g\in L^1\cap L^2$ complex, $0<s<s_0$ and $0<h\le1$,

$$
\| (\mathcal B_s(h)^*-\mathcal N_s)g\|_2
 \le C(h+s^5)(\|g\|_1+\|g\|_2)
       +Cs^7h^{-1/4}\|g\|_1.
\tag{29.3}
$$

Consequently, on the actual path with $h_s\le1$ and P (100.3)'s $r_s\ge c>0$,

$$
\| (\mathcal B_s(h_s)^*-\mathcal N_s)g\|_2
 \le C_g(h_s+s^5).
\tag{29.4}
$$

Proof. P (104.4), symmetry and semigroup composition give, uniformly in both endpoints and including zero extension,

$$
\begin{aligned}
\|Q_s(t)\|_{2\to2}&\le1,\\
\|Q_s(t)\|_{1\to\infty}&\le
 \begin{cases}Ct^{-7/2},&0<t\le T,\\Cs^4t^{-3/2},&t\ge T,\end{cases}\\
\|Q_s(t)\|_{1\to2}&\le
 \begin{cases}Ct^{-7/4},&0<t\le T,\\Cs^2t^{-3/4},&t\ge T.\end{cases}
\end{aligned}
\tag{29.5}
$$

For the middle line apply the column identity at time $t/2$ and Cauchy–Schwarz between the two endpoints. The overlap of the two time regimes changes only the constant. P (104.6) gives $\|F_s\|_2+\|F_s\|_\infty\le C$. The short-field part of the difference in (29.3) is

$$
F_s\int_0^T(e^{-ht}-1)Q_s(t)g\,dt
 +F_s\int_T^\infty e^{-ht}Q_s(t)g\,dt.
$$

On $(0,1)$ use $|e^{-ht}-1|\le ht$, the multiplier supremum and $L^2$ contraction. On $(1,T)$ use the multiplier $L^2$ norm and the $1\to\infty$ bound. The first term is bounded by
$Ch\|g\|_2+Ch\|g\|_1\int_1^\infty t^{-5/2}dt$.
The second is at most $Cs^4\|g\|_1\int_T^\infty t^{-3/2}dt=Cs^5\|g\|_1$.

The fixed-cutoff multiplier $W_1$ is bounded by Definition 1.2, so $\|U_s^{>}\|_\infty\le Cs^5$. Its return on $(0,T)$ costs
$Cs^5(\|g\|_2+\|g\|_1\int_1^\infty t^{-7/4}dt)$.
On $(T,\infty)$ it costs at most

$$
Cs^7\|g\|_1\int_T^\infty e^{-ht}t^{-3/4}dt
 \le Cs^7h^{-1/4}\|g\|_1.
$$

These estimates prove (29.3). Finally
$s^7h_s^{-1/4}=a^{1/4}s^5r_s^{-1/4}\le Cs^5$, proving (29.4). Absolute kernel bounds apply to complex inputs. Contraction uses $C_s\ge0$; the shifted heat has not been treated as a raw-measure Markov semigroup. Both native deaths remain in every heat operator. $\square$


## 30. Two-endpoint coefficients and their input-height weights

**Definition 30.1 (finite path coefficients).** Use the ordered Engel convolution of (2.6),
$(f*k)(\xi)=\int f(\eta)k(\eta^{-1}\xi)d\eta$.
For $\eta=(A,\mathbf z_\eta)$ and $\xi=(B,\mathbf z_\xi)$ let $H=A+W$ be the height bridge from $A$ to $B$ in time $t$, with $W$ starting at zero. Set

$$
\begin{aligned}
M_\vartheta[H]&=\int_0^t(1+\nu\vartheta H_u)^{-2}
                    u(H_u)u(H_u)^{\mathsf T}\,du,\\
\mathsf q_j(t;\eta,\xi)
 &=h_t(B-A)\mathbb E_{A,B}^t\left[
 \left.\frac1{j!}\partial_\vartheta^j
 \{e^{\lambda\vartheta^2t}\gamma_{M_\vartheta[H]}
                       (\mathbf z_\xi-\mathbf z_\eta)\}\right|_{\vartheta=0}\right],\\
(\mathsf Q_j(t)g)(\xi)&=\int\mathsf q_j(t;\eta,\xi)g(\eta)d\eta,
 \qquad 0\le j\le4.
\end{aligned}
\tag{30.1}
$$

The functions $u,h_t,\gamma_M$ are exactly (3.1). Differentiation is finite on each path in its neighborhood of zero; (30.1) defines coefficients, not a globally pole-free family for nonzero $\vartheta$. On finite safe paths it is the Taylor coefficient of the original sheared, shifted Gaussian. In particular $\mathsf Q_0(t)=P_t$. At the source endpoint zero the coefficients, in order, are

$$
p_0,\quad \nu p_1,\quad \nu^2p_2+\lambda tp_0,\quad
\nu^3p_3+\nu\lambda tp_1,\quad
\nu^4p_4+\nu^2\lambda tp_2+\tfrac12\lambda^2t^2p_0.
\tag{30.2}
$$

Thus their field integrals on $[1,\infty)$ divided by $j_0$ are exactly $\mathcal V_j$ of (23.1), with $\mathcal V_0=V$. Return coefficients have no additional $j_0^{-1}$.

**Lemma 30.2 (weighted ordered kernels).** There are signed kernels $k_{jm}(t)$, $0\le m\le j\le4$, such that

$$
\mathsf Q_j(t)g=\sum_{m=0}^j(r^{j-m}g)*k_{jm}(t),
\qquad
\|k_{jm}(t)\|_b\le Ct^{m/2-(7/2)(1-1/b)}
\quad(1\le b\le\infty).
\tag{30.3}
$$

Each kernel may be a finite sum of differentiated-Gaussian terms. Consequently, whenever the displayed input norms are finite and $1\le p_m\le q\le\infty$,

$$
\|\mathsf Q_j(t)g\|_q
 \le C\sum_{m=0}^j
 t^{m/2-(7/2)(1/p_m-1/q)}\|r^{j-m}g\|_{p_m}.
\tag{30.4}
$$

Proof. The triangular matrix

$$
D_A=\begin{pmatrix}1&0&0\\A&1&0\\A^2/2&A&1\end{pmatrix}
\quad\text{satisfies}\quad u(A+W)=D_Au(W),\qquad\det D_A=1.
$$

The phase component of $\eta^{-1}\xi$ is $D_A^{-1}(\mathbf z_\xi-\mathbf z_\eta)$. Conjugate the covariance by $D_A^{-1}$. Derivatives of $(1+\nu\vartheta(A+W))^{-2}$ at zero are polynomials in $A$ and $W$. Every coefficient of order $j$, after extracting $A^{j-m}$, has relative bridge degree $m$. A clock factor $t^\ell$ contributes degree $2\ell$, so is included in the same count. The remaining expression depends only on $\eta^{-1}\xi$, giving the factor order in (30.3).

Matrix differentiation produces a polynomial in whitened phase variables times a Gaussian. Its absolute value is bounded by a fixed inflated-covariance Gaussian times the corresponding powers of the relative bridge supremum, with clock powers retained. Phase integration of this majorant, then height integration and Brownian scaling, give $\|k_{jm}(t)\|_1\le Ct^{m/2}$. Taking the phase supremum and using P (107.5) on the relative zero-start bridge gives $\|k_{jm}(t)\|_\infty\le Ct^{(m-7)/2}$. Its layer-cake proof works for every nonnegative real moment order, not only integers: the integral $\int_L^\infty v^{\alpha-1}e^{-cv^2/t}dv$ is finite for $\alpha>0$, with the zero-order case supplied separately. Interpolation proves the remaining $L^b$ bounds. Young's inequality with $1+1/q=1/p_m+1/b$ proves (30.4).

Young's inequality here is the classical graded-group convolution inequality of Fischer–Ruzhansky, *Sobolev spaces on graded groups*, [arXiv:1311.0192v1, §2.1, (2.2)](https://arxiv.org/html/1311.0192v1#S2.SS1). The group (2.6) is graded and unimodular, its Haar measure is unit Lebesgue measure, and the factors have the order used in that inequality. It supplies the norm step, not the native coefficient decomposition. $\square$


## 31. The global return expansion on the noncompact seed

**Definition 31.1 (the fixed left coordinate).** With the original $p,V,\mu$ of (2.7), put

$$
g_0=Vp/\mu,\qquad
G_jg=\int_0^\infty\mathsf Q_j(t)g\,dt
\tag{31.1}
$$

on inputs and in norms for which this integral converges. The coordinate is exactly R (8.3): $\langle g_0,f\rangle=\mu^{-1}\int Vpf$. P §§87–88 and Entire-height response escape Theorem 3.1 give

$$
\begin{gathered}
|g_0(\xi)|\le C(1+\mathfrak d(\xi))^{-10},\quad
 g_0\in L^1\cap L^2,\quad \langle g_0,p\rangle=1,\\
G_0g_0=p/(\gamma\mu),\qquad
\gamma\mathcal N_0g_0=g_0,
\qquad \mathfrak d(\xi)=d_E(0,\xi).
\end{gathered}
\tag{31.2}
$$

The identities follow from the specified reconstruction of $Vp$ and its adjoint; they introduce no arbitrary zero-energy inverse. Homogeneous volume growth seven implies

$$
r^ng_0\in L^p\quad\text{if }(10-n)p>7,
\qquad r^ng_0\in L^\infty\quad(0\le n\le5).
\tag{31.3}
$$

**Theorem 31.2 (return remainder with complete endpoint and time tails).** On the entire common output space,

$$
\left\|H_sg_0-\sum_{j=0}^4s^jG_jg_0\right\|_\infty
 \le Cs^5(1+|\log s|).
\tag{31.4}
$$

Moreover $G_jg_0\in L^4$ for $j=1,2,3$, and $G_4g_0\in L^\infty$.

Proof. Fix $\ell>0$ so that $(-\ell/s,\ell/s)\Subset I_s$ and $\nu\ell<1/4$, and put $L=\ell/s$. Use auxiliary killing at $\pm L$ in addition to the original realization. On a path staying in this strip all interpolation covariances $M_\vartheta$, $0\le\vartheta\le s$, are comparable to $M_0$. Finite Gaussian differentiation through order five, as in (23.3), bounds the fifth derivative of the combined shifted density by inflated-Gaussian majorants with input factors $|A|^{5-m}$ and relative degree $m$, $0\le m\le5$. Indeed $|H|\le|A|+\sup|W|$, and clock derivatives contribute their degree-two time powers. Constants are uniform on these paths and $0<t\le T$, since $\vartheta\sqrt t\le1$.

For $t<1$, use the $L^1$ kernel bound against the bounded inputs $r^{5-m}g_0$. The resulting powers $t^{m/2}$ are integrable. For $t\ge1$, (30.4)'s majorant, now at total degree five, uses the following inputs in order $m=5,4,3,2,1,0$:

$$
g_0\in L^1,\quad rg_0\in L^1,\quad r^2g_0\in L^1,\quad
r^3g_0\in L^{7/6},\quad r^4g_0\in L^{7/5},\quad
r^5g_0\in L^{7/4}.
\tag{31.5}
$$

Their time powers in $L^\infty$ are respectively $-1,-3/2,-2,-2,-2,-2$. All memberships are strict instances of (31.3). Taylor's integral remainder on $(0,T)$ is therefore bounded by $Cs^5(1+\log T)$. This estimate does not assume a third or fourth absolute $L^1$ height moment of $g_0$.

We restore the original faces, noncompact input and canonical coefficient times. First split input heights at $|A|=L/4$. For inner input, a path leaving the auxiliary strip has relative height supremum at least $3L/4$. When $|\xi_r|\le L/2$ the deleted-path inverse-determinant bound applies; when $|\xi_r|>L/2$ the relative endpoint displacement is at least $L/4$. In both cases the kernel supremum is at most

$$
Ct^{-7/2}e^{-cL^2/t}.
\tag{31.6}
$$

For surviving original paths, the covariance comparison needed for this bound follows from the fixed positive lower and upper bounds of $(k-\alpha_\kappa)/d_0$ on $\overline I$. It applies even when such paths leave the auxiliary strip. Integrating (31.6) against $|g_0|$ and over $t\in(0,T)$ costs $CL^{-5}$.

For outer input, (31.2) gives supremum $CL^{-10}$ and $L^1$ norm $CL^{-3}$. On $t\le T$ the positive shifted heat has row mass at most $e^{\lambda s^2t}\le e^\lambda$, while (29.5) supplies its $1\to\infty$ bound. Thus the outer native contribution is at most

$$
C\int_0^T\min\{L^{-10},t^{-7/2}L^{-3}\}\,dt\le CL^{-8}.
\tag{31.7}
$$

The same estimate bounds the auxiliary contribution, so deleting it in the preceding Taylor argument is harmless.

For a coefficient of total degree $j\le4$ and relative degree $m$, put $n=j-m$. On inner input, removing the safe-path indicator costs at most $CL^{m-5}M_n(L)$ in the integrated supremum norm, where

$$
M_n(L)=\int_{|r|\le L/4}|r|^n|g_0|\le
 \begin{cases}C,&n<3,\\C(1+\log L),&n=3,\\CL^{n-3},&n>3.\end{cases}
\tag{31.8}
$$

To obtain the bound use the relative-moment version of (31.6) and integrate $t^{(m-7)/2}e^{-cL^2/t}$ on $(0,\infty)$. For (31.8), split homogeneous annuli below and above $L$: above $L$, the factor $|r|^n\le L^n$ on the truncated height region and the mass tail is $O(L^{-3})$. Each quantity $s^jL^{m-5}M_n(L)$ is $O(s^5)$ or smaller.

For outer coefficient input, integrate below $L^2$ with the $L^1$ kernel bound and $\|r^ng_0\mathbf1_{|r|>L/4}\|_\infty\le CL^{n-10}$. The result is $CL^{j-8}$. Above $L^2$, choose

$$
1\le p<\frac7{m+2},\qquad p>\frac7{10-n}.
\tag{31.9}
$$

Such a choice exists for every $j\le4$. The input tail is bounded by $CL^{n-10+7/p}$ and the integrated kernel factor is $CL^{m+2-7/p}$, again giving $CL^{j-8}$. Its prefactor $s^j$ makes it $O(s^8)$.

Finally restore coefficient times $t>T$. For $n=0,1,2$ use input $L^1$ and integrate $t^{(m-7)/2}$; after $s^j$ the costs are $O(s^{5+n})$. For $n=3$ use $p=7/6$, and for $n=4$ use $p=7/5$; (30.4) gives $O(s^7)$ in either case. Thus every omitted coefficient time tail is $O(s^5)$ or smaller. The bounds also cover outputs outside $I_s$: the native kernel is zero there, and a safe path cannot have such an endpoint. This proves (31.4) on the full output space.

For the asserted $L^4$ integrals, all small-time terms are integrable by the finite weighted $L^4$ input norms and the $L^1$ kernel bounds. At large time the unweighted terms for $j=1,2,3$ have powers $-17/8,-13/8,-9/8$. The inputs with one or two height powers lie in $L^1$ and have still more negative powers. The exceptional $r^3g_0$ input for $j=3$ may use $p=7/6$, giving exponent $-17/8$. For $G_4g_0$ in $L^\infty$, the unweighted exponent is $-3/2$, those with one or two input powers are smaller, and the inputs with three or four powers use $7/6,7/5$, giving respectively $-5/2,-5/2$. Small times use bounded weighted inputs. All these time integrals converge absolutely in their stated norms. $\square$


## 32. Early-field remainders in the consumed mixed norms

**Lemma 32.1 (integrated field estimate).** Set $\mathcal V_0=V$ and retain exactly (23.1)'s other coefficients. For $1<p<\infty$ and an integer $0\le n\le4$ satisfying $n<5-7/p$, put $\alpha_p=5-7/p$. Then

$$
\left\|F_s-\sum_{k=0}^ns^k\mathcal V_k\right\|_p\le C
\begin{cases}
s^{n+1},&n+1<\alpha_p,\\
s^{n+1}(1+|\log s|),&n+1=\alpha_p,\\
s^{\alpha_p},&n+1>\alpha_p.
\end{cases}
\tag{32.1}
$$

This is an estimate for the early field $F_s$, not for the long Coulomb field $U_s^{>}$.

Proof. Consider a source-started coefficient or Taylor derivative of total order $m$. Its phase $L^p$ norm is bounded, by Minkowski and the inflated-Gaussian estimate, by a constant times
$h_t(r)\mathbb E[S^m(\det M_0)^{-\alpha/2}]$, where $\alpha=1-1/p$. Concavity, equivalently Hölder, gives

$$
\mathbb E[S^m(\det M_0)^{-\alpha/2}]
 \le\left(\mathbb E[S^{m/\alpha}(\det M_0)^{-1/2}]\right)^\alpha.
\tag{32.2}
$$

P (107.5), with its layer-cake extension to the nonnegative real moment $m/\alpha$, leaves the factor
$h_t(r)^{1/p}t^{(m-7\alpha)/2}$.
Its $L^p(dr)$ norm is $t^{(m-7+7/p)/2}$, since $\int h_t(r)dr=1$. Clock terms have the identical estimate with their total degree. Thus

$$
\|\text{order-}m\text{ source Gaussian}\|_p
 \le Ct^{(m-7+7/p)/2}.
\tag{32.3}
$$

On the same fixed safe strip $(-L,L)$, $L=\ell/s$, the bound is uniform for the finite Taylor remainder at interpolation parameters $0\le\vartheta\le s$, $1\le t\le T$. Pathwise Taylor expansion through $n$ therefore costs
$Cs^{n+1}\int_1^Tt^{(n+1-7+7/p)/2}dt$.
Integrating this power gives the three alternatives in (32.1).

For completeness retain the exit restriction in (32.2). P (107.5) supplies an extra $e^{-cL^2/t}$ after taking its $\alpha$ power; the remaining height density still has unit integral in the calculation above. Hence the integrated deletion cost for coefficient degree $k$ is at most

$$
C\int_1^Tt^{(k-7+7/p)/2}e^{-cL^2/t}dt
 \le CL^{k-5+7/p}.
\tag{32.4}
$$

The substitution $t=L^2v$ proves this bound. For every retained $k\le n<5-7/p$, its full time tail above $T$ is bounded by $CT^{(k-5+7/p)/2}$. Multiplication by $s^k$ makes both costs $O(s^{5-7/p})$. Original surviving paths leaving the safe strip have comparable covariance by their original denominator margins, so their order-zero deletion has the same estimate. Outside $I_s$, the native field is zero and the retained safe path cannot end; the coefficient deletion bound applies there as well. These controls restore both original faces and the whole output, with the exact $j_0^{-1}$. Only the early integral is compared; no $L^p$ integrability of the full native Coulomb tail is required. $\square$


## 33. The joint fourth-order seed row and its actual consumer

**Definition 33.1 (coefficient rows).** On the fixed seed of Definition 31.1 define

$$
\mathcal N_mg_0=\sum_{k+j=m}\mathcal V_k(G_jg_0),\qquad 0\le m\le4.
\tag{33.1}
$$

Each summand is a pointwise product. This notation gives rows on this input, not bounded coefficient operators on arbitrary $L^2$. On another specified input the same notation is used only if the corresponding return integrals and products exist in the required norms. In particular $\mathcal N_0g_0$ agrees with Definition 29.1's bounded reconstruction adjoint. These rows are not a new scalar coefficient.

**Theorem 33.2 (joint noncompact seed expansion).** Each row in (33.1) belongs to complex $L^2$, and

$$
\left\|\mathcal N_sg_0-\sum_{m=0}^4s^m\mathcal N_mg_0\right\|_2
 \le Cs^{33/8}+Cs^5(1+|\log s|)=o(s^4).
\tag{33.2}
$$

Proof. Multiply (31.4)'s return remainder by $F_s$, whose $L^2$ norm is uniformly bounded. This costs $Cs^5(1+|\log s|)$. For the retained term $s^jG_jg_0$ expand the field only through order $4-j$. Use, in order $j=0,1,2,3,4$, the Hölder pairs

$$
(p_j,q_j)=(8,8/3),\ (4,4),\ (4,4),\ (4,4),\ (2,\infty),
\qquad 1/p_j+1/q_j=1/2.
\tag{33.3}
$$

The zeroth return is $p/(\gamma\mu)\in L^{8/3}$ by (31.2) and the mode decay; the other four return norms are Theorem 31.2. Each retained field coefficient is in the corresponding $L^{p_j}$ by (32.3), because its degree is at most $4-j<5-7/p_j$. Thus all coefficient products are in $L^2$. Lemma 32.1 gives the field remainders at these five degrees and exponents as

$$
O(s^{33/8}),\quad O(s^{13/4}),\quad O(s^3),\quad O(s^2),\quad O(s).
\tag{33.4}
$$

After multiplication by $s^j$, their powers are $33/8,17/4,5,5,5$. Hölder and the finite sum prove (33.2). The proof expands the ordered joint product; it requires no separate $L^2$ Taylor expansions of $\mathcal V_2,\mathcal V_3,\mathcal V_4$ or of the higher return coefficients. $\square$

**Corollary 33.3 (the live row in the actual equation).** Fix any sequence $s\downarrow0$ along which $\epsilon_c(s)=o(s^4)$. For every choice of actual normalized complex ground states $\psi_s\in D(S)$, put $f_s=\mathcal T_s\mathcal U_s\psi_s$, extended by zero. Uniformly over these choices,

$$
\begin{aligned}
\langle(I-\gamma\mathcal N_s)g_0,f_s\rangle&=o(s^4),\\
\left\langle\left(I-\gamma\sum_{m=0}^4s^m\mathcal N_m\right)g_0,f_s\right\rangle&=o(s^4),\\
\sum_{m=1}^4s^m\langle\mathcal N_mg_0,f_s\rangle&=o(s^4).
\end{aligned}
\tag{33.5}
$$

In particular the premise holds in Theorem 27.1's conditional zero-response, $C_4\ge0$ branch. Neither that branch nor zero-response occurrence is inferred from (33.5).

Proof. P (105.2), conjugated by the exact shear, is the original-domain equation

$$
f_s=\gamma\mathcal B_s(h_s)f_s,\qquad
\|f_s\|_2=1,\qquad h_s=-\epsilon_c(s)/a>0.
\tag{33.6}
$$

The bounded adjoint pairing at each $h_s>0$ gives
$\langle(I-\gamma\mathcal B_s(h_s)^*)g_0,f_s\rangle=0$.
It does not require $g_0$ to belong to a native form domain. By the stated premise $h_s=o(s^4)$; P (100.3) gives $r_s\ge c$. Theorem 29.2 therefore permits replacing the adjoint by $\mathcal N_s$ with error $O(h_s+s^5)=o(s^4)$. Theorem 33.2 and unit norm permit the fourth-order polynomial replacement. Finally $\gamma\mathcal N_0g_0=g_0$ cancels order zero, proving all three identities. Both moving faces, the full actual complement and every complex phase remain in the equation. No divergence of $r_s$ is assumed, so bounded-$r_s$ sequences satisfying the premise are included. The last sentence follows from (27.1) and (1.7). $\square$


## 34. The first still-unproved correction-row bridge

**Proposition 34.1 (the particular first Fredholm correction).** Let $A=I-\gamma\mathcal N_0$. There is a unique $g_1\in L^2$ satisfying

$$
Ag_1=\gamma\mathcal N_1g_0,\qquad \langle p,g_1\rangle=0.
\tag{34.1}
$$

It is real and odd under $\sigma$. This assertion supplies no weighted tail estimate for $g_1$.

Proof. P §§87–88 factor $K_{\rm rec}=TM$ and $K_0=MT$, with compact $T$ and bounded $M=V^{1/2}$. The nonzero spectral correspondence of these products and the simple top eigenvalue of the selfadjoint $K_0$ give
$\ker A=\mathbb Cg_0$ and $\ker A^*=\mathbb Cp$.
One can also check the second equality directly from $K_{\rm rec}p=\gamma^{-1}p$ and P (88.2), then use the Fredholm index zero of identity minus compact. The nonzero pairing $\langle p,g_0\rangle=1$ fixes the kernel ambiguity. The coefficient kernels satisfy reflection parity $j$ in (30.1); the field coefficients have parity $k$ by (23.1). Thus $\mathcal N_1g_0$ is real odd, in $L^2$ by Theorem 33.2, and orthogonal to the even $p$. The Fredholm alternative therefore gives a solution, and subtraction of its $g_0$ coordinate enforces (34.1)'s normalization. Reflection and conjugation preserve this equation and normalization, so uniqueness gives oddness and reality. These are properties of this fixed correction, not of actual states. This is the classical compact Fredholm alternative applied to the specified bounded reconstruction, not inversion of $\mathcal E$ on arbitrary $L^2$. $\square$

**Definition 34.2 (the unproved particular-input estimates).** The next needed row estimates on an actual sequence as in Corollary 33.3 are

$$
\begin{aligned}
s\left\|\mathcal N_sg_1-\sum_{j=0}^3s^j\mathcal N_jg_1\right\|_2&=o(s^4),\\
s\|(\mathcal B_s(h_s)^*-\mathcal N_s)g_1\|_2&=o(s^4),
\end{aligned}
\tag{34.2}
$$

including existence of the coefficient rows in the first line. They are not consequences established by Proposition 34.1. To specify the first missing joint integral, let $q_\vartheta^L$ denote the auxiliary killed, combined shifted Gaussian kernel on the fixed safe strip $(-L,L)$, with original endpoint measure. Its Taylor remainder of order three contributes

$$
sF_s(\xi)\int_0^T\!\int
 \left[\frac{s^4}{3!}\int_0^1(1-v)^3
  \left.\partial_\vartheta^4q_\vartheta^L(t;\eta,\xi)
          \right|_{\vartheta=vs}dv\right]g_1(\eta)d\eta\,dt
\tag{34.3}
$$

in full $L^2(d\xi)$. The prefactor is $s^5$, but the endpoint/time integral still requires a quantitative bound. The deleted-path contribution with $|\eta_r|>\ell/(4s)$ and the late return $t\ge s^{-2}$ must also be controlled. These terms retain the original two-face kernel in the comparison; the auxiliary strip estimates it and does not replace it.

For example, the fourth-derivative large-time portion of the seed argument would be integrable for this particular correction under the sufficient input conditions

$$
g_1,rg_1\in L^1,\qquad r^2g_1\in L^{7/6},\qquad
r^3g_1\in L^{7/5},\qquad r^4g_1\in L^{7/4},
\tag{34.4}
$$

together with the corresponding small-time and source-tail bounds. The time powers for relative degrees $4,3,2,1,0$ would then be $-3/2,-2,-2,-2,-2$. Proposition 34.1 does not prove these memberships or tail bounds. Conditions (34.4) are sufficient for that portion of this method, not necessary conditions for (34.2), for a different proof, or for the original actual-selection target.

P (104.9) gives only

$$
s\|(\mathcal N_s-\mathcal N_0)g_1\|_2
 \le s d_s\|g_1\|_2=o(s),\qquad d_s\to0,
\tag{34.5}
$$

without a polynomial rate. For the late difference, (29.3) on the dense class $L^1\cap L^2$, $h_s\to0$, and the uniform operator bounds from P (104.2) at $r_s\ge c$ give strong convergence on each fixed $L^2$ input. Its correction factor again supplies only $o(s)$. Neither observation reaches (34.2); neither is a lower bound proving that (34.2) fails.

The remaining finite corrected row would additionally require the actually consumed estimates for $g_2$ through order two, $g_3$ through order one and the final correcting row through order zero. No such chain is constructed here. Its fourth scalar has not been identified with the sole owned quartic scalar $C_4=D_4-h[\Upsilon]$ of (24.5), including the field-clock products and threshold term. Accordingly (33.5) gives no conclusion $cC_4=0$ at a microscopic weak limit $cp$.


## 35. Attribution and mathematical scope of the seed identity

**Definition 35.1 (source attribution and unresolved target).** Theorems 29.2, 31.2 and 33.2, Lemmas 30.2 and 32.1, and Corollary 33.3 are `repo-derived` conditional consequences for the one original datum. Their analytic suppliers are P §76's both-face all-height heat, P §§87–88's specified compact reconstruction and simple mode, P §97's exact shear and common conditional Gaussian, P §104's native time split and multiplier/column bounds, P §105's actual original-domain equation, and P §107's bridge moments. R (8.3) owns the left coordinate, and Entire-height response escape Theorem 3.1 supplies the full homogeneous mode decay used in (31.2). The coefficient fields and clock products are reused exactly from (23.1), and the previously obtained fourth-order spectral law remains Theorem 27.1. These are ordinary conditional antecedents at their stated scopes.

The intermediate methods are classical Gaussian matrix differentiation, finite Taylor expansion, Brownian bridge reflection and scaling, Minkowski, Hölder, interpolation, Young convolution and the compact Fredholm alternative. The convolution norm step is the Fischer–Ruzhansky formula cited in Lemma 30.2; the Engel group, Haar measure and ordered convolution also coincide with Bahouri–Barilari–Gallagher–Léautaud, [arXiv:2206.10396v1, (3.6)–(3.13)](https://arxiv.org/pdf/2206.10396v1), as in R Definition 23.1. The global native face/input/time estimates are the proofs above, not an application of a local compact positive-time heat expansion beyond its quantifiers. This attribution asserts no literature-wide priority.

The new conclusion is the live actual-equation seed identity (33.5) under its explicit $\epsilon_c=o(s^4)$ premise. It gives no absolute response or quartic sign, zero-response occurrence, corrected fourth-scalar identification or $cC_4=0$. The particular correction estimates (34.2) are still unproved. Missing proof is neither an actual-state counterexample nor a theorem that this route or another actual-state argument is impossible. The original every-actual-choice goal of Definition 9.1 remains unresolved, including nonnegative-quartic finer scale and response-zero mixed selection. The prior negative-response, positive-response and negative-quartic conclusions retain precisely their original hypotheses.

All constants fix the same admitted signed nonzero $\kappa$, original rational vector, denominator margin, source, interval, $a,\varepsilon$ and $j_0$ before $s\downarrow0$; no parameter-uniform statement through a denominator pole is made. Both moving Dirichlet faces, every real phase and the entire complex horizontal domains (1.5) remain in the actual equation. The original microscopic unitary has Jacobian $j_0s^7$, the shear has determinant one and fixes the source, and the field clock is $B$, independently of kinetic $a$. No actual-state parity, positive $L^2$ complement gap, arbitrary $L^2$ zero-energy inverse, uncut native response, assumed $r_s$ growth, norm-to-energy inference or trial-to-actual substitution enters. No analytic preparation or physical-space/dimension conclusion follows.

## 追加锚（本行以下为增补区）


## 36. The first return coefficient and both time boundaries

**Definition 36.1 (particular-input hypotheses and notation).** Fix exactly Definition 29.1's original admitted datum and conditional analytic antecedents. Retain the common complex space, restrictions and zero extensions, operators, coefficients and normalization of (29.1), (30.1), (31.1), (31.2) and (33.1). Thus $G_0$ denotes the specified heat reconstruction only where justified. Here $g_1$ always means Proposition 34.1's normalized correction, not R (16.5)'s different forcing. Write $\mathcal E=-X^2-Y^2$, $P_t=e^{-t\mathcal E}$ and $\mathcal G=\int_0^\infty k_t\,dt$ for the canonical heat and its specified fundamental solution. Convolution has exactly (2.6)'s order and unit Lebesgue Haar measure. Put

$$
\begin{aligned}
D_1&=2\nu Y(rY)=2\nu rY^2,&v&=\nu\Psi,&F&=rYp,\\
W&=-2\nu F*(Y^{\rm R}\mathcal G),&
q&=\mathcal V_1p+Vv,&Y^{\rm R}&=\partial_y.
\end{aligned}
\tag{36.1}
$$

The particular $\Psi$ is R Theorem 16.2's canonical form/$L^2$ representative. The symbol $v$ here means $\nu\Psi$, rather than R (16.7)'s residual. The multiplier $\mathcal V_1=\nu V_1$ is unchanged from (23.1). Inner products are conjugate linear in their first slot.

**Theorem 36.2 (coefficient heat equation and specified reconstruction).** For the fixed $g_0$,

$$
\begin{gathered}
(\partial_t+\mathcal E)\mathsf Q_1(t)g_0=-D_1P_tg_0
\quad\text{in distributions for }t>0,\\
\lim_{t\downarrow0}\|\mathsf Q_1(t)g_0\|_2
=\lim_{t\to\infty}\|\mathsf Q_1(t)g_0\|_2=0,\qquad
\int_0^\infty\|\mathsf Q_1(t)g_0\|_2dt<\infty,\\
\mathcal E G_1g_0=-D_1p/(\gamma\mu),\qquad
\gamma\mu G_1g_0=W.
\end{gathered}
\tag{36.2}
$$

Proof. On a fixed finite slab $(-L,L)$ define, only for $|\nu\vartheta|L<1/4$,

$$
\mathcal E_\vartheta^L=-X^2-(1+\nu\vartheta r)^{-2}Y^2
\tag{36.3}
$$

with both slab endpoints Dirichlet. First restrict phase Fourier frequencies to a fixed bounded set. On this set its potential and parameter derivative are bounded multipliers on the finite height interval, on a common height Dirichlet operator domain. Integrating the two heat equations gives the classical bounded-perturbation variation-of-constants identity. Its derivative at zero is therefore

$$
\begin{gathered}
(\partial_t+\mathcal E^L)\mathsf Q_1^L(t)=-D_1P_t^L,\qquad
\mathsf Q_1^L(0)=0,\\
\mathsf Q_1^L(t)u=-\int_0^tP_{t-b}^LD_1P_b^Lu\,db .
\end{gathered}
\tag{36.4}
$$

Finite differentiation of the conditional Gaussian on this safe slab gives precisely (30.1)'s first coefficient with the slab-survival indicator. The derivative of $e^{\lambda\vartheta^2t}$ at zero vanishes. Thus (36.4) has exactly the asserted coefficient, sign and absence of an order-one clock term; no rational family through a pole has been defined.

Lemma 30.2's absolute kernel calculation applies with the survival indicator and gives, uniformly in slab size,

$$
\|\mathsf Q_1^L(t)g\|_2+\|\mathsf Q_1(t)g\|_2
\le C(\|rg\|_2+\sqrt t\,\|g\|_2).
\tag{36.5}
$$

For fixed $t$, $\mathsf Q_1^L(t)g\to\mathsf Q_1(t)g$ in $L^2$ when $g,rg\in L^2$. Indeed restrict input first to $|r|\le L/4$. An omitted path has relative height supremum at least $3L/4$. Integrate the inflated Gaussian over every phase and then the height endpoint. Brownian reflection bounds its relative-kernel $L^1$ norm by $Ct^{m/2}e^{-cL^2/t}$ for degrees $m=0,1$, after changing the exponential constant. Ordered Young controls these terms against the corresponding input norms. The remaining input is controlled by (36.5) and its weighted $L^2$ tail tends to zero. The order-zero argument also gives $P_t^Lg\to P_tg$. Compact testing now passes (36.4) to the first equation of (36.2). Phase Fourier cutoff and density remove the preliminary bounded-frequency restriction, since $\mathcal E\varphi,D_1\varphi\in L^2$ for compact smooth $\varphi$. These are the global two-endpoint bounds of Lemma 30.2 and P (107.5).

The initial boundary requires cancellation. Approximate $g_0$ in $\|g\|_2+\|rg\|_2$ by functions $u$ with compact height support and bounded phase Fourier support. For these functions

$$
\sup_L\sup_{0\le b\le1}\|D_1P_b^Lu\|_2\le C_u.
\tag{36.6}
$$

On the bounded frequency set the multiplier of $D_1$ has absolute value at most $C(1+|r|^5)$. The nonnegative Fourier potential dominates the absolute killed height heat by the free one-dimensional heat applied to $|\widehat u|$. Gaussian moment integration, or weighted $L^2$ convolution followed by the Gaussian moments, bounds all height moments through order five for $b\le1$, independently of the slab. Compact initial height support and integration over the bounded frequency set give (36.6). Contraction in (36.4) yields $\|\mathsf Q_1^L(t)u\|_2\le C_ut$. Pass $L\to\infty$ and then approximate $g_0$ using (36.5). This proves $\mathsf Q_1(t)g_0\to0$ in $L^2$ at time zero, which does not follow from a size estimate alone.

For $t\ge1$, Lemma 30.2 gives

$$
\|\mathsf Q_1(t)g_0\|_2
\le C(t^{-5/4}\|g_0\|_1+t^{-7/4}\|rg_0\|_1).
\tag{36.7}
$$

The inputs are integrable by (31.2)–(31.3); both powers are integrable and tend to zero. Together with (36.5) this proves absolute $L^2$ convergence of $G_1g_0$ and the terminal boundary. Likewise $\int_0^\infty P_tg_0dt$ converges absolutely in $L^2$, by contraction below one and $Ct^{-7/4}\|g_0\|_1$ above one, and equals the owned $p/(\gamma\mu)$ in (31.2).

Integrate the tested coefficient equation from $\delta$ to $M$, and pass $\delta\downarrow0$, $M\to\infty$ using both boundaries. This gives $\mathcal E G_1g_0=-D_1p/(\gamma\mu)$. The ordered convolution and noncompact input-cutoff argument in R (16.4)–(16.9) give $W\in L^2$ and

$$
\mathcal EW=-2\nu Y(rYp)=-D_1p .
\tag{36.8}
$$

No factors of convolution are exchanged. The $L^2$ difference $d=\gamma\mu G_1g_0-W$ is distributionally $\mathcal E$-harmonic and is smooth by inherited canonical hypoellipticity. Take real smooth compact dilated cutoffs $\eta_R$, equal to one on an exhausting neighborhood, with $|\nabla_H\eta_R|\le C/R$. Testing against $\eta_R^2d$ and taking real parts gives, by the product rule,

$$
b[\eta_Rd]=\int|\nabla_H\eta_R|^2|d|^2
\le CR^{-2}\|d\|_2^2.
\tag{36.9}
$$

Every fixed compact set consequently has zero horizontal derivative as $R\to\infty$. Bracket generation makes $d$ constant and infinite Haar volume makes that $L^2$ constant zero. This proves (36.2) without an arbitrary zero-energy inverse, a maximal-domain theorem or $\Psi\in D(\mathcal E)$. The cutoff energy argument is a classical intermediate uniqueness tool within this particular reconstruction. $\square$


## 37. Identification of the owned normalized particular correction

**Theorem 37.1 (the source-forced first charge).** The unique correction of Proposition 34.1 is exactly

$$
g_1=\frac{\mathcal V_1p+Vv}{\mu}
=\frac{\mathcal V_1p+\nu V\Psi}{\mu},
\qquad Ag_1=\gamma\mathcal N_1g_0,\qquad
\langle p,g_1\rangle=0.
\tag{37.1}
$$

Proof. The specified reconstruction in R Theorem 16.2 gives

$$
v=W+\gamma G_0q,\qquad q=\mathcal V_1p+Vv.
\tag{37.2}
$$

This right side is an admitted multiplier source:

$$
q/\sqrt V=(\mathcal V_1/\sqrt V)p+\sqrt Vv\in L^2
\tag{37.3}
$$

by R Theorem 4.1, bounded $V$ and the owned $v\in L^2$. Thus $G_0q$ is precisely P Theorem 87.2's reconstruction with multiplication by $\sqrt V$; no inverse on arbitrary $L^2$ is used. Also $q\in L^2$. Since $p,V$ are even under $\sigma$ and $\mathcal V_1,v$ are odd, $\langle p,q/\mu\rangle=0$. Theorems 36.2 and (31.2) give

$$
\begin{aligned}
A(q/\mu)
&=(\mathcal V_1p+V(v-\gamma G_0q))/\mu\\
&=(\mathcal V_1p+VW)/\mu\\
&=\gamma(\mathcal V_1G_0g_0+VG_1g_0)
=\gamma\mathcal N_1g_0.
\end{aligned}
\tag{37.4}
$$

The already owned normalized Fredholm uniqueness of Proposition 34.1 now identifies $q/\mu=g_1$. Fixed canonical parity is used only to normalize this correction, never to restrict any actual state. The classical compact Fredholm alternative retains its stated reconstruction scope. $\square$


## 38. Full-spatial first-field control and consumed products

**Theorem 38.1 (particular height weights).** Put $\omega(r)=1+|r|$. With all phases integrated on the full group,

$$
\begin{gathered}
V_1\in L^2,\qquad \omega g_1\in L^1,\qquad \omega^5g_1\in L^2,\\
g_1,rg_1\in L^1,\qquad
r^2g_1\in L^{7/6},\quad r^3g_1\in L^{7/5},
\quad r^4g_1\in L^{7/4},\\
\|\mathbf1_{|r|>L}r^ng_1\|_2=o(L^{n-5})
\quad(0\le n\le5).
\end{gathered}
\tag{38.1}
$$

Proof. For the unscaled first source Gaussian coefficient $p_1(t)$ of (3.2), the majorants of Lemma 30.2 give

$$
\|p_1(t)\|_1\le C\sqrt t,\qquad
\|p_1(t)\|_\infty\le Ct^{-3},\qquad
\|p_1(t)\|_2\le Ct^{-5/4}.
\tag{38.2}
$$

For the first inequality integrate its inflated Gaussian over every phase and then the height endpoint, leaving the first Brownian-supremum moment. The second is the coefficient supremum P (107.8). The third is $\|u\|_2^2\le\|u\|_1\|u\|_\infty$. Integrating this strictly integrable $L^2$ bound on $[1,\infty)$ with the original $j_0^{-1}$ proves $V_1\in L^2$. A height supremum has not been substituted for full-spatial integrability.

The owned bounds imply $\omega V\in L^2$, $\omega^5V\in L^\infty$, and $|\mathcal V_1|\le C\omega^{-4}$. For the first, $V\le C(1+\mathfrak d)^{-5}$ and $|r|\le C\mathfrak d$ give $\omega V\le C(1+\mathfrak d)^{-4}$, square integrable in homogeneous dimension seven. The other two are the height estimates of R (2.7) and R (3.4)/P (107.4), respectively. The mode supplies $\omega p\in L^2$ and the particular response supplies $v\in L^2$. Applying Hölder to (37.1) gives

$$
\begin{aligned}
\|\omega Vv\|_1&\le\|\omega V\|_2\|v\|_2,&
\|\omega\mathcal V_1p\|_1&\le\|\mathcal V_1\|_2\|\omega p\|_2,\\
\|\omega^5Vv\|_2&\le C\|v\|_2,&
\|\omega^5\mathcal V_1p\|_2&\le C\|\omega p\|_2.
\end{aligned}
\tag{38.3}
$$

Thus both asserted weighted norms hold without a weighted $\Psi$ norm or pointwise response decay.

For $0\le\theta\le1$, Hölder gives $\omega^{1+4\theta}g_1\in L^{p_\theta}$, $1/p_\theta=1-\theta/2$, by factoring its absolute value as $|\omega g_1|^{1-\theta}|\omega^5g_1|^\theta$. Taking $\theta=2/7,4/7,6/7$ gives

$$
(p_\theta,1+4\theta)
=(7/6,15/7),\quad(7/5,23/7),\quad(7/4,31/7).
\tag{38.4}
$$

The weights exceed $2,3,4$, proving the consumed memberships. Finally,

$$
\|\mathbf1_{|r|>L}r^ng_1\|_2
\le CL^{n-5}\|\mathbf1_{|r|>L}\omega^5g_1\|_2
=o(L^{n-5})
\tag{38.5}
$$

for $L\ge1$ and $0\le n\le5$. Absolute continuity of the $L^2$ integral proves the little-o, including every weighted $L^2$ input through order five. Hölder and interpolation are classical intermediate inequalities; this is a particular-charge estimate, not a universal weighted response theorem. $\square$

**Theorem 38.2 (every consumed coefficient product).** For $0\le j\le3$, $G_jg_1$ converges absolutely in $L^4$. Each product $\mathcal V_k(G_jg_1)$ with $k+j\le3$ is $L^2$, so

$$
\mathcal N_jg_1=\sum_{k+b=j}\mathcal V_k(G_bg_1)\in L^2
\qquad(0\le j\le3).
\tag{38.6}
$$

Proof. In the ordered decomposition (30.3) put $n=j-m$. On $0<t<1$ use the weighted $L^2$ inputs of Theorem 38.1 and kernel $L^{4/3}$ to obtain the integrable output-$L^4$ powers $t^{m/2-7/8}$. On $t\ge1$ use input exponents

$$
p_0=p_1=1,\qquad p_2=7/6,\qquad p_3=7/5.
\tag{38.7}
$$

The time power is $m/2-(7/2)(1/p_n-1/4)$. Its largest value for $n=0,j\le3$ is $-9/8$; for $n\ge1$ it is at most $-13/8$. Hence all integrals converge absolutely in $L^4$. The coefficient bound of Lemma 32.1 gives $\mathcal V_k\in L^4$ for $k\le3$, since $k<5-7/4=13/4$. Hölder gives every asserted product. Young here is the classical ordered group inequality cited in Lemma 30.2, on the same Haar measure, with no additional $j_0$ in a return. No bounded coefficient operator on arbitrary $L^2$ is asserted. $\square$


## 39. The complete early native remainder on the particular charge

**Theorem 39.1 (full-output third-order first-correction row).** For fixed sufficiently small $\ell>0$ there is $\varepsilon_1(L)\to0$ such that

$$
\left\|\mathcal N_sg_1-\sum_{j=0}^3s^j\mathcal N_jg_1\right\|_2
\le Cs^3\varepsilon_1(\ell/s)+C(s^{13/4}+s^4+s^5).
\tag{39.1}
$$

Consequently the first line of (34.2) holds:

$$
s\left\|\mathcal N_sg_1-\sum_{j=0}^3s^j\mathcal N_jg_1\right\|_2=o(s^4).
\tag{39.2}
$$

Proof. Set $L=\ell/s$, $T=s^{-2}$, choosing $\ell$ so $(-L,L)\Subset I_s$ and $\nu\ell<1/4$. Retain the original killed heat, adding killing at the two safe faces only for estimation. Along safe paths every interpolation covariance for $0\le\vartheta\le s$ is comparable to the canonical covariance. Finite Gaussian differentiation through order four has the inflated-Gaussian bounds of Lemma 30.2, with input degree $n$, relative degree $m$ and $n+m=4$. Derivatives of $e^{\lambda\vartheta^2t}$ are bounded by $Ct^{k/2}$ at order $k$ on $t\le T$, since $\vartheta\sqrt t\le1$. Their time powers contribute the corresponding relative degree, so the clock products are included. This is finite safe-path Taylor expansion, not a global rational family through a pole.

On $0<t<1$ use $F_s\in L^\infty$, return output $L^2$, weighted inputs $r^ng_1\in L^2$ and kernel $L^1$. The time powers $t^{m/2}$ are integrable. On $1<t<T$ use $F_s\in L^2$ and return output $L^\infty$, with the five input/relative degrees and input exponents

$$
(n,m,p)=(0,4,1),(1,3,1),(2,2,7/6),(3,1,7/5),(4,0,7/4).
\tag{39.3}
$$

Their powers $m/2-7/(2p)$ are respectively $-3/2,-2,-2,-2,-2$. Thus Taylor's integral fourth derivative, before the exterior correction factor $s$ in (34.3), costs $Cs^4$ in the final product $L^2$ norm. No boundedness of $g_1$ at time zero is needed.

For noncompact input split at $|r|=L/4$ and put

$$
\varepsilon_1(L)=\|\mathbf1_{|r|>L/4}\omega^5g_1\|_2\longrightarrow0.
\tag{39.4}
$$

The original shifted heat is an $L^2$ contraction because $C_s\ge0$. The extra-killed heat is also a contraction because its form is a Dirichlet restriction of that form. Their outer-input returns have norms at most

$$
T\|\mathbf1_{|r|>L/4}g_1\|_2
\le CL^{-3}\varepsilon_1(L).
\tag{39.5}
$$

Bounded $F_s$ therefore gives $Cs^3\varepsilon_1(L)$. For each retained coefficient with $n+m=j\le3$, its outer-input return on $(0,T)$ has $L^2$ bound

$$
CT^{1+m/2}\|\mathbf1_{|r|>L/4}r^ng_1\|_2.
\tag{39.6}
$$

Multiply by $s^j$ and use (38.5) to obtain the same $Cs^3\varepsilon_1(L)$ bound. This includes input outside $\Omega_s$, discarded by native restriction. Hence no compact-support assumption is made on $g_1$.

For inner input $|\eta_r|\le L/4$, an original surviving path missing from the safe-strip kernel must leave a safe face and has relative height supremum at least $3L/4$. For output height beyond $L/2$ the relative displacement is at least $L/4$, giving the corresponding endpoint estimate directly. The full-output argument of (31.6) and P (107.5) give the absolute kernel bound

$$
Ct^{-7/2}e^{-cL^2/t}.
\tag{39.7}
$$

Original surviving covariances stay comparable to the canonical covariance even outside the auxiliary strip, by the fixed original denominator margins on $\overline I$. Integrate (39.7) on $(0,T)$ against $\|g_1\|_1$, then multiply by $\|F_s\|_2$. The cost is $CL^{-5}=Cs^5$, with every output phase included. Beyond either original face the native kernel is zero and the safe path cannot end; the omitted coefficient-path estimates below give exactly the required zero-extension comparison.

Restore omitted coefficient paths for inner input. For $n+m=j\le3$, their integrated return supremum is at most $CL^{m-5}M_n(L)$, where

$$
M_n(L)=\int_{|r|\le L/4}|r|^n|g_1|
\le
\begin{cases}
\|g_1\|_1,&n=0,\\
CL^{n-1}\|rg_1\|_1,&n\ge1.
\end{cases}
\tag{39.8}
$$

To obtain the bound use the relative-moment version of (39.7) and integrate $t^{(m-7)/2}e^{-cL^2/t}$ on $(0,\infty)$. Since $m\le3$ it converges, and $t=L^2b$ gives $L^{m-5}$. The estimate retains the same relative bridge exit event and inverse-determinant moments and covers complete output. After $s^j$ these costs are $O(s^5)$ for $n=0$ and $O(s^6)$ otherwise. Multiplication by $\|F_s\|_2$ preserves them.

Finally restore every coefficient time tail $t>T$ on the full input. Use (38.7) and return output $L^\infty$. For $n=0$ the power is $(j-7)/2$, whose tail after $s^j$ is $O(s^5)$. For $n\ge1$ the power is $(j-8)/2$, whose corresponding tail is $O(s^6)$. All are integrable for $j\le3$. Multiplication by $\|F_s\|_2$ is legitimate, so no infinite-time coefficient boundary is omitted.

Combining the safe Taylor remainder, outer input, original-path exits, coefficient-path exits and time tails gives

$$
\left\|F_s\left(H_sg_1-\sum_{j=0}^3s^jG_jg_1\right)\right\|_2
\le Cs^3\varepsilon_1(L)+C(s^4+s^5).
\tag{39.9}
$$

This is a joint-product estimate; it asserts no separate $L^2$ expansion of the unmultiplied return. For each retained $s^jG_jg_1$, Theorem 38.2 gives $L^4$. Expand its field through degree $3-j$. Lemma 32.1 at exponent four gives, for $j=0,1,2,3$, field remainder powers

$$
s^{13/4},\quad s^3,\quad s^2,\quad s.
\tag{39.10}
$$

The factors $s^j$ make these $s^{13/4},s^4,s^4,s^4$. Hölder and (39.9) prove (39.1), including all field-return cross terms and original clock coefficients. Multiplying by $s$ proves (39.2): $\varepsilon_1(\ell/s)\to0$ and $17/4>4$. Both original deaths have only been estimated by auxiliary killing. Taylor, Brownian reflection, ordered Young and Hölder are the classical intermediate tools attributed in §§30–35; the complete native first-charge accounting is the deduction here. $\square$


## 40. Actual-height late control and the exact corrected actual equation

**Theorem 40.1 (late first-correction remainder).** On every actual sequence of Corollary 33.3, including bounded-$r_s$ sequences,

$$
s\|(\mathcal B_s(h_s)^*-\mathcal N_s)g_1\|_2=o(s^4).
\tag{40.1}
$$

Together with Theorems 38.2 and 39.1 this establishes both estimates and coefficient existence in (34.2). It supersedes exactly the first-$g_1$ unproved boundary of Definition 34.2 and its corresponding assertion in Definition 35.1.

Proof. Theorem 38.1 puts this fixed $g_1$ in $L^1\cap L^2$. Apply the owned fixed-input bound (29.3):

$$
\|(\mathcal B_s(h)^*-\mathcal N_s)g_1\|_2
\le C\left[(h+s^5)(\|g_1\|_1+\|g_1\|_2)
+s^7h^{-1/4}\|g_1\|_1\right].
\tag{40.2}
$$

This bound uses the original two-face heat, short field and complete long field; no long Coulomb multiplier is assigned an $L^2$ norm. At the actual $h_s=r_ss^8/a$, P (100.3)'s $r_s\ge c>0$ gives $s^7h_s^{-1/4}=a^{1/4}s^5r_s^{-1/4}\le Cs^5$. Since $\epsilon_c(s)=o(s^4)$ gives $h_s=o(s^4)$, the norm is $O_{g_1}(h_s+s^5)$ and its exterior factor $s$ proves (40.1). No divergence of $r_s$ is assumed. $\square$

**Theorem 40.2 (exact actual equation retaining the full complement).** On each prescribed sequence $s\downarrow0$ with actual $\epsilon_c(s)=o(s^4)$, take every actual normalized complex ground-state choice and let $f_s=\mathcal T_s\mathcal U_s\psi_s$. Define the justified $L^2$ vectors

$$
\begin{aligned}
R_m&=\mathcal N_mg_0+\mathcal N_{m-1}g_1\qquad(m=2,3,4),\\
\delta_{0,s}&=\mathcal B_s(h_s)^*g_0-\sum_{m=0}^4s^m\mathcal N_mg_0,\\
\delta_{1,s}&=\mathcal B_s(h_s)^*g_1-\sum_{j=0}^3s^j\mathcal N_jg_1.
\end{aligned}
\tag{40.3}
$$

Then $\|\delta_{0,s}\|_2+s\|\delta_{1,s}\|_2=o(s^4)$ and, exactly,

$$
\begin{aligned}
0&=\langle(I-\gamma\mathcal B_s(h_s)^*)(g_0+sg_1),f_s\rangle\\
&=-\gamma\sum_{m=2}^4s^m\langle R_m,f_s\rangle
-\gamma\langle\delta_{0,s}+s\delta_{1,s},f_s\rangle.
\end{aligned}
\tag{40.4}
$$

In particular, with $\alpha_s=\langle g_0,f_s\rangle$, $z_s=f_s-\alpha_sp$,

$$
\begin{gathered}
\langle g_0,z_s\rangle=0,\\
\sum_{m=2}^4s^m
\left[\alpha_s\langle R_m,p\rangle+\langle R_m,z_s\rangle\right]
=-\langle\delta_{0,s}+s\delta_{1,s},f_s\rangle=o(s^4).
\end{gathered}
\tag{40.5}
$$

The remainder is uniform over actual normalized choices along each such fixed-datum sequence.

Proof. Theorem 33.2 and the actual-height application of Theorem 29.2 give $\|\delta_{0,s}\|_2=o(s^4)$, as in Corollary 33.3. Theorems 39.1 and 40.1 give $s\|\delta_{1,s}\|_2=o(s^4)$. Every $R_m$ is $L^2$ by Theorems 33.2 and 38.2.

The original actual equation is precisely (33.6): $f_s=\gamma\mathcal B_s(h_s)f_s$, $\|f_s\|_2=1$, on the transported original operator domain. At $h_s>0$ it is a bounded-operator equation. Pairing against the fixed $L^2$ vector $g_0+sg_1$ therefore needs no native form-domain membership of the test. Substituting (40.3) gives

$$
\begin{aligned}
(I-\gamma\mathcal B_s(h_s)^*)(g_0+sg_1)
&=Ag_0+s(Ag_1-\gamma\mathcal N_1g_0)\\
&\quad-\gamma\sum_{m=2}^4s^m(\mathcal N_mg_0+\mathcal N_{m-1}g_1)
-\gamma(\delta_{0,s}+s\delta_{1,s}).
\end{aligned}
\tag{40.6}
$$

The first two terms vanish by (31.2) and (37.1), canceling precisely orders zero and one. This proves (40.4). Since $\langle g_0,p\rangle=1$, substitution of $f_s=\alpha_sp+z_s$ gives (40.5), retaining every complement pairing. Unit norm bounds the remainder by its $L^2$ norm independently of the actual choice.

The second-, third- and fourth-order rows have not been canceled. No vanishing, parity, reality, positive $L^2$ gap or polynomial rate of $z_s$ is used. No scalar is identified with, substituted for or used to redefine (24.5)'s $C_4=D_4-h[\Upsilon]$. In particular this identity gives no conclusion $cC_4=0$. The adjoint pairing is the classical Hilbert-space identity, applied here to the exact original actual equation, never a trial state. $\square$


## 41. Attribution and remaining original mathematical obligations

**Definition 41.1 (mathematical attribution).** Theorems 36.2–40.2 are conditional repository-derived deductions for the one fixed original datum. The reconstruction, simple mode and particular response remain owned by P §§87–88, R §§4, 5 and 16, and Entire-height response escape Theorem 3.1. The coefficient calculus, field estimates, seed row and fixed-input actual-height bound are exactly §§29–33; normalized Fredholm uniqueness remains Proposition 34.1. The additional conclusions are the first coefficient heat dictionary and its two time boundaries, normalized particular identification, consumed weights and products, both native first-correction remainders and the exact actual-equation consumer.

The ordered derivative transfer in (36.8) and (37.2) is R (16.4)–(16.12), corresponding to Bahouri–Barilari–Gallagher–Léautaud, *Spectral summability for the quartic oscillator with applications to the Engel group*, [arXiv:2206.10396v1](https://arxiv.org/pdf/2206.10396v1), (3.6)–(3.13), (3.24)–(3.25) and (5.12). Young is the classical convolution inequality of Fischer–Ruzhansky, *Sobolev spaces on graded groups*, [arXiv:1311.0192v1, §2.1, (2.2)](https://arxiv.org/html/1311.0192v1#S2.SS1), as cited in Lemma 30.2. These tools use exactly the same Engel law, unit Haar measure and homogeneous dimension seven. Bounded finite-time perturbation, cutoff energy uniqueness, Gaussian moments, Hölder, interpolation and the compact Fredholm alternative are intermediate classical tools within the source-specific proofs, not new standalone results. The Colin de Verdière–Hillairet–Trélat local heat theorem keeps P §§104 and 107's compact positive-time/interior-endpoint scope; it supplies no unproved moving-face, time-zero, noncompact or infinite-time estimate. Those are proved here or supplied by §§29–33 at their explicit global scope. The analytic heat, hypoellipticity, reconstruction, mode, domain and attainment antecedents remain conditional. No literature-wide priority or absence claim is made.

**Definition 41.2 (unresolved original selection).** The first-row requirements (34.2) are established by Theorems 38.2, 39.1 and 40.1. Later correction rows for $g_2$ through order two, $g_3$ through order one and the final row through order zero remain unproved here. Their final scalar has not been identified with the unchanged (24.5) $C_4$, including its field-clock and threshold terms. Thus $cC_4=0$, the absolute response and quartic signs, zero-response occurrence, and finer nonnegative-$C_4$ actual scale/profile selection remain unresolved. The original every-actual-choice target of Definition 9.1 is not established; the preceding conditional conclusions retain their precise scope.

Every actual statement retains the same fixed admitted signed nonzero $\kappa$, full jointly realized rational vector, positive denominator margins, both original Dirichlet faces, all real phases, raw unit source and $j_0$ density, original microscopic unitary and determinant-one source-fixing shear, and full complex horizontal form/operator domains (1.5). The $B$ field heat clock is independent of kinetic $a$. No actual-state parity or reality, arbitrary zero-energy $L^2$ inverse, positive $L^2$ complement gap, uncut native response, assumed $r_s$ growth, global family through a denominator pole, norm-to-energy inference or trial-to-actual substitution is introduced. Neither an actual-state counterexample nor analytic preparation, empirical selection or physical-space/dimension conclusion follows.

## 追加锚（本行以下为增补区）


## 42. Higher finite charges at one fixed zero-response datum

**Definition 42.1 (hypotheses, full domains and coefficient notation).** Fix one admitted original datum of Definitions 1.1–2.2 before $s\downarrow0$. Retain every conditional analytic antecedent of Theorem 22.1 and Definitions 29.1 and 36.1. These are the canonical heat, Gaussian and bridge-moment estimates, hypoellipticity and horizontal Sobolev realization, the specified compact reconstruction and simple critical mode, the homogeneous-energy complement gap, the particular first-response representative and its stated derivative tails, and the original native domain, attainment, heat and actual-state reconstruction statements at their owning scopes. In particular the actual weak-disk conclusion, P §§104–105, Theorem 27.1 and Theorem 10.2 retain their original hypotheses. Suppose throughout §§42–50 that this fixed datum satisfies $C_{\rm resp}=0$.

All actual vectors have the entire complex form or operator domains (1.5), transported only by the original $\mathcal U_s$ and determinant-one $\mathcal T_s$. Both original moving Dirichlet faces, every real phase frequency, the signed nonzero $\kappa$ and full jointly realized rational vector (1.2), fixed denominator margins, raw unit source and $j_0$ remain unchanged. The field heat clock is $B$, independently of $a$. Constants may depend on the fixed datum and its antecedent constants; no uniformity for varying data or approaching a pole is asserted.

Use precisely $\mathsf Q_j,G_j,\mathcal V_j,\mathcal N_s,\mathcal B_s(h)$ of §§23 and 29–33, with $\mathcal V_0=V$. Set

$$
\gamma=\chi_c/a,\qquad \mu=\int Vp^2,\qquad
g_0=Vp/\mu,\qquad v=\nu\Psi,\qquad
A=I-\gamma\mathcal N_0,\qquad
\omega=1+|r|,\qquad \mathfrak d=d_E(0,\cdot).
\tag{42.1}
$$

The first charge $g_1$ is exactly (37.1). Inner products are conjugate linear in the first slot. To distinguish differential coefficients from the scalar $D_4$ in (24.5), write

$$
\begin{aligned}
\mathscr D_1&=2\nu rY^2,&
\mathscr D_2&=-3\nu^2r^2Y^2-\lambda,\\
\mathscr D_3&=4\nu^3r^3Y^2,&
\mathscr D_4&=-5\nu^4r^4Y^2.
\end{aligned}
\tag{42.2}
$$

They are the coefficients of
$-X^2-(1+\nu sr)^{-2}Y^2-\lambda s^2$.
Since $Yr=0$, integration by parts on compact tests gives exactly

$$
\mathfrak a_j(f,z)
 =a\langle\mathscr D_jf,z\rangle
   -\chi_c\int\mathcal V_j\bar fz
\tag{42.3}
$$

with the forms (24.1); this notation extends only to pairings justified below. In particular $\mathscr D_2$ includes $-\lambda$. The complete field coefficients retain $\nu^2\lambda V_{2t}$ and $\lambda^2V_{tt}/2$. No scalar is redefined: throughout this append

$$
C_4=D_4-h[\Upsilon]
\tag{42.4}
$$

means exactly (24.5).

**Theorem 42.2 (finite-row actual compatibility and positive-quartic endpoint).** Under Definition 42.1, for every prescribed sequence $s_n\downarrow0$ along which the actual spectral bottom satisfies $\epsilon_c(s_n)=o(s_n^4)$, choose any actual normalized complex ground state $\psi_{s_n}\in D(S)$ at each $s_n$. Every microscopic weak limit

$$
\mathcal U_{s_n}\psi_{s_n}\rightharpoonup cp
\quad\text{satisfies}\quad cC_4=0.
\tag{42.5}
$$

Both premises $C_{\rm resp}=0$ and $\epsilon_c=o(s^4)$ are part of this assertion. If the fixed datum additionally has $C_4>0$, every actual choice has weak microscopic limit zero, and

$$
E_s=\chi_c^2e_Cs^6+o(s^6),\qquad
r_s\longrightarrow-\chi_c^2e_C,\qquad
\operatorname{dist}_{L^2}\!
 \left(\mathcal D_{g_s}\psi_s,\mathbb T\,\phi h_C\right)
 \longrightarrow0 .
\tag{42.6}
$$

The endpoint has full unit mass and the original fixed-cutoff Coulomb normalization of Theorem 10.2. The proof is given in §§43–49, including every consumed row and scalar pairing. Neither zero-response nor positive-$C_4$ occurrence is asserted.

## 43. Input-specific return bounds and coefficient equations

**Lemma 43.1 (additional return and field norms).** All the following return integrals converge absolutely in their displayed norms:

$$
\begin{gathered}
G_2g_0\in L^{5/2}\cap L^{8/3}\cap L^{14/5}\cap L^4,\qquad
G_3g_0\in L^4,\qquad G_4g_0\in L^8,\\
g\in L^1,\ \omega^4g\in L^2
 \ \Longrightarrow\
 G_0g,G_1g\in L^2,\quad G_jg\in L^4\ (0\le j\le2),\\
g\in L^{6/5},\ \omega^3g\in L^2
 \ \Longrightarrow\
 G_0g\in L^2,\quad G_0g,G_1g\in L^4,\\
g\in L^{6/5}\cap L^2\ \Longrightarrow\ G_0g\in L^2,\qquad
\omega^3\mathcal V_1\in L^8.
\end{gathered}
\tag{43.1}
$$

These are particular-input conclusions, not bounded threshold inverses on arbitrary $L^2$.

Proof. In (30.4), let $n$ be the input-height degree and $m=j-n$ the relative degree. The output-$L^q$ time power is

$$
\frac m2-\frac72\left(\frac1{p_n}-\frac1q\right),
\qquad\text{with input norm }\|r^ng\|_{p_n}.
\tag{43.2}
$$

Below time one, weighted $L^2$ inputs give powers $m/2-7/8$ for output $L^4$, and no worse powers for the displayed $q\le4$. They are integrable. For $G_4g_0$ in $L^8$, use the weighted $L^8$ seed inputs and kernel $L^1$, giving powers $m/2\ge0$. These inputs follow from (31.3).

Above time one, the seed input exponents for $n=0,\ldots,4$ are

$$
(p_0,p_1,p_2,p_3,p_4)=(1,1,1,7/6,7/5).
\tag{43.3}
$$

For $G_2g_0$ the largest power is $1-(7/2)(1-1/q)$. At $q=5/2,8/3,14/5,4$ these powers are respectively
$-11/10,-19/16,-5/4,-13/8$.
For $G_3g_0$ in $L^4$ it is $-9/8$; for $G_4g_0$ in $L^8$ it is $-17/16$. All other terms at each indicated degree decay faster, proving these assertions.

For $g\in L^1$ with $\omega^4g\in L^2$, interpolation gives

$$
r^ng\in L^{p_n},\qquad
(p_0,p_1,p_2,p_3)=(1,7/6,7/5,7/4).
\tag{43.4}
$$

Indeed the interpolation weights for $n=1,2,3$ are $2n/7$, so the available height weights are $8n/7>n$. Inserting (43.4) in (43.2) proves the $L^2$ returns through order one and $L^4$ returns through order two. For example the largest large-time power for $G_1g$ in $L^2$ is $-5/4$, and for $G_2g$ in $L^4$ it is $-13/8$.

For $g\in L^{6/5}$ with $\omega^3g\in L^2$, interpolation gives
$rg\in L^{18/13}$ and $r^2g\in L^{18/11}$: the interpolation parameters $1/3,2/3$ give exactly weights one and two. For $G_1g$ in $L^4$, (43.2) gives $-37/24$ and $-119/72$ at large time; $G_0g$ in $L^2$ has power $-7/6$. All are integrable. The last $G_0$ assertion needs no weight: $L^2$ contraction handles $(0,1)$ and the same $t^{-7/6}$ bound handles $(1,\infty)$.

For the field, apply the phase integration and bridge-moment argument of (32.2)–(32.3) with the additional output weight $|r|^3$. A bridge started at zero has $|r|\le S_t$, so an order-one source Gaussian with this weight has $L^8$ norm at most

$$
Ct^{(4-7+7/8)/2}=Ct^{-17/16}.
\tag{43.5}
$$

Its integral over $t\ge1$ converges. The unweighted term also converges, and the finite-time part is bounded by the same full moment majorants. This proves $\omega^3\mathcal V_1\in L^8$ on the whole group, including all phases and its fixed $j_0^{-1}$ and $\nu$. It is not a height-supremum assertion. The convolution norm step is (30.4), with precisely its ordered Haar convolution. $\square$

**Lemma 43.2 (distributional return equations and time boundaries).** On the inputs and orders consumed in §§44–48,

$$
\mathcal EG_0g=g,\qquad
\mathcal EG_jg=-\sum_{\ell=1}^j\mathscr D_\ell G_{j-\ell}g
\quad(1\le j\le4)
\tag{43.6}
$$

in distributions. Only the seed uses order four; $g_1,g_2,g_3$ use at most orders three, two and one respectively.

Proof. On a finite safe height slab and bounded phase Fourier band the differentiated common Dirichlet heat equation is a bounded-potential variation-of-constants identity:

$$
(\partial_t+\mathcal E)\mathsf Q_j(t)g
 =-\sum_{\ell=1}^j\mathscr D_\ell\mathsf Q_{j-\ell}(t)g.
\tag{43.7}
$$

The coefficient of $e^{\lambda s^2t}$ gives exactly $-\lambda$ in $\mathscr D_2$. As in Theorem 36.2, remove the safe slab by the deleted-path inflated-Gaussian estimates of §§30 and 36 and then remove the Fourier cutoff against compact tests. This proves (43.7) without defining a nonzero rational parameter through a pole.

At time zero, $\mathsf Q_0(t)g\to g$ in $L^2$. For $j\ge1$, approximate the input simultaneously in its finite weighted $L^2$ norms through degree $j$ by compact-height, bounded-frequency inputs. For such inputs iterated variation of constants is $O(t)$ at time zero; the finite Gaussian height moments and (30.4) bound the approximation uniformly for $0<t\le1$. Therefore $\mathsf Q_j(t)g\to0$ in $L^2$. Every used input has these weights by (31.3), (38.1), or §§44–45.

At infinity use (43.2) with $q=\infty$. For the seed through degree four, $g_1$ through degree three, $g_2$ through degree two and $g_3$ through degree one, the largest powers are respectively $-3/2,-2,-5/2,-29/12$. In particular the supremum bounds tend to zero and are integrable for compact distributional testing. Near time zero the weighted $L^2$ bounds are likewise integrable after moving differential coefficients to the compact test. Thus integration of (43.7) over $(0,\infty)$ is justified and has exactly the time boundaries claimed in (43.6). Return coefficients integrate against unit Lebesgue Haar measure; no $j_0^{-1}$ is inserted into $G_j$. $\square$

## 44. The second finite charge and the homogeneous response

**Theorem 44.1 (normalized second charge).** Define

$$
\mathcal R_2=\mathcal N_2g_0+\mathcal N_1g_1.
\tag{44.1}
$$

There is a unique normalized real even $g_2\in L^2$ such that

$$
Ag_2=\gamma\mathcal R_2,\qquad
\langle p,g_2\rangle=0.
\tag{44.2}
$$

It has the consumed norms

$$
g_2\in L^1,\qquad \omega^4g_2\in L^2.
\tag{44.3}
$$

Moreover

$$
u_2=\gamma\mu(G_2g_0+G_1g_1+G_0g_2)
 \in\dot{\mathcal H},\qquad
u_2=\Upsilon+d_2p
\tag{44.4}
$$

for a real $d_2$. This identifies the homogeneous second response without asserting its $L^2$ membership.

Proof. Reuse the particular identity
$v=\gamma\mu(G_1g_0+G_0g_1)$ from §§36–37. Put
$W_2=\gamma\mu(G_2g_0+G_1g_1)$.
Lemma 43.1 and the first-charge bounds give $W_2\in L^{14/5}$ and

$$
\mathcal EW_2=-\mathscr D_1v-\mathscr D_2p
\tag{44.5}
$$

in distributions. The right side is continuous in free homogeneous energy: its divergence terms involve $rYv,r^2Yp\in L^2$, and the scalar term is $\lambda p\in L^{14/9}$, by (22.6). Riesz representation for $b$ gives a homogeneous solution in $L^{14/5}$.

To identify that solution with $W_2$, their difference is distributionally $\mathcal E$-harmonic and in $L^{14/5}$. Hypoellipticity makes it smooth. For each real or imaginary part $w$ take compact dilated cutoffs $\eta_R$, with horizontal derivative bounded by $C/R$, and test against $\eta_R^2|w|^{q-2}w$, $q=14/5$. Regularization at $w=0$, the product rule and absorption give

$$
b[\eta_R|w|^{q/2}]
 \le CR^{-2}\|w\|_q^q.
\tag{44.6}
$$

Letting $R\to\infty$ makes its horizontal derivatives zero on every compact set. Bracket generation makes $w$ constant; infinite Haar volume and $L^q$ membership force zero. Thus $W_2\in\dot{\mathcal H}$ and (44.5) is its homogeneous equation.

Expanding the two rows gives exactly

$$
\gamma\mu\mathcal R_2
 =VW_2+\mathcal V_1v+\mathcal V_2p.
\tag{44.7}
$$

Test (44.5) with $p$ and use $\mathcal Ep=\gamma Vp$. All the pairings are homogeneous-energy pairings; (24.1)–(24.4) then give

$$
\langle p,\mathcal R_2\rangle
 =-\frac{\mathfrak a_2[p]+\mathfrak a_1(p,v)}
          {a\gamma^2\mu}
 =-\frac{C_{\rm resp}}{a\gamma^2\mu}=0.
\tag{44.8}
$$

Here is also the required input regularity, before solving for $g_2$. In (44.7), $\mathcal V_2p\in L^1$ follows from $\mathcal V_2\in L^3$ and $p\in L^{3/2}$; its weighted $L^2$ bound follows from bounded $\omega^3\mathcal V_2$ and $\omega p\in L^2$. The term $\mathcal V_1v$ is $L^1$ by $\mathcal V_1,v\in L^2$, and its weighted bound uses bounded $\omega^4\mathcal V_1$. For $VG_2g_0$, the $L^1$ pair is $L^{5/3}\cdot L^{5/2}$; the weighted $L^2$ pair is $L^{10}\cdot L^{5/2}$, since

$$
\omega^4V\le C(1+\mathfrak d)^{-1}\in L^{10}.
\tag{44.9}
$$

Finally $VG_1g_1$ uses $V,G_1g_1\in L^2$ for $L^1$, and bounded $\omega^4V$ for the weighted $L^2$ norm. The $L^2$ return here follows from the same time powers as Lemma 43.1 using (38.1). Consequently
$\mathcal R_2\in L^1$ and $\omega^4\mathcal R_2\in L^2$, in particular $\mathcal R_2\in L^2$.

Proposition 34.1's compact Fredholm argument has
$\ker A=\mathbb Cg_0$, $\ker A^\ast=\mathbb Cp$ and
$\langle p,g_0\rangle=1$. Equation (44.8) therefore gives exactly one solution of (44.2). Conjugation and reflection preserve its normalization and even real right side, giving reality and evenness.

The weighted conclusion requires a bootstrap, rather than an inverse on general threshold data. Let
$R_V=G_0\sqrt V$ be precisely P Theorem 87.2's bounded specified reconstruction. Its adjoint factorization gives

$$
\mathcal N_0=\sqrt V\,R_V^\ast,\qquad
\mathcal N_0:L^2\longrightarrow L^{6/5},
\tag{44.10}
$$

because $\sqrt V\in L^3$. The equation
$g_2=\gamma\mathcal N_0g_2+\gamma\mathcal R_2$ first gives $g_2\in L^{6/5}$. Here $\mathcal R_2\in L^{6/5}$ follows by interpolation between its already proved $L^1$ and $L^2$ norms. Lemma 43.1 now constructs $G_0g_2$ as an absolutely convergent $L^2$ heat integral, without any new weight assumption. Compact testing and cutoff density identify the adjoint product in (44.10) with $VG_0g_2$.

For finite heat integrals, spectral calculus gives
$\mathcal E\int_\delta^TP_tg_2\,dt=P_\delta g_2-P_Tg_2$.
The right side tends in $L^2$ to $g_2$; the large-time heat bound forces $P_Tg_2\to0$. Closedness gives $G_0g_2\in D(\mathcal E)$ and $\mathcal EG_0g_2=g_2$. Since $V\in L^2$ and $\omega^4V$ is bounded, $VG_0g_2$ belongs to $L^1$ and has $\omega^4$ times it in $L^2$. Returning to the charge equation proves (44.3), without circularly using it to define $G_0g_2$.

The vector in (44.4) is in $\dot{\mathcal H}$: this holds for $W_2$, and $G_0g_2\in D(\mathcal E)$ has finite energy. Equations (43.6), (44.2) and (44.7) imply

$$
h(u_2,z)=-\mathfrak a_2(p,z)-\mathfrak a_1(v,z)
       =-\mathcal F_2(z)\qquad(z\in\dot{\mathcal H}).
\tag{44.11}
$$

Projecting along $p$ and using Lemma 24.1's homogeneous complement uniqueness gives $u_2=\Upsilon+d_2p$. Reality gives $d_2\in\mathbb R$. No $L^2$ conclusion about $u_2$ or $\Upsilon$ follows or is needed. $\square$

## 45. The third charge and the normalized fourth residual

**Theorem 45.1 (third charge and fourth solvability).** Set

$$
\begin{aligned}
\mathcal R_3&=\mathcal N_3g_0+\mathcal N_2g_1+\mathcal N_1g_2,\\
\mathcal R_4&=\mathcal N_4g_0+\mathcal N_3g_1
                         +\mathcal N_2g_2+\mathcal N_1g_3,\qquad
\rho=\langle p,\mathcal R_4\rangle.
\end{aligned}
\tag{45.1}
$$

There are unique normalized real $L^2$ charges $g_3,g_4$ with

$$
\begin{aligned}
Ag_3&=\gamma\mathcal R_3,&\langle p,g_3\rangle&=0,\\
Ag_4&=\gamma(\mathcal R_4-\rho g_0),&
\langle p,g_4\rangle&=0.
\end{aligned}
\tag{45.2}
$$

The third charge is odd and satisfies

$$
g_3\in L^{6/5},\qquad \omega^3g_3\in L^2.
\tag{45.3}
$$

Every coefficient row $\mathcal N_jg_i$, $i\le3$, $i+j\le4$, exists in $L^2$. Only the $L^2$ norm of $g_4$ is asserted or consumed.

Proof. For the seed contribution to $\mathcal R_3$, the products are
$\mathcal V_3p/(\gamma\mu)$,
$\mathcal V_2G_1g_0$,
$\mathcal V_1G_2g_0$ and $VG_3g_0$.
Their $\omega^3$-weighted $L^2$ bounds use, in order, $\omega p\in L^2$ and bounded $\omega^2\mathcal V_3$; bounded $\omega^3\mathcal V_2$ and $G_1g_0\in L^2$; $\omega^3\mathcal V_1\in L^8$ and $G_2g_0\in L^{8/3}$; and $\omega^3V\in L^4$ and $G_3g_0\in L^4$. The $G_1g_0$ norm is also an immediate instance of (43.2).

The three order-two products on $g_1$ use bounded $\omega^3\mathcal V_2$, bounded $\omega^3\mathcal V_1$, and $\omega^3V\in L^4$, respectively against $G_0g_1,G_1g_1\in L^2$ and $G_2g_1\in L^4$. The two order-one products on $g_2$ use bounded $\omega^3\mathcal V_1,\omega^3V$ against $G_0g_2,G_1g_2\in L^2$. Thus $\omega^3\mathcal R_3\in L^2$.

For completeness its $L^{6/5}$ norm uses the following field/return Hölder pairs:

$$
\begin{array}{c|c}
\text{product}&\text{field exponent, return exponent}\\ \hline
\mathcal V_3p&(4,12/7)\\
\mathcal V_2G_1g_0,\ \mathcal V_2G_0g_1&(3,2)\\
\mathcal V_1G_2g_0&(30/13,5/2)\\
VG_3g_0,\ VG_2g_1&(12/7,4)\\
\mathcal V_1G_1g_1,\ \mathcal V_1G_0g_2,\ VG_1g_2&(3,2).
\end{array}
\tag{45.4}
$$

Every reciprocal sum is $5/6$. All field exponents satisfy (32.3)'s strict integrability condition; the mode is in $L^{12/7}$ by its full spatial decay, and all return norms were proved above or in §38. Hence $\mathcal R_3\in L^{6/5}$.

Coefficient parity makes $\mathcal R_3$ real odd, so $\langle p,\mathcal R_3\rangle=0$. Fredholm solvability and normalization give $g_3$, and uniqueness makes it real odd. Equation (44.10) first gives $g_3\in L^{6/5}$. The unweighted $G_0$ assertion of Lemma 43.1 then gives $G_0g_3\in L^2$ with its specified adjoint interpretation. Bounded $\omega^3V$ and the already proved $\omega^3\mathcal R_3\in L^2$ give $\omega^3g_3\in L^2$ from its equation. This repeats the noncircular reconstruction bootstrap, not an $L^1$ claim about $g_3$.

Lemma 43.1 now gives $G_0g_3,G_1g_3\in L^4$, and $G_jg_2\in L^4$ for $j\le2$. Multiplication by the corresponding $L^4$ fields proves every new row is in $L^2$; the seed and $g_1$ rows are §§33 and 38. Thus $\mathcal R_4\in L^2$. Since $\langle p,g_0\rangle=1$, its subtraction in (45.2) is exactly orthogonal to $p$. Fredholm gives the normalized real $g_4$. This construction makes no weighted, native-domain or energy assertion about $g_4$. Parity of fixed charges never restricts the actual complex states. $\square$

## 46. Both later early native rows on the full output space

**Theorem 46.1 (second- and third-charge early remainders).** With restriction to the original $\Omega_s$ and zero extension as in Definition 29.1,

$$
\left\|\mathcal N_sg_i-\sum_{j=0}^{4-i}s^j\mathcal N_jg_i\right\|_2
 =o(s^{4-i}),\qquad i=2,3.
\tag{46.1}
$$

The norms are on the entire common $L^2(\mathbb R^4)$ space, with all real phases.

Proof. Fix sufficiently small $\ell>0$ so $(-L,L)\Subset I_s$, $L=\ell/s$, and $\nu\ell<1/4$. Put $T=s^{-2}$. Auxiliary killing at $\pm L$ is used only to estimate the original heat. On safe paths differentiate the combined shifted Gaussian; clock derivatives have the same relative-degree count as in §39.

For $g_2$, expand the return through degree two. On $(0,1)$, weighted $L^2$ inputs through degree three and kernel $L^1$ give integrable powers $t^{m/2}$; multiply by bounded $F_s$. On $(1,T)$ use return output $L^\infty$, $F_s\in L^2$, and (43.4). At derivative degree three the four powers

$$
\frac{3-n}{2}-\frac7{2p_n}=-2
\qquad(n=0,1,2,3)
\tag{46.2}
$$

are integrable. The Taylor remainder in the joint product is therefore $O(s^3)$.

For $g_3$ expand through degree one. The analogous second-derivative inputs are
$(p_0,p_1,p_2)=(6/5,18/13,18/11)$.
Their large-time powers are

$$
-\frac{23}{12},\qquad-\frac{73}{36},\qquad-\frac{77}{36}.
\tag{46.3}
$$

Small times use weighted $L^2$ and kernel $L^1$ as before. Hence this safe Taylor remainder is $O(s^2)$.

We account separately for all noncompact input, deleted paths and coefficient time tails. Let $w=6-i$ and

$$
e_i(L)=\|\mathbf1_{|r|>L/4}\omega^wg_i\|_2\longrightarrow0.
\tag{46.4}
$$

The original shifted heat and its extra-killed restriction are $L^2$ contractions because their nonnegative forms are $C_s$ and its Dirichlet restriction. On $(0,T)$ the outer-input return is therefore at most
$TL^{-w}e_i(L)$.
For an outer coefficient of relative degree $m$ and input degree $n$, multiply its $L^2$ bound by its factor $s^{m+n}$ to obtain

$$
Cs^{m+n}T^{1+m/2}L^{n-w}e_i(L)
 \le Cs^{w-2}e_i(L).
\tag{46.5}
$$

This includes input outside $\Omega_s$, which is absent from the native restriction. Since $w-2=4-i$, it is precisely the required little-o.

For inner input, a path deleted at an auxiliary face has relative height supremum at least a fixed multiple of $L$. The relative-degree-$m$ inflated kernel, retaining that exit event, has $L^p$-to-$L^\infty$ bound

$$
Ct^{m/2-7/(2p)}e^{-cL^2/t}.
\tag{46.6}
$$

To obtain it, retain the exit event in the phase-integration bound (30.3); the inverse-determinant moment estimate supplies the exponential, its $L^1$ bound supplies the relative moment, and interpolation gives the indicated convolution-kernel norm. The input factor remains $r^ng_i$. Its deleted-path time integral and its coefficient tail above $T$, after the coefficient factor, are each bounded by

$$
Cs^{m+n}L^{m+2-7/p}\|r^ng_i\|_p
 =Cs^{7/p-2+n}\|r^ng_i\|_p.
\tag{46.7}
$$

The substitution $t=L^2u$ proves the first bound; direct integration above $T$ proves the second, with a strictly integrable power in every used case.

For $g_2$, use $n=0,1,2$ and the corresponding exponents in (43.4): all powers in (46.7) equal five. For $g_3$, use $n=0,1$ and exponents $6/5,18/13$: the powers are $23/6,73/18$. They exceed the required orders two and one. The unexpanded native deletion is (46.6) with $m=n=0$ and input $L^1$ or $L^{6/5}$. Original surviving covariances remain uniformly comparable even after leaving the auxiliary strip, by the fixed original denominator margins. Safe paths cannot end outside either original face. Thus these same bounds cover the zero-extended output everywhere, without a phase cutoff or a replacement operator.

We have proved the joint return estimate multiplied by $F_s$. For each retained $s^jG_jg_i$ use its $L^4$ norm and expand $F_s$ only through degree $4-i-j$. Lemma 32.1 with $p=4$ gives remainder orders $s^3,s^2,s$ for $g_2$ at $j=0,1,2$, and $s^2,s$ for $g_3$ at $j=0,1$. Multiplication by $s^j$ makes these $O(s^{5-i})$. Hölder restores all complete-field cross terms and proves (46.1). No $L^p$ integrability has been assigned to the full long Coulomb multiplier. $\square$

## 47. The actual spectral parameter and the final strong row

**Theorem 47.1 (late corrections and final fixed-input limit).** On every actual sequence in Theorem 42.2, put $h_s=-\epsilon_c(s)/a=r_ss^8/a$. Then

$$
s^i\|(\mathcal B_s(h_s)^\ast-\mathcal N_s)g_i\|_2=o(s^4)
\quad(i=2,3),\qquad
\|(\mathcal B_s(h_s)^\ast-\mathcal N_0)g_4\|_2\longrightarrow0.
\tag{47.1}
$$

These statements include bounded-$r_s$ sequences.

Proof. Theorem 44.1 gives $g_2\in L^1\cap L^2$. The actual-path estimate (29.4) therefore bounds its unweighted late error by $C(h_s+s^5)$. Since $h_s=o(s^4)$, its factor $s^2$ proves the first assertion for $i=2$.

For $g_3$, interpolate (29.5)'s $1\to2$ and $2\to2$ estimates at $p=6/5$. Symmetry and composition with the $2\to\infty$ estimate give

$$
\begin{array}{c|cc}
& p\to2&p\to\infty\\ \hline
0<t\le T&Ct^{-7/6}&Ct^{-35/12}\\
t\ge T&Cs^{4/3}t^{-1/2}&Cs^{10/3}t^{-5/4}.
\end{array}
\tag{47.2}
$$

No Markov assertion for the shifted raw-measure semigroup is used. On $(0,1)$ use $L^2$ contraction and $\|F_s\|_\infty\le C$. On $(1,T)$, the replacement $e^{-h_st}-1$ in the short field costs

$$
Ch_s\|g_3\|_{6/5}\int_1^\infty t^{1-35/12}dt,
\tag{47.3}
$$

which is finite. The short-field return past $T$ costs
$Cs^{10/3}\int_T^\infty t^{-5/4}dt\,\|g_3\|_{6/5}
=Cs^{23/6}\|g_3\|_{6/5}$.

The long multiplier has supremum $Cs^5$. Its return below $T$ costs
$Cs^5(\|g_3\|_2+\|g_3\|_{6/5})$, because $t^{-7/6}$ is integrable above one. Past $T$ its cost is at most

$$
Cs^{19/3}\|g_3\|_{6/5}
 \int_T^\infty e^{-h_st}t^{-1/2}dt
 \le Cs^{19/3}h_s^{-1/2}\|g_3\|_{6/5}
 \le Cs^{7/3}\|g_3\|_{6/5}.
\tag{47.4}
$$

The last inequality uses only the owned actual $r_s\ge c>0$. Hence the $g_3$ error is $O(h_s+s^{7/3})$; its factor $s^3$ is $o(s^4)$. Both original deaths remain in every heat operator.

Finally (29.4) gives convergence on the dense class $L^1\cap L^2$. P (104.2) gives uniform $L^2$ bounds for $\mathcal B_s(h_s)^\ast$ along $h_s\ge cs^8$, $h_s\to0$; P (104.9) gives norm convergence $\mathcal N_s\to\mathcal N_0$. Approximate the fixed $g_4$ in $L^2$ by a member of the dense class. Uniform boundedness bounds the approximation error independently of $s$; first take $s\to0$, then the approximation error to zero. This proves the strong limit in (47.1), without a rate or a weight on $g_4$. $\square$

## 48. Infinite-domain scalar correspondence with the unchanged quartic

**Theorem 48.1 (paid fourth scalar).** The scalar $\rho$ of (45.1) satisfies

$$
\rho=-\frac{C_4}{a\gamma^2\mu},
\tag{48.1}
$$

where $C_4$ is exactly (24.5).

Proof. Define fixed reconstructed vectors

$$
u_0=p,\qquad u_1=v,\qquad
u_n=\gamma\mu\sum_{i+j=n}G_jg_i\quad(n=2,3),\qquad
u_4^0=\gamma\mu\sum_{\substack{i+j=4\\i\le3}}G_jg_i.
\tag{48.2}
$$

We have $u_2\in\dot{\mathcal H}\subset L^{14/5}$,
$u_3\in L^4$ and $u_4^0\in L^8+L^4$ by Lemma 43.1 and §38. The coefficient and charge equations give

$$
\begin{aligned}
\mathcal Eu_n
 &=\gamma\mu g_n-\sum_{\ell=1}^n\mathscr D_\ell u_{n-\ell}
 &&(0\le n\le3),\\
\mathcal Eu_4^0
 &=-\sum_{\ell=1}^4\mathscr D_\ell u_{4-\ell},\\
\mu g_n&=\sum_{k=0}^n\mathcal V_ku_{n-k}
 &&(0\le n\le3),\\
\gamma\mu\mathcal R_4
 &=Vu_4^0+\mathcal V_1u_3+\mathcal V_2u_2
                       +\mathcal V_3v+\mathcal V_4p.
\end{aligned}
\tag{48.3}
$$

The first two lines hold distributionally; the last two are locally integrable identities. There is no term $g_4$ in $u_4^0$.

We justify all integrations at spatial infinity before using them. On a homogeneous annulus $A_R$ and its fixed enlargement, the owned mode and response bounds give

$$
\|p\|_{2,A_R}=O(R^{-3/2}),\quad
\|\nabla_Hp\|_{2,A_R}=O(R^{-5/2}),\quad
\|v\|_{2,A_R}=O(R^{-1/2}),\quad
\|\nabla_Hv\|_{2,A_R}=O(R^{-3/2}).
\tag{48.4}
$$

The annulus has volume $O(R^7)$. Hölder therefore gives

$$
\|u_2\|_{2,A_R}=O(R),\qquad
\|u_3\|_{2,A_R}=O(R^{7/4}),\qquad
\|u_4^0\|_{2,A_R}=O(R^{21/8}+R^{7/4}).
\tag{48.5}
$$

For a local equation $\mathcal Eu=YF+G$ with locally $L^2$ data, the cutoff real-part energy test gives

$$
\|\nabla_Hu\|_{2,A_R}
 \le C\left(R^{-1}\|u\|_{2,\widetilde A_R}
            +\|F\|_{2,\widetilde A_R}
            +R\|G\|_{2,\widetilde A_R}\right).
\tag{48.6}
$$

Here is its local justification without assuming the derivative being estimated. Localize the distributional equation; the cutoff terms can be written as horizontal divergences of $L^2$ fields plus $L^2$ functions. Smooth in the group, perform the real-part test with $\eta^2u$, and absorb each mixed derivative term by $2AB\le\delta A^2+\delta^{-1}B^2$. The cutoff derivative contributes $R^{-1}\|u\|_2$ and the scalar forcing contributes $R\|G\|_2$. Weak closure gives local horizontal energy membership and (48.6) for the original data. This is a local estimate, not global homogeneous energy membership.

The third coefficient equation has explicitly

$$
\mathcal Eu_3
 =Y(-2\nu rYu_2+3\nu^2r^2Yv-4\nu^3r^3Yp)
     +\lambda v+\gamma\mu g_3.
\tag{48.7}
$$

Since $u_2\in\dot{\mathcal H}$ and $g_3\in L^2$, (48.4)–(48.6) give
$\|\nabla_Hu_3\|_{2,A_R}=O(R)$.
The fourth equation has divergence field

$$
-2\nu rYu_3+3\nu^2r^2Yu_2
       -4\nu^3r^3Yv+5\nu^4r^4Yp
\tag{48.8}
$$

and scalar forcing $\lambda u_2$. The same estimate gives
$\|\nabla_Hu_4^0\|_{2,A_R}=O(R^2)$.

Consequently the annular absolute pairings
$|\nabla_Hv|\,|\nabla_Hu_3|$,
$|rYp|\,|Yu_3|$ and
$|\nabla_Hp|\,|\nabla_Hu_4^0|$
are each $O(R^{-1/2})$. They are summable over dyadic annuli. Cutoff-derivative errors in the $v/u_3$ exchange are bounded by

$$
C\left(R^{-1}\|u_3\|_{2,A_R}\|\nabla_Hv\|_{2,A_R}
       +R^{-1}\|v\|_{2,A_R}\|\nabla_Hu_3\|_{2,A_R}\right)
 =O(R^{-3/4})+O(R^{-1/2}),
\tag{48.9}
$$

and those in the $p/u_4^0$ exchange are
$O(R^{-7/8})+O(R^{-1/2})$. They all vanish. The weighted first-coefficient cutoff pairing with $p,u_3$ is controlled in the same way using $rYp$.

The other kinetic terms are finite by
$\|rYv\|_2\|Yu_2\|_2$,
$\|r^2Yp\|_2\|Yu_2\|_2$ and
$\|r^2Yp\|_2\|rYv\|_2$.
For potentials, $\mathcal V_1p\in L^{4/3}$ pairs with $u_3\in L^4$;
$p\mathcal V_2\in L^{14/9}$ pairs with $u_2\in L^{14/5}$;
bounded $\mathcal V_3$ pairs $p,v\in L^2$.
The term $Vp$ is in both dual spaces for $L^8+L^4$, and $Vv\in L^{4/3}$. The remaining $\mathcal V_1v/u_2$ pair is the continuous energy-multiplier pairing of Lemma 24.1. The unweighted threshold $p/u_2$ term is paid by $p\in L^{14/9}$. Thus the limiting exchanges include every kinetic, potential and threshold term; neither $u_3$ nor $u_4^0$ has been assigned a global energy norm.

Now test the fourth equation in (48.3) with cutoffs of $p$. Use $\mathcal Ep=\gamma Vp$ and the last line of (48.3). The vanishing boundary terms just proved give

$$
\rho=-\frac{S_4}{a\gamma^2\mu},\qquad
S_4=\mathfrak a_4[p]+\mathfrak a_3(p,v)
          +\mathfrak a_2(p,u_2)+\mathfrak a_1(p,u_3).
\tag{48.10}
$$

The first response equation, tested against cutoffs of $u_3$, gives
$h(v,u_3)=-\mathfrak a_1(p,u_3)$.
The third equation, tested against cutoffs of $v$, gives

$$
h(u_3,v)
 =-\mathfrak a_1(u_2,v)-\mathfrak a_2[v]-\mathfrak a_3(p,v).
\tag{48.11}
$$

All these fixed vectors are real. Hermitian symmetry and the paid exchanges imply

$$
\begin{aligned}
S_4
 &=\mathfrak a_4[p]+2\mathfrak a_3(p,v)+\mathfrak a_2[v]
          +\mathfrak a_2(p,u_2)+\mathfrak a_1(v,u_2)\\
 &=D_4+\mathcal F_2(u_2).
\end{aligned}
\tag{48.12}
$$

By (44.4), $\mathcal F_2(p)=0$ and (24.2),

$$
\mathcal F_2(u_2)=\mathcal F_2(\Upsilon)
 =-h[\Upsilon],\qquad S_4=C_4.
\tag{48.13}
$$

This proves (48.1). In particular the field products
$\nu^2\lambda V_{2t}$ and $\lambda^2V_{tt}/2$ and the threshold term
$-a\lambda\|v\|_2^2$ in $D_4$ survive unchanged. The normalization is
$\rho=-C_4/(a\gamma^2\mu)$, not an identification of $\rho$ with $C_4$. $\square$

## 49. The exact fourth corrected actual equation

**Theorem 49.1 (full residual and every actual weak coefficient).** Define the finite $L^2$ vector

$$
G_s^{\rm corr}=g_0+sg_1+s^2g_2+s^3g_3+s^4g_4.
\tag{49.1}
$$

For every actual sequence with $C_{\rm resp}=0$ and $\epsilon_c(s)=o(s^4)$,

$$
\left\|(I-\gamma\mathcal B_s(h_s)^\ast)G_s^{\rm corr}
        -\frac{s^4C_4}{a\gamma\mu}g_0\right\|_2=o(s^4).
\tag{49.2}
$$

It follows that every actual microscopic weak coefficient satisfies (42.5).

Proof. Theorems 33.2, 39.1 and 40.1 give the seed and first-charge rows through degrees four and three, including their actual-height errors. Theorems 46.1 and 47.1 give the second and third rows through degrees two and one. The final strong row of Theorem 47.1 is multiplied by $s^4$. Expanding each fixed input only to its consumed degree, the equations for $g_0,g_1,g_2,g_3$ cancel exactly orders zero through three. The fourth row is

$$
Ag_4-\gamma\mathcal R_4
 =-\gamma\rho g_0=\frac{C_4}{a\gamma\mu}g_0.
\tag{49.3}
$$

Every omitted vector is $o(s^4)$ in the full common $L^2$ space. This proves (49.2), with constants independent of actual choices along the fixed sequence.

For an actual state let $f_s=\mathcal T_s\mathcal U_s\psi_s$. Its exact original-domain equation is (33.6):

$$
f_s=\gamma\mathcal B_s(h_s)f_s,\qquad \|f_s\|_2=1.
\tag{49.4}
$$

At each $h_s>0$ this is a bounded-operator equation. Pair it against the entire vector (49.1). Equations (49.2)–(49.4) give

$$
0=\frac{s^4C_4}{a\gamma\mu}\langle g_0,f_s\rangle+o(s^4).
\tag{49.5}
$$

The test needs no native form-domain membership. In particular, if
$\alpha_s=\langle g_0,f_s\rangle$ and $z_s=f_s-\alpha_sp$, then
$\langle g_0,z_s\rangle=0$ exactly. The full residual is paired with the unit vector $f_s$, so every remaining complement term is paid by its full $L^2$ norm. There is no unproved polynomial rate for $z_s$ and no multiplication of an uncontrolled $o(1)$ complement by a negative power of $s$.

If $f_s\rightharpoonup cp$, then $\alpha_s\to c$ because
$\langle g_0,p\rangle=1$. Division of (49.5) by $s^4$ gives $cC_4=0$. The determinant-one shears $\mathcal T_s$ and their inverses converge strongly to the identity on each fixed $L^2$ test: prove it first on compact smooth tests by their explicit matrices (2.4), then use unitarity and density. Thus $f_s$ and the original $\mathcal U_s\psi_s$ have the same weak limits. This proves (42.5) for all complex choices and weak coefficients, without imposing fixed-charge reality or parity on an actual state. $\square$

**Corollary 49.2 (conditional positive-quartic full-mass Coulomb branch).** If the fixed datum of Definition 42.1 has $C_4>0$, then (42.6) holds for every prescribed sequence and every actual normalized complex ground-state choice, with

$$
\begin{aligned}
M&=\int_I\phi(k)^2c_\kappa(k)c_\kappa(k)^{\mathsf T}\,dk,\\
\beta_C&=\frac{\phi(k_0)\int_I\phi(k)^3\,dk}{4\pi\sqrt{\det M}},
& e_C&=-\frac{\beta_C^2}{4a},&
\varrho&=\frac{\beta_C}{2a},\\
h_C(z)&=(\det M)^{-1/4}(\varrho^3/\pi)^{1/2}
       \exp\!\left(-\varrho\sqrt{z^{\mathsf T}M^{-1}z}\right),\\
(\mathcal D_g\psi)(k,z)&=g^{-3/2}\psi(k,z/g),&
\mathbb T&=\{\zeta\in\mathbb C:|\zeta|=1\}.
\end{aligned}
\tag{49.6}
$$

Proof. Under $C_{\rm resp}=0$ and $C_4>0$, the owning quartic spectral-bottom law, Theorem 27.1, supplies $\epsilon_c(s)=o(s^4)$. The owned actual compactness and weak-disk result identifies every microscopic weak cluster as $cp$. Theorem 49.1 forces $c=0$. Weak sequential compactness of the unit ball then makes each whole prescribed actual sequence weakly zero: a sequence failing a weak test would have a weakly convergent subsequence contradicting its zero cluster.

Apply the already proved actual weak-zero endpoint, Theorem 10.2, with its original fixed-cutoff source hypotheses. It gives $E_s/g_s^2\to e_C$, $r_s\to-\chi_c^2e_C$ and the full-mass phase orbit with exactly (49.6). Since $g_s=\chi_cs^3$, its energy statement is (42.6). This uses the actual theorem, not its one-sided trial upper bound.

All antecedents of Theorem 10.2 remain in force, including its fixed source, matrix positivity, both original faces and actual attainment. If an every-choice conclusion failed, choose failing actual ground states along a sequence $s_n\downarrow0$; the sequential argument just proved contradicts that failure. This establishes the stated every-choice quantifiers, with no trial, arbitrary near-minimizer or phase-fixed substitute. $\square$

## 50. Mathematical attribution and the remaining selection boundary

**Definition 50.1 (owning analytic scope and classical interfaces).** Theorems 44.1–49.1 and Corollary 49.2 are conditional repository-derived deductions from the fixed original problem. P §§76, 87–88, 97 and 104–107 own the both-face native heat, specified compact reconstruction and simple mode, exact shear, common bridge moments, attainment, actual equation and actual weak-disk/orbit criteria at their stated scopes. R §§4–5, 8, 16 and 19–20 own the multiplier controls, homogeneous complement gap, left coordinate, particular form/$L^2$ first response and exterior control. Entire-height response escape, Theorem 3.1, owns the mode and horizontal derivative tails. Theorems 22.1 and 27.1 retain their conditional full-domain energy hypotheses; Theorem 10.2 retains the original fixed-cutoff actual weak-zero endpoint hypotheses. The finite seed and first-charge results are reused from §§29–40.

The additional return norms, normalized higher charges and consumed weights, their two early native rows, actual-height late rows, final fixed-$L^2$ strong row, spatial-boundary payments and $\rho/C_4$ correspondence are proved in §§43–48. They are not assumed as extra analytic suppliers. The resulting finite residual is consumed by the exact actual equation in §49. There is no global $L^2$ threshold inverse, positive $L^2$ complement gap, uncut native representative of $\Upsilon$, global energy membership for $u_3,u_4^0$, prescribed $r_s$ growth or rational continuation across a pole.

The ordered Young norm step is Fischer–Ruzhansky, *Sobolev spaces on graded groups*, [arXiv:1311.0192v1, §2.1, (2.2)](https://arxiv.org/html/1311.0192v1#S2.SS1): $f*k(\xi)=\int f(\eta)k(\eta^{-1}\xi)d\eta$, with $1/p+1/b=1+1/q$. The Engel law (2.6) is graded and unimodular, Haar measure is unit Lebesgue measure, and this is exactly the input-first factor order of (30.3). The horizontal Sobolev realization remains the identical $Q=7$, order-one interface (22.7) from Bahouri–Barilari–Gallagher–Léautaud, Theorem 5.1. Riesz representation, compact Fredholm solvability, Hölder, interpolation, spectral calculus, finite Gaussian differentiation and cutoff energy estimates are classical intermediate tools. The local positive-time heat interface keeps its original interior-endpoint scope; it is not used to supply missing noncompact, time-zero, moving-face or infinite-time bounds. The inherited global analytic antecedents remain conditional, and no literature-wide novelty or absence claim is made.

**Definition 50.2 (resolved finite compatibility and unresolved original selection).** The later-row, scalar-identification and actual-consumer mathematical boundary stated in Definition 41.2 is replaced by Theorems 44.1–49.1 at their explicit hypotheses: $C_{\rm resp}=0$ and actual $\epsilon_c=o(s^4)$ give $cC_4=0$. Under the additional fixed-data condition $C_4>0$, Theorem 27.1 supplies the latter premise and Corollary 49.2 gives the original-source full-mass Coulomb endpoint. At $C_4=0$ the finite compatibility is nonselecting. At $C_4<0$, the owning quartic law does not give $\epsilon_c=o(s^4)$, so that premise cannot be omitted from Theorem 49.1.

Absolute response and quartic signs, zero-response and positive-quartic occurrence, and the finer $C_{\rm resp}=0,C_4=0$ actual scale/profile branch remain unresolved. The original full-family every-actual-choice target of Definition 9.1 is therefore still unresolved, including the remaining bounded, divergent or mixed actual scale alternatives where applicable. Centered crossover, analytic $L^2$ state preparation, physical-space or three-dimensional realization, and native operational clock/resource bridges are not consequences of these conditional analytic results. The original source and clock, raw and weighted charges, entire complex domains and every-choice quantifiers remain those of Definitions 1.1–2.2; canonical correction parity imposes no condition on actual states.

## 追加锚（本行以下为增补区）

## 51. A common-source translated two-face family

**Definition 51.1 (fixed realization and order of limits).** Write G for
*Native two-control Green stability* and L for *Native long-time phase
 diffusion*. Retain the ordinary analytic antecedents of Definitions
1.1–3.2, P §§70,75–76,87–88,97,104–107 and L §§35–36,41.
Fix $H\in(0,1/2)$, $a,\varepsilon>0$, a prescribed sign of $\kappa$
and $R_*>0$. Put $x=\sqrt{R_*}/\pi$ and $L_0=H/[4(x+1)]$.
Choose $b_{\rm ref}>0$ with
$\varepsilon b_{\rm ref}<\min(xL_0/4,L_0/4)$, and then a sufficiently
small fixed nonzero $\kappa$ of that sign. Set

$$
\begin{aligned}
k_0&=\alpha_\kappa+xL_0,&
I_b&=(k_0-\varepsilon b,k_0+L_0-\varepsilon b),
       &&0<b\le b_{\rm ref},\\
c_\kappa(k)&=\left(
\frac{(k-2\kappa)(H+\kappa-k)}{2H(k-\alpha_\kappa)},
-\frac{k(k-2\kappa)}{2H(k-\alpha_\kappa)},
\frac{H+\kappa-k}{H(k-\alpha_\kappa)}\right),\\
\lambda&=\varepsilon^2\pi^2/L_0^2,&
\nu&=\varepsilon/(k_0-\alpha_\kappa),&
\lambda/\nu^2&=R_*.
\end{aligned}
\tag{51.1}
$$

The original means are $X=Y=H+\kappa$, $Z=1-2H$, and the five
probabilities, in original order, are
$(k-2\kappa,H+\kappa-k,1-2H,H+\kappa-k,k)$.
The lifted real coordinate remains $x_{\rm lift}=D/\kappa$.
All members use precisely this one vector, raw $dk\,dq$, source
$o=(k_0,0)$, covariance $\operatorname{diag}(\varepsilon^2,1)$,
and the original $B$ heat clock, independently of $a$.
Only the two Dirichlet faces move. A limit in $s$ always fixes $b>0$
first; $b=0$ is only a coefficient-family closure point.

**Proposition 51.2 (admission and compact-family uniformity).** The
choices in Definition 51.1 can be made for either sign so that all
$I_b$ are admitted original intervals, with common larger-interval
probability, pole, determinant and derivative margins. The all-height
heat estimates of P76 and the two-endpoint band estimates of L41 hold
with constants uniform for $0<b\le b_{\rm ref}$.

Proof. At $\kappa=0$, the closed union of the intervals lies in
$[xL_0-\varepsilon b_{\rm ref},(x+1)L_0]\Subset(0,H)$.
Its lower endpoint is at least $3xL_0/4$ and its upper endpoint is $H/4$.
Continuity therefore permits a fixed larger interval $(l',u')\Subset(0,H)$
and a sufficiently small $\delta>0$ such that $|\kappa|=\delta$ and
$2\delta<\min\{l'/4,(H-u')/2,H/4\}$.
R Proposition 14.1 applies on $[-2\delta,2\delta]\times[l',u']$.
In particular every probability is positive, $k-\alpha_\kappa$ stays
positive, and
$\det(c_\kappa,c_\kappa',c_\kappa'')
=-(H^2-\kappa^2)/[2H^3(k-\alpha_\kappa)^3]$ stays away from zero.
All fixed-order derivatives are bounded there. These are actual
jointly realized source conditions, not independently prescribed jets.

Translate the height to $z=k-(k_0-\varepsilon b)\in(0,L_0)$.
The coefficient $c_b(z)=c_\kappa(k_0-\varepsilon b+z)$ extends smoothly
through $b=0$ on this fixed interval. In G (26.7) the map from a phase
vector to the quadratic numerator coefficients is invertible: its kernel
would give a linear combination of $c_b,c_b',c_b''$ equal to zero.
The translated polynomial coefficient map and its inverse have bounded
norms on the compact $b$ interval. G (26.8)–(26.12)'s sublevel proof
therefore gives uniform all-real-frequency coercivity and smoothing.
The scalar height eigenvalues are unchanged, with gap $3\lambda$.
Moreover

$$
M_b=\int_0^{L_0}c_b(z)c_b(z)^{\mathsf T}
             \frac2{L_0}\sin^2(\pi z/L_0)\,dz
\quad\hbox{satisfies}\quad m\mathrm{Id}\le M_b\le M\mathrm{Id}.
\tag{51.2}
$$

Indeed it is continuous even at $b=0$, and a zero quadratic form
would make a nonzero linear combination of $c_b$ vanish on an interval,
contradicting the determinant. Compactness gives the stated constants.
The bounded-potential perturbation and $H^2$ zero-boundary quotient
proofs in L36 and L41 now have uniform constants: the potential
coefficients, the inverse of the height gap and the matrices (51.2)
are uniformly bounded. Their complementary Riesz projections give the
same uniform band error including both endpoint factors. The common
larger interval supplies P76's all-height small-time bound, also
uniformly. This proves the asserted uniformity by its owning proofs.
It does not admit a source on the $b=0$ face. $\square$

## 52. A convergent signed diagonal coefficient and its late part

**Definition 52.1 (relative diagonal and canonical wall constant).** Let
$B_b$ denote (1.4) on $I_b\times\mathbb R^3$, $S_b=B_b-\lambda$ and
$K_b(t;Y,Z)=e^{\lambda t}p_t^{B_b}(Y,Z)$, extended by zero.
Write $K_{\rm ref}=K_{b_{\rm ref}}$, $W_{1,b}(Y)=\int_1^\infty K_b(t;o,Y)dt$,
$\ell_0=L_0/\varepsilon$, and define differences directly by

$$
\begin{aligned}
\delta_b^{<}&=\int_0^1(K_b-K_{\rm ref})(t;o,o)dt,\\
\Delta_b&=\int_0^\infty(K_b-K_{\rm ref})(t;o,o)dt.
\end{aligned}
\tag{52.1}
$$

For the canonical height bridge with generator $\partial_r^2$ from
zero to zero, use $M_0,h_t,\gamma_{M_0}$ of (3.1) and put

$$
D_E(t)=h_t(0)\mathbb E_{0,0}^t
 [\gamma_{M_0}(0)\mathbf1_{\{\min H\le-1\}}],
\qquad C_E=\int_0^\infty D_E(t)dt.
\tag{52.2}
$$

**Theorem 52.2 (signed boundary coefficient and late diagonal size).**
The integrals (52.1) converge absolutely for each fixed $b>0$,
$0<C_E<\infty$, and

$$
\lim_{b\downarrow0}b^5\Delta_b=-C_E/j_0<0,
\qquad W_{1,b}(o)\asymp b^2\quad(0<b\le b_{\rm ref}).
\tag{52.3}
$$

The comparison constants in the second assertion are independent of $b$.

Proof. In the source chart at scale one the height intervals are
$(-b,\ell_0-b)$ and $(-b_{\rm ref},\ell_0-b_{\rm ref})$.
Both kernels are expectations over the same free height bridge, with
the same rational covariance on a path surviving the relevant interval.
A difference of their survival indicators forces the path to reach
$-b$ or $\ell_0-b_{\rm ref}$, hence to have supremum at least $b$.
On paths surviving either interval the factor $(1+\nu H)^{-2}$ has
common positive bounds; its covariance is comparable to $M_0$.
Taking the phase Gaussian supremum and using (3.3), with $m=0$, gives

$$
|(K_b-K_{\rm ref})(t;o,o)|
 \le Ct^{-7/2}e^{-cb^2/t}\quad(0<t\le1).
\tag{52.4}
$$

The common raw chart factor and bounded $e^{\lambda t}$ are included
in $C$. L41 gives $Ct^{-3/2}$ for $t\ge1$. These are integrable
for each positive $b$; separate divergent diagonal Green integrals
have not been subtracted.

For $t\le1$, (3.3) bounds $D_E(t)$ by
$Ct^{-7/2}e^{-c/t}$; for $t\ge1$, it is at most
$k_t(0)=t^{-7/2}k_1(0)$. Thus $C_E$ is finite. The crossing event
has positive bridge probability and $M_0$ is positive definite almost
surely, so $C_E>0$. More explicitly, if $Z=-\min_{[0,1]}H$, Brownian
scaling and Tonelli give

$$
C_E=\frac25h_1(0)\mathbb E_{0,0}^1[\gamma_{M_0}(0)Z^5].
\tag{52.5}
$$

The integral of $t^{-7/2}\mathbf1_{\{t\ge Z^{-2}\}}$ is
$2Z^5/5$; (3.3)'s fifth moment also proves its finiteness.
The variance convention is exactly generator $\partial_r^2$.

Apply the exact privileged chart $\Xi_b$ and determinant-one shear
(2.4) at scale $b$, with raw Jacobian $j_0b^7$.
At physical time $b^2u$ the first interval becomes
$(-1,\ell_0/b-1)$, its covariance factor is $(1+\nu bH)^{-2}$,
and its clock is $e^{\lambda b^2u}$.
The reference interval becomes
$(-b_{\rm ref}/b,(\ell_0-b_{\rm ref})/b)$.
For every fixed $u>0$ continuity of bridges, covariance comparability
and (3.3)'s inverse moment give

$$
j_0b^7(K_b-K_{\rm ref})(b^2u;o,o)\longrightarrow-D_E(u).
\tag{52.6}
$$

The minimum equals $-1$ with probability zero; the upper face is
retained before tending to infinite rescaled distance. On
$u\le b^{-2}$, (52.4) gives the integrable majorant
$Cu^{-7/2}e^{-c/u}$ for the left side of (52.6).
Extend this integrand by zero beyond $b^{-2}$ and use dominated
convergence. The physical-time part $t\ge1$ has uniformly bounded
integral by Proposition 51.2 and vanishes after multiplication by
$b^5$. Since $dt=b^2du$, this proves the first limit in (52.3).
The original clock has remained present at every finite $b$.

For the late part L41, uniformly in $b$, gives
$K_b(t;o,o)\le C\phi_b(k_0)^2t^{-3/2}$ for $t\ge1$ and

$$
K_b(t;o,o)=\phi_b(k_0)^2
 \left[(4\pi)^{-3/2}(\det M_b)^{-1/2}t^{-3/2}
                         +O(t^{-5/2})\right].
\tag{52.7}
$$

By (51.2) the leading coefficient has a positive uniform lower
bound. Choose one fixed large $T_0$ making the error at most half
that coefficient for $t\ge T_0$. Integration on $[T_0,\infty)$
gives the lower bound for $W_{1,b}(o)$; the first estimate gives the
upper bound. Finally
$\phi_b(k_0)^2=(2/L_0)\sin^2(\pi\varepsilon b/L_0)\asymp b^2$.
Positivity alone would not have supplied this uniform lower bound.
$\square$

**Proposition 52.3 (precisely conditional local-coefficient invariance).**
All members of Definition 51.1 have the same $C_{\rm resp}$.
Whenever their common $C_{\rm resp}$ is zero, their existing coefficient
$C_4$ of §§23–24 is also the same.

Proof. The complete vector and every source jet, $d_0,\nu,j_0,a$
and $\lambda$ are identical. The canonical heat, $V,p$, homogeneous
response and each formula (3.1)–(3.7) therefore agree exactly.
Under $C_{\rm resp}=0$, the same observation applied to (23.1) and
(24.1)–(24.6) gives identical forcing, second response, $D_4$ and
$C_4$. Faces enter the native remainder, not those local formulas.
Each fixed $b>0$ has the positive source-face margins needed by those
expansions; their small-$s$ constants need not be uniform as $b\to0$.
This proves neither zero nor double-zero occurrence. $\square$

## 53. Relative heat on the full common space and moving early modes

**Definition 53.1 (original spectral tests).** For $d=b,b_{\rm ref}$
fix that admitted datum and use the exact $\Xi_s,\mathcal U_s,
\mathcal T_s$ of §2. Write $Y_s=\Xi_s\circ\mathscr L_s$ and, by
restriction and zero extension on complex $L^2(\mathbb R^4)$, set

$$
\begin{aligned}
C_d&=s^2(\mathcal T_s\mathcal U_s)S_d
                  (\mathcal T_s\mathcal U_s)^{-1},&T&=s^{-2},\\
Q_d(t)&=e^{-tC_d},&q_d(t;\eta,\xi)&=j_0s^7K_d(s^2t;Y_s\eta,Y_s\xi),\\
H_d&=\int_0^TQ_d(t)dt,&F_d&=j_0^{-1}\int_1^Tq_d(t;0,\cdot)dt,\\
J_d&=s^5W_{1,d}(Y_s\cdot),&U_d&=F_d+J_d,\\
R_d(h)&=(C_d+h)^{-1},&
\mathscr K_d(h)&=U_d^{1/2}R_d(h)U_d^{1/2},\\
k_d(h)&=\|\mathscr K_d(h)\|_{2\to2},&
A_p&=\int Vp,&\mathscr A&=(C_*+j_0A_p^2)/\mu>0.
\end{aligned}
\tag{53.1}
$$

Here $J_d$ denotes a multiplier only; it is not assumed in $L^2$.
The untransported domains are exactly (1.5) on $I_d$, for every real
phase frequency. The transported operator domain is
$(\mathcal T_s\mathcal U_s)D(S_d)$ and the form domain is
$(\mathcal T_s\mathcal U_s)\mathcal Q_d$. Both moving faces remain.

**Lemma 53.2 (relative kernel including remote endpoints).** For this
fixed pair choose a closed physical height neighborhood $J$ of $k_0$
strictly inside both intervals. For $0<t\le1$, whenever either endpoint
has height in $J$, uniformly over the other height and all phases,

$$
|(K_b-K_{\rm ref})(t;Y,Z)|\le Ct^{-7/2}e^{-c\delta^2/t},
\tag{53.2}
$$

where $\delta>0$ is fixed. For $t\ge1$ the difference is bounded
by $Ct^{-3/2}$. Consequently $(F_b-F_{\rm ref})/s^5$ is globally
bounded and tends pointwise to $\delta_b^{<}$, while on output heights
in $J$, $(H_b-H_{\rm ref})/s^5$ has globally bounded kernel tending
at every fixed microscopic endpoint pair to $j_0\delta_b^{<}$.

Proof. In the scale-one chart write the bridge as $H=A+W$, starting
at a height $A$ in the compact chart image of $J$. On paths surviving
either domain the common rational covariance is comparable to
$\int u(H)u(H)^{\mathsf T}$. The identity $u(A+W)=D_Au(W)$ from
Lemma 30.2 has $\det D_A=1$, so this covariance determinant equals
that of the relative zero-start bridge. Differing indicators force
$\sup|W|\ge\delta$, the distance from $J$ to the faces, with the
fixed height conversion absorbed into $\delta$. The phase Gaussian
supremum followed by (3.3), $m=0$, proves (53.2) for every other
endpoint, including one outside a domain. Symmetry interchanges
endpoints. The large-time bound is L41. Exact raw scaling gives

$$
\begin{aligned}
(F_b-F_{\rm ref})(\xi)
 &=s^5\int_{s^2}^1(K_b-K_{\rm ref})(t;o,Y_s\xi)dt,\\
(H_b-H_{\rm ref})(\eta,\xi)
 &=j_0s^5\int_0^1(K_b-K_{\rm ref})(t;Y_s\eta,Y_s\xi)dt.
\end{aligned}
\tag{53.3}
$$

The integrable estimate (53.2), positive-time smoothness near $(o,o)$
and dominated convergence prove every asserted limit and bound.
No compact-output approximation supplies the remote-endpoint bound.
$\square$

**Lemma 53.3 (full early vectors).** The top nonzero eigenvalue
$\ell_d$ of $H_dF_d$ has a nonnegative right eigenvector $u_d$ with
$\|u_d\|_2=1$, and

$$
\ell_d\to C_*,\quad u_d\to p\text{ in }L^2,\quad
x_d:=F_du_d\to Vp\text{ in }L^1,\quad
m_d:=\int F_du_d^2\to\mu.
\tag{53.4}
$$

The $x_d$ have bounded $L^1$ and $L^2$ norms.

Proof. P (104.6),(104.9) give $F_d\to V$ in $L^2$, bounded
$L^2$ and supremum norms, and $H_dF_d\to K_{\rm rec}$ in operator
norm. The source-fixing shears tend strongly to identity, and their
conjugation of a compact operator converges in norm, so these statements
hold in (53.1)'s coordinates. For each fixed $s$, truncating the heat
integral below a positive time makes $Q_d(t)F_d$ Hilbert–Schmidt by
the column bound and $F_d\in L^2$; the omitted norm is at most
$\delta\|F_d\|_\infty$. Thus $H_dF_d$ is compact. The symmetric
sandwich $F_d^{1/2}H_dF_d^{1/2}$ is compact too: its positive-time
squared Hilbert–Schmidt norm is at most
$\sup q_d(t)\langle F_d,Q_d(t)F_d\rangle
\le\sup q_d(t)\|F_d\|_2^2$, and the same truncation applies.
It is positive selfadjoint and its top vector can be chosen nonnegative
by the modulus Rayleigh inequality. The nonzero spectra of the two
products coincide, with multiplicities; applying $H_dF_d^{1/2}$
to that vector constructs a nonnegative $u_d$.

P87–88 identify the nonzero canonical reconstruction spectrum with
the compact canonical selfadjoint Birman–Schwinger spectrum, with
isolated simple top $C_*$. Compact spectral perturbation gives
$\ell_d\to C_*$. The equation $u_d=\ell_d^{-1}H_dF_du_d$
and compact norm convergence make these vectors precompact in the
full $L^2$ norm. Every nonnegative normalized cluster is $p$.
Cauchy–Schwarz now gives
$\|F_du_d-Vp\|_1\le\|F_d\|_2\|u_d-p\|_2+
\|F_d-V\|_2\|p\|_2\to0$; bounded multiplication bounds $\|x_d\|_2$.
Finally $u_d^2\to p^2$ in $L^1$; uniform boundedness and convergence
in measure of $F_d$ give $\int F_du_d^2\to\int Vp^2$ by truncation
against the fixed integrable $p^2$. Also $0<A_p<\infty$ since
$V,p\in L^2$ and both are positive. No rate or positive $L^2$ gap
for $H_c$ is used. $\square$

## 54. The complete relative early principal value

**Theorem 54.1 (both field and return contributions).** For each fixed
pair in Definition 53.1,

$$
\ell_b-\ell_{\rm ref}=\mathscr A\delta_b^{<}s^5+o_b(s^5).
\tag{54.1}
$$

Proof. Use conjugate-linear first slots. The two exact eigen-equations
and selfadjointness of $H_{\rm ref}$ give

$$
\begin{aligned}
(\ell_b-\ell_{\rm ref})\langle x_{\rm ref},u_b\rangle
={}&\langle x_{\rm ref},(H_b-H_{\rm ref})x_b\rangle\\
 &+\ell_{\rm ref}\langle u_{\rm ref},(F_b-F_{\rm ref})u_b\rangle.
\end{aligned}
\tag{54.2}
$$

The denominator tends to $\mu$, using bounded $F_{\rm ref}$,
$u_b-u_{\rm ref}\to0$ and (53.4). On output heights in $J$, the
first term divided by $s^5$ tends to $j_0\delta_b^{<}A_p^2$.
Indeed the normalized kernel in Lemma 53.2 is uniformly bounded;
replacing either moving $x$ by $Vp$ costs its $L^1$ error times a
bounded $L^1$ norm. Fixed-input dominated convergence then applies
on the entire product space, with the expanding indicator of $J$.

For its complementary output heights, (2.9) implies
$F_{\rm ref}\le Cs^5$, since there $|r|\ge c/s$.
Moreover $\|(H_b-H_{\rm ref})x_b\|_2\le C$: integrate contraction
on $(0,1)$ and $Ct^{-7/4}\|x_b\|_1$ on $(1,T)$, separately
for the two heats, using (29.5). Hence the omitted scalar is bounded by
$Cs^5\|\mathbf1_{\{k\notin J\}}u_{\rm ref}\|_2=o(s^5)$.
The last equality follows from full $L^2$ convergence to $p$, because
this set recedes to $|r|\ge c/s$; zero-extended domain differences
are included. For the second term in (54.2),
$u_{\rm ref}u_b\to p^2$ in $L^1$ and the bounded multiplier limit
of Lemma 53.2 gives $C_*\delta_b^{<}$ after division by $s^5$.
Dividing the sum by $\mu$ proves (54.1). $\square$

## 55. Full principal norm equality at both probes

**Theorem 55.1 (complete original relative spectral law).** For each
separately fixed admitted $b>0$, each $d=b,b_{\rm ref}$ and each
$q\in\{6,7\}$,

$$
\begin{aligned}
k_d(s^q)&=\ell_d+\mathscr A W_{1,d}(o)s^5+o_d(s^5),\\
k_b(s^q)-k_{\rm ref}(s^q)&=\mathscr A\Delta_b s^5+o_b(s^5),\\
\lim_{b\downarrow0}b^5\lim_{s\downarrow0}
 \frac{k_b(s^q)-k_{\rm ref}(s^q)}{s^5}
 &=-\mathscr A C_E/j_0<0.
\end{aligned}
\tag{55.1}
$$

In particular all sufficiently small separately fixed $b>0$ satisfy
$k_b(s^q)<k_{\rm ref}(s^q)$ for all sufficiently small $s$ depending
on $b$, at both probes. No response-zero premise is imposed.

Proof. Fix $d$ and suppress it. Put $h=s^q$, $x=Fu$, $y=Ju$,
$d_s=\int Ju^2$, $n=m+d_s$, and $z=U^{1/2}u/\sqrt n$.
These are actual early eigenvectors from Lemma 53.3, not actual ground
states; $z$ is a unit test for the full selfadjoint operator. Boundedness
and continuity of the original $W_1$ at $o$ give
$d_s/s^5\to W_1(o)$, using $u^2\to p^2$ in $L^1$.
Write

$$
H^h=\int_0^Te^{-ht}Q(t)dt,\qquad
L^h=\int_T^\infty e^{-ht}Q(t)dt,\qquad D=H-H^h,
\qquad R=H^h+L^h.
\tag{55.2}
$$

Their kernels and quadratic forms are nonnegative. Exact scaling gives

$$
s^{-5}L^h(\eta,\xi)=j_0\int_1^\infty
 e^{-(h/s^2)t}K(t;Y_s\eta,Y_s\xi)dt.
\tag{55.3}
$$

L41 bounds the integrand by $Ct^{-3/2}$ over both endpoints.
Since $h/s^2\to0$, (53.4) and dominated convergence on the full
product space yield
$\langle x,L^hx\rangle=j_0W_1(o)A_p^2s^5+o(s^5)$.
Replacing a moving input by $Vp$ costs at most its $L^1$ error
 times a bounded $L^1$ norm under this globally bounded kernel.

The damping has the input-specific estimates

$$
0\le\langle x,Dx\rangle\le
h\int_0^Tt\|Q(t/2)x\|_2^2dt\le Ch,
\qquad \|Dx\|_2\le Chs^{-1/2}.
\tag{55.4}
$$

For the first, use contraction below time one and
$\|Q(t/2)x\|_2\le Ct^{-7/4}\|x\|_1$ above it;
$\int_1^\infty t^{-5/2}dt$ is finite. For the second integrate
$ht\|Q(t)x\|_2$: its large-time integral up to $T$ is
$ChT^{1/4}=Chs^{-1/2}$. The time overlap near $T$ only changes $C$.
Furthermore $\|y\|_2\le Cs^5$ and P (104.14) imply

$$
0\le\langle y,Ry\rangle\le Cs^9h^{-1/2}=o(s^5).
\tag{55.5}
$$

Thus spectral Cauchy–Schwarz gives
$|\langle x,L^hy\rangle|\le
\langle x,L^hx\rangle^{1/2}\langle y,Ry\rangle^{1/2}=o(s^5)$,
and $|\langle y,Dx\rangle|\le Cs^5hs^{-1/2}=o(s^5)$.
As $Hx=\ell u$, the full quotient, with every long-field term retained,
is consequently

$$
\mathcal Q_s:=\langle z,\mathscr K(h)z\rangle
=\frac{\ell m+2\ell d_s+j_0W_1(o)A_p^2s^5+o(s^5)}{m+d_s}
=\ell+\mathscr A W_1(o)s^5+o(s^5).
\tag{55.6}
$$

In particular division retains one, rather than two, early cross copies.
The error estimates hold for both $q=6$ and $q=7$.

It remains to control improvement of the full principal value over this
quotient. P70 gives compactness of $\mathscr K(h)$ at each $s,h>0$.
P (104.2) gives $R(h)U\to K_{\rm rec}$ in operator norm for either
$q<8$. The nonzero spectrum of $R(h)U$ equals that of
$\mathscr K(h)$, with multiplicities, by bounded product factorization.
Compact spectral perturbation therefore gives $k(h)\to C_*$, a
single top eigenvalue separated from all the other spectrum by one
fixed positive gap, and $\|\mathscr K(h)\|\le C$.
This does not assert norm convergence of $\mathscr K(h)$ itself.

The exact unsandwiched residual is
$R(h)Uu=\ell u+e$, where $e=-Dx+L^hx+Ry$.
The early raw mass satisfies $\int F\le Cs^{-2}$: the integral of
$q(t;0,\cdot)$ is $e^{\lambda s^2t}$ times killed survival, at most
$e^\lambda$ for $t\le T$. Equation (55.3) and (29.5) give
$\|L^hx\|_\infty\le Cs^5$ and
$\|L^hx\|_2\le Cs^2h^{-1/4}\|x\|_1$.
Splitting its weighted norm into $F$ and $J$ therefore gives

$$
\begin{aligned}
\|U^{1/2}L^hx\|_2^2&\le C(s^8+s^9h^{-1/2}),\\
\|U^{1/2}Dx\|_2^2&\le Ch^2s^{-1},\\
\|U^{1/2}Ry\|_2^2
 &\le\|R^{1/2}UR^{1/2}\|\langle y,Ry\rangle
 \le Cs^9h^{-1/2}.
\end{aligned}
\tag{55.7}
$$

For the last line the middle norm equals $\|\mathscr K(h)\|$.
All these are bounded operators for fixed $h>0$; $J$ itself is
never assigned an $L^2$ norm. Since $n\to\mu>0$, (55.7) proves

$$
\| (\mathscr K(h)-\ell)z\|_2^2
 \le C(h^2s^{-1}+s^8+s^9h^{-1/2})=o(s^5).
\tag{55.8}
$$

The bound is $O(s^6)$ at $h=s^6$ and $O(s^{11/2})$ at $h=s^7$.
For completeness, if a positive selfadjoint operator has top $k$ and
remaining spectrum at most $k_2$, integrate
$(k-t)(t-k_2)\le0$ against the spectral measure of a unit vector
with quotient $\mathcal Q>k_2$. This gives
$\|(K-\mathcal Q)z\|^2\ge(k-\mathcal Q)(\mathcal Q-k_2)$.
Replacing $\ell$ by its quotient minimizes the squared residual.
The fixed gap and (55.8) thus imply $0\le k-\mathcal Q_s=o(s^5)$.
This classical variance argument is included inside the source-specific
proof so that (55.6) is upgraded to a norm equality.

The first line of (55.1) follows. Subtract it for the two fixed datasets
and apply Theorem 54.1. The exact identity
$\delta_b^{<}+W_{1,b}(o)-W_{1,\rm ref}(o)=\Delta_b$ gives the
second line; Theorem 52.2 gives the iterated limit and strict order.
No joint-uniform remainder in $(b,s)$ is asserted or used. $\square$

## 56. Exact original threshold tests and actual-infimum implications

**Theorem 56.1 (entire-complex-domain equivalence and relative order).**
For each fixed member and each $h>0$,

$$
k_d(h)\le C_*\ \Longleftrightarrow\ \epsilon_{c,d}(s)\ge-ah,
\qquad
k_d(h)>C_*\ \Longleftrightarrow\ \epsilon_{c,d}(s)<-ah.
\tag{56.1}
$$

For the small separately fixed $b$ in Theorem 55.1, at either probe,
$k_{\rm ref}(s^q)\le C_*$ implies $k_b(s^q)<C_*$ and
$\epsilon_{c,b}(s)\ge-as^q$; while $k_b(s^q)>C_*$ implies
$k_{\rm ref}(s^q)>C_*$ and $\epsilon_{c,\rm ref}(s)<-as^q$.
An eventual strict crossing for any fixed member gives, respectively,

$$
\begin{array}{c|c|c}
h&E_s&r_s\\ \hline
s^6&E_s<-as^4&r_s>as^{-2}\\
s^7&E_s<-as^5&r_s>a/s
\end{array}
\tag{56.2}
$$

In either eventual-crossing case P Theorem 105.1 gives
$\operatorname{dist}_{L^2}(\mathcal U_s\psi_s,\mathbb Tp)\to0$
for every prescribed sequence and every actual normalized complex
ground-state choice of that fixed datum, with the original $\mathcal U_s$.

Proof. On the entire transported complex form domain, exactly (2.2)
and (2.5) give

$$
q_s^c[\mathcal T_s^{-1}f]+ah\|f\|_2^2
=a\|(C_d+h)^{1/2}f\|_2^2-\chi_c\|U_d^{1/2}f\|_2^2.
\tag{56.3}
$$

Since $C_d\ge0$ and $h>0$, its square root maps that form domain
onto $L^2(\Omega_{s,d})$. The squared norm of
$U_d^{1/2}(C_d+h)^{-1/2}$ is $k_d(h)$.
Therefore nonnegativity of (56.3) for all complex $f$ is equivalent
to $k_d(h)\le a/\chi_c=C_*$, and by the actual infimum in (2.2)
is equivalent to $\epsilon_{c,d}\ge-ah$. Negation gives the strict
 equivalence. Zero extension does not change this norm or infimum.
Explicitly, for a unit top vector $z$ with $k>C_*$,
$f=R_d(h)U_d^{1/2}z\in D(C_d)$ is nonzero and its shifted form
is $a(k-\gamma k^2)<0$, $\gamma=\chi_c/a$.
Normalization supplies a lawful trial for the actual infimum; it
neither identifies a minimizer nor restricts actual states to be real.

The relative implications use only the strict norm ordering.
Using $\epsilon_c=s^2E_s=-r_ss^8$ gives (56.2).
If a crossing holds eventually then $r_s\to\infty$, so apply P105.1
directly to every prescribed actual sequence. A failure of the
 every-choice conclusion would provide failing actual choices along a
sequence and contradict that theorem. No new proof of P105 is required.
$\square$

## 57. Analytic correspondence and the absolute boundary

**Definition 57.1 (owners and mathematical scope).** The new deductions
of §§51–56 are conditional on the original ordinary analytic suppliers,
not on an absolute early spectral estimate. P70/75 own fixed-cutoff
compactness and attainment; P76/97/107 own both-face heat and the exact
rational same-bridge moments; P87–88 own specified compact reconstruction
and its simple mode; P104 owns global reconstruction and the long-field
resolvent bound. P105 is reused unchanged for actual choices.
L36/41 own the full-frequency tensor band with both endpoint factors.
The compact translated uniformity, convergent relative integral,
wall coefficient, moving early comparison, full residual and principal
norm equality are proved here, not supplied by local heat asymptotics.

The local primary interface is Colin de Verdière–Hillairet–Trélat,
*Small-time asymptotics of hypoelliptic heat kernels near the diagonal,
nilpotentization and related results*, Annales Henri Lebesgue 4,
[Theorem B, pp.915–916; §3.1 and Theorem 3.2, pp.917–922](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf).
The fields $\varepsilon\partial_k,c_\kappa(k)\cdot\partial_q$ have
zero divergence in raw measure, zero drift, and determinant nonzero
on the common larger interval, hence uniformly bounded step three.
The privileged weights are $(1,1,2,3)$ and density is $j_0d\xi$.
The killed realizations are selfadjoint contractions; after shift their
semigroups satisfy the allowed $e^{\lambda t}$ bound.
These meet the primary's smooth density, bracket, realization and
compact-interior localization hypotheses. That theorem supplies local
smoothness/nilpotentization only. Equations (52.4),(53.2) and L41,
rather than that local theorem, pay time-zero relative cancellation,
remote endpoints and infinite time. The compact spectral perturbation,
nonzero-product correspondence, Gaussian conditioning, spectral calculus
and variance inequality are classical intermediate steps. The resulting
same-source relative law is repository-derived; no worldwide novelty
or fresh global-antecedent certification is asserted.

**Definition 57.2 (unresolved absolute threshold).** The quantity
$k_{\rm ref}(s^q)-C_*$ remains unevaluated. In particular (55.1) does
not give a fifth-order expansion or enclosure for that absolute defect;
fixing a large negative relative coefficient cannot dominate an
uncontrolled reference offset. There is no response/quartic sign,
zero-response or double-zero occurrence, selected actual branch,
actual-state counterexample, physical spatial dimension, or analytic
state-preparation consequence. The original full-family target of
Definition 9.1 and its remaining doubly-zero actual scale/profile cases
remain unresolved. Local invariance is only Proposition 52.3's
conditional invariance; relative ordering is only Theorem 55.1's iterated
fixed-data statement. All full complex domains, actual-choice quantifiers,
raw source charges, original clock and both deaths remain unchanged.

## 追加锚（本行以下为增补区）

## 58. Complete finite-response reconstruction and normalized core comparison

**Definition 58.1 (fixed conditional data).** Write R, P, L and E for the sources named in R Definition 24.1. Fix one original datum of R Definition 32.1, with all its analytic antecedents: the original jointly realized signed rational source, the larger-interval probability, pole, coefficient and bracket margins of L Definition 35.1, L Lemma 41.2, P §§76, 87–88, 97, 104–107 and E Theorem 3.1. Assume $C_{\rm resp}=C_4=0$, without asserting that this stratum occurs. Fix the physical cutoff $\chi$ of R Definition 52.1, both source-to-face and denominator margins and a sufficiently small estimating $\ell>0$ before $s\downarrow0$. All constants below may depend on these fixed data. Retain the raw source and measure, both original Dirichlet faces, every real phase frequency and the full complex form and operator domains of R (1.5), transported by $\mathcal T_s\mathcal U_s$ and zero extended as in R (32.4).
Use the actual normalized Fredholm charges $g_0,\ldots,g_4$ of §§31, 36–45, with their owning equations and $\langle p,g_i\rangle=\delta_{i0}$, not arbitrary trial charges. In particular $g_1,g_2\in L^1$, $\omega^{6-i}g_i\in L^2$ for $i=1,2,3$, $g_3\in L^{6/5}$, and all five charges have fixed $L^2$ norms; these are (38.1), (44.3), (45.3) and R (24.29). The supplied charge regularity and lawful complex both-face pairings retain their ordinary conditional scope. No additional regularity of $g_4$ is required below. Let $p>0$, $\|p\|_2=1$, $\mu=\int Vp^2>0$, $\gamma=C_*^{-1}$ and $u_s$ be the positive unit early vector of Lemma 53.3. Keep its compact reconstruction convergence and isolated algebraically simple nonzero mode. Define
$$
T=s^{-2},\quad q_s(t;\eta,\xi)=j_0s^7e^{\lambda s^2t}p^B_{s^2t}(Y_s\eta,Y_s\xi),\quad H_s=\int_0^TQ_s(t)dt,\quad F_s=j_0^{-1}\int_1^Tq_s(t;0,\cdot)dt,\quad N_s=F_sH_s,\quad N_0=VG_0,\quad G_s=\sum_{i=0}^4s^ig_i,\quad E_s=(N_s-C_*)G_s.
\tag{58.1}
$$
Here $E_s$ denotes this residual, not the actual energy denoted by the same letter in R (32.5); $N_0$ is the bounded product, not a full-space threshold inverse. Multiplication follows the return. The $B$-clock is independent of $a$; $j_0^{-1}$ belongs only to the field. All complete coefficients include their $\nu$ and $\lambda$ terms. Every finite probe $M$ used below is fixed separately before $s\downarrow0$.

**Theorem 58.2 (complete response and finite-return left vector).** Under Definition 58.1, for all sufficiently small $s$,
$$
\|H_sE_s\|_2\le C_ds^4,\qquad z_s:=\frac{H_sG_s}{\|H_sG_s\|_2}\ \text{is defined},\qquad \|z_s-u_s\|_2\le C_ds^4.
\tag{58.2}
$$
The orientation is the positive $p$ orientation. Before zero extension $H_sG_s$ belongs to the original transported operator domain, including both faces.

Proof. First establish two response bounds on the entire common space. The group (2.6) has weights $(1,1,2,3)$, homogeneous dimension seven and unit Lebesgue Haar measure; left translation gives $X,Y$ and $d_E(\eta,\xi)=\rho(\eta^{-1}\xi)$. Set $N=(r^{12}+y^{12}+z^6+w^4)^{1/12}$. It is positive and smooth off zero, homogeneous of degree one; $\kappa=N^{-5}$ is smooth off zero and has degree $2-7$. Its radial singularity has finite integral $\int_0^1r^{6-5}dr$. Thus it is a type-two distribution in Fischer–Ruzhansky, *Sobolev spaces on graded groups*, [arXiv:1311.0192v1, §2.1, Definition 2.3 and the positive-order paragraph](https://arxiv.org/html/1311.0192v1#S2.SS1). Proposition 2.1 gives $\rho^{-5}\le C\kappa$. R (45.3) therefore gives $|H_sh|\le C(|h|*\kappa)$ with exactly the input-first convolution of (30.1). The primary's Theorem 2.4 applies with $\nu=2$, $Q=7$, $p=14/11$, $q=2$: both exponents are interior and $1/p-1/q=2/7$. Consequently
$$
\|H_sh\|_2\le C\|h\|_{14/11},\qquad \|H_sh\|_2\le CT\|h\|_2.
\tag{58.3}
$$
The first inequality is initially on compact inputs; simultaneous approximation in $L^{14/11}\cap L^2$ identifies its extension with the original finite-time $H_s$, since the two limits agree locally in measure. The second follows from the shifted killed contractions, whose norm is at most $e^\lambda$ for $t\le T$. Absolute domination treats complex inputs and zero-extended outputs. Only the majorant is homogeneous; no homogeneity of the native killed kernel, critical time-norm integration, or inverse at native kinetic threshold is used.

For completeness retain the exact entire residual partition. Put $m_i=4-i$, $R_{i,s}=H_sg_i-\sum_{j=0}^{m_i}s^jG_jg_i$, $\mathfrak F_{n,s}=F_s-\sum_{k=0}^ns^kV_k$ and $D_s=N_s-N_0$. R (24.24), (24.26), (24.40)–(24.41), including $\rho=-C_4/(a\gamma^2\mu)=0$, give
$$
E_s=\sum_{i=0}^3s^i\left[F_sR_{i,s}+\sum_{j=0}^{4-i}s^j\mathfrak F_{4-i-j,s}(G_jg_i)\right]+s^4D_sg_4.
\tag{58.4}
$$
All bounds in the following partition apply to complete products, in this factor order.

For $i=0$, (31.4) is the complete both-face return estimate, including noncompact input, actual and safe remote inputs, every coefficient deletion and every $t>T$ restoration. R (45.3) gives $\|q_s(t;0,\cdot)\|_{14/11}\le Ct^{-3/4}$ and hence $\|F_s\|_{14/11}\le Cs^{-1/2}$. Thus $\|F_sR_{0,s}\|_{14/11}\le Cs^{9/2}(1+|\log s|)$. For its five field products, in order $j=0,\ldots,4$, choose
$$
(P,q)=(8,56/37),(4,28/15),(8/3,56/23),(15/8,210/53),(3/2,42/5).
\tag{58.5}
$$
Each reciprocal sum is $11/14$. For $j=0$, $G_0g_0=p/(\gamma\mu)$ has the required norm by $|p|\le C(1+\rho)^{-5}$. For $j\ge1$, apply (30.4) to every $n+m=j$ with seed input exponents $(p_0,\ldots,p_4)=(1,1,1,7/6,7/5)$, justified by $(10-n)p_n>7$ in (31.3). Above time one the respective largest powers at the four chosen outputs are $-9/8,-17/16,-67/60,-13/12$, all below $-1$. Below one the same envelope gives each weighted $L^q$ input, and the $L^1$ kernel gives integrable $t^{m/2}$. Lemma 32.1 applies with $n=4-j<\alpha_P=5-7/P$, including its source-path, retained-coefficient and infinite-time restorations. The five total input powers, including $s^j$, are $33/8,17/4,35/8,64/15,13/3$. By (58.3) all six seed responses are $O(s^{33/8})$.

For $i=1,2,3$, split $R_{i,s}$ by the fixed height $|r|=L/4$, $L=\ell/s$, and Taylor expand only the inner safe heat through $4-i$, keeping $L,T$ fixed under differentiation. At derivative $k=5-i$, R (24.8) with output two and weighted $L^2$ inputs controls $t<1$ by integrable powers $t^{(k-n)/2}$. Multiplication by the uniformly bounded $L^{7/2}$ norm of $F_s$ gives output $14/11$. Above one use output infinity and exactly the following R (24.34) lists, indexed by $n=0,\ldots,k$:
$$
\begin{array}{c|c|c}
i&(p_n)&\text{time powers}\\ \hline
1&(1,1,7/6,7/5,7/4)&(-3/2,-2,-2,-2,-2)\\
2&(1,7/6,7/5,7/4)&(-2,-2,-2,-2)\\
3&(6/5,18/13,18/11)&(-23/12,-73/36,-77/36)
\end{array}
\tag{58.6}
$$
Every power is strictly integrable and each membership follows from (38.1), (43.4), (44.3), (45.3), not from arbitrary charge moments. Multiplying by $F_s\in L^{14/11}$ costs $s^{-1/2}$; the Taylor and exterior charge factors together are $s^5$. Each of these three responses is therefore $O(s^5+s^{9/2})$. This uses finite-time strip derivatives, not derivatives of a nonzero-parameter infinite-time return.

Here are all nine lower field products in (58.4). The last column is their full $L^{14/11}$ input power, including $s^{i+j}$; $q$ is the norm of $G_jg_i$ and $P$ that of the field remainder.
$$
\begin{array}{c|c|c|c|c|c}
i&j&P&q&\alpha_P&\text{power}\\ \hline
1&0&210/53&15/8&97/30&127/30\\
1&1&70/27&5/2&23/10&43/10\\
1&2&42/19&3&11/6&29/6\\
1&3&28/15&4&5/4&5\\
2&0&7/2&2&3&5\text{ with }(1+|\log s|)\\
2&1&70/27&5/2&23/10&5\\
2&2&42/19&3&11/6&5\\
3&0&7/2&2&3&5\\
3&1&70/27&5/2&23/10&5
\end{array}
\tag{58.7}
$$
Indeed every row has $1/P+1/q=11/14$ and $n=4-i-j<\alpha_P$. The complete Lemma 32.1 remainder has power $\min(n+1,\alpha_P)$, with its stated equality logarithm, giving the table. To verify all return norms, interpolate $g_1,g_2\in L^1$ with $\omega^{6-i}g_i\in L^2$: if $\theta=2(1-1/p)$ then $\omega^{(6-i)\theta}g_i\in L^p$. For input degrees $n=0,1,2,3$ use $(1,7/6,7/5,7/4)$; the available weights exceed or equal $n$. In every split $n+m=j$ above one, (30.4)'s power is $j/2-7/2+7/(2q)$. For $(j,q)=(1,5/2),(2,3),(3,4)$ these are $-8/5,-4/3,-9/8$; the $j=0$ rows have powers $-49/30,-7/4$. For $g_3$, interpolate its actual $L^{6/5}$ and $\omega^3L^2$ norms: use $p_0=6/5$, $p_1=18/13$. The powers are $-7/6$ at $(j,q)=(0,2)$ and $-61/60,-203/180$ for the two splits at $(1,5/2)$. Below one, weighted $L^2$ inputs handle every $q\ge2$, with worst power $-7/8$; the sole $q<2$ case $G_0g_1\in L^{15/8}$ follows from its interpolated $L^{15/8}$ input and the $L^1$ kernel. Thus all endpoints are integrable. The sole field logarithm satisfies $s^5(1+|\log s|)=O(s^4)$; the other powers exceed four. Apply (58.3) to these full restored products.

Restore the rest of the three lower-return partitions individually. R (24.35)–(24.36) and Lemma 41.2 give exterior $L^2$ powers at least $6,7,41/6$ for $i=1,2,3$, respectively, for original inner path deletions, every retained coefficient safe-path deletion and every forced coefficient tail $t>T$. Both actual and safe remote-input joint products separately have power six, by R Lemma 41.1 and $\|g_i^{\rm out}\|_2\le CL^{-(6-i)}$. The second channel in (58.3) gives response powers at least $4,5,29/6$ and four, respectively. The covariance comparison uses the original denominator margins even on surviving paths outside the safe strip. Safe paths cannot end beyond either original face; thus these restorations cover the zero-extended output as well.

There remain exactly nineteen retained remote coefficient products $s^{i+k+j}V_kG_jg_i^{\rm out}$: for $i=1$, $k=0,1,2,3$ have $j=0,\ldots,3-k$; for $i=2$, $k=0,1,2$ have $j=0,\ldots,2-k$; for $i=3$, $k=0,1$ have $j=0,\ldots,1-k$. R (41.8)–(41.10) give $L^2$ power at least six for fourteen of them, with every $n+m=j$ retained; (58.3) pays them. The five remaining index triples $(i,k,j)$ are $(1,0,3),(1,2,0),(2,2,0),(1,2,1),(1,3,0)$. For $g_1,g_2$, the preceding interpolation gives on the remote set
$$
\|r^ng_i^{\rm out}\|_p\le CL^{-((6-i)\theta-n)},\quad \theta=2(1-1/p),\quad 1\le p\le2,\quad n\le(6-i)\theta.
\tag{58.8}
$$

With field norm $P$ and return output $q$, require $1/P+1/q=11/14$. For a split $n+m=j$ the ordered kernel power is $m/2-(7/2)(1/p-1/q)$ and the exterior $s$ power is $i+k+m+(6-i)\theta$. The complete choices above time one are:
$$
\begin{array}{c|c|c|c|c}
(i,k,j)&(P,q)&(m,n,p)&\text{time powers}&\text{total }s\text{ powers}\\ \hline
(1,0,3)&(7/4,14/3)&(0,3,3/2),(1,2,4/3),(2,1,8/7),(3,0,1)&-19/12,-11/8,-21/16,-5/4&13/3,9/2,17/4,4\\
(1,2,0),(2,2,0)&(3,42/19)&(0,0,6/5)&-4/3&14/3,\ 16/3\\
(1,2,1)&(3,42/19)&(0,1,6/5),(1,0,1)&-4/3,-17/12&14/3,4\\
(1,3,0)&(4,28/15)&(0,0,1)&-13/8&4
\end{array}
\tag{58.9}
$$
Every listed $p\le q$ satisfies (58.8), and every time power is below $-1$. Below one, the first row uses $V\in L^{7/2}$, output two and weighted remote $L^2$ inputs, with powers $t^{m/2}$ and exterior power at least six. The middle rows keep $P=3,q=42/19$, with weighted remote $L^2$ inputs giving $t^{m/2-1/6}$ and exterior power at least six. The last row uses $p=q=28/15$ and the $L^1$ kernel: $\theta=13/14$ gives available weight $65/14$, and total power $4+65/14$. These are splits of the same coefficient integral at one. The fields really have these norms: integrating (32.3) gives $V_k\in L^P$ whenever $k<5-7/P$, strictly satisfied for $(k,P)=(0,7/4),(0,7/2),(2,3),(3,4)$. Thus (58.9) pays all splits in all five products by the first channel of (58.3); none is discarded.

Finally R (45.3) gives uniform $F_s,V\in L^r$ for each fixed $r>7/5$. For $t<1$, use $F_s\in L^3$ and the $2\to2$ heat bound to obtain an integrable $2\to6/5$ product bound. For $1<t<T$, use $F_s\in L^{42/29}$ and $Q_s(t):L^2\to L^7$; $29/42+1/7=5/6$ and R (45.6) gives the integrable power $-5/4$. Hence $N_s:L^2\to L^{6/5}$ is uniformly bounded. The identical canonical estimates define $N_0$ as $\int_0^\infty VP_tdt$ in both $L^{6/5}$ and $L^2$; the latter product is R Lemma 41.1. On compact inputs these are the actual products, and density with both target-space bounds identifies their versions. This does not require an unweighted $G_0$ on arbitrary $L^2$. Since R (41.1) gives $\|D_s\|_{2\to2}=O(s^{4/7})$, spatial interpolation yields
$$
\|D_s\|_{2\to14/11}\le \|D_s\|_{2\to6/5}^{6/7}\|D_s\|_{2\to2}^{1/7}\le Cs^{4/49},\qquad
\|H_s[s^4D_sg_4]\|_2\le Cs^{4+4/49}.
\tag{58.10}
$$
Here $11/14=(6/7)(5/6)+(1/7)(1/2)$, and only the fixed $L^2$ norm of $g_4$ is used. All native times remain finite and both deaths remain present. Adding the six seed terms, three safe Taylor blocks, nine fields, all restorations, all nineteen remote products and the last charge in (58.4) proves the first bound in (58.2), without cancellation or sign.

For the vector assertion put $v_s=H_sG_s$. R (24.16) gives $H_sg_0=(C_*/\mu)p+O_{L^2}(s)$. For $i=1,2,3$, their owned $L^{6/5}\cap L^2$ memberships, contraction below one and the integrable $t^{-7/6}$ bound above one give uniformly bounded $H_sg_i$. For $g_4$, $s^4\|H_sg_4\|_2=O(s^2)$ by (58.3). Thus $v_s=(C_*/\mu)p+O_{L^2}(s)$, with positive nonzero leading coefficient.

Spectral calculus on the native realization gives $C_sH_sh=(I-Q_s(T))h$ and $H_sh\in D(C_s)$ for $h\in L^2(\Omega_s)$, followed by zero extension; it preserves both Dirichlet faces. The exact bounded-product identity is $(L_s-C_*)v_s=H_sE_s$, where $L_s=H_sF_s$. By Lemma 53.3 and R Lemma 24.4, $L_s\to K_{\rm rec}$ in norm with isolated algebraically simple eigenvalue $C_*$. On the complementary range of its rank-one Riesz projection $P_s$, the inverse of $L_s-C_*$ is uniformly bounded: fix a contour separating $C_*$ from the remaining limiting spectrum and use norm convergence of resolvents, also at $C_*$ on the complementary range. Therefore $\|(I-P_s)v_s\|_2\le C\|H_sE_s\|_2$. The real vector $P_sv_s$ is a scalar multiple of $u_s$, with scalar tending to $C_*/\mu>0$. Normalizing $v_s$, whose norm is bounded away from zero, gives the second bound in (58.2). This is spectral isolation of compact reconstruction, not a positive native kinetic threshold gap. $\square$

**Theorem 58.3 (entire normalized retained-core comparison).** Under Definition 58.1, define every tilde quantity by substituting the vector $z_s$ of Theorem 58.2 for $u_s$ in the following exact R (24.42), (52.1) core, consistently in every occurrence:
$$
\begin{gathered}
x_s=F_su_s,\quad m_s=\int F_s|u_s|^2,\quad \delta_s=s^5\int f(Y_s\xi)|u_s|^2d\xi,\quad n_s=m_s+\delta_s,\quad d_s=\langle G_s,u_s\rangle,\quad R_s=\langle E_s,u_s\rangle,\\
\delta_{\chi,s}=s^5\int P_\chi(Y_s\xi)|u_s|^2d\xi,\quad
Q_{\chi,s}=j_0s^5\iint\Pi_\chi(Y_s\eta,Y_s\xi)\overline{x_s(\eta)}x_s(\xi)d\eta d\xi,\quad
c_s=\frac{n_s+\delta_{\chi,s}}{d_s},\\
\mathcal J_s=c_sR_s+C_*\delta_{\chi,s}+Q_{\chi,s}=n_s(\mathcal C_{\chi,s}-C_*),\qquad
\widetilde{\mathcal C}_{\chi,s}:=C_*+\frac{\widetilde c_s\langle E_s,z_s\rangle+C_*\widetilde\delta_{\chi,s}+\widetilde Q_{\chi,s}}{\widetilde n_s}.
\end{gathered}
\tag{58.11}
$$
Here $f=W_{1,d}$ is the full long field in physical variables, whereas $P_\chi=\chi\mathcal T_3f$ is the retained polynomial. The kernel $\Pi_\chi$ keeps the sum of the two endpoint weighted degrees at most three. In particular the denominator contains the full $\delta_s$, not $\delta_{\chi,s}$. Then both exact and substituted denominators $n_s,d_s$ are nonzero for small $s$, and
$$
|\widetilde{\mathcal C}_{\chi,s}-\mathcal C_{\chi,s}|
\le C_{d,\chi}\bigl(s^{65/8}+s^9+s^{13}\bigr)=o(s^8).
\tag{58.12}
$$

Proof. Put $\epsilon_s=\|z_s-u_s\|_2$. Both vectors have norm one. Bounded $f,P_\chi$ give $|\widetilde\delta_s-\delta_s|+|\widetilde\delta_{\chi,s}-\delta_{\chi,s}|\le Cs^5\epsilon_s$. Uniform boundedness of $F_s$ and the fixed $\|G_s\|_2$ give $|\widetilde m_s-m_s|+|\widetilde n_s-n_s|+|\widetilde d_s-d_s|\le C\epsilon_s$. Since $n_s\to\mu>0$, $d_s=1+O(s)$ and $\epsilon_s\to0$, all four denominators are bounded away from zero, and $|\widetilde c_s-c_s|\le C\epsilon_s$. The inherited tested identity R (24.39), (24.42) gives $R_s=O(s^5)$; independently R (41.7) gives $|\langle E_s,z_s-u_s\rangle|\le Cs^{33/8}\epsilon_s$.
For the late term put $e_s=F_s(z_s-u_s)$. Uniform $F_s\in L^2$ gives $\|x_s\|_1\le C$ and $\|e_s\|_1\le C\epsilon_s$. If $B_\chi$ is the sesquilinear pairing with kernel $\Pi_\chi(Y_s\eta,Y_s\xi)$, the exact difference is $j_0s^5[B_\chi(e_s,x_s)+B_\chi(x_s,e_s)+B_\chi(e_s,e_s)]$. The kernel is bounded, so this costs $Cs^5(\epsilon_s+\epsilon_s^2)$, retaining both single-input terms and the cross term. Also $\delta_{\chi,s},Q_{\chi,s}=O(s^5)$ and $c_s=O(1)$, so the entire numerator $\mathcal J_s$ is $O(s^5)$. Changing $c_s$ costs $Cs^5\epsilon_s$; changing the final division by $n_s$ costs the same, using its positive lower bound and $|\widetilde n_s-n_s|=O(\epsilon_s)$. Thus
$$
|\widetilde{\mathcal C}_{\chi,s}-\mathcal C_{\chi,s}|\le C\{s^{33/8}\epsilon_s+s^5(\epsilon_s+\epsilon_s^2)\}.
\tag{58.13}
$$
Insert $\epsilon_s=O(s^4)$ from (58.2). The three powers are $65/8,9,13$, all strictly larger than eight, proving (58.12). No condition $\mathfrak m_d=0$ entered. R Theorems 52.3 and 54.1 may consequently use the substituted core with the same $o_{d,M,\chi}(s^8)$ remainder, keeping the complete-minus-retained mass, both single-outer late inputs, the two-outer term and joint subtraction; each finite $M$ remains separately fixed. The known $s^8\log(1/(Ms^6))$ uplift in R Theorem 49.2 is unchanged. The entire approximant in (58.11) remains unsigned; its precision supplies no strict selecting inequality, actual-state branch, phase-orbit convergence or source-family obstruction. Zero-stratum occurrence, analytic $L^2$ preparation and physical spatial dimension remain unresolved. The comparison is a repository-derived conditional deduction; the cited Fischer–Ruzhansky interface and classical spectral calculus, Riesz projection and interpolation steps are intermediate results, not novelty claims. The underlying analytic suppliers are not independently recertified here. $\square$

## 追加锚（本行以下为增补区）
