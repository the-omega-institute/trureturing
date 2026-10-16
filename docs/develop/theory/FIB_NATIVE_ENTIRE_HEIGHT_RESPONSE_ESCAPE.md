# Native entire-height response escape

For the original rational native family, the homogeneous critical response has a strictly positive component orthogonal to the entire closed space of odd height multipliers. This volume proves strong tails for the same reconstructed mode and its first horizontal derivatives, determines the limiting slope of its full height projection, and constructs a compact odd response test giving a quantitative positive residual. All statements are ordinary conditional mathematics under the analytic antecedents specified below. The absolute complete signs and the general response-zero actual selection remain unresolved.

Write P for [Native full-state weak binding](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md), through §108; R for [Native exact-critical energy response and scale alternatives](FIB_NATIVE_EXACT_CRITICAL_ENERGY_RESPONSE_AND_SCALE_ALTERNATIVES.md), through §15; N for *Strict nonaffine response at the native critical scale*; A for [Actual critical solvability and conditional microscopic disappearance](FIB_NATIVE_ACTUAL_CRITICAL_SOLVABILITY_AND_MICROSCOPIC_DISAPPEARANCE.md), through §12; and H for *Native critical height projection and cutoff overlap bounds*. Numbered results from those sources are reused at their stated scopes. In particular A Theorems 10.2 and 11.1 and Corollary 12.1 already give the matching Coulomb energy and full-mass macroscopic profile for actual microscopic weak-zero sequences.

## 1. The original family and the conditional canonical problem

**Definition 1.1 (native data, source and full complex domains).** Fix one original admitted signed $\kappa\ne0$, $H$, $I=(l,u)$, $k_0\in I$, and $a,\varepsilon>0$, retaining every original probability, interval and denominator restriction. Put

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

The entire original vector $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$, including its third component, obeys the exact identity

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

All jets belong to this one original vector; none is freely chosen. The denominator has a positive margin on $\overline I$. On $\mathcal C=I\times\mathbb R^3$, $q=(\theta,v,x)$, use raw measure $dY=dk\,dq$ and

$$
B=-\varepsilon^2\partial_k^2-(c_\kappa(k)\cdot\partial_q)^2,
\qquad S=B-\lambda\ge0.
\tag{1.3}
$$

Both height endpoints are Dirichlet. With unitary phase Fourier factor $(2\pi)^{-3/2}$ and $B_\eta=-\varepsilon^2\partial_k^2+|\eta\cdot c_\kappa(k)|^2$, the complete complex domains, including underlying $L^2(dY)$ membership, are

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

Thus $\mathcal Q=D(S^{1/2})=D(B^{1/2})$. Every real phase frequency and every complex state in these domains is retained. No ordinary phase $H^1$, reality, parity or height-product restriction is imposed on native competitors.

For the killed heat kernel $p_t^B$ in raw measure and pole $o=(k_0,0)$, retain exactly

$$
\begin{aligned}
W_\tau&=\int_\tau^\infty e^{\lambda t}p_t^B(o,\cdot)dt,&
\rho_\tau&=e^{\lambda\tau}p_\tau^B(o,\cdot),&SW_\tau&=\rho_\tau,\\
\int\rho_\tau dY&=e^{\lambda\tau}\mathbb P_{k_0}(\zeta>\tau),&
\int\phi(k)\rho_\tau(k,q)dk\,dq&=\phi(k_0),\\
\mathfrak e_{g,\tau}[\psi]&=a\|S^{1/2}\psi\|_2^2-g\int W_\tau|\psi|^2dY,&
E_\tau(g)&=\inf_{\psi\in\mathcal Q,\ \|\psi\|_2=1}\mathfrak e_{g,\tau}[\psi].
\end{aligned}
\tag{1.5}
$$

The raw and $\phi$-weighted charges differ, without survival renormalization. The field clock is $B$, independently of $a$. P Propositions 70.2 and 75.2 supply, separately at each positive $g,\tau$, a bounded multiplier, operator $aS-gW_\tau$ on exactly $D(S)$, and finite negative attained bottom. The exact path is

$$
\tau=s^2,\qquad g_s=\chi_cs^3,\qquad E_s=E_{s^2}(\chi_cs^3),\qquad
\epsilon_c(s)=s^2E_s,\qquad r_s=-\epsilon_c(s)/s^8=-E_s/s^6>0.
\tag{1.6}
$$

**Definition 1.2 (unchanged microscopic dictionary).** For $\xi=(r,y,z,w)$ use

$$
\begin{aligned}
\Xi_s\xi&=(k_0+\varepsilon sr,
 s c_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w),\\
I_s&=((l-k_0)/(\varepsilon s),(u-k_0)/(\varepsilon s)),&
\Omega_s&=I_s\times\mathbb R^3,\\
\mathcal U_s\psi&=(j_0s^7)^{1/2}\psi\circ\Xi_s,&
\mathcal Q_s&=\mathcal U_s\mathcal Q,&U_s&=s^5W_{s^2}\circ\Xi_s,\\
X&=\partial_r,&Y_s&=\partial_y+r\partial_z+\frac{r^2}{2(1+\beta_sr)}\partial_w,&
\beta_s&=\nu s.
\end{aligned}
\tag{1.7}
$$

The raw Jacobian is $j_0s^7$ and $\mathcal U_s$ is unitary. If $b_s[F]=\|XF\|_2^2+\|Y_sF\|_2^2$ has Friedrichs operator $A_s$, then

$$
\begin{aligned}
D(A_s)&=\mathcal U_sD(S),&C_s&=A_s-\lambda s^2=s^2\mathcal U_sS\mathcal U_s^{-1}\ge0,\\
q_s^c[F]&=a b_s[F]-\chi_c\int U_s|F|^2-a\lambda s^2\|F\|_2^2,&
q_s^c[\mathcal U_s\psi]&=s^2\mathfrak e_{g_s,s^2}[\psi].
\end{aligned}
\tag{1.8}
$$

The determinant-one phase shear is $\mathscr L_s(r,\mathbf z)=(r,L_s\mathbf z)$, $\mathcal T_sF=F\circ\mathscr L_s$, where

$$
L_s=\begin{pmatrix}1&\beta_s&0\\0&1&2\beta_s\\0&0&1\end{pmatrix},\qquad
Y=\partial_y+r\partial_z+\tfrac12r^2\partial_w,\qquad
b_s[\mathcal T_s^{-1}f]
=\int_{\Omega_s}\bigl(|Xf|^2+(1+\beta_sr)^{-2}|Yf|^2\bigr)d\xi.
\tag{1.9}
$$

This is an exact closed-form identity, preserving the source and both moving deaths. Comparisons use zero extension. The corresponding heat and source are

$$
\begin{aligned}
P_s(t;\eta,\xi)&=j_0s^7p_{s^2t}^B(\Xi_s\eta,\Xi_s\xi),\\
U_s&=j_0^{-1}\int_1^\infty e^{\lambda s^2t}P_s(t;0,\cdot)dt,&
(A_s-\lambda s^2)U_s&=s^7\rho_{s^2}\circ\Xi_s.
\end{aligned}
\tag{1.10}
$$

**Definition 1.3 (conditional heat, mode and energy space).** On the same Engel group use

$$
\begin{aligned}
(r,y,z,w)(r',y',z',w')
 &=(r+r',y+y',z+z'+ry',w+w'+rz'+r^2y'/2),\\
\delta_R(r,y,z,w)&=(Rr,Ry,R^2z,R^3w),\qquad Q_{\rm hom}=7.
\end{aligned}
\tag{1.11}
$$

Unit Lebesgue measure is Haar measure. Let $b[u]=\|Xu\|_2^2+\|Yu\|_2^2$, let $\mathcal Q_E$ be the complex compact smooth core closure in $\|u\|_2^2+b[u]$, and let $\mathcal E=-X^2-Y^2$ be its Friedrichs operator. Retain the conservative, symmetric, positive heat $P_t=e^{-t\mathcal E}$, $k_t=p_E(t;0,\cdot)$, proper continuous homogeneous control metric $d$, and the supplied bounds and mode

$$
\begin{gathered}
p_E(t;\eta,\xi)\le Ct^{-7/2}e^{-c d(\eta,\xi)^2/t},\qquad
N=\max(|r|,|y|,|z|^{1/2},|w|^{1/3}),\qquad d(0,\xi)\ge cN(\xi),\\
V=j_0^{-1}\int_1^\infty k_tdt>0,\qquad
\mathcal EV=j_0^{-1}k_1,\qquad V\le C(1+N)^{-5},\\
C_* =\sup_{0\ne u\in\mathcal Q_E}\frac{\int V|u|^2}{b[u]}\in(0,\infty),\qquad
\chi=\chi_c=a/C_*,\qquad\gamma=\chi/a,\\
h[u]=a b[u]-\chi\int V|u|^2\ge0,\qquad h_0=h/a,\qquad
p=\Phi_c>0,\quad\|p\|_2=1,\quad p\in D(\mathcal E),\\
\mathcal Ep=\gamma Vp,\qquad\ker(a\mathcal E-\chi V)=\mathbb Cp,\qquad
p=\gamma\int_0^\infty P_t(Vp)dt\quad\text{in }L^2.
\end{gathered}
\tag{1.12}
$$

The metric has Haar-ball volume $v_d R^7$. The smoothness and hypoellipticity used below are those of the supplied canonical heat and operator. The potential $V$ is smooth and has a positive minimum on every compact set. P §§82–88 own these conditional statements and the compact reconstruction on specified multiplier right sides. They supply no inverse on general $L^2$.

P §106 supplies $rp\in\mathcal Q_E$, $h[rp]=a$, and $\int r^2(p^2+|Xp|^2+|Yp|^2)<\infty$. The involution $\sigma(r,y,z,w)=(-r,y,-z,w)$ fixes $p,V$; $X$ reverses parity and $Y$ preserves it. R §§4–5 supply the homogeneous gap and response. On the completion $\dot{\mathcal H}_-$ of the real odd compact smooth core in $\sqrt b$,

$$
\begin{gathered}
a\theta b\le h\le ab,\quad\theta>0,\qquad
\int V|u|^2\le C_*b[u],\\
\ell(u)=2a\int r(Yp)(Yu)+\chi\int V_1pu,\qquad
h(\Psi,u)=\ell(u),\qquad D_{\rm resp}=h[\Psi]<\infty.
\end{gathered}
\tag{1.13}
$$

The response $\Psi$ has only this real homogeneous meaning; no global $L^2$ or native-domain membership is assumed. Polarized forms on complex spaces are conjugate linear in their first slot. The new response arguments below use real vectors.

**Definition 1.4 (every complete coefficient).** On one height bridge $H_v$ with generator $\partial_r^2$, from zero to $r$ in time $t$, put

$$
\begin{aligned}
u(h)&=(1,h,h^2/2),&M_j&=\int_0^tH_v^j u(H_v)u(H_v)^{\mathsf T}dv\quad(j=0,1,2),\\
\gamma_M(\mathbf z)&=(4\pi)^{-3/2}(\det M)^{-1/2}e^{-\mathbf z^{\mathsf T}M^{-1}\mathbf z/4},&
h_t(r)&=(4\pi t)^{-1/2}e^{-r^2/(4t)},\\
p_1(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[-2D\gamma_{M_0}(\mathbf z)[M_1]],\\
p_2(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[
3D\gamma_{M_0}(\mathbf z)[M_2]+2D^2\gamma_{M_0}(\mathbf z)[M_1,M_1]],\\
V_j&=j_0^{-1}\int_1^\infty p_j(t;\cdot)dt\quad(j=1,2),&
V_{\rm t}&=j_0^{-1}\int_1^\infty t k_tdt>0.
\end{aligned}
\tag{1.14}
$$

Here $D\gamma$ differentiates the positive matrix, with phases fixed. The matrices and mode are jointly realized. P §107 supplies absolute convergence, odd $V_1$, even $V_2,V_{\rm t}$, $|V_1|\le C(1+|r|)^{-4}$, $|V_2|+V_{\rm t}\le C(1+|r|)^{-3}$, and

$$
\widetilde U_s:=U_s\circ\mathscr L_s
=V+\beta_sV_1+\beta_s^2V_2+\lambda s^2V_{\rm t}+\mathcal R_s,
\qquad\|\mathcal R_s\|_\infty\le Cs^{5/2}.
\tag{1.15}
$$

This inherited expansion includes every real phase, both moving faces, zero extension and the complete infinite-time native field. R supplies $V_j^2\le K_jV$, $V_{\rm t}^2\le K_{\rm t}V$ and their homogeneous multiplier bounds. None of these fields uses the clock $aB$.

Set

$$
\begin{aligned}
A&=\int r^2|Yp|^2,&B_1&=\int rV_1p^2,&C_2&=\int V_2p^2,&T&=\int V_{\rm t}p^2>0,\\
t_0&=2A+\gamma B_1,&K_{\rm base}&=3aA-\chi C_2,&D_{\rm clock}&=a+\chi T,\\
C_{\rm resp}&=\nu^2(K_{\rm base}-D_{\rm resp})-\lambda D_{\rm clock},\\
C_{108}&=\nu^2\{a(1-A)-\chi(C_2+2B_1)\}-\lambda(a+\chi T),\\
G_{\rm resp}&=3A-\gamma C_2-D_{\rm resp}/a,&
G_{108}&=1-A-\gamma(C_2+2B_1),\\
\overline D&=1+\gamma T,&\mathscr R&=\lambda/\nu^2=\pi^2d_0^2/L_I^2,\qquad
\frac{C_X}{a\nu^2}=G_X-\mathscr R\overline D\quad(X={\rm resp},108).
\end{aligned}
\tag{1.16}
$$

All integrals are over the entire canonical Haar space. Thus $A=A_2$, $C_2+2B_1=J_2$ and $T=J_{\rm t}$ of P §108. Every rational kinetic, source, field-clock and threshold term remains present.

## 2. The existing full height projection and auxiliary kernel

**Definition 2.1 (credited projection).** H §§3–6 establish the following marginal, force and projection dictionary:

$$
\begin{aligned}
\rho(r)&=\int_{\mathbb R^3}p(r,\mathbf z)^2d\mathbf z,&
m_Y(r)&=\int_{\mathbb R^3}|Yp(r,\mathbf z)|^2d\mathbf z,\\
v_1(r)&=\int_{\mathbb R^3}V_1(r,\mathbf z)p(r,\mathbf z)^2d\mathbf z,&
f_h(r)&=2r m_Y(r)+\gamma v_1(r),\\
J(r)&=\int_r^\infty f_h(t)dt,&I_h&=\int_{\mathbb R}\frac{J^2}{\rho},&
F_*(r)&=\int_0^r\frac{J(t)}{\rho(t)}dt.
\end{aligned}
\tag{2.1}
$$

The even continuous weight $\rho$ integrates to one and has a positive lower bound on each compact height interval. Its reciprocal has divergent integrals on both unbounded half-lines. The function $J$ is even, locally absolutely continuous and integrable, $J(\pm\infty)=0$, and $\int J=t_0$. In particular $q_*(r):=J(r)/\rho(r)$ has a continuous representative.

Let $\mathscr W_o$ be the completion of real odd compact smooth height functions in $\int\rho|F'|^2$. H proves that differentiation maps it onto all of $L^2_{\rm even}(\rho dr)$; the representative is $F(r)=\int_0^rF'$. The map $F\mapsto pF$ is an isometry with squared norm multiplied by $a$ into the homogeneous space. Its closed image is

$$
\mathcal H_h=\overline{\{pF:F\in C_c^\infty(\mathbb R;\mathbb R)_{\rm odd}\}}^{\,h}.
\tag{2.2}
$$

The $h$-orthogonal projection $U_h$ of $\Psi$ onto this entire subspace has local representative $pF_*$ and

$$
\begin{gathered}
h(pF,pG)=a\int\rho F'G',\qquad\ell(pF)=a\int JF',\qquad
h[U_h]=aI_h,\\
\delta_h:=h_0[\Psi-U_h]\ge0,\qquad
D_{\rm resp}/a=I_h+\delta_h,\qquad
G_{\rm resp}=3A-\gamma C_2-I_h-\delta_h,\\
I_h-t_0^2=\int\rho(q_*-t_0)^2\ge0,\qquad
\Delta_{\rm aff}/a=(I_h-t_0^2)+\delta_h>0.
\end{gathered}
\tag{2.3}
$$

Here $rp\in\mathcal H_h$ is the image of the derivative $1$, and N supplies only the strict total affine margin $\Delta_{\rm aff}$. That margin alone proves no separate strictness of either summand. Neither $U_h$ nor $pF_*$ has asserted global $L^2$ or native-domain membership.

**Definition 2.2 (credited same-heat auxiliary fundamental solution).** N §§4–5 already establish, for the identical canonical heat,

$$
\begin{gathered}
\mathcal G(\xi)=\int_0^\infty k_t(\xi)dt>0\quad(\xi\ne0),\qquad
\mathcal E\mathcal G=\delta_0,\qquad
\mathcal G(\delta_R\xi)=R^{-5}\mathcal G(\xi),\\
\mathcal G\text{ is smooth off }0,\qquad
\mathcal G(\xi)\le C d(0,\xi)^{-5},\qquad
\mathcal G(r,\mathbf z)\le C|r|^{-5}\quad(r\ne0),\\
f:=Vp\in L^1\cap L^2,\qquad m:=\int f\in(0,\infty),\qquad
p(\xi)=\gamma\int\mathcal G(\eta^{-1}\xi)f(\eta)d\eta\quad\text{a.e.}
\end{gathered}
\tag{2.4}
$$

N also proves $R^5p\circ\delta_R\to\gamma m\mathcal G$ distributionally with uniformly bounded compact local mass. These facts are reused rather than reproved. Their integral representation follows from positive finite-time reconstruction, Tonelli and its $L^2$ limit; the source is exactly $Vp$. The small-time distributional boundary in $\mathcal E\mathcal G=\delta_0$ is the heat initial condition, and the large-time boundary vanishes by $t^{-7/2}$. The kernel is auxiliary and supplies no replacement potential or cutoff-free native interaction. The next theorem adds global decay and strong first-derivative convergence to the distributional result.

## 3. Strong tails from the same source

**Theorem 3.1 (mode and first horizontal derivatives).** Put $c_\infty=\gamma m>0$. The reconstructed mode has continuous horizontal first derivatives and representatives satisfying, for $D=X,Y$,

$$
\begin{gathered}
0<p(\xi)\le C(1+d(0,\xi))^{-5},\qquad
|Dp(\xi)|\le C(1+d(0,\xi))^{-6},\\
p_R(\xi):=R^5p(\delta_R\xi)\longrightarrow c_\infty\mathcal G(\xi),\qquad
Dp_R(\xi)\longrightarrow c_\infty D\mathcal G(\xi)
\end{gathered}
\tag{3.1}
$$

uniformly on every compact subset of $\mathbb R^4\setminus\{0\}$ as $R\to\infty$.

Proof. The missing upper comparison between $d$ and $N$ follows directly from their homogeneity. The compact set $\{N=1\}$ avoids zero, and the finite continuous metric has a finite maximum there. Dilating each point gives $d(0,\xi)\le CN(\xi)$. Consequently $V\le C(1+d)^{-5}$.

For $D=X,Y$, smoothness and homogeneity of $\mathcal G$ make $D\mathcal G$ homogeneous of degree $-6$. The proper control unit sphere is compact and avoids the source, so

$$
|D\mathcal G(\xi)|\le Cd(0,\xi)^{-6},\qquad
\int_{d<L}\mathcal G\le CL^2,\qquad
\int_{d<L}|D\mathcal G|\le CL\quad(L>0).
\tag{3.2}
$$

The integrals follow by dyadic annuli and ball volume $v_dL^7$. These classical derivatives are also distributional derivatives across zero. Indeed use a smooth cutoff equal to one on a homogeneous ball of radius comparable to $\epsilon$, supported in a ball of radius comparable to $2\epsilon$, with horizontal derivatives $O(\epsilon^{-1})$. Its integration-by-parts error is bounded by $C\epsilon^{-1}\int_{d<C\epsilon}\mathcal G=O(\epsilon)$. The omitted derivative integral is also $O(\epsilon)$. Both vanish. This argument differentiates the already established auxiliary kernel, without differentiating an infinite-time heat integral.

First $p$ is bounded. The bounded-potential Dyson kernel for $e^{-t(\mathcal E-\gamma V)}$ is bounded above by $e^{t\gamma\|V\|_\infty}p_E(t;\eta,\xi)$. Since $p$ is its zero eigenvector,

$$
p\le e^{\gamma\|V\|_\infty}P_1p,\qquad
\sup_\xi|(P_1p)(\xi)|\le
\sup_\xi p_E(2;\xi,\xi)^{1/2}\|p\|_2<\infty.
\tag{3.3}
$$

The column identity uses symmetry and the semigroup law. Thus $f=Vp\le C(1+d)^{-5}$, initially, as well as $f\in L^1\cap L^\infty$.

For $R=d(0,\xi)\ge2$, split (2.4)'s convolution into

$$
\{d(0,\eta)\le R/2\},\qquad
\{d(0,\eta)>R/2,\ d(\eta,\xi)\le R/2\},\qquad
\{d(0,\eta)>R/2,\ d(\eta,\xi)>R/2\}.
\tag{3.4}
$$

On the first and third pieces the kernel is at most $CR^{-5}$, giving $CmR^{-5}$. On the middle piece the initial bound on $f$ and (3.2), with Haar invariance, give $CR^{-5}R^2=CR^{-3}$. Hence $p\le C(1+d)^{-3}$. This improves the source bound to $f\le C(1+d)^{-8}$. Repeating the same split gives a middle contribution at most $CR^{-6}$ and proves $p\le C(1+d)^{-5}$. In particular

$$
f\le C(1+d)^{-10}.
\tag{3.5}
$$

The derivative side of the convolution is fixed by the actual group law. A left invariant field at $\xi$ differentiates the path $\xi\exp(tD)$, so

$$
D_\xi\mathcal G(\eta^{-1}\xi)=(D\mathcal G)(\eta^{-1}\xi),\qquad
Dp(\xi)=\gamma\int(D\mathcal G)(\eta^{-1}\xi)f(\eta)d\eta.
\tag{3.6}
$$

For $X$ and $Y$ these paths are respectively right multiplication by $(t,0,0,0)$ and $(0,t,0,0)$, producing precisely the displayed fields in (1.9). There is no change to a right invariant derivative. Formula (3.6) is justified distributionally by compact testing, (3.2), the divergence-free output fields and $f\in L^1\cap L^\infty$. Absolute integrability follows from the locally integrable derivative kernel and its boundedness outside the unit ball. The split (3.4) bounds its first and third contributions by $CmR^{-6}$; the middle contribution is at most $CR^{-10}R=CR^{-9}$. This proves the derivative decay. It also bounds both convolutions at bounded output points.

These convolution representatives are continuous. For output in a fixed compact set, removing an $\epsilon$-ball around the input-output singularity costs at most $C\|f\|_\infty\epsilon^2$ for $\mathcal G$ and $C\|f\|_\infty\epsilon$ for $D\mathcal G$. On its complement, a smooth cutoff of that singularity gives a continuous bounded kernel with an $L^1$ input majorant. Dominated convergence and then $\epsilon\downarrow0$ prove continuity. Positivity follows also by retaining a positive finite heat-time interval in (2.4).

Define $f_R(\eta)=R^7f(\delta_R\eta)$. It has mass $m$, concentrates at zero, and for every fixed $\epsilon>0$,

$$
\int_{d(0,\eta)>\epsilon}f_R\longrightarrow0,\qquad
f_R(\eta)\le CR^{-3}d(0,\eta)^{-10}\quad(d(0,\eta)\ge\epsilon).
\tag{3.7}
$$

Haar scaling and (2.4), (3.6) give exact scaled convolutions with kernels $\mathcal G,D\mathcal G$ and input $f_R$. Fix a compact output set $K$ avoiding zero. On an input ball about zero of sufficiently small fixed radius the two kernels are uniformly continuous in input, uniformly over $K$, and tend to their values at input zero as that radius shrinks. Near each output singularity, the input stays a fixed distance from zero; (3.7) and the local integrals (3.2) bound that contribution uniformly by $O_K(R^{-3})$. On the remaining set the kernels are uniformly bounded and the input mass away from zero tends to zero. Take $R\to\infty$ first and then shrink the input ball. This proves both compact uniform limits in (3.1), with the complete input tail controlled. The scaling identity $Dp_R=R^6(Dp)\circ\delta_R$ follows from degree one of the fields. No native time or moving-face limit is taken here. $\square$

## 4. The limiting slope of the entire height projection

**Theorem 4.1 (full phase slices and strict slope bounds).** Define

$$
C_{\mathcal G}=\int_{\mathbb R^3}\mathcal G(1,\mathbf z)^2d\mathbf z,\quad
D_{\mathcal G}=\int_{\mathbb R^3}|Y\mathcal G(1,\mathbf z)|^2d\mathbf z,\quad
E_{\mathcal G}=\int_{\mathbb R^3}|X\mathcal G(1,\mathbf z)|^2d\mathbf z.
\tag{4.1}
$$

These numbers are finite and

$$
C_{\mathcal G}>0,\qquad D_{\mathcal G}>0,\qquad
E_{\mathcal G}+D_{\mathcal G}=10C_{\mathcal G},\qquad
E_{\mathcal G}>4C_{\mathcal G},\qquad
t_\infty:=\frac{D_{\mathcal G}}{2C_{\mathcal G}}\in(0,3).
\tag{4.2}
$$

On both tails,

$$
\begin{aligned}
\rho(r)&\sim c_\infty^2C_{\mathcal G}|r|^{-4},&
m_Y(r)&\sim c_\infty^2D_{\mathcal G}|r|^{-6},\\
J(r)&\sim\tfrac12c_\infty^2D_{\mathcal G}|r|^{-4},&
F_*'(r)=q_*(r)&\longrightarrow t_\infty,&F_*(r)/r&\longrightarrow t_\infty.
\end{aligned}
\tag{4.3}
$$

Moreover

$$
\lim_{R\to\infty}R^3\int_{|r|\ge R}\rho(r)(q_*(r)-t_0)^2dr
=\frac23c_\infty^2C_{\mathcal G}(t_\infty-t_0)^2.
\tag{4.4}
$$

Consequently $I_h=t_0^2$ requires $t_0=t_\infty\in(0,3)$. If $t_0\ne t_\infty$, then $I_h>t_0^2$. Neither condition on $t_0$ is evaluated here.

Proof. The phase dilation $\mathbf z\mapsto(Ry,R^2z,R^3w)$ has Jacobian $R^6$ and phase-box volume proportional to $R^6$. At height one, $d(0,(1,\mathbf z))$ is bounded below and comparable to $1+\max(|y|,|z|^{1/2},|w|^{1/3})$. Equations (3.1) and (3.2) therefore supply integrable phase majorants of degrees $-10$ for the squared modes and $-12$ for the squared derivatives. In particular

$$
|p_R(1,\mathbf z)|\le Cd(0,(1,\mathbf z))^{-5},\qquad
|Dp_R(1,\mathbf z)|\le Cd(0,(1,\mathbf z))^{-6}\quad(R\ge1).
\tag{4.5}
$$

Dominated convergence on the entire phase space now gives, as $r=R\to\infty$,

$$
r^4\rho(r)\to c_\infty^2C_{\mathcal G},\qquad
r^6m_Y(r)\to c_\infty^2D_{\mathcal G}.
\tag{4.6}
$$

This verifies the phase tails rather than integrating an uncontrolled local limit. It also gives the corresponding uniform big-oh bounds. Parity supplies the negative-height statements.

Homogeneity of $\mathcal G$ and its derivatives gives, for $r>0$,

$$
\rho_{\mathcal G}(r):=\int\mathcal G(r,\mathbf z)^2=C_{\mathcal G}r^{-4},\quad
\int|Y\mathcal G(r,\mathbf z)|^2=D_{\mathcal G}r^{-6},\quad
\int|X\mathcal G(r,\mathbf z)|^2=E_{\mathcal G}r^{-6}.
\tag{4.7}
$$

Second horizontal derivatives of $\mathcal G$ are smooth off zero and homogeneous of degree $-7$. On a compact positive height interval their bounds justify twice differentiating $\rho_{\mathcal G}$ under the phase integral: $\mathcal G X^2\mathcal G$ and $(X\mathcal G)^2$ have integrable degree $-12$ phase majorants. Harmonicity gives $X^2\mathcal G=-Y^2\mathcal G$ there. To integrate the latter term by parts in phases, insert cutoffs of the form $\zeta(y/L,z/L^2,w/L^3)$. On bounded height intervals $|Y\zeta_L|\le C/L$. Cauchy–Schwarz with the phase $L^2$ bounds makes the boundary term tend to zero, and the degree $-12$ bounds justify the other integrals. Thus

$$
\rho_{\mathcal G}''(r)
=2\int|X\mathcal G|^2+2\int|Y\mathcal G|^2
=2(E_{\mathcal G}+D_{\mathcal G})r^{-6}.
\tag{4.8}
$$

Comparing with $20C_{\mathcal G}r^{-6}$ proves the sum identity. Also $\int\mathcal G X\mathcal G=-2C_{\mathcal G}r^{-5}$, so Cauchy–Schwarz at height one gives $E_{\mathcal G}\ge4C_{\mathcal G}$. Equality would force $X\mathcal G(1,\mathbf z)=-2\mathcal G(1,\mathbf z)$ almost everywhere. Continuity and homogeneity extend it to $X\mathcal G(r,\mathbf z)=-2\mathcal G(r,\mathbf z)/r$ for every positive height and phase. Hence $\mathcal G(r,\mathbf z)=r^{-2}a(\mathbf z)$. The height bound $\mathcal G(r,\mathbf z)\le Cr^{-5}$ as $r\to\infty$ forces $a=0$, contradicting positivity. The inequality is strict.

If $D_{\mathcal G}=0$, continuity and homogeneity make $Y\mathcal G=0$ on the positive-height half-space. Harmonicity then gives $X^2\mathcal G=0$. At each fixed phase the resulting affine function of height decays at infinity and must vanish, again contradicting positivity. Thus $0<D_{\mathcal G}<6C_{\mathcal G}$, proving all of (4.2).

The full-height bound on $V_1$ and (4.6) give

$$
|v_1(r)|\le C(1+|r|)^{-4}\rho(r)=O(|r|^{-8}).
\tag{4.9}
$$

Integrating $2r m_Y+\gamma v_1$ on the positive tail gives $J(r)\sim c_\infty^2D_{\mathcal G}r^{-4}/2$. Explicitly, the error in $m_Y(t)$ is uniformly $o(t^{-6})$ beyond a sufficiently large fixed height, and its integrated contribution is $o(r^{-4})$; (4.9)'s contribution is $O(r^{-7})$. Evenness gives the other tail. Dividing by the positive $\rho$ proves the quotient limit. The average of $q_*$ over $[0,r]$ tends to its tail limit, so its primitive satisfies the last assertion of (4.3) on both sides. The continuous quotient is a valid representative of $F_*'$.

Finally (4.3) gives the two-sided asymptotic of $\rho(q_*-t_0)^2$. Integrating $r^{-4}$ on both tails, with uniform error bounds beyond a fixed height, proves (4.4), including when $t_\infty=t_0$. H's equality criterion in (2.3) then proves the necessary condition and the stated sufficient condition for a strict height gap. A matching limiting slope alone does not make the quotient constant. $\square$

## 5. A compact witness beyond the entire height subspace

**Lemma 5.1 (local product and derivative bridge).** The local representative of $U_h$ has distributional horizontal derivatives

$$
XU_h=F_*Xp+p q_*,\qquad YU_h=F_*Yp.
\tag{5.1}
$$

For $U_R(\xi)=R^4(pF_*)(\delta_R\xi)$, all three quantities $U_R,XU_R,YU_R$ converge uniformly on any compact set with $|r|$ bounded away from zero to, respectively,

$$
c_\infty t_\infty r\mathcal G,\qquad
c_\infty t_\infty(\mathcal G+rX\mathcal G),\qquad
c_\infty t_\infty rY\mathcal G.
\tag{5.2}
$$

Proof. H's derivative-range theorem supplies odd compact height functions $F_n$ with $F_n'\to q_*$ in $L^2(\rho dr)$ and $F_n\to F_*$ uniformly on bounded height intervals. Its isometry and the odd energy gap make $pF_n$ Cauchy in horizontal energy. The potential bound in (1.13), together with the positive minimum of $V$ on compact sets, identifies its unique local $L^2$ limit. Uniform height convergence identifies that limit as $pF_*$. Compact distributional testing identifies the global $L^2$ limits of its horizontal derivatives. The local product rule then gives (5.1): $F_*$ is locally absolutely continuous, $q_*\in L^2_{\rm loc}(dr)$, $F_*$ is locally bounded, and $p$ is bounded by Theorem 3.1. All displayed product terms are locally square integrable. In fact $q_*$ is continuous by Definition 2.1.

The exact local identities are

$$
\begin{aligned}
U_R&=p_R\,F_*(Rr)/R,\\
XU_R&=(Xp_R)F_*(Rr)/R+p_Rq_*(Rr),\\
YU_R&=(Yp_R)F_*(Rr)/R.
\end{aligned}
\tag{5.3}
$$

On the stated compact sets, (4.3) gives uniform convergence of $F_*(Rr)/R$ to $t_\infty r$ and of $q_*(Rr)$ to $t_\infty$. Theorem 3.1 proves (5.2). No second derivative of $F_*$ or representative of $\Psi$ is used. $\square$

**Theorem 5.2 (nonzero residual and quantitative orthogonal energy).** Define on $r\ne0$

$$
Z=-2rY^2\mathcal G+2t_\infty X\mathcal G.
\tag{5.4}
$$

This smooth odd function is nonzero on the positive-height half-space. Choose a nonnegative even-under-$\sigma$ compact smooth cutoff $\chi_0$, supported where $|r|\ge c_0>0$, such that

$$
L_\varphi:=\int\chi_0 Z^2>0,\qquad
\varphi:=\chi_0Z,\qquad
u_R(\xi)=R^{-4}\varphi(\delta_{1/R}\xi),\qquad
e_R:=\ell(u_R)/a-h_0(U_h,u_R).
\tag{5.5}
$$

Then $\varphi$ is a nonzero real odd compact smooth test with $b[\varphi]>0$, and

$$
R^3e_R\longrightarrow c_\infty L_\varphi>0,\qquad
R^3h_0[u_R]\longrightarrow b[\varphi]>0.
\tag{5.6}
$$

For some finite $R_0\ge1$, every finite $R\ge R_0$ gives

$$
\boxed{\displaystyle
\delta_h=h_0[\Psi-U_h]
\ge\frac{e_R^2}{h_0[u_R]}
\ge\frac{c_\infty^2L_\varphi^2}{4b[\varphi]R^3}>0.}
\tag{5.7}
$$

Thus $\Psi\notin\mathcal H_h$. The onset $R_0$ is proved finite but is not numerically evaluated.

Proof. The identical heat is invariant under $\sigma$, so $\mathcal G$ is even, $X\mathcal G$ odd and $Y^2\mathcal G$ even. Hence $Z$ is odd. If it vanished on $r>0$, harmonicity would give

$$
r\partial_r^2\mathcal G+t_\infty\partial_r\mathcal G=0.
\tag{5.8}
$$

Fix any nonzero phase triple $\mathbf z$. The function $g(r)=\mathcal G(r,\mathbf z)$ is positive, bounded as $r\downarrow0$ because $(0,\mathbf z)$ avoids the source, and tends to zero as $r\to\infty$ by the height bound. For any real $t$, the solutions of $rg''+tg'=0$ are $A+B r^{1-t}$ when $t\ne1$ and $A+B\log r$ when $t=1$. For $t<1$, decay at infinity forces $B=A=0$; for $t=1$ logarithmic growth and then decay do the same; for $t>1$, decay forces $A=0$ and boundedness at zero forces $B=0$. Taking $t=t_\infty$ contradicts positivity. Therefore $Z$ is nonzero somewhere with positive height. Choose a nonnegative bump near such a point and add its $\sigma$-reflection to obtain $\chi_0$. It has $L_\varphi>0$. If $b[\varphi]=0$, then $X\varphi=Y\varphi=0$; their brackets force all coordinate derivatives to vanish. A compactly supported constant is zero, contradicting the construction. Thus $b[\varphi]>0$.

The tests $u_R$ belong to the same real odd canonical core. Haar and horizontal scaling give exactly

$$
R^3h_0[u_R]
=b[\varphi]-\gamma R^2\int V(\delta_R\xi)\varphi(\xi)^2d\xi.
\tag{5.9}
$$

On this fixed support $V(\delta_R\xi)=O(R^{-5})$, since $|r|\ge c_0$. Consequently the correction tends to zero. The odd gap and $V\ge0$ also give $0<h_0[u_R]\le R^{-3}b[\varphi]$.

Scaling the exact response functional retains its entire $V_1$ term:

$$
R^3\ell(u_R)/a
=2\int r(Yp_R)(Y\varphi)
 +\gamma R\int V_1(\delta_R\xi)p_R\varphi.
\tag{5.10}
$$

The second term tends to zero: the height bound makes $V_1(\delta_R\xi)=O(R^{-4})$ uniformly on the support and $p_R$ is uniformly bounded there. The local representative and derivatives in Lemma 5.1 give, independently,

$$
R^3h_0(U_h,u_R)
=b(U_R,\varphi)-\gamma R^2\int V(\delta_R\xi)U_R\varphi.
\tag{5.11}
$$

Its potential term is $O(R^{-3})$, and its derivative pairing tends by (5.2) to $c_\infty t_\infty b(r\mathcal G,\varphi)$. These pairings use only the proved local representative of $U_h$, with compact tests, and not a global $L^2$ response.

The support avoids the source. Compact integration by parts, $Yr=0$, and $\mathcal E\mathcal G=0$ there give

$$
b(r\mathcal G,\varphi)=-2\int X\mathcal G\,\varphi,\qquad
\int r(Y\mathcal G)(Y\varphi)=-\int rY^2\mathcal G\,\varphi.
\tag{5.12}
$$

Equations (3.1), (5.10)–(5.12) imply

$$
\lim R^3e_R
=c_\infty\left\{2\int r(Y\mathcal G)(Y\varphi)
-t_\infty b(r\mathcal G,\varphi)\right\}
=c_\infty\int Z\varphi=c_\infty L_\varphi.
\tag{5.13}
$$

There is no boundary at phase infinity in this step because $\varphi$ is compact. Every source and coefficient tail discarded in (5.10)–(5.11) has an explicit bound.

Finally the genuine Riesz equation in the homogeneous Hilbert space gives $h_0(\Psi-U_h,u_R)=e_R$. Cauchy–Schwarz gives the first inequality in (5.7). By (5.13), $e_R\ge c_\infty L_\varphi/(2R^3)$ for every sufficiently large $R$. Combining this with the upper bound after (5.9) proves the quantitative inequality. In fact $R^3e_R^2/h_0[u_R]\to c_\infty^2L_\varphi^2/b[\varphi]$. This proves nonmembership in the entire closed height space by a nonzero witness, independently of the earlier affine nonmembership theorem. Each $u_R$ is a canonical response test; it is not an actual native eigenstate or a claimed native preparation. $\square$

## 6. Complete coefficient consequences and their direction

**Corollary 6.1 (strict entire-height comparison).** Set

$$
C_h:=\nu^2(K_{\rm base}-aI_h)-\lambda D_{\rm clock},\qquad
\epsilon_R:=\frac{c_\infty^2L_\varphi^2}{4b[\varphi]R^3}>0\quad(R\ge R_0).
\tag{6.1}
$$

The number $C_h$ is the entire-height second-order comparison: its correction is the infimum of $h[pF]-2\ell(pF)$ over the completed height space, equal to $-aI_h$ by H Theorem 5.1. Then

$$
\begin{gathered}
C_{\rm resp}=C_h-a\nu^2\delta_h<C_h,\\
G_{\rm resp}=3A-\gamma C_2-I_h-\delta_h
\le3A-\gamma C_2-I_h-\epsilon_R<3A-\gamma C_2-I_h,\\
G_{\rm resp}=G_{108}-(t_0-1)^2-(I_h-t_0^2)-\delta_h,\\
\frac{C_{\rm resp}}{a\nu^2}
\le3A-\gamma C_2-I_h-\epsilon_R-\mathscr R\overline D
<3A-\gamma C_2-I_h-\epsilon_R-\mathscr R(1+b[p]).
\end{gathered}
\tag{6.2}
$$

An admitted datum with $C_h\le0$, including its equality boundary, has $C_{\rm resp}<0$ and all the credited actual negative-response consequences. No additional datum satisfying this condition is asserted to occur.

Proof. Substitute (5.7) into the exact decomposition (2.3) and the full coefficient formula (1.16). H Theorem 8.1 gives $\mu<T<3\mu$, where $\mu=\int Vp^2$ and $b[p]=\gamma\mu$, hence $1+b[p]<\overline D<1+3b[p]$. Since $\mathscr R>0$, the strict final bound has the indicated direction. The condition on $C_h$ and the negative branch from R Theorem 11.2 give the last assertion directly. This invokes the existing actual-state bridge and does not add a transfer theorem. $\square$

Under the canonical normalization $W=j_0V$, $W_j=j_0V_j$, $W_{\rm t}=j_0V_{\rm t}$ and $\overline C=j_0C_*$, one has $\gamma=j_0/\overline C$. Thus $p$, $\mathcal G$, $c_\infty$, $t_\infty$, $\delta_h$ and the witness bound $\epsilon_R$ are canonical; the full original coefficients still retain $\nu^2$ and $\lambda$ as in (1.16). The strictly positive subtraction is an upper-bound improvement on $G_{\rm resp}$. It proves neither $G_{\rm resp}>0$ nor $G_{\rm resp}\le0$. The still unevaluated comparison is $\gamma C_2+I_h+\delta_h$ against $3A$; $G_{108}$ is also unevaluated. These fixed quantities are not independent scalar choices, and an unresolved comparison is not logical underdetermination of the source.

## 7. Current actual-state credit and the entire original target

**Proposition 7.1 (existing energy, occurrence and actual profiles).** The following are reused results for a fixed admitted datum under its supplied analytic antecedents. They apply sequencewise to every prescribed $s_n\downarrow0$ and every actual normalized complex ground-state choice $\psi_{s_n}\in D(S)$.

R Theorem 11.1 gives $E_s\to\min(0,C_{\rm resp})$. P Theorem 105.1 gives $r_s\to\infty$ along an actual sequence if and only if $\mathcal U_s\psi_s$ converges globally to the unit phase orbit of $p$. When $C_{\rm resp}<0$, R Theorem 11.2 therefore gives

$$
E_s\to C_{\rm resp},\qquad
\epsilon_c(s)=C_{\rm resp}s^2+o(s^2),\qquad
r_s\sim(-C_{\rm resp})s^{-6}\to\infty,
\qquad\operatorname{dist}_{L^2}(\mathcal U_s\psi_s,\{e^{i\theta}p\})\to0.
\tag{7.1}
$$

A Theorem 5.1 supplies the actual solvability relation $c(L-C_{\rm resp})=0$ whenever $E_s\to L$ and $\mathcal U_s\psi_s\rightharpoonup cp$. A Theorem 6.1 gives microscopic weak zero, local strong zero, vanishing rescaled horizontal and potential energies and orbit distance $\sqrt2$ when $C_{\rm resp}>0$, while the state norms remain one.

For the full original tensor and fixed-cutoff Coulomb normalization set

$$
\begin{aligned}
M&=\int_I\phi^2c_\kappa c_\kappa^{\mathsf T}dk>0,&
d_M(\mathbf z)&=(\mathbf z^{\mathsf T}M^{-1}\mathbf z)^{1/2},\\
\beta_C&=\frac{\phi(k_0)\int_I\phi^3dk}{4\pi\sqrt{\det M}},&
e_C&=-\beta_C^2/(4a),&\varrho&=\beta_C/(2a),\\
h_C(\mathbf z)&=(\det M)^{-1/4}(\varrho^3/\pi)^{1/2}e^{-\varrho d_M(\mathbf z)},&
\mathcal D_gv(k,\mathbf z)&=g^{-3/2}v(k,\mathbf z/g).
\end{aligned}
\tag{7.2}
$$

A Theorems 10.2 and 11.1 prove that, for these actual choices, microscopic weak zero is equivalent to the unit-mass macroscopic orbit convergence

$$
\inf_\theta\|\mathcal D_{g_s}\psi_s-e^{i\theta}\phi h_C\|_2\to0,
\tag{7.3}
$$

and either entails $E_s/g_s^2\to e_C$ and $r_s\to-\chi_c^2e_C$. In particular A Corollary 12.1 already proves, on the conditional positive-response branch,

$$
E_s=\chi_c^2e_Cs^6+o(s^6),\qquad
\epsilon_c(s)=\chi_c^2e_Cs^8+o(s^8),\qquad
r_s\to\frac{\chi_c^2\beta_C^2}{4a}>0,
\tag{7.4}
$$

with (7.3) for every actual choice. The same conclusions apply to any actual weak-zero subsequence at response zero. The exact coefficient and full-mass positive-branch macroscopic profile are therefore established credit, without an assertion that positive response occurs. Their proofs are not repeated here.

R Propositions 14.1 and 15.1 and Corollary 15.2 already give the exact admitted ratio images, the enlarged explicit admission neighbourhood and the full image $\mathscr R\in(0,\infty)$ across distinct fixed admitted datasets for each sign of $\kappa$. Negative response and negative $C_{108}$ occur for each sign; a sufficiently narrow fixed admitted interval gives actual negative-response unit-orbit selection. Across those datasets positive and zero response each occur if and only if $G_{\rm resp}>0$; positive and zero $C_{108}$ each occur if and only if $G_{108}>0$. Each datum is fixed before its own $s$-limit. These are existing occurrence results, not consequences newly obtained from the residual.

Credit and scope. P's actual equivalence uses its full finite-native weighted resolvent and negative attainment, not a coarse near-minimizer or a trial. R's matching theorem includes its original full-complex-domain lower argument. A's weak-zero implication uses actual short-field resolvent removal and its derived $o(g_s^2)$ fixed-cutoff variational error, then directly applies P §§72–73. Its converse is an actual microscopic/macroscopic norm comparison. Thus (7.3)–(7.4) are matching energy and global unit-mass statements at exactly their hypotheses. No duplicate transfer result is asserted in this volume.

**Definition 7.2 (remaining original decision).** The full original target is to decide the complete $C_{108}$ and $C_{\rm resp}$ signs throughout the admitted signed-$\kappa$, interval, interior-pole and jointly realized rational-field family, characterize occurrence or exclusion of every sign, and decide actual exact-critical $r_s$ and every normalized complex ground-state scale/profile behavior. All original path, source, clock, domain and death conditions remain (1.1)–(1.10).

The new result settles $\delta_h>0$ beyond all closed height multipliers. It leaves $I_h>t_0^2$ undecided; (4.4) and $t_0=t_\infty$ are only the stated conditional test and necessary equality condition. It leaves both canonical absolute signs unevaluated. Positive and zero response occurrence retain the unresolved predicate $G_{\rm resp}>0$ despite the already proved full ratio image and negative occurrence.

At $C_{\rm resp}=0$, the general conclusions remain $E_s\to0$ and $c\le r_s=o(s^{-6})$. The existence or selection of actual weak-zero subsequences, nonzero microscopic core limits, divergent or mixed alternatives, and the every-choice decision remain unresolved. On a weak-zero subsequence the coefficient and macroscopic profile are already (7.3)–(7.4); on a divergent-$r_s$ subsequence P's actual equivalence gives the microscopic unit orbit. The present residual does not select between them. A uniform centered detuning/crossover theorem also remains unresolved. No positive-branch exact Coulomb coefficient or full-mass profile obligation is left open here beyond its stated conditional occurrence premise.

## 8. Attribution and realization boundaries

**Definition 8.1 (scope of the substantive increment).** P §§70–75 supply the native fields, two charges, full domains and positive-cutoff attainment; §§78 and 81 supply the chart and exact conjugacy. P §§82–88 supply canonical geometry, heat, complete tails, compactness, reconstruction and the simple critical mode. P §§89–91 distinguish tangent onset and the coarse native weak disk from actual unit selection; §§92–96 supply observation, infinite-fibre, quantum and analytic-preparation boundaries. P §97 supplies the rational shear, §100 the one-sided macroscopic direction, §§102–105 the actual shell defect, native weighted resolvent and scale/no-loss equivalence, and §§106–108 the weighted mode, parity and complete field and affine coefficients.

R supplies coefficient multipliers, the homogeneous gap and Riesz response, recovery, the full-domain lower estimate, matching energy and conditional alternatives, canonical normalization, and the ratio/admission/negative-occurrence results. N supplies the identical-heat auxiliary $\mathcal G$, its distributional reconstructed-mode tail, strict affine nonmembership and fixed complex-slope comparison. H supplies the entire height isometry, derivative-range density, exact quadrature, local representative, nonnegative decomposition, and cutoff/clock comparisons. A supplies actual solvability and microscopic disappearance, and its §§10–12 supply the weak-zero/macroscopic equivalence, matching Coulomb coefficient and positive-branch full-mass profile.

The added proofs are the source-specific strong mode and first-horizontal-derivative tails, phase-integrated limiting projection slope and strict bounds, local scaled projection bridge, and nonzero compact residual with quantitative strictly positive orthogonal energy. The coefficient consequences preserve the complete original terms and the direction of every bound. Group convolution, Haar changes of variables, compact distributional testing, dominated integration, Cauchy–Schwarz, an elementary ODE and Hilbert-space projection are classical intermediate tools. The cited heat, localization, hypoelliptic and convolution suppliers retain their supplied conditional scopes; no external reauthentication, worldwide novelty or literature-absence claim is made. These are symbolic reference proofs, without executed mathematics, numerical validation or Lean/kernel/frozen certification.

**Definition 8.2 (native and interpretive limits).** With the original real lift $D=\kappa x$ and $J_\kappa=\operatorname{diag}(1,1,\kappa)$, retain

$$
\psi^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1/2}\psi(k,q),\qquad
W_\tau^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1}W_\tau(k,q),\qquad
g_{\rm orig}=|\kappa|g.
\tag{8.1}
$$

The long-time tensor transports to $J_\kappa M J_\kappa^{\mathsf T}$ with signed cross terms. Wavefunctions and unit raw-source kernels have different absolute-Jacobian factors. There is no uniform $\kappa\to0$, actual zero-leaf, wrapped-cover, torus or cutoff-free native conclusion. The auxiliary $\mathcal G$ and scaled response tests change no native field, source or clock. Scale limits in §§3–5 are canonical tail limits; the native small-$s$ statements in §7 are separately credited results with their original hypotheses.

The response, height projection and residual are elements of the real odd homogeneous completion. Their local representatives supply no global $L^2$ response, positive $L^2$ spectral gap or general inverse. A compact canonical response test is not an actual native state. Native actual states remain arbitrary complex vectors in the entire original domains, with both deaths and all real phase frequencies.

Four canonical coordinates, homogeneous dimension seven, three real phases, the rank-three long-time tensor, retained-coordinate counts and physical Euclidean space are distinct. No physical dimension or physical $SO(3)$ is selected. Analytic amplitudes and spectral identities supply no native preparation, actuation, lawful transport, density acquisition, resource or clock bridge. Spectral energy is distinct from acquired mass and ML error. No native implementation, autonomous reduced quantum dynamics, full-channel acquisition, general neural-network or empirical machine-learning conclusion, efficiency/capacity/impossibility claim, or wider-programme completion is asserted.

## 追加锚（本行以下为增补区）
