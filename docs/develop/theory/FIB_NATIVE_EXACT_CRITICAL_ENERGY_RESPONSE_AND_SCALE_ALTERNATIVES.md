# Native exact-critical energy response and scale alternatives

This companion to [Native full-state weak binding](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md), §§70–108, concerns the same original rational-field problem. Its conclusions are ordinary conditional mathematical theorems relative to the native, heat, domain, critical-mode and complete-field antecedents stated below. They give a homogeneous response construction, an improved lower estimate on the entire original complex domain, a matching actual energy limit, and conditional scale and profile alternatives. The sign of the complete coefficient over the original admitted family, and the finer decision at response zero, remain open.

## 1. The original problem, its source and its complete domains

**Definition 1.1 (fixed original data).** Fix one arbitrary admissible signed $\kappa\ne0$, the original height interval $I=(l,u)$, an interior pole $k_0\in I$, and $\varepsilon,a>0$. The three phase coordinates $q=(\theta,v,x)$ range over $\mathbb R^3$. All measures are raw $dY=dk\,dq$ unless a change of density is displayed. Retain the original rational vector $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$ of the source problem. It can be specified on the whole interval by its exact rational identity

$$
\begin{aligned}
\alpha_\kappa&=\kappa+\kappa^2/H,& d_0&=k_0-\alpha_\kappa>0,\\
c_j&=c_\kappa^{(j)}(k_0)\quad(j=0,1,2),\\
c_\kappa(k_0+h)&=c_0+h c_1+\frac{h^2}{2(1+h/d_0)}c_2.
\end{aligned}
\tag{1.1}
$$

Here $H$ and the jets are the fixed original data; they are not independently variable replacement coefficients. Formula (1.1) is an equality, rather than a truncated Taylor model. For example the original retained components are

$$
(A_\kappa(k),B_\kappa(k))
 =\frac{k-2\kappa}{2H(k-\alpha_\kappa)}(H+\kappa-k,-k).
\tag{1.2}
$$

The original admissibility conditions, including positive probabilities and absence of denominator zeros, remain in force. In particular $k-\alpha_\kappa>0$ on $I$, and the original third component in (1.1) is retained. The determinant is

$$
\det(c_\kappa,c_\kappa',c_\kappa'')(k)
 =-\frac{H^2-\kappa^2}{2H^3(k-\alpha_\kappa)^3}\ne0.
\tag{1.3}
$$

Let $L=u-l$, $\lambda=\varepsilon^2\pi^2/L^2$ and
$\phi(k)=(2/L)^{1/2}\sin(\pi(k-l)/L)$. Both actual height endpoints are Dirichlet. The free operator and threshold shift are

$$
B=-\varepsilon^2\partial_k^2-(c_\kappa(k)\cdot\partial_q)^2,
\qquad S=B-\lambda\ge0.
\tag{1.4}
$$

Use the unitary Fourier transform in the three real phases, with factor $(2\pi)^{-3/2}$. Put
$B_\eta=-\varepsilon^2\partial_k^2+|\eta\cdot c_\kappa(k)|^2$.
The entire complex form and operator domains, with underlying $L^2(dY)$ membership understood, are

$$
\begin{aligned}
\mathcal Q
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H_0^1(I)\text{ a.e.},\
 \int_{\mathbb R^3}\!\int_I
 \bigl(\varepsilon^2|\partial_k\widehat\psi|^2
       +|\eta\cdot c_\kappa|^2|\widehat\psi|^2\bigr)dk\,d\eta<\infty\right\},\\
D(S)=D(B)
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H^2(I)\cap H_0^1(I)\text{ a.e.},\
 \int_{\mathbb R^3}\|B_\eta\widehat\psi(\cdot,\eta)\|_{L^2(I)}^2d\eta<\infty\right\}.
\end{aligned}
\tag{1.5}
$$

Thus $\mathcal Q=D(S^{1/2})=D(B^{1/2})$. No ordinary phase $H^1$ assumption is imposed. Every real frequency and every complex state in these domains is allowed.

**Definition 1.2 (the unchanged threshold field).** Let $p_t^B(Y,Z)$ be the killed heat kernel of $e^{-tB}$ in raw measure, and $o=(k_0,0)$. For $\tau>0$ set

$$
\begin{aligned}
W_\tau(Y)&=\int_\tau^\infty e^{\lambda t}p_t^B(o,Y)dt,\\
\rho_\tau(Y)&=e^{\lambda\tau}p_\tau^B(o,Y),&
SW_\tau&=\rho_\tau,\\
\int\rho_\tau dY&=e^{\lambda\tau}\mathbb P_{k_0}(\zeta>\tau),&
\int\phi(k)\rho_\tau(k,q)dk\,dq&=\phi(k_0).
\end{aligned}
\tag{1.6}
$$

The last two charges are different. There is no division by survival probability. The heat clock in the field is $B$, independently of $a$. The native energy is

$$
\mathfrak e_{g,\tau}[\psi]
 =a\|S^{1/2}\psi\|_2^2-g\int W_\tau|\psi|^2dY,
\qquad
E_\tau(g)=\inf_{\psi\in\mathcal Q,\ \|\psi\|_2=1}
                       \mathfrak e_{g,\tau}[\psi].
\tag{1.7}
$$

At every fixed positive $g,\tau$, the supplied Propositions 70.2 and 75.2 assert that $W_\tau$ is bounded, the operator is $aS-gW_\tau$ on exactly $D(S)$, its essential spectrum is $[0,\infty)$, and its finite negative bottom is attained. These are standing native antecedents, without a uniform-in-$\tau$ multiplier assertion.

For reference, $M=\int_I\phi^2c_\kappa c_\kappa^{\mathsf T}dk>0$ is the original long-time tensor and $d(q)=(q^{\mathsf T}M^{-1}q)^{1/2}$. The fixed-cutoff tail is

$$
W_\tau(k,q)=\frac{\phi(k_0)\phi(k)}{4\pi\sqrt{\det M}\,d(q)}
              +O(\phi(k_0)\phi(k)|q|^{-3}).
\tag{1.8}
$$

Under the original real lift $D=\kappa x$ and $J_\kappa=\operatorname{diag}(1,1,\kappa)$, the exact correspondence is

$$
\psi^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1/2}\psi(k,q),\quad
W_\tau^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1}W_\tau(k,q),\quad
g_{\rm orig}=|\kappa|g.
\tag{1.9}
$$

The transported tensor is $J_\kappa M J_\kappa^{\mathsf T}$, including its signed cross terms. A wavefunction and a unit raw-source kernel have different Jacobian factors.

## 2. Exact microscopic dictionary and the inherited analytic hypotheses

**Definition 2.1 (unitary chart and rational shear).** Put
$j_0=\varepsilon^4|\det(c_0,c_1,c_2)|>0$, and, for $\xi=(r,y,z,w)$, set

$$
\begin{aligned}
\Xi_s(\xi)&=(k_0+\varepsilon sr,
       s c_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w),\\
I_s&=((l-k_0)/(\varepsilon s),(u-k_0)/(\varepsilon s)),&
\Omega_s&=I_s\times\mathbb R^3,\\
(\mathcal U_s\psi)(\xi)&=(j_0s^7)^{1/2}\psi(\Xi_s\xi),&
\mathcal Q_s&=\mathcal U_s\mathcal Q,\\
X&=\partial_r,&Y_s&=(1,r,r^2/[2(1+\beta_sr)])\cdot\partial_{y,z,w},\\
b_s[F]&=\|XF\|_2^2+\|Y_sF\|_2^2,&
\beta_s&=\nu s,\qquad \nu=\varepsilon/d_0,\\
U_s(\xi)&=s^5W_{s^2}(\Xi_s\xi),&
C_s&=A_s-\lambda s^2=s^2\mathcal U_sS\mathcal U_s^{-1}\ge0.
\end{aligned}
\tag{2.1}
$$

Here $A_s$ is the Friedrichs operator of $b_s$, with $D(A_s)=\mathcal U_sD(S)$. The raw Jacobian of $\Xi_s$ is exactly $j_0s^7$; $\mathcal U_s$ is unitary. Define

$$
L_s=\begin{pmatrix}1&\beta_s&0\\0&1&2\beta_s\\0&0&1\end{pmatrix},
\quad \mathscr L_s(r,z)=(r,L_sz),\quad
\mathcal T_sF=F\circ\mathscr L_s,
\quad \widetilde U_s=U_s\circ\mathscr L_s.
\tag{2.2}
$$

This determinant-one shear fixes the source and both moving height faces. With $Y=\partial_y+r\partial_z+(r^2/2)\partial_w$,

$$
\widetilde b_s[f]:=b_s[\mathcal T_s^{-1}f]
 =\int_{\Omega_s}\bigl(|Xf|^2+(1+\beta_sr)^{-2}|Yf|^2\bigr)d\xi.
\tag{2.3}
$$

These are exact identities of closed horizontal forms. On the actual height interval the denominator is positive. Neither face nor any phase direction has been removed.

Let $\mathcal Q_E$ be the closure of $C_c^\infty(\mathbb R^4;\mathbb C)$ in $\|f\|_2^2+b[f]$, where $b[f]=\|Xf\|_2^2+\|Yf\|_2^2$, and let $\mathcal E$ be its Friedrichs operator. The Engel group law and dilations are

$$
(r,y,z,w)(r',y',z',w')
 =(r+r',y+y',z+z'+ry',w+w'+rz'+r^2y'/2),
\quad
\delta_R\xi=(Rr,Ry,R^2z,R^3w).
\tag{2.4}
$$

Unit Lebesgue measure is Haar measure and the homogeneous dimension is seven. Write $N(\xi)=\max(|r|,|y|,|z|^{1/2},|w|^{1/3})$, $P_t=e^{-t\mathcal E}$ and

$$
V(\xi)=j_0^{-1}\int_1^\infty p_E(t;0,\xi)dt,
\qquad \mathcal EV=j_0^{-1}p_E(1;0,\cdot).
\tag{2.5}
$$

The unit-Lebesgue heat has mass one, so the last source has mass $1/j_0$. This is the original unit raw source in the changed density. More explicitly,

$$
P_s(t;\eta,\xi)=j_0s^7p_{s^2t}^B(\Xi_s\eta,\Xi_s\xi),
\quad U_s=j_0^{-1}\int_1^\infty e^{\lambda s^2t}P_s(t;0,\cdot)dt,
\quad
(A_s-\lambda s^2)U_s=s^7\rho_{s^2}\circ\Xi_s.
\tag{2.6}
$$

**Definition 2.2 (standing heat and threshold antecedents).** Retain the following results at exactly their supplied scopes from §§82–88, 97 and 102–107 of the companion source.

The canonical heat is conservative and positive, $\mathcal E$ has no $L^2$ kernel, and

$$
p_E(t;\eta,\xi)\le Ct^{-7/2}e^{-c d_E(\eta,\xi)^2/t},
\quad
0<V\le C(1+N)^{-5},
\quad
\sup_{|r|\ge R}\widetilde U_s\le CR^{-5}+Cs^5
\quad(R\ge1,\ sR\le c_0).
\tag{2.7}
$$

The last bound includes all heights of the original killed domain. It will be used on its native side only; canonical fields have the analogous height bound. Canonical local form compactness, the native height-strip core approximation, and both-face native heat bounds are retained. The threshold data satisfy

$$
\begin{aligned}
C_*&=\sup_{0\ne f\in\mathcal Q_E}\frac{\int V|f|^2}{b[f]}\in(0,\infty),&
\chi&=\chi_c=a/C_*,\\
h[f]&=a b[f]-\chi\int V|f|^2\ge0,&
H_c&=a\mathcal E-\chi V,\\
\ker H_c&=\mathbb C p,& p&=\Phi_c>0,\quad \|p\|_2=1,\quad p\in D(\mathcal E),\\
\mathcal Ep&=C_*^{-1}Vp,& \mu&=\int Vp^2>0,\quad a b[p]=\chi\mu.
\end{aligned}
\tag{2.8}
$$

Multiplication by $V^{1/2}$ is denoted $M_V$. The bounded compact positive operator

$$
K_0=\lim_{b\downarrow0}M_V(\mathcal E+b)^{-1}M_V
\tag{2.9}
$$

has norm $C_*$ and a simple top eigenvalue. Its zero-energy reconstruction $\int_0^\infty P_tM_Vdt$ is compact into $L^2$ and has range in $D(\mathcal E)$ on these right sides. These statements do not assert a bounded inverse of $\mathcal E$ on all of $L^2$.

The weighted mode and parity antecedents of §106 are

$$
\begin{gathered}
rp\in\mathcal Q_E,\qquad h[rp]=a,\qquad
\int r^2(p^2+|Xp|^2+|Yp|^2)d\xi<\infty,\\
\sigma(r,y,z,w)=(-r,y,-z,w),\qquad p\circ\sigma=p,\quad V\circ\sigma=V.
\end{gathered}
\tag{2.10}
$$

If $\eta$ is smooth and even, one on $[-1,1]$ and zero outside $[-2,2]$, with a smooth quadratic complement $\zeta$ satisfying $\eta^2+\zeta^2=1$, then

$$
\int |\eta_R'|^2p^2=o(R^{-4}),\qquad \eta_R(r)=\eta(r/R).
\tag{2.11}
$$

Indeed the integral is bounded by $CR^{-4}\int_{|r|>R}r^2p^2$. The cutoff is native form admissible whenever its height support lies between both faces. This follows by multiplying canonical core approximants by the height cutoff and using the equivalence of (2.3) and $b$ on that strip. The same argument applies to every supported canonical form vector used below.

All these are conditional antecedents of this volume. In particular their cited external heat and localization suppliers are not independently authenticated here.

## 3. The complete common-bridge fields and exact critical units

**Definition 3.1 (coefficient fields).** For the bridge $H_v$ of height Brownian motion with generator $\partial_r^2$, from zero to $r$ in time $t$, put

$$
\begin{aligned}
u(h)&=(1,h,h^2/2),& S_t&=\sup_{0\le v\le t}|H_v|,\\
M_j&=\int_0^tH_v^j u(H_v)u(H_v)^{\mathsf T}dv\quad(j=0,1,2),\\
\gamma_M(z)&=(4\pi)^{-3/2}(\det M)^{-1/2}e^{-z^{\mathsf T}M^{-1}z/4},&
h_t(r)&=(4\pi t)^{-1/2}e^{-r^2/(4t)}.
\end{aligned}
\tag{3.1}
$$

In the first line $u(h)$ denotes the displayed vector. All three matrices belong to this single bridge. The coefficient kernels and fields are exactly

$$
\begin{aligned}
p_0(t;r,z)&=h_t(r)\mathbb E_{0,r}^t[\gamma_{M_0}(z)]=p_E(t;0,(r,z)),\\
p_1(t;r,z)&=h_t(r)\mathbb E_{0,r}^t[-2D\gamma_{M_0}(z)[M_1]],\\
p_2(t;r,z)&=h_t(r)\mathbb E_{0,r}^t[3D\gamma_{M_0}(z)[M_2]
                     +2D^2\gamma_{M_0}(z)[M_1,M_1]],\\
V_j&=j_0^{-1}\int_1^\infty p_j(t;\cdot)dt\quad(j=1,2),&
V_{\rm t}&=j_0^{-1}\int_1^\infty t p_0(t;\cdot)dt>0.
\end{aligned}
\tag{3.2}
$$

The full-space antecedent from §107, with the original zero extension of $\widetilde U_s$, is

$$
\widetilde U_s=V+\beta_sV_1+\beta_s^2V_2+\lambda s^2V_{\rm t}+\mathcal R_s,
\qquad \|\mathcal R_s\|_\infty\le Cs^{5/2}.
\tag{3.3}
$$

It includes every real phase, the entire expanding native domain and its complement, the original infinite-time tail and both faces. Its additional hypotheses and estimates are absolute convergence in (3.2),

$$
\begin{gathered}
|V_1|\le C(1+|r|)^{-4},\qquad |V_2|+V_{\rm t}\le C(1+|r|)^{-3},\\
V_j\circ\sigma=(-1)^jV_j,\qquad V_{\rm t}\circ\sigma=V_{\rm t},\\
h_t(r)\mathbb E_{0,r}^t[(\det M_0)^{-1/2}S_t^m\mathbf1_{S_t>L}]
 \le C_m t^{(m-7)/2}e^{-c_mL^2/t}\quad(m\in\mathbb N_0).
\end{gathered}
\tag{3.4}
$$

The corresponding full moment estimate at $L=0$ is understood without the indicator. These are source-weighted and full-space hypotheses, rather than a newly certified extension of a local heat expansion. They use $B$, not $aB$.

**Definition 3.2 (actual path and response notation).** On exactly the path

$$
\tau=s^2,\quad g_s=\chi s^3,\quad E_s=E_{s^2}(\chi s^3),\quad
\epsilon_c(s)=s^2E_s,\quad r_s=-\epsilon_c(s)/s^8=-E_s/s^6>0,
\tag{3.5}
$$

the full rescaled form and infimum are

$$
q_s^c[F]=a b_s[F]-\chi\int U_s|F|^2-a\lambda s^2\|F\|_2^2,
\qquad \inf_{\|F\|_2=1}q_s^c[F]=\epsilon_c(s).
\tag{3.6}
$$

For arbitrary norms, (3.6) is exactly $s^2\mathfrak e_{g_s,s^2}[\mathcal U_s^{-1}F]$. In particular $E_s$ is unscaled and $\epsilon_c(s)$ is rescaled. Write

$$
\begin{aligned}
A&=\int r^2|Yp|^2,& B_1&=\int rV_1p^2,& C_2&=\int V_2p^2,\\
T&=\int V_{\rm t}p^2>0,& J_2&=C_2+2B_1,\\
D_{\rm clock}&=a+\chi T,& K_{\rm base}&=3aA-\chi C_2.
\end{aligned}
\tag{3.7}
$$

All integrals use full unit Lebesgue measure. The quantities are finite by (2.10), (3.4) and Cauchy–Schwarz. They are jointly realized by the fixed source and mode.

Two actual-state antecedents will be used with their original hypotheses. The macroscopic one-sided estimate of Proposition 100.1 supplies a fixed $c>0$ with

$$
E_s\le-cs^6,\qquad r_s\ge c
\tag{3.8}
$$

for small $s$; fixed $\chi$ factors are absorbed in $c$. It does not identify a minimizing branch or a matching coefficient. For every prescribed sequence $s_n\downarrow0$ and every choice of actual normalized complex ground states $\psi_{s_n}\in D(S)$, Theorem 105.1 gives

$$
r_{s_n}\to\infty
\quad\Longleftrightarrow\quad
\operatorname{dist}_{L^2}(\mathcal U_{s_n}\psi_{s_n},\mathcal O_c)\to0,
\qquad \mathcal O_c=\{e^{i\theta}p:\theta\in\mathbb R\}.
\tag{3.9}
$$

The bounded-$r$ defect of Theorem 103.1 says that for every positive-measure compact $K$, with its original constant $\gamma_K>0$, an eventual bound $r_{s_n}\le B<\infty$ forces every weak limit $cp$ to satisfy

$$
|c|^2\le(1+\gamma_K/\sqrt B)^{-1},\qquad
\liminf_n\operatorname{dist}(\mathcal U_{s_n}\psi_{s_n},\mathcal O_c)
 \ge\left(2-2(1+\gamma_K/\sqrt B)^{-1/2}\right)^{1/2}.
\tag{3.10}
$$

Concretely, these source constants can be taken as

$$
\begin{aligned}
J_K&=\int_K Vp>0,&
b_0&=\frac{e^{-3}}{24\pi\sqrt{\det M}},&
v_M&=\frac{28\pi}{3}\sqrt{\det M},\\
C_0&=\frac{\chi^2j_0}{a^{3/2}}b_0^2v_M,&
\gamma_K&=C_0\phi(k_0)^2J_K^2.
\end{aligned}
\tag{3.11}
$$

These are actual eigenstate results, depending on negative attainment, the original two-face resolvent and its compact-charge shell estimate. They are not assumptions about trial states. The native weak-profile disk in Theorem 90.1 allows $|c|\le1$ and lost mass; it supplies no global unit norm by itself.

## 4. Relative coefficient bounds and homogeneous multipliers

**Theorem 4.1 (same-realization bounds).** There are finite constants $K_1,K_2,K_{\rm t},\Gamma$ such that on all $\mathbb R^4$,

$$
V_1^2\le K_1V,\qquad V_2^2\le K_2V,\qquad V_{\rm t}^2\le K_{\rm t}V,
\qquad
\int V^{1/2}|u|^2\le\Gamma b[u]\quad(u\in\mathcal Q_E).
\tag{4.1}
$$

Consequently $|V_1|,|V_2|,V_{\rm t}$ are bounded homogeneous form multipliers, on the full complex domain.

Proof. On the common bridge set $x=M_0^{-1/2}z$, $A_b=M_0^{-1/2}M_1M_0^{-1/2}$ and $B_b=M_0^{-1/2}M_2M_0^{-1/2}$. Matrix order gives $\|A_b\|\le S_t$ and $\|B_b\|\le S_t^2$. For $A_N=M_0^{-1/2}NM_0^{-1/2}$, matrix differentiation yields

$$
D\log\gamma[N]=-\tfrac12\operatorname{tr}A_N+\tfrac14x^{\mathsf T}A_Nx,
\qquad
D^2\log\gamma[N,N]=\tfrac12\operatorname{tr}A_N^2-\tfrac12x^{\mathsf T}A_N^2x.
\tag{4.2}
$$

Put $R_1=-2D\gamma[M_1]/\gamma$ and $R_2=(3D\gamma[M_2]+2D^2\gamma[M_1,M_1])/\gamma$. Since $D^2\gamma/\gamma=D^2\log\gamma+(D\log\gamma)^2$, every term is retained and

$$
|R_1|\le CS_t(1+|x|^2),\qquad |R_2|\le CS_t^2(1+|x|^4).
\tag{4.3}
$$

For fixed $\xi$, use the single positive measure
$d\mu_\xi=j_0^{-1}h_t(r)\gamma_{M_0}(z)dt\,d\mathbb P_{0,r}^t$ on $t\ge1$. Its mass is $V(\xi)$, and its $R_1,R_2,t$ moments are exactly $V_1,V_2,V_{\rm t}$. Cauchy–Schwarz first on finite time windows and then by convergence gives

$$
\frac{V_j^2}{V}\le\int R_j^2d\mu_\xi,\qquad
\frac{V_{\rm t}^2}{V}\le\int t^2d\mu_\xi.
\tag{4.4}
$$

A polynomial in $x$ times its Gaussian is bounded uniformly. Hence $\gamma R_1^2\le CS_t^2(\det M_0)^{-1/2}$ and $\gamma R_2^2\le CS_t^4(\det M_0)^{-1/2}$. The $m=2,4$ cases of (3.4) bound their time integrals by constants times $\int_1^\infty t^{-5/2}dt$ and $\int_1^\infty t^{-3/2}dt$. The last integral in (4.4) is bounded by $C\int_1^\infty t^2t^{-7/2}dt$. All are finite, uniformly in $\xi$. This proves the first three inequalities, justifies the time limits, and keeps the original $j_0$ factors.

The boxes $\{N\le R\}$ have volume $16R^7$. The decay of $V$ implies $V^{1/2}\in L^3\cap L^\infty$, since its $L^3$ dyadic summands are bounded by $C2^{7j}2^{-15j/2}$. Conservativity gives $\|P_tV^{1/2}\|_\infty\le\|V^{1/2}\|_\infty$ for $t\le1$. The heat bound and mass one give $\|p_E(t;0,\cdot)\|_{3/2}\le Ct^{-7/6}$. Young's inequality on this unimodular group thus gives $\|P_tV^{1/2}\|_\infty\le Ct^{-7/6}\|V^{1/2}\|_3$ for $t\ge1$. Their time integrals are bounded by a finite $\Gamma$.

For $b>0$ apply the positive-kernel weighted Schur test to
$V^{1/4}(\mathcal E+b)^{-1}V^{1/4}$, with weight $V^{1/4}$. Its weighted row integral is bounded by $\Gamma V^{1/4}$, so its operator norm is at most $\Gamma$. Factoring through $(\mathcal E+b)^{-1/2}$ gives
$\int V^{1/2}|u|^2\le\Gamma(b[u]+b\|u\|_2^2)$. Let the positive resolvent parameter decrease to zero. This proves the last part of (4.1), also for complex functions. The pointwise bounds give $|V_j|\le\sqrt{K_j}V^{1/2}$ and the analogous bound for $V_{\rm t}$, proving the assertion. $\square$

In particular, for any $L\in\{V_1,V_2,V_{\rm t}\}$,

$$
\left|\int Lp u\right|
 \le\left(\int\frac{L^2}{V}p^2\right)^{1/2}
       \left(\int V|u|^2\right)^{1/2}
 \le C\sqrt{b[u]}.
\tag{4.5}
$$

The inequalities prove finiteness and continuity. They do not combine independently attainable extrema into a sign assertion.

## 5. A compact gap in horizontal energy and the odd response

Use polarized forms conjugate linear in the first variable. All real functionals below are extended complex linearly when applied to complex vectors.

**Theorem 5.1 (homogeneous gap).** There exists $\theta>0$ such that

$$
h[u]\ge a\theta b[u]\quad\text{if }u\in\mathcal Q_E\text{ and }b(p,u)=0.
\tag{5.1}
$$

Every $\sigma$-odd vector satisfies this orthogonality. The estimate is a gap in horizontal energy, without a positive $L^2$ spectral gap above the threshold zero mode.

Proof. Spectral calculus and the bounded increasing resolvent forms in (2.9) show that $M_Vf\in D(\mathcal E^{-1/2})$ for every $f\in L^2$. Define $A_0=\mathcal E^{-1/2}M_V$. Monotone spectral convergence gives $A_0^*A_0=K_0$ and $\|A_0\|^2=C_*$. Polar decomposition and compactness of $K_0$ make $A_0$ compact. Thus $P=A_0A_0^*$ is compact positive, with the same nonzero eigenvalues and multiplicities as $K_0$.

For $f\in\mathcal Q_E$, spectral pairing gives $A_0^*\mathcal E^{1/2}f=M_Vf$, and consequently

$$
\int V|f|^2=\langle\mathcal E^{1/2}f,P\mathcal E^{1/2}f\rangle.
\tag{5.2}
$$

The critical equation implies $P\mathcal E^{1/2}p=C_*\mathcal E^{1/2}p$. The vector is nonzero, since $b[p]=\chi\mu/a>0$. Simplicity of the top eigenvalue in (2.9) therefore gives $\rho<C_*$ bounding $P$ on the orthogonal complement of $\mathcal E^{1/2}p$. Set $\theta=1-\rho/C_*$. Substitute $\mathcal E^{1/2}u$ in (5.2) and use $\chi C_*=a$ to obtain (5.1). Reflection commutes with the canonical form and $p$ is even, so $b(p,u)=0$ for odd $u$. The argument concerns the compact operator on energy coordinates and does not bound $h[u]$ below by a positive multiple of $\|u\|_2^2$. $\square$

**Definition 5.2 (response and its coefficient).** Let $\dot{\mathcal H}_-$ be the completion of the real odd compact smooth core in $\sqrt b$. Define on that core

$$
\ell(u)=2a\int r(Yp)(Yu)+\chi\int V_1p u,
\qquad
S_1=\int(V_1^2/V)p^2\le K_1.
\tag{5.3}
$$

**Theorem 5.3 (well-posed homogeneous response).** There is a unique $\Psi\in\dot{\mathcal H}_-$ with $h(\Psi,u)=\ell(u)$ for every $u$ in that real Hilbert space. Put

$$
\begin{aligned}
D_{\rm resp}&=h[\Psi]
 =\sup_{0\ne u\in C_c^\infty,\ u\circ\sigma=-u}\frac{\ell(u)^2}{h[u]},\\
C_{\rm resp}&=\nu^2(K_{\rm base}-D_{\rm resp})-\lambda D_{\rm clock}.
\end{aligned}
\tag{5.4}
$$

The supremum is zero when $\ell=0$, and

$$
0\le D_{\rm resp}
 \le\frac{(2a\sqrt A+\chi\sqrt{C_*S_1})^2}{a\theta}<\infty.
\tag{5.5}
$$

No $L^2$ or native operator-domain membership of $\Psi$ is asserted.

Proof. Cauchy–Schwarz, (4.5) and $\int V|u|^2\le C_*b[u]$ give
$|\ell(u)|\le(2a\sqrt A+\chi\sqrt{C_*S_1})\sqrt{b[u]}$. On the odd core, (5.1) and nonnegativity of $V$ give $a\theta b\le h\le a b$. Thus the two completions agree, and Riesz representation gives the unique element and (5.4)–(5.5). Odd core density is obtained by parity averaging canonical core approximants. In particular $rp$ belongs to this completion by (2.10).

For a complex $v$ with $b(p,v)=0$, its even and odd parts are $h$-orthogonal, $h$ on the even part is nonnegative, and $\ell$ vanishes there by parity. Completing the Riesz square on the real and imaginary odd parts proves, for every $c\in\mathbb C$ and real $\beta$,

$$
h[v]-2\beta\operatorname{Re}(\overline c\,\ell(v))
 \ge-\beta^2|c|^2D_{\rm resp}.
\tag{5.6}
$$

This is the inequality for arbitrary complex complements needed below. It imposes no oddness or reality on native competitors. $\square$

## 6. Every corrected-core upper construction

**Theorem 6.1 (normalized admissible correction).** Fix any real odd $u\in C_c^\infty(\mathbb R^4)$ and set $R_s=s^{-1/2}$,

$$
f_s=\eta_{R_s}p+\beta_su,
\qquad Z_s=\mathcal T_s^{-1}f_s/\|f_s\|_2.
\tag{6.1}
$$

For every sufficiently small original real $s>0$, $Z_s\in\mathcal Q_s$ is normalized and

$$
\frac{q_s^c[Z_s]}{s^2}\longrightarrow
\nu^2\{K_{\rm base}+h[u]-2\ell(u)\}-\lambda D_{\rm clock}.
\tag{6.2}
$$

In particular

$$
\limsup_{s\downarrow0}E_s\le C_{\rm resp}.
\tag{6.3}
$$

Proof. Since $sR_s\to0$, both faces lie outside the height support in (6.1). The cutoff core argument after (2.11) proves native admissibility of the first summand; the second is a compact core vector. Its phase support need not restrict that of the first summand. Parity gives the exact norm identity

$$
\|f_s\|_2^2=\|\eta_{R_s}p\|_2^2+\beta_s^2\|u\|_2^2\to1.
\tag{6.4}
$$

The weak critical equation gives $h(p,v)=0$ for every canonical form vector. For small $s$, the cutoff is identically one on the height support of $u$, so $h(\eta_{R_s}p,u)=h(p,u)=0$. The product identity
$h[g p]=a\int|g'|^2p^2$, obtained by testing with $g^2p$, and (2.11) imply

$$
h[f_s]=\beta_s^2h[u]+o(s^2).
\tag{6.5}
$$

On the support of the cutoff, $|\beta_sr|\to0$ uniformly. Expand the exact rational difference
$(1+\beta_sr)^{-2}-1=-2\beta_sr+3\beta_s^2r^2+O(|\beta_sr|^3)$. Since $Y\eta_{R_s}=0$, parity removes its base linear term, and

$$
a\int\bigl((1+\beta_sr)^{-2}-1\bigr)|Yf_s|^2
 =\beta_s^2\left(3aA-4a\int r(Yp)(Yu)\right)+o(s^2).
\tag{6.6}
$$

For its base remainder use $C|\beta_s|^3R_s\int r^2|Yp|^2=o(s^2)$. The base quadratic integral converges by $rYp\in L^2$. The terms involving $u$ have fixed compact support; their remaining products are of smaller order by Cauchy–Schwarz.

The complete field expansion (3.3) gives

$$
\int(\widetilde U_s-V)|f_s|^2
 =\beta_s^2\left(C_2+2\int V_1pu\right)+\lambda s^2T+o(s^2).
\tag{6.7}
$$

Here the base $V_1$ integral vanishes exactly by parity. Boundedness of the fields and convergence of the cutoff handle $C_2,T$; the compact cross terms give the displayed $V_1$ correction, and all other correction terms have higher powers of $s$. The remainder is bounded by $Cs^{5/2}\|f_s\|_2^2$. Finally the exact original subtraction is $-a\lambda s^2\|f_s\|_2^2$. Combine (6.5)–(6.7), then divide by (6.4). The numerator divided by $s^2$ has a finite limit, so a denominator tending to one suffices; no unproved second-order norm expansion is required.

Each fixed $u$ gives an upper bound on $\limsup E_s$. Taking their infimum and using
$\inf_u(h[u]-2\ell(u))=-D_{\rm resp}$ proves (6.3).

A single normalized recovery family can also be chosen. Take odd compact $u_m\to\Psi$ in $h$. Choose decreasing positive thresholds $s_m\to0$ so that for every $0<s\le s_m$ the fixed-$u_m$ coefficient error in (6.2) is at most $1/m$, both-face admissibility holds, and $\beta_s^2\|u_m\|_2^2\le1/m$. Require also $|\|\eta_{R_s}p\|_2^2-1|\le1/m$. Use $u_m$ for $s_{m+1}<s\le s_m$ and normalize as in (6.1). The norm tends to one and stays positive; its normalized coefficient tends to $C_{\rm resp}$. This selects admissible vectors for every small $s$ on the prescribed original path. It never inserts $\Psi$ itself into an $L^2$ or operator domain. $\square$

## 7. The whole affine family and the complete original coefficient

**Theorem 7.1 (affine response comparison).** For every fixed $t\in\mathbb R$, the normalized native trial obtained from
$f_s^t=\eta_{R_s}(1+t\beta_sr)p$, $R_s=s^{-1/2}$, has coefficient

$$
C_{\rm aff}(t)=\nu^2\{a t^2-(4aA+2\chi B_1)t+3aA-\chi C_2\}
                       -\lambda(a+\chi T).
\tag{7.1}
$$

At $t=1$ this is exactly the entire coefficient in source (108.3):

$$
C_{108}=\nu^2\{a(1-A)-\chi(C_2+2B_1)\}-\lambda(a+\chi T).
\tag{7.2}
$$

With $t_0=2A+(\chi/a)B_1$,

$$
\begin{gathered}
\min_{t\in\mathbb R}C_{\rm aff}(t)=C_{108}-a\nu^2(t_0-1)^2,\qquad
D_{\rm resp}\ge a t_0^2,\\
C_{\rm resp}\le\min_t C_{\rm aff}(t)\le C_{108},\qquad
C_{108}-C_{\rm resp}=\nu^2h[\Psi-rp]\ge0.
\end{gathered}
\tag{7.3}
$$

Proof. The cutoff strip is native admissible, $sR_s\to0$, and $rp\in L^2$ gives $\|f_s^t\|_2\to1$. The product identity and parity give

$$
h[f_s^t]
 =a\int|\eta_{R_s}'|^2p^2
  +a t^2\beta_s^2\int|\eta_{R_s}+r\eta_{R_s}'|^2p^2
 =a t^2\beta_s^2+o(s^2).
\tag{7.4}
$$

The term linear in $t\beta_s$ is odd. The second multiplier is bounded and tends pointwise to one. Rational expansion of
$((1+\beta_sr)^{-2}-1)(1+t\beta_sr)^2$ gives the even quadratic coefficient $(3-4t)\beta_s^2r^2$. Its cubic remainder is bounded, on the support, by $C_t|\beta_s|^3R_s r^2$, and its linear term is odd. Thus the kinetic difference from $b$ is $a(3-4t)\beta_s^2A+o(s^2)$.

For the complete potential, the $V_1$ term contributes $2t\beta_s^2B_1$; its base and cubic terms are odd. The $V_2$ term contributes $\beta_s^2C_2$, its linear cross term is odd, and its quadratic amplitude correction is $O(s^4)\int r^2p^2$. The clock field similarly contributes $\lambda s^2T$, with vanishing odd cross term and an $O(s^4)$ weighted correction. The uniform remainder costs $O(s^{5/2})\|f_s^t\|_2^2$. Retain $-a\lambda s^2\|f_s^t\|_2^2$ and normalize. This proves (7.1), including all rational kinetic, $V_2+2rV_1$, raw-source and clock terms.

The minimum of the scalar quadratic occurs at $t_0$. Moreover $h[rp]=a$ and $\ell(rp)=2aA+\chi B_1=a t_0$, so the Riesz supremum gives $D_{\rm resp}\ge a t_0^2$. The exact square identity
$h[\Psi-rp]=D_{\rm resp}+a-2\ell(rp)$ proves the final equality and all comparisons in (7.3). Neither comparison evaluates a sign. $\square$

## 8. Supportwise auxiliary coefficient and uniform local coercivity

**Lemma 8.1 (an exact estimating extension).** Choose $\delta_*>0$ sufficiently small that for $0<\delta\le\delta_*$ the strip $|r|\le3\delta/s$ lies strictly between both original faces and $3\nu\delta<1/4$. Let $\rho\in C_c^\infty(\mathbb R)$ be even, $0\le\rho\le1$, one on $[-2,2]$ and zero on $|r|\ge3$. Define

$$
d_{s,\delta}(r)=
\begin{cases}
\rho(sr/\delta)((1+\beta_sr)^{-2}-1),& |r|<3\delta/s,\\
0,&|r|\ge3\delta/s.
\end{cases}
\tag{8.1}
$$

The rational expression is evaluated only in the first branch. It has no singularity there. In particular (8.1) does not multiply an undefined remote singularity by zero. Put

$$
\begin{aligned}
\widehat q_{s,\delta}[u]
 =h[u]+a\int d_{s,\delta}|Yu|^2
 -\chi\int(\beta_sV_1+\beta_s^2V_2+\lambda s^2V_{\rm t}+\mathcal R_s)|u|^2
 -a\lambda s^2\|u\|_2^2.
\end{aligned}
\tag{8.2}
$$

This is an estimating form on $\mathcal Q_E$. On vectors supported in $|r|\le2\delta/s$, it agrees exactly with the original sheared $q_s^c$, including its original multiplier. It is not a replacement native operator.

For every such complex supported vector $u$, define

$$
c=\frac{b(p,u)}{b[p]}=\frac{\int Vp u}{\mu},\qquad v=u-cp.
\tag{8.3}
$$

There are $c_1,C>0$, independent of sufficiently small fixed $\delta$, such that for all sufficiently small $s$,

$$
\widehat q_{s,\delta}[u]\ge c_1b[v]-Cs^2\|u\|_2^2.
\tag{8.4}
$$

The eventual small-$s$ threshold is allowed to depend on $\delta$.

Proof. Exact agreement follows from (2.3), (3.3) and $\rho=1$ on the indicated support. Smoothness of the cutoff makes (8.1) a bounded smooth coefficient. Uniformly for $\delta\le\delta_*$,

$$
\begin{gathered}
|d_{s,\delta}|\le C\delta,\qquad
|d_{s,\delta}|\le C|\beta_sr|\rho(sr/\delta),\\
|d_{s,\delta}+2\beta_sr\rho(sr/\delta)|
 \le C\beta_s^2r^2\rho(sr/\delta).
\end{gathered}
\tag{8.5}
$$

The weak critical equation proves the equality in (8.3), and $Vp\in L^2$ gives $|c|\le C\|u\|_2$, $\|v\|_2\le C\|u\|_2$, $b(p,v)=0$. Also $h[u]=h[v]$. The gap (5.1) applies.

In the kinetic expansion of (8.2), the base linear integral against $|Yp|^2$ vanishes by parity, so (8.5) bounds its remaining base term by $C\beta_s^2A|c|^2$. The cross term is bounded by $Cs|c|\sqrt{b[v]}$, using $rYp\in L^2$, and the $v$ diagonal term is at least $-C\delta b[v]$. This decomposition uses the extension on $p$ and $v$ outside the strip, where each is defined; exact agreement with the native form is needed only for their sum $u$.

For the potential, the $V_1$ base term is zero. The $V_2,V_{\rm t}$ base terms cost at most $Cs^2|c|^2$. Formula (4.5) bounds the cross terms by $C(s+s^2)|c|\sqrt{b[v]}$, and Theorem 4.1 bounds the diagonal coefficient terms by $C(s+s^2)b[v]$. Keep the residual as a form on $u$, bounding it by $Cs^{5/2}\|u\|_2^2$, and keep the exact threshold subtraction. Consequently

$$
\widehat q_{s,\delta}[u]
 \ge(a\theta-C\delta-Cs)b[v]
       -Cs|c|\sqrt{b[v]}-Cs^2(|c|^2+\|u\|_2^2).
\tag{8.6}
$$

Choose $\delta_*$ smaller if necessary, then $s$ small, to preserve a fixed fraction of $a\theta$. Young's scalar inequality in $\sqrt{b[v]}$ and $|c|\le C\|u\|_2$ prove (8.4) with constants uniform over these fixed $\delta$. All steps hold for complex $u$, irrespective of kinetic size. $\square$

## 9. The improved lower error for every original complex state

**Theorem 9.1 (full-domain critical lower estimate).** There are $C,s_0>0$ depending only on the fixed original data such that

$$
q_s^c[F]\ge-Cs^2\|F\|_2^2
\quad(0<s<s_0,\ F\in\mathcal Q_s\text{ complex}).
\tag{9.1}
$$

Thus, using the credited macroscopic direction,

$$
-C\le E_s<0,\qquad cs^8\le-\epsilon_c(s)\le Cs^2,
\qquad c\le r_s\le Cs^{-6}.
\tag{9.2}
$$

Proof. Fix one $\delta\in(0,\delta_*]$ and put $R=\delta/s$. For arbitrary $F\in\mathcal Q_s$ set $f=\mathcal T_sF$, and use the exact quadratic partition $\eta_R^2+\zeta_R^2=1$ from (2.11). Products preserve the native closed domain. The inner vector $u=\eta_R f$, zero extended, belongs to $\mathcal Q_E$ by native core approximation and strip norm equivalence. Since $Y$ differentiates neither cutoff, the exact horizontal IMS identity is

$$
\widetilde q_s^c[f]
 =\widetilde q_s^c[\eta_Rf]+\widetilde q_s^c[\zeta_Rf]
    -a\int(|\eta_R'|^2+|\zeta_R'|^2)|f|^2,
\qquad \widetilde q_s^c=q_s^c\circ\mathcal T_s^{-1}.
\tag{9.3}
$$

It holds first on the smooth native core, then on the entire complex domain by closure. Lemma 8.1 bounds the inner term below by $-Cs^2\|\eta_Rf\|_2^2$.

For the outer term retain the exact nonnegative native free threshold form $aC_s$, transported by the shear, with both original Dirichlet faces. The actual height tail (2.7) gives

$$
\sup_{|r|\ge\delta/s}\widetilde U_s\le C_\delta s^5,
\qquad
\widetilde q_s^c[\zeta_Rf]\ge-C_\delta s^5\|\zeta_Rf\|_2^2.
\tag{9.4}
$$

Using only $A_s\ge0$ and discarding its threshold subtraction would lose this stronger outer bound. Here no native height tail or moving-face region is omitted. The IMS integral is at most $C_\delta s^2\|f\|_2^2$. Summing, using the norm partition and unitarity, proves (9.1) for every native vector. Fixing $\delta$ makes its final constant a fixed-data constant. Infimizing gives $E_s\ge-C$; negative attainment from Proposition 75.2 and the one-sided estimate (3.8) give (9.2). This improves the supplied $O(s^{2/3})$ error in source Theorem 98.1. $\square$

## 10. A response lower bound for actual unit-profile sequences

**Theorem 10.1 (unit-profile lower implication).** Let $s_n\downarrow0$ be any prescribed sequence, and for each $n$ choose an actual normalized complex ground state $\psi_{s_n}\in D(S)$ on (3.5). If

$$
\operatorname{dist}(F_{s_n},\mathcal O_c)\to0,
\qquad F_s=\mathcal U_s\psi_s,
\tag{10.1}
$$

then

$$
\liminf_n E_{s_n}\ge C_{\rm resp}.
\tag{10.2}
$$

Proof. Remove a constant phase from each actual state so that $F_s\to p$ globally in $L^2$ along the sequence. The determinant-one shears are unitary and converge strongly to the identity: this follows on compact continuous functions from $L_s\to I$, and on $L^2$ by density. Therefore $f_s=\mathcal T_sF_s\to p$ globally, since
$\|\mathcal T_s(F_s-p)\|_2=\|F_s-p\|_2$ and $\mathcal T_sp\to p$. No spatially varying phase or phase derivative is used.

Fix any $\delta\in(0,\delta_*]$ before taking a limit. Put $R=\delta/s$, $u_s=\eta_Rf_s$ and decompose it by (8.3) as $u_s=c_sp+v_s$. Then $u_s\to p$ globally, $\|u_s\|_2\to1$, and $c_s\to1$, because $Vp\in L^2$. The IMS error is now

$$
C_\delta s^2\int_{\delta/s\le|r|\le2\delta/s}|f_s|^2=o_\delta(s^2).
\tag{10.3}
$$

Indeed its mass tends to zero by global strong convergence to the fixed $L^2$ vector $p$. The outer error is $O_\delta(s^5)$. Hence (9.3)–(9.4) imply

$$
\epsilon_c(s)\ge\widehat q_{s,\delta}[u_s]-o_\delta(s^2),
\qquad
\widehat q_{s,\delta}[u_s]\le\epsilon_c(s)+o_\delta(s^2)\le o_\delta(s^2),
\tag{10.4}
$$

where actual native negativity gives the final inequality. The enhanced local estimate (8.4) now gives $b[v_s]=O(s^2)$ at fixed $\delta$. More precisely there is a constant $B_0$ independent of small fixed $\delta$ such that

$$
\limsup_{s\to0}\frac{b[v_s]}{s^2}\le B_0.
\tag{10.5}
$$

This follows by dividing (8.4) and (10.4) by $s^2$: $c_1,C$ are uniform in $\delta$, $\|u_s\|_2\to1$, and the IMS contribution tends to zero at each fixed $\delta$. Uniform IMS little-oh as $\delta\downarrow0$ is not required.

Write $d=d_{s,\delta}$. Its exact expansion on its defined support and parity give

$$
\int d|Yp|^2=3\beta_s^2A+o_\delta(s^2),
\qquad
\|(d/\beta_s+2r)Yp\|_2\to0.
\tag{10.6}
$$

For the first assertion subtract the exactly odd term $-2\beta_sr\rho(sr/\delta)$. The quotient of the remaining coefficient by $\beta_s^2$ converges pointwise to $3r^2$ and is dominated by $Cr^2$. For the second, the coefficient tends pointwise to zero after addition of $2r$, and is bounded by $C|r|$ on the whole space, including outside the auxiliary support. Both assertions follow by $rYp\in L^2$ and dominated convergence. Thus the kinetic cross term is

$$
-4a\beta_s\operatorname{Re}\left(\overline{c_s}\int r(Yp)(Yv_s)\right)
                 +o_\delta(s^2).
\tag{10.7}
$$

Its $v_s$ diagonal is bounded below by $-C\delta b[v_s]$. By (10.5), its limiting error divided by $s^2$ is at worst $-C'\delta$ with $C'$ independent of small fixed $\delta$.

Expand the entire potential in (8.2), keeping the remainder on $u_s$. Its base $V_1$ term vanishes, its leading cross term is
$-2\chi\beta_s\operatorname{Re}(\overline{c_s}\int V_1pv_s)$, and its base $V_2,V_{\rm t}$ integrals are $|c_s|^2C_2$ and $|c_s|^2T$. The diagonal $V_1$ term is $O(s b[v_s])=O(s^3)$ by Theorem 4.1. The $V_2,V_{\rm t}$ cross terms are $O(s^2\sqrt{b[v_s]})=O(s^3)$ by (4.5), and their diagonals are $O(s^2b[v_s])=O(s^4)$. The residual costs $O(s^{5/2})\|u_s\|_2^2=o(s^2)$. Keep the original threshold term exactly. Using $h[u_s]=h[v_s]$ yields the limiting lower estimate

$$
\begin{aligned}
\widehat q_{s,\delta}[u_s]\ge{}&h[v_s]
 -2\beta_s\operatorname{Re}(\overline{c_s}\ell(v_s))
 +|c_s|^2\beta_s^2K_{\rm base}\\
 &-\chi\lambda s^2|c_s|^2T-a\lambda s^2\|u_s\|_2^2
 -C'\delta s^2+o_\delta(s^2).
\end{aligned}
\tag{10.8}
$$

Here the $-C'\delta$ assertion is interpreted in liminf, as supplied by (10.5); an arbitrarily small additional error can be absorbed in $o_\delta(s^2)$. Apply (5.6) to the whole complex $v_s$. Divide (10.8) and (10.4) by $s^2$, use $c_s\to1$, $\|u_s\|_2\to1$ and $\beta_s/s=\nu$, to obtain

$$
\liminf_{s\to0}E_s\ge C_{\rm resp}-C'\delta.
\tag{10.9}
$$

Take $s\to0$ first at each fixed $\delta$, then $\delta\downarrow0$. This proves (10.2). Global unit norm was an explicit hypothesis at the start; it was never inferred from the native weak-profile disk, local convergence or a successful trial. $\square$

## 11. Matching actual energy and every nonzero-sign alternative

**Theorem 11.1 (actual unscaled energy limit).** On the unchanged original full complex problem and exact critical path,

$$
\boxed{\displaystyle\lim_{s\downarrow0}E_{s^2}(\chi_cs^3)
                      =\min(0,C_{\rm resp}).}
\tag{11.1}
$$

Proof. Theorem 6.1 and native negativity give $\limsup E_s\le\min(0,C_{\rm resp})$. Theorem 9.1 bounds $E_s$ below by a finite constant. If its liminf were strictly smaller, a sequence could be chosen with $E_s\to L<\min(0,C_{\rm resp})$. In particular $L<0$, so $r_s=-E_s/s^6\to\infty$ there. Choose actual normalized ground states; Proposition 75.2 gives existence and $D(S)$ membership at each positive cutoff. The actual equivalence (3.9), with precisely these hypotheses, supplies global convergence to $\mathcal O_c$. Theorem 10.1 forces $L\ge C_{\rm resp}$, a contradiction. This proves the matching lower direction. No equality of an actual infimum was inferred from an upper construction alone. $\square$

**Theorem 11.2 (conditional actual scale and profile alternatives).** The following statements concern each fixed original admitted datum satisfying the standing antecedents.

If $C_{\rm resp}<0$, then

$$
\epsilon_c(s)=C_{\rm resp}s^2+o(s^2),\qquad
r_s\sim(-C_{\rm resp})s^{-6}\to\infty.
\tag{11.2}
$$

For every prescribed sequence $s_n\downarrow0$ and every actual normalized complex ground-state choice, $\operatorname{dist}(F_{s_n},\mathcal O_c)\to0$. Equivalently every such chosen family converges to that orbit as $s\downarrow0$.

If $C_{\rm resp}>0$, there exist fixed-data constants $0<c\le B<\infty$ and $s_0>0$ such that for all $0<s<s_0$,

$$
c\le r_s\le B,\qquad -\epsilon_c(s)=\Theta(s^8),\qquad -E_s=\Theta(s^6).
\tag{11.3}
$$

For every prescribed sequence and every actual normalized complex ground-state choice, every fixed positive-measure compact $K$ gives the strictly positive orbit defect (3.10) with this $B$. Every subsequence has a weakly convergent further subsequence of the form $cp$, whose coefficient satisfies (3.10). Neither the coefficient of the energy on the $s^8$ rescaled scale nor a replacement actual profile is identified.

If $C_{\rm resp}=0$, the established conclusions are

$$
E_s\to0,\qquad c\le r_s=o(s^{-6}).
\tag{11.4}
$$

Bounded, divergent, or mixed subsequential behavior of $r_s$ remains undecided; (3.9) still governs each actual sequence to which it applies.

Proof. A negative response makes (11.1) a strictly negative limit. The identities (3.5) give (11.2), and (3.9) gives convergence for every actual choice.

For positive response, if $r_s$ had no eventual finite upper bound, one could select $s_n\downarrow0$ with $r_{s_n}\to\infty$. Choose any actual ground states on this sequence. Equivalence (3.9) gives the unit orbit, whereas Theorem 10.1 gives $\liminf E_{s_n}\ge C_{\rm resp}>0$, contradicting native negativity. Thus $r_s\le B$ eventually. The independent macroscopic one-sided bound supplies $r_s\ge c>0$, proving (11.3). The actual bounded-$r$ theorem (3.10) gives the stated defect and weak-limit restrictions for every choice. This is an actual lower argument, rather than failure of an affine or corrected trial.

At response zero, (11.1) and (3.5) give (11.4), with the positive lower bound again from (3.8). A vanishing unscaled energy has no implication deciding boundedness versus divergence after division by $s^6$. No occurrence of either nonzero-sign case or of response zero is established merely by listing these alternatives. $\square$

## 12. Canonical reduction and the unchanged complete-sign question

**Proposition 12.1 (normalization without sign evaluation).** Put

$$
W=j_0V,\quad W_j=j_0V_j,\quad W_{\rm t}=j_0V_{\rm t},\quad
\overline C=j_0C_*.
\tag{12.1}
$$

The canonical heat, these $W$ fields and $\overline C$ have no remaining original fixed-data parameter. The normalized mode solves $\mathcal Ep=\overline C^{-1}Wp$ and is canonical. Define

$$
G_{108}=1-A-(\chi/a)(C_2+2B_1),\qquad
G_{\rm resp}=(K_{\rm base}-D_{\rm resp})/a,\qquad
\overline D=1+(\chi/a)T>1.
\tag{12.2}
$$

These are constants of this particular canonical source and

$$
\frac{C_{108}}a=\nu^2G_{108}-\lambda\overline D,\qquad
\frac{C_{\rm resp}}a=\nu^2G_{\rm resp}-\lambda\overline D,
\qquad G_{\rm resp}\le G_{108}.
\tag{12.3}
$$

Proof. The factors in (12.1) remove exactly the original $1/j_0$ from the heat integrals. The threshold quotient gives $\chi/a=j_0/\overline C$. Hence $h$ and $\ell$ are $a$ times canonical forms and functionals, $\Psi$ is canonical in energy space, and $D_{\rm resp}/a$ is canonical. Substitution in (5.4) and (7.2) proves (12.3). Strict positivity of $T$ gives $\overline D>1$. $\square$

The identities do not evaluate $G_{108}$ or $G_{\rm resp}$, and do not prove that every ratio $\lambda/\nu^2$ occurs under the original interval, pole and admissibility constraints. If $G_{\rm resp}\le0$ were proved, $\lambda>0$ would force a negative response for all original data. That inequality is not proved here. If $G_{\rm resp}>0$, the sign comparison is with the actual ratio $\lambda/\nu^2$ and $G_{\rm resp}/\overline D$, retaining its original parameter restrictions. Occurrence on either side and at equality is not established here.

The original task of signing the complete $C_{108}$ for the entire admitted family remains active. Its negative clock term alone does not sign its rational and response terms. A nonnegative $C_{108}$ does not imply profile failure, since $C_{\rm resp}$ can be smaller. The present comparison, response limit and conditional alternatives therefore do not relabel the original full-family decision as complete. The still required relations are an evaluated same-realization complete affine sign, an evaluated response sign over the permitted original data, and, if response zero occurs, a finer actual energy and $r_s$ analysis. Even in the positive case, the exact finer coefficient, centered crossover and replacement profile remain separate questions.

## 13. Source credit and realization boundaries

**Definition 13.1 (scope and attribution).** Sections 70–75 of the companion source supply the original threshold field, raw source, entire complex domains and fixed-positive-cutoff negative attainment. Sections 78 and 81 supply the exact privileged chart, Jacobian and conjugacy. Sections 82–83 supply canonical and native heat estimates, integrated tails, local compactness and admissible recovery; §§84, 87 and 88 supply the homogeneous threshold bound, compact zero-energy Birman–Schwinger operator and simple attained critical mode. Sections 89–91 distinguish tangent onset and the native weak-profile disk from actual unit-mass selection. Sections 92–96 retain the original observation, infinite-fibre, quantum and preparation boundaries.

The exact rational shear and common-bridge comparison belong to §97. The previous full-domain $O(s^{2/3})$ lower error is Theorem 98.1. The macroscopic branch is used only in the one-sided energy direction of Proposition 100.1. The actual compact-charge shell estimate and bounded-$r$ defect are §§102–103; global finite-native resolvent reconstruction and actual scale/no-loss equivalence are §§104–105. The weighted mode, parity and cutoff estimate are §106; the complete same-bridge field expansion with its full-space remainder is §107. The specified complete affine coefficient is §108 and is recovered in full in (7.2).

The homogeneous response formulation, its coefficient-field estimates, improved lower estimate, matching actual energy and conditional alternatives are the substantive companion increment developed from the supplied response analysis and its independent mathematical assessment. The proofs in this volume carry those deductions; an assessment or approval is not a mathematical premise. Riesz representation, spectral calculus, compact polar and spectral theory, Schur, Young, Cauchy–Schwarz, IMS, parity and dominated convergence are mature intermediate tools. The original cited heat/localization and library literature retain their supplied conditional scope; this volume adds no external reauthentication or literature-wide originality claim.

All results fix the original signed nonzero $\kappa$, source, positive cutoffs, $a,\varepsilon$, raw densities, all real phase frequencies and both height deaths. There is no claimed uniformity as $\kappa\to0$, theorem on the actual zero leaf or a wrapped cover, cutoff-free realization, isotropic phase-$H^1$ restriction, physical three-space or physical $SO(3)$ selection. The real odd space organizes the response; actual states remain arbitrary complex vectors in the original domains.

Analytic amplitudes do not supply native amplitude preparation, lawful transport realization, acquisition of the relevant density, or timing and resource permissions. This differential-operator phase/spectral theorem is distinct from the selected-input acquired-mass quantity also denoted $E_s$ in other quantum volumes: a shared symbol or scale supplies no task, resource or full-channel bridge. There is no claim of native feasibility, efficiency, impossibility or capacity, autonomous reduced quantum dynamics, generic neural-network or empirical machine-learning performance, ML implementation migration, or completion of a through-2027 programme. There is no Lean/kernel/frozen certification or executed mathematical/numerical validation. The full-family sign, response-zero finer scale, and realization obligations remain at their explicit boundaries.

## 追加锚（本行以下为增补区）


## 14. Exact native ratio images and the admission neighbourhood

**Proposition 14.1 (fixed interval, interior pole and signed window).**
Write $R=\lambda/\nu^2$ and $L=u-l$. For any fixed admitted $H,I,\kappa\ne0$,
varying only $k_0\in(l,u)$ gives exactly the open interval

$$
R=\pi^2\frac{(k_0-\alpha_\kappa)^2}{L^2},\qquad
\mathscr R_\kappa=
\left(\frac{\pi^2(l-\alpha_\kappa)^2}{L^2},
      \frac{\pi^2(u-\alpha_\kappa)^2}{L^2}\right).
\tag{14.1}
$$

More specifically fix $0<H<1/2$, $0<l<u<H$ and an explicit radius
$0<b<\min\{l/4,(H-u)/2,H/4\}$ as in G (16.2).
With $k_0$ varying over $I$, the respective images for $0<\kappa\le b$
and $-b\le\kappa<0$ are exactly

$$
\mathscr R_+=\left(\frac{\pi^2(l-b-b^2/H)^2}{L^2},
                          \frac{\pi^2u^2}{L^2}\right),\qquad
\mathscr R_-=\left(\frac{\pi^2l^2}{L^2},
                          \frac{\pi^2(u+b-b^2/H)^2}{L^2}\right).
\tag{14.2}
$$

Every interior value in (14.1)–(14.2) is attained; neither endpoint is.
With $k_0$ fixed instead, the positive and negative window images are

$$
\left[\frac{\pi^2(k_0-b-b^2/H)^2}{L^2},\frac{\pi^2k_0^2}{L^2}\right),\qquad
\left(\frac{\pi^2k_0^2}{L^2},\frac{\pi^2(k_0+b-b^2/H)^2}{L^2}\right].
$$

The included endpoints occur only at $\kappa=b,-b$, respectively;
the excluded endpoints require $\kappa=0$.
This explicit window meets the larger-height-interval geometric and
scalar-fibre requirements of L Definition 35.1, with the original rational
coefficients. The heat, domain, mode and complete-field antecedents of
this volume retain their supplied ordinary conditional status.

Proof. The factors $\varepsilon^2$ cancel in $\lambda/\nu^2$.
Since $l-\alpha_\kappa>0$, the map in (14.1) is strictly increasing
and continuous in $k_0$, with precisely the displayed endpoint limits.
On $[-b,b]$, $\alpha_\kappa'=1+2\kappa/H>0$.
For positive $\kappa$, its range is $(0,b+b^2/H]$; for negative
$\kappa$, it is $[-b+b^2/H,0)$. The differences $k_0-\alpha_\kappa$
therefore have infimum and supremum $l-b-b^2/H,u$ in the first case,
and $l,u+b-b^2/H$ in the second. None is attained because $k_0$
is interior (and the zero parameter is excluded). Each parameter-pole
rectangle is connected and the difference is continuous, so its image
is an interval. These infima and suprema thus prove every intermediate
value occurs. All differences are positive, so squaring preserves the
intervals and their endpoint exclusions. Subtracting the same alpha
intervals from a fixed $k_0$ proves the half-open images as well.

For the analytic neighbourhood, strictness of the bound on $b$ allows
$b'>b$ and $0<l'<l<u<u'<H$ with
$b'<\min\{l'/4,(H-u')/2,H/4\}$. On the compact rectangle
$[-b',b']\times[l',u']$, the original five probabilities
$(k-2\kappa,H+\kappa-k,1-2H,H+\kappa-k,k)$ have positive margins.
For $\kappa\ge0$, $\alpha_\kappa\le5b'/4<5l'/16$; for
$\kappa<0$, $\alpha_\kappa<0$. Thus $k-\alpha_\kappa$ has a
positive margin. Formula (1.3) is nonzero there since $b'<H/4$;
compactness gives a uniform determinant lower bound and bounded
coefficient derivatives of every fixed order.
The numerator coefficient map $e\mapsto P_{\kappa,e}$ in G (26.7)
is invertible throughout this rectangle: a zero polynomial would give
$e\cdot c_\kappa=e\cdot c_\kappa'=e\cdot c_\kappa''=0$, forcing
$e=0$. Its inverse is uniformly bounded by compactness.
Consequently the sublevel, height Poincare and scalar semigroup proof
of G (26.6), (26.12) applies on the whole explicit window, with constants
depending on this fixed rectangle. The determinant and derivative bounds
are exactly G (32.2)'s larger-cylinder hypotheses for its supplied local
heat estimate. Restriction to $[-b,b]$ therefore supplies the neighbourhood
required in L Definition 35.1; no unknown further parameter shrink is
needed for these conditions. The pole may be any interior point, and
none of these restrictions depends on a subsequent heat time.
The inherited analytic suppliers retain their conditional status. $\square$

## 15. Occurrence across distinct fixed native datasets

**Proposition 15.1 (full ratio image for each sign).**
Fix any $H\in(0,1/2)$ and any $a,\varepsilon>0$.
Across distinct datasets obeying the explicit window of Proposition 14.1,
for each prescribed sign of $\kappa\ne0$ the exact ratio image is $(0,\infty)$.
Here intervals, poles and nonzero parameters may differ between datasets;
each is fixed before its own critical limit. The endpoint zero is not
attained and there is no finite upper endpoint.

Proof. Positivity and finiteness follow from (14.1). Given any $R_*>0$,
put $x=\sqrt{R_*}/\pi$, $t_0=\min\{x/2,1/2\}$ and
$L=H/[2(x+1)]$. For the prescribed sign choose $\kappa=\pm\delta$
with $\delta>0$ small, and set

$$
l=\alpha_\kappa+(x-t_0)L,\quad
k_0=\alpha_\kappa+xL,\quad
u=\alpha_\kappa+(x+1-t_0)L.
\tag{15.1}
$$

At $\delta=0$ these endpoints satisfy $0<l<k_0<u<H/2$.
By continuity, for all sufficiently small positive $\delta$ they satisfy
$2\delta<\min\{l/4,(H-u)/2,H/4\}$. Taking the fixed radius
$b=2\delta$ proves all original explicit admission restrictions,
and Proposition 14.1 supplies the larger analytic neighbourhood.
The original means are $X=Y=H+\kappa$ and $Z=1-2H$; no jet is
chosen independently. Since $k_0-\alpha_\kappa=xL$, the ratio is
exactly $R_*$. This proves surjectivity for each sign, including all
intermediate values, while zero requires the impossible $d_0=0$.
$\square$

**Corollary 15.2 (nonempty actual critical-orbit regime and occurrence dictionary).**
Retain all standing antecedents and set $Q=G_{\rm resp}/\overline D$.
For any dataset in Propositions 14.1–15.1, $R>Q$ gives $C_{\rm resp}<0$
and hence every actual normalized complex ground-state choice converges
under the original $\mathcal U_s$ to $\mathcal O_c$ as $s\downarrow0$.
For every fixed admitted nonzero signed $\kappa$ in the explicit window,
this regime is nonempty even with $H,k_0,a,\varepsilon$ fixed: replace
$I$ by any sufficiently narrow fixed symmetric interval about $k_0$.
For each open image $(A,B)$ in (14.1) or (14.2), negative, positive and
zero response occur respectively exactly when $B>Q$, $A<Q$ and
$A<Q<B$. Across the distinct datasets of Proposition 15.1, negative
response always occurs for each sign; positive and zero response each
occur if and only if $G_{\rm resp}>0$.

Proof. Equation (12.3) gives the exact identity
$C_{\rm resp}=a\nu^2\overline D(Q-R)$, with positive prefactor.
For the symmetric interval $(k_0-h,k_0+h)\subset I$, the same explicit
radius remains admissible, while $R=\pi^2d_0^2/(4h^2)\to\infty$
as $h\downarrow0$. Fix any sufficiently small $h>0$ with $R>Q$
before taking $s\downarrow0$; Theorem 11.2 gives the asserted actual
orbit convergence and $r_s\sim(-C_{\rm resp})s^{-6}$.
The open-image assertions follow by intersection with $(Q,\infty)$,
$(0,Q)$ and $\{Q\}$ respectively; Proposition 15.1 gives the full
positive-axis image. For positive response the actual bounded-$r_s$
scale and orbit defect are exactly Theorem 11.2, not an identified
replacement profile. At zero response only (11.4) and the sequencewise
criterion (3.9) apply; the actual $r_s$ decision remains unresolved.
These are `repo-derived` parameter and actual-state consequences, with
no evaluation of the canonical constants or sign for an arbitrary
fixed datum. They assert no preparation of analytic amplitudes, positive
$L^2$ spectral gap, $L^2$ response vector, finer coefficient, physical
dimension or kernel verification. $\square$

## 追加锚（本行以下为增补区）
## 16. Particular response reconstruction in the canonical form domain

**Definition 16.1 (common realization and reconstruction convention).** Retain Definitions 1.1–3.2 and their conditional analytic antecedents, including the original raw source, $B$ heat clock, fixed signed nonzero $\kappa$, full rational vector, both height deaths and entire complex native domains. Write $h_0=h/a$, $\gamma=\chi_c/a=C_*^{-1}$, $\mathcal L=\ell/a$ and $\nabla_H=(X,Y)$. The real odd homogeneous energy space is $\dot{\mathcal H}_-$, with

$$
\theta b[u]\le h_0[u]\le b[u],\qquad 0<\theta<1.
\tag{16.1}
$$

The local representatives and injection of this completion are those of [Height projection and cutoff overlap](FIB_NATIVE_CRITICAL_HEIGHT_PROJECTION_AND_CUTOFF_OVERLAP_BOUNDS.md), Theorem 4.1. Its Theorem 5.1 supplies the exact height projection $U_h=pF_*$, where $F_*(0)=0$, $F_*'=q_*=J/\rho$, and

$$
h_0[U_h]=\mathcal L(U_h)=I_h=\int p^2q_*^2.
\tag{16.2}
$$

[Entire-height response escape](FIB_NATIVE_ENTIRE_HEIGHT_RESPONSE_ESCAPE.md), §§3–5, and [Exterior response gain](FIB_NATIVE_EXTERIOR_RESPONSE_GAIN_BOUND.md), Lemmas 4.1–4.2, supply the full-space bounds

$$
p\le C(1+\mathfrak d)^{-5},\quad |\nabla_Hp|\le C(1+\mathfrak d)^{-6},
\quad \|q_*\|_\infty<\infty,\quad |F_*(r)|\le C|r|,
\tag{16.3}
$$

and the positive heat fundamental solution $\mathcal G=\int_0^\infty p_E(t;0,\cdot)dt$, homogeneous of degree $-5$. Here $\mathfrak d(\xi)=d(0,\xi)$ for the original homogeneous control metric; it is invariant under $\sigma$ and satisfies $\mathfrak d\ge c_r|r|$ for a fixed $c_r>0$. Its balls $\mathbb B_R$ have volume $v_dR^7$. All these suppliers refer to the same $p,V,V_1,V_2,V_{\rm t}$.

Use the ordered group convolution

$$
(f*g)(\xi)=\int f(\eta)g(\eta^{-1}\xi)d\eta,\qquad Y^{\rm R}=\partial_y.
\tag{16.4}
$$

An output left invariant derivative acts on the second factor. An input derivative satisfies $(Yf)*g=f*(Y^{\rm R}g)$, since $Y_\eta g(\eta^{-1}\xi)=-(Y^{\rm R}g)(\eta^{-1}\xi)$. These identities follow from (2.4); the convolution factors are not interchangeable. The matching primary formulas are Bahouri–Barilari–Gallagher–Léautaud, [arXiv:2206.10396v1](https://arxiv.org/pdf/2206.10396v1), (3.6)–(3.13), (3.24)–(3.25) and (5.12).

**Theorem 16.2 (the particular free response and three form representatives).** Define

$$
F=rYp,\qquad g_1=\gamma V_1p,\qquad
w_{\rm f}=-2F*(Y^{\rm R}\mathcal G)+g_1*\mathcal G.
\tag{16.5}
$$

The integrals converge absolutely, $w_{\rm f}=O((1+\mathfrak d)^{-4})$, and

$$
w_{\rm f}\in\mathcal Q_E\cap\dot{\mathcal H}_-,\qquad
b(w_{\rm f},u)=\mathcal L(u)\quad(u\in\dot{\mathcal H}_-).
\tag{16.6}
$$

For the particular Riesz response $\Psi$ of Theorem 5.3,

$$
U_h,\ \Psi,\ v:=\Psi-U_h\in\mathcal Q_E\subset L^2.
\tag{16.7}
$$

Proof. Theorem 4.1 and (16.3) give $F=O((1+\mathfrak d)^{-5})$ and $g_1=O((1+\mathfrak d)^{-15/2})$. Thus $F,g_1\in L^2$ and $g_1\in L^1$. Homogeneity and smoothness off zero give $|Y^{\rm R}\mathcal G|\le C\mathfrak d^{-6}$. This is also its distributional derivative at zero: cutting out a ball of radius $\epsilon$ leaves an integration-by-parts error bounded by $C\epsilon^{-1}\int_{\mathbb B_{C\epsilon}}\mathfrak d^{-5}=O(\epsilon)$.

At an output with $\mathfrak d=R\ge2$, split the first convolution into inputs within $R/2$ of zero, within $R/2$ of the output, and the remaining set. The first two contributions are bounded by

$$
CR^{-6}\int_{\mathbb B_{R/2}}(1+\mathfrak d)^{-5}\le CR^{-4},\qquad
CR^{-5}\int_{\mathbb B_{R/2}}\mathfrak d^{-6}\le CR^{-4}.
$$

On the remainder with input radius at most $2R$, the volume is $O(R^7)$ and the product is $O(R^{-11})$. Beyond $2R$ the triangle inequality bounds the product by $C\mathfrak d^{-11}$, whose integral is $O(R^{-4})$. The same split for $g_1*\mathcal G$ gives $O(R^{-5})$: the input near zero uses $\|g_1\|_1$, the input near the output costs $CR^{-15/2}R^2$, and the remaining annuli are smaller. Local kernel integrability gives boundedness for bounded outputs. This proves the decay and $w_{\rm f}\in L^2$, since $\int_1^\infty R^6R^{-8}dR<\infty$.

Using (16.4), the commutation of left and right invariant fields and $\mathcal E\mathcal G=\delta_0$ gives

$$
\mathcal Ew_{\rm f}=-2YF+g_1,\qquad
\langle\mathcal Ew_{\rm f},u\rangle
 =2\int r(Yp)(Yu)+\gamma\int V_1pu=\mathcal L(u).
\tag{16.8}
$$

For noncompact inputs these are distributional identities obtained by input cutoffs and the preceding bounds. To verify the minimal closed form domain, take a smooth compact group approximate identity $\omega_\epsilon$ and set $w_\epsilon=\omega_\epsilon*w_{\rm f}$, $F_\epsilon=\omega_\epsilon*F$, $g_\epsilon=\omega_\epsilon*g_1$. Output differentiation commutes with this left convolution, so $\mathcal Ew_\epsilon=-2YF_\epsilon+g_\epsilon$. All three $L^2$ norms are uniformly bounded. With smooth compact dilated cutoffs $\eta_R$, equal to one near zero and $|\nabla_H\eta_R|\le C/R$, test with $\eta_R^2w_\epsilon$. Integration by parts and Young's inequality give

$$
b[\eta_Rw_\epsilon]\le C\left(\|F\|_2^2+
 \|g_1\|_2\|w_{\rm f}\|_2+R^{-2}\|w_{\rm f}\|_2^2\right),
\tag{16.9}
$$

uniformly in $R,\epsilon$. Weak closedness, first as $R\to\infty$ and then $\epsilon\downarrow0$, puts $w_{\rm f}$ in $\mathcal Q_E$. The inputs $F,g_1$ are real odd and the kernels in (16.5) are real even under $\sigma$; change of variables in the group automorphism proves oddness. Odd core approximation and continuity extend (16.8) to (16.6).

Bounded $q_*$ and (2.10) give

$$
pF_*\in L^2,\qquad F_*Xp+pq_*\in L^2,\qquad F_*Yp\in L^2.
\tag{16.10}
$$

The vectors $p\eta(r/R)F_*(r)$ belong to $\mathcal Q_E$ by smooth approximation of the bounded height multiplier and its derivative. Their full form norms converge to the vector and derivatives in (16.10), by dominated convergence. The local representative injection identifies the limit with $U_h$.

On $\dot{\mathcal H}_-$ let $\mathsf K$ be defined by

$$
b(\mathsf Ku,u')=\gamma\int Vuu',\qquad 0\le\mathsf K\le q_KI,
\quad q_K=1-\theta<1.
\tag{16.11}
$$

The order and norm here use the $b$ inner product. Let $M_V$ be multiplication by $\sqrt V$, as in §2, and $\mathsf R_V=\int_0^\infty P_tM_Vdt$. The specified reconstruction of [Native full-state weak binding](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md), Theorem 87.2, gives

$$
\mathsf Ku=\gamma\mathsf R_V(M_Vu)\in D(\mathcal E),\qquad
\|\mathsf Ku\|_2\le C_{\rm rec}\sqrt{b[u]},\quad
C_{\rm rec}=\gamma\|\mathsf R_V\|\sqrt{C_*}.
\tag{16.12}
$$

Indeed $\|M_Vu\|_2^2\le C_*b[u]$; the reconstructed vector is odd and its weak equation identifies it with (16.11). The Riesz equation and (16.6) imply $(I-\mathsf K)\Psi=w_{\rm f}$. Thus $\Psi=w_{\rm f}+\mathsf K\Psi$ has a $\mathcal Q_E$ representative, and subtraction gives (16.7). This proves only these particular response memberships. It does not prove $\Psi\in D(\mathcal E)$, arbitrary response membership, a bounded all-$L^2$ threshold inverse, a positive $L^2$ gap or native-domain membership. $\square$

## 17. Two-sided series for the same complete residual

**Theorem 17.1 (positive energy series and finite strict-sign criteria).** Define only from the fields and projection already specified

$$
d_*=w_{\rm f}-(I-\mathsf K)U_h,\quad m_n=b(d_*,\mathsf K^nd_*),\quad
S_N=\sum_{n=0}^Nm_n,\quad B_h=3A-\gamma C_2-I_h.
\tag{17.1}
$$

Then $(I-\mathsf K)v=d_*$, and the full residual of the height projection satisfies

$$
\delta_h=h_0[v]=\sum_{n=0}^\infty m_n,\qquad
S_N+m_{N+1}\le\delta_h\le S_N+\frac{m_{N+1}}\theta,\qquad m_n\ge0.
\tag{17.2}
$$

Consequently $G_{\rm resp}=B_h-\delta_h$ lies between

$$
\mathfrak L_N=B_h-S_N-m_{N+1}/\theta,\qquad
\mathfrak U_N=B_h-S_N-m_{N+1},
\quad 0\le\mathfrak U_N-\mathfrak L_N\le q_K^{N+2}m_0/\theta.
\tag{17.3}
$$

The lower endpoints increase and the upper endpoints decrease. In particular $G_{\rm resp}>0$ if and only if some $\mathfrak L_N>0$, and $G_{\rm resp}<0$ if and only if some $\mathfrak U_N<0$. The same criterion applies to a fixed original coefficient after subtracting $\mathscr R\overline D$ from each endpoint, where $\mathscr R=\lambda/\nu^2$.

Proof. The spectral measure of the positive contraction $\mathsf K$ at $d_*$ is supported in $[0,q_K]$. Thus $m_n\ge0$, $m_{n+1}\le q_Km_n$, and the norm-convergent energy series $v=\sum_{n\ge0}\mathsf K^nd_*$ gives $h_0[v]=b(d_*,v)=\sum m_n$. The tail after $S_N$ contains $m_{N+1}$ and is at most its geometric bound $m_{N+1}/\theta$. These inequalities prove (17.2)–(17.3), monotonicity and convergence. Convergence proves both reverse implications in the strict-sign criteria. No endpoint crossing is asserted to have been evaluated.

For later explicit estimates the same series gives

$$
\begin{aligned}
\sqrt{b\left[v-\sum_{n=0}^N\mathsf K^nd_*\right]}
 &\le q_K^{N+1}\sqrt{m_0}/\theta,\\
\left\|v-\sum_{n=0}^N\mathsf K^nd_*\right\|_2
 &\le C_{\rm rec}q_K^N\sqrt{m_0}/\theta,\\
\|v\|_2&\le M_v:=\|d_*\|_2+C_{\rm rec}\sqrt{m_0}/\theta.
\end{aligned}
\tag{17.4}
$$

For the second inequality write the tail as $\mathsf K(\mathsf K^Nv)$ and use (16.12); for the last use $v=d_*+\mathsf Kv$. These are estimates on one response in the energy norm and its particular $L^2$ representative. $\square$

## 18. A sign-changing marginal of the original second coefficient kernel

**Proposition 18.1 (one common bridge, with no fixed-sign second correction).** For $t>0$, at terminal height zero, integrate the original $p_2$ of (3.2) over the last two phase coordinates. With $g_m(y)=(4\pi m)^{-1/2}e^{-y^2/(4m)}$,

$$
\int_{\mathbb R^2}p_2(t;0,y,z,w)dz\,dw
 =h_t(0)g_t(y)\left(\frac{y^4}{48t}-\frac t4\right).
\tag{18.1}
$$

It is negative for $y^4<12t^2$ and positive for $y^4>12t^2$. In particular positivity of the unperturbed Gaussian cannot imply a fixed sign of this second coefficient.

Proof. On the same bridge used in (3.1), put $A_t=\int_0^tH_vdv$ and $B_t=\int_0^tH_v^2dv$. The first diagonal entry of $M_0$ is $t$; the corresponding entries of the linear and quadratic coefficients of $M(\beta)=M_0-2\beta M_1+3\beta^2M_2+O(\beta^3)$ are $-2A_t$ and $3B_t$. The Gaussian covariance is $2M(\beta)$. Marginalizing a Gaussian, and its displayed matrix derivatives, gives

$$
h_t(0)\mathbb E_{0,0}^t[3B_t\partial_mg_m+2A_t^2\partial_m^2g_m]_{m=t}.
\tag{18.2}
$$

The exchanges retain that common bridge. To justify absolute marginalization, the whitened matrix bounds $\|M_0^{-1/2}M_jM_0^{-1/2}\|\le S_t^j$ bound the absolute differentiated Gaussian marginal by $CS_t^2g_t(y)(1+|y|^4/t^2)$. Conditional Gaussian moments in the other two coordinates give this bound directly. Its bridge expectation is finite. The zero-endpoint bridge has covariance $2(\min(v,v')-vv'/t)$, so direct integration yields

$$
\mathbb EB_t=t^2/3,\qquad \mathbb EA_t^2=t^3/6.
$$

Thus (18.2) equals $h_t(0)[t^2\partial_mg_m+(t^3/3)\partial_m^2g_m]_{m=t}$. Differentiating the one-dimensional density proves (18.1). This fixed-time unweighted marginal does not sign the weighted infinite-time integral $C_2=\int V_2p^2$, either complete canonical coefficient, or an actual native energy. $\square$

## 19. Exterior control for a compact exhaustion of the full response

**Definition 19.1 (compact response spaces and explicit error data).** Take a fixed smooth real $\sigma$-even $0\le\zeta\le1$, equal to one on $\overline{\mathbb B_2}$ and supported compactly in $\mathbb B_3$. Put $\zeta_R=\zeta\circ\delta_{1/R}$ and $c_\zeta=\|\nabla_H\zeta\|_\infty$, so $\|\nabla_H\zeta_R\|_\infty=c_\zeta/R$. Let

$$
\mathcal H_R^c=\overline{C_{c,-}^\infty(\mathbb B_{3R};\mathbb R)}^{\sqrt b},\qquad
h_0(v_R,u)=e(u)\ (u\in\mathcal H_R^c),\qquad \delta_R=h_0[v_R],
\tag{19.1}
$$

where $e(u)=\mathcal L(u)-h_0(U_h,u)=h_0(v,u)$. Coercivity (16.1) gives the unique $v_R$. All fields, the mode and the height projection remain the full-space ones; none is regenerated or normalized on the ball.

The complete forcing, obtained by the product rule in $U_h=pF_*$, is

$$
\mathbf g=(-F_*Xp-pq_*,\ (2r-F_*)Yp),\qquad
k=\gamma(V_1+VF_*)p,\qquad
e(u)=\int\mathbf g\cdot\nabla_Hu+\int ku.
\tag{19.2}
$$

Fix a valid Engel Sobolev constant $S_H$ such that $\|u\|_{14/5}\le S_H\sqrt{b[u]}$. Bahouri–Barilari–Gallagher–Léautaud, Theorem 5.1, p.29 of the cited version, gives precisely this case $s=1,Q=7$; its norm (4.25), p.21, equals $\|\mathcal E^{1/2}u\|_2$. For $R\ge1$ with $\omega_R<1$, define

$$
\begin{aligned}
\omega_R&=\gamma S_H^2\|V\mathbf1_{\mathfrak d>R}\|_{7/2},\\
a_R&=\frac{(\|\mathbf g\mathbf1_{\mathfrak d>R}\|_2+
 S_H\|k\mathbf1_{\mathfrak d>R}\|_{14/9})^2}{1-\omega_R},\\
H_R&=\|\mathcal G\mathbf1_{\mathfrak d>R/2}\|_2\|V\|_2
 +\|\mathcal G\mathbf1_{\mathfrak d\le R/2}\|_1
       \|V\mathbf1_{\mathfrak d>R/2}\|_\infty,\\
T_R^v&=\|\mathbf1_{\mathfrak d>R}(w_{\rm f}-U_h)\|_2
 +\gamma H_R(M_v+\|U_h\|_2),\\
\operatorname{Err}_R&=\left(\sqrt{a_R}+\frac{c_\zeta}{R}T_R^v\right)^2.
\end{aligned}
\tag{19.3}
$$

These expressions involve only the specified fields, $w_{\rm f},U_h,d_*$ and bounds for their known norms and constants. They contain neither the unknown full $v$ nor $\delta_h$ on the right. Numerical use requires valid enclosures of these inputs; no numerical values for $S_H,\theta,C_{\rm rec}$ or a sufficient cutoff radius are supplied here.

**Lemma 19.2 (the whole spatial exterior, including far phase at bounded height).** In the $b$ closure of the exterior smooth core supported in $\{\mathfrak d>R\}$,

$$
h_0[u]\ge(1-\omega_R)b[u],\qquad
|e(u)|\le\sqrt{a_R}\sqrt{h_0[u]}.
\tag{19.4}
$$

Moreover $\omega_R=O(R^{-3})$, $a_R=O(R^{-3})$, so (19.3) is defined for all sufficiently large $R$.

Proof. The full-space estimates give $|\mathbf g|\le C(1+\mathfrak d)^{-5}$ and $|k|\le C(1+\mathfrak d)^{-15/2}$. In particular $V_1p$ has power $-15/2$, while the retained $VF_*p$ has power $-9$. Hölder and the stated Sobolev inequality give

$$
\gamma\int V|u|^2\le\omega_Rb[u],\qquad
|e(u)|\le(\|\mathbf g\mathbf1_{\mathfrak d>R}\|_2+
 S_H\|k\mathbf1_{\mathfrak d>R}\|_{14/9})\sqrt{b[u]}.
$$

This proves (19.4) on the core. Sobolev convergence implies local $L^2$ convergence; it preserves the exterior support and all displayed pairings in the completion. The volume law gives

$$
\|\mathbf g\mathbf1_{\mathfrak d>R}\|_2=O(R^{-3/2}),\qquad
\|k\mathbf1_{\mathfrak d>R}\|_{14/9}=O(R^{-3}),\qquad
\|V\mathbf1_{\mathfrak d>R}\|_{7/2}=O(R^{-3}).
$$

These are spatial-exterior estimates, rather than height-exterior estimates. $\square$

## 20. Full compact-domain loss and its computable upper bound

**Lemma 20.1 (ordered reconstruction and a particular response tail).** For a specified $z\in L^2$, the actual heat reconstruction satisfies

$$
\gamma\mathsf R_V(M_Vz)=\gamma(Vz)*\mathcal G,\qquad
\|\mathbf1_{\mathfrak d>R}\gamma(Vz)*\mathcal G\|_2
 \le\gamma H_R\|z\|_2.
\tag{20.1}
$$

Consequently $\|\mathbf1_{\mathfrak d>R}v\|_2\le T_R^v=O(R^{-1/2})$ and $H_R=O(R^{-3/2})+O(R^{-3})$.

Proof. Put $f=Vz\in L^1\cap L^2$. The metric triangle inequality gives the exact ordered split

$$
\mathbf1_{\mathfrak d>R}(f*\mathcal G)=\mathbf1_{\mathfrak d>R}
 \left[f*(\mathcal G\mathbf1_{\mathfrak d>R/2})
 +(f\mathbf1_{\mathfrak d>R/2})*(\mathcal G\mathbf1_{\mathfrak d\le R/2})\right].
\tag{20.2}
$$

A near relative kernel and an output outside $\mathbb B_R$ force the input outside $\mathbb B_{R/2}$. Young's inequality with the factor order shown proves the norm bound. To identify the actual heat integral, split $\mathcal G$ at radius one into an $L^1$ near kernel and an $L^2$ far kernel. Young's inequality gives $(V|z|)*\mathcal G\in L^2$. This positive function dominates the finite heat integrals; Tonelli and $L^2$ dominated convergence identify their limit with the convolution and with the specified $\mathsf R_V(M_Vz)$.

Homogeneity in dimension seven gives $\|\mathcal G\mathbf1_{\mathfrak d>R/2}\|_2=O(R^{-3/2})$ and $\|\mathcal G\mathbf1_{\mathfrak d\le R/2}\|_1=O(R^2)$. The second term in $H_R$ is therefore $O(R^{-3})$. Apply (20.1) to the same equation

$$
v=(w_{\rm f}-U_h)+\mathsf K\Psi,\qquad \Psi=U_h+v,
$$

using (17.4). This gives the stated $T_R^v$ bound, without an unknown response norm on its right. Both $w_{\rm f}$ and $U_h$ are $O((1+\mathfrak d)^{-4})$, so their exterior $L^2$ norms are $O(R^{-1/2})$. $\square$

**Lemma 20.2 (ground-state closure and the transition coupling).** For every complex $u\in\mathcal Q_E$,

$$
h_0[u]=\int p^2\left|\nabla_H(u/p)\right|^2.
\tag{20.3}
$$

For $w=1-\zeta_R$, the particular vectors $wv,w^2v$ are legitimate odd form multipliers in the exterior closure of Lemma 19.2, and $\zeta_Rv\in\mathcal H_R^c$. They obey

$$
h_0[wv]=e(w^2v)+\int|\nabla_Hw|^2|v|^2,\qquad
\sqrt{h_0[wv]}\le\sqrt{a_R}+\frac{c_\zeta}{R}T_R^v.
\tag{20.4}
$$

Proof. On the compact smooth core, test $\mathcal Ep=\gamma Vp$ with $|u|^2/p$ and expand the two divergence-free horizontal product rules. This proves (20.3). For a general form vector take core approximants. The transformed gradients are Cauchy in $L^2(p^2d\xi)$ by the core identity and form convergence. Smooth strict positivity of $p$ on compact sets identifies their limit with the local distributional gradient of $u/p$; passing to the limit proves (20.3) on the full complex domain.

The bounded multipliers $w,w^2$ have bounded horizontal derivatives, so preserve $\mathcal Q_E$ by its core definition and $v\in L^2$. Multiplying core approximants by $w$ or $w^2$ gives exterior approximants, since both vanish on $\mathbb B_{2R}$. Multiplication by $\zeta_R$ gives compact approximants supported inside $\mathbb B_{3R}$. Oddness is preserved. The product rule in $h_0(v,w^2v)=e(w^2v)$ gives the first identity in (20.4); the transition integral is retained.

Set $x=\sqrt{h_0[wv]}$, $t=\|v\nabla_Hw\|_2$ and $a=\sqrt{a_R}$. By (20.3) and $0\le w\le1$,

$$
\sqrt{h_0[w^2v]}\le x+t,\qquad
x^2\le a(x+t)+t^2,\qquad (x-a-t)(x+t)\le0.
$$

Thus $x\le a+t$, including the case $x+t=0$. Lemma 20.1 bounds $t$ by $c_\zeta T_R^v/R$, proving (20.4). The horizontal identity has been proved on its actual form closure; no Euclidean elliptic ground-state theorem is assumed. $\square$

**Theorem 20.3 (compact exhaustion and matching full loss).** For all sufficiently large $R$, with $L=3R/c_r$,

$$
\boxed{\quad
\mathfrak G(L)\le\delta_h-\delta_R=h_0[v-v_R]
 \le\operatorname{Err}_R=O(R^{-3}),\qquad
\delta_R\uparrow\delta_h,\quad \delta_h-\delta_R=\Theta(R^{-3}).\quad}
\tag{20.5}
$$

Here $\mathfrak G$ is exactly the height-exterior gain of Exterior response gain, Theorem 7.1.

Proof. Equation (19.1) makes $v_R$ the $h_0$ orthogonal projection of $v$. Pythagoras proves the loss equality. Its best-approximation property and $\zeta_Rv\in\mathcal H_R^c$ give

$$
\delta_h-\delta_R\le h_0[v-\zeta_Rv]=h_0[wv]\le\operatorname{Err}_R.
$$

Lemmas 19.2 and 20.1 give the asserted upper power. The spaces $\mathcal H_R^c$ are nested and their union contains every real odd compact core vector. Thus the projections converge in energy and $\delta_R\uparrow\delta_h$.

Every core test supported in $|r|>L$ has disjoint support from $\mathbb B_{3R}$, since $\mathfrak d\ge c_r|r|$. Locality and closure give $h_0(v_R,u)=0$, hence $e(u)=h_0(v-v_R,u)$. Cauchy–Schwarz bounds $e(u)^2/h_0[u]$ by the loss. Supremizing and using line optimization, together with the real/complex exterior equivalence in the cited theorem, gives $\mathfrak G(L)\le\delta_h-\delta_R$. That theorem supplies $\mathfrak G(L)=\Theta(L^{-3})$ and the matching lower power follows. This compares the full compact-domain loss with the existing exterior gain; it asserts neither $\delta_h=\delta_R+\mathfrak G(L)$ nor an optimal leading constant. $\square$

## 21. A finite-region horizontal flux certificate

**Theorem 21.1 (Dirichlet residual and full-response enclosure).** Let $R$ satisfy (19.3), $\Omega=\mathbb B_{3R}$, and let $z\in\mathcal H_R^c$ be real odd. Choose a real horizontal flux $\mathbf j\in L^2(\Omega;\mathbb R^2)$ whose distributional horizontal divergence $\operatorname{div}_H\mathbf j=Xj_X+Yj_Y$ belongs to $L^2(\Omega)$. Define

$$
\begin{aligned}
\mathbf a_z&=\mathbf g-\nabla_Hz,&f_z&=k+\gamma Vz,\\
\mathcal J(z)&=2e(z)-h_0[z],\\
\eta_R(z,\mathbf j)&=\theta^{-1/2}\left(
 \|\mathbf a_z+\mathbf j\|_{2,\Omega}
 +\frac{6R}{\pi c_r}\|f_z+\operatorname{div}_H\mathbf j\|_{2,\Omega}\right).
\end{aligned}
\tag{21.1}
$$

With $L=3R/c_r$, take the fixed real odd witness $u_L=L^{-4}\varphi\circ\delta_{1/L}$ of Exterior response gain, Theorem 7.1, and put $\ell_L=e(u_L)^2/h_0[u_L]$. For sufficiently large $L$ it has $\ell_L\sim k_\varphi L^{-3}>0$. Then

$$
\begin{gathered}
\mathcal J(z)\le\delta_R\le\mathcal J(z)+\eta_R(z,\mathbf j)^2,\\
B_h-\mathcal J(z)-\eta_R(z,\mathbf j)^2-\operatorname{Err}_R
 \le G_{\rm resp}\le B_h-\mathcal J(z)-\ell_L.
\end{gathered}
\tag{21.2}
$$

Proof. Zero extension of a compact core vector in $\Omega$ lies in the height slab $(-3R/c_r,3R/c_r)\times\mathbb R^3$. The one-dimensional Dirichlet Poincare inequality on that interval, integrated over phases, gives

$$
\|u\|_2\le\frac{6R}{\pi c_r}\|Xu\|_2
 \le\frac{6R}{\pi c_r}\sqrt{b[u]}.
\tag{21.3}
$$

It extends to $\mathcal H_R^c$ by closure and proves that this finite-region completion is a subspace of $\mathcal Q_E$. Distributional integration by parts and then (21.3) give, for its vectors,

$$
\begin{aligned}
e(u)-h_0(z,u)
 &=\int_\Omega(\mathbf a_z+\mathbf j)\cdot\nabla_Hu
   +\int_\Omega(f_z+\operatorname{div}_H\mathbf j)u,\\
|e(u)-h_0(z,u)|&\le\eta_R(z,\mathbf j)\sqrt{h_0[u]}.
\end{aligned}
\tag{21.4}
$$

Both plus signs are fixed by $\int\mathbf j\cdot\nabla_Hu=-\int(\operatorname{div}_H\mathbf j)u$. Testing with $v_R-z$ bounds its squared $h_0$ norm by $\eta_R^2$. The exact identity $\delta_R=\mathcal J(z)+h_0[v_R-z]$ proves the first line of (21.2). The exterior witness obeys $\ell_L\le\delta_h-\delta_R\le\operatorname{Err}_R$ by the proof of Theorem 20.3, so subtraction from $G_{\rm resp}=B_h-\delta_h$ proves its second line.

The divergence hypothesis is on the whole distribution in $\Omega$. A piecewise flux with a nonzero horizontal interface jump need not have $L^2$ divergence and cannot be used after discarding its jump. No boundary trace regularity for the control ball is needed in this proof: core testing and closure supply the integration by parts. The finite slab constant (21.3) gives no global $L^2$ gap. $\square$

## 22. Complete scalar tails and same-source clock and ratio intervals

**Proposition 22.1 (absolute integrands, constants and distinct tail powers).** Fix valid constants, for $\mathfrak d\ge1$,

$$
p\le C_p\mathfrak d^{-5},\quad |Yp|\le C_Y\mathfrak d^{-6},\quad
V\le C_V\mathfrak d^{-5},\quad |q_*|\le M_q,\quad
|V_j|\le\sqrt{K_jV},\quad V_{\rm t}\le\sqrt{K_{\rm t}V}.
\tag{22.1}
$$

For $r_0\ge1$, the five complete tail bounds are

$$
\begin{aligned}
\int_{\mathfrak d>r_0}r^2|Yp|^2
 &\le\epsilon_A(r_0)=\frac{7v_d}{3}c_r^{-2}C_Y^2r_0^{-3},\\
\int_{\mathfrak d>r_0}p^2q_*^2
 &\le\epsilon_I(r_0)=\frac{7v_d}{3}C_p^2M_q^2r_0^{-3},\\
\int_{\mathfrak d>r_0}|rV_1|p^2
 &\le\epsilon_B(r_0)=\frac{14v_d}{9}c_r^{-1}\sqrt{K_1C_V}C_p^2r_0^{-9/2},\\
\int_{\mathfrak d>r_0}|V_2|p^2
 &\le\epsilon_2(r_0)=\frac{14v_d}{11}\sqrt{K_2C_V}C_p^2r_0^{-11/2},\\
\int_{\mathfrak d>r_0}V_{\rm t}p^2
 &\le\epsilon_T(r_0)=\frac{14v_d}{11}\sqrt{K_{\rm t}C_V}C_p^2r_0^{-11/2}.
\end{aligned}
\tag{22.2}
$$

Proof. The homogeneous ball law implies, for $\alpha>7$,

$$
\int_{\mathfrak d>r_0}\mathfrak d^{-\alpha}d\xi
 =\frac{7v_d}{\alpha-7}r_0^{7-\alpha}.
\tag{22.3}
$$

The five integrands in (22.2) are bounded by the stated constants times powers $-10,-10,-23/2,-25/2,-25/2$, respectively, using $|r|\le\mathfrak d/c_r$. Substitution in (22.3) proves every constant and power. In particular the $|rV_1|p^2$ and $|V_2|p^2$ tails have different powers. $\square$

**Corollary 22.2 (canonical coefficients and the full clock).** Let $A_\Omega,I_\Omega,B_{1,\Omega},C_{2,\Omega},T_\Omega$ denote the five defining integrals restricted to $\Omega=\mathbb B_{3R}$, with their original signed integrands for $B_1,C_2$. In this corollary every $\epsilon$ means its value at $3R$. Then

$$
\begin{gathered}
A\in[A_\Omega,A_\Omega+\epsilon_A],\quad I_h\in[I_\Omega,I_\Omega+\epsilon_I],\\
B_1\in[B_{1,\Omega}-\epsilon_B,B_{1,\Omega}+\epsilon_B],\quad
C_2\in[C_{2,\Omega}-\epsilon_2,C_{2,\Omega}+\epsilon_2],\\
T\in[T_\Omega,T_\Omega+\epsilon_T].
\end{gathered}
\tag{22.4}
$$

Define

$$
\begin{aligned}
B_h^-&=3A_\Omega-\gamma(C_{2,\Omega}+\epsilon_2)-I_\Omega-\epsilon_I,\\
B_h^+&=3(A_\Omega+\epsilon_A)-\gamma(C_{2,\Omega}-\epsilon_2)-I_\Omega,\\
G_{108}^-&=1-A_\Omega-\epsilon_A
 -\gamma(C_{2,\Omega}+\epsilon_2+2B_{1,\Omega}+2\epsilon_B),\\
G_{108}^+&=1-A_\Omega
 -\gamma(C_{2,\Omega}-\epsilon_2+2B_{1,\Omega}-2\epsilon_B),\\
G_{\rm resp}^-&=B_h^- -\mathcal J(z)-\eta_R(z,\mathbf j)^2-\operatorname{Err}_R,\\
G_{\rm resp}^+&=B_h^+ -\mathcal J(z)-\ell_L,\\
D^-&=1+\gamma T_\Omega,&D^+&=1+\gamma(T_\Omega+\epsilon_T).
\end{aligned}
\tag{22.5}
$$

These enclose the same-source $B_h,G_{108},G_{\rm resp},\overline D$ in the correspondingly named intervals. For either $X=108$ or $X={\rm resp}$, write $[L_X,U_X]=[G_X^-,G_X^+]$. Then

$$
\boxed{\quad
\frac{C_X}{a\nu^2}\in
 [L_X-\mathscr R D^+,\ U_X-\mathscr R D^-],\qquad
\mathscr R=\lambda/\nu^2>0.\quad}
\tag{22.6}
$$

The threshold ratio $Q_X=G_X/\overline D$ lies between the minimum and maximum of the four numbers

$$
L_X/D^-,\quad L_X/D^+,\quad U_X/D^-,\quad U_X/D^+.
\tag{22.7}
$$

Proof. Nonnegativity gives the one-sided $A,I_h,T$ intervals and the absolute tails give the symmetric signed intervals. Substitute them into $B_h=3A-\gamma C_2-I_h$ and $G_{108}=1-A-\gamma(C_2+2B_1)$, and use Theorem 21.1 for $G_{\rm resp}$. Since $\mathscr R>0$, the larger clock is subtracted at the lower endpoint in (22.6). Both $D^-,D^+$ are positive, so the extrema of division on this rectangle occur at corners, proving (22.7) without a numerator sign assumption.

An evaluated upper endpoint below zero or lower endpoint above zero is a sufficient strict-sign certificate. The formulas alone evaluate neither absolute canonical sign nor the sign at an arbitrary fixed datum. No sign is inferred from separate extrema being simultaneously attainable; intervals are used only in their valid enclosure directions. The parameter-occurrence consequences of §§14–15 use the resulting threshold only with the actual admitted ratio image. $\square$

## 23. Primary correspondence and the remaining actual selection problem

**Definition 23.1 (attribution and applicability).** The response-space coercivity is Theorem 5.1 of this volume and the height projection and strict residual are the credited companion results in Definition 16.1; the strict nonaffine gap is [Strict nonaffine response gap](FIB_NATIVE_STRICT_NONAFFINE_CRITICAL_RESPONSE_GAP.md), Theorems 6.1–7.1. The specific $L^2$ multiplier reconstruction is Native full-state weak binding, Theorem 87.2, with multiplication by $\sqrt V$. The positive exterior witness and its sharp exterior power remain Exterior response gain, Theorem 7.1. Sections 16–22 add the particular response form representatives, two-sided same-residual series, exact same-bridge marginal, full compact-domain loss and error, horizontal flux certificate and complete scalar enclosures. These are conditional repository-derived deductions, not a literature-wide novelty claim.

The direct Engel suppliers are Bahouri–Barilari–Gallagher–Léautaud, *Spectral summability for the quartic oscillator with applications to the Engel group*, arXiv:2206.10396v1: the identical group law and fields are (3.6)–(3.8), pp.15–16; convolution and Young are (3.11)–(3.13), p.16; right fields are (3.24)–(3.25), p.17; derivative transfer is (5.12), p.34; the norm and Sobolev embedding used here are (4.25), p.21, and Theorem 5.1, p.29. Unit Lebesgue Haar measure, $Q=7$, $s=1$ and $\mathcal E=-\Delta_G$ give exactly the required correspondence.

The ground-state method has a Euclidean counterpart in Pinchover–Tintarev, *A ground state alternative for singular Schrödinger operators*, [arXiv:math/0411658v1](https://arxiv.org/pdf/math/0411658v1), Lemma 2.4 and (2.6), p.7. Its assumptions (1.1)–(1.4), p.2, include local uniform ellipticity of a Euclidean matrix and a locally $L^p$ potential with $p>d/2$. Those hypotheses do not identify the rank-two Engel form in four coordinates. Lemma 20.2 therefore proves its own horizontal identity and closure.

Pauly–Repin, *Functional a posteriori error estimates for elliptic problems in exterior domains*, [arXiv:1105.4101v1](https://arxiv.org/pdf/1105.4101v1), Theorem 3, p.5, supplies the classical residual-dual-norm method; §2.3, (2.17)–(2.19), p.8, and Proposition 9, p.9, explicitly retain interface flux jumps. Their setting is an exterior Euclidean Lipschitz domain with a symmetric bounded uniformly strongly elliptic matrix, weighted Sobolev spaces and the corresponding data assumptions, §§1–2. It is a method comparison here; (21.3)–(21.4) prove the horizontal certificate directly.

Chaumont-Frelet, *A posteriori error estimates for the finite element discretization of second-order PDEs set in unbounded domains*, [arXiv:2503.22297v1](https://arxiv.org/pdf/2503.22297v1), gives the reaction-diffusion setting in §3.1, p.6, and Theorem 3.1 with (3.1) in §3.3, p.7. The theorem uses a Euclidean Lipschitz polyhedral domain in dimension two or three, ordinary $H_0^1$, a reaction coefficient bounded above and away from zero, a finite mesh and an equilibrated $H(\operatorname{div})$ flux. It retains the artificial-boundary flux and exterior-source terms. It does not furnish reliability for this full-space critical horizontal problem; Theorems 20.3 and 21.1 provide the required truncation and flux estimates with their own assumptions. Riesz representation, spectral calculus, Gaussian marginalization, Poincare, Young, Hölder and closed-form approximation are mature intermediate tools in the proofs above.

**Definition 23.2 (published finite-separated-scale supplier and unresolved boundaries).** [Actual critical solvability and microscopic disappearance](FIB_NATIVE_ACTUAL_CRITICAL_SOLVABILITY_AND_MICROSCOPIC_DISAPPEARANCE.md), §§17–20, already supplies a unique positive $L^2$ Coulomb column $\zeta_{R_0}$ for each fixed separated parameter $R_0>r_C$, with the original source charge and Friedrichs Coulomb operator. If an actual ground-state sequence of one fixed admitted datum has $r_s\to R_0\in(r_C,\infty)$, its Theorem 20.1 supplies the moving $L^2$ comparison orbit

$$
\inf_\theta\|F_s-e^{i\theta}\alpha_{R_0}(p+\mathcal M_s\zeta_{R_0})\|_2\to0,\qquad
\alpha_{R_0}=(1+\|\zeta_{R_0}\|_2^2)^{-1/2}.
\tag{23.1}
$$

The map $\mathcal M_s$ is exactly its isometric comparison map (17.4), not an asserted native form map. Its Corollary 20.2 gives microscopic and macroscopic masses $\alpha_{R_0}^2$ and $\alpha_{R_0}^2\|\zeta_{R_0}\|_2^2$, a common complex phase, sum one and no third $L^2$ mass scale. These are credited shape and mass suppliers at an actually occurring finite separated $R_0$; they force $C_{\rm resp}=0$ but prove neither occurrence of that branch nor selection of $R_0$. Their constants need not be uniform through $R_0=r_C$ and they give no kinetic-energy transfer or native point interaction.

The absolute signs of $G_{\rm resp},G_{108}$, positive/zero response occurrence and the every-actual-choice response-zero selection remain unresolved. The symbolic error and interval formulas do not enclose numerical values until all their same-source inputs and constants are enclosed. The original entire complex native domains, both Dirichlet deaths, raw source charges, signed nonzero parameter, determinant-one shear and heat clock remain those of §§1–3. There is no general $L^2$ inverse or spectral gap, arbitrary response membership, assertion $\Psi\in D(\mathcal E)$, or passage from a canonical form representative to native admissibility without the original cutoff and transport argument.

The complete finite-$(s,A)$ quantum frontier, evaluated fixed-source coefficients through precontact/contact and degenerate gluing, all finite-budget contacts and optimizer/rank/actual-alphabet changes, endpoint uniform rates and joint critical limits retain their original universal-necessity and common-attainer obligations. The analytic differential-operator coefficients above supply no bridge to acquired mass, completely positive instrument resources, controller permissions, amplitude preparation or a joint native implementation. No physical-space or physical-$SO(3)$ selection, zero-leaf, torus, cutoff-free or parameter-uniform theorem is obtained. Finite analytic or numerical checks do not imply Lean, root or native certification, and this conditional finite theory does not complete the continuous quantum-first programme.

## 追加锚（本行以下为增补区）


## 24. Fixed critical tests and a fifth-order reference principal enclosure

**Definition 24.1 (fixed datum, measure and ordered coefficients).** Write J for [Actual critical solvability](FIB_NATIVE_ACTUAL_CRITICAL_SOLVABILITY_AND_MICROSCOPIC_DISAPPEARANCE.md), P for [Native full-state weak binding](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md), L for [Native phase diffusion](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md), and E for [Entire-height response escape](FIB_NATIVE_ENTIRE_HEIGHT_RESPONSE_ESCAPE.md). Fix one admitted original datum of Definitions 1.1–2.1 and J Definitions 1.1–3.2, 29.1 and 42.1, together with all their stated ordinary analytic antecedents, before taking $s\downarrow0$. Retain the jointly realized signed rational vector $c_\kappa$, raw measure $dk\,dq$, unit raw source, both original Dirichlet faces, all real phase frequencies and the entire complex form and operator domains (1.5). The coordinate Jacobian is $j_0s^7$; this does not divide the original measure by $j_0$. The factor $j_0^{-1}$ below belongs to the microscopic field source. The heat clock is $B$, with shift $S=B-\lambda$, independently of the kinetic constant $a$.

Throughout this section assume

$$
C_{\rm resp}=0,\qquad C_4=0.
\tag{24.1}
$$

No occurrence of these equalities is assumed to have been established. Use exactly the original unitary $\mathcal U_s$ and determinant-one shear $\mathcal T_s$ of Definition 2.1 and J §2. In their sheared coordinates, restriction to $\Omega_s=I_s\times\mathbb R^3$ followed by zero extension puts every kernel on the common complex $L^2(\mathbb R^4,d\xi)$. Suppress only these transport tildes, and put

$$
\begin{aligned}
\gamma&=\chi_c/a,& C_*&=\gamma^{-1},&T&=s^{-2},\\
Q_s(t)&=e^{-tC_s},& C_s&=s^2(\mathcal T_s\mathcal U_s)S(\mathcal T_s\mathcal U_s)^{-1},\\
F_s&=j_0^{-1}\int_1^Tq_s(t;0,\cdot)dt,&
H_s&=\int_0^TQ_s(t)dt,&N_s&=F_sH_s,&L_s&=H_sF_s.
\end{aligned}
\tag{24.2}
$$

A field in a product denotes multiplication. Thus $`N_s^*=L_s`$. The full field is $U_s=F_s+U_s^{>}$, where $U_s^{>}=s^5W_1\circ\Xi_s\circ\mathscr L_s$ is the original long field. It is not discarded from the final principal norm.

Let $p>0$, $\|p\|_2=1$, be the canonical critical mode; set $\mu=\int Vp^2>0$ and $g_0=Vp/\mu$. Use the complete coefficients, returns and normalized charges already defined in J §§23, 30–49:

$$
\begin{aligned}
V_k&=\mathcal V_k,\quad V_0=V,&
G_jf&=\int_0^\infty\mathsf Q_j(t)fdt,\\
N_mg_i&=\sum_{k+j=m}V_k(G_jg_i),&
G_s&=\sum_{i=0}^4s^ig_i,\\
L_su_s&=\ell_su_s,&u_s&\ge0,&\|u_s\|_2&=1.
\end{aligned}
\tag{24.3}
$$

Each return is used only on its owning inputs and norms. In particular $G_0g_0=p/(\gamma\mu)$. The $g_i$ are real signed charges; no positivity is imposed on a correction charge. Positivity belongs to $p$ and the auxiliary early vector $u_s$ of J Lemma 53.3. This vector is not a native ground state. Returns have no extra $j_0^{-1}$, and $V_k$ includes every clock coefficient in J (23.1) and (30.2).

**Lemma 24.2 (height weights on the full phase space).** Let $\mathfrak d(\xi)=d_E(0,\xi)$ and $\omega(r)=1+|r|$. There are fixed-data constants such that

$$
|p|\le C(1+\mathfrak d)^{-5},\qquad
|g_0|\le C(1+\mathfrak d)^{-10},\qquad
0\le F_s\le C\omega^{-5}.
\tag{24.4}
$$

Consequently

$$
\begin{gathered}
p\in L^{3/2}\cap L^2,\qquad
r^ng_0\in L^p\quad\text{if }(10-n)p>7,\qquad
r^ng_0\in L^\infty\quad(0\le n\le6),\\
w_s:=F_sp,\qquad
\|w_s\|_1+\|w_s\|_2+
\sum_{n=0}^3\bigl(\|r^nw_s\|_{3/2}+\|r^nw_s\|_2\bigr)\le C.
\end{gathered}
\tag{24.5}
$$

The following early-field bounds also hold:

$$
\begin{gathered}
\|F_s-V\|_2+\|F_s-V\|_\infty\le Cs,\qquad
\left\|F_s-\sum_{k=0}^3s^kV_k\right\|_\infty\le Cs^4,\\
\left\|F_s-\sum_{k=0}^ns^kV_k\right\|_4\le Cs^{n+1}
\quad(n=0,1,2).
\end{gathered}
\tag{24.6}
$$

Proof. E Theorem 3.1 and J (31.2) give the two full-distance bounds. Since $|r|\le C\mathfrak d$ and homogeneous volume has dimension seven, polar integration gives all stated canonical memberships, including the sixth bounded seed moment.

For the native field use $0\le F_s\le U_s$ and the height estimate J (2.9). Fix $0<\delta<c_0$. For $1\le|r|\le\delta/s$, take its radius to be $|r|$; the result is $C|r|^{-5}+Cs^5\le C_\delta\omega^{-5}$. For $|r|>\delta/s$ take the radius to be $\delta/s$, obtaining $C_\delta s^5$. On the original interval $|r|\le D/s$ for one fixed $D$, so this too is bounded by $C_{\delta,D}\omega^{-5}$. For $|r|<1$ use the uniform multiplier bound, and outside $I_s$ use zero extension. This proves the height bound in (24.4) uniformly over all three unrestricted phase coordinates.

For $n\le3$, $|r|^nF_s\le C$; hence $|r|^nw_s$ is bounded in $L^{3/2}$ and $L^2$ by the corresponding norm of $p$. Also $\|w_s\|_1\le\|F_s\|_2\|p\|_2$. J Lemma 32.1 bounds $\|F_s\|_2$ and gives (24.6): at exponent two use degree zero, and at exponent four use $5-7/4=13/4>n+1$ for $n\le2$. The supremum bounds follow from J Lemma 23.2, bounded complete coefficients, and $\|U_s^{>}\|_\infty=O(s^5)$. These arguments establish exactly (24.5) on $I_s\times\mathbb R^3$. No homogeneous-distance envelope for $F_s$, or cap on a phase coordinate, is inferred from the height interval. $\square$

**Lemma 24.3 (six finite derivatives on a fixed estimating strip).** Fix sufficiently small $\ell>0$, put $L=\ell/s$ and keep $L,T$ fixed during parameter differentiation. Require $(-L,L)\Subset I_s$ and $|\nu|\ell<1/4$. For $|\theta|\le s$ let $Q_\theta^L(t)$ be the Friedrichs heat on this symmetric strip, zero extended, with generator

$$
C_\theta^L=-X^2-(1+\nu\theta r)^{-2}Y^2-\lambda\theta^2.
\tag{24.7}
$$

For $0\le k\le6$, $0<t\le T$, and $1\le p_n\le q\le\infty$, one has

$$
\|\partial_\theta^kQ_\theta^L(t)f\|_q
\le C_k\sum_{n=0}^k
 t^{(k-n)/2-(7/2)(1/p_n-1/q)}\|r^nf\|_{p_n},
\qquad
\|\partial_\theta^kq_\theta^L(t;0,\cdot)\|_\infty
\le C_kt^{(k-7)/2}.
\tag{24.8}
$$

These are bounds on the indicated weighted inputs, not bounded parameter derivatives on arbitrary $L^2$.

Proof. Use the single height bridge from $A$ to $B$ and retain its killing indicator in $(-L,L)$; it is independent of $\theta$. Its covariance is

$$
M_\theta[H]=\int_0^t(1+\nu\theta H_v)^{-2}u(H_v)u(H_v)^{\mathsf T}dv,
\qquad u(h)=(1,h,h^2/2).
\tag{24.9}
$$

On this event $M_\theta$ is uniformly comparable to $M_0$, and its $j$th relative matrix derivative has norm at most $C_j\sup|H|^j$ for $j\le6$. Repeated differentiation of the phase Gaussian gives a finite sum of Gaussian polynomials in the whitened phase variable, of degree at most $2k$ at order $k$. A fixed inflated-covariance Gaussian absorbs each such polynomial with its order-dependent constant. This follows directly by differentiating the determinant and the quadratic exponential; it extends the finite matrix calculation in J (23.3) to order six.

Write $H=A+W$ and use the triangular matrix

$$
D_A=\begin{pmatrix}1&0&0\\A&1&0\\A^2/2&A&1\end{pmatrix},\qquad
u(A+W)=D_Au(W),\qquad\det D_A=1.
\tag{24.10}
$$

Here the left side of the middle identity is the vector $u$ evaluated at $A+W$. Conjugation by $D_A^{-1}$ puts the phase displacement in the input-first group coordinate $\eta^{-1}\xi$. Extracting $|A|^n$ leaves relative bridge degree $k-n$. The clock obeys

$$
|\partial_\theta^be^{\lambda\theta^2t}|\le C_bt^{b/2}
\quad\text{because }|\theta|\sqrt t\le1.
\tag{24.11}
$$

A clock derivative therefore contributes its own relative degree and is included in the same count. The full fixed-order bridge moments J (3.3)/P (107.5), followed by phase integration, give relative majorant kernels with norms

$$
\|K_{kn}(t)\|_b
\le C_kt^{(k-n)/2-(7/2)(1-1/b)},\qquad1\le b\le\infty.
\tag{24.12}
$$

Indeed the $L^1$ estimate is Brownian scaling of the relative supremum moment; the supremum estimate uses the inverse-determinant moment and has degree $k-n-7$; interpolation gives the remaining exponents. The safe indicator can be dropped in these positive majorants. Ordered Young, with $1+1/q=1/p_n+1/b$, proves the first bound in (24.8). Setting the input height to zero gives the column bound. The moments permit every fixed degree used here; no infinite-time differentiation is involved. Weighted approximation and dominated convergence on each finite time interval justify the derivatives and pairings, also for complex inputs. Only the strip family has been defined at nonzero $\theta$; no rational coefficient is continued through a pole. $\square$

**Lemma 24.4 (fixed residual and early-vector rate).** For this fixed datum,

$$
\|(L_s-C_*)p\|_2\le Cs,\qquad \|u_s-p\|_2\le Cs.
\tag{24.13}
$$

Proof. J (29.5) gives, uniformly for the original return and its extra-killed restriction,

$$
\|H_sf\|_2+\|H_s^Lf\|_2\le C(\|f\|_1+\|f\|_2).
\tag{24.14}
$$

Use contraction below time one and integrate $t^{-7/4}$ above it. On the strip, the first derivative applied to $g_0$ has bounds

$$
\begin{cases}
C(\|rg_0\|_2+\sqrt t\,\|g_0\|_2),&0<t\le1,\\
C(t^{-7/4}\|rg_0\|_1+t^{-5/4}\|g_0\|_1),&1\le t\le T.
\end{cases}
\tag{24.15}
$$

They are time integrable uniformly, so $\|(H_s^L-H_0^L)g_0\|_2\le Cs$.

To restore both original faces, split input by height $|A|\le L/4$. The deleted-path kernel on this inner input has supremum $Ct^{-7/2}e^{-cL^2/t}$ by J (31.6), for every output height and phase. Its column mass is at most a fixed constant for $t\le T$ (the shifted mass is at most $e^\lambda$). Thus its column $L^2$ norm is at most $Ct^{-7/4}e^{-c'L^2/t}$, with time integral $O(L^{-3/2})$. Integrate this against the inner input's $L^1$ norm. The outer seed has $L^2$ norm $O(L^{-13/2})$ by (24.4); native, canonical and restricted contractions on $(0,T)$ cost at most $CT L^{-13/2}=O(s^{9/2})$. The remaining canonical time tail costs $CT^{-3/4}=O(s^{3/2})$. These full-output estimates show

$$
\|H_sg_0-G_0g_0\|_2=O(s).
\tag{24.16}
$$

They include outputs outside the original interval by zero extension. Since $Vp=\mu g_0$ and $\mu G_0g_0=C_*p$,

$$
(L_s-C_*)p=H_s((F_s-V)p)+\mu(H_s-G_0)g_0.
\tag{24.17}
$$

The first input has $L^1+L^2$ norm $O(s)$ by (24.6), proving the first assertion.

J Lemma 53.3 supplies $L_s\to K_{\rm rec}$ in norm, with isolated algebraically simple eigenvalue $C_*$ and right vector $p$. On one fixed surrounding contour the resolvents of $L_s$ are uniformly bounded. The exact identity

$$
(z-L_s)^{-1}p-(z-C_*)^{-1}p
=(z-C_*)^{-1}(z-L_s)^{-1}(L_s-C_*)p
\tag{24.18}
$$

gives $P_sp-p=O_{L^2}(s)$ for its rank-one Riesz projection. Its range is spanned by $u_s$. The projection is real, and its scalar multiple of $u_s$ is positive for small $s$, since both converge to $p$. Normalizing $P_sp$ proves the second assertion. The spectral isolation here belongs to a compact reconstruction operator; no positive $L^2$ gap for the critical Hamiltonian is used. $\square$

**Lemma 24.5 (two fixed seed scalar remainders).** On the original zero-extended domain,

$$
\begin{aligned}
\left|\int p^2\left(F_s-\sum_{k=0}^4s^kV_k\right)d\xi\right|&\le Cs^5,\\
\left|\left\langle g_0,H_sg_0-\sum_{j=0}^4s^jG_jg_0\right\rangle\right|&\le Cs^5.
\end{aligned}
\tag{24.19}
$$

Proof. Keep the strip of Lemma 24.3 fixed during differentiation and set

$$
\phi_\theta(t)=j_0^{-1}\int p^2q_\theta^L(t;0,\xi)d\xi,
\qquad \psi_\theta(t)=\langle g_0,Q_\theta^L(t)g_0\rangle.
\tag{24.20}
$$

The measure-preserving reflection $\sigma(r,y,z,w)=(-r,y,-z,w)$ preserves this strip, reverses $X$, preserves $Y$, and conjugates $C_\theta^L$ to $C_{-\theta}^L$ as Friedrichs realizations. It fixes the source, $p$ and $g_0$. Hence both scalar functions are exactly even in $\theta$, and their fifth derivatives at zero vanish. No symmetry of the original two faces or of $u_s$ is asserted.

The source-column bound gives $|\partial_\theta^6\phi_\theta(t)|\le Ct^{-1/2}$ for $1\le t\le T$. For the return, use output $L^\infty$ in (24.8) and then multiply by $\|g_0\|_1$. For input degrees $n=0,\ldots,6$ choose

$$
(p_0,\ldots,p_6)=(1,1,1,7/6,7/5,7/4,2).
\tag{24.21}
$$

Every membership is a strict instance of $(10-n)p_n>7$. Their large-time exponents are

$$
-\tfrac12,\ -1,\ -\tfrac32,\ -\tfrac32,\ -\tfrac32,\ -\tfrac32,\ -\tfrac74.
\tag{24.22}
$$

Below time one use bounded $r^ng_0$, $n\le6$, and the $L^1$ kernel bounds, giving integrable nonnegative half powers of $t$. The integrated sixth derivative is therefore at most $C(1+\sqrt T+\log T)\le C\sqrt T$. Taylor through degree five, whose fifth scalar coefficient is zero, has remainder $Cs^6\sqrt T=Cs^5$. This is a finite-time scalar Taylor argument, not the assertion that an infinite fifth return coefficient exists.

Here are the separate restorations. For the field, J Lemma 23.2's proof bounds actual deleted paths by $CL^{-5}$, degree-$j$ coefficient deletion by $CL^{j-5}$, and its time tail by $CT^{(j-5)/2}$, $j\le4$. After multiplication by $s^j$ each is $O(s^5)$. Pair them with $p^2\in L^1$; this yields the first original-domain estimate in (24.19).

For the return split input height at $L/4$. Inner native path deletion costs $CL^{-5}$ in integrated supremum by J (31.6). Outer native and safe inputs have integrated supremum at most $CL^{-8}$ by J (31.7). For an inner coefficient with input degree $n$ and relative degree $m$, $n+m=j\le4$, the deleted contribution is bounded by

$$
CL^{m-5}M_n(L),\qquad
M_n(L)\le
\begin{cases}
C,&n<3,\\
C(1+\log L),&n=3,\\
CL^{n-3},&n>3.
\end{cases}
\tag{24.23}
$$

Thus $s^jL^{m-5}M_n(L)=O(s^5)$ or smaller. For outer coefficients the integrated supremum is $CL^{j-8}$; its factor $s^j$ makes it $O(s^8)$. One obtains this bound below $L^2$ from the weighted input supremum and above $L^2$ by choosing $7/(10-n)<p<7/(m+2)$, $p\ge1$, as in J (31.9). Such a choice exists for all $j\le4$. Coefficient tails above $T$ use $p=1$ for $n=0,1,2$ and $p=7/6,7/5$ for $n=3,4$; their costs after $s^j$ are respectively $O(s^{5+n})$ and $O(s^7)$. Pair these supremum estimates with $g_0\in L^1$.

All are individual restoration estimates, independent of the logarithmic fifth Taylor bound of J (31.4). Original surviving paths outside the safe strip still have uniformly comparable covariance by the original denominator margins. A safe path cannot end beyond an original face, so the same coefficient-deletion bounds cover zero-extended outputs. This proves the second estimate of (24.19), with both native deaths and all phase/input/time tails restored. $\square$

**Lemma 24.6 (all tested ordered charge projections).** For $i=0,1,2,3$ put $m_i=4-i$ and

$$
\begin{aligned}
R_{i,s}&=H_sg_i-\sum_{j=0}^{m_i}s^jG_jg_i,\\
E_{i,s}&=N_sg_i-\sum_{j=0}^{m_i}s^jN_jg_i,\\
\mathfrak F_{n,s}&=F_s-\sum_{k=0}^ns^kV_k.
\end{aligned}
\tag{24.24}
$$

Then

$$
|\langle p,E_{i,s}\rangle|\le Cs^{5-i}\qquad(0\le i\le3).
\tag{24.25}
$$

Proof. Preserve factor order throughout:

$$
E_{i,s}=F_sR_{i,s}
 +\sum_{j=0}^{m_i}s^j\mathfrak F_{m_i-j,s}(G_jg_i).
\tag{24.26}
$$

For the seed return, the required test is $F_sp$, not merely $g_0$. Its exact decomposition is

$$
\langle F_sp,R_{0,s}\rangle
=\mu\langle g_0,R_{0,s}\rangle
 +\langle(F_s-V)p,R_{0,s}\rangle.
\tag{24.27}
$$

The first term is $O(s^5)$ by Lemma 24.5. The second is at most

$$
\|(F_s-V)p\|_1\|R_{0,s}\|_\infty
\le Cs\,s^5(1+|\log s|)=o(s^5),
\tag{24.28}
$$

using (24.6) and J (31.4). Thus the complete seed return summand is paid.

The five seed field summands in (24.26) have the following separate estimates. The $j=0$ scalar is $(\gamma\mu)^{-1}\int p^2\mathfrak F_{4,s}$ and is $O(s^5)$ by (24.19). For $j=1$ use $p,G_1g_0\in L^2$ and $\|\mathfrak F_{3,s}\|_\infty=O(s^4)$. For $j=2,3$ use $p\in L^2$, $G_jg_0\in L^4$ and $\|\mathfrak F_{4-j,s}\|_4=O(s^{5-j})$. For $j=4$ use $G_4g_0\in L^\infty$, $p\in L^2$ and $\|\mathfrak F_{0,s}\|_2=O(s)$. The prefactor $s^j$ makes each of these four terms $O(s^5)$. The return norms are J §§31 and 43; in particular $G_1g_0\in L^2$ follows by the degree-one seed estimate in J (43.2). This proves (24.25) for $i=0$.

For the lower charges first improve the tested outer-input returns. Their owning weights are

$$
\omega^5g_1\in L^2,\qquad\omega^4g_2\in L^2,\qquad
\omega^3g_3\in L^2,
\qquad \|g_i^{\rm out}\|_2\le CL^{-(6-i)},
\tag{24.29}
$$

where $g_i^{\rm out}=\mathbf1_{|r|>L/4}g_i$. Selfadjointness and (24.14) applied to $w_s=F_sp$, whose $L^1+L^2$ norms are bounded, give

$$
|\langle w_s,H_sg_i^{\rm out}\rangle|
 +|\langle w_s,H_s^Lg_i^{\rm out}\rangle|
\le CL^{-(6-i)}.
\tag{24.30}
$$

This avoids a factor $T$ in the tested native/safe outer returns.

Each complete coefficient kernel $\mathsf q_j(t;\eta,\xi)$ is symmetric in its two endpoints. Reverse the height bridge from $A$ to $B$; its covariance integral is unchanged. Reverse the phase displacement; the centered Gaussian is unchanged. Differentiation at zero preserves this equality, including the clock. Therefore

$$
\left\langle w_s,\int_0^T\mathsf Q_j(t)g_i^{\rm out}dt\right\rangle
=\left\langle\int_0^T\mathsf Q_j(t)w_sdt,g_i^{\rm out}\right\rangle.
\tag{24.31}
$$

This transposes the complete kernel, without commuting any ordered convolution factors or assuming positivity of a coefficient. First prove it for compact inputs and then pass by the finite weighted $L^2$ bounds J (30.4); all integrated vectors are in $L^2$ at finite $T$.

For $j\le3$, write $n+m=j$. On $t<1$ apply the $L^2$ moment bounds of (24.5). On $t\ge1$ apply the $L^{3/2}$ moments with output $L^2$. The latter time power is $m/2-7/12$, so

$$
\begin{aligned}
\sum_{j=0}^{m_i}s^j\left\|\int_0^T\mathsf Q_j(t)w_sdt\right\|_2
&\le C\sum_{n+m\le m_i}s^{n+m}(1+T^{m/2+5/12})\\
&\le Cs^{-5/6}.
\end{aligned}
\tag{24.32}
$$

Combining with (24.29), all outer complete-coefficient returns, after the exterior charge factor $s^i$, cost

$$
s^iL^{-(6-i)}s^{-5/6}=O(s^{31/6})=o(s^5).
\tag{24.33}
$$

The corresponding native and safe returns cost $O(s^6)$ by (24.30).

For completeness account for the remaining pieces of $R_{i,s}$. Apply strip Taylor only to the inner input $\mathbf1_{|r|\le L/4}g_i$. On $t<1$, multiply return output $L^2$ by bounded $F_s$ and use the weighted $L^2$ input moments. On $t\ge1$, multiply return output $L^\infty$ by $F_s\in L^2$. At derivative order $5-i$, the full list of input exponents and time powers is

$$
\begin{array}{c|c|c|c}
i&5-i&(p_n)_{n=0}^{5-i}&
((5-i-n)/2-7/(2p_n))_{n=0}^{5-i}\\ \hline
1&4&(1,1,7/6,7/5,7/4)&(-3/2,-2,-2,-2,-2)\\
2&3&(1,7/6,7/5,7/4)&(-2,-2,-2,-2)\\
3&2&(6/5,18/13,18/11)&(-23/12,-73/36,-77/36)
\end{array}
\tag{24.34}
$$

These memberships are exactly J (38.1), (43.4), (44.3) and (45.3), and all long-time powers are strictly integrable. The safe Taylor product thus has $L^2$ norm $O(s^{5-i})$ and its pairing with $p$ has the same order.

For $i=1$, original inner path deletion costs $O(s^5)$ using $g_1\in L^1$. A retained degree-$j$ coefficient, $j\le3$, with input degree $n$ and relative degree $m=j-n$, has integrated deletion bound $CL^{m-5}M_n(L)$, where

$$
M_0(L)\le C,\qquad M_n(L)\le CL^{n-1}\|rg_1\|_1\quad(n\ge1).
\tag{24.35}
$$

After $s^j$ its cost is $O(s^5)$ for $n=0$ and $O(s^6)$ otherwise. The complete time tails $t>T$ use input exponents $(1,1,7/6,7/5)$ at $n=0,1,2,3$ and give the same respective orders. These are precisely the restoration pieces in J (39.7)–(39.9); their earlier outer-input norm loss is replaced here by (24.30)–(24.33).

For $i=2,3$, retain the exit event in the relative degree-$m$ majorant. Its input-$L^p$ to output-$L^\infty$ bound is $Ct^{m/2-7/(2p)}e^{-cL^2/t}$. Its deletion integral and coefficient time tail, including $s^{m+n}$, are each at most

$$
Cs^{m+n}L^{m+2-7/p}\|r^ng_i\|_p
=Cs^{7/p-2+n}\|r^ng_i\|_p.
\tag{24.36}
$$

The substitution $t=L^2v$ gives the deletion bound; direct integration gives the time tail, with strictly integrable exponents in every case. For $i=2$, $n=0,1,2$, take $p=1,7/6,7/5$, respectively: all three powers are five. For $i=3$, $n=0,1$, take $p=6/5,18/13$: the powers are $23/6,73/18$, respectively. Unexpanded native deletion uses $n=m=0$, with $g_2\in L^1$ or $g_3\in L^{6/5}$. These powers exceed the required orders three and two. Multiply by bounded $\|F_s\|_2$ and then pair with $p\in L^2$.

Original surviving covariances remain comparable outside the estimating strip by the fixed denominator margins. Safe paths cannot end outside either original face, so these bounds include all zero-extended outputs. Together with the outer-input estimates this proves

$$
|\langle F_sp,R_{i,s}\rangle|\le Cs^{5-i},\qquad i=1,2,3.
\tag{24.37}
$$

Finally the lower-charge field products in (24.26) are all as follows. Every line also uses $p\in L^2$; the displayed order includes its prefactor $s^j$.

$$
\begin{array}{c|c|c|c|c}
i&j&G_jg_i\text{ norm}&\mathfrak F_{4-i-j,s}\text{ norm and order}&
\text{scalar order after }s^j\\ \hline
1&0&L^2&L^\infty:O(s^4)&O(s^4)\\
1&1&L^4&L^4:O(s^3)&O(s^4)\\
1&2&L^4&L^4:O(s^2)&O(s^4)\\
1&3&L^4&L^4:O(s)&O(s^4)\\
2&0&L^4&L^4:O(s^3)&O(s^3)\\
2&1&L^4&L^4:O(s^2)&O(s^3)\\
2&2&L^4&L^4:O(s)&O(s^3)\\
3&0&L^4&L^4:O(s^2)&O(s^2)\\
3&1&L^4&L^4:O(s)&O(s^2)
\end{array}
\tag{24.38}
$$

For the exceptional first line, $G_0g_1\in L^2$ follows from J Lemma 43.1 using $g_1\in L^1$ and $\omega^4g_1\in L^2$. The other return norms are J Theorem 38.2 and Lemma 43.1 on the particular $g_2,g_3$ inputs. Equation (24.6) supplies all field remainders. Hölder now proves every listed scalar bound. Adding them to (24.37) closes (24.25) for each lower charge. None of these improved scalar orders is inferred from the earlier, weaker full-row norm remainder. $\square$

**Theorem 24.7 (complete reference principal enclosure).** There are finite fixed-data constants $C,A_0$ and $s_0>0$ such that

$$
\|(L_s-C_*)p\|_2+\|u_s-p\|_2\le Cs,\qquad
|\ell_s-C_*|\le Cs^5,\qquad
k_{\rm ref}(s^6)\le C_*+A_0s^5
\quad(0<s<s_0).
\tag{24.39}
$$

Here $k_{\rm ref}$ is the original full positive compact Birman–Schwinger norm of J Definition 53.1, with its infinite-time field and return.

Proof. The first assertion is Lemma 24.4. In addition to (24.24) define

$$
E_{4,s}=(N_s-N_0)g_4,\qquad E_s^{\rm row}=\sum_{i=0}^4s^iE_{i,s}.
\tag{24.40}
$$

The owning full-row results J Theorems 33.2, 39.1 and 46.1, and $N_s\to N_0$ in norm, give $\|E_s^{\rm row}\|_2=o(s^4)$. This little-o is used only for replacement of the moving test. The charge equations cancel every coefficient through degree four. J (48.1) gives $\rho=-C_4/(a\gamma^2\mu)=0$, so the exact finite-vector identity is

$$
(I-\gamma N_s)G_s=-\gamma E_s^{\rm row}.
\tag{24.41}
$$

Pairing with $u_s$, using $`N_s^*=L_s`$, gives the exact scalar

$$
\ell_s-C_*=
\frac{\langle E_s^{\rm row},u_s\rangle}{\langle G_s,u_s\rangle},
\qquad\langle G_s,u_s\rangle=1+O(s).
\tag{24.42}
$$

The denominator uses $\langle g_0,p\rangle=1$, the fixed $L^2$ charges and Lemma 24.4. The final charge needs only its owned $L^2$ norm:

$$
|\langle p,(N_s-N_0)g_4\rangle|
=|\langle(L_s-K_{\rm rec})p,g_4\rangle|
\le Cs\|g_4\|_2.
\tag{24.43}
$$

Its exterior factor is $s^4$. All other fixed-test terms are supplied by Lemma 24.6, hence $|\langle p,E_s^{\rm row}\rangle|\le Cs^5$. Moreover

$$
|\langle u_s-p,E_s^{\rm row}\rangle|
\le\|u_s-p\|_2\|E_s^{\rm row}\|_2=o(s^5).
\tag{24.44}
$$

All vectors in this scalar calculation are real; conjugating the order of these pairings has no effect. Equations (24.42)–(24.44) prove $|\ell_s-C_*|\le Cs^5$. No weight or threshold return $G_0g_4$ has been introduced.

J Theorem 55.1 applies at its stated probe $h=s^6$ and gives

$$
k_{\rm ref}(s^6)=\ell_s+\mathscr A W_{1,\rm ref}(o)s^5+o(s^5),
\qquad A_p=\int Vp,\qquad
\mathscr A=(C_*+j_0A_p^2)/\mu>0.
\tag{24.45}
$$

The fixed-cutoff value $W_{1,\rm ref}(o)$ is finite. Choosing $A_0=C+|\mathscr A W_{1,\rm ref}(o)|+1$ and reducing $s_0$ proves the last inequality. J's quotient-to-norm argument at $s^6$ includes the complete long field, return, damping and cross terms. Thus this is a principal upper enclosure, rather than a trial Rayleigh lower bound. $\square$

## 25. The finite-$M s^8$ endpoint and actual complex ground states

**Lemma 25.1 (endpoint principal upper comparison).** Fix separately one admitted member $d$ of the translated two-face family J Definition 51.1, retaining its original source and all analytic antecedents. Use its $F,H,J,U,R,\ell,u$ of J (53.1), where $J=s^5W_{1,d}\circ\Xi_s\circ\mathscr L_s$ denotes the long multiplier. There are $M_{0,d}\ge1$ and $C_d<\infty$ such that, for every separately fixed finite $M\ge M_{0,d}$,

$$
\limsup_{s\downarrow0}
\frac{k_d(Ms^8)-\ell_d-\mathscr A W_{1,d}(o)s^5}{s^5}
\le C_d(M^{-1/4}+M^{-1/2}).
\tag{25.1}
$$

This comparison itself does not require (24.1). J Theorem 55.1 states the probes $s^6,s^7$; its ingredients give the following endpoint argument with the displayed finite-$M$ errors retained.

Proof. Fix $d$, suppress it, and write $h=Ms^8$. Set

$$
\begin{aligned}
x&=Fu,&y&=Ju,&m&=\int Fu^2,&\delta_s&=\int Ju^2,&n&=m+\delta_s,\\
z&=U^{1/2}u/\sqrt n,&
H^h&=\int_0^Te^{-ht}Q(t)dt,&
L^h&=\int_T^\infty e^{-ht}Q(t)dt,\\
D&=H-H^h,&R(h)&=H^h+L^h,&\mathscr K(h)&=U^{1/2}R(h)U^{1/2}.
\end{aligned}
\tag{25.2}
$$

J Lemma 53.3 gives $x\to Vp$ in $L^1$, bounded $L^1+L^2$ norms for $x$, $m\to\mu$ and $\ell\to C_*$. Since $W_1$ is bounded and continuous at $o$, $u^2\to p^2$ in $L^1$ and the physical chart tends to $o$ at each fixed microscopic point,

$$
\delta_s/s^5\to W_1(o),\qquad n\to\mu>0,\qquad\|y\|_2\le Cs^5.
\tag{25.3}
$$

First establish the needed finite-$M$ spectral neighborhood. P Theorem 104.2, in these sheared coordinates, gives

$$
\|R(h)U-K_{\rm rec}\|
\le\eta_s+C M^{3/4}s^6+C(M^{-1/4}+M^{-1/2}),\qquad\eta_s\to0.
\tag{25.4}
$$

The nonzero canonical spectrum has isolated simple top $C_*$ by P §§87–88. Choose one norm-perturbation neighborhood of this compact operator, a contour around $C_*$, and $\delta>0$, so that throughout the neighborhood there is one simple eigenvalue near $C_*$ and every other spectral value has real part at most $C_*-3\delta$. Such a neighborhood follows from the resolvent identity on the contour and on the compact remaining spectral exclusion set. Choose $M_{0,d}$ so that the last two errors in (25.4) lie inside half this neighborhood. For each fixed $M\ge M_{0,d}$, the first two errors lie in the other half for small enough $s$, possibly depending on $M$.

For each $s,h>0$, $\mathscr K(h)$ is positive, compact and selfadjoint by the original fixed-cutoff relative compactness. Bounded product factorization identifies its nonzero eigenvalues, with multiplicities, with those of $R(h)U$. For example factor these as $(R U^{1/2})U^{1/2}$ and $U^{1/2}(R U^{1/2})$; both factors are bounded. Therefore its principal value $k$ is uniformly bounded and simple, while the rest of its spectrum is at most $k_2\le C_*-3\delta$. The constants may be fixed for all $M\ge M_{0,d}$ once $s$ is sufficiently small for that fixed $M$. This is compact spectral separation, not a Hamiltonian threshold gap. In particular (25.4) has not been called norm convergence at a fixed finite $M$.

The exact scaled late kernel J (55.3) is bounded globally by $Cs^5$. Since $h/s^2=Ms^6\to0$, its pointwise scaled limit at fixed endpoints is $j_0W_1(o)$. The global bound, $x\to Vp$ in $L^1$ and dominated convergence on the entire product space give

$$
\langle x,L^hx\rangle=j_0W_1(o)A_p^2s^5+o_{d,M}(s^5).
\tag{25.5}
$$

Moving either input costs its $L^1$ error times a bounded $L^1$ norm. No output phase cutoff is used.

The input-specific damping estimates J (55.4) remain

$$
0\le\langle x,Dx\rangle\le Ch,\qquad\|Dx\|_2\le Chs^{-1/2}.
\tag{25.6}
$$

For the first, integrate $ht\|Q(t/2)x\|_2^2$ using contraction below one and $Ct^{-7/4}\|x\|_1$ above it; the latter integral is $\int_1^\infty t^{-5/2}dt$. For the second integrate $ht\|Q(t)x\|_2$ up to $T$, giving $ChT^{1/4}$. P (104.14), with the original long multiplier, yields

$$
0\le\langle y,Ry\rangle\le Cs^9h^{-1/2}=C M^{-1/2}s^5.
\tag{25.7}
$$

Indeed $\|RJ\|\le Cs^4h^{-1/2}$ and $\|Ju\|_2\le Cs^5$. Since $0\le L^h\le R$ as operators, spectral Cauchy–Schwarz gives

$$
|\langle x,L^hy\rangle|\le C M^{-1/4}s^5,\qquad
|\langle y,Dx\rangle|\le Cs^5hs^{-1/2}=o_{d,M}(s^5).
\tag{25.8}
$$

Thus both long-field self and cross terms are retained. In particular the first error in (25.8) cannot be replaced by $o(s^5)$ at fixed $M$.

Using $Hx=\ell u$, expand the full unit quotient exactly:

$$
\mathcal Q_s:=\langle z,\mathscr K(h)z\rangle
=\frac{\ell m+2\ell\delta_s+
 \langle x,L^hx\rangle-\langle x,Dx\rangle
 -2\operatorname{Re}\langle y,Dx\rangle
 +2\operatorname{Re}\langle x,L^hy\rangle+\langle y,Ry\rangle}
 {m+\delta_s}.
\tag{25.9}
$$

Subtract $\ell$ before dividing; one early cross copy remains. Equations (25.3)–(25.8), with the negative damping kept or dropped only in the upper direction, show $\mathcal Q_s\to C_*$ and

$$
\limsup_{s\downarrow0}
\frac{\mathcal Q_s-\ell-\mathscr A W_1(o)s^5}{s^5}
\le C_d(M^{-1/4}+M^{-1/2}).
\tag{25.10}
$$

This is a quotient estimate so far. To obtain the principal upper bound use the full residual

$$
R(h)Uu=\ell u+e,\qquad e=-Dx+L^hx+Ry.
\tag{25.11}
$$

Its three weighted terms have bounds

$$
\begin{aligned}
\|U^{1/2}Dx\|_2^2&\le Ch^2s^{-1},\\
\|U^{1/2}L^hx\|_2^2&\le C(s^8+s^9h^{-1/2}),\\
\|U^{1/2}Ry\|_2^2&\le Cs^9h^{-1/2}.
\end{aligned}
\tag{25.12}
$$

For the second line use $\int F\le Cs^{-2}$ (shifted killed source mass up to $T$ is at most $e^\lambda T$), $\|L^hx\|_\infty\le Cs^5$, $\|L^hx\|_2\le Cs^2h^{-1/4}$, and $\|J\|_\infty\le Cs^5$. These respectively give its $F$ and $J$ pieces. The $L^2$ late-return estimate follows by integrating $Cs^2e^{-ht}t^{-3/4}\|x\|_1$ on $(T,\infty)$. The first line follows from (25.6) and bounded $U$. For the third,

$$
\|U^{1/2}Ry\|_2^2
\le\|R^{1/2}UR^{1/2}\|\langle y,Ry\rangle,
\tag{25.13}
$$

and the middle norm equals $k$, already uniformly bounded by the finite-$M$ spectral neighborhood. No $L^2$ norm of the multiplier $J$ is asserted.

Since $n\to\mu$, (25.11)–(25.12) give

$$
\|(\mathscr K(h)-\ell)z\|_2^2
\le C_d(h^2s^{-1}+s^8+s^9h^{-1/2})
=C_d(M^2s^{15}+s^8+M^{-1/2}s^5).
\tag{25.14}
$$

For a unit vector with quotient $\mathcal Q_s>k_2$, the spectral variance inequality reads

$$
0\le k-\mathcal Q_s
\le\frac{\|(\mathscr K(h)-\mathcal Q_s)z\|_2^2}{\mathcal Q_s-k_2}
\le C_d\|(\mathscr K(h)-\ell)z\|_2^2.
\tag{25.15}
$$

To verify it, integrate $(k-t)(t-k_2)\le0$ over the spectral measure, supported at $k$ and at values at most $k_2$. The resulting variance is at least $(k-\mathcal Q_s)(\mathcal Q_s-k_2)$. Subtracting the quotient minimizes the squared residual. Here $\mathcal Q_s\to C_*$ and $k_2\le C_*-3\delta$, so the denominator is bounded below. Divide (25.14) by $s^5$ and take the fixed-$M$ limsup: its surviving error is $C_dM^{-1/2}$. Combining with (25.10) proves (25.1) as an upper bound for the full principal norm. $\square$

**Theorem 25.2 (fixed translated data and every actual choice).** Suppose the fixed reference member of J Definition 51.1 satisfies (24.1). There is $b_0>0$ such that for every separately fixed $0<b<b_0$ there is a finite $M_b$, fixed before $s\downarrow0$, with

$$
k_b(M_bs^8)<C_*,\qquad
\epsilon_{c,b}(s)\ge-aM_bs^8,\qquad
0<r_b(s)\le aM_b
\tag{25.16}
$$

for all sufficiently small $s$ depending on $b,M_b$. For every prescribed sequence $s_n\downarrow0$ and every actual normalized complex ground-state choice $\psi_{b,s_n}\in D(S_b)$ on the unchanged path $\tau=s_n^2$, $g=\chi_cs_n^3$,

$$
\liminf_n\operatorname{dist}_{L^2}
 (\mathcal U_{b,s_n}\psi_{b,s_n},\mathbb T p)
\ge\left[2-2\left(1+\frac{\gamma_{K,b}}{\sqrt{aM_b}}\right)^{-1/2}\right]^{1/2}>0.
\tag{25.17}
$$

Here $K$ is any fixed compact set allowed by P §§102–103, and $\gamma_{K,b}>0$ is exactly P (103.1)'s constant.

Proof. J Proposition 52.3 makes $C_{\rm resp},C_4$, $p,\mu,C_*,j_0,\nu,\lambda$ and $\mathscr A$ common to this translated family. Only the native faces move; each member retains a fixed positive source-face distance. Write its convergent relative diagonal integral as $\Delta_b$. J Theorems 52.2 and 54.1, and J Theorem 55.1 at the reference probe $s^6$, give

$$
\begin{aligned}
\Delta_b&\sim-(C_E/j_0)b^{-5},\qquad C_E>0,\\
\ell_b+\mathscr A W_{1,b}(o)s^5
 &=k_{\rm ref}(s^6)+\mathscr A\Delta_bs^5+o_b(s^5).
\end{aligned}
\tag{25.18}
$$

Indeed $\ell_b-\ell_{\rm ref}=\mathscr A\delta_b^{<}s^5+o_b(s^5)$ and $\Delta_b=\delta_b^{<}+W_{1,b}(o)-W_{1,\rm ref}(o)$; substitution proves the second identity with all early and late contributions.

Theorem 24.7 supplies one finite $A_0$ for the reference. Lemma 25.1 and (25.18) therefore imply, for each fixed $b$ and then each fixed $M\ge M_{0,b}$,

$$
\limsup_{s\downarrow0}\frac{k_b(Ms^8)-C_*}{s^5}
\le A_0+\mathscr A\Delta_b+C_b(M^{-1/4}+M^{-1/2}).
\tag{25.19}
$$

Choose $b_0\le b_{\rm ref}$ so that $A_0+\mathscr A\Delta_b<-2$ for every $0<b<b_0$. For each such fixed $b$ choose a finite $M_b\ge M_{0,b}$ with $C_b(M_b^{-1/4}+M_b^{-1/2})<1$. The right side is strictly negative, proving the first inequality in (25.16).

J Theorem 56.1 applies at every $h>0$ on the entire original complex form domain: $k_b(h)\le C_*$ is equivalent to $\epsilon_{c,b}(s)\ge-ah$. Use $h=M_bs^8$. Negative attainment on the original path gives $\epsilon_{c,b}<0$, and the exact dictionary $\epsilon_{c,b}=s^2E_{b,s}=-r_b(s)s^8$ gives the remaining inequalities. P Theorem 103.1 with its finite bound $B=aM_b$ gives (25.17), using the original $\mathcal U_{b,s}$, not an auxiliary early vector or a trial state. Its sequential conclusion is for every prescribed sequence and every actual normalized complex choice; if it failed, the sequence of failing actual choices would contradict that same theorem. No reality, parity or auxiliary-eigenvector constraint is imposed on these actual states. $\square$

**Corollary 25.3 (order of limits and conditional scope).** The quantifier order is a fixed admitted reference datum, then a separately fixed $b>0$, then a finite $M_b$, and only then $s\downarrow0$. No $b(s)$, $b=0$ source, uniform $M_b$ or joint-uniform $(b,s)$ assertion follows. If no admitted reference realizes (24.1), the preceding implication supplies no actual counterexample to critical-orbit convergence.

## 26. Mathematical provenance and remaining boundaries

**Proposition 26.1 (tools and their precise interfaces).** The fixed-test enclosure uses the owning mode decay, complete field/return coefficients and tails of E Theorem 3.1, P §§104–107 and J §§23, 29–49. The additional fixed-test estimates are Lemmas 24.2–24.6; the final scalar keeps the existing normalization $\rho=-C_4/(a\gamma^2\mu)$. The finite-$M$ argument in Lemma 25.1 is the endpoint consequence of P (104.2), P (104.14), and the full kernel, damping and residual estimates J (55.2)–(55.8). It retains the two errors that do not disappear at a fixed finite $M$; J Theorem 55.1 is used as stated only at $s^6$. The actual profile implication is the existing P Theorem 103.1, with the original threshold equivalence J Theorem 56.1.

The convolution and volume interface is Fischer–Ruzhansky, *Sobolev spaces on graded groups*, [arXiv:1311.0192v1](https://arxiv.org/pdf/1311.0192v1), §2.1 (2.1)–(2.2) and Proposition 2.2 (2.4). The Engel law has weights $(1,1,2,3)$, homogeneous dimension seven and unit Lebesgue Haar measure. Its input-first ordered convolution satisfies the printed Young relation; in particular $L^{3/2}$ input to $L^2$ output gives the time exponent $-7/12$. This primary supplies the norm and volume step, not native parameter derivatives, boundary restoration or tails.

The local heat interface is Colin de Verdière–Hillairet–Trélat, *Small-time asymptotics of hypoelliptic heat kernels near the diagonal, nilpotentization and related results*, Annales Henri Lebesgue 4 (2021), [DOI 10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf), Theorem A, Corollary 1.1 and Theorem 3.2. The original fields $\varepsilon\partial_k$ and $c_\kappa(k)\cdot\partial_q$ are smooth and divergence free on the fixed pole-free interval, with the step-three determinant and raw smooth measure in Definition 1.1. Physical time is $s^2t$ and the coordinate Jacobian is $j_0s^7$; the retained potential shift is $-\lambda$. Those local theorems do not supply a global moving-input or expanding-time estimate. Here the finite derivatives are proved from the common bridge, and all global tails are paid by the explicit owning majorants. Reflection is used solely on the fixed symmetric estimating strip.

Compact Riesz projections, Taylor's formula, Hölder, dominated convergence, bounded product factorization and the displayed selfadjoint spectral variance inequality are classical intermediate tools. The heat, bridge-moment, Sobolev, compact reconstruction, particular-response, attainment and native-domain hypotheses remain ordinary conditional premises at their declared scopes. The argument asserts no positive $L^2$ threshold gap, arbitrary zero-energy inverse, extra weight on $g_4$ or extra membership for the second response.

**Proposition 26.2 (what remains undecided).** The argument does not establish nonemptiness of the admitted double-zero locus, the full original-family response or quartic signs, or the finer actual energy/profile selection at an arbitrary double-zero datum. Theorem 25.2 concerns the stated fixed translated family only when its common coefficients satisfy (24.1). It does not identify every actual ground state with an auxiliary positive early vector. All complex native states, original signed rational data, raw unit source, both deaths, all phases, exact transports and the original critical path remain in scope. Physical-space dimension, physical $SO(3)$ selection and operational analytic-state preparation require separate correspondences and are not consequences of this conditional spectral enclosure.

## 追加锚（本行以下为增补区）

## 27. Fixed translated data and the actual-state mass dictionary

**Definition 27.1 (conditional family and fixed parameters).** Use J, P, L and E as in Definition 24.1. Fix exactly an admitted reference realization of J Definition 51.1, retaining the ordinary analytic antecedents of Definition 24.1 and J Definitions 1.1–3.2, 29.1, 42.1 and 51.1. In particular, fix $H\in(0,1/2)$, $a,\varepsilon>0$, $R_*>0$ and the prescribed nonzero sign of the sufficiently small fixed $\kappa$. Write

$$
\begin{aligned}
\alpha_\kappa&=\kappa+\kappa^2/H,&
x_*&=\sqrt{R_*}/\pi,&L_0&=H/[4(x_*+1)],\\
k_0&=\alpha_\kappa+x_*L_0,&
l_b&=k_0-\varepsilon b,&u_b&=k_0+L_0-\varepsilon b,\\
I_b&=(l_b,u_b),&
\lambda&=\varepsilon^2\pi^2/L_0^2,&
\nu&=\varepsilon/(k_0-\alpha_\kappa).
\end{aligned}
\tag{27.1}
$$

All probability, pole and determinant margins are those of J Proposition 51.2. The one jointly realized signed rational vector is

$$
c_\kappa(k)=\left(
\frac{(k-2\kappa)(H+\kappa-k)}{2H(k-\alpha_\kappa)},
-\frac{k(k-2\kappa)}{2H(k-\alpha_\kappa)},
\frac{H+\kappa-k}{H(k-\alpha_\kappa)}\right).
\tag{27.2}
$$

Its components and jets are not separately variable. The original five probabilities are $(k-2\kappa,H+\kappa-k,1-2H,H+\kappa-k,k)$, the real lift remains $x_{\rm lift}=D/\kappa$, and the source is the unit point source at $o=(k_0,0)$ in raw $dk\,dq$, $q\in\mathbb R^3$. Only the two Dirichlet faces vary with $b$.

Assume the reference satisfies $C_{\rm resp}=C_4=0$ as in (24.1). J Proposition 52.3 makes these coefficients and the canonical $p,V,C_*,\chi_c,j_0$ common to this family. Choose $b_0$ and, for each separately fixed $0<b<b_0$, a positive finite scalar $M_b$ exactly as in the proof of Theorem 25.2. Thus

$$
\Lambda_b:=A_0+\mathscr A\Delta_b
       +C_b(M_b^{-1/4}+M_b^{-1/2})<-1,
\qquad d_b=-\Lambda_b/2>0.
\tag{27.3}
$$

Here $A_0,\mathscr A,\Delta_b,C_b$ are the quantities in (25.19), with its stated range $M_b\ge M_{0,b}$. The order is the fixed reference, then fixed $b>0$, then fixed finite $M_b$, and only then $s\downarrow0$. No realization of the double-zero antecedent is asserted. The scalar $M_b$ in (27.3) is a spectral probe; the Coulomb tensor will be denoted $\mathsf M_b$.

**Definition 27.2 (entire complex domains and the unchanged clock).** In $\mathcal H_b=L^2(I_b\times\mathbb R^3,dk\,dq;\mathbb C)$ let

$$
\begin{aligned}
B_b&=-\varepsilon^2\partial_k^2
                -(c_\kappa(k)\cdot\partial_q)^2,&S_b&=B_b-\lambda\ge0,\\
B_\eta&=-\varepsilon^2\partial_k^2+|\eta\cdot c_\kappa(k)|^2,
                &&\eta\in\mathbb R^3.
\end{aligned}
\tag{27.4}
$$

Use the unitary phase Fourier transform with factor $(2\pi)^{-3/2}$. With underlying $\mathcal H_b$ membership required, the domains are exactly

$$
\begin{aligned}
\mathcal Q_b=\bigg\{\psi:\ &\widehat\psi(\cdot,\eta)\in H_0^1(I_b)
                 \text{ for a.e. }\eta,\\
 &\int_{\mathbb R^3}\!\int_{I_b}
 (\varepsilon^2|\partial_k\widehat\psi|^2
       +|\eta\cdot c_\kappa|^2|\widehat\psi|^2)dk\,d\eta<\infty\bigg\},\\
D(S_b)=D(B_b)=\bigg\{\psi:\ &\widehat\psi(\cdot,\eta)
          \in H^2(I_b)\cap H_0^1(I_b)\text{ for a.e. }\eta,\\
 &\int_{\mathbb R^3}\|B_\eta\widehat\psi(\cdot,\eta)\|_{L^2(I_b)}^2d\eta
                 <\infty\bigg\}.
\end{aligned}
\tag{27.5}
$$

Thus $\mathcal Q_b=D(S_b^{1/2})$. Both endpoint deaths and every real phase frequency are retained; no ordinary phase $H^1$, reality, parity or product-state condition is added.

Let $p_t^{B_b}$ be the killed kernel in raw measure and set

$$
W_{b,\tau}(Y)=\int_\tau^\infty e^{\lambda t}p_t^{B_b}(o,Y)dt,
\qquad
E_{b,s}=\inf_{\substack{\psi\in\mathcal Q_b\\\|\psi\|_2=1}}
\left\{a\|S_b^{1/2}\psi\|_2^2
       -g_s\int W_{b,s^2}|\psi|^2dk\,dq\right\},
\quad \tau=s^2,\quad g_s=\chi_cs^3.
\tag{27.6}
$$

The field uses the $B_b$ clock independently of $a$, includes its full infinite-time integral and has no survival renormalization. The inherited fixed-positive-cutoff statements P Propositions 70.2 and 75.2 give boundedness of $W_{b,s^2}$ at each fixed $s>0$, the operator $aS_b-g_sW_{b,s^2}$ on exactly $D(S_b)$ and a finite negative attained bottom. An actual choice always means any normalized complex ground state $\psi_{b,s}\in D(S_b)$ of this operator, not a trial or a near-minimizer.

**Definition 27.3 (two exact microscopic transports and the full norm).** Let $c_j=c_\kappa^{(j)}(k_0)$, $j=0,1,2$, and $j_0=\varepsilon^4|\det(c_0,c_1,c_2)|>0$. For $\xi=(r,y,z,w)$ put

$$
\begin{aligned}
\Xi_s\xi&=(k_0+\varepsilon sr,
          sc_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w),\\
\Omega_{s,b}&=(-b/s,L_0/(\varepsilon s)-b/s)\times\mathbb R^3,\\
(\mathcal U_{b,s}\psi)(\xi)&=(j_0s^7)^{1/2}\psi(\Xi_s\xi),\\
L_s&=\begin{pmatrix}1&\nu s&0\\0&1&2\nu s\\0&0&1\end{pmatrix},&
\mathscr L_s(r,\mathbf z)&=(r,L_s\mathbf z),&
\mathcal T_sF&=F\circ\mathscr L_s,\\
U_{b,s}&=s^5W_{b,s^2}\circ\Xi_s,&
\widetilde U_{b,s}&=U_{b,s}\circ\mathscr L_s,\\
C^{\rm sh}_{b,s}&=s^2(\mathcal T_s\mathcal U_{b,s})S_b
                              (\mathcal T_s\mathcal U_{b,s})^{-1}.
\end{aligned}
\tag{27.7}
$$

Here $\mathbf z=(y,z,w)$ is only the microscopic phase-coordinate vector. The chart has raw Jacobian $j_0s^7$. The shear has determinant one, fixes the source and both faces, and is unitary on $\mathcal H_{s,b}=L^2(\Omega_{s,b},d\xi;\mathbb C)$. Before zero extension,

$$
\begin{aligned}
D(C^{\rm sh}_{b,s})&=(\mathcal T_s\mathcal U_{b,s})D(S_b),\\
D((C^{\rm sh}_{b,s})^{1/2})&=(\mathcal T_s\mathcal U_{b,s})\mathcal Q_b,\\
\|(C^{\rm sh}_{b,s})^{1/2}f\|_2^2
 &=\int_{\Omega_{s,b}}
 \left(|Xf|^2+(1+\nu sr)^{-2}|Yf|^2\right)d\xi
       -\lambda s^2\|f\|_2^2,\\
X&=\partial_r,&Y&=\partial_y+r\partial_z+(r^2/2)\partial_w.
\end{aligned}
\tag{27.8}
$$

This is the original nonnegative selfadjoint threshold-shifted operator and its entire closed form. In particular, the $-\lambda s^2$ shift is retained. If $P_{b,s}(t;\eta,\xi)=j_0s^7p_{s^2t}^{B_b}(\Xi_s\eta,\Xi_s\xi)$, the full field is equivalently

$$
\widetilde U_{b,s}(\xi)
 =j_0^{-1}\int_1^\infty e^{\lambda s^2t}
                       P_{b,s}(t;0,\mathscr L_s\xi)dt.
\tag{27.9}
$$

The source factor $j_0^{-1}$ belongs to the transformed unit raw source, not to a replacement measure $dk\,dq/j_0$.

For any $h>0$ use exactly J Definition 53.1's full positive operator and norm,

$$
\mathscr K_b(h)=\widetilde U_{b,s}^{1/2}
        (C^{\rm sh}_{b,s}+h)^{-1}\widetilde U_{b,s}^{1/2},
\qquad k_b(h)=\|\mathscr K_b(h)\|_{2\to2}.
\tag{27.10}
$$

Its dependence on $s$ is suppressed as in §25; its field includes the original long part. Products and operator domains in (27.10) are taken on $\mathcal H_{s,b}$. Restriction and zero extension give the same norm on the common $L^2(\mathbb R^4)$, as in J §53.

## 28. A quantitative bound on the actual rescaled potential mass

**Theorem 28.1 (actual mass from the fixed principal deficit).** Fix the data in Definition 27.1 in their stated order. Write

$$
\begin{aligned}
H_s&=M_bs^8,&k_s&=k_b(H_s),&\delta_s&=C_*-k_s,&
\gamma&=\chi_c/a=1/C_*,\\
\epsilon_{c,b}(s)&=s^2E_{b,s},&
\eta_s&=-\epsilon_{c,b}(s)/a,&
r_b(s)&=-E_{b,s}/s^6,\\
F_s&=\mathcal U_{b,s}\psi_{b,s},&
f_s&=\mathcal T_sF_s,&
m_s&=\int_{\Omega_{s,b}}\widetilde U_{b,s}|f_s|^2d\xi.
\end{aligned}
\tag{28.1}
$$

Here $H_s$ is the scalar probe, not the time-integrated operator denoted by $H_s$ in (24.2), and $m_s$ denotes potential mass. There is $s_b>0$, depending only on the fixed datum and $b,M_b$, such that for $0<s<s_b$ and every actual normalized complex choice,

$$
\begin{gathered}
\delta_s\ge d_bs^5>0,\qquad 0<\eta_s\le H_s,\\
0\le m_s\le\frac{C_*k_s(H_s-\eta_s)}{\delta_s}
       \le\frac{C_*^2M_b}{d_b}s^3,\\
0\le\|(C^{\rm sh}_{b,s})^{1/2}f_s\|_2^2
       \le\frac{\gamma C_*^2M_b}{d_b}s^3,\\
m_s=s^5\int_{I_b\times\mathbb R^3}
                 W_{b,s^2}|\psi_{b,s}|^2dk\,dq.
\end{gathered}
\tag{28.2}
$$

These bounds are independent of the actual ground-state choice at each $s$.

Proof. Theorem 25.2 supplies the finite-$M_b$ inequality (25.19) and $\Lambda_b<-1$, with its full-field norm. Since $\Lambda_b=-2d_b$, the definition of limsup gives

$$
\frac{k_b(M_bs^8)-C_*}{s^5}\le-d_b
\tag{28.3}
$$

for all sufficiently small $s$. This proves the deficit in (28.2). The same theorem's (25.16), together with negative attainment, gives $0<\eta_s\le H_s$. This uses the finite-probe statement itself; no asymptotic at $s^6$ or $s^7$ is extended to $M_bs^8$.

We use the positive-shift form factorization of J (56.3) on the entire complex domain, displaying its application here. Fix such an $s$ and abbreviate $C=C^{\rm sh}_{b,s}$ and $U=\widetilde U_{b,s}$. The operator $C$ is nonnegative selfadjoint and $U$ is bounded and nonnegative at this fixed $s$. Since $H_s>0$, the bounded operator

$$
\mathcal B_s=U^{1/2}(C+H_s)^{-1/2}
\quad\hbox{satisfies}\quad
\mathcal B_s\mathcal B_s^*
     =U^{1/2}(C+H_s)^{-1}U^{1/2}=\mathscr K_b(H_s),
\qquad \|\mathcal B_s\|^2=k_s.
\tag{28.4}
$$

Functional calculus makes $(C+H_s)^{1/2}$ a map from $D(C^{1/2})$ onto $\mathcal H_{s,b}$, with inverse $(C+H_s)^{-1/2}$. Applying (28.4) to $(C+H_s)^{1/2}f$, for any complex $f\in D(C^{1/2})$, proves

$$
\int U|f|^2d\xi
 \le k_s\|(C+H_s)^{1/2}f\|_2^2
 =k_s\bigl(\|C^{1/2}f\|_2^2+H_s\|f\|_2^2\bigr).
\tag{28.5}
$$

This argument uses neither a zero-energy inverse nor a positive $L^2$ spectral gap, and makes no support, sign or symmetry restriction on $f$.

For the actual state, boundedness of the original multiplier and (27.5) give its operator equation on exactly $D(S_b)$. The unitaries (27.7), the coupling $g_s=\chi_cs^3$ and the factor $s^2$ transport it to

$$
(aC-\chi_cU)f_s=\epsilon_{c,b}(s)f_s=-a\eta_sf_s,
\qquad f_s\in D(C),\qquad\|f_s\|_2=1.
\tag{28.6}
$$

Taking its Hermitian inner product with $f_s$ gives the real equality

$$
\|C^{1/2}f_s\|_2^2=\gamma m_s-\eta_s.
\tag{28.7}
$$

Apply (28.5) and substitute (28.7). The result is

$$
m_s\le k_s(\gamma m_s+H_s-\eta_s),
\qquad
\frac{\delta_s}{C_*}m_s\le k_s(H_s-\eta_s).
\tag{28.8}
$$

Division is legitimate because $\delta_s\ge d_bs^5>0$. Also $0\le H_s-\eta_s\le H_s$ and $0\le k_s<C_*$. Thus (28.8) proves the mass bound in (28.2), and (28.7) bounds the nonnegative kinetic form by $\gamma m_s$.

Finally change variables first by the determinant-one shear and then by the raw chart of Jacobian $j_0s^7$. The unitary amplitude cancels that Jacobian, yielding

$$
\begin{aligned}
\int_{\Omega_{s,b}}\widetilde U_{b,s}|f_s|^2d\xi
 &=\int_{\Omega_{s,b}}s^5W_{b,s^2}(\Xi_s\xi)
                  |\mathcal U_{b,s}\psi_{b,s}(\xi)|^2d\xi\\
 &=s^5\int W_{b,s^2}|\psi_{b,s}|^2dk\,dq.
\end{aligned}
\tag{28.9}
$$

Every step used the actual equation and constants independent of its normalized eigenvector. This proves all assertions. $\square$

The kinetic quantity in (28.2) is the threshold-shifted form (27.8). The unshifted horizontal form equals this quantity plus $\lambda s^2$, since the state has norm one. Likewise (28.9) controls a rescaled expectation: it gives only an $O_{b}(s^{-2})$ upper bound for the raw expectation, and does not assert that the latter vanishes.

## 29. Local mass loss and global microscopic weak zero

**Theorem 29.1 (both microscopic states and the exact orbit distance).** Under Definition 27.1, zero extend $f_s$ and $F_s$ of (28.1) to $\mathbb R^4$. For every fixed compact $K\subset\mathbb R^4$, there are finite constants depending on the fixed datum, $b,M_b,K$ such that, uniformly over actual normalized complex choices,

$$
\|f_s\|_{L^2(K)}^2=O_{b,K}(s^3),\qquad
\|F_s\|_{L^2(K)}^2=O_{b,K}(s^3).
\tag{29.1}
$$

In particular both converge locally strongly to zero and globally weakly to zero in complex $L^2(\mathbb R^4)$, while $\|f_s\|_2=\|F_s\|_2=1$. For the canonical normalized mode $p$ and $\mathbb T p=\{e^{i\theta}p:\theta\in\mathbb R\}$,

$$
\operatorname{dist}_{L^2}(\mathcal U_{b,s}\psi_{b,s},\mathbb T p)
                    \longrightarrow\sqrt2.
\tag{29.2}
$$

All conclusions hold along every prescribed sequence $s_n\downarrow0$ and every actual normalized complex choice along it.

Proof. P Theorem 107.2, specifically (107.3)–(107.4), gives for this separately fixed admitted datum the full-field convergence

$$
\|\widetilde U_{b,s}-V\|_\infty\longrightarrow0,
\qquad V(\xi)=j_0^{-1}\int_1^\infty p_E(t;0,\xi)dt>0.
\tag{29.3}
$$

This is the original field with its long tail and clock. The positivity and positive-time kernel continuity are those retained in J (2.7)–(2.9a). They also give continuity of $V$: its finite-time integrals on $[1,T]$ are continuous, and their infinite-time tails tend uniformly to zero by J (2.9a). Thus, for a nonempty compact $K$,

$$
v_K:=\min_{\xi\in K}V(\xi)>0.
\tag{29.4}
$$

Since $b>0$ is fixed and $L_0/\varepsilon-b>0$, both faces of $\Omega_{s,b}$ recede. Hence $K\subset\Omega_{s,b}$ eventually; by (29.3), $\widetilde U_{b,s}\ge v_K/2$ on $K$ for small $s$. Theorem 28.1 gives

$$
\int_K|f_s|^2d\xi\le\frac{2m_s}{v_K}
       \le\frac{2C_*^2M_b}{v_Kd_b}s^3.
\tag{29.5}
$$

The empty compact set needs no estimate. For a fixed complex test $v\in L^2(\mathbb R^4)$ and a compact $K$, Cauchy–Schwarz and the global unit norm imply

$$
|\langle v,f_s\rangle|
 \le\|v1_K\|_2\|f_s1_K\|_2+\|v1_{K^c}\|_2.
\tag{29.6}
$$

Choose $K$ large enough to make the last term arbitrarily small, and then let $s\downarrow0$ in the first term using (29.5). This proves global weak zero for $f_s$ without any additional compactness hypothesis on actual states.

For the original unsheared state $F_s=\mathcal T_s^{-1}f_s$, the exact change of variables is

$$
\int_K|F_s|^2d\xi
 =\int_{\mathscr L_s^{-1}K}|f_s|^2d\xi.
\tag{29.7}
$$

The equality also holds for the zero extensions, since the shear preserves the height domain. The matrices $L_s^{-1}$ tend to the identity. For a fixed $K$ all sets $\mathscr L_s^{-1}K$ therefore lie in a single fixed compact $K'$ for small $s$. Apply (29.5) to $K'$ to prove the second local estimate in (29.1). Repeating (29.6) with $F_s$ and its unit norm proves its global weak zero. This uses an exact compact-set change of variables, not a norm estimate obtained by applying strong operator convergence to the varying vectors $f_s$.

Finally, the unit-vector identity

$$
\operatorname{dist}_{L^2}(F_s,\mathbb T p)^2
       =2-2|\langle p,F_s\rangle|
\tag{29.8}
$$

and weak zero give (29.2). The estimates and compact-test argument are uniform in actual choices at each sufficiently small $s$, so apply to every stated sequence and every choice on it. Global strong convergence to zero is impossible because the norms remain one. $\square$

## 30. The owning Coulomb endpoint for the same actual choices

**Theorem 30.1 (application of J Theorem 10.2 with its exact constants).** Keep exactly Definition 27.1 and the actual states of Theorem 28.1. In the fixed-cutoff-one normalization of J Definition 10.1 write

$$
\begin{aligned}
\phi_b(k)&=\sqrt{2/L_0}\sin\frac{\pi(k-l_b)}{L_0},\\
\mathsf M_b&=\int_{I_b}\phi_b(k)^2
                    c_\kappa(k)c_\kappa(k)^{\mathsf T}dk>0,&
d_{C,b}(\mathbf z)&=\sqrt{\mathbf z^{\mathsf T}\mathsf M_b^{-1}\mathbf z},\\
\beta_{C,b}&=\frac{\phi_b(k_0)\int_{I_b}\phi_b(k)^3dk}
                    {4\pi\sqrt{\det\mathsf M_b}},&
e_{C,b}&=-\frac{\beta_{C,b}^2}{4a},&
\rho_{C,b}&=\frac{\beta_{C,b}}{2a},\\
h_{C,b}(\mathbf z)&=(\det\mathsf M_b)^{-1/4}
           \left(\frac{\rho_{C,b}^3}{\pi}\right)^{1/2}
                 e^{-\rho_{C,b}d_{C,b}(\mathbf z)},\\
(\mathcal D_gv)(k,\mathbf z)&=g^{-3/2}v(k,\mathbf z/g).
\end{aligned}
\tag{30.1}
$$

The vector in the tensor is precisely (27.2), including all signed cross terms. The tensor $\mathsf M_b$ is distinct from the scalar probe $M_b$. The coordinate $\mathbf z\in\mathbb R^3$ in (30.1) is macroscopic, and $\mathcal D_g$ is unitary from raw native $L^2(dk\,dq)$ to $L^2(dk\,d\mathbf z)$. Both $\phi_b$ and $h_{C,b}$ have norm one.

For every prescribed sequence $s_n\downarrow0$ and every actual normalized complex ground-state choice on it, along that sequence,

$$
\begin{aligned}
\frac{E_{b,s}}{g_s^2}&\longrightarrow e_{C,b},&
r_b(s)&\longrightarrow-\chi_c^2e_{C,b}
                       =\frac{\chi_c^2\beta_{C,b}^2}{4a}>0,\\
\inf_{\theta\in\mathbb R}
\|\mathcal D_{g_s}\psi_{b,s}
            -e^{i\theta}\phi_bh_{C,b}\|_{L^2(dk\,d\mathbf z)}
 &\longrightarrow0,\\
E_{b,s}&=\chi_c^2e_{C,b}s^6+o(s^6),&
\epsilon_{c,b}(s)&=\chi_c^2e_{C,b}s^8+o(s^8).
\end{aligned}
\tag{30.2}
$$

The source-centred macroscopic phase orbit carries the entire unit mass; no moving centre or restriction on the actual complex phase is imposed.

Proof. Fix any such sequence and actual choices. The separately fixed member $I_b$ is admitted by J Definition 51.1 and Proposition 51.2. Definitions 27.1–27.3 retain the same rational vector, raw unit source, both deaths, full complex domains, negative attainment and all ordinary analytic antecedents of J §§1–3. The critical path is exactly J (1.7). Theorem 29.1 proves

$$
\mathcal U_{b,s_n}\psi_{b,s_n}\rightharpoonup0
                   \quad\hbox{globally in }L^2(\mathbb R^4),
\tag{30.3}
$$

for the original unsheared unitary. This is exactly the additional hypothesis J (10.2). Thus every hypothesis of J Theorem 10.2 is met for this fixed datum. Its conclusion (10.3) is the first three assertions of (30.2), with precisely its Definition 10.1 constants displayed in (30.1). This applies the owning endpoint; no new resolvent or fixed-cutoff endpoint theorem is asserted.

For completeness, the normalization appearing in that application is literal. The sine has integral square one, and $\mathbf z=\mathsf M_b^{1/2}y$ cancels the squared determinant prefactor in $|h_{C,b}|^2$. The remaining radial integral is

$$
\frac{\rho_{C,b}^3}{\pi}\,4\pi
                \int_0^\infty R^2e^{-2\rho_{C,b}R}dR=1.
\tag{30.4}
$$

Thus $\phi_bh_{C,b}$ has unit norm, which is the full mass claimed in (30.2). Positivity of $\phi_b(k_0)$ and $\int\phi_b^3$ gives $\beta_{C,b}>0$ and $e_{C,b}<0$. The identities $g_s^2=\chi_c^2s^6$ and $\epsilon_{c,b}(s)=s^2E_{b,s}$ give the two energy expansions.

The argument started with an arbitrary prescribed sequence and arbitrary actual choices, and the estimates proving (30.3) do not depend on those choices. If a phase-orbit conclusion failed uniformly over actual choices as $s\downarrow0$, one could select failing actual states along a sequence; they would satisfy (30.3) and contradict the same application of J Theorem 10.2. No uniqueness of actual minimizers, or choice of a real representative, is used. $\square$

## 31. Provenance and the remaining conditional boundary

**Definition 31.1 (mathematical attribution and analytic interface).** The new deduction is the principal-deficit-to-actual-mass estimate (28.8), its local and weak-zero consequences for exactly the translated double-zero family, and the resulting applicability of the existing actual endpoint. Theorem 25.2 and (25.19) own the fixed finite-probe supplier; J Definition 53.1 and (56.3) own the full norm/form interface. P Theorem 107.2 and J (2.7)–(2.9a) own the complete-field convergence, positivity and tails. J Definition 10.1 and Theorem 10.2 own the Coulomb constants and actual full-mass energy/profile endpoint. These results retain their original attribution. The inference here is repository-derived; no worldwide novelty claim is attached to the classical intermediate tools.

The complex closed-form interface is Gerald Teschl, *Mathematical Methods in Quantum Mechanics*, [§2.3, Theorem 2.13, Lemma 2.14 and (2.65), pp. 71–73](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf). The cited theorem concerns densely defined closed semibounded Hermitian forms and their selfadjoint realizations; the lemma gives the bounded symmetric form/operator norm correspondence. Here the underlying Hilbert space is $\mathcal H_{s,b}$, the form is the inherited nonnegative Friedrichs form (27.8), the shift $H_s$ is strictly positive, and $U$ is a bounded nonnegative multiplier at fixed $s$. Formulae (28.4)–(28.5) explicitly derive the needed norm inequality on that entire complex domain. The primary interface does not supply a native heat estimate, alter the source or clock, or assert a threshold inverse. All global heat, compactness, reconstruction, attainment and other ordinary analytic antecedents remain inherited at their original scopes.

**Definition 31.2 (scope of the consequence).** The implication in §§27–30 requires exactly the reference double-zero equalities and the fixed translated members selected by Theorem 25.2. Nonemptiness of this locus, its occurrence in admitted original data, the full-family response and quartic signs, and the actual energy/profile selection at an arbitrary double-zero datum remain unresolved. A conditional implication alone supplies no unconditional failure or resolution of the original actual-state selection problem.

The parameter order remains reference, $b>0$, finite $M_b$, then $s\downarrow0$. No $b(s)$, source on the $b=0$ face, simultaneous limit, uniform-in-$b$ rate or uniform scalar probe is obtained. Local mass in (29.1) means squared $L^2$ norm; global microscopic convergence is weak with norm one. The unscaled raw potential expectation need not vanish. The macroscopic conclusion is the original source-centred unit-mass phase orbit under $\mathcal D_{g_s}$, not a microscopic strong-zero limit. None of these conditional analytic results selects physical-space dimension, physical $SO(3)$, a native preparation procedure or an operational resource bound.

## 追加锚（本行以下为增补区）


## 32. Fixed original data and the absolute heat functional

**Definition 32.1 (analytic window, clocks and actual choices).** Use J, P, L and E as in Definition 24.1. Fix one original datum $d=(H,I,k_0,\kappa,\varepsilon,a)$ before any limit. Retain Definitions 1.1–2.1 and 24.1, J Definitions 1.1–3.2, 29.1 and 42.1, and their ordinary analytic antecedents. More explicitly, $I=(l,u)\Subset(0,H)$, $k_0\in I$, $a,\varepsilon>0$, and $\kappa\ne0$ lies in the sufficiently small fixed two-sided window of L Definition 35.1. Retain its larger-interval positive-probability, coefficient, pole and bracket-determinant margins, L Lemma 41.2, P §§76, 87–88, 97 and 104–107, and E Theorem 3.1. These heat hypotheses are additional applicability conditions; general geometric admission alone does not imply them. Throughout §§32–38 assume

$$
C_{\rm resp}(d)=0,\qquad C_4(d)=0.
\tag{32.1}
$$

The original five probabilities are $(k-2\kappa,H+\kappa-k,1-2H,H+\kappa-k,k)$. With $\alpha_\kappa=\kappa+\kappa^2/H$, the single jointly realized vector is

$$
c_\kappa(k)=\left(
\frac{(k-2\kappa)(H+\kappa-k)}{2H(k-\alpha_\kappa)},
-\frac{k(k-2\kappa)}{2H(k-\alpha_\kappa)},
\frac{H+\kappa-k}{H(k-\alpha_\kappa)}\right).
\tag{32.2}
$$

All three components, including their signed cross terms and rational denominator, are retained. The real lift remains $x_{\rm lift}=D/\kappa$. The source is the unit point source at $o=(k_0,0)$ in raw $dY=dk\,dq$, $q\in\mathbb R^3$, with no survival or Haar normalization. Put

$$
\begin{aligned}
B&=-\varepsilon^2\partial_k^2-(c_\kappa\cdot\partial_q)^2,&
\lambda&=\varepsilon^2\pi^2/(u-l)^2,&S&=B-\lambda\ge0,\\
K_d(t;Y,Z)&=e^{\lambda t}p_t^B(Y,Z),&
W_{\tau,d}(Y)&=\int_\tau^\infty K_d(t;o,Y)dt.
\end{aligned}
\tag{32.3}
$$

Both original height faces are Dirichlet, and every real phase frequency is admitted. The entire complex domains remain (1.5): the fibre form domain is $H_0^1(I)$ with the integrability of $\varepsilon^2|\partial_k\widehat\psi|^2+|\eta\cdot c_\kappa|^2|\widehat\psi|^2$, and the operator domain has fibres $H^2(I)\cap H_0^1(I)$ and $\int\|B_\eta\widehat\psi\|_2^2d\eta<\infty$. Underlying raw $L^2$ membership is required in both cases. No phase $H^1$, reality or parity constraint is added.

Use exactly $\Xi_s,\mathcal U_s,\mathscr L_s,\mathcal T_s$ of Definition 2.1 and J §2. Thus $|\det D\Xi_s|=j_0s^7$, $\det D\mathscr L_s=1$, $Y_s=\Xi_s\circ\mathscr L_s$, and $\mathcal T_sf=f\circ\mathscr L_s$. Suppress tildes only on the sheared operators and multipliers, so that

$$
\begin{aligned}
C_s&=s^2(\mathcal T_s\mathcal U_s)S(\mathcal T_s\mathcal U_s)^{-1},&Q_s(t)&=e^{-tC_s},\\
q_s(t;\eta,\xi)&=j_0s^7K_d(s^2t;Y_s\eta,Y_s\xi),&T&=s^{-2},\\
F_s&=j_0^{-1}\int_1^Tq_s(t;0,\cdot)dt,&J_s&=s^5W_{1,d}(Y_s\cdot),\\
U_s&=F_s+J_s,&H_s&=\int_0^TQ_s(t)dt,\\
N_s&=F_sH_s,&L_s&=H_sF_s.
\end{aligned}
\tag{32.4}
$$

Here $J_s$ is a multiplier, not the source volume J, and $L_s$ is the early operator, not the phase matrix inside $\mathscr L_s$. Restriction to $\Omega_s=I_s\times\mathbb R^3$ and zero extension give common-space operators. Their native domains before extension are exactly $(\mathcal T_s\mathcal U_s)\mathcal Q$ and $(\mathcal T_s\mathcal U_s)D(S)$. The factor $j_0^{-1}$ occurs in the field alone. The heat clock is $B$ independently of $a$; neither $Q_s$ nor $W_\tau$ contains a replacement kinetic clock.

On the original critical path put

$$
\tau=s^2,\quad g_s=\chi_cs^3,\quad E_s=E_{s^2}(\chi_cs^3),\quad
\epsilon_c(s)=s^2E_s<0,\quad r_s=-E_s/s^6,
\quad\gamma=\chi_c/a=C_*^{-1}.
\tag{32.5}
$$

An actual choice means any normalized complex ground state $\psi_s\in D(S)$ at this path. All actual-state conclusions below hold along every prescribed sequence $s_n\downarrow0$ and every such choice on it.

**Definition 32.2 (canonical coefficients and constants).** Retain the complete two-endpoint coefficients $\mathsf q_j,\mathsf Q_j$ of J (30.1), their field integrals $V_j$ of J (23.1), and their input-specific returns $G_j$ of Definition 24.1. They include every $\lambda$-clock term and the exact $\nu=\varepsilon/(k_0-\alpha_\kappa)$. Let $p>0$, $\|p\|_2=1$, be the canonical mode, $g_0=Vp/\mu$, $\mu=\int Vp^2$, and $g_1,\ldots,g_4$ the normalized charges of J §§36–45. Set

$$
A_p=\int Vp,\qquad a_0=\int g_0=A_p/\mu,\qquad
\mathscr A=\frac{C_*+j_0A_p^2}{\mu}>0,\qquad
\beta_*=\frac{C_*^2}{\mu}>0.
\tag{32.6}
$$

Write $d_j^{\rm h}=j_0^{-1}\mathsf q_{2j}(1;0,0)$ for $j=0,1,2$. In the notation $p_j$ of J (30.2), these are

$$
\begin{aligned}
d_0^{\rm h}&=j_0^{-1}p_0(1;0),\\
d_1^{\rm h}&=j_0^{-1}\{\nu^2p_2(1;0)+\lambda p_0(1;0)\},\\
d_2^{\rm h}&=j_0^{-1}\{\nu^4p_4(1;0)+\nu^2\lambda p_2(1;0)
                       +\tfrac12\lambda^2p_0(1;0)\}.
\end{aligned}
\tag{32.7}
$$

These are coefficients of the same original source, not separately variable jets. The notation $d_j^{\rm h}$ is distinct from the pole distance in (1.1). Define

$$
\begin{aligned}
\mathfrak m_d={}&W_{1,d}(o)-\frac{2d_0^{\rm h}}5
                         -\frac{2d_1^{\rm h}}3-2d_2^{\rm h}\\
&+\int_0^1\left[K_d(t;o,o)-d_0^{\rm h}t^{-7/2}
                         -d_1^{\rm h}t^{-5/2}
                         -d_2^{\rm h}t^{-3/2}\right]dt,\\
Z_d&=\mathfrak m_d-W_{1,d}(o).
\end{aligned}
\tag{32.8}
$$

Thus $\mathfrak m_d$ is specified by the raw original heat before any spectral limit is considered.

**Theorem 32.3 (existence and truncation of the original heat finite part).** The subtracted integrand in (32.8) is $O_d(t^{-1/2})$ as $t\downarrow0$, the original tail $W_{1,d}(o)$ is finite, and

$$
\mathfrak m_d=\lim_{\delta\downarrow0}
\left[\int_\delta^\infty K_d(t;o,o)dt
 -\frac{2d_0^{\rm h}}5\delta^{-5/2}
 -\frac{2d_1^{\rm h}}3\delta^{-3/2}
 -2d_2^{\rm h}\delta^{-1/2}\right].
\tag{32.9}
$$

Replacing $\infty$ by $R\ge1$ in the bracket has total error at most $C_d(\sqrt\delta+R^{-1/2})$ from $\mathfrak m_d$, for sufficiently small $\delta>0$.

Proof. Choose a fixed safe radius $\ell>0$ as in Lemma 24.3. At microscopic time one use its strip $(-\ell/s,\ell/s)$, held fixed during parameter differentiation. At the source diagonal the reflection $\sigma(r,y,z,w)=(-r,y,-z,w)$ conjugates the parameter $\theta$ to $-\theta$. Its odd scalar coefficients vanish. The sixth finite derivative in (24.8) bounds Taylor's remainder through degree five by $Cs^6$. The deleted-path bounds J (31.6), and their degree-$j$ versions, restore the original faces and the full canonical coefficients with polynomial times $e^{-c\ell^2/s^2}$ errors. Hence the exact raw scaling (32.4) gives

$$
j_0s^7K_d(s^2;o,o)
 =\mathsf q_0(1;0,0)+s^2\mathsf q_2(1;0,0)
                       +s^4\mathsf q_4(1;0,0)+O_d(s^6).
\tag{32.10}
$$

Divide by $j_0s^7$ and put $t=s^2$. This proves the asserted integrable remainder. Independently, L Lemma 41.2 bounds $K_d(t;o,o)$ by $C_dt^{-3/2}$ for $t\ge1$, proving tail convergence. Integrating the three explicit powers over $(\delta,1)$ proves (32.9), including the constants at the upper endpoint. Integrating $Ct^{-1/2}$ over $(0,\delta)$ and $Ct^{-3/2}$ over $(R,\infty)$ gives the error bound. The original faces need not be symmetric: reflection was used only on the estimating strip. $\square$

## 33. Absolute matching of the two seed scalars

**Theorem 33.1 (complete field and two-endpoint seed matching).** In the fixed frame of Definition 32.1, define

$$
\alpha_s=\int p^2\left(F_s-\sum_{j=0}^4s^jV_j\right),\qquad
\beta_s=\left\langle g_0,H_sg_0-\sum_{j=0}^4s^jG_jg_0\right\rangle.
\tag{33.1}
$$

Then

$$
\frac{\alpha_s}{s^5}\longrightarrow Z_d,\qquad
\frac{\beta_s}{s^5}\longrightarrow j_0a_0^2Z_d.
\tag{33.2}
$$

The returns and pairings include the whole endpoint product space, both original deaths, all phases and the entire coefficient-time tails. More precisely, fix an admissible $\ell$ first. There is a function $\rho_\ell(\delta)\downarrow0$ as $\delta\downarrow0$ such that, with

$$
\begin{aligned}
B_d(\delta)&=\int_\delta^1K_d(t;o,o)dt
 -\frac{2d_0^{\rm h}}5\delta^{-5/2}
 -\frac{2d_1^{\rm h}}3\delta^{-3/2}
 -2d_2^{\rm h}\delta^{-1/2},\\
\Psi_\ell(\delta)&=\sum_{j=0}^4\int_0^\delta
              t^{(j-7)/2}e^{-c\ell^2/t}dt,
\end{aligned}
\tag{33.3}
$$

one has

$$
\limsup_{s\downarrow0}\left|\alpha_s/s^5-B_d(\delta)\right|
+\limsup_{s\downarrow0}\left|\beta_s/s^5-j_0a_0^2B_d(\delta)\right|
\le C_d\sqrt\delta+C_d\Psi_\ell(\delta)=:\rho_\ell(\delta).
\tag{33.4}
$$

Here $\delta>0$ is fixed before $s$, and tends to zero only after the displayed limsups. No rate for convergence at fixed positive physical time is required.

Proof. Set $L=\ell/s$ and $D=\delta/s^2$. For small $s$, $1<D<T$. Split the field at microscopic time $D$, beginning at time one; split the return there, beginning at time zero. Each canonical coefficient is integrated to infinity, so its complementary tail begins at $D$ in both cases.

On the symmetric strip use exactly the two scalar tests (24.20). Their odd derivatives at zero vanish. Taylor through degree five is therefore Taylor through degree four. The column sixth derivative is bounded by $Ct^{-1/2}$ for $t\ge1$. For the return, the input exponents (24.21) give precisely the powers (24.22); below time one bounded weighted seed inputs give integrable nonnegative half powers. The integrated sixth derivative on $(0,D)$ is at most

$$
C\{1+\sqrt D+\log(2+D)\}.
\tag{33.5}
$$

Multiplication by $s^6$ and division by $s^5$ give a fixed-$\delta$ limsup at most $C\sqrt\delta$. This controls the short-physical-time scalar Taylor error. It does not differentiate an infinite-time return.

Restore the original kernels on this short interval. For the field, the source is at zero. A deleted native source kernel is bounded by $Ct^{-7/2}e^{-cL^2/t}$; a deleted degree-$j$ coefficient by $Ct^{(j-7)/2}e^{-cL^2/t}$, $j\le4$. Integrate against $p^2$, whose mass is one. After its factor $s^j$, the substitution $v=s^2t$ and division by $s^5$ leave the corresponding term of $C\Psi_\ell(\delta)$. The native term is $j=0$. These bounds hold for all outputs, including zero extension beyond either original face.

For the return, split input height at $L/4$. The outer seed has supremum $O(L^{-10})$ and $L^1$ mass $O(L^{-3})$. Native and safe returns cost $O(L^{-8})$ by J (31.7). A retained outer degree-$j$ coefficient has integrated supremum $O(L^{j-8})$ by J (31.9). After its factor $s^j$ this is $O(s^8)$. Pairing with the output $g_0\in L^1$ preserves these bounds, all negligible after division by $s^5$.

For the inner input, write $j=n+m$ as in J (30.3), where $n$ is the input-height degree and $m$ is the relative degree. Retaining the exit event bounds the deleted kernel by $Ct^{(m-7)/2}e^{-cL^2/t}$ times the input moment. For $n=0$, physical rescaling gives $C\Psi_\ell(\delta)$. For $n\ge1$, the full integrated bound (24.23), after normalization, is at most

$$
C_{\ell,j}s^nM_n(L),\qquad
M_1,M_2\le C,\quad M_3\le C(1+\log L),\quad M_4\le CL.
\tag{33.6}
$$

Every expression in (33.6) tends to zero. Original paths that survive outside the estimating strip still have uniformly comparable covariance, by the fixed denominator margins. Thus the same deletion bound applies to them; safe paths cannot end outside an original face. This accounts for all input, output and face restorations on the short interval. It retains a modulus at order $s^5$, rather than declaring all face contributions zero.

On physical times $v\in[\delta,1]$, exact scaling gives the complementary native pieces

$$
\begin{aligned}
s^5\int_\delta^1\!\int p(\xi)^2K_d(v;o,Y_s\xi)d\xi\,dv,\\
j_0s^5\int_\delta^1\!\iint g_0(\eta)g_0(\xi)
                 K_d(v;Y_s\eta,Y_s\xi)d\eta d\xi\,dv.
\end{aligned}
\tag{33.7}
$$

For each fixed endpoint $Y_s\xi\to o$. The both-endpoint bound P76 is uniform on $[\delta,1]$, and $p^2$ and $|g_0|\otimes|g_0|$ have finite mass. Positive-time kernel continuity and dominated convergence on the entire endpoint product space therefore give the limits $\int_\delta^1K_d(v;o,o)dv$ and $j_0a_0^2$ times that integral after division by $s^5$. No compact-output replacement is made.

It remains to identify the canonical tails, not just the native middle interval. Brownian scaling of J (30.1), with every clock factor of degree two included, gives

$$
\mathsf q_j(t;\eta,\xi)=t^{(j-7)/2}
 \mathsf q_j(1;\delta_{t^{-1/2}}\eta,\delta_{t^{-1/2}}\xi),
\qquad \delta_R(r,y,z,w)=(Rr,Ry,R^2z,R^3w).
\tag{33.8}
$$

For the field the source-column supremum is $Ct^{(j-7)/2}$. At $t=v/s^2$ this is integrable on $v\in[\delta,\infty)$ for $j\le4$, and dominated convergence against $p^2$ collapses the output to zero. Odd diagonal coefficients vanish. For $j=0,2,4$, the normalized field tail is therefore respectively

$$
\frac{2d_0^{\rm h}}5\delta^{-5/2},\qquad
\frac{2d_1^{\rm h}}3\delta^{-3/2},\qquad
2d_2^{\rm h}\delta^{-1/2}.
\tag{33.9}
$$

For the return, use the ordered decomposition J (30.3), not an unproved fourth $L^1$ height moment. The $n=0$ relative kernel is uniformly bounded after the scaling (33.8). Its limit at each fixed endpoint pair is the diagonal value. Dominated convergence against $|g_0|\otimes|g_0|$ gives $j_0a_0^2$ times each expression in (33.9). The other input degrees vanish. Indeed, using

$$
p_n=1,1,1,7/6,7/5\quad(n=0,\ldots,4)
\tag{33.10}
$$

in J (30.4), their integrated tails satisfy

$$
s^j\int_D^\infty
 t^{(j-n)/2-7/(2p_n)}\|r^ng_0\|_{p_n}dt
 \le C_{\delta,j,n}s^{7/p_n-2+n}.
\tag{33.11}
$$

For $n=1,2,3,4$ the powers are $6,7,7,7$, all strictly greater than five. For $n=0$ the power is five, and the just-proved dominated limit applies. All time powers in (33.11) are strictly integrable. The $n=0$ decomposition evaluated at input height zero is the full source coefficient, which identifies its limiting constant. No third or fourth absolute $L^1$ height moment of $g_0$ enters.

Subtracting these full coefficient tails from (33.7), and adding the short-interval error, proves (33.4). Theorem 32.3 gives $B_d(\delta)\to Z_d$ with error $O(\sqrt\delta)$. Taking $s\downarrow0$ first and then $\delta\downarrow0$ proves (33.2). All physical times beyond one remain in $W_{1,d}(o)$ in (32.8). $\square$


## 34. Lower-charge completion and the absolute early principal value

**Theorem 34.1 (tested lower-charge cancellation).** With $E_{i,s}$ and $E_s^{\rm row}$ of (24.24), (24.40),

$$
s^i\langle p,E_{i,s}\rangle=o_d(s^5),\qquad i=1,2,3,4.
\tag{34.1}
$$

Only the already specified $L^2$ norm of $g_4$ is required. Reflection is a property of the fixed canonical charges, not a restriction on any actual state.

Proof. For $i=1,2,3$ put $k_i=5-i$. On the estimating strip apply Taylor's integral formula through degree $k_i-1$ to the return on the inner-height truncation of $g_i$. The next derivative orders are $4,3,2$. For $t<1$ its weighted-input $L^2$ bounds are integrable. For $t\ge1$, (24.34) gives respectively the complete lists

$$
\begin{array}{c|c|c}
i&\text{input exponents}&\text{time exponents in }L^\infty\\ \hline
1&(1,1,7/6,7/5,7/4)&(-3/2,-2,-2,-2,-2)\\
2&(1,7/6,7/5,7/4)&(-2,-2,-2,-2)\\
3&(6/5,18/13,18/11)&(-23/12,-73/36,-77/36)
\end{array}
\tag{34.2}
$$

Every long-time exponent is strictly below $-1$. At each fixed positive time, the finite strip derivatives at $\theta=vs$, $0\le v\le1$, converge to the canonical derivatives. To justify this on the noncompact inputs, approximate $g_i$ simultaneously in the finitely many weighted $L^2$ and weighted $L^p$ norms displayed in (34.2). Compact inputs admit dominated differentiation of the common bridge; (24.8) bounds the approximation error independently of $s,L$ at each time and by the stated integrable powers. This proves dominated convergence of the time-integrated Taylor remainder.

The test $w_s=F_sp$ converges to $Vp$ both in $L^1$ and $L^2$: (24.6), Cauchy–Schwarz and bounded multiplication give errors $O(s)$. Pair the short-time output with its $L^2$ test, and the long-time output with its $L^1$ test. The normalized scalar return remainder consequently tends to

$$
\left\langle Vp,\int_0^\infty\mathsf Q_{k_i}(t)g_i\,dt\right\rangle.
\tag{34.3}
$$

The integral in (34.3) is used only in $L^2$ for $0<t<1$ plus $L^\infty$ for $t>1$. The Taylor normalization is exactly $\mathsf Q_{k_i}=\partial_\theta^{k_i}Q_\theta|_0/k_i!$. Thus this step asserts neither a bounded operator derivative nor an additional $L^2$ threshold return.

All restorations are smaller than $s^5$ after the exterior factor $s^i$. Equations (24.29)–(24.33) give $O(s^6)$ for outer native/safe inputs and $O(s^{31/6})$ for outer coefficient inputs, by transposing the complete symmetric endpoint kernel. The inner deleted-path and time-tail bounds (24.35)–(24.36) give $O(s^6)$ for $i=1$, $O(s^7)$ for $i=2$, and at worst $O(s^{41/6})$ for $i=3$ after that factor. These include outputs outside the original interval. They justify the same normalized scalar limit on the actual domain.

Canonical reflection gives $g_i\circ\sigma=(-1)^ig_i$ and $\mathsf Q_j$ parity $(-1)^j$. Since $i+k_i=5$, (34.3) is zero. For the field products retain their exact order (24.26). Add the first omitted coefficient to each field remainder in (24.38). The exceptional $(i,j)=(1,0)$ uses convergence to $V_4$ in $L^\infty$, paired with $G_0g_1\in L^2$ and $p\in L^2$. Every other entry uses convergence to $V_{5-i-j}$ in $L^4$ paired with its stated $L^4$ return. These convergences follow from J Lemma 23.2 and Lemma 32.1: after including degree three the $L^4$ error is $O(s^{13/4})=o(s^3)$, and at degrees two and one the errors are $O(s^3)=o(s^2)$ and $O(s^2)=o(s)$. The degree-four supremum error is $O(s^5(1+|\log s|))=o(s^4)$. Each limiting field scalar has total degree $i+j+(5-i-j)=5$ and is zero by reflection. This proves (34.1) for $i=1,2,3$.

For the last charge, the fourth right side in J (45.2) is even: every constituent has total degree four, and $g_0$ is even. Reflection commutes with its Fredholm operator and preserves $\langle p,g_4\rangle=0$. Normalized uniqueness therefore makes $g_4$ even, without adding a weight.

We need only the following strong derivative on the single fixed input $p$:

$$
\frac{(L_s-K_{\rm rec})p}{s}
 \longrightarrow D_1p:=G_0(V_1p)+\mu G_1g_0
                   \quad\text{in }L^2.
\tag{34.4}
$$

Indeed (24.17) splits the left numerator into $H_s((F_s-V)p)$ and $\mu(H_s-G_0)g_0$. The divided field input tends to $V_1p$ in both $L^1$ and $L^2$. For $L^1$ use the degree-one $L^2$ field expansion paired with $p$; for $L^2$ use the supremum expansion. The uniform bound (24.14) controls its moving-input error. On the fixed input $V_1p\in L^1\cap L^2$, finite-time heat convergence and the integrable $t^{-7/4}$ return bound give $H_s(V_1p)\to G_0(V_1p)$ in $L^2$.

For the seed-return derivative, (24.15) is an integrable $L^2$ majorant for the first strip derivative. Weighted compact approximation and fixed-time bridge convergence identify its limit with $G_1g_0$. The original/strip and canonical zero-order time restorations in the proof of Lemma 24.4 are $O(s^{3/2})+O(s^{9/2})=o(s)$. The degree-one coefficient restorations after its exterior factor are also $O(s^{3/2})$ or smaller, from the same column $L^2$ interpolation. Removing them proves $(H_s-G_0)g_0/s\to G_1g_0$ strongly and hence (34.4).

Both terms of $D_1p$ are odd $L^2$ vectors. By adjointness,

$$
\frac{\langle p,(N_s-N_0)g_4\rangle}{s}
 =\left\langle\frac{(L_s-K_{\rm rec})p}{s},g_4\right\rangle
 \longrightarrow\langle D_1p,g_4\rangle=0.
\tag{34.5}
$$

Multiplication by $s^4$ proves the remaining assertion. No $G_0g_4$ or height moment of $g_4$ is involved. $\square$

**Theorem 34.2 (absolute early fifth-order matching).** Let $\ell_s$ and $u_s$ be the original early principal value and nonnegative unit right vector. Then

$$
\begin{aligned}
\ell_s&=C_*+\mathscr A Z_ds^5+o_d(s^5),\\
\Theta_d(s)&:=\frac{\ell_s-C_*}{s^5}+\mathscr A W_{1,d}(o)
           \longrightarrow\mathscr A\mathfrak m_d.
\end{aligned}
\tag{34.6}
$$

Proof. In the seed ordered identity (24.26), the return scalar is $\mu\beta_s+o(s^5)$ by (24.27)–(24.28). Its degree-zero field term is $(C_*/\mu)\alpha_s$, since $G_0g_0=C_*p/\mu$. For its remaining field terms $j=1,2,3,4$, divide by their total factor $s^5$. The first omitted field coefficients are $V_4,V_3,V_2,V_1$, respectively, in $L^\infty,L^4,L^4,L^2$. Their little-o remainders follow from J Lemmas 23.2 and 32.1. The required returns lie respectively in $L^2,L^4,L^4,L^\infty$, by J §§31 and 43. Hölder therefore gives the limits $\langle p,V_{5-j}G_jg_0\rangle$. Each is an integrable odd scalar of total degree five, hence zero. Theorem 33.1 yields

$$
\frac{\langle p,E_{0,s}\rangle}{s^5}
 \longrightarrow\left(\frac{C_*}{\mu}+\mu j_0a_0^2\right)Z_d
 =\mathscr A Z_d.
\tag{34.7}
$$

Theorem 34.1 removes all other charge projections. The full row has norm $o(s^4)$ by its owning J §§33, 39 and 46 estimates. Lemma 24.4 gives $\|u_s-p\|_2=O(s)$, so changing the fixed test to $u_s$ costs $o(s^5)$. The exact scalar (24.42), with denominator $\langle G_s,u_s\rangle=1+O(s)$, proves (34.6). This uses the full finite charge identity rather than an eigenvalue ansatz. The early vector is only an auxiliary test. $\square$

## 35. Original-domain reconstruction at fixed positive spectral probes

**Theorem 35.1 (single-datum reconstruction and principal comparison).** Retain the original-data analytic hypotheses of Definition 32.1. The comparison in this theorem does not require the two equalities (32.1). Define, on the original transported complex space,

$$
R_s(h)=(C_s+h)^{-1},\qquad
\mathscr K_s(h)=U_s^{1/2}R_s(h)U_s^{1/2},\qquad
k_d(h)=\|\mathscr K_s(h)\|,\quad h>0.
\tag{35.1}
$$

The early operator $L_s$ has an eventually simple principal value $\ell_s\to C_*$ and a nonnegative unit vector $u_s\to p$ in $L^2$. There are $M_{0,d}\ge1$ and $C_d<\infty$ such that for every separately fixed finite $M\ge M_{0,d}$,

$$
0\le\liminf_{s\downarrow0}
 \frac{k_d(Ms^8)-\ell_s-\mathscr A W_{1,d}(o)s^5}{s^5}
\le\limsup_{s\downarrow0}
 \frac{k_d(Ms^8)-\ell_s-\mathscr A W_{1,d}(o)s^5}{s^5}
\le C_d(M^{-1/4}+M^{-1/2}).
\tag{35.2}
$$

For each $q=6,7$ one also has

$$
k_d(s^q)=\ell_s+\mathscr A W_{1,d}(o)s^5+o_d(s^5).
\tag{35.3}
$$

This theorem concerns an arbitrary separately fixed original datum within the stated analytic window; membership in J Definition 51.1's translated family is not a hypothesis.

Proof. All constructions below use the original-domain P104 and J29 suppliers. First justify the early vector at this scope. At each fixed $s$, $Q_s(t)F_s$ is Hilbert–Schmidt for $t>0$: its squared kernel norm is at most $C_{s,t}\|F_s\|_2^2$ by the both-endpoint column $L^2$ bound. Removing $(0,\delta)$ from $H_sF_s$ costs at most $\delta\|F_s\|_\infty$, and on $[\delta,T]$ operator-norm continuity of the selfadjoint heat gives compactness of the integral. The sandwich $F_s^{1/2}H_sF_s^{1/2}$ is likewise compact. Indeed its positive-time squared Hilbert–Schmidt norm is at most

$$
\sup_{\eta,\xi}q_s(t;\eta,\xi)\,
       \langle F_s,Q_s(t)F_s\rangle
 \le C_{s,t}\|F_s\|_2^2,
\tag{35.4}
$$

and the same small-time truncation applies. It is positive selfadjoint and positivity preserving; taking absolute values in its Rayleigh quotient supplies a nonnegative top eigenvector. Bounded product factorization transfers its nonzero eigenvalue to $H_sF_s$ with a nonnegative nonzero right vector.

P (104.9) gives $H_sF_s\to K_{\rm rec}$ in norm; compact conjugation by the strongly convergent shears preserves this convergence. P §§87–88 identify its isolated algebraically simple nonzero top $C_*$ and right vector $p$. Compact spectral perturbation makes the early top eventually simple and convergent. The equation $u_s=\ell_s^{-1}H_sF_su_s$ gives precompactness of its unit vectors. Every nonnegative unit cluster is $p$, so $u_s\to p$. P (104.6) and (24.6) then give

$$
\begin{aligned}
x:=F_su_s&\longrightarrow Vp\quad\text{in }L^1\cap L^2,\\
m:=\int F_su_s^2&\longrightarrow\mu,&
\|x\|_1+\|x\|_2&\le C.
\end{aligned}
\tag{35.5}
$$

For example the $L^1$ difference is bounded by $\|F_s\|_2\|u_s-p\|_2+\|F_s-V\|_2\|p\|_2$; the $L^2$ difference uses the bounded multiplier and $(F_s-V)p\to0$. This proves the early-vector statements without translated-family membership. The residual/Riesz argument (24.17)–(24.18) applies at this same scope if its $O(s)$ rate is needed.

Write $h>0$, $y=J_su_s$, $d_s=\int J_su_s^2$, $n=m+d_s$, and

$$
\begin{aligned}
z&=U_s^{1/2}u_s/\sqrt n,&
H^h&=\int_0^Te^{-ht}Q_s(t)dt,\\
L^h&=\int_T^\infty e^{-ht}Q_s(t)dt,&
D&=H_s-H^h,&R_s(h)&=H^h+L^h.
\end{aligned}
\tag{35.6}
$$

The multiplier $W_1$ is bounded and continuous at $o$, hence

$$
d_s/s^5\to W_1(o),\qquad n\to\mu,\qquad\|y\|_2\le Cs^5.
\tag{35.7}
$$

For $h=Ms^8$, P (104.2) gives

$$
\|R_s(h)U_s-K_{\rm rec}\|
\le\eta_s+CM^{3/4}s^6+C(M^{-1/4}+M^{-1/2}),\qquad\eta_s\to0.
\tag{35.8}
$$

Choose a fixed small perturbation neighborhood of the compact reconstruction whose simple top is $C_*$. The resolvent identity on a contour around $C_*$, and on a compact spectral exclusion set outside that contour, preserves one simple eigenvalue near $C_*$ and excludes all remaining spectrum above $C_*-3\zeta$, for some fixed $\zeta>0$. First choose $M_{0,d}$ so the retained $M$-error is inside half this neighborhood. For each fixed finite $M\ge M_{0,d}$, choose $s$ small so the other errors fit. At $h=s^6,s^7$, all errors of P (104.2) tend to zero and the same neighborhood applies.

At each $s,h>0$, positive-cutoff relative compactness P70 makes $\mathscr K_s(h)$ positive compact selfadjoint on the full complex space. The bounded products $(R_s(h)U_s^{1/2})U_s^{1/2}$ and $U_s^{1/2}(R_s(h)U_s^{1/2})$ have identical nonzero spectra and algebraic multiplicities. Thus the full principal value $k$ is bounded and simple, and its remaining spectrum is at most $k_2\le C_*-3\zeta$. This is a compact reconstruction separation; it is not an $L^2$ gap of the critical Hamiltonian. In particular (35.8) is not called norm convergence at fixed $M$.

Exact scaling and L41 give the globally bounded late kernel

$$
s^{-5}L^h(\eta,\xi)=j_0\int_1^\infty
 e^{-(h/s^2)t}K_d(t;Y_s\eta,Y_s\xi)dt,
\quad |s^{-5}L^h(\eta,\xi)|\le C.
\tag{35.9}
$$

At any of the present probes $h/s^2\to0$. Dominated convergence on the full product space, followed by (35.5), yields

$$
\langle x,L^hx\rangle=j_0W_1(o)A_p^2s^5+o(s^5).
\tag{35.10}
$$

Moving an input costs its $L^1$ error under the bounded kernel. Contraction below time one and J (29.5) above it give

$$
0\le\langle x,Dx\rangle\le Ch,\quad
\|Dx\|_2\le Chs^{-1/2},\quad
0\le\langle y,R_s(h)y\rangle\le Cs^9h^{-1/2}.
\tag{35.11}
$$

The first estimate integrates $ht\|Q_s(t/2)x\|_2^2$, whose large-time majorant is $Ct^{-5/2}h$. The second integrates $ht\|Q_s(t)x\|_2$ up to $T$, giving $ChT^{1/4}$. The last uses the original long-multiplier estimate P (104.14), $\|R_s(h)J_s\|\le Cs^4h^{-1/2}$, and $\|y\|_2\le Cs^5$. Spectral Cauchy–Schwarz for $0\le L^h\le R_s(h)$ consequently gives

$$
|\langle x,L^hy\rangle|\le Cs^7h^{-1/4},\qquad
|\langle y,Dx\rangle|\le Cs^5hs^{-1/2}.
\tag{35.12}
$$

Since $H_sx=\ell_su_s$, the full unit quotient is exactly

$$
\mathcal Q_s:=\langle z,\mathscr K_s(h)z\rangle
=\frac{\ell_sm+2\ell_sd_s+\langle x,L^hx\rangle-\langle x,Dx\rangle
 -2\operatorname{Re}\langle y,Dx\rangle
 +2\operatorname{Re}\langle x,L^hy\rangle+\langle y,R_s(h)y\rangle}{m+d_s}.
\tag{35.13}
$$

Subtracting $\ell_s$ leaves one early cross copy. At fixed $M$, (35.7), (35.10)–(35.12) give the upper quotient error $C(M^{-1/4}+M^{-1/2})s^5+o_M(s^5)$. For the lower limit, $x,y$ and the late heat kernels are nonnegative. Therefore $\langle x,L^hy\rangle$ and $\langle y,R_s(h)y\rangle$ are nonnegative scalars, while both damping terms are $o_M(s^5)$. Since $k\ge\mathcal Q_s$, this proves the lower inequality in (35.2). At $h=s^q$, the normalized damping, long self and late cross bounds are respectively

$$
O(s^{q-5}),\qquad O(s^{4-q/2}),\qquad O(s^{2-q/4}),
\tag{35.14}
$$

all tending to zero for $q=6,7$. Thus the quotient has the equality in (35.3).

To upgrade its upper bound to the full principal value, keep the exact residual

$$
R_s(h)U_su_s=\ell_su_s+e_s,\qquad e_s=-Dx+L^hx+R_s(h)y.
\tag{35.15}
$$

The following weighted squared bounds hold:

$$
\begin{aligned}
\|U_s^{1/2}Dx\|_2^2&\le Ch^2s^{-1},\\
\|U_s^{1/2}L^hx\|_2^2&\le C(s^8+s^9h^{-1/2}),\\
\|U_s^{1/2}R_s(h)y\|_2^2&\le Cs^9h^{-1/2}.
\end{aligned}
\tag{35.16}
$$

For the middle line, the raw killed-source mass up to $T$ gives $\int F_s\le Cs^{-2}$. Equation (35.9) gives $\|L^hx\|_\infty\le Cs^5$, so the $F_s$-weighted square costs $Cs^8$. The long-time $1\to2$ bound J (29.5), integrated with $e^{-ht}$, gives $\|L^hx\|_2\le Cs^2h^{-1/4}$. Multiplication by $\|J_s\|_\infty\le Cs^5$ gives its other weighted square $Cs^9h^{-1/2}$. The first line follows from (35.11) and bounded $U_s$. For the last, bounded product factorization gives

$$
\|U_s^{1/2}R_s(h)y\|_2^2
\le\|R_s(h)^{1/2}U_sR_s(h)^{1/2}\|\,
                   \langle y,R_s(h)y\rangle
=k\langle y,R_s(h)y\rangle.
\tag{35.17}
$$

The norm $k$ is already bounded by the spectral neighborhood. No $L^2$ norm is assigned to $J_s$ itself. Since $n\to\mu$,

$$
\|(\mathscr K_s(h)-\ell_s)z\|_2^2
\le C(h^2s^{-1}+s^8+s^9h^{-1/2}).
\tag{35.18}
$$

For a unit vector with quotient $\mathcal Q_s>k_2$, integrating $(k-t)(t-k_2)\le0$ over its spectral measure gives

$$
0\le k-\mathcal Q_s
\le\frac{\|(\mathscr K_s(h)-\mathcal Q_s)z\|_2^2}{\mathcal Q_s-k_2}
\le C\|(\mathscr K_s(h)-\ell_s)z\|_2^2.
\tag{35.19}
$$

Here $\mathcal Q_s\to C_*$, and subtracting the quotient minimizes the residual. At fixed $M$, (35.18) is $C(M^2s^{15}+s^8+M^{-1/2}s^5)$; after division by $s^5$ it adds exactly a retained $CM^{-1/2}$ error. At $h=s^q$, its normalized bound is $C(s^{2q-6}+s^3+s^{4-q/2})\to0$. Combining with (35.13)–(35.14) proves (35.2)–(35.3). This proves the original-domain extension directly from its suppliers. $\square$


## 36. Fixed-$H s^5$ damping and the complete principal laws

**Theorem 36.1 (fixed spectral scale and absolute full-principal coefficient).** Assume Definition 32.1, including (32.1). For every separately fixed spectral probe constant $H>0$, independent of the probability parameter contained in $d$,

$$
k_d(Hs^5)=C_*+(\mathscr A\mathfrak m_d-\beta_*H)s^5+o_{d,H}(s^5).
\tag{36.1}
$$

At the two smaller probes, for $q=6,7$,

$$
k_d(s^q)=C_*+\mathscr A\mathfrak m_ds^5+o_d(s^5).
\tag{36.2}
$$

For each separately fixed finite $M\ge M_{0,d}$ of Theorem 35.1,

$$
\begin{aligned}
\mathscr A\mathfrak m_d
&\le\liminf_{s\downarrow0}\frac{k_d(Ms^8)-C_*}{s^5}\\
&\le\limsup_{s\downarrow0}\frac{k_d(Ms^8)-C_*}{s^5}
\le\mathscr A\mathfrak m_d+C_d(M^{-1/4}+M^{-1/2}).
\end{aligned}
\tag{36.3}
$$

In particular (36.3) is a bracket with a retained error, rather than equality at a fixed finite $M$.

Proof. Equations (36.2)–(36.3) follow by inserting Theorem 34.2 into Theorem 35.1. For (36.1), fix $H>0$ first and set $h=Hs^5$. P (104.2) now has all errors tending to zero. The same bounded product factorization and compact spectral neighborhood in Theorem 35.1 give a bounded simple top $k$ and a fixed gap from the rest of the spectrum. Use exactly the vectors and split (35.5)–(35.6), so every field and return remains present.

The late kernel still has (35.9), with $h/s^2=Hs^3\to0$. Therefore (35.7) and (35.10) hold. The long self and late cross bounds in (35.11)–(35.12) are $O_H(s^{13/2})$ and $O_H(s^{23/4})$, hence $o(s^5)$. The damping cross is at most $Cs^5hs^{-1/2}=O_H(s^{19/2})$. The damping quadratic scalar itself has a nonzero limit at this scale; we compute it.

For every fixed $t>0$, $Q_s(t)\to P_t$ strongly on common $L^2$, where $P_t=e^{-t\mathcal E}$. To see the strong assertion directly, first take compactly supported smooth inputs. P104's local both-endpoint convergence gives weak convergence. Selfadjoint semigroup composition gives

$$
\|Q_s(t)f\|_2^2=\langle f,Q_s(2t)f\rangle
 \longrightarrow\langle f,P_{2t}f\rangle=\|P_tf\|_2^2.
\tag{36.4}
$$

Weak convergence plus convergence of norms gives strong convergence on this dense class. Contraction of both semigroups extends it to every fixed $L^2$ input. Restriction and zero extension preserve the composition identity. Since $x=F_su_s\to Vp$ in $L^2$, this also gives convergence of $\langle x,Q_s(t)x\rangle$ at each fixed positive time.

The exact damping scalar is

$$
\frac{\langle x,Dx\rangle}{h}
 =\int_0^T\frac{1-e^{-ht}}h\,\langle x,Q_s(t)x\rangle dt.
\tag{36.5}
$$

Its integrand, extended by zero beyond $T$, is bounded by $Ct$ for $t<1$ and by $Ct^{-5/2}$ for $1\le t\le T$. Indeed $(1-e^{-ht})/h\le t$, and contraction or the $1\to2$ bound applied at $t/2$ gives these two bounds using the uniform $L^2$ and $L^1$ norms of $x$. Both majorants are integrable on their respective intervals. Dominated convergence in (36.5) yields

$$
\frac{\langle x,Dx\rangle}{h}
\longrightarrow\int_0^\infty t\langle Vp,P_tVp\rangle dt
=\|G_0(Vp)\|_2^2=C_*^2.
\tag{36.6}
$$

For the middle equality integrate the nonnegative spectral measure of $\mathcal E$; its $\lambda^{-2}$ moment is finite since $G_0(Vp)=C_*p\in L^2$. Equivalently integrate $\|P_{t/2}Vp\|_2^2t$ by Tonelli. This evaluates the damping on this one input and does not assert a global derivative of an infinite-time operator.

It follows that $\langle x,Dx\rangle=HC_*^2s^5+o_H(s^5)$. Insert this into the exact quotient (35.13). Since $m\to\mu$, $d_s/s^5\to W_1(o)$ and $\ell_s\to C_*$, it gives

$$
\mathcal Q_s=\ell_s+\mathscr A W_1(o)s^5
                         -\frac{C_*^2}{\mu}Hs^5+o_H(s^5).
\tag{36.7}
$$

The full weighted residual (35.18) is, at this fixed scale,

$$
O_H(s^9+s^8+s^{13/2})=O_H(s^{13/2})=o(s^5).
\tag{36.8}
$$

The selfadjoint variance inequality (35.19) consequently upgrades (36.7) to the full principal value, with the same $o_H(s^5)$ remainder. Combining with Theorem 34.2 proves (36.1). Each $H$ was fixed before its $s$ limit. The proof has not replaced a fixed finite $M$ by an $s$-dependent value or inferred a fixed-$M$ equality from (36.1). $\square$

## 37. Strict signs and every actual normalized complex choice

**Theorem 37.1 (positive heat finite part, exact energy and critical orbit).** Fix one datum satisfying Definition 32.1 and suppose additionally $\mathfrak m_d>0$. Define

$$
H_*:=\frac{\mathscr A\mathfrak m_d}{\beta_*}
     =\frac{C_*+j_0A_p^2}{C_*^2}\mathfrak m_d>0.
\tag{37.1}
$$

Then the actual infimum on the original entire complex form domain obeys

$$
\epsilon_c(s)=-aH_*s^5+o_d(s^5),\qquad
E_s=-aH_*s^3+o_d(s^3),\qquad
r_s\sim aH_*s^{-3}\longrightarrow\infty.
\tag{37.2}
$$

For every prescribed $s_n\downarrow0$ and every actual normalized complex choice $\psi_{s_n}\in D(S)$,

$$
\operatorname{dist}_{L^2(\mathbb R^4)}
       (\mathcal U_{s_n}\psi_{s_n},\mathbb Tp)\longrightarrow0.
\tag{37.3}
$$

Proof. For clarity, the positive-shift threshold test applies on this arbitrary fixed original domain, not just on a translated family. For every $h>0$ and every $f\in(\mathcal T_s\mathcal U_s)\mathcal Q$,

$$
q_s^c[\mathcal T_s^{-1}f]+ah\|f\|_2^2
 =a\|(C_s+h)^{1/2}f\|_2^2-\chi_c\|U_s^{1/2}f\|_2^2.
\tag{37.4}
$$

The map $(C_s+h)^{1/2}$ takes this whole complex form domain onto $L^2(\Omega_s)$. The squared norm of $U_s^{1/2}(C_s+h)^{-1/2}$ equals $k_d(h)$. Thus nonnegativity of (37.4) for all complex $f$ is equivalent to $k_d(h)\le C_*$ and, by the actual variational definition, to $\epsilon_c(s)\ge-ah$. Negation gives

$$
k_d(h)>C_*\quad\Longleftrightarrow\quad\epsilon_c(s)<-ah.
\tag{37.5}
$$

This is the bounded complex-form factorization underlying J (56.3). The inverse-square-root product and the Birman–Schwinger operators used for the norm comparison are bounded at each fixed positive shift; no zero-energy inverse is invoked.

Choose separately fixed $0<H_-<H_*<H_+$. Theorem 36.1 gives $k_d(H_-s^5)>C_*$ and $k_d(H_+s^5)<C_*$ for sufficiently small $s$, depending on these choices. Therefore

$$
-aH_+s^5\le\epsilon_c(s)<-aH_-s^5.
\tag{37.6}
$$

First take the scalar liminf and limsup in $s$. Only afterward let the fixed bracketing constants approach $H_*$. This proves the first formula of (37.2), and (32.5) gives the other two. The full actual infimum, not the value of any chosen trial, has been squeezed.

Now P Theorem 105.1 applies to each prescribed sequence and each actual normalized complex ground-state choice, since $r_s\to\infty$. It gives exactly (37.3) with the original $\mathcal U_s$. To make the transport explicit, if $f_s=\mathcal T_s\mathcal U_s\psi_s$, then

$$
\psi_s=(\mathcal U_s)^{-1}\mathcal T_s^{-1}f_s,\qquad
\psi_s(Y)=(j_0s^7)^{-1/2}f_s(\mathscr L_s^{-1}\Xi_s^{-1}Y)
\quad(Y\in I\times\mathbb R^3).
\tag{37.7}
$$

In the phase coordinates of (2.2), the literal inverse is

$$
L_s^{-1}=\begin{pmatrix}1&-\nu s&2\nu^2s^2\\0&1&-2\nu s\\0&0&1\end{pmatrix},
\qquad \mathscr L_s^{-1}(r,z)=(r,L_s^{-1}z).
\tag{37.7a}
$$

The determinant-one maps $\mathcal T_s$ tend strongly to the identity. An auxiliary early vector was used only in spectral tests; no parity, reality or chosen phase is imposed on $f_s$ or $\psi_s$. $\square$

**Theorem 37.2 (negative heat finite part, actual mass and the full Coulomb endpoint).** Fix one datum satisfying Definition 32.1 and suppose instead $\mathfrak m_d<0$. There exist one finite $M\ge M_{0,d}$ and constants $\eta_d,C_d>0$, all fixed before $s\downarrow0$, such that

$$
k_d(Ms^8)\le C_*-\eta_ds^5,\qquad
0<-\epsilon_c(s)/a\le Ms^8
\tag{37.8}
$$

for sufficiently small $s$. For every actual normalized complex choice put $f_s=\mathcal T_s\mathcal U_s\psi_s$. Its full sheared potential expectation satisfies

$$
\mathcal M_s:=\int_{\Omega_s}U_s|f_s|^2d\xi
\le\frac{C_*^2M}{\eta_d}s^3.
\tag{37.9}
$$

For every fixed compact $K\subset\mathbb R^4$,

$$
\|f_s\|_{L^2(K)}^2+\|\mathcal U_s\psi_s\|_{L^2(K)}^2
\le C_{d,K}s^3,
\qquad \mathcal U_s\psi_s\rightharpoonup0\text{ in }L^2(\mathbb R^4).
\tag{37.10}
$$

The bounds hold uniformly over actual choices at each sufficiently small $s$, and the weak assertion holds in the every-choice sequential sense of Definition 32.1.

For the endpoint constants use precisely J Definition 10.1. In raw native coordinates set

$$
\begin{aligned}
\phi(k)&=\sqrt{2/(u-l)}\sin\frac{\pi(k-l)}{u-l},&
\mathsf M_d&=\int_I\phi(k)^2c_\kappa(k)c_\kappa(k)^{\mathsf T}dk>0,\\
d_{C,d}(\mathbf z)&=\sqrt{\mathbf z^{\mathsf T}\mathsf M_d^{-1}\mathbf z},&
\beta_{C,d}&=\frac{\phi(k_0)\int_I\phi(k)^3dk}
                       {4\pi\sqrt{\det\mathsf M_d}},\\
e_{C,d}&=-\frac{\beta_{C,d}^2}{4a}<0,&
\rho_{C,d}&=\frac{\beta_{C,d}}{2a},\\
h_{C,d}(\mathbf z)&=(\det\mathsf M_d)^{-1/4}
 \left(\frac{\rho_{C,d}^3}{\pi}\right)^{1/2}
                    e^{-\rho_{C,d}d_{C,d}(\mathbf z)},&
(\mathcal D_gv)(k,\mathbf z)&=g^{-3/2}v(k,\mathbf z/g).
\end{aligned}
\tag{37.11}
$$

Then along every prescribed $s_n\downarrow0$ and every actual choice on it,

$$
\begin{aligned}
E_s/g_s^2&\longrightarrow e_{C,d},&
E_s&=\chi_c^2e_{C,d}s^6+o_d(s^6),\\
\epsilon_c(s)&=\chi_c^2e_{C,d}s^8+o_d(s^8),&
r_s&\longrightarrow-\chi_c^2e_{C,d}>0,\\
\operatorname{dist}_{L^2(dk\,d\mathbf z)}
 (\mathcal D_{g_s}\psi_s,\mathbb T(\phi h_{C,d}))
 &\longrightarrow0,&
\operatorname{dist}_{L^2}(\mathcal U_s\psi_s,\mathbb Tp)
 &\longrightarrow\sqrt2.
\end{aligned}
\tag{37.12}
$$

The macroscopic phase orbit is centred at the original phase source and has full unit mass.

Proof. Choose $M$ once, after fixing the datum, so that the upper error in (36.3) is less than $-\mathscr A\mathfrak m_d/2$. Its upper limsup is then strictly negative, giving a fixed $\eta_d>0$ and the first inequality in (37.8). The threshold equivalence (37.4)–(37.5) and negative attainment give the other inequality. Set $h=Ms^8$, $\alpha_s=-\epsilon_c(s)/a\in(0,h]$ and $t_s=\|C_s^{1/2}f_s\|_2^2$. The actual eigen-equation, valid on the full transported operator domain, is

$$
(aC_s-\chi_cU_s)f_s=\epsilon_c(s)f_s,\qquad
t_s=\gamma\mathcal M_s-\alpha_s.
\tag{37.13}
$$

For all complex form-domain vectors $f$, the same bounded factorization gives

$$
\int U_s|f|^2\le k_d(h)\{\|C_s^{1/2}f\|_2^2+h\|f\|_2^2\}.
\tag{37.14}
$$

Apply it to the actual unit vector $f_s$ and substitute (37.13). With $k=k_d(h)<C_*$,

$$
\frac{C_*-k}{C_*}\mathcal M_s\le k(h-\alpha_s),\qquad
\mathcal M_s\le\frac{C_*k(h-\alpha_s)}{C_*-k}
                 \le\frac{C_*^2M}{\eta_d}s^3.
\tag{37.15}
$$

This repeats the form algebra in (28.4)–(28.8) on the present original domain; here the signed supplier is (36.3), so translated-family membership is unnecessary. All constants are independent of the actual normalized complex eigenvector.

The full field $U_s\to V$ uniformly, and $V$ has positive minimum on each fixed compact set. Such a compact lies inside $\Omega_s$ for small $s$. Hence (37.9) gives the first local bound in (37.10). The inverse shears send a fixed compact into one fixed larger compact and preserve measure; (37.7) gives the unsheared bound with the same order. Testing against compactly supported $L^2$ functions now gives weak convergence to zero; approximation of an arbitrary $L^2$ test and unit norm give global weak zero. This does not give global strong zero, since every state still has norm one.

This is exactly J (10.2)'s additional actual weak-zero hypothesis, with the original source, path, cutoff-one normalization and complex domains. J Theorem 10.2 therefore yields the first four assertions and the macroscopic orbit in (37.12) with exactly (37.11). Both $\phi$ and $h_{C,d}$ have norm one: after $\mathbf z=\mathsf M_d^{1/2}y$, the latter normalization reduces to $4\rho_{C,d}^3\int_0^\infty R^2e^{-2\rho_{C,d}R}dR=1$. This verifies the full unit mass without a new endpoint theorem. Finally unit norm and weak zero imply

$$
\operatorname{dist}(\mathcal U_s\psi_s,\mathbb Tp)^2
 =2-2|\langle p,\mathcal U_s\psi_s\rangle|\longrightarrow2.
\tag{37.16}
$$

The argument began with arbitrary actual choices. Any failure of its every-choice limiting statements supplies a sequence of failing actual choices, contradicting the same estimates and the same application of J Theorem 10.2. $\square$

## 38. Analytic interfaces and the remaining zero stratum

**Definition 38.1 (local heat and global scope).** The local heat tool used with (32.10) is Colin de Verdière–Hillairet–Trélat, *Small-time asymptotics of hypoelliptic heat kernels near the diagonal, nilpotentization and related results*, Annales Henri Lebesgue 4, [Theorem A, Corollary 1.1 and Theorem 3.2](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf). Its original vector fields here are $\varepsilon\partial_k$ and $c_\kappa(k)\cdot\partial_q$, smooth and divergence free on the fixed larger pole-free neighborhood, with zero drift and raw smooth density. The flag is $(2,3,4)$, the privileged weights are $(1,1,2,3)$ and the step is three because the determinant in (1.3) has a nonzero margin. The source is interior. The Dirichlet realizations are selfadjoint contractions before shift, and satisfy the allowed exponential bound after the retained $\lambda$ shift. The nilpotent density in the chart is $j_0d\xi$. The integer diagonal expansion through order three gives precisely an integrable $O(t^{-1/2})$ remainder after the three displayed subtractions. Localization uses a common interior neighborhood, not equality of different operator domains.

These local facts concern diagonal coefficients and local smoothness. In Theorem 33.1, the six finite strip derivatives, the bridge deletion estimates, the exact raw scaling, the input-height exponents and the separate L41 large-time bound supply all global time/input passages. In particular the local heat theorem alone does not permit an expanding-time derivative or an exchange of endpoint and infinite-time limits. The homogeneous dimension seven in these estimates is a dilation-volume exponent.

The form interface in (37.4) and (37.14) is the closed semibounded complex-form/selfadjoint-operator correspondence; see Teschl, *Mathematical Methods in Quantum Mechanics*, [§2.3, Theorem 2.13, Lemma 2.14 and (2.65)](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf). Here the inherited Friedrichs form is nonnegative, $h>0$ makes its square root onto, and $U_s$ is bounded nonnegative at each fixed $s$. These are exactly the hypotheses used in the displayed bounded factorization. The compact spectral separation in Theorems 35.1 and 36.1 belongs only to the specified reconstruction/Birman–Schwinger operators, not to a positive $L^2$ threshold gap for $H_c$. All canonical heat, bridge, Sobolev, response, reconstruction, attainment and original-domain antecedents retain their stated ordinary conditional scopes.

**Definition 38.2 (fixed limits and unresolved classification).** The scalar $\mathfrak m_d$ is the original raw heat functional (32.8), including both faces, the full clock coefficients and the entire original large-time tail. Theorems 34.2 and 36.1 identify its absolute spectral coefficient; they do not evaluate its sign or nonvanishing on the realized original double-zero locus. Nonemptiness or exclusion of that locus, the full original-family response and quartic sign classification, and actual scale/profile selection when $\mathfrak m_d=0$ remain unresolved. The zero fifth-order coefficient supplies no strict crossing or deficit. Thus the strict-sign implications do not by themselves settle every admitted original datum.

Every datum, its interval, source, signed vector, analytic margins, $a$ and $B$ clock is fixed first. In the matching argument, $\ell$ and then $\delta$ are fixed before $s\downarrow0$, and $\delta\downarrow0$ follows that limit. In (36.3) and Theorem 37.2, one finite $M$ is fixed before $s$. In (36.1), each $H>0$ is fixed before $s$, and the bracketing constants in (37.6) approach $H_*$ only after the scalar $s$ limits. There is no $M(s)$, $H(s)$, moving source, source-to-face limit, phase cutoff or claim uniform over data outside the retained analytic window. In particular the finite-$M$ error in (36.3) is not discarded.

The exact inverse-shear reconstruction remains (37.7); original raw wavefunctions and unit-source kernels have their different Jacobian factors in (1.9). All actual-state conclusions concern every normalized complex choice on every prescribed sequence. The early positive vector and the fixed canonical parities do not restrict the actual competitor class. Physical spatial dimension, physical $SO(3)$, operational state preparation and resource clocks require additional correspondences and are not selected by these analytic alternatives.

## 追加锚（本行以下为增补区）


## 39. Quantitative estimates at zero absolute heat finite part

**Definition 39.1 (fixed frame and quantitative scales).** Fix precisely one datum satisfying Definition 32.1, including its analytic window and $C_{\rm resp}=C_4=0$, and assume additionally $\mathfrak m_d=0$. Retain all notation of (32.3)–(32.8), (33.1), (24.24) and (24.40). In particular $G_s=\sum_{i=0}^4s^ig_i$, $N_0=VG_0$, $N_s=F_sH_s$, $L_s=H_sF_s$, and $L_su_s=\ell_su_s$, with the normalization in (24.3). Write

$$
\omega=1+|r|,\qquad R(\xi)=1+\mathfrak d(\xi),\qquad
\mathfrak d(\xi)=d_E(0,\xi),\qquad q=\frac{41}{8}.
\tag{39.1}
$$

First fix a safe radius $\ell>0$ so that $(-\ell/s,\ell/s)\Subset I_s$ and $\nu\ell<1/4$. The constants in the following estimates may depend on this fixed datum and radius. Set $L=\ell/s$, $T=s^{-2}$. The symbols $\delta$ and $\epsilon$ below are time integration split points; the estimates are uniform in their indicated ranges. They do not change the datum, either original face, a spectral probe, or a competitor domain.

The source is exactly (32.2), with all three jointly realized rational components. Measures, the unit raw source, the factors $j_0s^7$ and the field-only $j_0^{-1}$ are (32.4); all real frequencies and the complete complex domains are those of Definition 32.1. The $B$ heat clock and its $\lambda$ shift are independent of $a$. A spectral constant denoted $H>0$ below is distinct from the fixed probability parameter in $d$, and is always fixed separately before $s\downarrow0$.

The quantitative statements in §§39–44 are `repo-derived` consequences for this original-source conditional problem. The compact endpoint regularity used below is the `literature-attested` scope of Colin de Verdière–Hillairet–Trélat, [Theorem A and Corollary 1.1, pp. 901–904](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf), with the hypotheses identified in Definition 38.1. The global integrations will be proved using the original P76, L41 and finite-bridge estimates, separately from that local regularity.

**Lemma 39.2 (endpoint estimates with integrable tests).** There are fixed constants $C,\delta_0>0$ such that, for $0<v\le1$, the zero-extended original kernel satisfies

$$
\left|K_d(v;Y_s\eta,Y_s\xi)-K_d(v;o,o)\right|
\le Cv^{-7/2}\min\left\{1,\frac{s}{\sqrt v}
                  (\mathfrak d(\eta)+\mathfrak d(\xi))\right\}.
\tag{39.2}
$$

For the input-height-zero relative coefficient kernel $k_j$ in J (30.3), $0\le j\le4$, the corresponding bound is

$$
|k_j(t;\eta^{-1}\xi)-k_j(t;0)|
\le Ct^{(j-7)/2}\min\left\{1,
          \frac{\mathfrak d(\eta)+\mathfrak d(\xi)}{\sqrt t}\right\}.
\tag{39.3}
$$

The tests $p^2$ and $|g_0|\otimes|g_0|$ have finite first homogeneous moments.

Proof. Put $u=\sqrt v$. The exact chart relations are
$\Xi_s=\Xi_u\delta_{s/u}$ and
$\mathscr L_u\delta_{s/u}=\delta_{s/u}\mathscr L_s$; hence
$Y_s=Y_u\delta_{s/u}$. On a fixed sufficiently small compact set of rescaled endpoints, the local heat theorem just cited bounds the first endpoint derivatives of
$j_0u^7K_d(u^2;Y_u\eta',Y_u\xi')$ uniformly as $u\downarrow0$. Its $C^\infty$ conclusion includes these $C^1$ bounds. The smooth determinant-one shear and the bounded clock factor preserve them. For $u$ bounded away from zero, positive-time interior regularity gives the same bound on a smaller fixed compact set.

A homogeneous gauge equivalent to $\mathfrak d$ has coordinates of weights $(1,1,2,3)$. On a small gauge ball, ordinary coordinate displacement is bounded by a constant times gauge displacement. The mean value inequality therefore proves (39.2) when both scaled endpoints are in that ball. If either is outside it, the minimum in (39.2) is bounded below by a fixed positive constant. P Proposition 76.1's global both-endpoint bound then proves the assertion there. This also covers an endpoint outside the native domain, where its kernel is zero: such an endpoint cannot lie in the fixed interior ball. Local Dirichlet heat localization requires a common interior neighborhood, not identical whole-space and killed operator domains.

At time one the relative $n=0$ kernels have the global supremum bound of J Lemma 30.2 and bounded derivatives near the identity. The latter follow from the same smooth local coefficients, or directly from the finite Gaussian bridge coefficients. Scaling (33.8), followed by the group quasi-triangle inequality, gives (39.3). Input-height terms of degrees $n\ge1$ are not included in this bounded relative kernel and will be estimated separately. Finally (24.4) gives $p^2,|g_0|\le CR^{-10}$. Homogeneous volume has degree seven, so their first homogeneous moments, and consequently the first moments of the product test, are finite. $\square$

## 40. Uniform quantitative seed matching

**Theorem 40.1 (seed rate on the full endpoint spaces).** With $\alpha_s,\beta_s$ as in (33.1),

$$
|\alpha_s-s^5Z_d|+
 |\beta_s-j_0a_0^2s^5Z_d|\le C_ds^{41/8}.
\tag{40.1}
$$

More precisely, for every $s^2<\delta<\delta_0<1$ and sufficiently small $s$, uniformly over those split points,

$$
\begin{aligned}
&|\alpha_s-s^5Z_d|+|\beta_s-j_0a_0^2s^5Z_d|\\
&\quad\le Cs^5\left\{\sqrt\delta+\Psi_\ell(\delta)
               +s\delta^{-3}+s(1+|\log s|)\right\},
\end{aligned}
\tag{40.2}
$$

where $\Psi_\ell$ is (33.3).

Proof. Split at $D=\delta/s^2$, keeping the safe strip fixed during differentiation. The sixth finite derivative estimate (33.5), multiplied by $s^6$, is bounded uniformly by

$$
C\{s^5\sqrt\delta+s^6(1+|\log s|)\}.
\tag{40.3}
$$

Indeed $1<D<T$ and $\log(2+D)\le C(1+|\log s|)$. Odd fifth scalar derivatives vanish on this symmetric estimating strip for both tests. They are not discarded on the original nonsymmetric interval by a parity assumption on an actual state.

Restore the full kernels on the short interval as in the proof of Theorem 33.1, retaining the exit event. The $n=0$ field and relative-return deleted paths cost $Cs^5\Psi_\ell(\delta)$: the bound is $Ct^{(j-7)/2}e^{-cL^2/t}$ at degree $j$, including the native degree zero, and substitution $v=s^2t$ gives precisely that expression. The outer seed input has supremum $O(L^{-10})$ and mass $O(L^{-3})$; J (31.7), (31.9) bound its native/safe and retained coefficient returns, after their factors, by $Cs^8$. These are full-output bounds.

For inner inputs of height degree $n\ge1$, (33.6) before taking a limit gives the uniform bound

$$
Cs^5\sum_{n=1}^4s^nM_n(L),\qquad
M_1,M_2\le C,\quad M_3\le C(1+\log L),\quad M_4\le CL.
\tag{40.4}
$$

It is at most $Cs^6(1+|\log s|)$. The original covariance comparison remains valid after a path leaves the safe strip by the fixed denominator margins. Safe paths cannot end beyond either original face. Thus these estimates include every deleted input, output and face contribution, not just outputs on a compact set.

For the native middle interval $v\in[\delta,1]$, apply (39.2) in the two exact expressions (33.7). Their endpoint tests have finite first moments, so their differences from the exact source diagonal are at most

$$
Cs^6\int_\delta^1v^{-4}dv\le Cs^6\delta^{-3}.
\tag{40.5}
$$

For each canonical $n=0$ tail, (39.3) similarly gives

$$
Cs^6\int_\delta^\infty v^{(j-8)/2}dv
\le Cs^6\delta^{-3},\qquad0\le j\le4.
\tag{40.6}
$$

Here the factor $s^j$ and the exact heat rescaling have both been included. All five integrals converge at infinity. Odd diagonal coefficients are zero; the even diagonal integrals are exactly the three quantities in (33.9), with their original clock terms and $j_0$ factors.

For $n\ge1$ retain the entire ordered kernel (33.11). After division by $s^5$ its bound is

$$
Cs^{7/p_n-7+n}\,
 \delta^{(j-n)/2-7/(2p_n)+1},\qquad
(p_1,p_2,p_3,p_4)=(1,1,7/6,7/5),\quad n\le j\le4.
\tag{40.7}
$$

For $n=1,2$, the most negative $\delta$ exponent is $-5/2$; for $n=3,4$ it is respectively $-2,-3/2$. The corresponding powers of $s$ are $1,2,2,2$. Thus the sum of (40.7) is at most $Cs\delta^{-3}$. This accounts for every nonzero input-height degree without an absolute fourth $L^1$ height moment.

Combining (40.3)–(40.7) identifies the two scalars with $s^5B_d(\delta)$ and $j_0a_0^2s^5B_d(\delta)$ up to the displayed errors. Theorem 32.3 gives $|B_d(\delta)-Z_d|\le C\sqrt\delta$, proving (40.2). That inequality is uniform on the whole stated range. It therefore permits the substitution $\delta=s^{1/4}$. Since $\Psi_\ell(\delta)$ is bounded by every positive power of $\delta$ as $\delta\downarrow0$, its terms are bounded by $Cs^{1/8}$ after division by $s^5$; so are $\sqrt\delta$, $s\delta^{-3}=s^{1/4}$ and $s(1+|\log s|)$. This proves (40.1). $\square$

## 41. Bounded products and the complete finite-row rate

**Lemma 41.1 (product convergence with a rate).** The bounded reconstruction products satisfy

$$
\|N_s-N_0\|_{2\to2}\le C_ds^{4/7}.
\tag{41.1}
$$

Consequently $s^4\|(N_s-N_0)g_4\|_2=O(s^{32/7})$ using only the existing fixed $L^2$ charge $g_4$.

Proof. The field memberships used here are $V,rV\in L^2$, $V\in L^\infty$ and $\sup_{|r|>L/4}V\le CL^{-5}$, from (24.4) and the canonical field bounds. Below time one, contraction and (24.6) bound $(F_s-V)Q_s(t)$ by $Cs$. Above time one the row/column $L^2$ heat estimate gives

$$
\|M_{F_s-V}Q_s(t)\|_{2\to2}
\le\|M_{F_s-V}Q_s(t)\|_{\rm HS}
\le C\|F_s-V\|_2t^{-7/4}.
\tag{41.2}
$$

Its integral is $O(s)$. Thus it remains to estimate $V(H_s-G_0)$ as a product. Here $VG_0$ means the operator-norm convergent integral $\int_0^\infty VP_tdt$, $P_t=e^{-t\mathcal E}$: contraction controls the lower end and the Hilbert–Schmidt estimate $C\|V\|_2t^{-7/4}$ controls the upper end. Compact testing and adjointness identify it with $N_0$. No unweighted $G_0$ on arbitrary $L^2$ is used.

On output heights $|r|>L/4$, the native, safe and canonical finite-time products have norm at most $CTL^{-5}=O(s^3)$. On inner output heights, reverse the symmetric heat kernel and retain the event of leaving the safe strip. J (31.6) gives the row supremum $Ct^{-7/2}e^{-cL^2/t}$, while its row mass is bounded. Interpolation gives row $L^2$ norm $Ct^{-7/4}e^{-c'L^2/t}$. Multiplication by $V\in L^2$ and integration in $t$ therefore cost

$$
C\|V\|_2\int_0^Tt^{-7/4}e^{-c'L^2/t}dt
\le CL^{-3/2}=O(s^{3/2}).
\tag{41.3}
$$

This handles original/safe and canonical/safe deletions, including all input phases and zero-extended outputs. The canonical time tail above $T$ has norm $CT^{-3/4}=O(s^{3/2})$ after multiplication by $V$.

For the inner safe comparison, the first derivative has the row bound

$$
\|\partial_\theta q_\theta^L(t;\xi,\cdot)\|_2
 \le Ct^{-7/4}(|r_\xi|+\sqrt t),
\qquad0\le\theta\le s,\quad0<t\le T.
\tag{41.4}
$$

To derive it, differentiate the same common bridge as in (24.9). At first order its positive majorant has row $L^1$ norm $C(|r_\xi|+\sqrt t)$ and row supremum $Ct^{-7/2}(|r_\xi|+\sqrt t)$. The determinant-one $D_A$ change in (24.10) preserves phase volume; the inverse-determinant and supremum moments in (24.12), P (107.5) give these two bounds with the safe indicator retained. Their geometric mean gives (41.4). By symmetry one may use the output height in it. This proves the asserted row bound rather than inferring it from an arbitrary-input threshold derivative.

For $0<\epsilon<1$, integrate (41.4) on $[\epsilon,T]$ after multiplication by $V$. The Hilbert–Schmidt bound is

$$
Cs\int_\epsilon^Tt^{-7/4}
       (\|rV\|_2+\sqrt t\|V\|_2)dt
\le Cs\epsilon^{-3/4}.
\tag{41.5}
$$

On $(0,\epsilon)$ contraction costs $C\epsilon$. Equations (41.2)–(41.5) give, uniformly in that range,

$$
\|N_s-N_0\|\le C\{s+\epsilon+s\epsilon^{-3/4}
                                      +s^{3/2}+s^3\}.
\tag{41.6}
$$

Set $\epsilon=s^{4/7}$ in this uniform inequality to obtain (41.1). The same proof with extra safe killing gives a uniform bound for the safe joint product; all constants are independent of the time split. $\square$

**Lemma 41.2 (full finite-row norm).** The exact finite-row error of (24.40) satisfies

$$
\|E_s^{\rm row}\|_2\le C_ds^{33/8}.
\tag{41.7}
$$

Proof. J Theorem 33.2 already gives this rate for the seed, with the smaller error $Cs^5(1+|\log s|)$. For $i=1,2,3$, the inner safe return Taylor products have norm $O(s^{5-i})$ by the integrable derivative lists (24.34). After the exterior factor $s^i$ they cost $O(s^5)$. Their original-path deletions, coefficient-path deletions and coefficient time tails have the explicit higher powers (24.35)–(24.36). For $i=1$ these give $O(s^6)$ after the exterior factor; for $i=2$ they give $O(s^7)$; for $i=3$ the least power is $s^{41/6}$. These estimates cover the entire output space.

It remains to replace the old outer-input norm loss. Write $w_i=6-i$ and $g_i^{\rm out}=\mathbf1_{|r|>L/4}g_i$. By (24.29), $\|g_i^{\rm out}\|_2\le CL^{-w_i}$. The actual and safe joint products are uniformly bounded by Lemma 41.1 and its safe proof. Their outer-input contributions after $s^i$ are therefore $O(s^iL^{-w_i})=O(s^6)$, with no factor $T$.

For every retained coefficient product $s^{i+k+j}V_kG_jg_i^{\rm out}$, $k+j\le4-i$, put $j=n+m$. On times below one use bounded $V_k$, return output $L^2$ and $\|r^ng_i^{\rm out}\|_2\le CL^{n-w_i}$. Integration of $t^{m/2}$ gives total order at least $s^{i+k+m+w_i}$, hence at least $s^6$.

For long times $V,V_1\in L^2$ are paired with output $L^\infty$; $V_2,V_3\in L^4$ are paired with output $L^4$. J (30.4)'s time power for input exponent $p$ and output exponent $b$ is $m/2-(7/2)(1/p-1/b)$. The following choices cover all relative degrees that occur:

$$
\begin{array}{c|c|c|c}
b&m&p&\text{time power}\\ \hline
\infty&0,1&2&-7/4,-5/4\\
\infty&2&3/2&-4/3\\
\infty&3&7/6&-3/2\\
4&0&6/5&-49/24\\
4&0&3/2&-35/24\\
4&1&7/6&-13/8
\end{array}
\tag{41.8}
$$

All powers are strictly below $-1$. For $g_1,g_2$, interpolate $L^1$ with $\omega^{w_i}L^2$: for $\vartheta=2(1-1/p)$,

$$
\omega^{w_i\vartheta}g_i\in L^p,\qquad
\|r^ng_i^{\rm out}\|_p\le CL^{-(w_i\vartheta-n)}
\quad(n\le w_i\vartheta).
\tag{41.9}
$$

Thus the total power is $i+k+m+w_i\vartheta$. For $g_3$, only $m=0,1$ with $p=2$ is needed and its weighted $L^2$ bound suffices. To make the complete index coverage explicit, the minimum powers over $0\le n\le j$ for each retained group of products are

$$
\begin{array}{c|c|c|c}
i&k&j&\text{minimum power}\\ \hline
1&0&0,1,2&6\\
1&0&3&38/7\\
1&1&0,1,2&7\\
1&2&0&14/3\\
1&2&1&38/7\\
1&3&0&17/3\\
2&0&0,1,2&6\\
2&1&0,1&7\\
2&2&0&16/3\\
3&0&0,1&6\\
3&1&0&7
\end{array}
\tag{41.10}
$$

The entries are lower bounds when a group contains several $j$'s. In the $V_2G_1g_1$ entry, use $p=3/2$ for $n=1,m=0$ and $p=7/6$ for $n=0,m=1$; in $V_2G_0g_i$, use $p=6/5$. For $V G_3g_1$, the successive $m=0,1,2,3$ choices are exactly the first three lines of (41.8). All height inequalities in (41.9) hold for these choices. In particular the least powers for $i=1,2,3$ are $14/3,16/3,6$, respectively, all larger than $33/8$.

Finally the ordered field cross remainders retain the norms in J §§39, 46: for $g_1$, the $j=0$ product uses $G_0g_1\in L^2$ and a supremum remainder $O(s^4)$, while $j=1,2,3$ use $L^4$ returns with field remainders $O(s^3),O(s^2),O(s)$. Their total orders after $s^{1+j}$ are at least $s^5$. For $g_2$, the three $L^4$ remainders are $s^3,s^2,s$, and for $g_3$ they are $s^2,s$; after $s^{i+j}$ these again cost $O(s^5)$. These are full ordered products, so no separate $L^2$ membership for a high field coefficient is asserted. Lemma 41.1 gives the remaining $g_4$ row as $O(s^{32/7})$. Adding the seed, all three lower rows and this last row proves (41.7). $\square$

## 42. Quantitative tested charges and the early principal value

**Lemma 42.1 (tested lower charges).** For the errors in (24.24),

$$
\begin{aligned}
\sum_{i=1}^3s^i|\langle p,E_{i,s}\rangle|
 &\le C\{s^{31/6}+s^{21/4}+s^6(1+|\log s|)\},\\
s^4|\langle p,(N_s-N_0)g_4\rangle|&\le Cs^{11/2}.
\end{aligned}
\tag{42.1}
$$

Proof. Put $k_i=5-i$. In the ordered return term (24.26), Taylor expand the inner input through degree $k_i$, keeping its degree-$k_i$ coefficient, and bound the next derivative of order $6-i$. The required input exponents, indexed in order by $n=0,\ldots,6-i$, are

$$
\begin{array}{c|c|c}
i&(p_n)&\text{large-time powers}\\ \hline
1&(1,1,7/6,7/5,7/4,2)&(-1,-3/2,-3/2,-3/2,-3/2,-7/4)\\
2&(1,7/6,7/5,7/4,2)&(-3/2,-3/2,-3/2,-3/2,-7/4)\\
3&(6/5,18/13,18/11,2)&(-17/12,-55/36,-59/36,-7/4)
\end{array}
\tag{42.2}
$$

These memberships follow from J (38.1), (43.4), (44.3), (45.3) and the retained weighted $L^2$ norms. The time powers are $(6-i-n)/2-7/(2p_n)$. At short times use the available weighted $L^2$ norms and integrable nonnegative half powers. The sole logarithm is the first entry for $i=1$; every other long-time exponent is strictly below $-1$. After $s^i$, Taylor's remainder is consequently $O(s^6(1+|\log s|))$.

The added coefficient has total degree $i+k_i=5$. Replace its test $F_sp$ by $Vp$; their $L^1+L^2$ difference is $O(s)$ by (24.6). The derivative list (24.34) bounds this coefficient in $L^2$ below time one and $L^\infty$ above it, so that replacement costs $O(s^6)$. Its complete canonical scalar with test $Vp$ is zero by reflection: $g_i$ has parity $(-1)^i$ and $\mathsf Q_{k_i}$ has parity $(-1)^{k_i}$. This uses only canonical fixed-test parity.

We spell out restoration of the additional degree, beyond the old retained degrees. The latter have outer coefficient scalar bound $O(s^{31/6})$ in (24.33), and native/safe outer scalar bound $O(s^6)$ in (24.30). For the new coefficient transpose its complete symmetric endpoint kernel onto $Vp=\mu g_0$. The finite-time $L^2$ bound is

$$
\left\|\int_0^T\mathsf Q_{k_i}(t)(Vp)dt\right\|_2
 \le C(1+T^{k_i/2-3/4}).
\tag{42.3}
$$

For $t\ge1$ its $n=0$ term uses $Vp\in L^1$ and output $L^2$, with power $k_i/2-7/4$. For $n\ge1$ use the seed memberships in (33.10); their integrated powers are no larger. For $t<1$ the weighted $L^2$ seed moments give a finite bound. Therefore its outer scalar, after $s^{i+k_i}=s^5$, is at most

$$
Cs^5L^{-(6-i)}(1+T^{k_i/2-3/4})=O(s^{15/2}).
\tag{42.4}
$$

For its inner coefficient exits and its time tail use the order-$k_i$ sublists of (42.2), omitting the final entry. Formula (24.36), with the exterior $s^i$, gives powers $i+7/p_n-2+n$. For $i=1$ these are $6,7,7,7,7$; for $i=2$ all are $7$; for $i=3$ they are $41/6,127/18,131/18$. Every time power is strictly integrable and every resulting power is at least six. The exit event remains in the positive majorant before integration. This covers the extra retained coefficient on all output points and restores its whole canonical time interval. Thus there is no unquantified tail modulus in this scalar restoration.

For the field part of (24.26), keep its first omitted coefficient as in Theorem 34.1. Every such scalar has total degree five and vanishes by reflection. The exceptional $(i,j)=(1,0)$ uses the degree-four supremum remainder $O(s^5(1+|\log s|))$ and costs $O(s^6(1+|\log s|))$ after $s^i$. The other eight entries of (24.38) use $L^4$ returns: when the added field degree is three, J Lemma 32.1 gives $O(s^{13/4})$ and the exterior degree is two, giving $O(s^{21/4})$; at added degrees two and one the remainders $O(s^3),O(s^2)$ give order at least six. This proves the first line of (42.1).

For the final charge refine (34.4) to

$$
(L_s-K_{\rm rec})p=sD_1p+O_{L^2}(s^{3/2}),\qquad
D_1p=G_0(V_1p)+\mu G_1g_0.
\tag{42.5}
$$

For the seed-return term, the second strip derivative on $g_0$ has time-integrated $L^2$ bound $C(1+T^{1/4})$: the $n=0$ large-time power is $-3/4$, the $n=1$ power $-5/4$, and the $n=2$ power $-7/4$. Multiplication by $s^2$ gives $O(s^{3/2})$. Native/strip and degree-zero/one coefficient restorations are the $O(s^{3/2})$ column $L^2$ bounds in the proof of Lemma 24.4 and (34.4).

For the field input, J Lemma 32.1 gives $\|F_s-V-sV_1\|_2=O(s^{3/2})$, and its supremum norm is $O(s^2)$. Multiplication by $p$ and (24.14) give the same $L^2$ return error. It remains to bound $H_s(V_1p)-G_0(V_1p)$ by $Cs$. Its first strip derivative is time integrable since $V_1p,rV_1p\in L^1$; here use $V_1\in L^2$, $p,rp\in L^2$. Its short-time weighted $L^2$ bounds hold because $\omega^4V_1$ is bounded. That same weight bounds its outer-input error by $CTL^{-4}=O(s^2)$; its native deletion and canonical time tail cost $O(s^{3/2})$. This proves (42.5).

The normalized charge $g_4$ is even, as proved in Theorem 34.1, whereas $D_1p$ is odd. By adjointness, with only $g_4\in L^2$,

$$
s^4\langle p,(N_s-N_0)g_4\rangle
=s^4\langle(L_s-K_{\rm rec})p,g_4\rangle
=O(s^{11/2}).
\tag{42.6}
$$

This proves the second assertion. $\square$

**Theorem 42.2 (quantitative early principal matching).** Under Definition 39.1,

$$
\ell_s=C_*+\mathscr A Z_ds^5+O_d(s^{41/8}).
\tag{42.7}
$$

Proof. In the seed ordered identity (24.26), its return scalar is $\mu\beta_s$ up to $O(s^6(1+|\log s|))$ by (24.27)–(24.28). Its degree-zero field scalar is $(C_*/\mu)\alpha_s$. Theorem 40.1 therefore makes their sum

$$
\left(\frac{C_*}{\mu}+\mu j_0a_0^2\right)Z_ds^5
       +O(s^{41/8})=\mathscr A Z_ds^5+O(s^{41/8}).
\tag{42.8}
$$

For seed field terms $j=1,2,3,4$, retain the first omitted coefficients $V_4,V_3,V_2,V_1$. Their integrable degree-five scalars vanish by reflection. The return norms are respectively $L^2,L^4,L^4,L^\infty$, as in the proof of Theorem 34.2. After their factors, the quantitative field remainders give $O(s^6(1+|\log s|))$, $O(s^{21/4})$, $O(s^6)$ and $O(s^{11/2})$. In the last case use the degree-one $L^2$ field remainder $O(s^{3/2})$. All these exponents exceed $41/8$.

Lemma 42.1 treats every other fixed-test charge. Lemma 41.2 and (24.13) give the moving-test error

$$
|\langle E_s^{\rm row},u_s-p\rangle|
 \le Cs^{33/8}s=Cs^{41/8}.
\tag{42.9}
$$

Insert these bounds into the exact finite-vector scalar (24.42). Its denominator is $1+O(s)$, so its effect on the displayed $s^5$ term is $O(s^6)$. This proves (42.7). $\square$

## 43. Quantitative late collapse and the full principal norm

**Lemma 43.1 (late two-endpoint collapse).** The function

$$
W^{\rm late}(Y,Z)=\int_1^\infty K_d(t;Y,Z)dt
\tag{43.1}
$$

is globally bounded and jointly smooth in a fixed interior neighborhood of $(o,o)$. It satisfies

$$
|W^{\rm late}(Y_s\eta,Y_s\xi)-W^{\rm late}(o,o)|
\le C\min\{1,s(\mathfrak d(\eta)+\mathfrak d(\xi))\}.
\tag{43.2}
$$

In the notation (35.5)–(35.6), for each fixed $H>0$, $h=Hs^q$, $b=h/s^2$,

$$
\begin{aligned}
x&=Vp+O_{L^1\cap L^2}(s),&m&=\mu+O(s),\\
d_s&=W_{1,d}(o)s^5+O(s^6),\\
\langle x,L^hx\rangle
 &=j_0A_p^2W_{1,d}(o)s^5+O(s^6)+O(s^5\sqrt b).
\end{aligned}
\tag{43.3}
$$

Proof. L Lemma 41.2 bounds $K_d(t;Y,Z)$ by $Ct^{-3/2}$ for $t\ge1$, uniformly in both endpoints; hence (43.1) is bounded. On the interior product space its distribution identity is

$$
(S_Y+S_Z)W^{\rm late}=2K_d(1;Y,Z).
\tag{43.4}
$$

Compact testing justifies integration of the heat equation, and the boundary term at infinity vanishes by the same large-time bound. The sum of the two original bracket-generating systems on the product is bracket generating there. Local hypoelliptic regularity for this sum of squares, with its smooth constant potential $-2\lambda$, makes (43.1) jointly smooth. Thus a local mean value estimate gives (43.2) inside a fixed neighborhood; outside it use the global bound and the positive lower bound of the minimum. This argument requires no large-time endpoint derivative estimate.

By (24.6), (24.13), bounded multiplication and Cauchy–Schwarz, $x-Vp=O(s)$ in $L^1\cap L^2$, $m-\mu=O(s)$ and $\|u_s^2-p^2\|_1=O(s)$. Apply (43.2) to $p^2$ for $d_s$ and to $Vp\otimes Vp$ for the late quadratic scalar. Their first homogeneous moments are finite by (24.4). Replacing either moving $x$ by $Vp$ costs $O(s)$ under the bounded late kernel. The exact kernel scaling is (35.9), so it retains its factor $j_0s^5$.

Finally damping that kernel changes its normalized supremum by at most

$$
C\int_1^\infty\min(1,bt)t^{-3/2}dt\le C\sqrt b
\quad(0<b<1).
\tag{43.5}
$$

Combining the endpoint, moving-input and damping errors proves (43.3). Each $H$ is fixed; the constants in the undamped $O(s^6)$ errors are independent of it. $\square$

**Theorem 43.2 (full-principal enclosure independent of the fixed probe constant).** There is a finite constant $B_d$, independent of the separately fixed $H>0$, such that

$$
\limsup_{s\downarrow0}s^{-41/8}
 \left\{k_d(Hs^{41/8})-C_*+\beta_*Hs^{41/8}\right\}
\le B_d.
\tag{43.6}
$$

This is the norm $k_d$ of the full original positive compact operator (35.1), including the infinite-time field and return.

Proof. Fix $H>0$ and put $h=Hs^{41/8}$. P (104.2) gives norm convergence of the bounded reconstruction product to $K_{\rm rec}$ at this probe: in particular $s^2h^{-1/4}\to0$ and $s^4h^{-1/2}\to0$. The compact spectral neighborhood and bounded product factorization in the proof of Theorem 35.1 therefore apply unchanged. They give a bounded simple top and fixed separation of the remainder of the full selfadjoint compact spectrum. This is separation for the reconstruction, not a positive critical-Hamiltonian threshold gap.

Keep exactly $x,y,m,d_s,z,D,L^h$ in (35.5)–(35.6) and its full quotient (35.13). The damping proof (36.4)–(36.6) applies at the present probe. Its majorants are $Ct$ below time one and $Ct^{-5/2}$ above it, independent of $h$, and $h\to0$, $T\to\infty$. It gives on this fixed input

$$
\langle x,Dx\rangle=C_*^2h+o_{d,H}(h).
\tag{43.7}
$$

Theorem 42.2 and Lemma 43.1 evaluate the remaining early and late scalar terms in the quotient. Subtracting $\ell_s$ from (35.13) leaves
$\ell_sd_s+\langle x,L^hx\rangle$ before the damping and smaller cross/self terms. Division by $m+d_s=\mu+O(s)$ therefore gives

$$
\begin{aligned}
\ell_s+\frac{\ell_sd_s+\langle x,L^hx\rangle}{m+d_s}
 &=C_*+\mathscr A\{Z_d+W_{1,d}(o)\}s^5
       +O_d(s^q)+O(s^5\sqrt b)\\
 &=C_*+O_d(s^q)+O(s^5\sqrt b).
\end{aligned}
\tag{43.8}
$$

The last equality uses exactly $\mathfrak m_d=Z_d+W_{1,d}(o)=0$. The constant in $O_d(s^q)$ is independent of $H$. Changes in its $s^5$ scalar denominators cost $O(s^6)$.

For completeness every remaining term of (35.11)–(35.12), and the late damping error in (43.3), has the following order at this probe:

$$
\begin{array}{c|c}
\text{term}&\text{bound}\\ \hline
\langle y,R_s(h)y\rangle& O_H(s^{103/16})\\
\langle x,L^hy\rangle& O_H(s^{183/32})\\
\langle y,Dx\rangle& O_H(s^{77/8})\\
s^5\sqrt{h/s^2}&O_H(s^{105/16})
\end{array}
\tag{43.9}
$$

Every exponent is greater than $q=41/8$. Dividing (43.7) by $m+d_s$ gives $\beta_*Hs^q+o_{d,H}(s^q)$; its denominator error $O_H(s^{q+1})$ is smaller. Consequently the exact full quotient satisfies

$$
\mathcal Q_s\le C_*+B_ds^q-\beta_*Hs^q+o_{d,H}(s^q)
\tag{43.10}
$$

for one finite $B_d$ independent of $H$.

The weighted full residual (35.18) is

$$
O_H(s^{37/4}+s^8+s^{103/16})=o_{d,H}(s^q).
\tag{43.11}
$$

Here $\mathcal Q_s\to C_*$ and the rest of the spectrum stays below $C_*-3\zeta$. The selfadjoint variance inequality (35.19) upgrades (43.10) to the full principal value, with additional error bounded by (43.11). This proves (43.6). Thus a quotient upper estimate has been transferred by an explicit residual and spectral separation to the full norm. $\square$

## 44. The actual energy bound on the entire original complex domain

**Theorem 44.1 (zero finite part and the actual infimum).** For every fixed datum satisfying exactly Definition 32.1 and $\mathfrak m_d=0$, there are finite constants $C_d,s_d>0$ such that

$$
-C_ds^{25/8}\le E_s<0\qquad(0<s<s_d).
\tag{44.1}
$$

The lower bound is for the actual variational infimum (1.7) on its complete complex form domain. It therefore holds for every actual normalized complex ground-state choice, without a parity, support or reality restriction.

Proof. After fixing the datum, choose one finite constant

$$
H_0>\frac{\max(B_d,0)+1}{\beta_*}
\tag{44.2}
$$

and keep it fixed before $s\downarrow0$. Theorem 43.2 gives $k_d(H_0s^q)<C_*$ for all sufficiently small $s$. For every $f$ in the entire transported complex form domain, (37.4) is the exact identity

$$
q_s^c[\mathcal T_s^{-1}f]+ah\|f\|_2^2
 =a\|(C_s+h)^{1/2}f\|_2^2-\chi_c\|U_s^{1/2}f\|_2^2,
\qquad h=H_0s^q.
\tag{44.3}
$$

Since $C_s\ge0$ and $h>0$, its positive square root maps that full domain onto $L^2(\Omega_s)$. The bounded factor satisfies

$$
\|U_s^{1/2}(C_s+h)^{-1/2}\|^2
 =\|U_s^{1/2}(C_s+h)^{-1}U_s^{1/2}\|
 =k_d(h)\le C_*=a/\chi_c.
\tag{44.4}
$$

Thus the right side of (44.3) is nonnegative for every such complex $f$. Taking its infimum over all unit vectors gives $\epsilon_c(s)\ge-aH_0s^q$. The exact original rescaling in (32.5), $\epsilon_c(s)=s^2E_s$, proves the lower bound with $C_d=aH_0$ and $q-2=25/8$. The strict upper bound is the inherited original negative attainment at each positive coupling; it is not needed in the lower-bound argument. $\square$

**Definition 44.2 (scope of the zero-stratum estimate).** Theorem 44.1 is conditional on the original analytic applicability conditions of Definition 32.1 and its three vanishing coefficients. It neither asserts nor excludes occurrence of such a datum. It gives no sign evaluation, exact energy asymptotic or actual scale/profile selection on that stratum. The original unitary, shear, rational source, two Dirichlet faces, raw source measure, full real-frequency set and entire complex domains remain unchanged. The constants are for each separately fixed original datum; no uniform source-to-face or pole-margin limit is asserted. The only substitutions $\delta=s^{1/4}$ and $\epsilon=s^{4/7}$ were made in the uniform inequalities (40.2), (41.6). The final $H_0$ is one finite fixed spectral constant, with no $H(s)$ or $M(s)$. Physical dimension, state preparation and operational resource clocks require additional correspondences beyond these inequalities.

## 追加锚（本行以下为增补区）

## 45. Global early geometry and the moving positive mode

**Definition 45.1 (fixed analytic data and the two spatial scales).** Fix one original datum $d$ satisfying exactly the analytic applicability conditions of Definition 32.1: the jointly realized rational vector (32.2), the larger-interval positive-probability, pole and bracket margins of L Definition 35.1, L Lemma 41.2, P §§76, 87–88, 97 and 104–107, and E Theorem 3.1. The equalities (32.1) are not assumptions in §§45–49. General geometric admission without these analytic antecedents is insufficient. Retain the unit raw $dk\,dq$ source, $j_0$, both original Dirichlet faces, all real phases, the $B$-clock independent of $a$, and the full complex form and operator domains (1.5). Use the sheared chart $Y_s=\Xi_s\circ\mathscr L_s$ and zero extensions in (32.4), with $T=s^{-2}$. All constants below may depend on this separately fixed datum.

Use the positive unit early vector and the exact split of Theorem 35.1, writing

$$
\begin{aligned}
H_sF_su_s&=\ell_su_s,&u_s&\ge0,&\|u_s\|_2&=1,\\
x_s&=F_su_s,&y_s&=J_su_s,&m_s&=\int F_su_s^2,\\
\delta_s&=\int J_su_s^2,&n_s&=m_s+\delta_s,&
z_s&=U_s^{1/2}u_s/\sqrt{n_s}.
\end{aligned}
\tag{45.1}
$$

Thus $x_s\to Vp$ in $L^1\cap L^2$, $u_s\to p$ in $L^2$, $m_s\to\mu$, and $\ell_s\to C_*$. The vector $u_s$ is an auxiliary early eigenvector, not an actual ground state of the native Hamiltonian. Write $\rho(\xi)=d_E(0,\xi)$ for the ambient Engel distance, whose balls have volume $v_E R^7$. Physical phase radius will instead mean

$$
\mathsf M=\int_I\phi(k)^2c_\kappa(k)c_\kappa(k)^{\mathsf T}dk,
\qquad \Delta=\det\mathsf M>0,
\qquad \mathfrak r(q)=(q^{\mathsf T}\mathsf M^{-1}q)^{1/2}.
\tag{45.2}
$$

These are the original tensor and raw density of L Theorem 36.1. Put $\phi_0=\phi(k_0)$, $I_3=\int_I\phi^3dk$, and $A_p=\int Vp>0$ as in (32.6). A finite spectral probe constant $M$ is distinct from $\mathsf M$.

**Lemma 45.2 (one-sided global distance comparison and early heat).** For every pair of endpoints in the complete $\Omega_s$, and $0<t\le T$,

$$
\begin{gathered}
d_E(\eta,\xi)\le C s^{-1}d_{\rm nat}(Y_s\eta,Y_s\xi),\\
0\le q_s(t;\eta,\xi)\le Ct^{-7/2}
 \exp[-c d_E(\eta,\xi)^2/t],\\
0\le F_s(\xi)\le C(1+\rho(\xi))^{-5},\qquad
0\le H_s(\eta,\xi)\le C d_E(\eta,\xi)^{-5}\quad(\eta\ne\xi).
\end{gathered}
\tag{45.3}
$$

Here $d_{\rm nat}$ is the control distance of the original two fields with paths inside the original height interval. The same kernel upper bounds hold after zero extension.

Proof. By the exact rational shear (2.3), or P (97.2), the microscopic fields are $X$ and $a_s(r)Y$, where $a_s(r)=(1+\nu sr)^{-1}$. On the entire actual height interval,

$$
1+\nu sr=\frac{k-\alpha_\kappa}{k_0-\alpha_\kappa},
\qquad 0<c\le1+\nu sr\le C<\infty.
\tag{45.4}
$$

A path with controls $(v,w)$ for $X,a_sY$ has controls $(v,a_sw)$ for $X,Y$ and ambient Engel length at most a fixed multiple of its microscopic native length. The original controls scale by $s$, by the exact chart and form identity. Taking infima over native paths proves the first inequality. The ambient infimum may use more paths, so no reverse comparison or removal of either face is required.

P Lemma 82.2 supplies the original all-endpoint bound $p_t^B\le Ct^{-7/2}\exp(-c d_{\rm nat}^2/t)$. Its Coulhon–Sikora Theorem 4.1 hypotheses are checked there: the nonnegative selfadjoint killed $B$, continuous kernel, all-time diagonal bound and native Davies–Gaffney estimate. Using $q_s=j_0s^7e^{\lambda s^2t}p_{s^2t}^B\circ(Y_s,Y_s)$ and $e^{\lambda s^2t}\le e^\lambda$ for $t\le T$ proves the second line. The polynomial factor in that Gaussian theorem is absorbed by reducing its exponential constant. Integrating from $1$ to $T$ gives the field bound; integrating from $0$ to $T$ gives the off-diagonal return bound. The substitution $v=d_E(\eta,\xi)^2/t$ gives the power $-5$. All comparisons keep the killed kernel itself. $\square$

**Theorem 45.3 (uniform full-spatial moving-mode envelope).** Uniformly on the common space,

$$
0\le u_s(\xi)\le C(1+\rho(\xi))^{-5},\qquad
0\le x_s(\xi)\le C(1+\rho(\xi))^{-10}.
\tag{45.5}
$$

In particular $\sup_s\|u_s\|_p<\infty$ for each fixed $p>7/5$, including $p=\infty$. There is no uniform $L^1$ assertion here.

Proof. The Gaussian (45.3), Haar-ball volume and symmetry imply, by integration in either endpoint and interpolation,

$$
\|Q_s(t)\|_{p\to q}\le
 C t^{-\frac72(1/p-1/q)},\qquad
1\le p\le q\le\infty,\quad0<t\le T.
\tag{45.6}
$$

The constants for $p=q$ are bounded on this finite early interval; sub-Markovianity is only used for the unshifted killed heat. From (35.5), $\|x_s\|_1+\|x_s\|_2\le C$ and $\ell_s\ge c>0$. In $u_s=\ell_s^{-1}H_sx_s$, use $2\to4$ on $(0,1)$ and $1\to4$ on $(1,T)$. The powers are $t^{-7/8}$ and $t^{-21/8}$, respectively, both integrable at the relevant ends. Thus $\|u_s\|_4\le C$, and bounded $F_s$ gives $\|x_s\|_4\le C$. Now use $4\to\infty$ on $(0,1)$ and $1\to\infty$ on $(1,T)$; their powers are $t^{-7/8}$ and $t^{-7/2}$. This proves $\|u_s\|_\infty\le C$.

For completeness apply the convolution split of E Theorem 3.1 to the actual two-endpoint upper kernel in (45.3). If $R=\rho(\xi)\ge2$, split input into

$$
\rho(\eta)\le R/2;\qquad
\rho(\eta)>R/2,\ d_E(\eta,\xi)\le R/2;\qquad
\rho(\eta)>R/2,\ d_E(\eta,\xi)>R/2.
\tag{45.7}
$$

On the first and third regions the kernel is at most $CR^{-5}$, so their sum is at most $CR^{-5}\|x_s\|_1$. Initially $x_s\le C(1+\rho)^{-5}$ by bounded $u_s$ and (45.3). On the middle region its supremum is $CR^{-5}$ and the kernel integral is at most $CR^2$, giving $CR^{-3}$. Hence $u_s\le C(1+\rho)^{-3}$ and $x_s\le C(1+\rho)^{-8}$. Repeating the same split makes the middle contribution $CR^{-6}$; the other contributions remain $CR^{-5}$. This proves (45.5). Local kernel integrability follows from dimension seven, since $\int_{d_E(\eta,\xi)<R}d_E(\eta,\xi)^{-5}d\eta=CR^2$. Finally integrate $(1+\rho)^{-5p}$ in homogeneous polar shells. This uses the existing convolution method on a new globally controlled moving input, without a radial assumption on the native mode. $\square$

## 46. Moving mass and matching full cross and self estimates

**Theorem 46.1 (mass and fixed-probe orders).** There are positive fixed-data constants such that, eventually,

$$
\|u_s\|_1\asymp_d s^{-2},\qquad
\|y_s\|_1\asymp_d s^3,\qquad \|y_s\|_2\le Cs^5.
\tag{46.1}
$$

Fix any finite $M\ge M_{0,d}$ from Theorem 35.1, separately from $s$, and put

$$
h=Ms^8,\qquad b=h/s^2=Ms^6,\qquad
R=R_s(h),\quad L=L^h,\quad D=H_s-H^h.
\tag{46.2}
$$

For this fixed $M$, with a small-$s$ threshold allowed to depend on $M$,

$$
\begin{aligned}
c_ds^8&\le\langle x_s,Ly_s\rangle\le C_ds^8,\\
c_ds^{10}&\le\langle y_s,Ry_s\rangle\le C_ds^{10}.
\end{aligned}
\tag{46.3}
$$

The quantities are nonnegative. Constants may be enlarged for the fixed datum; no $M(s)$ or joint source-to-face limit is asserted.

Proof. Integrating the positive equation for $u_s$ and using the raw killed mass gives

$$
\|u_s\|_1\le\ell_s^{-1}\int_0^T
 e^{\lambda s^2t}\|x_s\|_1dt\le CT=Cs^{-2}.
\tag{46.4}
$$

This is valid by Tonelli even before finiteness is known. For a matching lower bound, choose a microscopic compact set $A$ with $\int_A Vp>0$. Equation (35.5) gives $\int_Ax_s\ge c>0$. Choose a physical compact set $K$ with positive volume, contained in the height interior, and an interval $[t_0,t_1]\Subset(0,1)$. Strict positivity and continuity of the original native heat, uniformly for input $Y_s\eta\to o$ with $\eta\in A$, give

$$
u_s(Y_s^{-1}Y)\ge c s^5\quad(Y\in K),
\qquad |Y_s^{-1}K|=|K|/(j_0s^7).
\tag{46.5}
$$

Indeed the kernel of the restricted time interval in $H_s$ is $j_0s^5\int_{t_0}^{t_1}K_d(t;Y_s\eta,Y)dt$, and $H_sx_s=\ell_su_s$. Integrating (46.5) proves the lower $s^{-2}$ mass. Since $W_1$ is bounded and strictly positive on $K$, multiplication by $J_s=s^5W_1\circ Y_s$ gives both $L^1$ bounds for $y_s$; its $L^2$ bound follows from $\|u_s\|_2=1$.

The bounded late kernel (35.9) now gives

$$
\langle x_s,Ly_s\rangle\le Cs^5\|x_s\|_1\|y_s\|_1\le Cs^8,
\qquad
\langle y_s,Ly_s\rangle\le Cs^{11}.
\tag{46.6}
$$

Also $y_s\le Cs^5(1+\rho)^{-5}$ by (45.5). The integral of $d_E(\eta,\xi)^{-5}(1+\rho(\eta))^{-5}$ is bounded by $C(1+\rho(\xi))^{-3}$. To see this, use (45.7): its first region costs $CR^{-5}R^2$, its second $CR^{-5}R^2$, and its third outside a ball of radius $2R$ costs $C\int_R^\infty r^{6-10}dr=CR^{-3}$; the remaining annulus has the same bound. Therefore

$$
H_sy_s\le Cs^5(1+\rho)^{-3},\qquad
\langle y_s,H_sy_s\rangle\le
 Cs^{10}\int(1+\rho)^{-8}d\xi\le Cs^{10}.
\tag{46.7}
$$

As $0\le H^h\le H_s$ at the positive-kernel level, (46.6)–(46.7) prove the self upper bound.

For the cross lower bound use $x_s$ on $A$ and $y_s$ on $Y_s^{-1}K$. In the physical late time integral restrict to a fixed interval inside $(1,\infty)$. Its positive kernel is bounded below on these compact endpoint sets, and $e^{-bt}\to1$ at fixed $M$. The kernel scaling supplies $cs^5$, while their respective input masses are at least $c$ and $cs^3$. This gives $cs^8$.

For the self lower bound choose a fixed microscopic compact set where $\int u_s\ge c$. Such a set follows from $u_s\to p$ in $L^2$ and positivity. On it $W_1(Y_s\xi)\ge c$, hence $\int y_s\ge cs^5$. The original microscopic heat on a fixed positive time interval converges locally to the positive canonical heat, by the inherited local heat convergence and the smooth exact fields. Its integral is bounded below on a fixed compact product; $e^{-ht}\to1$. Restricting both self inputs to that product gives $cs^{10}$. These lower bounds concern the actual moving $u_s$, not a replacement trial vector. $\square$

## 47. A global weighted late kernel and its logarithmic coefficient

**Lemma 47.1 (global domination and compact-input asymptotic).** For physical endpoints $A,B,Y\in\mathcal C$, define

$$
\begin{aligned}
\mathcal K_b(A,Y)&=\int_1^\infty e^{-bt}K_d(t;A,Y)dt,\\
\mathcal I_b(A,B)&=\int_{\mathcal C}W_1(Y)
             \mathcal K_b(A,Y)\mathcal K_b(B,Y)dY,\qquad 0<b<1.
\end{aligned}
\tag{47.1}
$$

On the entire two-input space,

$$
0\le\mathcal I_b(A,B)\le C(1+\log(1/b)).
\tag{47.2}
$$

Uniformly for $A=(k_A,q_A),B=(k_B,q_B)$ in any fixed physical compact subset of the height interior,

$$
\mathcal I_b(A,B)=
 \frac{\phi_0\phi(k_A)\phi(k_B)I_3}{32\pi^2\Delta}
 \log(1/b)+O(1).
\tag{47.3}
$$

Proof. Integrating the large-time Gaussian of L Lemma 41.2 gives

$$
\begin{aligned}
\mathcal K_b(A,(k,q))&\le
 C\phi(k_A)\phi(k)
 \frac{e^{-c\sqrt b|q-q_A|}}{1+|q-q_A|},\\
W_1(k,q)&\le C\phi(k)(1+|q|)^{-1}.
\end{aligned}
\tag{47.4}
$$

The first estimate follows by splitting its time integral at $|q-q_A|^2$ and using $bt+c|q-q_A|^2/t\ge c'\sqrt b|q-q_A|$; bounded displacements use integrability of $t^{-3/2}$ from one. Heights have bounded factors. To bound the square at any input, the two radial decreasing functions $(1+|q|)^{-1}$ and $e^{-2c\sqrt b|q|}(1+|q|)^{-2}$ have convolution maximized at coincident centers. Explicitly their layer-cake superlevel sets are balls, and the intersection of two balls has volume at most the smaller ball's volume, attained for common centers. Tonelli reduces the assertion to that observation. At the common center the radial integral is bounded by

$$
C\int_0^\infty\frac{r^2e^{-2c\sqrt b r}}{(1+r)^3}dr
 \le C(1+\log(1/b)).
\tag{47.5}
$$

Split at $1$ and $b^{-1/2}$ to obtain the last bound. Cauchy–Schwarz in the positive measure $W_1(Y)dY$ then proves (47.2) for different inputs. This proves a bound on all inputs, including heights near either face and arbitrarily remote phase inputs.

For the coefficient use L Theorem 42.1, keeping its polynomial error. Outside a fixed phase ball containing $q_A,q_B$, uniformly for compact inputs,

$$
\begin{aligned}
W_1(k,q)&=\frac{\phi_0\phi(k)}{4\pi\sqrt\Delta\,\mathfrak r(q)}
                    +O(\phi(k)|q|^{-3}),\\
\mathcal K_b(A,(k,q))&=
 \frac{\phi(k_A)\phi(k)e^{-\sqrt b\mathfrak r(q-q_A)}}
      {4\pi\sqrt\Delta\,\mathfrak r(q-q_A)}
                    +O(\phi(k)|q|^{-3}).
\end{aligned}
\tag{47.6}
$$

The subtracted time interval $(0,1)$ in each expression is exponentially small at remote output, by L (41.2); it is included in the displayed polynomial errors. Translation by bounded $q_A$ changes the leading Yukawa factor to its centered value with error $C\phi(k)|q|^{-2}$, uniformly in $b$, since $(1+\sqrt b r)e^{-\sqrt b r}$ is bounded. All product errors, integrated against $dq\,dk$, are $O(1)$: a leading triple product has degree $-3$, and replacing a Yukawa factor by its translation error adds one inverse power, while native errors add at least two. The errors are integrated as polynomial bounds, without assigning exponential decay to them. The inner region is uniformly bounded by (47.4).

In raw phase measure the change $q=\mathsf M^{1/2}(r\omega)$ gives $dq=\sqrt\Delta\,r^2dr\,d\omega$, with sphere area $4\pi$. Thus the leading outer integral is

$$
\frac{\phi_0\phi(k_A)\phi(k_B)I_3}{16\pi^2\Delta}
 \int_{R_0}^\infty e^{-2\sqrt b r}\frac{dr}{r}.
\tag{47.7}
$$

For any fixed $R_0>0$ the radial integral is $\tfrac12\log(1/b)+O(1)$: subtract the integral of $1/r$ on $[R_0,b^{-1/2}]$, then substitute $v=\sqrt b r$ in both remaining integrals; $(e^{-2v}-1)/v$ is integrable at zero and $e^{-2v}/v$ at infinity. This proves (47.3), including its raw-density constant. $\square$

**Theorem 47.2 (both full moving inputs).** At every separately fixed probe (46.2),

$$
\begin{aligned}
\|J_s^{1/2}Lx_s\|_2^2
 &=B_{\log}s^8\log(1/b)+o_{d,M}(s^8\log(1/b)),\\
B_{\log}&=\frac{j_0A_p^2\phi_0^3 I_3}{32\pi^2\Delta}>0.
\end{aligned}
\tag{47.8}
$$

Proof. The exact late scaling (35.9) and the full output change $Y=Y_s\xi$ give, by Tonelli,

$$
\|J_s^{1/2}Lx_s\|_2^2
 =j_0s^8\iint x_s(\eta)x_s(\eta')
 \mathcal I_b(Y_s\eta,Y_s\eta')d\eta\,d\eta'.
\tag{47.9}
$$

Indeed the three factors are $s^5$ from $J_s$, $(j_0s^5)^2$ from the two late kernels, and $(j_0s^7)^{-1}$ from output volume. Each input retains its complete microscopic measure; neither is restricted to an annulus or compact set.

Divide the bilinear kernel by $\log(1/b)$. Lemma 47.1 bounds it uniformly on the entire two-input space for small $s$. Since $x_s\to Vp$ in $L^1$, replacing either input by $Vp$ costs at most

$$
C\|x_s-Vp\|_1(\|x_s\|_1+\|Vp\|_1)=o(1).
\tag{47.10}
$$

For each fixed $\eta,\eta'$, the physical inputs $Y_s\eta,Y_s\eta'$ tend to $o$, so (47.3) gives the limit $\phi_0^3I_3/(32\pi^2\Delta)$. Dominated convergence against $(Vp)(\eta)(Vp)(\eta')$ is legitimate by the same global bound. Their two masses give $A_p^2$, proving (47.8). At $b=Ms^6$, the upper physical radius is $b^{-1/2}=M^{-1/2}s^{-3}$ and

$$
\log(1/b)=6\log(1/s)-\log M.
\tag{47.11}
$$

Consequently the coefficient with $\log(1/s)$ is six times the coefficient displayed with $\log(1/b)$. $\square$

## 48. The complete weighted residual

**Theorem 48.1 (full residual variance).** Keep the exact full quotient $\mathcal Q_s=\langle z_s,\mathscr K_s(h)z_s\rangle$ of (35.13), at a separately fixed probe (46.2). Then

$$
\|(\mathscr K_s(h)-\mathcal Q_s)z_s\|_2^2
 =\frac{B_{\log}}{\mu}s^8\log(1/b)
       +o_{d,M}(s^8\log(1/b)).
\tag{48.1}
$$

In addition the complete component estimates are

$$
\begin{aligned}
\|U_s^{1/2}Dx_s\|_2^2&\le Ch^2s^{-1},\\
\|F_s^{1/2}Lx_s\|_2^2&\le Cs^8,\\
\|U_s^{1/2}R y_s\|_2^2&\le Cs^{10}.
\end{aligned}
\tag{48.2}
$$

Proof. Use the exact original-domain residual (35.15), with no omitted term,

$$
e_s=-Dx_s+Lx_s+Ry_s,\qquad
(\mathscr K_s(h)-\ell_s)z_s=U_s^{1/2}e_s/\sqrt{n_s}.
\tag{48.3}
$$

The first bound of (48.2) is (35.11) and bounded $U_s$. The uniform late kernel gives $\|Lx_s\|_\infty\le Cs^5$, and raw killed mass gives $\int F_s\le CT=Cs^{-2}$, proving its second bound. The last uses (35.17), bounded $k_d(h)$ from Theorem 35.1, and the full self estimate (46.3):

$$
\|U_s^{1/2}Ry_s\|_2^2\le k_d(h)\langle y_s,Ry_s\rangle\le Cs^{10}.
\tag{48.4}
$$

As $U_s=F_s+J_s$, the square of the middle term is exactly the sum of its two weighted squares. The $J_s$ square is (47.8), while the $F_s$ square is $O(s^8)=o(s^8\log(1/b))$. The other two full weighted squares are $O(M^2s^{15})$ and $O(s^{10})$, respectively. Cauchy–Schwarz shows that every cross term among the three vectors in (48.3) is $o(s^8\log(1/b))$. This accounts for both multiplier pieces also in the mixed terms, since their sum is the full $U_s$ norm. Thus

$$
\|U_s^{1/2}e_s\|_2^2
 =B_{\log}s^8\log(1/b)+o_{d,M}(s^8\log(1/b)).
\tag{48.5}
$$

The exact quotient (35.13), (35.11), (43.3) and (46.3) give $\mathcal Q_s-\ell_s=O_{d,M}(s^5)$. For a unit vector, subtracting its exact quotient satisfies the identity

$$
\|(\mathscr K_s(h)-\mathcal Q_s)z_s\|_2^2
 =n_s^{-1}\|U_s^{1/2}e_s\|_2^2-(\mathcal Q_s-\ell_s)^2.
\tag{48.6}
$$

The subtracted square is $O(s^{10})$ and $n_s\to\mu$, proving (48.1). This is a full variance asymptotic, not a first-Born or restricted-annulus lower bound. $\square$

## 49. Positive uplift above an exact baseline and the fixed-probe consequence

**Definition 49.1 (exact baseline).** At (46.2) define the real scalar

$$
\mathcal B_s(h)=\ell_s+
 \frac{\ell_s\delta_s+\langle x_s,L^hx_s\rangle
                        -\langle x_s,Dx_s\rangle}{n_s}.
\tag{49.1}
$$

It retains the actual early scalar, moving mass and damped late quadratic, rather than assigning them evaluated coefficients.

**Theorem 49.2 (full principal uplift and enclosure).** For each separately fixed finite $M\ge M_{0,d}$,

$$
\begin{gathered}
\mathcal Q_s-\mathcal B_s(h)=O_{d,M}(s^8),\\
0<\frac{B_{\log}}{\mu C_*}
\le\liminf_{s\downarrow0}
 \frac{k_d(Ms^8)-\mathcal B_s(Ms^8)}{s^8\log(1/(Ms^6))}\\
\le\limsup_{s\downarrow0}
 \frac{k_d(Ms^8)-\mathcal B_s(Ms^8)}{s^8\log(1/(Ms^6))}<\infty.
\end{gathered}
\tag{49.2}
$$

In particular this difference is positive and of order $s^8\log(1/(Ms^6))$. Also, with exactly $\mathscr A$ from (32.6),

$$
\begin{aligned}
k_d(Ms^8)&=\ell_s+\mathscr A W_{1,d}(o)s^5+O_{d,M}(s^6),\\
s^{-5}\{k_d(Ms^8)-\ell_s-\mathscr A W_{1,d}(o)s^5\}&\longrightarrow0.
\end{aligned}
\tag{49.3}
$$

Proof. Subtract (49.1) from (35.13) exactly:

$$
\mathcal Q_s-\mathcal B_s(h)
 =\frac{-2\operatorname{Re}\langle y_s,Dx_s\rangle
       +2\operatorname{Re}\langle x_s,L^hy_s\rangle
       +\langle y_s,Ry_s\rangle}{n_s}.
\tag{49.4}
$$

The last two terms have orders $s^8,s^{10}$ by (46.3), and the remaining term has magnitude at most $Cs^5hs^{-1/2}=CMs^{25/2}$ by (35.11) and $\|y_s\|_2\le Cs^5$. This proves the first line of (49.2).

Write $v_s=\|(\mathscr K_s(h)-\mathcal Q_s)z_s\|_2^2$ and $k=k_d(h)$. Spectral positivity of the full selfadjoint compact operator gives $t^2\le kt$ for every point of its spectrum, hence

$$
v_s\le\mathcal Q_s(k-\mathcal Q_s).
\tag{49.5}
$$

The fixed compact spectral separation of Theorem 35.1 gives $k_2\le C_*-3\zeta$ and $\mathcal Q_s\to C_*$; its upper variance inequality (35.19) is

$$
0\le k-\mathcal Q_s\le v_s/(\mathcal Q_s-k_2).
\tag{49.6}
$$

Since $v_s\to0$, this also proves $k\to C_*$ at each fixed $M$, without asserting norm convergence of the reconstruction at fixed $M$. Divide (49.5)–(49.6) by $s^8\log(1/b)$ and use (48.1). The lower limit is at least $B_{\log}/(\mu C_*)$, and the upper limit is finite since $\mathcal Q_s-k_2$ stays positive. Equation (49.4) has zero normalized limit, proving the full enclosure. The two spectral inequalities do not identify an exact uplift coefficient.

For (49.3), reuse the endpoint and input estimates (43.3), which require no vanishing coefficient, and the $O(s)$ early-vector estimate in the proof of (35.5). In particular $m_s=\mu+O(s)$, $\delta_s=W_1(o)s^5+O(s^6)$, and $\ell_s=C_*+O(s)$; the last follows also from (24.13) and its isolated Riesz projection. At $b=Ms^6$,

$$
\langle x_s,L^hx_s\rangle
 =j_0A_p^2W_1(o)s^5+O_d(s^6)+O_{d,M}(s^8).
\tag{49.7}
$$

The damping scalar is $O(h)=O_M(s^8)$. The cross and self scalars have the improved orders (46.3), and (49.6) bounds the quotient-to-principal difference by $O_{d,M}(s^8\log(1/b))=o_{d,M}(s^6)$. Inserting these facts in (35.13) gives (49.3), because $(C_*+j_0A_p^2)/\mu=\mathscr A$. Every finite $M$ was fixed before its $s$ limit; no hidden uniform limit in $M$ is used. $\square$

## 50. The larger unsigned baseline and the actual-state implication

**Proposition 50.1 (remaining complete comparison).** The exact baseline has the enclosure

$$
\mathcal B_s(h)=\ell_s+
 \frac{\ell_s\delta_s+\langle x_s,L^0x_s\rangle}{n_s}
 +O_{d,M}(s^8),\qquad h=Ms^8.
\tag{50.1}
$$

Under the additional conditional identities $C_{\rm resp}=C_4=\mathfrak m_d=0$, the conclusions above and Theorem 42.2 give only

$$
k_d(Ms^8)-C_*=O_{d,M}(s^{41/8}).
\tag{50.2}
$$

The positive uplift in (49.2) therefore does not evaluate the sign of this complete difference.

Proof. The damping difference of the late quadratic is $O(s^5\sqrt b)=O_M(s^8)$ by (43.5), while $\langle x_s,Dx_s\rangle=O(h)=O_M(s^8)$. This proves (50.1). On the stated zero stratum, $Z_d+W_1(o)=0$ by the zero-stratum assumption and (32.8). Insert $\ell_s=C_*+\mathscr A Z_ds^5+O(s^{41/8})$ from (42.7) into (49.3). The two fifth-order terms cancel, giving (50.2). Neither $O(s^{41/8})$ nor the remaining $O(s^6)$ endpoint/input enclosure is $o(s^8\log(1/s))$. In particular the unresolved early scalar

$$
\ell_s-C_*=
 \frac{\langle E_s^{\rm row},u_s\rangle}{\langle G_s,u_s\rangle}
\tag{50.3}
$$

from (24.42), together with $\ell_s\delta_s/n_s$ and the full undamped late quadratic in (50.1), remains a signed joint obligation. $\square$

**Corollary 50.2 (conditional every-choice consumer).** If, in addition, eventual $k_d(Ms^8)>C_*$ is proved for every arbitrarily large separately fixed finite $M$, the original actual scale satisfies $r_s\to\infty$. Every sequence $s_n\downarrow0$ and every normalized complex actual ground-state choice on it then converges under the original unsheared observation $\mathcal U_{s_n}$ to the phase orbit of $p$, as in P Theorem 105.1.

Proof. The exact original Birman–Schwinger correspondence at positive probe compares the actual microscopic bottom of $aC_s-\chi_cU_s$ with $-ah$. The strict inequality $k_d(h)>a/\chi_c=C_*$ gives $\epsilon_c(s)<-ah$, hence $r_s>aM$. Arbitrarily large separately fixed $M$ force $r_s\to\infty$. P Theorem 105.1 then supplies the every-choice phase-orbit convergence with the original observation. The shear used in the intermediate estimates does not replace that observation. $\square$

**Definition 50.3 (mathematical scope and attribution).** The estimates in §§45–49 use no coefficient-zero identity; Proposition 50.1's final estimate additionally assumes all three vanishing coefficients, without asserting their occurrence. Corollary 50.2 has an additional strict complete-principal premise that (49.2) does not supply. No exact uplift coefficient, complete $C_*$ selecting sign, realized bounded-$r$ branch, physical spatial dimension or analytic-state preparation follows. The ambient Engel homogeneous dimension seven controls early estimates; the native three-phase tensor controls the physical late radius. These are different structures. All statements fix the original datum and each finite probe separately before $s\downarrow0$.

The Gaussian method is Coulhon–Sikora, *Gaussian heat kernel upper bounds via Phragmén–Lindelöf theorem*, [Theorem 4.1](https://arxiv.org/abs/math/0609429), with its native hypotheses already matched in P Lemma 82.2. The convolution split is E Theorem 3.1; native Gaussian and Yukawa asymptotics with both height factors are L Lemma 41.2 and Theorem 42.1. The exact quotient, bounded-product factorization, spectral variance inequality, endpoint replacement and actual-state consumer are respectively Theorem 35.1, Lemma 43.1 and P Theorem 105.1. The positive Coulomb-annulus mechanism is the same radial $dr/r$ mechanism retained in the earlier annular estimates; it is an intermediate ingredient of the full moving-input and full-residual statements here. These source-specific deductions carry no claim of worldwide novelty or new generic spectral or convolution theorem.

## 追加锚（本行以下为增补区）

## 51. Fixed physical coordinates and the moving early input

**Definition 51.1 (applicability and physical kernels).** Throughout §§51–55 fix one original datum satisfying exactly Definition 45.1. In particular retain Definition 32.1's jointly realized rational vector (32.2), the larger-interval positive-probability, coefficient, pole and bracket margins of L Definition 35.1, L Lemma 41.2, P §§76, 87–88, 97, 104–107 and E Theorem 3.1. No equality $C_{\rm resp}=0$, $C_4=0$ or $\mathfrak m_d=0$ is assumed. General geometric admission alone is insufficient. Every cutoff below is separately fixed, and every finite $M\ge M_{0,d}$ is separately fixed before $s\downarrow0$.

All physical kernels use raw $dY=dk\,dq$ on $\mathcal C=I\times\mathbb R^3$, both original Dirichlet faces and the original clock

$$
K(t;A,Y)=e^{\lambda t}p_t^B(A,Y),\qquad
G(A,Y)=\int_0^1K(t;A,Y)dt,\qquad
\Lambda(A,Y)=\int_1^\infty K(t;A,Y)dt,\quad f(Y)=\Lambda(o,Y)=W_1(Y).
\tag{51.1}
$$

The kinetic coefficient $a$ does not enter this clock. Let $\delta_s^E$ be the Engel dilation with coordinate weights $(1,1,2,3)$, and define the fixed algebraic chart

$$
\Phi=\Xi_1\circ\mathscr L_1,\qquad
\mathcal D=\Phi^{-1}\mathcal C,\qquad
r(Y)=d_E(0,\Phi^{-1}Y),\qquad
Y_s=\Phi\circ\delta_s^E.
\tag{51.2}
$$

Here $\Xi_1,\mathscr L_1$ mean the algebraic maps (2.1)–(2.2), without any requirement that $s=1$ be in the asymptotic regime. Indeed $L_1\operatorname{diag}(s,s^2,s^3)=\operatorname{diag}(s,s^2,s^3)L_s$; hence (51.2) is exactly the original sheared chart. Its absolute Jacobian is $j_0s^7$, $|\det D\Phi|=j_0$, and $r(Y_s\xi)=s\rho(\xi)$. Physical volume is $j_0$ times Engel Haar volume in this fixed chart. Restricting that volume to $\mathcal D$ only decreases upper bounds from full Engel balls.

Use the exact transported dictionary (32.4), with restriction to $\Omega_s$ and zero extension:

$$
\begin{aligned}
C_s&=s^2(\mathcal T_s\mathcal U_s)S(\mathcal T_s\mathcal U_s)^{-1},&
Q_s(t)&=e^{-tC_s},&T&=s^{-2},\\
q_s(t;\eta,\xi)&=j_0s^7K(s^2t;Y_s\eta,Y_s\xi),\\
F_s(\xi)&=j_0^{-1}\int_1^Tq_s(t;0,\xi)dt,&
H_s&=\int_0^TQ_s(t)dt,\\
J_s(\xi)&=s^5f(Y_s\xi),&U_s&=F_s+J_s.
\end{aligned}
\tag{51.2a}
$$

Take $u_s,x_s,\ell_s,\delta_s,n_s$ exactly from (45.1). In particular $H_sF_su_s=\ell_su_s$, $x_s=F_su_s$, $u_s\ge0$ and $\|u_s\|_2=1$. Here $U_s$ is a multiplier, distinct from the unsheared unitary $\mathcal U_s$. Define

$$
A_s=\int x_s(\xi)d\xi,\quad A_p=\int Vp>0,\quad
w_s(Y)=s^{-5}u_s(Y_s^{-1}Y),\quad
v_s(Y)=\frac{x_s(Y_s^{-1}Y)}{j_0s^7},\quad d\nu_s(Y)=v_s(Y)dY.
\tag{51.3}
$$

Thus $\nu_s$ is the complete physical pushforward of $x_s(\xi)d\xi$, not a probability measure. Regard it also as a measure on $\mathbb R^4$ by zero extension outside $\mathcal C$. Pointwise statements use the representative $u_s=\ell_s^{-1}H_sx_s$ defined by the heat-kernel integral and $x_s=F_su_s$ with that representative; the integral is finite at every interior output by (45.3), (45.5) and local kernel integrability.

**Lemma 51.2 (global physical domination).** For interior distinct endpoints,

$$
G(A,Y)\le C d_E(\Phi^{-1}A,\Phi^{-1}Y)^{-5}.
\tag{51.4}
$$

The kernel is continuous off the diagonal. On the whole physical output space, for $Y\ne o$,

$$
0\le w_s(Y)\le Cr(Y)^{-5},\qquad
0\le v_s(Y)\le Cs^{-7}(1+r(Y)/s)^{-10}\le Cs^3r(Y)^{-10}.
\tag{51.5}
$$

Proof. The rational denominator margins used in (45.4) compare the native control length with the ambient Engel length in the fixed chart (51.2). P Lemma 82.2 and the proof of Lemma 45.2 give the original killed Gaussian bound for $0<t\le1$, including the harmless bounded factor $e^{\lambda t}$. Integrating $Ct^{-7/2}\exp(-cd_E^2/t)$ gives (51.4), by $v=d_E^2/t$. Positive-time continuity and the same Gaussian small-time majorant give off-diagonal continuity: on a compact product away from the diagonal, the integral over $(0,\epsilon)$ tends uniformly to zero. Theorem 45.3 gives (51.5) directly after (51.2)–(51.3); for the first inequality use $s^{-5}(1+r/s)^{-5}\le r^{-5}$. The second uses the full input envelope of degree ten, not an unweighted error estimate. All kernels remain the original killed kernels. $\square$

**Theorem 51.3 (physical moving-vector and full-input limits).** For every fixed interior $Y\ne o$,

$$
w_s(Y)\longrightarrow\frac{j_0A_p}{C_*}G(o,Y),\qquad
\frac{v_s(Y)}{s^3}\longrightarrow\frac{A_p}{C_*}G(o,Y)^2.
\tag{51.6}
$$

These are pointwise limits, with global domination (51.5); they concern the auxiliary early eigenvector only.

Proof. By (35.5), $A_s\to A_p$ and $x_s\to Vp$ in $L^1$. For any bounded continuous test $g$ on the ambient physical $\mathbb R^4$, replace $x_s$ by $Vp$ in $\int g(Y_s\xi)x_s(\xi)d\xi$ with error at most $\|g\|_\infty\|x_s-Vp\|_1$. Dominated convergence on the remaining fixed input gives $A_pg(o)$. Thus $\nu_s\rightharpoonup A_p\delta_o$, with total masses converging. Exact heat scaling and the early eigen-equation give

$$
\frac{F_s(Y_s^{-1}Y)}{s^5}=\int_{s^2}^1K(t;o,Y)dt,\qquad
w_s(Y)=\frac{j_0}{\ell_s}\int_{\mathcal C}G(A,Y)d\nu_s(A).
\tag{51.7}
$$

The first identity includes the field-only $j_0^{-1}$ in the microscopic definition of $F_s$; the return kernel in the second has the factor $j_0s^5$. For fixed $Y\ne o$, the first integral tends to $G(o,Y)$ and is at most $Cr(Y)^{-5}$.

Choose $0<\epsilon<r(Y)/2$ sufficiently small that the ball about $o$ is interior. On $r(A)<\epsilon$, off-diagonal continuity gives

$$
\left|\int_{r(A)<\epsilon}[G(A,Y)-G(o,Y)]d\nu_s(A)\right|
\le A_s\sup_{r(A)<\epsilon}|G(A,Y)-G(o,Y)|.
\tag{51.8}
$$

The mass of its complement is $O_\epsilon(s^3)$ by (51.5). More strongly its whole kernel contribution is $O_{\epsilon,Y}(s^3)$, since

$$
\int_{r(A)\ge\epsilon}G(A,Y)d\nu_s(A)
\le Cs^3\int_{r(A)\ge\epsilon}r(A)^{-10}
 d_E(\Phi^{-1}A,\Phi^{-1}Y)^{-5}dA<\infty\cdot s^3.
\tag{51.9}
$$

For $r(A)>2r(Y)$ the triangle inequality gives $d_E(\Phi^{-1}A,\Phi^{-1}Y)\ge r(A)/2$. The integral is finite near $A=Y$ because the degree $-5$ singularity is locally integrable in homogeneous dimension seven; away from that point there is no singularity, and at infinity the integrand is bounded by $Cr(A)^{-15}$. First let $s\downarrow0$ and then $\epsilon\downarrow0$ in (51.7)–(51.9), using $\ell_s\to C_*$. This proves the first limit. Finally the exact identity

$$
\frac{v_s(Y)}{s^3}=\frac1{j_0}
 \frac{F_s(Y_s^{-1}Y)}{s^5}w_s(Y)
\tag{51.10}
$$

proves the second. The faces have raw measure zero, while all dominating bounds include their killed realization and every real phase. $\square$

## 52. One common weighted Taylor subtraction

**Definition 52.1 (joint polynomial and retained core).** Choose one real $\chi\in C_c^\infty(\mathcal C)$ equal to one near $o$, supported in a sufficiently small fixed interior source neighborhood. Pull smooth functions back by $\Phi$ and Taylor expand at zero. For a multi-index $\alpha$ put $|\alpha|_E=\alpha_1+\alpha_2+2\alpha_3+3\alpha_4$. Let $\mathcal T_3 f$ contain exactly the Taylor monomials with $|\alpha|_E\le3$. For $\Lambda$, retain exactly the two-endpoint monomials with $|\alpha|_E+|\gamma|_E\le3$. Set

$$
\begin{aligned}
P_\chi(Y)&=\chi(Y)\mathcal T_3f(Y),\\
\Pi_\chi(A,Y)&=\chi(A)\chi(Y)\mathcal T_3\Lambda(A,Y),\\
R_\chi(Y)&=f(Y)-P_\chi(Y),&
\mathcal R_\chi(A,Y)&=\Lambda(A,Y)-\Pi_\chi(A,Y),\\
I_\chi&=\int_{\mathcal C}R_\chi(Y)G(o,Y)^2dY,\\
\delta_{\chi,s}&=s^5\int P_\chi(Y_s\xi)u_s(\xi)^2d\xi,\\
Q_{\chi,s}&=j_0s^5\iint\Pi_\chi(Y_s\eta,Y_s\xi)x_s(\eta)x_s(\xi)d\eta d\xi,\\
\mathcal C_{\chi,s}&=\ell_s+\frac{\ell_s\delta_{\chi,s}+Q_{\chi,s}}{n_s}.
\end{aligned}
\tag{52.1}
$$

The two endpoint degrees are summed before truncation. In particular this is not a separate degree-three truncation at each endpoint. These signed retained scalars do not change any native operator or multiplier.

**Lemma 52.2 (remainders and absolute convergence).** The kernels in (52.1) satisfy

$$
\Pi_\chi(o,Y)=\Pi_\chi(Y,o)=P_\chi(Y),\quad
R_\chi(Y)=O(r(Y)^4),\quad
\mathcal R_\chi(A,Y)=O((r(A)+r(Y))^4)
\tag{52.2}
$$

near the source and source pair respectively, and $\mathcal R_\chi$ is globally bounded. The integral defining $I_\chi$ is absolutely convergent.

Proof. Lemma 43.1 gives boundedness of $\Lambda$ and joint smoothness near $(o,o)$. Its symmetry gives both endpoint restrictions in (52.2), since setting one endpoint to zero in the joint polynomial leaves exactly $\mathcal T_3f$. Ordinary Taylor through Euclidean degree three has remainder bounded by the fourth power of the Euclidean distance. In a small Engel ball, each coordinate of weight $j$ is $O(r^j)$. Every discarded monomial has weighted degree at least four, and the ordinary remainder is also $O(r^4)$. Apply the same argument in the endpoint product, with radius $r(A)+r(Y)$. The cutoffs are one there and the polynomial-cutoff products are compactly supported and bounded, proving the other assertions. Near $o$, (51.4) bounds the absolute integrand of $I_\chi$ by $Cr^{-6}$; outside a fixed source ball it is bounded by $Cr^{-10}$, using bounded $f,P_\chi$. The respective radial upper integrals are $C\int_0^\epsilon 1\,dr$ and $C\int_\epsilon^\infty r^{-4}dr$. These include the complete output and all remote phases. $\square$

**Theorem 52.3 (joint moving mass and both undamped inputs).** Let $L^0$ denote the undamped late kernel (35.9) at $h=0$, used in its finite quadratic pairing against $x_s\in L^1$. Its kernel is bounded by $Cj_0s^5$ by L Lemma 41.2; no bounded inverse on all of $L^2$ is asserted. Then

$$
\begin{aligned}
s^{-8}(\delta_s-\delta_{\chi,s})
 &\longrightarrow\frac{j_0A_p^2}{C_*^2}I_\chi,\\
s^{-8}(\langle x_s,L^0x_s\rangle-Q_{\chi,s})
 &\longrightarrow\frac{2j_0A_p^2}{C_*}I_\chi,\\
\frac{\ell_s(\delta_s-\delta_{\chi,s})+
 \langle x_s,L^0x_s\rangle-Q_{\chi,s}}{n_s}
 &=c_\chi s^8+o_{d,\chi}(s^8),\qquad
c_\chi=\frac{3j_0A_p^2}{\mu C_*}I_\chi.
\end{aligned}
\tag{52.3}
$$

Proof. Change the complete output variable in the mass scalar. The exact equality is

$$
s^{-8}(\delta_s-\delta_{\chi,s})
 =j_0^{-1}\int_{\mathcal C}R_\chi(Y)w_s(Y)^2dY.
\tag{52.4}
$$

The global majorant $C|R_\chi|r^{-10}$ is integrable by the proof of Lemma 52.2. Theorem 51.3 and dominated convergence prove the first line of (52.3).

For the late scalar use its exact full-product kernel scaling:

$$
\langle x_s,L^0x_s\rangle-Q_{\chi,s}
 =j_0s^5\iint_{\mathcal C^2}\mathcal R_\chi(A,Y)d\nu_s(A)d\nu_s(Y).
\tag{52.5}
$$

Fix a small $\epsilon>0$ and split each endpoint into $r<\epsilon$ and $r\ge\epsilon$. The two-outer piece is $O_\epsilon(s^6)$, since the kernel is bounded and each exterior mass is $O_\epsilon(s^3)$. On the $A$-outer, $Y$-inner piece, for each fixed exterior $A$,

$$
\int_{r(Y)<\epsilon}\mathcal R_\chi(A,Y)d\nu_s(Y)
 \longrightarrow A_p\mathcal R_\chi(A,o)=A_pR_\chi(A).
\tag{52.6}
$$

Continuity at $Y=o$ follows from positive-time heat continuity and the integrable large-time bound of L Lemma 41.2; the compact cutoff adds no difficulty. Concentration gives (52.6) by first restricting to an arbitrarily small ball about $o$; the intervening annulus has $O(s^3)$ mass. The integrand after division by $s^3$ is dominated on the exterior by $Cr(A)^{-10}$, uniformly in its inner integral. Therefore (51.6) and dominated convergence make this piece divided by $s^3$ tend to

$$
\frac{A_p^2}{C_*}\int_{r(A)\ge\epsilon}R_\chi(A)G(o,A)^2dA.
\tag{52.7}
$$

The other single-outer piece gives the identical limit by symmetry. The two-inner piece is bounded, using (52.2), by a constant times $A_s\int_{r<\epsilon}r^4d\nu_s$. Homogeneous ball integration and (51.5) give the quantitative bound

$$
\begin{aligned}
\int_{r<\epsilon}r^4d\nu_s
 &\le Cs^{-7}\int_0^\epsilon r^{10}(1+r/s)^{-10}dr
 \le Cs^3\epsilon,\\
 s^{-3}\left|\iint_{r(A),r(Y)<\epsilon}\mathcal R_\chi(A,Y)d\nu_s(A)d\nu_s(Y)\right|
 &\le C\epsilon.
\end{aligned}
\tag{52.8}
$$

This bound follows also shell by shell and requires no finite fourth absolute moment of $x_s$. The omitted inner portion of the integral in (52.7) is $O(\epsilon)$ by Lemma 52.2. Let $s\downarrow0$ at fixed $\epsilon$ and then $\epsilon\downarrow0$. Equations (52.5)–(52.8) prove the second line of (52.3). Finally $\ell_s\to C_*$ and $n_s\to\mu>0$; the mass contribution supplies one copy and the two moving late endpoints supply two copies of the same finite integral. This proves the factor three. $\square$

## 53. Exact separately fixed spectral-probe costs

**Theorem 53.1 (early damping and the late square-root coefficient).** Fix any finite $M\ge M_{0,d}$ and put $h=Ms^8$, $b=h/s^2=Ms^6$, $D=H_s-H^h$. Distinguish $M$ from the original positive phase tensor $\mathsf M=\int_I\phi(k)^2c_\kappa(k)c_\kappa(k)^{\mathsf T}dk$. Then

$$
\begin{aligned}
\langle x_s,Dx_s\rangle&=C_*^2Ms^8+o_{d,M}(s^8),\\
\langle x_s,(L^0-L^h)x_s\rangle
 &=\frac{j_0A_p^2\phi(k_0)^2}{4\pi\sqrt{\det\mathsf M}}\sqrt M\,s^8+o_{d,M}(s^8).
\end{aligned}
\tag{53.1}
$$

Proof. Reuse the input-specific damping argument (36.4)–(36.6). Its hypotheses are (35.5), strong fixed-time heat convergence, and the early Gaussian bounds, all available at Definition 45.1 scope without the vanishing identities used for Theorem 36.1's other conclusions. In particular

$$
\frac{\langle x_s,Dx_s\rangle}{h}
 =\int_0^{s^{-2}}\frac{1-e^{-ht}}h\langle x_s,Q_s(t)x_s\rangle dt
 \longrightarrow\int_0^\infty t\langle Vp,P_tVp\rangle dt=C_*^2.
\tag{53.2}
$$

The integrand, zero extended in time, is dominated by $Ct$ below one and $Ct^{-5/2}$ above one. The spectral-calculus equality is $\|G_0(Vp)\|_2^2=C_*^2$, since $G_0(Vp)=C_*p$ and $\|p\|_2=1$. This is the existing early damping coefficient on its existing input, applied at the present fixed probe.

For the late difference define

$$
J_b(A,Y)=\int_1^\infty(1-e^{-bt})K(t;A,Y)dt.
\tag{53.3}
$$

L Lemma 41.2 gives $0\le J_b\le C\sqrt b$ globally. Its integrable band error contributes at most $C\int_1^\infty\min(bt,1)t^{-5/2}dt=O(b)$. Uniformly on fixed compact endpoint sets, replacing the Gaussian phase displacement by zero costs the same $O(b)$, since $|e^{-|q_A-q_Y|_{\mathsf M}^2/(4t)}-1|\le C/t$. The remaining time integral is

$$
\begin{aligned}
\frac1{\sqrt b}\int_1^\infty(1-e^{-bt})t^{-3/2}dt
 &\longrightarrow\int_0^\infty(1-e^{-v})v^{-3/2}dv\\
 &=2\int_0^\infty e^{-v}v^{-1/2}dv=2\sqrt\pi.
\end{aligned}
\tag{53.4}
$$

The equality follows by integration by parts, whose two boundary terms vanish, and the Gaussian integral. Consequently

$$
\frac{J_b(A,Y)}{\sqrt b}\longrightarrow
 \frac{\phi(k_A)\phi(k_Y)}{4\pi\sqrt{\det\mathsf M}}
\tag{53.5}
$$

uniformly on fixed compact endpoint sets. This evaluates the constant in the square-root order already supplied by Lemma 43.1.

The exact late difference in microscopic variables is

$$
\langle x_s,(L^0-L^h)x_s\rangle
 =j_0s^5\iint J_b(Y_s\eta,Y_s\xi)x_s(\eta)x_s(\xi)d\eta d\xi.
\tag{53.6}
$$

After division by $j_0s^5\sqrt b$, the global bound above permits replacement of both inputs by $Vp$ with error bounded by $C\|x_s-Vp\|_1(\|x_s\|_1+\|Vp\|_1)=o(1)$. For each fixed microscopic pair, its physical endpoints tend to $(o,o)$ and lie in one fixed interior compact set. Thus (53.5) applies with limiting height factor $\phi(k_0)^2$. Full-product dominated convergence against $(Vp)(\eta)(Vp)(\xi)$ gives the coefficient in (53.1), since $s^5\sqrt b=\sqrt M\,s^8$. Neither endpoint has been held fixed while discarding the other moving input. $\square$

## 54. Complete subtracted baseline and cutoff compensation

**Theorem 54.1 (exact fixed-$M$ baseline expansion).** Set

$$
\beta=\frac{C_*^2}{\mu},\qquad
c_{\rm tail}=\frac{j_0A_p^2\phi(k_0)^2}{4\pi\mu\sqrt{\det\mathsf M}}.
\tag{54.1}
$$

For every separately fixed finite $M\ge M_{0,d}$, the exact baseline (49.1) satisfies

$$
\mathcal B_s(Ms^8)=\mathcal C_{\chi,s}
 +s^8\bigl(c_\chi-\beta M-c_{\rm tail}\sqrt M\bigr)
 +o_{d,M,\chi}(s^8).
\tag{54.2}
$$

Proof. The baseline definition, with no discarded term, is

$$
\mathcal B_s(h)=\ell_s+
 \frac{\ell_s\delta_s+\langle x_s,L^hx_s\rangle-\langle x_s,Dx_s\rangle}{n_s}.
\tag{54.3}
$$

Subtract $\mathcal C_{\chi,s}$, insert $L^h=L^0-(L^0-L^h)$, and apply (52.3) and (53.1), with $n_s\to\mu$. This proves (54.2). Every probe constant and cutoff was fixed first; the remainder is not asserted uniform for $M\to\infty$, a varying $M(s)$, moving faces or varying cutoffs. $\square$

**Proposition 54.2 (compensating cutoff dependence).** For any two allowed fixed cutoffs,

$$
\mathcal C_{\chi_2,s}-\mathcal C_{\chi_1,s}
 =-\frac{3j_0A_p^2}{\mu C_*}(I_{\chi_2}-I_{\chi_1})s^8+o_{d,\chi_1,\chi_2}(s^8).
\tag{54.4}
$$

There are allowed cutoffs with $I_{\chi_2}<I_{\chi_1}$; hence the isolated $I_\chi$ has cutoff dependence and is not a source-invariant selecting coefficient.

Proof. Subtract the two expansions of the same undamped quantity
$\ell_s+(\ell_s\delta_s+\langle x_s,L^0x_s\rangle)/n_s$ supplied by (52.3). This gives (54.4) directly, without any probe remainder. Since $f(o)>0$, continuity makes $\mathcal T_3f>0$ in a sufficiently small source ball. Choose $\chi_1$ supported in that ball and equal to one on a smaller ball, and choose a nonzero nonnegative smooth bump $\eta$ supported off $o$ in a still smaller interior annulus. Put $\chi_2=\chi_1+\eta$, also supported in the first ball. Both are allowed, and

$$
I_{\chi_2}-I_{\chi_1}
 =-\int_{\mathcal C}\eta(Y)\mathcal T_3f(Y)G(o,Y)^2dY<0.
\tag{54.5}
$$

Strict positivity of the original killed heat makes $G(o,Y)>0$ on this annulus. The integral is finite because its support avoids $o$. The opposite core change in (54.4) compensates this change exactly to the displayed order in the full baseline. $\square$

## 55. Applicability, retained core and existing actual-state consumer

**Definition 55.1 (full complex domains and the unsigned core).** The generators underlying the heat and return kernels above are the original Friedrichs realizations. Their complex form fibres are $H_0^1(I)$ with underlying raw $L^2$ membership and the full finite frequency integral

$$
\int_{\mathbb R^3}\int_I
 \bigl(\varepsilon^2|\partial_k\widehat\psi|^2+
 |\eta\cdot c_\kappa|^2|\widehat\psi|^2\bigr)dk\,d\eta<\infty.
\tag{55.1}
$$

Their operator fibres are $H^2(I)\cap H_0^1(I)$ with
$\int_{\mathbb R^3}\|B_\eta\widehat\psi(\cdot,\eta)\|_2^2d\eta<\infty$.
These are exactly (1.5), transported by $\mathcal T_s\mathcal U_s$ for intermediate sheared calculations. No reality, parity, ordinary phase-$H^1$, or finite-rank condition is imposed on actual states. Positivity is used for heat and the auxiliary $u_s$; (51.6) is not an actual ground-state profile theorem. The observation for every normalized complex actual choice remains the original unsheared $\mathcal U_s$.

Equation (54.2) evaluates a complete nonlocal part of the baseline while retaining $\mathcal C_{\chi,s}$ exactly. It is neither an expansion of $\mathcal C_{\chi,s}-C_*$ nor of $k_d(Ms^8)-C_*$. In particular (50.3)'s early-row projection and the moving local moments in (52.1) remain unsigned jointly. Even on the additional conditional stratum $C_{\rm resp}=C_4=\mathfrak m_d=0$, the owned $O(s^{41/8})$ enclosure (50.2) is larger than $s^8\log(1/s)$. Thus the positive full-residual uplift of Theorem 49.2 does not acquire a complete selecting sign from (54.2). No occurrence or exclusion of that stratum is asserted.

The existing sufficient route is the exact baseline (49.1), the full principal uplift (49.2), and Corollary 50.2/P Theorem 105.1. A further eventual strict FULL inequality $k_d(Ms^8)>C_*$ for arbitrarily large separately fixed finite $M$ would force $r_s\to\infty$ and the stated every-choice phase-orbit convergence. This is a sufficient implication, not a necessary condition or an inequality supplied by §§51–54. No actual branch classification, exact principal uplift coefficient, physical spatial dimension or analytic-state preparation follows here.

**Definition 55.2 (mathematical attribution).** The convergence of the early mode and its input is (35.5); the early damping coefficient is (36.4)–(36.6); late smoothness and square-root order are Lemma 43.1; full spatial envelopes are Theorem 45.3. Their uses above retain their original hypotheses. The physical convolution/concentration split follows the method of E Theorem 3.1, with the complete moving output and both moving inputs kept in (51.9) and (52.5)–(52.8). The Gaussian bound is Coulhon–Sikora, *Gaussian heat kernel upper bounds via Phragmén–Lindelöf theorem*, [Theorem 4.1](https://arxiv.org/abs/math/0609429), through the native hypothesis correspondence in P Lemma 82.2 and Lemma 45.2. L Lemma 41.2 and Theorem 42.1 supply the original band error, Gaussian and Yukawa normalization with both height factors. Sections 46–49 supply the already established mass/cross/self orders and full logarithmic residual uplift; §§51–54 retain the physical density limits, common joint subtraction, its factor three and evaluated fixed-probe constant. The actual-state implication is the existing Corollary 50.2/P Theorem 105.1. These are source-specific deductions by Taylor subtraction and dominated convergence, with no new generic theorem or worldwide novelty claim.

## 追加锚（本行以下为增补区）
