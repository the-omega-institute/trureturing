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
