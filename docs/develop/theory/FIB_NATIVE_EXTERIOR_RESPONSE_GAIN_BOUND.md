# Native exterior response gain bound

The improvement obtainable from the entire class of exterior corrections to the canonical height projection has sharp power $R^{-3}$. Its uniform upper bound has an explicit constant determined by the same source and critical mode. Arbitrary sums, overlapping supports, complex coefficients and even components satisfy the bound. These are ordinary conditional mathematical results under the analytic antecedents specified below. They do not determine either absolute canonical sign or the original every-ground-state decision at response zero.

Write P for [Native full-state weak binding](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md), through §108; R for [Native exact-critical energy response and scale alternatives](FIB_NATIVE_EXACT_CRITICAL_ENERGY_RESPONSE_AND_SCALE_ALTERNATIVES.md), through §15; N for *Strict nonaffine response at the native critical scale*; A for [Actual critical solvability and conditional microscopic disappearance](FIB_NATIVE_ACTUAL_CRITICAL_SOLVABILITY_AND_MICROSCOPIC_DISAPPEARANCE.md), through §16; H for *Native critical height projection and cutoff overlap bounds*; and E for *Native entire-height response escape*. Their stated results retain their supplied conditional scopes. E already supplies strong tails, the limiting height slope, a positive residual beyond the entire height subspace and a lower witness. H already supplies the entire height projection and its decomposition. The additional content here is the upper bound uniform over the whole exterior class, its explicit source constant, and its combination with the credited lower witness to identify the sharp power.

## 1. The unchanged original family and its complete domains

**Definition 1.1 (fixed admitted native data).** Fix one arbitrary original admitted signed $\kappa\ne0$, $H$, $I=(l,u)$, interior $k_0\in I$, and $a,\varepsilon>0$. Retain every original probability, interval and denominator condition. In particular $k-\alpha_\kappa$ has a positive margin on $\overline I$. Put

$$
\begin{aligned}
\alpha_\kappa&=\kappa+\kappa^2/H,&d_0&=k_0-\alpha_\kappa>0,&\nu&=\varepsilon/d_0,\\
L_I&=u-l,&\lambda&=\varepsilon^2\pi^2/L_I^2,&
\phi(k)&=\sqrt{2/L_I}\sin\bigl(\pi(k-l)/L_I\bigr),\\
c_j&=c_\kappa^{(j)}(k_0)\quad(j=0,1,2),&
j_0&=\varepsilon^4|\det(c_0,c_1,c_2)|>0.
\end{aligned}
\tag{1.1}
$$

The full original rational vector $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$ satisfies exactly

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

The third component is exactly $b_0+h b_1+h^2b_2/[2(1+h/d_0)]$, where these are its original jets. None of the vector components, jets or source constants is independently selectable. Every datum is fixed before its native limit.

On $\mathcal C=I\times\mathbb R^3$, $q=(\theta,v,x)$, use raw measure $dY=dk\,dq$ and the complex Hilbert space $L^2(dY)$. Both actual height faces are Dirichlet. Define

$$
B=-\varepsilon^2\partial_k^2-(c_\kappa(k)\cdot\partial_q)^2,
\qquad S=B-\lambda\ge0.
\tag{1.3}
$$

With unitary phase Fourier factor $(2\pi)^{-3/2}$ and $B_\eta=-\varepsilon^2\partial_k^2+|\eta\cdot c_\kappa|^2$, the entire domains, including underlying $L^2$ membership, are

$$
\begin{aligned}
\mathcal Q
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H_0^1(I)\text{ a.e.},\quad
 \int_{\mathbb R^3}\!\int_I
 (\varepsilon^2|\partial_k\widehat\psi|^2+
 |\eta\cdot c_\kappa|^2|\widehat\psi|^2)dk\,d\eta<\infty\right\},\\
D(S)=D(B)
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H^2(I)\cap H_0^1(I)\text{ a.e.},\quad
 \int_{\mathbb R^3}\|B_\eta\widehat\psi(\cdot,\eta)\|_{L^2(I)}^2d\eta<\infty\right\}.
\end{aligned}
\tag{1.4}
$$

Thus $\mathcal Q=D(S^{1/2})=D(B^{1/2})$. Every real phase frequency and every complex competitor in these domains remains allowed. No ordinary phase $H^1$, reality, parity or product restriction is imposed on native states.

**Definition 1.2 (raw source, clock and actual units).** For the killed heat kernel $p_t^B$ relative to raw measure and pole $o=(k_0,0)$, retain

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

The raw and $\phi$-weighted source charges differ. Neither is divided by a survival probability. The field clock is $B$, independently of $a$. P Propositions 70.2 and 75.2 supply, separately at each positive $g,\tau$, boundedness of the multiplier, operator domain exactly $D(S)$ for $aS-gW_\tau$, essential spectrum $[0,\infty)$ and a finite negative attained bottom. This supplies no uniform bound at zero cutoff.

The original actual path and units remain

$$
\tau=s^2,\quad g_s=\chi_cs^3,\quad E_s=E_{s^2}(\chi_cs^3),\quad
\epsilon_c(s)=s^2E_s<0,\quad r_s=-\epsilon_c(s)/s^8=-E_s/s^6>0.
\tag{1.6}
$$

Actual-state statements mean every prescribed sequence $s_n\downarrow0$ and every choice of actual normalized complex ground states $\psi_{s_n}\in D(S)$.

**Definition 1.3 (exact microscopic correspondence).** For $\xi=(r,y,z,w)$ put

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

The raw Jacobian is $j_0s^7$ and $\mathcal U_s$ is unitary. If $A_s$ is the Friedrichs operator of $b_s[F]=\|XF\|_2^2+\|Y_sF\|_2^2$, then

$$
\begin{aligned}
D(A_s)&=\mathcal U_sD(S),&
C_s&=A_s-\lambda s^2=s^2\mathcal U_sS\mathcal U_s^{-1}\ge0,\\
q_s^c[F]&=a b_s[F]-\chi_c\int U_s|F|^2-a\lambda s^2\|F\|_2^2,&
q_s^c[\mathcal U_s\psi]&=s^2\mathfrak e_{g_s,s^2}[\psi].
\end{aligned}
\tag{1.8}
$$

With $\mathbf z=(y,z,w)$ set

$$
L_s=\begin{pmatrix}1&\beta_s&0\\0&1&2\beta_s\\0&0&1\end{pmatrix},\quad
\mathscr L_s(r,\mathbf z)=(r,L_s\mathbf z),\quad
\mathcal T_sF=F\circ\mathscr L_s,\quad
Y=\partial_y+r\partial_z+\tfrac12r^2\partial_w.
\tag{1.9}
$$

P §97 gives the exact closed-form identity

$$
b_s[\mathcal T_s^{-1}f]
 =\int_{\Omega_s}\bigl(|Xf|^2+(1+\beta_sr)^{-2}|Yf|^2\bigr)d\xi.
\tag{1.10}
$$

The determinant-one shear fixes the source and both moving Dirichlet faces; its denominator is positive on the entire actual interval. Comparisons on $\mathbb R^4$ use zero extension. The exact heat and source factors are

$$
\begin{aligned}
P_s(t;\eta,\xi)&=j_0s^7p_{s^2t}^B(\Xi_s\eta,\Xi_s\xi),\\
U_s&=j_0^{-1}\int_1^\infty e^{\lambda s^2t}P_s(t;0,\cdot)dt,&
(A_s-\lambda s^2)U_s&=s^7\rho_{s^2}\circ\Xi_s.
\end{aligned}
\tag{1.11}
$$

P supplies $j_0s^7\rho_{s^2}\circ\Xi_s\to k_1$ in $L^1$ and locally uniformly, with canonical heat $k_t$ defined below. Its limiting Lebesgue source mass is $1/j_0$, corresponding to unit native raw-source mass. Neither the amplitude Jacobian nor either source charge has been suppressed.

## 2. Conditional canonical data and every complete coefficient

**Definition 2.1 (heat, mode and horizontal energy).** Use the Engel product, dilation and Haar measure

$$
\begin{aligned}
(r,y,z,w)(r',y',z',w')
 &=(r+r',y+y',z+z'+ry',w+w'+rz'+r^2y'/2),\\
\delta_R(r,y,z,w)&=(Rr,Ry,R^2z,R^3w),&d\xi&=dr\,dy\,dz\,dw.
\end{aligned}
\tag{2.1}
$$

Its homogeneous dimension is seven. Let $b[u]=\|Xu\|_2^2+\|Yu\|_2^2$, let $\mathcal Q_E$ be the complex compact smooth core closure in $\|u\|_2^2+b[u]$, and let $\mathcal E=-X^2-Y^2$ be its Friedrichs operator. P §§82–88 supply conservative, symmetric, positive continuous heat $P_t=e^{-t\mathcal E}$, $k_t(\xi)=p_E(t;0,\xi)$, a proper continuous homogeneous control distance $d$, and

$$
\begin{gathered}
p_E(t;\eta,\xi)\le Ct^{-7/2}e^{-c d(\eta,\xi)^2/t},\quad
N=\max(|r|,|y|,|z|^{1/2},|w|^{1/3}),\quad d(0,\xi)\ge cN(\xi),\\
V=j_0^{-1}\int_1^\infty k_tdt>0,\quad
\mathcal EV=j_0^{-1}k_1,\quad V\le C(1+N)^{-5},\\
C_*=\sup_{0\ne u\in\mathcal Q_E}\frac{\int V|u|^2}{b[u]}\in(0,\infty),\quad
\chi=\chi_c=a/C_*,\quad\gamma=\chi/a,\\
h_0[u]=b[u]-\gamma\int V|u|^2\ge0,\quad h=a h_0,\quad
p=\Phi_c>0,\quad\|p\|_2=1,\quad p\in D(\mathcal E),\\
\mathcal Ep=\gamma Vp,\quad\ker(a\mathcal E-\chi V)=\mathbb Cp,\quad
p=\gamma\int_0^\infty P_t(Vp)dt\quad\text{in }L^2.
\end{gathered}
\tag{2.2}
$$

Haar balls have volume $v_d R^7$. Smoothness, hypoellipticity, compact zero-energy reconstruction on the specified multiplier right sides, local form compactness, native supported-strip approximation and complete native heat/field tail assertions retain exactly their supplied conditional scopes. In particular a local positive-time heat limit is not used as an infinite-time interchange. No external heat or localization supplier is newly authenticated here.

P §106 supplies

$$
rp\in\mathcal Q_E,\quad h_0[rp]=1,\quad
\int r^2(p^2+|Xp|^2+|Yp|^2)d\xi<\infty,\quad
\sigma(r,y,z,w)=(-r,y,-z,w),\quad p\circ\sigma=p,\quad V\circ\sigma=V.
\tag{2.3}
$$

The involution reverses $X$ and preserves $Y$. R §§4–5 supply the potential form bound and compact horizontal-energy gap

$$
\int V|u|^2\le C_*b[u],\qquad
h_0[v]\ge\theta b[v]\quad\text{if }b(p,v)=0,\qquad\theta>0.
\tag{2.4}
$$

Polarized forms are conjugate linear in their first argument. Let $\dot{\mathcal H}_-$ be the completion of the real $\sigma$-odd compact smooth core in $\sqrt b$. On it $\theta b\le h_0\le b$. The real response functional and its unique Riesz representative are

$$
\mathcal L(u)=\ell(u)/a=2\int r(Yp)(Yu)+\gamma\int V_1pu,
\quad h_0(\Psi,u)=\mathcal L(u),\quad D_{\rm resp}=a h_0[\Psi].
\tag{2.5}
$$

The functional is extended complex linearly when needed. The homogeneous completion gives local representatives and global horizontal derivative vectors, using (2.4) and the positive minimum of $V$ on compact sets. No global $L^2$ or native membership of $\Psi$ is assumed. The gap is in horizontal energy, with no positive $L^2$ spectral gap or inverse on all $L^2$.

**Definition 2.2 (one source and all second-order terms).** On one height bridge $H_v$ with generator $\partial_r^2$, from zero to $r$ in time $t$, define

$$
\begin{aligned}
u(h)&=(1,h,h^2/2),&M_j&=\int_0^tH_v^j u(H_v)u(H_v)^{\mathsf T}dv\quad(j=0,1,2),\\
h_t(r)&=(4\pi t)^{-1/2}e^{-r^2/(4t)},&
\gamma_M(\mathbf z)&=(4\pi)^{-3/2}(\det M)^{-1/2}e^{-\mathbf z^{\mathsf T}M^{-1}\mathbf z/4},\\
p_1(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[-2D\gamma_{M_0}(\mathbf z)[M_1]],\\
p_2(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[
3D\gamma_{M_0}(\mathbf z)[M_2]+2D^2\gamma_{M_0}(\mathbf z)[M_1,M_1]],\\
V_j&=j_0^{-1}\int_1^\infty p_j(t;\cdot)dt\quad(j=1,2),&
V_{\rm t}&=j_0^{-1}\int_1^\infty t k_tdt>0.
\end{aligned}
\tag{2.6}
$$

Here $u(h)$ is the vector in the first line; $D\gamma$ differentiates the positive matrix at fixed phases. All matrices come from this same bridge. P §107 supplies absolute convergence, odd $V_1$, even $V_2,V_{\rm t}$, and the full-space expansion

$$
\begin{gathered}
\widetilde U_s:=U_s\circ\mathscr L_s
 =V+\beta_sV_1+\beta_s^2V_2+\lambda s^2V_{\rm t}+\mathcal R_s,
\quad\|\mathcal R_s\|_\infty\le Cs^{5/2},\\
|V_1|\le C(1+|r|)^{-4},\qquad |V_2|+V_{\rm t}\le C(1+|r|)^{-3}.
\end{gathered}
\tag{2.7}
$$

It retains every real phase, both moving faces, zero extension and the original infinite-time field. R supplies $V_j^2\le K_jV$, $V_{\rm t}^2\le K_{\rm t}V$, and their homogeneous multiplier bounds, including $\int V^{1/2}|u|^2\le\Gamma b[u]$. These ensure continuity of the coefficient pairings. No field clock contains $a$.

Write the jointly realized finite numbers and complete coefficients as

$$
\begin{aligned}
A&=\int r^2|Yp|^2,&B_1&=\int rV_1p^2,&C_2&=\int V_2p^2,&T&=\int V_{\rm t}p^2>0,\\
t_0&=2A+\gamma B_1,&K_{\rm base}&=3aA-\chi C_2,&D_{\rm clock}&=a+\chi T,\\
C_{\rm resp}&=\nu^2(K_{\rm base}-D_{\rm resp})-\lambda D_{\rm clock},\\
C_{108}&=\nu^2\{a(1-A)-\chi(C_2+2B_1)\}-\lambda(a+\chi T),\\
G_{\rm resp}&=3A-\gamma C_2-D_{\rm resp}/a,&G_{108}&=1-A-\gamma(C_2+2B_1),\\
\overline D&=1+\gamma T,&\mathscr R&=\lambda/\nu^2=\pi^2d_0^2/L_I^2>0,\\
\frac{C_X}{a\nu^2}&=G_X-\mathscr R\overline D\quad(X={\rm resp},108).
\end{aligned}
\tag{2.8}
$$

Thus $A=A_2$, $C_2+2B_1=J_2$ and $T=J_{\rm t}$ of P §108. Both the field-clock term and original threshold subtraction remain present. They cannot be discarded to sign a complete coefficient.

## 3. The height projection used as the comparison point

**Proposition 3.1 (credited projection and its local derivative meaning).** Define

$$
\begin{aligned}
\rho(r)&=\int p(r,\mathbf z)^2d\mathbf z,&m_Y(r)&=\int|Yp(r,\mathbf z)|^2d\mathbf z,\\
v_1(r)&=\int V_1(r,\mathbf z)p(r,\mathbf z)^2d\mathbf z,&
f_h(r)&=2r m_Y(r)+\gamma v_1(r),\\
J(r)&=\int_r^\infty f_h(t)dt,&q_*(r)&=J(r)/\rho(r),\\
I_h&=\int_{\mathbb R}J^2/\rho,&F_*(r)&=\int_0^r q_*(t)dt.
\end{aligned}
\tag{3.1}
$$

H supplies $I_h<\infty$ and the $h_0$-orthogonal projection $U_h$ of $\Psi$ onto the entire closed height subspace

$$
\mathcal H_h=\overline{\{pF:F\in C_c^\infty(\mathbb R;\mathbb R)_{\rm odd}\}}^{\,h_0}.
\tag{3.2}
$$

It has local representative $pF_*$, with

$$
\begin{gathered}
h_0[U_h]=\mathcal L(U_h)=I_h,\qquad
\delta_h=h_0[\Psi-U_h]\ge0,\qquad D_{\rm resp}/a=I_h+\delta_h,\\
G_{\rm resp}=3A-\gamma C_2-I_h-\delta_h,\qquad
XU_h=F_*Xp+p q_*,\quad YU_h=F_*Yp.
\end{gathered}
\tag{3.3}
$$

The weight $\rho$ is even, continuous, integrates to one and has a positive minimum on compact height intervals. The functions $J,q_*$ are even and continuous; $F_*$ is odd and locally absolutely continuous. These are homogeneous/local assertions and assume no global $L^2$ or native-domain representative for the projection.

Proof and correspondence. The following checks specify the H ingredients used here. Since $p,Xp\in L^2$, $p$ is a Hilbert-valued $H^1$ function of height, so $\rho$ is continuous and $\rho'=2\int pXp$ is integrable. The positive bounded-potential semigroup gives $p\ge P_t p$ for $t>0$ for the operator $\mathcal E-\gamma V$. Restrict its input to a compact set with positive integral of $p$ and its output to a compact height interval times a fixed compact phase box. Positivity and continuity of the heat kernel give a uniform positive lower bound there. Continuity of $\rho$ extends the resulting lower bound to every height in the interval. Also

$$
(B-A)^2\le\left(\int_A^B\rho\right)\left(\int_A^B\rho^{-1}\right)
\le\int_A^B\rho^{-1}.
\tag{3.4}
$$

Thus the reciprocal-weight integral diverges on each unbounded half-line. Parity gives even $m_Y$, odd $v_1$ and odd $f_h$. The weighted mode and bounded $V_1$ give $f_h,rf_h\in L^1$. Therefore $J$ is even, locally absolutely continuous, tends to zero at both infinities, is integrable, and $\int J=\int rf_h=t_0$.

For odd compact smooth height functions $F,G$, the critical weak equation tested with $F^2p$ and polarized gives

$$
h_0(pF,pG)=\int\rho F'G',\qquad
\mathcal L(pF)=\int f_hF=\int JF'.
\tag{3.5}
$$

All tests preserve the canonical form domain by the horizontal product rule. Differentiation of odd compact height functions has dense range in $L^2_{\rm even}(\rho dr)$: if an even $q$ is orthogonal to every $F'$, then the even locally integrable distribution $\rho q$ has zero derivative. Odd tests give this from the orthogonality, and even tests give it by parity. Hence $\rho q$ is constant. A nonzero constant contradicts (3.4) and $\int\rho q^2<\infty$. This proves the density and the onto isometry after completion.

Continuity of $\mathcal L$ on $\dot{\mathcal H}_-$ makes $q\mapsto\int Jq$ a bounded functional on this entire weighted derivative space. If $\widetilde q$ is its Riesz representative, the same distributional argument gives $\rho\widetilde q-J=c$. Since $J\to0$ at both ends, a nonzero $c$ would again violate the divergent reciprocal-weight tails. Thus $\widetilde q=J/\rho$, proving the finite quadrature. The image of this derivative is exactly the orthogonal projection by (3.5), and Pythagoras proves (3.3)'s norm identities. This is H's projection, rather than a new projection theorem.

For local representatives, choose compact odd $F_n$ whose derivatives converge to $q_*$ in $L^2(\rho dr)$. Cauchy–Schwarz with $\rho^{-1}$ on a compact interval and $F_n(0)=0$ gives uniform convergence there to $F_*$. The isometry and odd energy gap make $pF_n$ Cauchy in horizontal energy. The potential bound and positive compact minima of $V$ identify its local $L^2$ representative with $pF_*$. Compact distributional tests identify its derivative limits. The local product rules yield the last two identities of (3.3). This verifies every projection pairing used below without a global $L^2$ substitution. $\square$

## 4. Checked strong tails and full phase slices of the same source

**Lemma 4.1 (strong mode and derivative tails).** For the identical canonical heat let

$$
\mathcal G(\xi)=\int_0^\infty k_t(\xi)dt\quad(\xi\ne0),\qquad
c_\infty=\gamma\int Vp>0.
\tag{4.1}
$$

N supplies the positive locally integrable fundamental solution, smooth off zero, with $\mathcal E\mathcal G=\delta_0$, homogeneity of degree $-5$, and $\mathcal G\le C d(0,\xi)^{-5}$. The E tails used here are

$$
\begin{gathered}
p(\xi)\le C(1+d(0,\xi))^{-5},\qquad
|Dp(\xi)|\le C(1+d(0,\xi))^{-6}\quad(D=X,Y),\\
p_R:=R^5p\circ\delta_R\to c_\infty\mathcal G,\qquad
Dp_R\to c_\infty D\mathcal G
\quad\text{uniformly on compact sets avoiding zero}.
\end{gathered}
\tag{4.2}
$$

They have continuous representatives, and for $R\ge1$ are dominated away from zero by $C d^{-5}$ and $C d^{-6}$, respectively.

Proof. The compact set $\{N=1\}$ and homogeneity give $d\le CN$, so the two gauges are comparable. Smoothness and homogeneity of $\mathcal G$ on the proper compact control sphere give $|D\mathcal G|\le Cd^{-6}$. Dyadic annuli with ball volume $v_d L^7$ give

$$
\int_{d<L}\mathcal G\le CL^2,\qquad
\int_{d<L}|D\mathcal G|\le CL.
\tag{4.3}
$$

These derivatives also hold distributionally through zero. Indeed a smooth dilation cutoff at radius $\epsilon$ has horizontal derivative $O(\epsilon^{-1})$ and is supported in a ball of comparable radius. Its integration-by-parts error is $O(\epsilon^{-1})O(\epsilon^2)=O(\epsilon)$; the omitted derivative integral is $O(\epsilon)$. Both vanish.

The bounded nonnegative potential gives at time one $p\le e^{\gamma\|V\|_\infty}P_1p$. The heat column identity $\int p_E(1;\eta,\xi)^2d\eta=p_E(2;\xi,\xi)$ and (2.2) show $p$ is bounded. Put $f=Vp$. Decay of $V$ and dimension seven imply $V\in L^2\cap L^\infty$; thus $f\in L^1\cap L^2\cap L^\infty$, its mass $m$ is strictly positive, and initially $f\le C(1+d)^{-5}$.

N's source reconstruction, whose orientation follows from left invariance, is

$$
p(\xi)=\gamma\int\mathcal G(\eta^{-1}\xi)f(\eta)d\eta.
\tag{4.4}
$$

It also follows directly from (2.2)'s positive finite-time integrals, Tonelli and their $L^2$ limit. At an output distance $L=d(0,\xi)\ge2$, partition inputs into $d(0,\eta)\le L/2$; $d(0,\eta)>L/2$ with $d(\eta,\xi)\le L/2$; and the remaining set where both distances exceed $L/2$. The first and third contributions are at most $CmL^{-5}$. The middle is initially at most $CL^{-5}L^2=CL^{-3}$ by (4.3). Thus $p\le C(1+d)^{-3}$ and $f\le C(1+d)^{-8}$. Repeating the same split makes the middle $O(L^{-6})$, proving $p\le C(1+d)^{-5}$ and

$$
f\le C(1+d)^{-10}.
\tag{4.5}
$$

A left invariant output derivative follows the path $\xi\exp(tD)$, so $D_\xi\mathcal G(\eta^{-1}\xi)=(D\mathcal G)(\eta^{-1}\xi)$. Compact testing, (4.3) and $f\in L^1\cap L^\infty$ justify differentiating (4.4) distributionally in this orientation. The same split bounds the first and third derivative contributions by $CmL^{-6}$ and the middle by $CL^{-10}L=CL^{-9}$. This proves the derivative bound. Removing an $\epsilon$-ball around the input-output singularity costs uniformly $O(\epsilon^2)$ for $\mathcal G$ and $O(\epsilon)$ for $D\mathcal G$. On its complement the cut-off kernels are bounded and continuous with an $L^1$ input majorant. Dominated convergence and then $\epsilon\downarrow0$ prove continuity of both convolution representatives.

Set $f_R=R^7 f\circ\delta_R$. Its mass is $m$, it concentrates at zero, and outside every fixed input ball it satisfies $f_R\le CR^{-3}d^{-10}$. Exact group and Haar scaling express $p_R,Dp_R$ as convolutions of $f_R$ with $\gamma\mathcal G,\gamma D\mathcal G$. On a compact output set avoiding zero, a sufficiently small input ball about zero sees uniformly continuous kernels. The input mass there tends to $m$. Near an output singularity, inputs stay away from zero, so (4.3) bounds their contribution by $O(R^{-3})$, uniformly on that compact output set. On the remainder the kernels are uniformly bounded and input mass outside the small input ball tends to zero. Take $R\to\infty$ and then shrink that input ball. This proves the compact uniform limits, including the whole input tail. Finally degree one gives $Dp_R=R^6(Dp)\circ\delta_R$; the decay estimates give the stated uniform majorants. This checks the E tail ingredient from its supplied upstream antecedents. $\square$

**Lemma 4.2 (phase integrals and projection slope).** Define

$$
C_{\mathcal G}=\int\mathcal G(1,\mathbf z)^2d\mathbf z,\quad
D_{\mathcal G}=\int|Y\mathcal G(1,\mathbf z)|^2d\mathbf z,\quad
E_{\mathcal G}=\int|X\mathcal G(1,\mathbf z)|^2d\mathbf z,\quad
t_\infty=D_{\mathcal G}/(2C_{\mathcal G}).
\tag{4.6}
$$

All are finite and

$$
C_{\mathcal G},D_{\mathcal G}>0,\quad
E_{\mathcal G}+D_{\mathcal G}=10C_{\mathcal G},\quad
E_{\mathcal G}>4C_{\mathcal G},\quad 0<t_\infty<3.
\tag{4.7}
$$

On both height tails,

$$
\begin{aligned}
\rho(r)&\sim c_\infty^2C_{\mathcal G}|r|^{-4},&
m_Y(r)&\sim c_\infty^2D_{\mathcal G}|r|^{-6},\\
\int|Xp(r,\mathbf z)|^2d\mathbf z&\sim c_\infty^2E_{\mathcal G}|r|^{-6},&
J(r)&\sim\tfrac12c_\infty^2D_{\mathcal G}|r|^{-4},\\
q_*(r)&\to t_\infty,&F_*(r)/r&\to t_\infty.
\end{aligned}
\tag{4.8}
$$

In particular $q_*$ is bounded on the whole line and $|F_*(r)|\le C|r|$.

Proof. At height one $d(0,(1,\mathbf z))$ is comparable to $1+\max(|y|,|z|^{1/2},|w|^{1/3})$. The phase dilation $(y,z,w)\mapsto(Ry,R^2z,R^3w)$ has Jacobian $R^6$. The squared bounds in (4.2) have degrees $-10$ and $-12$ and are integrable on this phase space of homogeneous dimension six. They therefore majorize the entire phase slices, including their complements of compact sets. Dominated convergence yields the positive-height limits of $r^4\rho$, $r^6m_Y$ and $r^6\int|Xp|^2$. It also gives the mixed limit

$$
r^5\int p(r,\mathbf z)Xp(r,\mathbf z)d\mathbf z
 \longrightarrow c_\infty^2\int\mathcal G(1,\mathbf z)X\mathcal G(1,\mathbf z)d\mathbf z.
\tag{4.9}
$$

The mixed integrand has an integrable degree $-11$ majorant. Parity supplies the negative tails, with the sign change in the mixed integral.

Homogeneity gives $\int\mathcal G(r,\mathbf z)^2=C_{\mathcal G}r^{-4}$ and the corresponding derivative slices $E_{\mathcal G}r^{-6},D_{\mathcal G}r^{-6}$ for $r>0$. Second horizontal derivatives of $\mathcal G$ are smooth off zero and homogeneous of degree $-7$. On a compact positive height interval these yield integrable phase majorants for $(X\mathcal G)^2$ and $\mathcal G X^2\mathcal G$. Hence the squared mode slice can be differentiated twice under the phase integral. Harmonicity and phase integration by parts give

$$
20C_{\mathcal G}r^{-6}
 =2\int|X\mathcal G|^2+2\int|Y\mathcal G|^2.
\tag{4.10}
$$

For that integration by parts, insert phase cutoffs $\zeta(y/L,z/L^2,w/L^3)$. Their $Y$ derivatives are $O(L^{-1})$ on bounded height intervals. The phase $L^2$ bounds and Cauchy–Schwarz make the boundary term vanish. The same slice differentiation gives $\int\mathcal G X\mathcal G=-2C_{\mathcal G}r^{-5}$. Thus at height one Cauchy–Schwarz gives $E_{\mathcal G}\ge4C_{\mathcal G}$. Equality would imply $X\mathcal G(1,\mathbf z)=-2\mathcal G(1,\mathbf z)$, first almost everywhere and then everywhere by continuity. Homogeneity extends it to $X\mathcal G=-2\mathcal G/r$ on $r>0$. At each fixed phase, $\mathcal G=r^{-2}a(\mathbf z)$ would then contradict the bound $\mathcal G\le Cr^{-5}$ at infinity and positivity. The inequality is strict. If $D_{\mathcal G}=0$, continuity and homogeneity give $Y\mathcal G=0$ on $r>0$. Harmonicity makes $\mathcal G$ affine in height at each fixed phase; decay at infinity contradicts positivity again. This proves (4.7).

The full-height $V_1$ bound gives $|v_1(r)|\le C(1+|r|)^{-4}\rho(r)=O(|r|^{-8})$. Integrating $2r m_Y+\gamma v_1$ on the positive tail yields the asserted $J$ asymptotic: the slice error is uniformly $o(r^{-6})$ beyond a sufficiently large height, so its integrated error is $o(r^{-4})$, while the $v_1$ contribution is $O(r^{-7})$. Evenness gives the other tail. Division by positive $\rho$ gives $q_*\to t_\infty$; its primitive has $F_*/r\to t_\infty$. Continuity on compact intervals and the two tail limits make $q_*$ globally bounded. These are the E slice and slope results with their majorants checked; no local limit has been integrated over uncontrolled phases. $\square$

## 5. The exact exterior forcing and its explicit tail constant

**Definition 5.1 (exterior residual).** For a compact smooth complex test $u$ set

$$
e(u)=\mathcal L(u)-h_0(U_h,u),\qquad
\begin{aligned}
g_X&=-F_*Xp-pq_*,\\
g_Y&=(2r-F_*)Yp,\\
k&=\gamma(V_1+VF_*)p.
\end{aligned}
\tag{5.1}
$$

Using the local projection representative and its homogeneous derivative vector gives the exact identity

$$
e(u)=\int g_X Xu+\int g_Y Yu+\int k u.
\tag{5.2}
$$

Both coefficient-potential contributions, $\gamma V_1p$ and $\gamma VpF_*$, are retained with the displayed signs. The identity uses only compact tests and does not assign a global $L^2$ representative to the response. It follows directly by subtracting $h_0(U_h,u)=b(U_h,u)-\gamma\int VpF_*u$ from (2.5).

**Theorem 5.2 (exact norm of the horizontal forcing tail).** Put

$$
K_{\rm tail}=\frac23c_\infty^2C_{\mathcal G}t_\infty(8-t_\infty)>0,
\quad
M_R^2=\int_{|r|>R}(|g_X|^2+|g_Y|^2)d\xi,
\quad
N_R^2=\int_{|r|>R}|rk|^2d\xi.
\tag{5.3}
$$

Then

$$
M_R^2=K_{\rm tail}R^{-3}+o(R^{-3}),\qquad N_R^2=O(R^{-9}).
\tag{5.4}
$$

The constant is an explicit upper-bound constant for the response gain; it is not asserted to be the optimal gain constant.

Proof. At positive height $r$, dilate the entire phase slice and use Lemma 4.2 and its uniform majorants. With $t=t_\infty$, the scaled $g_X,g_Y$ tend respectively to $-c_\infty t(\mathcal G+X\mathcal G)$ and $c_\infty(2-t)Y\mathcal G$ at height one. Therefore

$$
\begin{aligned}
r^4\int(|g_X|^2+|g_Y|^2)d\mathbf z
 &\longrightarrow c_\infty^2\{t^2(E_{\mathcal G}-3C_{\mathcal G})+(2-t)^2D_{\mathcal G}\}\\
 &=c_\infty^2C_{\mathcal G}t(8-t).
\end{aligned}
\tag{5.5}
$$

Here $\int(\mathcal G+X\mathcal G)^2=E_{\mathcal G}-3C_{\mathcal G}$ because $\int\mathcal G X\mathcal G=-2C_{\mathcal G}$. Inserting $D_{\mathcal G}=2tC_{\mathcal G}$ and $E_{\mathcal G}=(10-2t)C_{\mathcal G}$ gives the last equality. To specify the domination, after phase dilation the $g_X$ expression is $-(F_*(r)/r)Xp_r(1,\mathbf z)-q_*(r)p_r(1,\mathbf z)$, and the $g_Y$ expression is $(2-F_*(r)/r)Yp_r(1,\mathbf z)$. Their coefficients are bounded and their squared mode/derivative majorants are integrable. Thus every cross term in (5.5) is controlled.

The squared slice is even under $\sigma$. The uniformly valid tail asymptotic in (5.5) integrates over both half-lines with $\int_{|r|>R}|r|^{-4}dr=2/(3R^3)$, proving the first part of (5.4). For $|r|\ge1$, $V\le C|r|^{-5}$, $|V_1|\le C|r|^{-4}$ and $|F_*|\le C|r|$, so $|k|\le C|r|^{-4}p$. Consequently

$$
N_R^2\le C\int_{|r|>R}|r|^{-6}\rho(r)dr=O(R^{-9}).
\tag{5.6}
$$

This bounds both potential terms quantitatively; neither has been removed by a parity assertion. $\square$

## 6. A bound uniform over the entire exterior class

**Definition 6.1 (all exterior tests and their completion).** For $R\ge1$ let $\mathscr E_R$ be the real compact smooth functions on $\mathbb R^4$ supported in $\{|r|>R\}$. Let $\dot{\mathscr E}_R$ be its completion in $\sqrt b$, with complexification $\dot{\mathscr E}_R^{\mathbb C}$. No parity restriction is made in this definition. Odd/even parts preserve this exterior class. The odd real subspace embeds in $\dot{\mathcal H}_-$ by inclusion of its core. Potential and polarized pairings extend by (2.4) and the bounds below. The completion has local representatives with support in $\{|r|\ge R\}$; no global $L^2$ or native membership is required.

**Theorem 6.2 (uniform exterior gain).** Let

$$
C_V=\sup_{|r|\ge1,\,\mathbf z}|r|^5V(r,\mathbf z)<\infty,
\qquad\kappa_0=4\gamma C_V.
\tag{6.1}
$$

Choose $R_1\ge1$ so that $1-\kappa_0R^{-3}\ge1/2$ for $R\ge R_1$. There is a nonnegative function $\eta(R)\to0$, depending only on the fixed canonical source, such that for every $R\ge R_1$ and every $u\in\dot{\mathscr E}_R^{\mathbb C}$,

$$
\begin{gathered}
h_0[u]\ge(1-\kappa_0R^{-3})b[u],\\
\frac{|e(u)|^2}{h_0[u]}\le\frac{K_{\rm tail}+\eta(R)}{R^3}\quad(u\ne0),\qquad
2\operatorname{Re}e(u)-h_0[u]\le\frac{K_{\rm tail}+\eta(R)}{R^3}.
\end{gathered}
\tag{6.2}
$$

The supremum of the latter gain is the same over all complex exterior vectors, all real exterior vectors, and just real odd exterior vectors. It equals the supremum of $|e(u)|^2/h_0[u]$ over nonzero vectors in any of these respective classes. In particular arbitrary finite sums, with arbitrary complex coefficients and every cross term retained, obey the one uniform bound. Every convergent sum in the exterior completion obeys it as well.

Proof. For a compact complex exterior test, integrate $(|u|^2/r)'$ separately on $(R,\infty)$ and $(-\infty,-R)$. All endpoint terms vanish because the compact support lies strictly beyond the excluded heights. Integrating also in phases gives

$$
\int\frac{|u|^2}{r^2}=2\operatorname{Re}\int\frac{\overline u Xu}{r}
\le2\left\|u/r\right\|_2\|Xu\|_2,
\qquad \|u/r\|_2\le2\|Xu\|_2.
\tag{6.3}
$$

This is the needed Hardy boundary condition on both tails. It is not an assertion for arbitrary functions with a nonzero boundary trace. Since $V\le C_VR^{-3}r^{-2}$ on this support,

$$
\gamma\int V|u|^2\le4\gamma C_VR^{-3}\|Xu\|_2^2
\le\kappa_0R^{-3}b[u].
\tag{6.4}
$$

This proves coercivity. Equation (5.2), Cauchy–Schwarz on the joint horizontal derivative vector, and Hardy give

$$
|e(u)|\le(M_R+2N_R)\sqrt{b[u]},\qquad
\frac{|e(u)|^2}{h_0[u]}
\le\mathcal A_R:=\frac{(M_R+2N_R)^2}{1-\kappa_0R^{-3}}.
\tag{6.5}
$$

Theorem 5.2 gives $R^3\mathcal A_R\to K_{\rm tail}$. For example define

$$
\eta(R)=|R^3\mathcal A_R-K_{\rm tail}|\quad(R\ge R_1).
\tag{6.6}
$$

This is nonnegative, tends to zero and is independent of $u$. The inequality $|e(u)-h_0[u]|^2\ge0$ yields $2\operatorname{Re}e(u)-h_0[u]\le |e(u)|^2/h_0[u]$ for nonzero $u$; zero is immediate.

Hardy makes a $b$-Cauchy exterior sequence Cauchy in $L^2(r^{-2}d\xi)$, hence on every compact set. Compact testing identifies its derivative limits and preserves the exterior support in the local representative. The potential bound, (6.4), and polarization extend $h_0$ continuously; (6.5) extends $e$. Thus every inequality passes to the stated completion. There is no boundary contribution left over from its limiting trace.

The involution preserves $h_0$, and both $\mathcal L$ and $h_0(U_h,\cdot)$ annihilate even tests. Hence $e(u_+)=0$ and $h_0[u]=h_0[u_-]+h_0[u_+]$. For $u=v+iw$ with real $v,w$, $2\operatorname{Re}e(u)-h_0[u]=2e(v)-h_0[v]-h_0[w]$. Coercivity makes these added energies nonnegative. Dropping imaginary and even parts therefore cannot reduce the gain. For the quotient, $|e(u)|^2=e(v_-)^2+e(w_-)^2$ while $h_0[u]$ contains the sum of their energies and the nonnegative even energies. Its supremum also equals the real odd supremum. Along a real odd nonzero direction $v$, the maximum of $2t e(v)-t^2h_0[v]$ is exactly $e(v)^2/h_0[v]$ at $t=e(v)/h_0[v]$. These facts prove all supremum equalities, without a claim of a compact maximizing vector.

For clarity, if $u=\sum_{j=1}^n a_j u_j$, the quantity used is exactly

$$
h_0[u]=\sum_{i,j=1}^n\overline{a_i}a_jh_0(u_i,u_j),\qquad
e(u)=\sum_{j=1}^n a_j e(u_j).
\tag{6.7}
$$

The proof bounds this combined vector. It never adds separately optimized gains or assumes disjointness. Continuity treats any sum converging in the exterior completion. This proves the full exterior-class assertion. $\square$

## 7. Matching lower power from the credited compact witness

**Theorem 7.1 (sharp exterior power).** Let

$$
\mathfrak G(R)=\sup_{u\in\dot{\mathscr E}_R^{\mathbb C}}
 \{2\operatorname{Re}e(u)-h_0[u]\}.
\tag{7.1}
$$

There is a fixed real odd nonzero compact smooth $\varphi$, supported in $\{|r|>1\}$, for which

$$
\begin{gathered}
u_R=R^{-4}\varphi\circ\delta_{1/R},\quad
\frac{e(u_R)^2}{h_0[u_R]}=k_\varphi R^{-3}+o(R^{-3}),\quad k_\varphi>0,\\
0<\liminf_{R\to\infty}R^3\mathfrak G(R)
\le\limsup_{R\to\infty}R^3\mathfrak G(R)\le K_{\rm tail}.
\end{gathered}
\tag{7.2}
$$

Consequently $\mathfrak G(R)=\Theta(R^{-3})$. Neither an exact optimal leading constant nor attainment by an exterior compact test is asserted.

Proof and correspondence. This is E Theorem 5.2's lower witness, placed beyond height one and checked in the present units. Put $t=t_\infty$ and

$$
Z=-2rY^2\mathcal G+2tX\mathcal G\quad(r\ne0).
\tag{7.3}
$$

It is smooth, odd and homogeneous of degree $-6$. It is nonzero on $r>0$. Otherwise harmonicity gives $r\partial_r^2\mathcal G+t\partial_r\mathcal G=0$. At any fixed nonzero phase triple, the positive smooth function of $r>0$ is bounded as $r\downarrow0$ and tends to zero as $r\to\infty$. The complete solutions of this equation are $A+B r^{1-t}$ for $t\ne1$, and $A+B\log r$ for $t=1$. If $t<1$, decay at infinity forces $B=A=0$; if $t=1$, logarithmic growth and then decay do the same; if $t>1$, decay forces $A=0$ and boundedness at zero forces $B=0$. Each contradicts positivity.

Homogeneity moves a nonzero point to $r>1$. Choose a nonnegative compact smooth bump near that point, supported in $r>1$, and add its $\sigma$ reflection to get $\chi_0$. Set

$$
\varphi=\chi_0Z,\qquad L_\varphi=\int\chi_0Z^2>0,\qquad
k_\varphi=\frac{c_\infty^2L_\varphi^2}{b[\varphi]}.
\tag{7.4}
$$

The test is real odd, smooth and compact beyond both excluded heights. If $b[\varphi]=0$, then $X\varphi=Y\varphi=0$; their successive brackets span all four coordinate derivatives. The compactly supported constant would be zero, a contradiction. Thus $k_\varphi>0$.

Exact Haar and horizontal scaling gives

$$
R^3h_0[u_R]=b[\varphi]-\gamma R^2\int V(\delta_R\xi)\varphi^2d\xi\longrightarrow b[\varphi].
\tag{7.5}
$$

Here $V(\delta_R\xi)=O(R^{-5})$ uniformly on the fixed support. Let $U_R=R^4(pF_*)\circ\delta_R$. Lemmas 4.1–4.2 and the local derivative rules give, uniformly on that support,

$$
\begin{aligned}
U_R&\to c_\infty t r\mathcal G,\\
XU_R&\to c_\infty t(\mathcal G+rX\mathcal G),&
YU_R&\to c_\infty t rY\mathcal G.
\end{aligned}
\tag{7.6}
$$

Indeed $U_R=p_R F_*(Rr)/R$, $XU_R=(Xp_R)F_*(Rr)/R+p_Rq_*(Rr)$, and $YU_R=(Yp_R)F_*(Rr)/R$. The height support stays away from zero on both tails. No second derivative of $F_*$ is assumed.

Scale each complete functional separately:

$$
\begin{aligned}
R^3\mathcal L(u_R)
 &=2\int r(Yp_R)(Y\varphi)+\gamma R\int V_1(\delta_R\xi)p_R\varphi,\\
R^3h_0(U_h,u_R)
 &=b(U_R,\varphi)-\gamma R^2\int V(\delta_R\xi)U_R\varphi.
\end{aligned}
\tag{7.7}
$$

The first potential term is $O(R^{-3})$ by $|V_1(\delta_R\xi)|=O(R^{-4})$. The second is $O(R^{-3})$ by the $V$ bound. Thus both potential contributions are retained and bounded. Compact integration by parts, $Yr=0$ and $\mathcal E\mathcal G=0$ on the support yield

$$
b(r\mathcal G,\varphi)=-2\int X\mathcal G\,\varphi,\qquad
\int r(Y\mathcal G)(Y\varphi)=-\int rY^2\mathcal G\,\varphi.
\tag{7.8}
$$

There is no phase-infinity boundary because $\varphi$ is compact. Passing to the limits in (7.7) gives

$$
R^3e(u_R)\longrightarrow c_\infty\int Z\varphi=c_\infty L_\varphi>0.
\tag{7.9}
$$

Combine (7.5) and (7.9) to obtain the quotient asymptotic in (7.2). The multiple $[e(u_R)/h_0[u_R]]u_R$ realizes this quotient as a gain along its line and still belongs to the exterior core. Theorem 6.2 gives the matching uniform upper power. This reuses E's positive witness; the new inference is its comparison with a uniform bound on the entire exterior class. $\square$

## 8. Complete-coefficient interpretation and the exact obstruction

**Corollary 8.1 (all remote corrections to the height comparison).** Put

$$
B_h=3A-\gamma C_2-I_h,\qquad C_h=a\nu^2B_h-\lambda D_{\rm clock}.
\tag{8.1}
$$

For real odd exterior corrections, and by complexification for all complex odd exterior corrections, the homogeneous comparison value is exactly

$$
\begin{aligned}
\mathcal Q_h(u)
 &:=3A-\gamma C_2+h_0[U_h+u]-2\operatorname{Re}\mathcal L(U_h+u)\\
 &=B_h+h_0[u]-2\operatorname{Re}e(u)
 \ge B_h-\frac{K_{\rm tail}+\eta(R)}{R^3}.
\end{aligned}
\tag{8.2}
$$

The same formula for even additions is understood through its continuous polarized forms; they only add nonnegative energy. The complete coefficient in original units therefore satisfies

$$
a\nu^2\mathcal Q_h(u)-\lambda D_{\rm clock}
\ge C_h-a\nu^2\frac{K_{\rm tail}+\eta(R)}{R^3}.
\tag{8.3}
$$

The infimum of $\mathcal Q_h(u)$ over the exterior class is $B_h-\mathfrak G(R)$, so its maximal improvement has precisely power $R^{-3}$. If $B_h>0$, every sufficiently remote canonical comparison stays positive. If $B_h-\mathscr R\overline D>0$ at a fixed admitted datum, every sufficiently remote complete comparison stays positive. Neither hypothesis is asserted to hold.

Proof. H's projection identity gives $h_0[U_h]=\mathcal L(U_h)=I_h$. Exact polarization, including the cross term between $U_h$ and $u$, gives (8.2); Theorem 6.2 bounds its gain. Since $\lambda D_{\rm clock}=a\nu^2\mathscr R\overline D$, subtraction yields (8.3) with every original source, clock and threshold term intact. The supremum definition and Theorem 7.1 give the infimum identity and power. If either stated margin is positive, choose $R$ sufficiently large that the uniform error is smaller than half that margin. $\square$

The full response remains

$$
G_{\rm resp}=B_h-\delta_h,\qquad \delta_h=h_0[\Psi-U_h]>0,
\tag{8.4}
$$

where E supplies strict positivity. The exterior estimate is not an upper bound on the full $\delta_h$. Its interior and unrestricted components remain in (8.4). The bound rules out obtaining an unbounded or nonvanishing gain at arbitrarily remote heights by accumulating witnesses at arbitrarily many scales: every finite combined exterior correction, and every convergent exterior sum, satisfies the same bound with all cross terms. It does not exclude a sign proof from a finite core estimate, another same-source identity, or a sufficiently strong finite witness. A vanishing remote gain is neither a sign decision nor logical underdetermination of this fixed source.

Under $W=j_0V$, $W_j=j_0V_j$, $W_{\rm t}=j_0V_{\rm t}$ and $\overline C=j_0C_*$, one has $\gamma=j_0/\overline C$. Consequently $p$, $\mathcal G$, $c_\infty$, $t_\infty$ and $K_{\rm tail}$ are canonical for this precise source. This normalization changes no original $\nu$, $\lambda$, signed parameter, raw source or native clock. The exterior parameter $R$ is independent of the native small-$s$ limit. A homogeneous comparison value is not substituted for an actual eigenstate or asserted to be a matching native infimum.

## 9. Resolved occurrence and actual-state credit

**Proposition 9.1 (existing ratio images and admitted occurrence).** R14 already proves, at fixed admitted $H,I,\kappa$, the exact interior-pole image

$$
\mathscr R\in\left(\frac{\pi^2(l-\alpha_\kappa)^2}{L_I^2},
                       \frac{\pi^2(u-\alpha_\kappa)^2}{L_I^2}\right).
\tag{9.1}
$$

For $0<H<1/2$, $0<l<u<H$ and a fixed radius $0<b<\min\{l/4,(H-u)/2,H/4\}$, the pole and positive or negative signed-window images are respectively

$$
\begin{aligned}
\mathscr R_+&=\left(\frac{\pi^2(l-b-b^2/H)^2}{L_I^2},\frac{\pi^2u^2}{L_I^2}\right),\\
\mathscr R_-&=\left(\frac{\pi^2l^2}{L_I^2},\frac{\pi^2(u+b-b^2/H)^2}{L_I^2}\right).
\end{aligned}
\tag{9.2}
$$

Every interior value is attained and endpoints are excluded. At fixed pole the images are

$$
\left[\frac{\pi^2(k_0-b-b^2/H)^2}{L_I^2},\frac{\pi^2k_0^2}{L_I^2}\right),\qquad
\left(\frac{\pi^2k_0^2}{L_I^2},\frac{\pi^2(k_0+b-b^2/H)^2}{L_I^2}\right].
\tag{9.3}
$$

The included endpoints use $\kappa=b,-b$; excluded endpoints require zero parameter. R14 supplies the enlarged admitted parameter-height neighbourhood, including positive margins of the original five probabilities, denominator and determinant margins, bounded derivatives and scalar-fibre invertibility. Its original means are $X=Y=H+\kappa$, $Z=1-2H$ and its original third component is retained.

R15 proves that across distinct fixed admitted datasets in this window, at fixed $H,a,\varepsilon$ and for each sign of $\kappa$, the ratio image is exactly $(0,\infty)$. Thus negative response and negative $C_{108}$ already occur for each sign. With $Q_X=G_X/\overline D$, each coefficient is $C_X=a\nu^2\overline D(Q_X-\mathscr R)$. On an available open image $(A_0,B_0)$, negative, positive and zero $C_X$ occur exactly when $B_0>Q_X$, $A_0<Q_X$ and $A_0<Q_X<B_0$. Across the full image, positive and zero response each occur if and only if $G_{\rm resp}>0$; positive and zero $C_{108}$ each occur if and only if $G_{108}>0$. Narrowing one admitted symmetric interval about a fixed pole makes its ratio arbitrarily large; choosing a sufficiently narrow fixed interval already gives actual negative-response unit-orbit selection. Each datum is fixed before its own $s$-limit. These are credited R14–15 results, with their proofs and conditional analytic admission scope, rather than new occurrence claims from an exterior estimate.

**Proposition 9.2 (existing actual energy and all-state bridges).** Under their original hypotheses, R11.1 gives $E_s\to\min(0,C_{\rm resp})$. P105.1 gives, for every prescribed sequence and every actual normalized complex ground-state choice,

$$
r_{s_n}\to\infty\quad\Longleftrightarrow\quad
\operatorname{dist}_{L^2}(\mathcal U_{s_n}\psi_{s_n},\{e^{i\theta}p\})\to0.
\tag{9.4}
$$

A5.1 gives $c(L-C_{\rm resp})=0$ whenever the actual unscaled energies tend to $L$ and actual microscopic states tend weakly to $cp$. If $C_{\rm resp}<0$, R11.2 gives $E_s\to C_{\rm resp}$, $\epsilon_c(s)=C_{\rm resp}s^2+o(s^2)$ and $r_s\sim(-C_{\rm resp})s^{-6}\to\infty$, hence the microscopic unit orbit for every actual choice.

For a fixed original datum define the complete long-time tensor and normalized Coulomb data

$$
\begin{aligned}
M&=\int_I\phi^2c_\kappa c_\kappa^{\mathsf T}dk>0,&d_M(z)&=(z^{\mathsf T}M^{-1}z)^{1/2},\\
\beta_C&=\frac{\phi(k_0)\int_I\phi^3dk}{4\pi\sqrt{\det M}},&
e_C&=-\frac{\beta_C^2}{4a},&\varrho&=\frac{\beta_C}{2a},\\
h_C(z)&=(\det M)^{-1/4}(\varrho^3/\pi)^{1/2}e^{-\varrho d_M(z)},&
\mathcal D_gv(k,z)&=g^{-3/2}v(k,z/g).
\end{aligned}
\tag{9.5}
$$

A10.2 and A11.1 already prove, for each such actual sequence and choice, equivalence of microscopic weak zero with the source-centred full-mass Coulomb orbit, and either implies

$$
\frac{E_s}{g_s^2}\to e_C,\qquad r_s\to-\chi_c^2e_C>0,\qquad
\inf_\theta\|\mathcal D_{g_s}\psi_s-e^{i\theta}\phi h_C\|_2\to0.
\tag{9.6}
$$

At $C_{\rm resp}>0$, A6.1 supplies microscopic global weak zero, local strong zero, vanishing rescaled horizontal and potential energies and orbit distance $\sqrt2$, while norms remain one. A12.1 consequently gives (9.6) for every actual choice, with

$$
E_s=\chi_c^2e_Cs^6+o(s^6),\qquad
\epsilon_c(s)=\chi_c^2e_Cs^8+o(s^8).
\tag{9.7}
$$

The exact coefficient, mass-carrying macroscopic scale and normalized full-mass profile on that conditional branch are resolved credit. The same conclusions apply on any actual weak-zero subsequence at response zero, without asserting that any or every actual choice has one.

Credit and proof scope. R's matching law uses its full-complex-domain lower estimate, actual negative attainment and P's actual resolvent equivalence, beyond its corrected-core trial upper construction. A's solvability uses the actual bilinear equation and compact tests fixed before homogeneous approximation. Its weak-zero transfer removes the short field in the actual resolvent and derives an $o(g_s^2)$ fixed-cutoff variational deficit before invoking P72–73. Norm proximity alone would not provide that energy precision. The macroscopic-orbit converse is a microscopic/macroscopic norm comparison. A15.2 supplies the energy-endpoint converse through the strict core margin recorded below. None of these actual-state theorems is proved from, or strengthened by substituting an exterior homogeneous correction into, the actual eigen-equation.

**Proposition 9.3 (existing quantitative core margin and three-way endpoint equivalence).** Fix one original admitted datum before any limit. In addition to the conditional antecedents already specified, retain A13.1's use of P §§70–73 and L Lemma 41.2, with the parameter applicability conditions of L Definition 35.1, where L is [Native long-time phase diffusion](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md). All statements below retain those scopes. With exactly the Coulomb normalization (9.5), put

$$
c_{\rm ref}=\frac{e^{-4}h_C(0)}{24\sqrt\pi}
 =\frac{e^{-4}\varrho^{3/2}}{24\pi(\det M)^{1/4}}>0,
\qquad
\mathbb B_g=\{q:\varrho d_M(gq)\le1\},
\qquad e_1(g)=E_1(g).
\tag{9.8}
$$

A13.2 supplies a datum-dependent $g_0>0$ such that every nonnegative normalized actual reference ground state $v_g\in D(S)$ of $aS-gW_1$, for every $0<g<g_0$, satisfies

$$
v_g(k,q)\ge c_{\rm ref}g^{3/2}\phi(k)
\quad\text{for almost every }(k,q)\in I\times\mathbb B_g.
\tag{9.9}
$$

The height range is the whole original interval. A13.3 supplies the same lower amplitude on every fixed microscopic compact set after composition with the exact $\Xi_s$. The constant $c_{\rm ref}$ is precisely A13.1's $c_*$, with no ground-state, compact-set or response-sign dependence.

For any actual normalized complex ground-state choice set $F_s=\mathcal U_s\psi_s$, $u_s=|\psi_s|$, $D_s=W_{s^2}-W_1\ge0$ and $U_s^{<}=s^5D_s\circ\Xi_s$. The modulus $u_s$ is itself a normalized actual ground state in the unchanged $D(S)$. For each fixed compact Lebesgue measurable $K\subset\mathbb R^4$ of positive measure define the scalar charge

$$
\mathfrak a_s(K)=\int_K\phi(k_0+\varepsilon sr)U_s^{<}(\xi)|F_s(\xi)|d\xi.
\tag{9.10}
$$

This is A14.1's scalar $A_s(K)$, distinct from the Friedrichs operator of §1. For sufficiently small $s$ depending on $K$ and the fixed datum, A14.2 gives, uniformly over every actual complex ground-state choice,

$$
\frac{e_1(g_s)-E_s}{g_s^2}
 \ge c_{\rm ref}\sqrt{j_0\chi_c}\,\mathfrak a_s(K)\ge0.
\tag{9.11}
$$

There is no response-sign or bounded-$r_s$ hypothesis. Its exact finite-native pairing, supplied by A14.2, is

$$
O_s=\langle v_{g_s},u_s\rangle\in(0,1],\qquad
(e_1(g_s)-E_s)O_s
 =g_s\int_{\mathcal C}D_s v_{g_s}u_s\,dY.
\tag{9.12}
$$

Both vectors lie in the exact common original $D(S)$; the multipliers are bounded separately at each positive $s$. This is an actual spectral comparison, with no homogeneous response vector substituted into a native domain.

Define the finite positive core charge and strict margin

$$
m_{\rm core}=\int_{\mathbb R^4}Vp\,d\xi\in(0,\infty),\qquad
\eta_*=c_{\rm ref}\sqrt{j_0\chi_c}\,\phi(k_0)m_{\rm core}>0,
\qquad r_C=-\chi_c^2e_C>0.
\tag{9.13}
$$

A15.1 gives, for every prescribed $s_n\downarrow0$ and every actual normalized complex choice with $F_{s_n}\rightharpoonup cp$ globally in $L^2$,

$$
\liminf_{n\to\infty}\frac{e_1(g_{s_n})-E_{s_n}}{g_{s_n}^2}
 \ge\eta_*|c|,
\qquad
\liminf_{n\to\infty}r_{s_n}
 \ge r_C+\chi_c^2\eta_*|c|.
\tag{9.14}
$$

Thus a finite actual endpoint with nonzero microscopic weak core lies strictly above $r_C$. In particular such a core is excluded at the Coulomb endpoint. A15.2 proves that, for every prescribed sequence and every actual normalized complex choice in $D(S)$, the following three assertions are equivalent along that same sequence:

$$
\begin{aligned}
&r_{s_n}\longrightarrow r_C;\\
&F_{s_n}\rightharpoonup0\quad\text{globally in }L^2(\mathbb R^4);\\
&\inf_{\theta\in\mathbb R}
 \|\mathcal D_{g_{s_n}}\psi_{s_n}-e^{i\theta}\phi h_C\|_2
 \longrightarrow0.
\end{aligned}
\tag{9.15}
$$

Whenever they hold, the energy limits (9.6) hold and $F_{s_n}\to0$ in $L^2(K)$ on every compact $K$. No response-sign hypothesis is needed for this equivalence. At response zero it asserts neither existence nor selection of any of its three equivalent endpoints.

Source correspondence. These are existing conditional A13–16 results, not additional theorems derived from the exterior estimate. A13 uses the all-height relative kernel estimate of L Lemma 41.2 and the actual fixed-cutoff Coulomb energy/profile of P72–73 to obtain the reference amplitude; macroscopic $L^2$ convergence alone supplies no shrinking-core pointwise bound. A14 pairs two actual eigen-equations on the same $D(S)$ and retains the exact raw Jacobian and path factors. A15 takes compact charge limits first and then exhausts space, using N's finite positive $\int Vp$; its strict margin excludes a nonzero weak core when the energy defect vanishes. A10.2 and A11.1 supply the other endpoint implications. A16 states these scopes and the unresolved selection boundary. None assumes a positive canonical $L^2$ spectral gap, global $L^2$ membership or native realizability of the homogeneous response, or a transfer of actual kinetic energies from norm proximity. The margin constrains actual weak core mass and does not sign either canonical coefficient or bound the full $\delta_h$.

## 10. Remaining original goal, attribution and boundaries

**Definition 10.1 (entire original decision).** The target remains to determine the complete $C_{108}$ and $C_{\rm resp}$ signs throughout the original admitted signed-$\kappa$, interval, interior-pole and jointly realized rational-vector family; determine occurrence or exclusion of every sign; and decide actual exact-critical $r_s$ and every normalized complex ground-state scale/profile behavior. The full domains, both deaths, all real frequencies, raw source, heat clock and path are exactly §1.

The unevaluated same-source comparisons are

$$
\gamma C_2+I_h+\delta_h\quad\text{against }3A,
\qquad
A+\gamma(C_2+2B_1)\quad\text{against }1.
\tag{10.1}
$$

They determine the canonical signs before comparison with $\mathscr R\overline D$. The strict residual $\delta_h>0$, the strict affine margin from N, the exact height projection from H and the exterior upper bound do not evaluate them. The ratio images and negative occurrence are already resolved. Positive and zero occurrence retain precisely their unevaluated canonical sign predicates. Arbitrary independent scalar assignments, unrelated potentials and separately optimized extrema do not respect this common realization and cannot decide it.

At response zero, the general established facts remain $E_s\to0$ and $c_0\le r_s=o(s^{-6})$ for a fixed $c_0>0$. A5.1's solvability identity is then vacuous, while A15.1–15.2 give the strict core margin (9.14) and the three-way endpoint equivalence (9.15). A nonzero microscopic weak core at the Coulomb energy endpoint is excluded. Existence or selection of that endpoint and actual weak-zero subsequences, actual endpoint selection away from $r_C$, deeper finite mixed/core branches, divergence or mixed subsequential scale behavior, and the complete every-choice decision remain unresolved. The weak-zero subsequence, if present, already has the matching energy and full-mass profile (9.6); a divergent-$r_s$ subsequence already has the microscopic unit orbit by (9.4). Neither the exterior theorem nor the credited margin selects among the remaining actual alternatives. A uniform centered detuning or crossover theorem remains unresolved. No positive-branch exact Coulomb coefficient or full-mass profile obligation is left open beyond its stated conditional occurrence premise.

**Definition 10.2 (source credit and evidence).** P §§70–75 supply the native field, charges, full domains and positive-cutoff attainment; §§78 and 81 supply the chart, Jacobian and exact conjugacy. P §§82–88 supply geometry, heat, integrated tails, compactness, reconstruction and the simple mode; §§89–91 distinguish tangent onset and the weak disk from actual unit selection; §§92–96 supply observation, infinite-fibre, quantum and analytic-preparation boundaries. P §97 supplies the rational shear, §100 the one-sided macroscopic bound, §§102–105 the actual shell defect, finite-native weighted resolvent and actual equivalence, and §§106–108 the weighted mode, parity, complete common-bridge field and specified affine coefficient.

R supplies coefficient multipliers, the homogeneous gap and Riesz response, recovery, the full-domain lower estimate, matching energy and conditional branches, canonical normalization, and the exact ratio/admission/negative-occurrence results. N supplies the identical-heat auxiliary fundamental solution, source reconstruction, strict nonaffinity and affine gap, including fixed complex slopes. H supplies the full height isometry, derivative-range theorem, quadrature, local representative and orthogonal decomposition, and its strict overlap/source/clock results. In particular $\mu<T<3\mu$ and $1+b[p]<\overline D<1+3b[p]$. E supplies the strong tails, slope, local derivative bridge and positive compact residual; §§3–4 and 7 above check each such ingredient used here. A supplies actual solvability and microscopic disappearance, and A10.2/A11.1/A12.1 supply weak-zero/Coulomb equivalence and the matching coefficient and full-mass positive-branch profile. A13.2/A13.3 supply the explicit reference lower amplitude, A14.2 the finite-native actual core-charge energy comparison, A15.1 the strict core margin, and A15.2 the same-sequence three-way Coulomb energy/weak-zero/full-mass-orbit equivalence. A16 retains the conditional analytic and unresolved selection scopes, including L Lemma 41.2's parameter conditions. These are existing actual-state credit, independent of the exterior response bound.

The substantive additional deduction is the full exterior-class upper bound (6.2), with the explicit constant (5.3) obtained from the exact two-sided horizontal forcing norm. Combining it with the credited lower witness proves the sharp power. H's decomposition and E's strict escape are reused, not counted again as new results. Haar scaling, convolution, compact distributional testing, Riesz representation, density, phase integration by parts, Hardy, Cauchy–Schwarz, Hilbert-space projection and elementary ODEs are mature intermediate tools. The underlying heat, localization, hypoellipticity and convolution suppliers retain their supplied conditional scopes, as do upstream analytic and completely positive realization antecedents. No external reauthentication, numerical validation, Lean/kernel/frozen certification or worldwide novelty/absence claim is made. Author identity, publication and prior verdicts are not mathematical premises.

**Definition 10.3 (native and interpretive limits).** Under the original real lift $D=\kappa x$ and $J_\kappa=\operatorname{diag}(1,1,\kappa)$, retain

$$
\psi^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1/2}\psi(k,q),\qquad
W_\tau^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1}W_\tau(k,q),\qquad
g_{\rm orig}=|\kappa|g.
\tag{10.2}
$$

The tensor transports to $J_\kappa M J_\kappa^{\mathsf T}$ with signed cross terms. Wavefunctions and unit raw-source fields have different absolute-Jacobian factors. No uniform $\kappa\to0$, actual frozen zero-leaf, wrapped-cover, torus or cutoff-free native conclusion follows. The auxiliary $\mathcal G$ supplies no replacement potential or cutoff-free native realization.

Homogeneous response and projection representatives are used only with their proved local and energy meanings. No global $L^2$ response, native response state, positive $L^2$ gap or all-$L^2$ inverse is assumed. The canonical tail parameter is independent of native time and every datum is fixed before its native limit. Native actual states retain the entire original complex domains; local or weak convergence never supplies global unit mass without the credited actual-state argument.

Four canonical coordinates, homogeneous dimension seven, three real phases, the rank-three long-time tensor, retained coordinate counts and physical Euclidean space are distinct predicates. No physical dimension or physical $SO(3)$ is selected. Analytic spectral amplitudes supply no native actuator, preparation, lawful transport, acquisition, resource or clock permission. Spectral energy is distinct from acquired mass and ML error. No autonomous reduced quantum evolution, full-channel acquisition, general neural-network or empirical machine-learning theorem, implementation migration, native efficiency/capacity/impossibility or wider-programme completion claim is made.

## 追加锚（本行以下为增补区）
