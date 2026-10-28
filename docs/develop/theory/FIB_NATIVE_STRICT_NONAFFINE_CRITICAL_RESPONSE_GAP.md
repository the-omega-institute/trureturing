# Strict nonaffine response at the native critical scale

This volume concerns the unchanged rational native problem of [Native full-state weak binding](FIB_NATIVE_LONG_TIME_PHASE_WEAK_BINDING.md), denoted P, and the homogeneous response of *Native exact-critical energy response and scale alternatives*, denoted R. All conclusions are conditional on their stated native, heat, source, domain and critical-mode antecedents. The new assertion is that the homogeneous response is never an affine height correction. It yields a strictly smaller complete coefficient than every member of the affine family. It does not evaluate the absolute coefficients or settle the original full-family sign, admitted occurrence and actual scale/profile question.

## 1. The original fixed data and complete native problem

**Definition 1.1 (unchanged original family).** Fix any one original admissible signed $\kappa\ne0$, $a>0$, $\varepsilon>0$, height interval $I=(l,u)$ and interior pole $k_0\in I$. Retain all original probability, interval and denominator restrictions and the original rational vector $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$, including its third component. Its jets are jointly realized, rather than independent parameters. Write

$$
\begin{aligned}
\alpha_\kappa&=\kappa+\kappa^2/H,& d_0&=k_0-\alpha_\kappa>0,& \nu&=\varepsilon/d_0,\\
c_j&=c_\kappa^{(j)}(k_0)\quad(j=0,1,2),&
j_0&=\varepsilon^4|\det(c_0,c_1,c_2)|>0,\\
c_\kappa(k_0+h)&=c_0+h c_1+\frac{h^2}{2(1+h/d_0)}c_2.
\end{aligned}
\tag{1.1}
$$

The last equality is exact on the original interval. In particular $k-\alpha_\kappa>0$ there. The retained components and determinant are

$$
\begin{aligned}
(A_\kappa(k),B_\kappa(k))
 &=\frac{k-2\kappa}{2H(k-\alpha_\kappa)}(H+\kappa-k,-k),\\
\det(c_\kappa,c_\kappa',c_\kappa'')(k)
 &=-\frac{H^2-\kappa^2}{2H^3(k-\alpha_\kappa)^3}\ne0.
\end{aligned}
\tag{1.2}
$$

The constants and jets in these identities retain their original admissibility conditions. The three phases $q=(\theta,v,x)$ range over $\mathbb R^3$, with raw measure $dY=dk\,dq$. Put $L=u-l$,

$$
\lambda=\frac{\varepsilon^2\pi^2}{L^2},\qquad
\phi(k)=\sqrt{2/L}\sin\frac{\pi(k-l)}L,\qquad
B=-\varepsilon^2\partial_k^2-(c_\kappa(k)\cdot\partial_q)^2,
\qquad S=B-\lambda\ge0.
\tag{1.3}
$$

Both actual height faces are Dirichlet. For the unitary phase Fourier transform with factor $(2\pi)^{-3/2}$, let $B_\eta=-\varepsilon^2\partial_k^2+|\eta\cdot c_\kappa(k)|^2$. Including underlying complex $L^2(dY)$ membership, the complete domains are

$$
\begin{aligned}
\mathcal Q
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H_0^1(I)\text{ a.e.},\quad
 \int_{\mathbb R^3}\!\int_I
  \left(\varepsilon^2|\partial_k\widehat\psi|^2
       +|\eta\cdot c_\kappa|^2|\widehat\psi|^2\right)dk\,d\eta<\infty\right\},\\
D(S)=D(B)
 &=\left\{\psi:\widehat\psi(\cdot,\eta)\in H^2(I)\cap H_0^1(I)\text{ a.e.},\quad
 \int_{\mathbb R^3}\|B_\eta\widehat\psi(\cdot,\eta)\|_{L^2(I)}^2d\eta<\infty\right\}.
\end{aligned}
\tag{1.4}
$$

Thus $\mathcal Q=D(S^{1/2})=D(B^{1/2})$. Every real phase frequency is retained. Actual competitors are unrestricted complex vectors in these domains; no real, odd, symmetric or isotropic phase-$H^1$ class is imposed.

**Definition 1.2 (raw source, field and actual units).** Let $p_t^B$ be the killed heat kernel of $B$ relative to raw measure, with source $o=(k_0,0)$. For $\tau>0$ set

$$
\begin{aligned}
W_\tau&=\int_\tau^\infty e^{\lambda t}p_t^B(o,\cdot)dt,&
\rho_\tau&=e^{\lambda\tau}p_\tau^B(o,\cdot),& SW_\tau&=\rho_\tau,\\
\int\rho_\tau dY&=e^{\lambda\tau}\mathbb P_{k_0}(\zeta>\tau),&
\int\phi(k)\rho_\tau(k,q)dk\,dq&=\phi(k_0).
\end{aligned}
\tag{1.5}
$$

These are distinct source charges, without survival normalization. The field uses the $B$ heat clock independently of $a$. Define

$$
\begin{aligned}
\mathfrak e_{g,\tau}[\psi]
 &=a\|S^{1/2}\psi\|_2^2-g\int W_\tau|\psi|^2dY,&
E_\tau(g)&=\inf_{\psi\in\mathcal Q,\ \|\psi\|_2=1}\mathfrak e_{g,\tau}[\psi],\\
\tau&=s^2,&g_s&=\chi_c s^3,& E_s&=E_{s^2}(\chi_c s^3),\\
\epsilon_c(s)&=s^2E_s,&r_s&=-\epsilon_c(s)/s^8=-E_s/s^6.
\end{aligned}
\tag{1.6}
$$

P Propositions 70.2 and 75.2 supply boundedness of $W_\tau$ at each positive cutoff, operator domain exactly $D(S)$ for $aS-gW_\tau$, essential spectrum $[0,\infty)$ and an attained finite negative bottom for each positive $g,\tau$. They do not assert a uniform multiplier bound as $\tau\downarrow0$. The unscaled energy $E_s$, rescaled energy $\epsilon_c(s)$ and positive scale ratio $r_s$ are distinct quantities. None denotes quantum acquired mass or machine-learning error.

## 2. Exact microscopic dictionary and conditional analytic antecedents

**Definition 2.1 (chart, moving faces and exact shear).** For $\xi=(r,y,z,w)$ put

$$
\begin{aligned}
\Xi_s\xi&=(k_0+\varepsilon sr,
       s c_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w),\\
I_s&=((l-k_0)/(\varepsilon s),(u-k_0)/(\varepsilon s)),&\Omega_s&=I_s\times\mathbb R^3,\\
\mathcal U_s\psi&=(j_0s^7)^{1/2}\psi\circ\Xi_s,&\mathcal Q_s&=\mathcal U_s\mathcal Q,\\
X&=\partial_r,&Y_s&=\partial_y+r\partial_z+\frac{r^2}{2(1+\beta_sr)}\partial_w,\\
\beta_s&=\nu s,&b_s[F]&=\|XF\|_2^2+\|Y_sF\|_2^2,&U_s&=s^5W_{s^2}\circ\Xi_s.
\end{aligned}
\tag{2.1}
$$

The raw Jacobian is exactly $j_0s^7$. The map $\mathcal U_s$ is unitary onto $L^2(\Omega_s,d\xi)$. The Friedrichs operator $A_s$ of $b_s$ has domain $\mathcal U_sD(S)$, and

$$
\begin{aligned}
C_s&=A_s-\lambda s^2=s^2\mathcal U_s S\mathcal U_s^{-1}\ge0,\\
q_s^c[F]&=a b_s[F]-\chi_c\int U_s|F|^2-a\lambda s^2\|F\|_2^2,\\
q_s^c[\mathcal U_s\psi]&=s^2\mathfrak e_{g_s,s^2}[\psi],\qquad
\inf_{\|F\|_2=1}q_s^c[F]=\epsilon_c(s).
\end{aligned}
\tag{2.2}
$$

The native heat and rescaled source retain the exact density correspondence of P Proposition 81.2:

$$
\begin{aligned}
P_s(t;\eta,\xi)&=j_0s^7p_{s^2t}^B(\Xi_s\eta,\Xi_s\xi),\\
U_s&=j_0^{-1}\int_1^\infty e^{\lambda s^2t}P_s(t;0,\cdot)dt,\\
(A_s-\lambda s^2)U_s&=s^7\rho_{s^2}\circ\Xi_s,\qquad
j_0s^7\rho_{s^2}\circ\Xi_s\longrightarrow k_1
\quad\text{in }L^1\text{ and locally uniformly}.
\end{aligned}
\tag{2.2a}
$$

The limiting source for $V$ has Lebesgue mass $1/j_0$; its native raw-source mass is one. The amplitude factor remains the square root of the raw Jacobian.

For the phase triple $\mathbf z=(y,z,w)$ define

$$
L_s=\begin{pmatrix}1&\beta_s&0\\0&1&2\beta_s\\0&0&1\end{pmatrix},\qquad
\mathscr L_s(r,\mathbf z)=(r,L_s\mathbf z),\qquad
\mathcal T_sF=F\circ\mathscr L_s,\qquad
\widetilde U_s=U_s\circ\mathscr L_s.
\tag{2.3}
$$

The shear has determinant one, fixes the source and preserves both moving height faces. P Definition 97.1 gives, on the entire transported closed form domain,

$$
\widetilde b_s[f]:=b_s[\mathcal T_s^{-1}f]
 =\int_{\Omega_s}\left(|Xf|^2+(1+\beta_sr)^{-2}|Yf|^2\right)d\xi,
\qquad Y=\partial_y+r\partial_z+\tfrac12r^2\partial_w.
\tag{2.4}
$$

This is the same native problem under an exact unitary change of variables. All comparisons on $\mathbb R^4$ use zero extension from $\Omega_s$, preserving both Dirichlet deaths.

**Definition 2.2 (canonical source and threshold mode).** Use the Engel product, Haar measure and automorphic dilations

$$
\begin{aligned}
(r,y,z,w)(r',y',z',w')
 &=(r+r',y+y',z+z'+ry',w+w'+rz'+r^2y'/2),\\
\delta_R(r,y,z,w)&=(Rr,Ry,R^2z,R^3w),\qquad Q=7.
\end{aligned}
\tag{2.5}
$$

Let $b[f]=\|Xf\|_2^2+\|Yf\|_2^2$, let $\mathcal Q_E$ be the complex compact smooth core closure in $\|f\|_2^2+b[f]$, and let $\mathcal E=-X^2-Y^2$ denote its Friedrichs operator. Write $P_t=e^{-t\mathcal E}$, $k_t(\xi)=p_E(t;0,\xi)$ and

$$
\begin{aligned}
V&=j_0^{-1}\int_1^\infty k_tdt,&\mathcal EV&=j_0^{-1}k_1,\\
C_*&=\sup_{0\ne f\in\mathcal Q_E}\frac{\int V|f|^2}{b[f]}\in(0,\infty),&
\chi&=\chi_c=a/C_*,&\gamma&=\chi/a,\\
h[f]&=a b[f]-\chi\int V|f|^2\ge0,&
H_c&=a\mathcal E-\chi V,\\
p&=\Phi_c>0,&\|p\|_2&=1,&\ker H_c&=\mathbb Cp,&\mathcal Ep&=\gamma Vp.
\end{aligned}
\tag{2.6}
$$

P §§82–88 supply a conservative, positive, symmetric canonical heat, the absence of an $L^2$ kernel for $\mathcal E$, and the following precise antecedents. If $d_E$ is its proper control distance and $N=\max(|r|,|y|,|z|^{1/2},|w|^{1/3})$, then

$$
p_E(t;\eta,\xi)\le Ct^{-7/2}e^{-c d_E(\eta,\xi)^2/t},\qquad
0<V\le C(1+N)^{-5}.
\tag{2.7}
$$

The critical mode belongs to $D(\mathcal E)$, and its reconstruction is

$$
p=\gamma\int_0^\infty P_t(Vp)dt\quad\text{in }L^2.
\tag{2.8}
$$

The zero-energy reconstruction on the multiplier right sides in P Theorem 87.2 is compact into $L^2$ with range in $D(\mathcal E)$; it is not a bounded inverse of $\mathcal E$ on all $L^2$. P Theorem 106.1 supplies

$$
\begin{gathered}
rp\in\mathcal Q_E,\qquad h[rp]=a,\qquad
\int r^2(p^2+|Xp|^2+|Yp|^2)d\xi<\infty,\\
\sigma(r,y,z,w)=(-r,y,-z,w),\qquad p\circ\sigma=p,\quad V\circ\sigma=V.
\end{gathered}
\tag{2.9}
$$

For a fixed smooth even height cutoff $\eta$, one on $[-1,1]$, zero outside $[-2,2]$, its scaled cutoff $\eta_R(r)=\eta(r/R)$ satisfies

$$
\int|\eta_R'|^2p^2=o(R^{-4}).
\tag{2.10}
$$

Supported canonical form vectors are native admissible when their height support lies between both faces: approximate by the canonical compact core, multiply by the height cutoff, and use the equivalence of (2.4) and $b$ on that strip. No separate phase derivative is needed. Canonical local compactness and the corresponding native core and both-face heat assertions retain their supplied scopes. The underlying cited heat, localization and library literature remain conditional; none is independently authenticated by this volume.

## 3. Every coefficient and the homogeneous response

**Definition 3.1 (one common bridge).** Let $H_v$ be the height bridge with generator $\partial_r^2$ from $0$ to $r$ in time $t$. With $\mathbf z=(y,z,w)$ set

$$
\begin{aligned}
u(h)&=(1,h,h^2/2),& S_t&=\sup_{0\le v\le t}|H_v|,\\
M_j&=\int_0^t H_v^j u(H_v)u(H_v)^{\mathsf T}dv\quad(j=0,1,2),\\
\gamma_M(\mathbf z)&=(4\pi)^{-3/2}(\det M)^{-1/2}
 e^{-\mathbf z^{\mathsf T}M^{-1}\mathbf z/4},&
h_t(r)&=(4\pi t)^{-1/2}e^{-r^2/(4t)},\\
p_0(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[\gamma_{M_0}(\mathbf z)]=k_t(r,\mathbf z),\\
p_1(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[-2D\gamma_{M_0}(\mathbf z)[M_1]],\\
p_2(t;r,\mathbf z)&=h_t(r)\mathbb E_{0,r}^t[
 3D\gamma_{M_0}(\mathbf z)[M_2]+2D^2\gamma_{M_0}(\mathbf z)[M_1,M_1]],\\
V_j&=j_0^{-1}\int_1^\infty p_j(t;\cdot)dt\quad(j=1,2),&
V_{\rm t}&=j_0^{-1}\int_1^\infty t k_tdt>0.
\end{aligned}
\tag{3.1}
$$

Here $D$ differentiates with respect to the positive matrix; $u(h)$ is the vector in the first line. The same bridge supplies every matrix, and the same source supplies every field. P Theorem 107.2 supplies absolute convergence, parity and the full-space expansion

$$
\begin{gathered}
\widetilde U_s=V+\beta_sV_1+\beta_s^2V_2+\lambda s^2V_{\rm t}+\mathcal R_s,
\qquad \|\mathcal R_s\|_\infty\le Cs^{5/2},\\
|V_1(r,\mathbf z)|\le C(1+|r|)^{-4},\qquad
|V_2(r,\mathbf z)|+V_{\rm t}(r,\mathbf z)\le C(1+|r|)^{-3},\\
V_j\circ\sigma=(-1)^jV_j,\qquad V_{\rm t}\circ\sigma=V_{\rm t}.
\end{gathered}
\tag{3.2}
$$

This includes all real phases, both moving faces, the original infinite-time field and zero extension outside $\Omega_s$. It is not inferred here from a local heat expansion. The heat clock is still $B$; $a$ has not entered any of (3.1).

**Definition 3.2 (response Hilbert space and full coefficients).** Polarized forms are conjugate linear in the first slot. Let $\dot{\mathcal H}_-$ be the completion of the real $\sigma$-odd compact smooth core in $\sqrt b$. R Theorems 4.1, 5.1 and 5.3 supply the bounds and response

$$
\begin{gathered}
V_1^2\le K_1V,\quad V_2^2\le K_2V,\quad V_{\rm t}^2\le K_{\rm t}V,\qquad
\int V^{1/2}|u|^2\le\Gamma b[u]\quad(u\in\mathcal Q_E),\\
h[u]\ge a\theta b[u]\quad\text{if }b(p,u)=0,\qquad \theta>0,\\
\ell(u)=2a\int r(Yp)(Yu)+\chi\int V_1pu,\qquad
h(\Psi,u)=\ell(u)\quad(u\in\dot{\mathcal H}_-),\\
D_{\rm resp}=h[\Psi]=\sup_{0\ne u\text{ odd compact smooth}}\frac{\ell(u)^2}{h[u]}<\infty.
\end{gathered}
\tag{3.3}
$$

The gap is in horizontal energy, not in $L^2$. Reflection invariance of $b$ and evenness of $p$ give $b(p,u)=0$ on the odd core. Hence $a\theta b\le h\le ab$ there, so $h$ is a genuine Hilbert norm on its completion. To make the response pairings explicit, put $S_1=\int(V_1^2/V)p^2\le K_1$. Cauchy–Schwarz and $\int V|u|^2\le C_*b[u]$ give

$$
|\ell(u)|\le\left(2a\sqrt A+\chi\sqrt{C_*S_1}\right)\sqrt{b[u]},
\qquad
D_{\rm resp}\le\frac{(2a\sqrt A+\chi\sqrt{C_*S_1})^2}{a\theta}.
\tag{3.3a}
$$

Here $A=\int r^2|Yp|^2$ is finite by (2.9). Thus every response pairing extends continuously. In particular $rp$ is an element of this real completion by parity averaging its canonical core approximants. The abstract vector $\Psi$ has no asserted $L^2$, canonical form-domain or native operator-domain representative.

Set

$$
\begin{aligned}
A&=\int r^2|Yp|^2,&B_1&=\int rV_1p^2,&C_2&=\int V_2p^2,&T&=\int V_{\rm t}p^2>0,\\
K_{\rm base}&=3aA-\chi C_2,&D_{\rm clock}&=a+\chi T,&
t_0&=2A+(\chi/a)B_1=\ell(rp)/a,\\
C_{\rm resp}&=\nu^2(K_{\rm base}-D_{\rm resp})-\lambda D_{\rm clock},\\
C_{\rm aff}(t)&=\nu^2\{a t^2-(4aA+2\chi B_1)t+K_{\rm base}\}
                 -\lambda(a+\chi T),\qquad t\in\mathbb R,\\
C_{108}&=C_{\rm aff}(1)
 =\nu^2\{a(1-A)-\chi(C_2+2B_1)\}-\lambda(a+\chi T).
\end{aligned}
\tag{3.4}
$$

Every integral is finite by (2.9), (3.2) and (3.3). The $C_2+2B_1$ term is exactly P (108.2)'s integral of $(V_2+2rV_1)p^2$. Thus (3.4) retains the entire rational kinetic correction, raw-source factor, time-weighted field and threshold subtraction. R Theorem 7.1 supplies this affine coefficient and its non-strict comparison with the response. The next sections prove the strict improvement.

## 4. A free fundamental solution used only in the proof

**Lemma 4.1 (positive homogeneous auxiliary kernel).** On the canonical group define

$$
\mathcal G(\xi)=\int_0^\infty k_t(\xi)dt\quad(\xi\ne0).
\tag{4.1}
$$

It is positive, locally integrable on the whole group, smooth away from $0$, and

$$
\mathcal E\mathcal G=\delta_0,\qquad
\mathcal G(\delta_R\xi)=R^{-5}\mathcal G(\xi),\qquad
0<\mathcal G(\xi)\le C d_E(0,\xi)^{-5}.
\tag{4.2}
$$

In particular $\mathcal G(r,\mathbf z)\le C|r|^{-5}$ for $r\ne0$.

Proof. The left invariant fields in (2.5) have degree one under $\delta_R$, and Haar measure has degree seven. Unitary dilation of the Friedrichs form therefore gives

$$
k_t(\delta_R\xi)=R^{-7}k_{t/R^2}(\xi).
\tag{4.3}
$$

The Gaussian estimate (2.7), with $D=d_E(0,\xi)>0$, gives

$$
\int_0^\infty k_t(\xi)dt
 \le C\int_0^\infty t^{-7/2}e^{-cD^2/t}dt
 =C D^{-5}\int_0^\infty v^{-7/2}e^{-c/v}dv<\infty.
\tag{4.4}
$$

Both ends of the last integral converge. Positivity of the heat makes the result strictly positive. Changing time in (4.3) gives the homogeneity in (4.2).

The control metric is left invariant and homogeneous. Its proper unit ball has finite positive Haar volume $v_E$, and hence its radius-$\rho$ ball has volume $v_E\rho^7$. On annuli of radii $2^{-j-1}$ and $2^{-j}$ the bound in (4.2) has integral at most $C2^{-2j}$. Summing proves integrability at zero. Away from zero it is bounded on compact sets, so it defines a distribution. This also proves

$$
\int_{d_E(0,\xi)<1}\mathcal G(\xi)d\xi<\infty,
\qquad \sup_{d_E(0,\xi)\ge1}\mathcal G(\xi)<\infty.
\tag{4.5}
$$

For $\varphi\in C_c^\infty$, integrate the heat equation between $\epsilon$ and $T$:

$$
\int_\epsilon^T\!\int k_t\mathcal E\varphi\,d\xi\,dt
 =\int k_\epsilon\varphi\,d\xi-\int k_T\varphi\,d\xi.
\tag{4.6}
$$

Near time zero, absolute integrability on the left follows from conservativity and $\|\mathcal E\varphi\|_\infty$. At large time it follows from the uniform $Ct^{-7/2}$ bound and $\|\mathcal E\varphi\|_1$. Thus the time integral can be identified with $\langle\mathcal G,\mathcal E\varphi\rangle$. The first term on the right tends to $\varphi(0)$ by the heat initial condition, and the second tends to zero by $Ct^{-7/2}\|\varphi\|_1$. This proves the distributional fundamental-solution identity.

The brackets $[X,Y]=\partial_z+r\partial_w$ and $[X,[X,Y]]=\partial_w$, together with $X,Y$, span everywhere. The supplied hypoellipticity of this canonical operator makes its distributional harmonic solution have a smooth representative off the source. Use that representative for $\mathcal G$. Its upper bound extends from almost every point to every point off the source by continuity of the control distance and of the representative. Likewise, for any fixed $t>0$, the semigroup property and positivity give the pointwise raw-integral bound $\mathcal G\ge\int_t^{2t}k_vdv$. The latter is positive and continuous, so the same bound extends everywhere to the smooth representative. Thus it remains strictly positive. Homogeneity also extends from its distributional equality to this representative. Finally the height component of a controlled path changes at speed at most its control speed, so $d_E(0,(r,\mathbf z))\ge|r|$, with the stated normalization. This proves the height bound. The kernel $\mathcal G$ is auxiliary; it does not replace $V$, remove the native cutoff, or assert a semibounded unregularized native interaction. $\square$

## 5. Distributional dilation of the reconstructed positive mode

**Lemma 5.1 (convolution orientation and positive source mass).** Let $f=Vp$ and $m=\int f$. Then $f\in L^1\cap L^2$, $0<m<\infty$, and

$$
p(\xi)=\gamma\int\mathcal G(\eta^{-1}\xi)f(\eta)d\eta
\quad\text{for a.e. }\xi.
\tag{5.1}
$$

Proof. The boxes $\{N\le R\}$ have volume $16R^7$. Since $V\le C(1+N)^{-5}$, its squared integral over successive dyadic annuli is bounded by a summable multiple of $2^{-3j}$. Thus $V\in L^2\cap L^\infty$. Cauchy–Schwarz with $p\in L^2$ gives $f\in L^1$, while boundedness of $V$ gives $f\in L^2$. Positivity of $V,p$ gives $m>0$.

The fields are left invariant. With source first and output second, left translation gives

$$
p_E(t;\eta,\xi)=k_t(\eta^{-1}\xi).
\tag{5.2}
$$

Indeed a process started at $\eta$ is the left translate by $\eta$ of the process from the identity. Haar measure is unchanged. Symmetry of the selfadjoint heat is consistent with $k_t(g)=k_t(g^{-1})$, so (5.2) is also the kernel of $P_tf$ integrated over its input $\eta$.

On finite time intervals Tonelli applies to the nonnegative kernel and $f$. The positive integrals $\int_0^T P_tfdt$ increase pointwise as $T\to\infty$ and converge in $L^2$ by (2.8). An almost everywhere convergent subsequence of this $L^2$ convergence identifies their monotone pointwise limit with $p/\gamma$. A second application of Tonelli gives (5.1). This uses precisely the supplied reconstruction on $Vp$, without a bounded inverse assertion on general $L^2$. $\square$

**Lemma 5.2 (a distributional limit with local mass control).** For $R\ge1$ let

$$
p_R(\xi)=R^5p(\delta_R\xi),\qquad
f_R(\eta)=R^7f(\delta_R\eta).
\tag{5.3}
$$

Then

$$
p_R\longrightarrow\gamma m\mathcal G
\quad\text{in distributions on }\mathbb R^4,
\qquad
\sup_{R\ge1}\int_K p_R<\infty
\quad\text{for every compact }K.
\tag{5.4}
$$

Proof. The group automorphism $\delta_R$, its Haar Jacobian $R^7$, and the homogeneity of $\mathcal G$ turn (5.1) exactly into

$$
p_R(\xi)=\gamma\int\mathcal G(\eta^{-1}\xi)f_R(\eta)d\eta.
\tag{5.5}
$$

The functions $f_R$ are nonnegative and have mass $m$. For each $\rho>0$,

$$
\int_{d_E(0,\eta)>\rho}f_R(\eta)d\eta
 =\int_{d_E(0,\eta)>R\rho}f(\eta)d\eta\longrightarrow0.
\tag{5.6}
$$

For a compact smooth test $\varphi$, define

$$
J_\varphi(\eta)=\int\mathcal G(\eta^{-1}\xi)\varphi(\xi)d\xi.
\tag{5.7}
$$

It is bounded uniformly in $\eta$: on $d_E(\eta,\xi)<1$ use $\|\varphi\|_\infty$ times the first bound in (4.5), changing variables by left translation; on the complement use the second bound times $\|\varphi\|_1$. The same bounds apply to $|\varphi|$, justifying all pairings in (5.5).

It is continuous as well. On a compact neighborhood of any $\eta$, change variables $\xi=\eta\zeta$. The supports of $\varphi(\eta\zeta)$ lie in one compact set of $\zeta$. Local integrability of $\mathcal G$ supplies an integrable majorant there, while continuity of $\varphi$ gives pointwise convergence. Dominated convergence proves continuity of (5.7). Therefore (5.6), boundedness and continuity at zero imply

$$
\langle p_R,\varphi\rangle
 =\gamma\int f_RJ_\varphi\longrightarrow\gamma mJ_\varphi(0)
 =\gamma m\langle\mathcal G,\varphi\rangle.
\tag{5.8}
$$

For completeness, this follows by choosing a small fixed ball on which $J_\varphi-J_\varphi(0)$ is uniformly small, and bounding the complementary integral by its uniform bound times the mass in (5.6). Signed and complex tests are handled by the same absolute bounds. No source moment or pointwise far-field expansion is needed.

Choose a nonnegative compact smooth $\varphi$ equal to one on $K$. Since $p_R\ge0$, (5.5) and the uniform bound on $J_\varphi$ give $\int_Kp_R\le\gamma m\|J_\varphi\|_\infty$ for all $R\ge1$. This proves the second claim. The dilated $p_R$ is not a normalized native eigenstate; (5.4) asserts neither a pointwise asymptotic nor global norm convergence. $\square$

## 6. Exclusion of every real affine height response

**Theorem 6.1 (strict nonaffinity).** Under Definitions 1.1–3.2, for every $t\in\mathbb R$,

$$
\Psi\ne t\,rp\quad\text{in }\dot{\mathcal H}_-.
\tag{6.1}
$$

In particular $\ell\ne0$ and $D_{\rm resp}>0$.

Proof. Suppose equality holds for some fixed real $t$. Testing its Riesz equation on any real odd $u\in C_c^\infty$ gives

$$
t\,h(rp,u)=\ell(u).
\tag{6.2}
$$

All pairings are legitimate in the completion because $rp\in\mathcal Q_E$ and has odd core approximation. The weak critical equation can be tested with $ru$. Since $Xr=1$ and $Yr=0$, subtraction gives

$$
\begin{aligned}
h(p,ru)&=a\int (Xp)(u+rXu)+a\int (Yp)rYu-\chi\int Vpru=0,\\
h(rp,u)&=a\int pXu-a\int(Xp)u=-2a\int(Xp)u.
\end{aligned}
\tag{6.3}
$$

The last integration by parts uses the compact support of $u$ and the weak derivative $Xp\in L^2$. It requires no operator-domain assertion for $rp$. The field $Y$ has zero divergence and $Yr=0$, so its response pairing is, distributionally,

$$
\ell(u)=-2a\langle rY^2p,u\rangle+\chi\int V_1pu.
\tag{6.4}
$$

Equations (6.2)–(6.4) imply

$$
2a(rY^2p-tXp)=\chi V_1p.
\tag{6.5}
$$

Initially this equality holds on odd compact tests. Each distribution in its residual is odd under $\sigma$: $X$ changes parity, $Y$ preserves parity, $r$ and $V_1$ are odd, and $p$ is even. An odd distribution vanishes on every even test. Splitting any compact test into its even and odd parts therefore extends (6.5) to all tests. No representative of a general abstract $\Psi$ has been assigned; only the proposed concrete equality was used.

The degree-one scaling of $X,Y$ and (5.3) turn (6.5) into

$$
2a(rY^2p_R-tXp_R)=\chi R(V_1\circ\delta_R)p_R.
\tag{6.6}
$$

For example $(Y^2p)(\delta_R\xi)=R^{-7}Y^2p_R(\xi)$ and the height at $\delta_R\xi$ is $Rr$, which gives exactly the factor $R$ on the right. These identities hold distributionally by change of variables.

On any compact $K\subset\{r>0\}$, write $r\ge c_K>0$. The full-space height bound (3.2) gives

$$
\sup_K R|V_1(\delta_R\xi)|\le CR(1+Rc_K)^{-4}=O_K(R^{-3}).
\tag{6.7}
$$

Lemma 5.2 bounds the local $L^1$ mass of the nonnegative $p_R$. Thus the right side of (6.6) tends to zero in $L^1(K)$. Differential operators with smooth coefficients act continuously on distributions. Passing to the limit (5.4), then canceling $\gamma m>0$, proves

$$
rY^2\mathcal G-tX\mathcal G=0\quad\text{on }\{r>0\}.
\tag{6.8}
$$

The fundamental solution is harmonic on that open set. Hence $Y^2\mathcal G=-X^2\mathcal G$, and (6.8) becomes

$$
r\partial_r^2\mathcal G+t\partial_r\mathcal G=0
\quad\text{on }\{r>0\}.
\tag{6.9}
$$

Only distributional convergence was used to reach this equation. Lemma 4.1 makes $\mathcal G$ smooth away from zero, so it is now an ordinary equation there.

Fix any nonzero phase triple $\mathbf z$. The function $g(r)=\mathcal G(r,\mathbf z)$ for $r>0$ is smooth, strictly positive and tends to zero at infinity by the height bound in Lemma 4.1. It is bounded as $r\downarrow0$, since $(0,\mathbf z)$ is away from the source and $\mathcal G$ is smooth there. Equation (6.9) says $(r^tg')'=0$. Its complete solutions are

$$
g(r)=
\begin{cases}
A_{\mathbf z}+B_{\mathbf z}r^{1-t},&t\ne1,\\
A_{\mathbf z}+B_{\mathbf z}\log r,&t=1.
\end{cases}
\tag{6.10}
$$

When $t<1$, decay at infinity forces $B_{\mathbf z}=0$ and then $A_{\mathbf z}=0$. For the exceptional integration case $t=1$, the logarithmic growth gives the same conclusion. When $t>1$, decay forces $A_{\mathbf z}=0$, while boundedness at zero forces $B_{\mathbf z}=0$. Every real case contradicts strict positivity. This proves (6.1), including $t=0$. If $\ell=0$, uniqueness of its Riesz representative would give $\Psi=0$, the excluded case $t=0$. The Hilbert norm then gives $D_{\rm resp}>0$. $\square$

## 7. The strict projection identity and complete coefficient gap

**Theorem 7.1 (positive distance from the entire affine line).** Define

$$
\Delta_{\rm aff}=h[\Psi-t_0rp].
\tag{7.1}
$$

Then

$$
\begin{gathered}
\Delta_{\rm aff}=D_{\rm resp}-a t_0^2>0,\\
h[\Psi-trp]=\Delta_{\rm aff}+a(t-t_0)^2\quad(t\in\mathbb R),\\
C_{\rm resp}=\min_{t\in\mathbb R}C_{\rm aff}(t)-\nu^2\Delta_{\rm aff}
 <\min_{t\in\mathbb R}C_{\rm aff}(t)\le C_{108},\\
C_{\rm aff}(t)-C_{\rm resp}
 =\nu^2\{\Delta_{\rm aff}+a(t-t_0)^2\},\\
C_{108}-C_{\rm resp}=\nu^2\{\Delta_{\rm aff}+a(t_0-1)^2\}>0.
\end{gathered}
\tag{7.2}
$$

Proof. Extend the response equation continuously from the odd core to $rp$. Since $h[rp]=a$ and $h(\Psi,rp)=\ell(rp)=a t_0$, the vector $\Psi-t_0rp$ is $h$-orthogonal to $rp$. The Hilbert-space Pythagorean identity gives the first two equalities in (7.2). Theorem 6.1 excludes its being zero, so its squared Hilbert norm is strictly positive. Completing the full scalar polynomial in (3.4) gives

$$
C_{\rm aff}(t)
 =\nu^2(K_{\rm base}-a t_0^2)-\lambda D_{\rm clock}
    +a\nu^2(t-t_0)^2.
\tag{7.3}
$$

Insert $D_{\rm resp}=a t_0^2+\Delta_{\rm aff}$ into the full response coefficient. Since $\nu>0$, all assertions follow. The time-weighted and threshold clock contributions remain present in each complete coefficient; they cancel only when taking this exact difference. Every quantity belongs to the same original realization. $\square$

## 8. Fixed complex affine slopes

**Theorem 8.1 (complex affine coefficient at a fixed slope).** Fix $z_0\in\mathbb C$, independent of $s$. Set $R_s=s^{-1/2}$ and

$$
f_s^{z_0}=\eta_{R_s}(1+\beta_s z_0r)p,\qquad
Z_s^{z_0}=\mathcal T_s^{-1}f_s^{z_0}/\|f_s^{z_0}\|_2.
\tag{8.1}
$$

For all sufficiently small original real $s>0$, these are normalized vectors in the full native complex form domain, and

$$
\begin{aligned}
\lim_{s\downarrow0}\frac{q_s^c[Z_s^{z_0}]}{s^2}
 &=C_{\rm aff}^{\mathbb C}(z_0)\\
 &=\nu^2\{a|z_0|^2-2a t_0\operatorname{Re}z_0+K_{\rm base}\}
       -\lambda D_{\rm clock}\\
 &=\min_{t\in\mathbb R}C_{\rm aff}(t)+a\nu^2|z_0-t_0|^2,\\
C_{\rm aff}^{\mathbb C}(z_0)-C_{\rm resp}
 &=\nu^2\{\Delta_{\rm aff}+a|z_0-t_0|^2\}>0.
\end{aligned}
\tag{8.2}
$$

Proof. Since $sR_s\to0$, the height support lies strictly between both moving faces. The strip core approximation in Definition 2.2, multiplication by the smooth height factor, and unitarity give admissibility. The norm has the exact parity identity

$$
\|f_s^{z_0}\|_2^2=\int\eta_{R_s}^2p^2
       +\beta_s^2|z_0|^2\int r^2\eta_{R_s}^2p^2\longrightarrow1.
\tag{8.3}
$$

Here the real linear term vanishes under $\sigma$. Testing the weak critical equation with the square of a real height multiplier gives $h[g p]=a\int|g'|^2p^2$; applying this separately to the real and imaginary parts also gives this identity for a complex height multiplier. Thus

$$
\begin{aligned}
h[f_s^{z_0}]
 &=a\int|\eta_{R_s}'|^2p^2
   +a\beta_s^2|z_0|^2\int|\eta_{R_s}+r\eta_{R_s}'|^2p^2\\
 &=a\beta_s^2|z_0|^2+o(s^2).
\end{aligned}
\tag{8.4}
$$

The cross term is odd. The first integral is $o(s^2)$ by (2.10). The second multiplier is uniformly bounded, tends pointwise to one, and is dominated against $p^2$.

On this strip $|\beta_sr|\to0$ uniformly. The exact rational difference times the squared amplitude has expansion

$$
\bigl((1+\beta_sr)^{-2}-1\bigr)|1+\beta_s z_0r|^2
 =-2\beta_sr+(3-4\operatorname{Re}z_0)\beta_s^2r^2
       +O_{z_0}(|\beta_sr|^3).
\tag{8.5}
$$

Since $Y\eta_{R_s}=0$, its odd linear term integrates to zero against $\eta_{R_s}^2|Yp|^2$. The remainder integral is bounded by $C_{z_0}|\beta_s|^3R_s\int r^2|Yp|^2=o(s^2)$. The quadratic integral converges by (2.9). Consequently the rational kinetic correction is

$$
a\int\bigl((1+\beta_sr)^{-2}-1\bigr)|Yf_s^{z_0}|^2
 =a(3-4\operatorname{Re}z_0)\beta_s^2A+o(s^2).
\tag{8.6}
$$

The full potential expansion, with exactly the fields in (3.1), gives

$$
\int(\widetilde U_s-V)|f_s^{z_0}|^2
 =\beta_s^2(C_2+2\operatorname{Re}z_0 B_1)
       +\lambda s^2T+o(s^2).
\tag{8.7}
$$

Indeed the base and quadratic-amplitude $V_1$ terms are odd; its linear-amplitude term gives $2\operatorname{Re}z_0 B_1$. For $V_2$ and $V_{\rm t}$ the linear-amplitude terms are odd, while the quadratic-amplitude corrections are $O_{z_0}(s^4)\int r^2p^2$, using boundedness of those fields. Dominated convergence handles their base integrals and the displayed $rV_1$ integral. The uniform remainder is at most $Cs^{5/2}\|f_s^{z_0}\|_2^2=o(s^2)$.

Retain the original subtraction $-a\lambda s^2\|f_s^{z_0}\|_2^2$. Combining (8.4), (8.6) and (8.7), then normalizing by (8.3), gives the first formula in (8.2), since $4aA+2\chi B_1=2a t_0$. The numerator is already $O(s^2)$, so a norm tending to one suffices; no missing second-order norm term remains. Completing the complex scalar square gives the last two formulas. The estimate is for each fixed complex slope. It supplies no uniform assertion for slopes depending on $s$ and diverging as $s\downarrow0$, and restricts no actual competitor to an affine family. $\square$

## 9. Matching actual energy and exact conditional consequences

**Proposition 9.1 (credited actual-state bridges).** R Theorems 6.1, 9.1 and 10.1 supply, on exactly the domains above,

$$
\begin{gathered}
\limsup_{s\downarrow0}E_s\le C_{\rm resp},\qquad
q_s^c[F]\ge-Cs^2\|F\|_2^2\quad(F\in\mathcal Q_s\text{ complex}),\\
\operatorname{dist}(\mathcal U_{s_n}\psi_{s_n},\mathcal O_c)\to0
 \ \Longrightarrow\ \liminf_nE_{s_n}\ge C_{\rm resp},\qquad
\mathcal O_c=\{e^{i\theta}p:\theta\in\mathbb R\}.
\end{gathered}
\tag{9.1}
$$

The last implication requires a prescribed sequence $s_n\downarrow0$ and actual normalized complex ground states $\psi_{s_n}\in D(S)$ on the exact path (1.6). P Theorem 105.1, with these same actual-state hypotheses, supplies

$$
r_{s_n}\to\infty
 \quad\Longleftrightarrow\quad
\operatorname{dist}_{L^2}(\mathcal U_{s_n}\psi_{s_n},\mathcal O_c)\to0.
\tag{9.2}
$$

P Proposition 100.1 gives $E_s\le-cs^6$, hence $r_s\ge c>0$, for small $s$. Its direction is an upper bound on energy, not a matching lower bound.

These results include the original lower arguments. R's upper construction uses compact odd approximants of $\Psi$, not $\Psi$ itself as an $L^2$ trial. Its full-domain lower estimate localizes a general complex vector, uses the compact horizontal-energy gap on its complement to $p$, and retains the nonnegative native $C_s$ outside the inner strip. Its unit-profile lower implication completes the full complex response square after obtaining an $O(s^2)$ complement energy; the strip limit is taken before the auxiliary strip parameter tends to zero. Thus none of (9.1) is merely an affine trial assertion.

P's equivalence depends on its finite-native resolvent estimate and actual negative attainment. It is not an assertion for arbitrary near-minimizers. P Theorem 90.1's weaker critical near-minimizer class has the entire weak disk $\{cp:|c|\le1\}$, including lost mass, and cannot supply the unit norm in (9.1) or (9.2).

**Theorem 9.2 (matching limit, with its existing proof credited).** Under the supplied bridges,

$$
\lim_{s\downarrow0}E_s=\min(0,C_{\rm resp}).
\tag{9.3}
$$

Proof. This is R Theorem 11.1. Its inference can be stated briefly to make the lower requirement explicit. The upper response construction and actual negativity give $\limsup E_s\le\min(0,C_{\rm resp})$. The lower estimate in (9.1) bounds $E_s$ below. If a lower subsequential limit $L$ were strictly below $\min(0,C_{\rm resp})$, then $L<0$ and $r_s=-E_s/s^6\to\infty$ along that sequence. Negative attainment supplies actual normalized states in $D(S)$. Equivalence (9.2) gives global unit-orbit convergence, so the last implication in (9.1) forces $L\ge C_{\rm resp}$, a contradiction. This is the existing matching argument, not a new matching conclusion from the present strictness proof alone. $\square$

**Corollary 9.3 (affine nonpositive boundary and every actual ground state).** For any actually admitted fixed datum, if

$$
\min_{t\in\mathbb R}C_{\rm aff}(t)\le0,
\tag{9.4}
$$

then $C_{\rm resp}<0$ and

$$
E_s\to C_{\rm resp},\qquad
\epsilon_c(s)=C_{\rm resp}s^2+o(s^2),\qquad
r_s\sim(-C_{\rm resp})s^{-6}\to\infty.
\tag{9.5}
$$

For every prescribed $s_n\downarrow0$ and every choice of actual normalized complex ground states in $D(S)$,

$$
\operatorname{dist}_{L^2}(\mathcal U_{s_n}\psi_{s_n},\mathcal O_c)\to0.
\tag{9.6}
$$

In particular the same implication holds if $C_{108}\le0$, including $C_{108}=0$, or if a fixed complex affine coefficient in (8.2) is nonpositive. No such datum is asserted to occur.

Proof. Theorem 7.1 makes (9.4) imply a strictly negative response. Theorem 9.2 then gives its negative unscaled energy limit; the exact unit identities (1.6) give (9.5). At each positive cutoff the bottom is attained in $D(S)$, and (9.2) applies to every chosen actual state on every prescribed sequence, giving (9.6). Since $\min_t C_{\rm aff}(t)\le C_{108}$ and is also at most each fixed complex affine coefficient, the additional implications follow. Negative affine coefficients were already sufficient under R's non-strict comparison; the strict theorem additionally covers the affine zero boundary. $\square$

**Corollary 9.4 (separation of zero and nonnegative sets).** At an admitted datum with $C_{\rm resp}=0$,

$$
\min_t C_{\rm aff}(t)=\nu^2\Delta_{\rm aff}>0,
\qquad
C_{\rm aff}^{\mathbb C}(z_0)=\nu^2\{\Delta_{\rm aff}+a|z_0-t_0|^2\}>0
\quad(z_0\in\mathbb C\text{ fixed}).
\tag{9.7}
$$

More generally $C_{\rm resp}\ge0$ forces $\min_tC_{\rm aff}(t)>0$, hence $C_{108}>0$. Thus neither an affine minimum zero nor $C_{108}=0$ can be a response-zero witness. Conversely, positivity of every affine coefficient does not by itself imply nonnegative response.

Proof. These are direct consequences of the exact positive differences (7.2) and (8.2). They separate sets conditional on occurrence and prove no set nonempty. $\square$

**Proposition 9.5 (all supplied response-sign alternatives).** For each fixed admitted datum, R Theorem 11.2 retains the following precise consequences.

If $C_{\rm resp}<0$, (9.5)–(9.6) hold whether or not an affine coefficient is nonpositive.

If $C_{\rm resp}>0$, there are fixed-data constants $0<c\le B_*<\infty$ such that eventually

$$
c\le r_s\le B_*,\qquad -E_s=\Theta(s^6),\qquad
-\epsilon_c(s)=\Theta(s^8).
\tag{9.8}
$$

For every prescribed sequence and every actual normalized complex ground-state choice, every subsequence has a further weak global limit $cp$. For each fixed positive-measure compact $K$, all such limits obey

$$
\begin{gathered}
|c|^2\le(1+\gamma_K/\sqrt{B_*})^{-1}<1,\\
\liminf_n\operatorname{dist}(\mathcal U_{s_n}\psi_{s_n},\mathcal O_c)
 \ge\left(2-2(1+\gamma_K/\sqrt{B_*})^{-1/2}\right)^{1/2}>0.
\end{gathered}
\tag{9.9}
$$

Here, for the original long-time tensor $M=\int_I\phi^2c_\kappa c_\kappa^{\mathsf T}dk>0$, the source constants from P §§102–103 are

$$
\begin{aligned}
J_K&=\int_K Vp>0,& b_0&=\frac{e^{-3}}{24\pi\sqrt{\det M}},&
v_M&=\frac{28\pi}{3}\sqrt{\det M},\\
C_0&=\frac{\chi^2j_0}{a^{3/2}}b_0^2v_M,&
\gamma_K&=C_0\phi(k_0)^2J_K^2>0.
\end{aligned}
\tag{9.10}
$$

No exact finer coefficient, replacement actual profile or centered crossover is identified.

If $C_{\rm resp}=0$, the supplied assertions remain only

$$
E_s\to0,\qquad c\le r_s=o(s^{-6}).
\tag{9.11}
$$

Bounded, divergent or mixed subsequential $r_s$ behavior remains undecided. Equivalence (9.2) still applies to every actual sequence, but (9.11) does not choose its branch. In particular (9.7) is no proof of actual profile failure.

Proof. The negative case follows from (9.3) and (9.2). For positive response, absence of an eventual finite upper bound on $r_s$ would supply a sequence tending to zero along which $r_s\to\infty$. Choosing actual ground states and using (9.2) and (9.1) would give $\liminf E_s\ge C_{\rm resp}>0$, contradicting actual negativity. Thus $r_s\le B_*$ eventually. The independent macroscopic upper direction gives the lower bound $r_s\ge c$, hence (9.8). The compact-charge shell argument in P Theorems 102.2 and 103.1 supplies exactly (9.9) with (9.10); its mass escapes each fixed microscopic compact set, so a local weak profile is not a global unit profile. At response zero, (9.3), (1.6) and the same macroscopic direction give (9.11). A vanishing unscaled energy does not decide its size after division by $s^6$. These are the existing conditional alternatives, retained with their actual-state hypotheses. $\square$

## 10. Canonical margin and the unchanged full decision target

**Proposition 10.1 (canonical strict identity without absolute sign).** Define

$$
\begin{aligned}
W&=j_0V,&W_j&=j_0V_j,&W_{\rm t}&=j_0V_{\rm t},&\overline C&=j_0C_*,\\
G_{108}&=1-A-(\chi/a)(C_2+2B_1),&
G_{\rm resp}&=(K_{\rm base}-D_{\rm resp})/a,\\
\overline D&=1+(\chi/a)T>1,&\delta_{\rm aff}&=\Delta_{\rm aff}/a>0.
\end{aligned}
\tag{10.1}
$$

The fields $W,W_j,W_{\rm t}$, $\overline C$, $p$, $\Psi$, $t_0$ and $\delta_{\rm aff}$ are canonical, and

$$
\begin{gathered}
\frac{C_{108}}a=\nu^2G_{108}-\lambda\overline D,\qquad
\frac{C_{\rm resp}}a=\nu^2G_{\rm resp}-\lambda\overline D,\\
G_{\rm resp}=G_{108}-(t_0-1)^2-\delta_{\rm aff}
 <G_{108}-(t_0-1)^2\le G_{108},\\
\frac{\min_tC_{\rm aff}(t)}a
 =\nu^2\{G_{108}-(t_0-1)^2\}-\lambda\overline D.
\end{gathered}
\tag{10.2}
$$

Proof. Removing $1/j_0$ from the fixed canonical heat integrals gives the displayed $W$ fields. The threshold quotient gives $\chi/a=j_0/\overline C$, so the normalized equation for $p$ has no original parameter. The response form and functional are both $a$ times canonical objects; hence their Riesz vector is canonical and $\Delta_{\rm aff}/a$ is canonical. This is R Proposition 12.1's normalization, with the strictly positive margin supplied by Theorem 7.1. Dividing (7.2) by $a\nu^2$ gives (10.2). $\square$

**Definition 10.2 (original goal retained without weakening).** The full target is to determine the signs of the complete specified $C_{108}$, and of the complete homogeneous-response $C_{\rm resp}$, across the original admitted signed-$\kappa$, interval, interior-pole and jointly realized rational-field data; determine which negative, zero and positive cases actually occur; and decide the actual exact-critical $r_s$ and every-ground-state scale/profile behavior, with finer analysis at response zero if such data occur. The prescribed path, original complex competitor class, source and clock are exactly (1.1)–(2.4). A strict relative improvement, a new sufficient condition without an admitted witness, or a trial upper bound does not complete this target.

The present strict theorem leaves the absolute canonical quantities unevaluated. In particular it proves neither $G_{\rm resp}\le0$ nor its negation. The relevant ratio is the actual original

$$
\lambda/\nu^2=\pi^2d_0^2/(u-l)^2,
\tag{10.3}
$$

subject to every original interval, pole, probability and denominator restriction. Canonical normalization does not authorize freely varying this ratio. Signing a complete coefficient requires a same-realization comparison with its threshold $G/\overline D$; occurrence requires an original admitted datum or a proof of exclusion. No independent optimization of $A,B_1,C_2,T,D_{\rm resp}$ can substitute for their joint realization.

The positive relative margin does not sign either complete coefficient. The negative clock term alone also does not sign it. If an admitted datum has response zero, the finer actual energy relative to $s^6$ and the resulting behavior of $r_s$ remain necessary obligations. Positive-response data, if present, still require an exact finer coefficient, centered crossover and replacement actual profile. Neither a sign/equality occurrence nor a full original decision is established here.

## 11. Source attribution and interpretation limits

**Definition 11.1 (antecedents and scope of the increment).** P §§70–75 own the threshold field, distinct raw charges, full complex domains and fixed-positive-cutoff attainment; §§78 and 81 own the privileged chart, $j_0$ and exact conjugacy. P §§82–88 own the canonical heat, geometry, integrated tails, compactness, reconstruction and simple positive critical mode. P §§89–91 distinguish tangent onset and the native weak-profile disk from actual selection. P §§92–96 own the observation, infinite-fibre, quantum and analytic-preparation boundaries.

P §97 owns the exact rational shear and common-bridge comparison; Theorem 98.1 owns the earlier $O(s^{2/3})$ native lower error; Proposition 100.1 owns the macroscopic one-sided direction. P §§102–105 own compact-charge shell control, the bounded-$r$ defect, global finite-native weighted-resolvent reconstruction and the actual scale/no-loss equivalence. P §§106–108 own the weighted mode, involution parity, cutoff error, complete common-bridge expansion and complete original affine coefficient.

R Theorems 4.1, 5.1 and 5.3 own the coefficient multipliers, compact horizontal-energy gap and homogeneous Riesz response. R Theorems 6.1 and 7.1 own corrected-core recovery, the full real affine polynomial and non-strict square identities. R §§8–11 own the full-domain $O(s^2)$ lower estimate, actual unit-profile lower implication, matching energy and sign-conditional alternatives; R §§12–13 own the canonical normalization and its unresolved sign and realization boundaries.

The additional deductions proved here are the distributional dilation of the reconstructed source, exclusion of every affine real response, strict Hilbert projection distance, complete coefficient gap, fixed complex-slope refinement and their stated strict-boundary consequences. Heat equation testing, Tonelli, Cauchy–Schwarz, Haar changes of variables, distributional convergence, dominated convergence, an elementary ordinary differential equation and Hilbert-space projection are classical intermediate tools. No approval or authorial authority is a proof premise. This volume makes no worldwide originality or literature-absence claim.

The cited Colin de Verdière–Hillairet–Trélat heat and localization results, Coulhon–Sikora Gaussian implication and Fischer–Ruzhansky Young inequality retain exactly the conditional correspondences supplied in P and R. No unlisted antecedent is silently added, and no local heat theorem is promoted to a global integrated-field theorem here. This is ordinary reference mathematics, without Lean, kernel or frozen certification or executed mathematical/numerical validation.

**Definition 11.2 (native and interpretive boundaries).** The original-coordinate transport remains

$$
\begin{gathered}
J_\kappa=\operatorname{diag}(1,1,\kappa),\qquad D=\kappa x,\\
\psi^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1/2}\psi(k,q),\qquad
W_\tau^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1}W_\tau(k,q),\qquad
g_{\rm orig}=|\kappa|g.
\end{gathered}
\tag{11.1}
$$

The transported long-time tensor is $J_\kappa M J_\kappa^{\mathsf T}$ with its signed cross terms. The amplitude and unit raw-source kernel have different absolute-Jacobian factors. No result is uniform as $\kappa\to0$, on the actual frozen zero leaf, on a wrapped phase cover or torus, or at zero cutoff. The auxiliary $\mathcal G$ in §4 supplies no native cutoff-free realization.

The four canonical coordinates, Engel homogeneous dimension seven, rank-three long-time phase tensor, retained three-coordinate observation and physical Euclidean three-space are distinct notions. Neither physical three-space nor physical $SO(3)$ is selected. Analytic amplitudes and spectral identities supply no native preparation, actuation, lawful transport realization, clock permission, density acquisition or resource bridge. The infinite-fibre and interacting quantum distinctions in P §§92–96 remain in force; no autonomous reduced quantum evolution follows.

This differential-operator spectral energy is distinct from the selected-input quantum acquired-mass quantity with the same symbol in other volumes. There is no full-channel acquisition conclusion, native feasibility, efficiency, impossibility or capacity claim, generic neural-network or empirical machine-learning conclusion, ML implementation migration, or completion of the wider programme. Actual competitors remain unrestricted complex vectors throughout. The original complete-sign, occurrence and finer actual-scale obligations remain exactly those of Definition 10.2.

## 追加锚（本行以下为增补区）
