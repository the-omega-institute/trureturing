# Native Coulomb column: exact mass law and amplitude inverse

This conditional companion evaluates the original anisotropic Friedrichs Coulomb column and its full $L^2$ norm. It gives a positive convergent series for that norm, a strictly monotone scalar law, its unique inverse from a supplied core amplitude, and both endpoint mass and amplitude coefficients. The actual two-scale reconstruction, its common phase and its complete mass accounting are credited results of [Actual critical solvability and conditional microscopic disappearance](FIB_NATIVE_ACTUAL_CRITICAL_SOLVABILITY_AND_MICROSCOPIC_DISAPPEARANCE.md), called Source below. The new deductions evaluate its comparison column; they do not establish occurrence or select an actual branch.

## 1. Fixed native correspondence and conditional antecedents

**Definition 1.1 (unchanged original problem).** Fix one admitted signed $\kappa\ne0$, $H$, $I=(l,u)$, $k_0\in I$ and $a,\varepsilon>0$ satisfying every original probability, denominator, interval and parameter applicability condition of Source Definitions 1.1, 2.2, 10.1, 13.1 and 17.1, including the condition cited there as L Definition 35.1. These data remain fixed before every limit. Set

$$
\begin{aligned}
\alpha_\kappa&=\kappa+\kappa^2/H,&d_0&=k_0-\alpha_\kappa>0,\\
L_I&=u-l,&\lambda&=\varepsilon^2\pi^2/L_I^2,&
\phi(k)&=(2/L_I)^{1/2}\sin\frac{\pi(k-l)}{L_I},\\
c_j&=c_\kappa^{(j)}(k_0),&j_0&=\varepsilon^4|\det(c_0,c_1,c_2)|>0.
\end{aligned}
$$

All components of the same original vector $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$ are retained:

$$
\begin{aligned}
c_\kappa(k_0+h)&=c_0+hc_1+\frac{h^2}{2(1+h/d_0)}c_2,\\
b_\kappa(k_0+h)&=b_0+hb_1+\frac{h^2b_2}{2(1+h/d_0)},\\
(A_\kappa(k),B_\kappa(k))
 &=\frac{k-2\kappa}{2H(k-\alpha_\kappa)}(H+\kappa-k,-k),\\
\det(c_\kappa,c_\kappa',c_\kappa'')(k)
 &=-\frac{H^2-\kappa^2}{2H^3(k-\alpha_\kappa)^3}\ne0.
\end{aligned}
$$

The denominator has a positive margin on $\overline I$. In raw measure $dY=dk\,dq$, $q=(\theta,v,x)\in\mathbb R^3$, the unchanged native operators and domains are

$$
B=-\varepsilon^2\partial_k^2-(c_\kappa(k)\cdot\partial_q)^2,
\qquad S=B-\lambda\ge0,
\qquad B_\eta=-\varepsilon^2\partial_k^2+|\eta\cdot c_\kappa(k)|^2,
$$

$$
\begin{aligned}
\mathcal Q
 &=\left\{\psi\in L^2(I\times\mathbb R^3;\mathbb C):
 \widehat\psi(\cdot,\eta)\in H_0^1(I)\text{ a.e.},\quad
 \int\!\int_I\bigl(\varepsilon^2|\partial_k\widehat\psi|^2
 +|\eta\cdot c_\kappa|^2|\widehat\psi|^2\bigr)dk\,d\eta<\infty\right\},\\
D(S)=D(B)
 &=\left\{\psi\in L^2(I\times\mathbb R^3;\mathbb C):
 \widehat\psi(\cdot,\eta)\in H^2(I)\cap H_0^1(I)\text{ a.e.},\quad
 \int\|B_\eta\widehat\psi(\cdot,\eta)\|_{L^2(I)}^2d\eta<\infty\right\}.
\end{aligned}
$$

The Fourier factor is $(2\pi)^{-3/2}$ and all real $\eta$ are admitted. Both height faces are Dirichlet. There is no additional ordinary phase-$H^1$, reality, parity or affine restriction on actual states. With $o=(k_0,0)$, the field and charges are exactly

$$
\begin{aligned}
W_\tau&=\int_\tau^\infty e^{\lambda T}p_T^B(o,\cdot)dT,&
\rho_\tau&=e^{\lambda\tau}p_\tau^B(o,\cdot),&SW_\tau&=\rho_\tau,\\
\int\rho_\tau dY&=e^{\lambda\tau}\mathbb P_{k_0}(\zeta>\tau),&
\int\phi(k)\rho_\tau(k,q)dk\,dq&=\phi(k_0).
\end{aligned}
$$

Neither charge is divided by survival probability. The defining field clock is $B$, independently of $a$. Write $E_\tau(g)=\inf\sigma(aS-gW_\tau)$; Source supplies its negative attained bottom and the common operator domain $D(S)$ at each positive cutoff. For every prescribed sequence $s_n\downarrow0$, each $\psi_{s_n}$ may be any normalized complex actual ground state of $aS-g_sW_{s^2}$ in the complete $D(S)$, with

$$
g_s=\chi_cs^3,\qquad E_s=E_{s^2}(g_s)<0,\qquad
\epsilon_c(s)=s^2E_s,\qquad r_s=-E_s/s^6.
$$

**Definition 1.2 (canonical source and the original Coulomb constants).** Retain all conditional heat, integrated-tail, compactness, reconstruction, multiplier, weighted-mode and response antecedents in Source §§1–3, 10, 13 and 17–20, at their stated scopes. In particular, on the canonical Engel space,

$$
V=j_0^{-1}\int_1^\infty k_TdT>0,\qquad
p>0,\quad \|p\|_2=1,\quad
(a\mathcal E-\chi_cV)p=0,\quad
\chi_c=a/C_*>0,
$$

where $p\in D(\mathcal E)$ is the simple critical mode, $V\in L^2$ and $k_T$ has unit Haar mass. Thus

$$
m_{\rm core}=\int Vp\,d\xi\in(0,\infty),\qquad
Q=\sqrt{j_0\chi_c}\,\phi(k_0)m_{\rm core}>0.
$$

Indeed Cauchy–Schwarz proves finiteness, and $V,p>0$ and $k_0\in I$ prove strict positivity. This is the raw charge of Source (17.6). Define

$$
\begin{aligned}
M&=\int_I\phi(k)^2c_\kappa(k)c_\kappa(k)^{\mathsf T}dk>0,
&J&=\sqrt{\det M},&d(\mathbf z)&=\sqrt{\mathbf z^{\mathsf T}M^{-1}\mathbf z},\\
\beta_C&=\frac{\phi(k_0)\int_I\phi(k)^3dk}{4\pi J}>0,
&\varrho&=\frac{\beta_C}{2a},&e_C&=-\frac{\beta_C^2}{4a}=-a\varrho^2,\\
r_C&=-\chi_c^2e_C=\chi_c^2a\varrho^2,
&H_0&=-a\nabla\cdot M\nabla,&U_C&=\beta_C/d,\quad H_C=H_0-U_C.
\end{aligned}
$$

Here $H_C$ is exactly the original Friedrichs form operator on $H^1(\mathbb R^3)$. Source Proposition 17.2, with the supplied bottom $\inf\sigma(H_C)=e_C$, gives for every fixed $R>r_C$ the unique $L^2$ distributional solution

$$
(H_C+t)\zeta_R=Q\delta_0,\qquad t=R/\chi_c^2,
\qquad \zeta_R=Q(I-T_t)^{-1}Y_t,
$$

$$
T_t=[(H_0+t)^{-1}U_C]_{\rm ext},\qquad
Y_t(\mathbf z)=\frac{e^{-\sqrt{t/a}\,d(\mathbf z)}}{4\pi aJd(\mathbf z)}.
$$

Its proof uses the Hardy multiplier bound, bounded inversion of $I-T_t$ and whole-space distributional uniqueness; it introduces no origin boundary parameter. Its antecedents remain conditional here. The column is an $L^2$ comparison object, not an assertion of native or Coulomb form-domain membership.

## 2. Integral construction and the decisive origin expansion

**Definition 2.1 (integral functions and series).** For $A>0$ let

$$
\Gamma(A)=\int_0^\infty e^{-u}u^{A-1}du.
$$

For $0<\eta<1$, set $A=1-\eta$ and, for $x>0$, define

$$
\begin{aligned}
U(A,2,x)&=\frac1{\Gamma(A)}\int_0^\infty
 e^{-xq}q^{A-1}(1+q)^{1-A}dq,\\
W_\eta(x)&=e^{-x/2}xU(1-\eta,2,x),\\
P_\eta(x)&=\Gamma(1-\eta)W_\eta(x)
 =e^{-x/2}x\int_0^\infty e^{-xq}(1+1/q)^\eta dq.
\end{aligned}
$$

Specify the constant and auxiliary functions by convergent integrals and series:

$$
\begin{aligned}
\gamma&=-\int_0^1\frac{e^{-u}-1}{u}du-\int_1^\infty\frac{e^{-u}}u du,\\
\psi(A)&=-\gamma+\sum_{n=0}^\infty
 \left(\frac1{n+1}-\frac1{n+A}\right),\\
\psi_1(A)&=\sum_{n=0}^\infty\frac1{(n+A)^2}.
\end{aligned}
$$

The last series is the trigamma series; its displayed definition suffices for every use below. No logarithmic-derivative identity for $\Gamma$ is needed.

**Lemma 2.2 (ODE, decay and parameter control).** The integrals above are positive and finite at their stated parameters, smooth on compact subsets of those parameters, and

$$
xU_{xx}+(2-x)U_x-AU=0,\qquad
W_\eta''+\left(-\frac14+\frac\eta x\right)W_\eta=0.
$$

Uniformly for $\eta$ in any compact $K\subset(0,1)$,

$$
W_\eta(x)=e^{-x/2}x^\eta(1+O_K(x^{-1}))\qquad(x\to\infty).
$$

The differentiated functions through the orders needed for one parameter derivative and one radial derivative have exponential decay times powers of $x$ and $1+\log x$.

Proof. The integrand at $q=0$ has size $q^{-\eta}$; parameter derivatives add powers of $|\log q|$. These are integrable uniformly on $K$. At infinity the exponential dominates all the polynomial factors introduced by $x$ derivatives and the logarithms introduced by parameter derivatives. The same observations prove finiteness and smoothness of $\Gamma$ on compact $A$ intervals. Differentiation under each integral is therefore justified.

Put $f_A(q)=q^{A-1}(1+q)^{1-A}$. The derivative of $q(1+q)f_A(q)$ is $(A+2q)f_A(q)$. Integration of the derivative of $e^{-xq}q(1+q)f_A(q)$ has zero boundary terms: at zero its size is $O(q^A)$, and at infinity it decays exponentially. Consequently

$$
\int_0^\infty e^{-xq}\{xq(1+q)-2q-A\}f_A(q)dq=0.
$$

This is the stated equation for $U$. Direct differentiation of $W=e^{-x/2}xU$ gives the stated equation for $W$.

In the defining integral substitute $q=y/x$:

$$
U(1-\eta,2,x)=\frac{x^{\eta-1}}{\Gamma(1-\eta)}
 \int_0^\infty e^{-y}y^{-\eta}(1+y/x)^\eta dy.
$$

For $x\ge1$, the difference between $(1+y/x)^\eta$ and $1$ is bounded by $C_Ky/x$. The integral is therefore $\Gamma(1-\eta)+O_K(x^{-1})$. Parameter differentiation adds integrable powers of $|\log y|$ and factors bounded by powers of $1+y$; differentiating in $x$ has the same exponential majorant in $y$. These estimates give the asserted differentiated exponential bounds, also after $x=2kr$ with $k$ in a compact subset of $(\varrho,\infty)$. $\square$

**Lemma 2.3 (origin expansion with differentiated remainder).** Uniformly on each compact $K\subset(0,1)$, as $x\downarrow0$,

$$
\begin{aligned}
P_\eta(x)&=1+x\{-\eta\log x+B(\eta)\}+\mathcal R(\eta,x),\\
B(\eta)&=-\eta\psi(1-\eta)-2\eta\gamma+\eta-\tfrac12.
\end{aligned}
$$

Writing $L(x)=1+|\log x|$ for bounds only, the remainder and its parameter derivatives through order two satisfy

$$
\partial_\eta^j\mathcal R=O_K(x^2L(x)),\qquad
\partial_x\partial_\eta^j\mathcal R=O_K(xL(x)),\qquad
\partial_x^2\partial_\eta^j\mathcal R=O_K(L(x))
\quad(0\le j\le2).
$$

In particular, the coefficient and logarithm in this expansion follow from the defining integral.

Proof. Write $f_\eta(q)=(1+1/q)^\eta$ and

$$
h_\eta(q)=f_\eta(q)-1-\frac\eta{1+q},\quad
H_\eta(x)=\int_0^\infty e^{-xq}h_\eta(q)dq,\quad
\mathcal L(x)=\int_0^\infty\frac{e^{-xq}}{1+q}dq.
$$

At $q\ge1$, Taylor's formula for $(1+1/q)^\eta$ gives $\partial_\eta^jh_\eta(q)=O_K(q^{-2})$ for $0\le j\le2$. For $0<q\le1$ these derivatives are bounded by $C_K[1+q^{-b}(1+|\log q|^2)]$, where $b=\max K<1$. Thus they have an integrable majorant.

The exact derivative identity

$$
\{q(f_\eta(q)-1)\}'=f_\eta(q)-1-\frac{\eta f_\eta(q)}{1+q}
$$

gives, upon integration,

$$
H_\eta(0)=\eta+\eta\int_0^\infty\frac{f_\eta(q)-1}{1+q}dq.
$$

The boundary values of $q(f_\eta-1)$ are $0$ at zero and $\eta$ at infinity, justified respectively by $\eta<1$ and the same Taylor expansion. Substitute $t=q/(1+q)$ in the remaining integral. Expanding $(1-t)^{-1}$ gives

$$
\int_0^1\frac{t^{-\eta}-1}{1-t}dt
 =\sum_{n=0}^\infty\left(\frac1{n+1-\eta}-\frac1{n+1}\right)
 =-\psi(1-\eta)-\gamma.
$$

The summands before integration are nonnegative, so monotone convergence justifies this expansion. The resulting series is finite because its tail is $O_K(n^{-2})$. Parameter differentiation is also justified by the preceding integrable bounds, or by locally uniform convergence of its differentiated series. Hence

$$
H_\eta(0)=\eta\{1-\psi(1-\eta)-\gamma\}.
$$

An elementary substitution gives

$$
\mathcal L(x)=e^x\int_x^\infty\frac{e^{-u}}u du
 =-\log x-\gamma+O(xL(x)).
$$

For the last equality, subtract $1/u$ on $(x,1)$; the omitted integral on $(0,x)$ is $O(x)$. Its differentiated bounds follow directly from $\mathcal L'=\mathcal L-1/x$ and $\mathcal L''=\mathcal L'+1/x^2$.

For $0<x\le1/2$, split the integral for $H_\eta(x)-H_\eta(0)$ into $(0,1)$, $(1,1/x)$ and $(1/x,\infty)$, using $|e^{-xq}-1|\le\min(xq,2)$. The bounds on $h_\eta$ give

$$
H_\eta(x)-H_\eta(0)=O_K(xL(x)),\quad
H_\eta'(x)=O_K(L(x)),\quad H_\eta''(x)=O_K(x^{-1}).
$$

The same bounds hold after zero, one or two $\eta$ derivatives. For example, the middle interval in the first bound contributes at most $C_Kx\int_1^{1/x}q^{-1}dq$, and the tail at most $C_K\int_{1/x}^\infty q^{-2}dq$; the derivative estimates follow by inserting $q$ or $q^2$ under the exponentially damped integral.

Finally the exact decomposition is

$$
P_\eta(x)=e^{-x/2}\{1+x[\eta\mathcal L(x)+H_\eta(x)]\}.
$$

Insert the evaluated $H_\eta(0)$ and the expansion of $\mathcal L$, and expand $e^{-x/2}$. This gives the displayed $B(\eta)$. The differentiated estimates just proved give all three stated remainder bounds by the product rule. In particular these bounds control mixed radial and parameter derivatives, rather than merely an undifferentiated little-oh term. $\square$

## 3. Identification of the original Friedrichs column

**Theorem 3.1 (explicit column with its exact distributional source).** For every fixed $R>r_C$, put

$$
k=k_R=\sqrt{t/a}=\frac{\sqrt R}{\chi_c\sqrt a}>\varrho,
\qquad \eta=\eta_R=\frac{\varrho}k=\sqrt{r_C/R}\in(0,1).
$$

The column of Definition 1.2 is

$$
\boxed{\displaystyle
\zeta_R(\mathbf z)=\frac{Q}{4\pi aJd(\mathbf z)}P_{\eta_R}(2k_Rd(\mathbf z))
 =\frac{Q\Gamma(1-\eta_R)}{4\pi aJd(\mathbf z)}
 W_{\eta_R}(2k_Rd(\mathbf z)).}
$$

It is positive, lies in $L^2$, and has singular coefficient $Q/(4\pi aJ)$ in the radial coordinate $d$. The decaying radial solution away from zero is unique up to multiplication; the all-space distributional source fixes that multiplication.

Proof. Set $\mathbf z=M^{1/2}y$, $r=|y|$. Then $d(\mathbf z)=r$, $d\mathbf z=Jdy$ and $H_0=-a\Delta_y$. For a radial function $f(r)=u(r)/r$, its equation away from zero becomes

$$
u''(r)=\left(k^2-\frac b r\right)u(r),\qquad b=\beta_C/a=2\varrho.
$$

The substitution $x=2kr$ gives $u_{xx}+(-1/4+\eta/x)u=0$. Lemma 2.2 therefore supplies the decaying positive solution $u(r)=P_\eta(2kr)$. It has exponential decay times $r^\eta$.

For completeness, reduction of order gives a second independent solution

$$
u_2(r)=u(r)\int_{r_0}^r u(v)^{-2}dv.
$$

Direct differentiation verifies its equation and its nonzero constant Wronskian with $u$. Since $u(r)\sim C r^\eta e^{-kr}$ with $C>0$, differentiation of $r^{-2\eta}e^{2kr}/(2kC^2)$, or a comparison of its derivative with $u^{-2}$, gives

$$
\int_{r_0}^r u(v)^{-2}dv\sim\frac{r^{-2\eta}e^{2kr}}{2kC^2}.
$$

Thus $u_2(r)\sim r^{-\eta}e^{kr}/(2kC)$ grows exponentially. Every other solution is a linear combination of these two by the initial-value uniqueness theorem on $(0,\infty)$, proving uniqueness of the decaying radial solution.

Lemma 2.3 gives $u(r)=1+O(r(1+|\log r|))$, and more precisely $ru'(r)-u(r)\to-1$. Hence $u(r)/r$ is square integrable near zero in three dimensions; exponential decay proves square integrability at infinity. The potential times this function is locally integrable, since its strongest singularity is $r^{-2}$. To check the source, pair with a compact smooth test in $y$, exclude the ball $r\le\epsilon$ and integrate the Laplacian by parts twice. The term with the normal derivative of the test tends to zero, being $O(\epsilon)$. The flux term tends to $4\pi a$ times the test value at zero, because $r^2(u/r)'=ru'-u\to-1$. The excluded potential and zeroth-order terms tend to zero by local integrability. The coefficient $Q/(4\pi aJ)$ and volume factor $J$ therefore give exactly $Q$ times the test value at zero in the original $\mathbf z$ variable. Thus

$$
(H_C+R/\chi_c^2)\zeta_R=Q\delta_0
$$

on all of $\mathbb R^3$, with no additional distribution at zero. Source Proposition 17.2 identifies this $L^2$ solution with its original Friedrichs column. In particular radial uniqueness alone has not been used to assert nonradial distributional uniqueness. No freely chosen origin boundary condition or point interaction is present. $\square$

## 4. The parameter-differentiated Wronskian and the evaluated norm

**Theorem 4.1 (positive series mass law).** Define

$$
\begin{aligned}
F(\eta)&=1+2\eta+2\eta^2\psi_1(1-\eta)
 =1+2\eta+2\eta^2\sum_{n=0}^\infty(n+1-\eta)^{-2},\\
C_0&=\frac{Q^2}{8\pi a^2J\varrho},\qquad
G(\eta)=\eta F(\eta).
\end{aligned}
$$

Then the full column norm is

$$
\boxed{\displaystyle N(R):=\|\zeta_R\|_2^2
 =\frac{Q^2}{8\pi a^2Jk_R}F(\eta_R)
 =C_0G(\eta_R).}
$$

Proof. The series for $\psi$ converges absolutely and locally uniformly on $A>0$, since its summand is $(A-1)/[(n+1)(n+A)]$. Its derivative series also converges locally uniformly by comparison with $n^{-2}$, giving $\psi'(A)=\psi_1(A)$. Subsequent derivatives needed here are locally uniformly convergent series dominated by $n^{-3}$ or higher powers. These observations justify all following parameter derivatives.

Fix $b=\beta_C/a=2\varrho$, rather than $\eta$, when differentiating $k$. Put

$$
u_k(r)=P_{\eta(k)}(2kr),\qquad \eta(k)=b/(2k),\qquad v_k=\partial_ku_k.
$$

On every compact $k$ interval contained in $(\varrho,\infty)$, Lemma 2.3 and its differentiated remainder give

$$
\begin{aligned}
u_k(r)&=1+r\{-b\log r+D(k)\}+O(r^2(1+|\log r|)),\\
u_k'(r)&=-b\log r+D(k)-b+O(r(1+|\log r|)),\\
v_k(r)&=rD'(k)+O(r^2(1+|\log r|)),\\
v_k'(r)&=D'(k)+O(r(1+|\log r|)),\\
D(k)&=-b\log(2k)-b\psi(1-\eta(k))-2b\gamma+b-k.
\end{aligned}
$$

The absence of a $k$ derivative of $-b\log r$ uses precisely the fixed-$b$ differentiation. Since $\eta'(k)=-\eta/k$ and $(1-\eta)'=\eta/k$,

$$
D'(k)=-\frac b k-\frac{b\eta}k\psi_1(1-\eta)-1
 =-1-2\eta-2\eta^2\psi_1(1-\eta)=-F(\eta).
$$

Differentiate the radial ODE $u_k''=(k^2-b/r)u_k$ to obtain

$$
v_k''=(k^2-b/r)v_k+2ku_k,\qquad
\{u_kv_k'-u_k'v_k\}'=2ku_k^2.
$$

At zero, the displayed expansions show $u_kv_k'-u_k'v_k\to D'(k)$: the potentially logarithmic product is $O(r|\log r|)$ and vanishes. At infinity this Wronskian tends to zero by Lemma 2.2 and its differentiated exponential bounds. The same bounds give an integrable exponential majorant on each compact $k$ interval at infinity, while the origin expansions bound $u_k^2$ there. Thus integration first on $[\epsilon,L]$ and passage to both limits is justified, as is the parameter differentiation used to derive the identity. It follows that

$$
2k\int_0^\infty u_k(r)^2dr=-D'(k)=F(\eta).
$$

Equivalently,

$$
\int_0^\infty W_\eta(x)^2dx
 =\frac{F(\eta)}{\Gamma(1-\eta)^2}.
$$

If the unnormalized $W$ solution is differentiated instead, its leading coefficient is $A_0=1/\Gamma(1-\eta)$ and the zero Wronskian is $A_0^2D'(k)$; derivatives of $A_0$ cancel between the two Wronskian terms. The normalized computation above implements that cancellation directly.

Finally anisotropic radial integration gives every constant explicitly:

$$
\begin{aligned}
N(R)&=4\pi J\left(\frac{Q}{4\pi aJ}\right)^2
 \int_0^\infty P_\eta(2kr)^2dr\\
 &=\frac{Q^2}{4\pi a^2J}\frac{F(\eta)}{2k}
 =\frac{Q^2}{8\pi a^2Jk}F(\eta).
\end{aligned}
$$

Using the $W$ representation instead produces $\Gamma(1-\eta)^2$ in the squared prefactor and its reciprocal in the evaluated integral; they cancel exactly. This is the full $L^2$ norm, including $4\pi$, the determinant, the raw charge and the kinetic constant. $\square$

## 5. Strict monotonicity, range and the amplitude inverse

**Theorem 5.1 (scalar bijection).** For $R\in(r_C,\infty)$, $N(R)$ is smooth and strictly decreasing with range $(0,\infty)$. Define the comparison core amplitude and two mass fractions by

$$
\alpha(R)=(1+N(R))^{-1/2},\qquad
m_\mu(R)=\frac1{1+N(R)},\qquad
m_M(R)=\frac{N(R)}{1+N(R)}.
$$

Then $\alpha$ increases bijectively from $0$ to $1$, $m_\mu=\alpha^2$ increases from $0$ to $1$, $m_M$ decreases from $1$ to $0$, and $m_\mu+m_M=1$. For every supplied $\alpha\in(0,1)$ there is exactly one $R>r_C$ satisfying this law: solve the positive scalar equation

$$
C_0\eta\left[1+2\eta+2\eta^2\sum_{n=0}^\infty(n+1-\eta)^{-2}\right]
 =\frac{1-\alpha^2}{\alpha^2},\qquad 0<\eta<1,
\qquad R=\frac{r_C}{\eta^2}.
$$

Proof. On any compact subinterval of $(0,1)$, the series and all its derivatives converge uniformly by comparison with convergent power series in $1/n$. In particular

$$
F'(\eta)=2+4\eta\psi_1(1-\eta)
 +4\eta^2\sum_{n=0}^\infty(n+1-\eta)^{-3}>0,
\qquad G'=F+\eta F'>0.
$$

Since $\eta_R'=-\eta_R/(2R)$,

$$
N'(R)=-\frac{C_0\eta_R}{2R}\{F(\eta_R)+\eta_RF'(\eta_R)\}<0.
$$

As $\eta\downarrow0$, the trigamma series remains bounded and $G(\eta)\to0$. As $\eta\uparrow1$, its $n=0$ term gives $G(\eta)\ge2\eta^3/(1-\eta)^2\to\infty$. Continuity, strict monotonicity and the intermediate value theorem prove the claimed range and unique inverse. Differentiating the elementary functions of $N$ proves their strict monotonicities. A complex supplied core coefficient $c$ determines this $R$ only through its modulus $\alpha=|c|\in(0,1)$; its phase is unconstrained by the scalar equation. Values $\alpha=0$ and $\alpha=1$ are endpoint values of this family and correspond to no finite $R>r_C$. $\square$

**Proposition 5.2 (source phase correspondence).** The formulas use the positive canonical choice $p>0$, so $Q>0$ is exact, not a replacement of an unspecified signed charge by its modulus. If the same canonical mode is represented instead as $p_\theta=e^{i\theta}p$, then its integral charge is $Q_\theta=e^{i\theta}Q$, its column is $\zeta_{R,\theta}=e^{i\theta}\zeta_R$, and its microscopic coefficient is $c_\theta=e^{-i\theta}c$. Thus the two comparison terms $c_\theta p_\theta$ and $c_\theta\zeta_{R,\theta}$ equal $cp$ and $c\zeta_R$ respectively. For this representation the norm formula contains $|Q_\theta|^2=Q^2$.

Proof. The integral defining the charge and the distributional column equation are complex linear. Theorem 3.1 and whole-space uniqueness give the column's transformation. The coefficient transformation is the identity $c_\theta p_\theta=cp$, and multiplication gives the second comparison identity. Taking squared norms proves the modulus statement. No phase, modulus or sign of an actual state has been removed. $\square$

## 6. Both endpoint coefficients of the scalar comparison family

**Theorem 6.1 (large-$R$ endpoint).** Keep the datum fixed and set

$$
K_\infty=\frac{Q^2\chi_c}{8\pi a^{3/2}J}=C_0\sqrt{r_C}>0.
$$

For the comparison functions, as $R\to\infty$,

$$
\begin{aligned}
N(R)&=K_\infty R^{-1/2}+2K_\infty\sqrt{r_C}\,R^{-1}+O(R^{-3/2}),\\
m_M(R)&=K_\infty R^{-1/2}+O(R^{-1}),\\
m_\mu(R)&=1-K_\infty R^{-1/2}+O(R^{-1}),\\
\alpha(R)&=1-\tfrac12K_\infty R^{-1/2}+O(R^{-1}).
\end{aligned}
$$

When these are interpreted through actual finite branches, each native limit is taken first at its own fixed finite $R>r_C$. These expansions assert no simultaneous $s\downarrow0$, $R\to\infty$ rate, no uniform native resolvent approximation and no theorem selecting a divergent $r_s$ branch.

Proof. Put $Z_2=\sum_{n=1}^\infty n^{-2}<\infty$. For $0\le\eta\le1/2$, the mean value theorem and convergence of $\sum n^{-3}$ give $\psi_1(1-\eta)=Z_2+O(\eta)$. Therefore

$$
F(\eta)=1+2\eta+2Z_2\eta^2+O(\eta^3),\qquad
G(\eta)=\eta+2\eta^2+O(\eta^3).
$$

Insert $\eta=\sqrt{r_C/R}$ into $N=C_0G$. The identity $r_C=\chi_c^2a\varrho^2$ gives the stated $K_\infty$. Taylor's formula at $N=0$ for $(1+N)^{-1}$ and $(1+N)^{-1/2}$, with bounded second derivatives on a fixed neighbourhood of zero, proves the three remaining estimates. They concern the scalar family alone. Their actual interpretation has exactly the fixed-$R$-before-endpoint order stated in the theorem; no native estimate has been differentiated or made uniform. $\square$

**Theorem 6.2 (Coulomb endpoint).** Put $\Delta=R-r_C$ and

$$
K_{\rm edge}=8C_0r_C^2
 =\frac{Q^2r_C^2}{\pi a^2J\varrho}>0.
$$

For the comparison functions, as $\Delta\downarrow0$,

$$
\begin{aligned}
N(R)&=K_{\rm edge}\Delta^{-2}+O(1),\\
m_\mu(R)&=\frac{\Delta^2}{K_{\rm edge}}+O(\Delta^4),\\
m_M(R)&=1-\frac{\Delta^2}{K_{\rm edge}}+O(\Delta^4),\\
\alpha(R)&=\frac{\Delta}{\sqrt{K_{\rm edge}}}+O(\Delta^3).
\end{aligned}
$$

In particular the microscopic mass coefficient is $\pi a^2J\varrho/(Q^2r_C^2)$ and the core amplitude coefficient is $\sqrt{\pi a^2J\varrho}/(Qr_C)$. If applied to actual finite branches, these describe their scalar values only after the credited native limit at each fixed $R>r_C$. They give no uniform estimate through the native threshold, no joint endpoint/native rate, and no interchange of limits or actual occurrence theorem.

Proof. Let $\delta=1-\eta$ and $h=\Delta/r_C=\eta^{-2}-1$. Separating the first trigamma term gives

$$
G(\eta)=\frac{2\eta^3}{\delta^2}+\eta+2\eta^2
 +2\eta^3\sum_{n=1}^\infty(n+\delta)^{-2}.
$$

The remaining series is uniformly bounded by $Z_2$. The exact algebraic identity

$$
\frac{2\eta^3}{(1-\eta)^2}
 =\frac8{h^2}+\frac{2\eta^3}{(1+\eta)^2}
$$

shows $G=8h^{-2}+O(1)$, including the cancellation of any term of order $h^{-1}$. Multiplying by $C_0$ proves the norm estimate and its complete coefficient. Consequently

$$
1+N=K_{\rm edge}\Delta^{-2}\{1+O(\Delta^2)\}.
$$

Taking its reciprocal and inverse square root gives the stated orders and coefficients. Complementarity gives the macroscopic mass. The hypotheses of the actual reconstruction are separated from this scalar calculation: constants in that reconstruction can depend on the fixed gap $R-r_C$, so this calculation supplies none of the joint native conclusions excluded in the theorem. $\square$

## 7. Transfer to actually occurring finite branches

**Definition 7.1 (the credited complete reconstruction).** Use Source's exact isometries

$$
\begin{aligned}
\Xi_s(r,y,z,w)&=(k_0+\varepsilon sr,\mathbf q_s(r,y,z,w)),\\
\mathbf q_s(r,y,z,w)&=sc_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w,\\
\Omega_s&=((l-k_0)/(\varepsilon s),(u-k_0)/(\varepsilon s))\times\mathbb R^3,\\
\mathcal U_s\psi&=\sqrt{j_0s^7}\,\psi\circ\Xi_s,\qquad
(\mathcal D_g\psi)(k,\mathbf z)=g^{-3/2}\psi(k,\mathbf z/g),\\
\iota h(k,\mathbf z)&=\phi(k)h(\mathbf z),\qquad
\mathcal M_sh=\mathcal U_s\mathcal D_{g_s}^{-1}\iota h.
\end{aligned}
$$

Put $F_s=\mathcal U_s\psi_s$. Outputs in microscopic space are zero extended. In particular $\|\mathcal M_sh\|_2=\|h\|_2$. Both original deaths and the rational third component persist in Source's transported native operator, whose horizontal field is

$$
Y_s=\partial_y+r\partial_z+
 \frac{r^2}{2(1+\varepsilon sr/d_0)}\partial_w.
$$

For every prescribed sequence and every actual complex ground-state choice, Source Theorems 19.1 and 20.1 give, conditional on $r_s\to R\in(r_C,\infty)$, the whole-sequence phase-orbit reconstruction

$$
\inf_{\theta\in\mathbb R}\|F_s-e^{i\theta}\alpha_R(p+\mathcal M_s\zeta_R)\|_2\to0,
\qquad \alpha_R=(1+\|\zeta_R\|_2^2)^{-1/2}.
$$

On a subsequence with $F_s\rightharpoonup cp$, they give the stronger fixed-phase statement

$$
\|F_s-cp-c\mathcal M_s\zeta_R\|_2\to0,\qquad
1=|c|^2(1+\|\zeta_R\|_2^2).
$$

These are supplied complete-output $L^2$ conclusions. Source §18 obtains the early compact core and late free column from the actual short-field source; §19 applies the bounded native inverse at a fixed separated parameter and the full-output macroscopic comparison. The resulting common complex factor, asymptotic orthogonality and exact norm accounting are Source credit. Local convergence or a trial state alone would not imply these conclusions.

**Corollary 7.2 (explicit necessary law for every actual finite branch).** Under exactly the fixed-datum, analytic-antecedent, sequence and actual-choice conditions of Definition 7.1, if $r_s\to R\in(r_C,\infty)$, then every microscopic weak cluster $cp$ has

$$
|c|=\alpha(R),\qquad
\mathfrak m_{\rm micro}=m_\mu(R)=\frac1{1+C_0G(\eta_R)},\qquad
\mathfrak m_{\rm macro}=m_M(R)=\frac{C_0G(\eta_R)}{1+C_0G(\eta_R)}.
$$

The common phase, full reconstruction and absence of a third $L^2$ mass scale remain those of Source Corollary 20.2. Necessarily $C_{\rm resp}=0$. A supplied nonzero core modulus in $(0,1)$ fixes the only possible finite $R$ by Theorem 5.1.

Proof. Substitute Theorem 4.1 into the credited complete norm identity and phase-orbit formula. Source Corollary 20.2 identifies the two actual mass fractions by first taking $s\to0$ at this fixed $R$, then exhausting microscopic compact sets for the first mass or shrinking the excluded macroscopic origin ball for the second. Their sum is one and its complete reconstruction excludes additional intermediate or exterior mass. Thus these are actual mass fractions under the antecedent, not merely norms assigned to trial functions. Since $E_s=-r_ss^6\to0$ and every such weak cluster has $c\ne0$, Source Theorem 5.1 gives $c(0-C_{\rm resp})=0$, hence $C_{\rm resp}=0$. Theorem 5.1 of this companion gives the last assertion. Neither substitution produces the supplied modulus or the branch antecedent. $\square$

## 8. Attribution and the unchanged remaining decision

**Definition 8.1 (result ownership and analytic boundaries).** Source §§1–3 supply the original equation, source, domain, canonical mode and complete coefficient fields. Its §§4–6 own the actual solvability identity $c(L-C_{\rm resp})=0$ and positive-response microscopic disappearance. Its §§7–9 credit the matching energy, negative branch, affine comparisons, exact parameter images and admission/negative-response occurrence, and specify the full original target. Its §§10–12 own the weak-zero/full-mass macroscopic implication and positive-response macroscopic selection; §§13–16 own the quantitative reference amplitude, strict nonzero-core margin and the endpoint/weak-zero/full-mass equivalence. Its Proposition 17.2 owns the original Friedrichs column's whole-space uniqueness, positivity and bounded comparison inversion. Its §§18–20 own the short-field complete output, complete two-scale reconstruction, common phase, exact two mass fractions and absence of a third $L^2$ mass scale. All the applicable original antecedents, including heat and all-height output estimates, remain conditional. Their publication, source status or authorship is not additional mathematical evidence.

The new work here is the integral derivation and fully differentiated origin expansion, explicit identification and norm evaluation of that exact column, its positive-series scalar bijection, and its endpoint coefficients. Gamma integrals, elementary ODE uniqueness, integration by parts, convergent series, radial integration and the intermediate value theorem are classical tools. This is a source-specific conditional evaluation, with no literature-wide originality or absence claim and no external, numerical or Lean/kernel/frozen certification.

**Definition 8.2 (unchanged unresolved target and limit order).** The complete target of Source Definitions 9.1 and 20.3 remains unchanged: evaluate both full absolute signs $C_{108},C_{\rm resp}$ on the original admitted jointly realized signed rational family; characterize actual sign occurrence; and decide the exact-critical scale and profile of every normalized complex actual ground state, including response zero. Exact ratio maps and negative-response occurrence retain their existing credit. Canonical absolute signs and positive/zero occurrence remain unresolved here. At response zero, no actual endpoint, particular finite mixed branch, divergent $r_s$ branch or other subsequential alternative is selected by this companion. Existence of a comparison column for every $R>r_C$ and unique invertibility from a supplied amplitude imply neither actual branch existence nor an amplitude selected by the original equation.

Source's weak-zero endpoint equivalence, strict core margin and every-finite-branch rigidity remain valid conditional constraints. Theorems 6.1 and 6.2 concern the comparison scalar family after the native limit at each fixed finite $R>r_C$. They do not add a simultaneous native/endpoint rate, uniform native resolvent approximation, divergent-branch theorem, interchange of limits or missing every-choice occurrence conclusion. In particular the comparison limits $\alpha\to0$ at $r_C$ and $\alpha\to1$ at infinity are not such selection theorems.

No assertion is uniform in varying data, as $\kappa\to0$, on the actual zero leaf, on wrapped phases or at zero cutoff. The anisotropic $M$, signed cross terms, raw $j_0s^7$ Jacobian, source sign and phase, both Dirichlet deaths, full rational third component, real phases and complex native domains are retained exactly. The $1/a$ in the comparison fundamental solution changes no defining field clock. The singular column has no new native form-domain, kinetic-energy, point-interaction or cutoff-free interpretation. No spectral-energy/acquired-mass/record-total-variation/ML-error identity, general neural-network or empirical-ML result, physical realization, physical dimension, analytic-state preparation or completion of the wider programme follows.

## 追加锚（本行以下为增补区）
