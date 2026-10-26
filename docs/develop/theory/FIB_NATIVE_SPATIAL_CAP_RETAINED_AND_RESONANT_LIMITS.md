# Native spatial-cap retained and resonant ground-state limits

## 1. The unchanged native family and its source normalizations

Use the both-wall periodic cylinder, preparations, guards, grouped phases,
horizontal controls and killed outer boundary of
[Native Green stability, §§1–3 and 10](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md).
Fix the original interior source $o$, a smooth positive raw density
$\rho$, and a smooth horizontal SPD matrix $A$. The original kinetic form
and its domain are

$$
T_A[f]=\int_\Omega\langle AXf,Xf\rangle\,d\mu,\qquad
d\mu=\rho\,dk\,dh,\qquad
\mathcal F_A=\overline{C_c^\infty(\Omega)}^{\,T_A+\|\cdot\|_2^2}.
\tag{1.1}
$$

The actual phases are periodic; killing is at the original two ends of
the cylinder. The clock has covariance $2A\,dt$, with no additional
factor $1/2$ in (1.1). Let $\Gamma$ be the full killed Green field of
$L_A$ for the original unit source relative to $d\mu$.
Fix once and for all an admissible chart radius $b>0$. Only

$$
\begin{aligned}
L&=\log(b/\epsilon),&
\Gamma_\epsilon&=\min(\Gamma,c_G\epsilon^{-2}),\\
g_{\epsilon,\lambda}&=g_{\mathrm c}(1+\lambda/L^2),&
q_{\epsilon,\lambda}[f]&=T_A[f]
             -g_{\epsilon,\lambda}\int\Gamma_\epsilon|f|^2d\mu
\end{aligned}
\tag{1.2}
$$

vary. Their form domain is exactly $\mathcal F_A$ and their operator
domain is $D(L_A)$. For every fixed real $\lambda$ the coupling is
eventually positive. Write $E_{\epsilon,\lambda}$ and
$f_{\epsilon,\lambda}>0$ for the actual lowest energy and its positive
$L^2(\mu)$-normalized state. Suppress $\lambda$ when fixed. Set

$$
V_{\rm raw}[f]=\int\Gamma|f|^2d\mu,\quad
V_{\rm cap}[f]=\int\Gamma_\epsilon|f|^2d\mu,\quad
\mathcal C_\epsilon=\{\Gamma>c_G\epsilon^{-2}\}.
\tag{1.3}
$$

Here $T_A[f;\mathcal C_\epsilon]$ is the original kinetic integral over
this moving set, not a new form or boundary condition.

In the exact source chart $q=(\xi,\eta,\tau)=\Psi(\cdot)$ of Native
Green stability, (10.1)–(10.2), put

$$
\begin{gathered}
U=\partial_\xi-\tfrac12\eta\partial_\tau,\qquad
V=\partial_\eta+\tfrac12\xi\partial_\tau,\qquad \nabla_H=(U,V),\\
R^4=(\xi^2+\eta^2)^2+16\tau^2,\qquad
\delta_s q=(s\xi,s\eta,s^2\tau),\\
d\mu=m(q)dq,\qquad C(0)=I_2,\qquad
m_0=\frac{\rho(o)\det A(o)}{2r},\\
dq=\tfrac14R^3dR\,da\,d\theta,\quad
J=(-\pi/2,\pi/2),\quad c=\cos a,\quad 0\le\theta<2\pi.
\end{gathered}
\tag{1.4}
$$

The scalar angular integral $C$ below is distinguished from the matrix
$C(q)$ by its argument. Let $S$ be the natural angular operator of Native
Green stability, (10.4)–(10.5), with positive simple ground pair
$(\lambda_0,\phi)$ normalized by $\phi(0)=1$, and set

$$
\begin{gathered}
h=R^{-1}\phi(a),\quad M=\int_J\phi^2da,\quad C=\int_Jc\phi^2da,
\quad k=\frac\pi2C,\quad N=\frac k2,\\
c_G=(2\pi m_0)^{-1},\quad g_{\mathrm c}=2\pi m_0\lambda_0,\quad
K=m_0k,\quad \alpha=\lambda_0M/C,\\
\lambda_D=\pi^2/\alpha,\qquad \lambda_Z=\pi^2/(4\alpha).
\end{gathered}
\tag{1.5}
$$

Let $F=K_*$ be the completed critical operator from Native Green
stability, §§12–16, with form domain $\mathcal Q$, ground energy $E_*$,
and positive normalized ground $f_*$. Its actual scalar source trace is
$f_*/h=a_*+O(R^\gamma)$, with annular derivatives and $a_*>0$.
Here and below $0<\gamma<1$ may be decreased. Thus
$\mathsf K=a_*^2K$; $K$ itself contains no normalized-state factor.

The inherited-wall maximal pair of Native Green stability, Theorem 21.1,
has genuine vectors $p=f_*/a_*$ and $\zeta$ with traces $(1,0)$ and
$(0,1)$. With scalar product linear in its first variable,

$$
\begin{aligned}
[u,v]&=K\{\mathcal B(u)\overline{\mathcal A(v)}
                    -\mathcal A(u)\overline{\mathcal B(v)}\},\\
D(F)&=\ker\mathcal B,\qquad
u/h=\mathcal A(u)+\mathcal B(u)\log R+O(R^\gamma)
\end{aligned}
\tag{1.6}
$$

for finite-energy maximal solutions, uniformly in all directions with
rescaled-annular derivatives. General maximal vectors have the weaker
graph/angular topology of that theorem. No finite-resolution capped
state has these uncapped operator traces. Its normalization here is
always the actual number

$$
A_\epsilon=\frac{\epsilon f_\epsilon(o)}{Z(0)}.
\tag{1.7}
$$

The source-regular frozen cap solution $Z$ and its analytic family $Z_z$
are those of Native Green stability, Theorems 18.1 and 22.1.
In particular $a(0)=\kappa_{\rm cap}>0$ in the exact exterior response

$$
RZ_z=\phi_z\{s_z(y)+a(z)c_z(y)\}+r_z,\quad y=\log R,\quad
s_z(y)=\frac{\sin(\sqrt z\,y)}{\sqrt z},\quad c_z(y)=\cos(\sqrt z\,y).
\tag{1.8}
$$

The entire power series define $s_z,c_z$ also at $z\le0$.
The complement decays exponentially with the stated energy and
exterior-annulus derivatives. Smooth bounds are used only outside the
interface; horizontal $W^{1,2}$ is the topology through it.
If $\Lambda(z)$ is the lowest eigenvalue of $S+zc$, choose the small real
$z_L$ by $\Lambda(z_L)=\lambda_0(1+\lambda/L^2)$. The normalization
$\langle\phi_z,\phi\rangle=M$ gives

$$
\begin{gathered}
v_{\rm ang}=(c-C/M)\phi,\qquad
Q_{\rm ang}=\langle(S-\lambda_0)^{-1}_{\phi^\perp}v_{\rm ang},
                                                   v_{\rm ang}\rangle>0,\\
\beta_{\rm ang}=Q_{\rm ang}/(2C),\\
\Lambda(z)=\lambda_0+(C/M)z-(Q_{\rm ang}/M)z^2+O(z^3),\\
z_L=\alpha\lambda/L^2+
                 2\beta_{\rm ang}(\alpha\lambda)^2/L^4+O(L^{-6}).
\end{gathered}
\tag{1.9}
$$

These are the angular curvature and analytic pencil of Native Green
stability, (25.1) and (25.11). Strict positivity holds because
$v_{\rm ang}\ne0$ is perpendicular to $\phi$ and the reduced inverse is
positive. The moving cap constants are

$$
\begin{aligned}
I&=\int_{R<1}(R^{-2}-1)Z^2dq>0,&
J_{\rm raw}&=\int_{R<1}R^{-2}Z^2dq,\\
J_{\rm cap}&=\int_{R<1}Z^2dq=N/\lambda_0,&
J_T&=\int_{R<1}|\nabla_HZ|^2dq.
\end{aligned}
\tag{1.10}
$$

All are finite. The normalized actual core, cap integrals divided by
$A_\epsilon^2$, and $Q_\epsilon/A_\epsilon\to a_*K$, for
$Q_\epsilon=\int g_{\mathrm c}(\Gamma-\Gamma_\epsilon)f_*f_\epsilon d\mu$,
are Native Green stability, Theorem 23.2 and Proposition 23.3.
Those results alone determine no rate for $A_\epsilon$.

## 2. Retention below the first threshold

**Definition 2.1 (transition functions).** For $0<\lambda<\lambda_D$ put
$\mu_\lambda=\sqrt{\alpha\lambda}$ and define

$$
S_\lambda(s)=\frac{\sin(\mu_\lambda s)}{\sin\mu_\lambda},\quad
H_\lambda=\mu_\lambda\cot\mu_\lambda,\quad
C_\lambda=\frac{\mu_\lambda}{\sin\mu_\lambda}.
\tag{2.1}
$$

For $\lambda<0$, with $\nu_\lambda=\sqrt{-\alpha\lambda}$, use
$\sinh(\nu_\lambda s)/\sinh\nu_\lambda$,
$\nu_\lambda\coth\nu_\lambda$ and $\nu_\lambda/\sinh\nu_\lambda$,
respectively. Their continuous values at zero are $s,1,1$. Set

$$
J_\lambda=\int_0^1S_\lambda(s)^2ds
=\begin{cases}
\displaystyle\frac{1/2-\sin(2\mu_\lambda)/(4\mu_\lambda)}
                       {\sin^2\mu_\lambda},&\lambda>0,\\[4pt]
1/3,&\lambda=0,\\[2pt]
\displaystyle\frac{\sinh(2\nu_\lambda)/(4\nu_\lambda)-1/2}
                       {\sinh^2\nu_\lambda},&\lambda<0.
\end{cases}
\tag{2.2}
$$

**Theorem 2.2 (actual retained ground and separate resources).** For every
fixed admissible model and $b$, and every fixed real $\lambda<\lambda_D$,

$$
E_{\epsilon,\lambda}=E_*+\mathsf K H_\lambda/L+o(L^{-1}),
\qquad LA_\epsilon\longrightarrow a_*C_\lambda.
\tag{2.3}
$$

The normalized state converges strongly to $f_*$ in $L^2(\mu)$ and the
shifted critical form norm of $\mathcal Q$, and smoothly on compact
interior sets away from $o$. Its rank-one positive ground projection
converges in norm. No mass escapes. For a chart function $u$ write

$$
\mathcal M u(t)=\frac1{2\pi C}\int_J\int_0^{2\pi}
                       c\phi^2u(e^t,a,\theta)\,d\theta da.
\tag{2.4}
$$

At $R=\epsilon e^{sL}$,

$$
\begin{aligned}
\mathcal M(f_\epsilon/f_*)(\log\epsilon+sL)&\longrightarrow S_\lambda(s)
                                               &&\text{in }H^1(0,1),\\
f_\epsilon/h&\longrightarrow a_*S_\lambda(s)
                            &&\text{in }L^2(\phi^2ds\,da\,d\theta),\\
\epsilon Lf_\epsilon(\Psi^{-1}\delta_\epsilon x)
                    &\longrightarrow a_*C_\lambda Z(x).
\end{aligned}
\tag{2.5}
$$

The last convergence is locally uniform and strong in local horizontal
$W^{1,2}$, including the source and through $R=1$, and is smooth only
off that interface. On each compact Cartesian annulus and for
$s\in[\delta,1-\delta]$, the rescaled second convergence is smooth,
uniformly in $s$, for every $0<\delta<1/2$. The $H^1$ assertion concerns
$f_\epsilon/f_*$; it does not assert an $H^1$ limit for $f_\epsilon/h$
at the fixed outer endpoint.

The actual separate total and moving-core costs obey

$$
\begin{aligned}
\frac{V_{\rm raw}[f_\epsilon]}L,\quad
\frac{V_{\rm cap}[f_\epsilon]}L
       &\longrightarrow \frac{a_*^2M J_\lambda}{4},\\
\frac{T_A[f_\epsilon]}L
       &\longrightarrow \frac{g_{\mathrm c}a_*^2M J_\lambda}{4},\\
L^2(V_{\rm raw}-V_{\rm cap})[f_\epsilon]
       &\longrightarrow \frac{a_*^2C_\lambda^2I}{2\pi},\\
L^2\int_{\mathcal C_\epsilon}\Gamma f_\epsilon^2d\mu
       &\longrightarrow \frac{a_*^2C_\lambda^2J_{\rm raw}}{2\pi},\\
L^2\int_{\mathcal C_\epsilon}\Gamma_\epsilon f_\epsilon^2d\mu
       &\longrightarrow \frac{a_*^2C_\lambda^2J_{\rm cap}}{2\pi},\\
L^2T_A[f_\epsilon;\mathcal C_\epsilon]
       &\longrightarrow m_0a_*^2C_\lambda^2J_T,\\
LQ_\epsilon&\longrightarrow\mathsf K C_\lambda.
\end{aligned}
\tag{2.6}
$$

The limits and remainders are uniform on each compact subset of
$(-\infty,\lambda_D)$ for a fixed model and $b$. No uniformity over
$\rho,A$ or through $\lambda_D$ is asserted. The zero case is exactly
Native Green stability, §§14–19. At the unique zero $\lambda_Z$ of
$H_\lambda$, its Theorem 25.2, (25.2)–(25.5), supplies the sharper
actual energy and resource finite parts, including admissible balanced
$b$. Those results are used without repeating their proof.
Thus $E_\epsilon-E_*$ has positive leading sign below $\lambda_Z$ and
negative leading sign between $\lambda_Z$ and $\lambda_D$; a zero first
coefficient is not a sign determination.

## 3. The actual retained comparison and its lower direction

Proof of Theorem 2.2. At $\lambda=0$ use Native Green stability,
§§15–18. The estimates below retain their continuous zero limits to
give compact-parameter uniformity, without a separate critical-case
derivation. Put $d\nu_*=f_*^2d\mu$ and use the exact transform
of Native Green stability, (25.6)–(25.7):

$$
\begin{gathered}
B_\epsilon[u]=\mathscr A[u]+\int D_\epsilon|u|^2d\nu_*,
\quad D_\epsilon=g_{\mathrm c}(\Gamma-\Gamma_\epsilon),\\
\mathcal W_\epsilon[u]=g_{\mathrm c}\int\Gamma_\epsilon|u|^2d\nu_*,
\qquad
q_{\epsilon,\lambda}[f]-E_*\|f\|^2
     =B_\epsilon[f/f_*]-\lambda\mathcal W_\epsilon[f/f_*]/L^2.
\end{gathered}
\tag{3.1}
$$

Its all-angular inequality (25.10) says, for every $\eta>0$,

$$
\mathcal W_\epsilon[u]\le(\alpha/\pi^2+\eta)L^2B_\epsilon[u]
                                      +C_\eta L\|f_*u\|^2.
\tag{3.2}
$$

On each compact subthreshold parameter set a fixed shifted
$q_{\epsilon,\lambda}$ norm is therefore uniformly equivalent to

$$
\mathcal N_\epsilon(f)^2=B_\epsilon[f/f_*]+\|f\|_2^2.
\tag{3.3}
$$

For negative $\lambda$ the detuning improves the lower bound; (3.2)
also supplies the upper equivalence on bounded parameter sets.
Bounded sublevels are bounded in the compact critical completion.
Pair against fixed punctured-core vectors, on whose supports the cap
defect eventually vanishes. Positivity of the shifted form on $f-z$,
followed by the supremum over this dense core, proves the limiting lower
inequality. Diagonal core approximation proves recovery.
Compact min-max gives convergence of the first two actual eigenvalues
to those of $F$ and strong $L^2$ convergence of the positive normalized
ground to $f_*$. Its simple first eigenvalue supplies a uniform positive
first gap. This is the compact-subthreshold argument in Native Green
stability, §25, with its full-angular remainder estimate; no equality
gap is used.

Construct a genuine global corrector before matching the cap. Set
$F_0=(S_{D,\max}-E_*)\zeta$. By (1.6),
$\langle F_0,f_*\rangle=Ka_*$. Hence
$\mathsf Kf_*-a_*F_0$ is perpendicular to $f_*$. Apply the reduced
inverse of $F-E_*$ to it, add $a_*\zeta$, and subtract its $f_*$
component. The real result $V$ retains the original outer walls and
satisfies

$$
\mathcal B(V)=a_*,\qquad \langle V,f_*\rangle=0,\qquad
(\mathcal T-E_*)V=\mathsf Kf_*,
\quad \mathcal T=L_A-g_{\mathrm c}\Gamma.
\tag{3.4}
$$

Its graph-minimal remainder has the weighted control of Native Green
stability, (21.8). The forcing in its rescaled annular equation is
$O(R^2(1+|\log R|))$. The same local barriers and interior upgrade as
in §21 give

$$
V/h=a_*\log R+A_V+O(R^\gamma(1+|\log R|))
\tag{3.5}
$$

with rescaled derivatives. This is the actual inhomogeneous
inherited-wall equation, not a homogeneous scalar reduction.

Use (1.8) with $z=z_L$ and write

$$
\begin{gathered}
D_L=s_z(L)+a(z)c_z(L),\quad
D'_L=c_z(L)-z a(z)s_z(L),\quad r_0=D'_L/D_L,\\
c_b=A_V/a_*+\log b,\qquad
r=\frac{r_0}{1-c_b r_0},\qquad
C_L=\frac{a_*}{D_L(1-c_b r_0)},\\
\Xi_\epsilon(q)=\epsilon^{-1}Z_{z_L}(\delta_{1/\epsilon}q).
\end{gathered}
\tag{3.6}
$$

Uniformly on compact subthreshold sets,

$$
D_L/L\longrightarrow C_\lambda^{-1},\qquad
Lr_0\longrightarrow H_\lambda,\qquad
LC_L\longrightarrow a_*C_\lambda.
\tag{3.7}
$$

In $x=\log(R/b)$ the exterior $f_*+rV$ has affine coefficients
$a_*(1+rc_b)$ and $ra_*$. They equal $C_LD_L$ and $C_LD'_L$
exactly. Choose $r_L=L^{-p}$, with fixed $p$ sufficiently large, and
splice $f_*+rV$ to $C_L\Xi_\epsilon$ on a fixed-width logarithmic collar
about $r_L$. Taylor expansion here has $|x|=O(\log L)$, not $O(L)$;
the exact sine is retained on the whole inner interval.
The quotient-by-$h$ mismatch, with fixed annular derivatives, is

$$
O\bigl(L^{-2}(\log L)^j+r_L^\gamma(\log L)^j\bigr)
\tag{3.8}
$$

for fixed finite $j$. The exponential complement in (1.8) is smaller.
The inner reference is positive on this ball for large $L$, and the
exterior differs relatively from $f_*$ there by $O(L^{-1}\log L)$.
The splice is source-regular inside, truncated away from the source
outside, and belongs to the original $\mathcal F_A$.
Its squared norm is $1+O(L^{-2})$, using $\langle V,f_*\rangle=0$
and the small norm of the replaced ball. Denote its normalization by $t_L$.

Estimate its residual in the dual of (3.3), for all angular tests.
On the exterior the residual at $E_{\rm app}=E_*+\mathsf Kr$ is
exactly

$$
-\mathsf Kr^2V-(g_{\epsilon,\lambda}-g_{\mathrm c})\Gamma(f_*+rV).
\tag{3.9}
$$

An arbitrary $\mathcal N_\epsilon$-unit test has logarithmic mean at
$R$ bounded by $C\sqrt{1+|\log R|}$, from its mean derivative energy
and a fixed outer trace. Its whole mean-zero part is controlled by
Native Green stability, (17.10). Integration only down to $r_L$ bounds
(3.9) by $CL^{-2}(\log L)^j$ in the form dual.

In the inner piece the exact frozen capped equation cancels. The actual
coefficient and full-Green errors leave $W_\epsilon=O(R^{-1})$, derived
explicitly in §4 below. Here $|C_L\Xi_\epsilon/h|\le C$.
Cauchy–Schwarz, Native Green stability, (12.7), for
$\int R^{-1}|f|^2d\mu$, and
$\int_{R<r_L}R^{-1}h^2d\mu=O(r_L)$ give a dual bound
$Cr_L^\delta$ for some $\delta>0$, including the bounded energy term.
Write all splice pairings in the exact $f_*$ transform (3.1).
Their cost is (3.8) times a fixed logarithmic factor; no divergent free
gradient term is bounded separately. With $p\delta>1$,

$$
\|(q_{\epsilon,\lambda}-E_{\rm app})t_L\|_{\mathcal N_\epsilon'}
\le C\{L^{-2}(\log L)^j+r_L^\delta(\log L)^j\}
=:\eta_L=o(L^{-1}).
\tag{3.10}
$$

The normalization correction is included. This is a first-derivative
form estimate, not a singular pointwise $L^2$ residual.

To transfer it to the actual minimum, expand $t_L=\sum t_je_j$ in the
actual finite-cap orthonormal eigenbasis. At its Rayleigh value $r(t_L)$
the squared shifted-form dual residual is
$\sum|e_j-r(t_L)|^2|t_j|^2/(e_j+\beta)$.
The uniform first gap and $r(t_L)\to E_*$ imply, for every $j\ge2$,

$$
e_j-e_1\le C\frac{(e_j-r(t_L))^2}{e_j+\beta},\qquad
e_j+\beta\le C\frac{(e_j-r(t_L))^2}{e_j+\beta}.
\tag{3.11}
$$

These estimates include arbitrarily high eigenvalues. The Rayleigh
excess over the minimum is $O(\eta_L^2)$ and the higher component has
$\mathcal N_\epsilon$ norm $O(\eta_L)$. Since $t_L\to f_*$ in $L^2$,
its overlap with the actual positive ground tends to one, fixing
the first coefficient's sign. Normalization controls its remaining error.
Consequently

$$
E_\epsilon=E_*+\mathsf KH_\lambda/L+o(L^{-1}),\qquad
\|f_\epsilon-t_L\|_{\mathcal N_\epsilon}=o(L^{-1}).
\tag{3.12}
$$

This supplies the lower direction for the actual minimum.

The cap-deficit norm of $f_\epsilon-t_L$ is $o(L^{-1})$, because this
nonnegative term is a summand of $B_\epsilon$. On a fixed scaled
interior annulus the actual core theorem gives $A_\epsilon Z(1+o(1))$,
whereas the trial core is $C_LZ_{z_L}$. Positivity of the deficit on an
interior subannulus first gives $A_\epsilon=O(L^{-1})$ and then
$A_\epsilon-C_L=o(L^{-1})$, since $Z_{z_L}\to Z$.
Thus (2.3) is an amplitude law for actual positive states; no uncapped
trace of a capped state has been assigned.

The error in (3.12) has rescaled mean derivative energy bounded by
$L\,o(L^{-2})=o(1)$. The full-angular collar inequality likewise removes
its rescaled squared norm. Formula (1.8) and matching (3.6) give (2.5).
For the mean of $f_\epsilon/f_*$ the exterior corrector costs a
vanishing $H^1$ error. The trace $f_*/h=a_*+O(R^\gamma)$ transfers the
whole angular $L^2$ profile. Rescaled interior estimates give smoothness
on intermediate annuli, where native coefficient errors and
$E_\epsilon R^2$ both vanish.

The actual raw attraction density in the chart is

$$
\Gamma f_\epsilon^2d\mu
=\left(\frac1{8\pi}+O(R)\right)
                     \phi^2(f_\epsilon/h)^2dt\,da\,d\theta.
\tag{3.13}
$$

Its profile integral is $a_*^2MLJ_\lambda/4$. Cut first at fixed small
$d$, remove the $O(R)$ contribution by the weighted/collar estimates,
then let $d\downarrow0$. The fixed exterior costs $O(1)$.
The actual amplitude and normalized core give every cap constant in
(2.6), with $m_0c_G=1/(2\pi)$ for attraction and $m_0$ for kinetic
energy. In particular $V_{\rm raw}-V_{\rm cap}=O(L^{-2})$.
The exact finite-domain identity

$$
T_A[f_\epsilon]=E_\epsilon+g_{\epsilon,\lambda}V_{\rm cap}[f_\epsilon]
\tag{3.14}
$$

gives the kinetic law. Finally,

$$
\overline q_{\mathrm c}[f_\epsilon]
=E_\epsilon+\frac{\lambda}{L^2}g_{\mathrm c}V_{\rm cap}[f_\epsilon]
             -g_{\mathrm c}(V_{\rm raw}-V_{\rm cap})[f_\epsilon]
\longrightarrow E_*.
\tag{3.15}
$$

Coercivity bounds the critical form norm. Weak convergence, strong
$L^2$ convergence and convergence of shifted norms give strong
$\mathcal Q$ convergence. Normalized-vector convergence gives norm
convergence of the rank-one projections. The charge follows from
$Q_\epsilon/A_\epsilon\to a_*K$. This proves the theorem. $\square$

## 4. A positive native reference at equality and uniform weighted tails

At $\lambda=\lambda_D$, (1.9) gives

$$
q_L=\sqrt{z_L}=\pi/L+\beta_{\rm ang}\pi^3/L^3+O(L^{-5}),\qquad
q_LL=\pi+\beta_{\rm ang}\pi^3/L^2+O(L^{-4}).
\tag{4.1}
$$

The first zero of the auxiliary $Z_{z_L}$ has physical radius tending to
$be^{-\kappa_{\rm cap}}$, by Native Green stability, Corollary 22.2.
Choose a fixed $2d$ strictly below this radius and inside the source
chart. On $R<2d$ the function $\Xi_\epsilon$ from (3.6) is positive.
Extend it by a fixed positive annular interpolation to one, and denote
the global reference by $H_\epsilon$. This is only a comparison
function on the original cylinder; the ball introduces no wall or hole.
On fixed punctured compact sets,

$$
H_\epsilon\longrightarrow H_{\eta_b},\qquad
\eta_b=\log b-\kappa_{\rm cap},\qquad
H_{\eta_b}=h(-\log R+\eta_b)\quad(R<d).
\tag{4.2}
$$

The limiting reference uses the same positive interpolation outside.

On rescaled cap balls the potential is bounded and locally Hölder,
uniformly in the scaled variables. Harnack and interior horizontal
estimates give

$$
|XH_\epsilon|\le C H_\epsilon/R,\qquad
|X_iX_jH_\epsilon|\le C H_\epsilon/R^2.
\tag{4.3}
$$

In the inner core these follow from the sharper $\epsilon$-scaled
bounds; outside use the exact slow wave and its complementary
estimates only on their permitted exterior annuli. Across the cap
the frozen function is weakly matched. There is no interface delta
and no assertion of smoothness of every order across that surface.

In chart variables write
$\mathcal R=L_A-(-\Delta_H)$ and $G_1=\Gamma-c_GR^{-2}$.
The second-order coefficients of $\mathcal R$ are $O(R)$, its
first-order coefficients are $O(1)$, and $G_1=O(R^{-1})$ with the
annular derivative bounds of Native Green stability, §11.
The minimum map is Lipschitz, so

$$
|\Gamma_\epsilon-c_G\min(R^{-2},\epsilon^{-2})|\le C/R.
\tag{4.4}
$$

The frozen detuned capped equation for $\Xi_\epsilon$ cancels exactly.
Equations (4.3)–(4.4), including the density drift in $\mathcal R$,
therefore prove

$$
W_\epsilon=H_\epsilon^{-1}
            (L_A-g_{\epsilon,\lambda_D}\Gamma_\epsilon)H_\epsilon,
\qquad |W_\epsilon|\le C/R
\tag{4.5}
$$

near zero, uniformly in $\epsilon$; it is uniformly bounded elsewhere.
On the original finite-resolution domain the exact product identity is

$$
\begin{aligned}
q_{\epsilon,\lambda_D}[H_\epsilon v]
 &=\mathcal E_\epsilon[v]
                     +\int W_\epsilon H_\epsilon^2|v|^2d\mu,\\
\mathcal E_\epsilon[v]
 &=\int H_\epsilon^2\langle AXv,Xv\rangle d\mu .
\end{aligned}
\tag{4.6}
$$

It follows first for smooth tests by weak integration by parts, then by
free-form approximation. For fixed $\epsilon$, $H_\epsilon$ is positive
and source-regular, so multiplication identifies the appropriate
quotient domain with the original $\mathcal F_A$. The same local
cancellation proves the inner residual estimate used in §3, without
requiring a normalized actual-state trace.

We prove uniform tail bounds for all quotient directions. Put
$t=\log R$, $t_\epsilon=\log\epsilon$. Up to fixed positive angular
factors, $H_\epsilon/h$ is comparable to the scalar weight

$$
w_\epsilon(t)\asymp
\begin{cases}
e^{t-t_\epsilon},&t\le t_\epsilon,\\
\min(1+t-t_\epsilon,-t+\eta_b),&t_\epsilon\le t\le\log d.
\end{cases}
\tag{4.7}
$$

The positive core proves this on its first collars. Beyond them the
exact sine, whose phase runs from near zero to below $\pi$, is
comparable to the minimum of its distances from the two zeros.
The exponential complement preserves the comparison, including
the polar endpoints. In particular

$$
\frac{w_\epsilon(t)}{w_\epsilon(s)}\le C(1+s-t),
\qquad t\le s\le\log d.
\tag{4.8}
$$

The constant is independent of the resolution. The limiting weight
$w(t)=-t+\eta_b$ has the same property.

For a quotient with zero outer cutoff let
$F_v(t,a)=(\int_0^{2\pi}|v|^2d\theta)^{1/2}$.
The full-angular diamagnetic inequality of Native Green stability,
(12.9), and comparability give control of

$$
\int w_\epsilon^2 c\phi^2
                         (|(F_v)_t|^2+4|(F_v)_a|^2)\,dt\,da
\tag{4.9}
$$

by $\mathcal E_\epsilon[v]$, with a fixed constant. This norm includes
every angular direction. For $T\le\log d$ use
$F_v(t)=-\int_t^T(F_v)_sds$ and (4.8). After multiplying by
$e^{pt/2}w_\epsilon(t)$, Young's inequality with the integrable kernel
$(1+u)e^{-pu/2}$ gives

$$
\int_{-\infty}^T e^{pt}w_\epsilon^2 c\phi^2F_v^2\,dt\,da
\le C_pe^{pT}\int_{-\infty}^T
                   w_\epsilon^2c\phi^2|(F_v)_t|^2\,dt\,da,\qquad p>0.
\tag{4.10}
$$

The endpoint inequality (12.10) of Native Green stability supplies the
unweighted angular norm: apply it at each $t$ and bound its derivative
term using $e^{pt}\le e^{pT}$. Localization and $p=1,2$ yield the
uniform counterparts of its (12.7). In particular $|W_\epsilon|$ is
uniformly infinitesimally form bounded, and for a fixed sufficiently
large shift the actual form norm is equivalent to

$$
\mathfrak N_\epsilon(H_\epsilon v)^2
                 =\mathcal E_\epsilon[v]+\|H_\epsilon v\|_2^2.
\tag{4.11}
$$

There is also a useful quantitative tail. Anchor $F_v$ at a fixed outer
trace and integrate its derivative by Cauchy–Schwarz. Equation (4.8)
implies
$w_\epsilon(t)\|\sqrt c\,\phi F_v(t)\|
\le C(1+|t|)^{3/2}\mathfrak N_\epsilon(H_\epsilon v)$.
Integrate this bound with $e^{pt}$ and apply the angular endpoint
inequality to the derivative part as in (4.10). For $p=1,2$,

$$
\int_{R<r}R^{p-2}|H_\epsilon v|^2d\mu
\le Cr^p(1+|\log r|)^3
              \{\mathcal E_\epsilon[v]+\|H_\epsilon v\|_2^2\}.
\tag{4.12}
$$

The same estimates hold for $H_{\eta_b}$, and locally uniformly for
nearby $\eta$. Thus both the source $L^2$ mass and the $R^{-1}$
potential tail vanish uniformly on bounded shifted sublevels.
Away from the source those sublevels are bounded in the actual local
free form, with its compact embedding. This proves collective $L^2$
compactness without scalar finite-energy separation or any estimate
on an uncapped complex trace of a capped state.

## 5. The natural logarithmic source form and positive point capacity

**Definition 5.1 (natural source domain).** For any real $\eta$ choose a
positive $H_\eta$ equal to $h(-\log R+\eta)$ on a sufficiently small
source ball and smoothly positive elsewhere. Let $\mathcal V_\eta$ be
the completion, in weighted horizontal energy plus weighted $L^2$, of
quotients smooth away from the source, constant on some source
neighbourhood, and satisfying the inherited outer killing. Put

$$
\begin{aligned}
W_\eta&=H_\eta^{-1}\mathcal T H_\eta,\\
q_\eta[H_\eta v]
 &=\int H_\eta^2\langle AXv,Xv\rangle d\mu
                   +\int W_\eta H_\eta^2|v|^2d\mu,\qquad
D(q_\eta)=H_\eta\mathcal V_\eta.
\end{aligned}
\tag{5.1}
$$

The expression for $W_\eta$ is taken off the source. The frozen
critical equation for both $h$ and $h\log R$, together with the native
coefficient and Green remainders, gives $W_\eta=O(R^{-1})$.

**Proposition 5.2 (domain, capacity and source condition).**
The completion in Definition 5.1 is the full finite weighted-energy
space with the inherited outer condition. It has a continuous scalar
source trace. The point has positive capacity for this log-squared
weight, and

$$
D(q_\eta)=\mathcal Q\dotplus
       \operatorname{span}\{\chi h(-\log R+\eta)\},
\tag{5.2}
$$

where $\chi=1$ near zero is a smooth chart cutoff.
The zero-trace subspace is exactly $\mathcal Q$ after multiplication
by $H_\eta$. The form is closed, semibounded, compactly embedded in
$L^2(\mu)$, and independent of the positive interpolation.
Its represented operator, denoted $F_\eta$, is the inherited-wall
critical realization

$$
D(F_\eta)=\{u\in D(S_{D,\max}):
                         \mathcal A(u)+\eta\mathcal B(u)=0\}.
\tag{5.3}
$$

Proof. Write $w=-t+\eta$ near the source. For a finite-energy quotient
$v$, its $c\phi^2$ mean $p_v$ has $\int w^2|p_v'|^2dt<\infty$.
Since
$\int_{-\infty}^T w^{-2}dt=(-T+\eta)^{-1}$ is finite, its scalar
trace $p_v(-\infty)$ exists. More precisely,

$$
|p_v(t)-p_v(-\infty)|^2
\le\frac1{-t+\eta}\int_{-\infty}^t(-s+\eta)^2|p_v'(s)|^2ds.
\tag{5.4}
$$

The outer trace estimate and this inequality bound the source trace
by the weighted energy plus $L^2$ norm. A quotient constant one near
the point has nonzero trace and finite norm. Continuity therefore
gives a strictly positive lower bound for its squared norm among all
such quotients. This is positive point capacity. Closing only
punctured quotients would impose zero source trace and discard a
genuine direction.

We verify density in the full finite-energy space. Write
$v=p_v+v^\perp$ on the inner cylinder. The all-angular collar
Poincaré inequality of Native Green stability, (17.10), controls the
entire mean-zero remainder. Multiply by the log-squared weight, which
is comparable on each enlarged collar. Cut $v^\perp$ to zero for
$t<-2T$ and join on $[-2T,-T]$. Its derivative error is bounded by
the weighted energy tail, using the collar inequality and the
$O(T^{-1})$ cutoff derivative, and tends to zero.
Cut $p_v$ instead to $p_v(-\infty)$ on that interval. Equation (5.4)
bounds the new derivative cost by a constant times
$\int_{-\infty}^{-T}w^2|p_v'|^2$, which tends to zero.
Norm and potential tails vanish by (4.12).
Ordinary local approximation away from the point completes the
density proof, while retaining the original outer condition.

For trace zero, (5.4) implies $w|p_v|^2\to0$. The remainder has the
same vanishing boundary contribution in the collar approximation.
Expanding the critical weighted energy of $wv$ gives, in its radial
part,

$$
|(wv)'|^2=w^2|v'|^2-(w|v|^2)'.
\tag{5.5}
$$

The angular and mixed terms obey the same product identity because
$w$ depends only on $t$; the native lower-order terms agree by the
full ground transform. The source term in (5.5) vanishes for trace
zero. Thus these quotients multiply precisely into the critical
completion $\mathcal Q$. Conversely, the punctured core is dense in
$\mathcal Q$; its two product identities agree, so the zero-trace
approximation and trace continuity put every $\mathcal Q$ vector
in that subspace. Subtracting the scalar trace times $\chi$ proves
(5.2), with a genuinely direct sum.

Weighted kinetic energy is closable: test weak derivative limits on
compact sets away from the point, where its density is smooth and
positive, then use that the point has measure zero. Equations
(4.10)–(4.12) make $W_\eta$ infinitesimally form bounded. The usual
closed-form perturbation and representation theorems, with these
specific bounds, give closedness and semiboundedness. The same tails
and actual local free compactness give compact embedding.
Changing the positive interpolation is multiplication of quotients
by a smooth positive ratio equal to one near the point. It preserves
the dense natural domain, and the product identities agree there.
Closedness proves independence of interpolation.

For a finite-energy operator solution let $u/h=A+B t+O(R^\gamma)$.
Then

$$
\partial_t(u/H_\eta)=\frac{A+\eta B}{(-t+\eta)^2}
                                    +O(R^\gamma)
\tag{5.6}
$$

with harmless logarithmic improvements in the error. Its full source
conormal is $K(A+\eta B)$ in the convention (1.6).
Testing (5.1) against a quotient constant near zero forces this to
vanish. Conversely this condition cancels the source pairing.
For general operator vectors the identical conclusion follows by
graph approximation and the graph-continuous pair in (1.6); a uniform
pointwise trace on the whole maximal domain is unnecessary.
The inherited-wall domain theorem then identifies (5.3).
Thus the source condition is derived from the natural form, not
selected in advance. $\square$

## 6. The full inherited-wall response and the finite selected energy

**Theorem 6.1 (actual global response).** For every $E<E_*$ there is a
unique inherited-wall maximal solution $U_E\in L^2(\mu)$ of
$(\mathcal T-E)U_E=0$ with $\mathcal B(U_E)=-1$. It is strictly
positive and has the all-angular expansion

$$
U_E/h=-\log R+\eta(E)+O(R^\gamma).
\tag{6.1}
$$

The response $\eta:(-\infty,E_*)\to\mathbb R$ is real analytic,
strictly increasing and onto. For any $E_0<E_*$,

$$
\begin{aligned}
U_E&=U_{E_0}+(E-E_0)(F-E)^{-1}U_{E_0},\\
\eta(E)&=\eta(E_0)+\frac{E-E_0}{K}
 \{\|U_{E_0}\|_2^2+
           (E-E_0)\langle(F-E)^{-1}U_{E_0},U_{E_0}\rangle\},\\
\frac{\eta(E)-\eta(E')}{E-E'}
 &=\frac{\langle U_E,U_{E'}\rangle}{K}>0,\qquad
\eta'(E)=\|U_E\|_2^2/K.
\end{aligned}
\tag{6.2}
$$

For every real $\eta$, let $E_\eta<E_*$ be its unique response root,
and put

$$
\eta(E_\eta)=\eta,\qquad
a_\eta=\|U_{E_\eta}\|_2^{-1}
                 =[K\eta'(E_\eta)]^{-1/2},\qquad
f_\eta=a_\eta U_{E_\eta}.
\tag{6.3}
$$

Then $(E_\eta,f_\eta)$ is the simple positive normalized ground pair
of $F_\eta$, and $dE_\eta/d\eta=Ka_\eta^2$.

Proof. Use the genuine native vector $\zeta$, not the bare expression
$h\log R$, and define

$$
U_E=-\zeta+(F-E)^{-1}(S_{D,\max}-E)\zeta.
\tag{6.4}
$$

Every term retains the original killed outer walls. The trace is
$\mathcal B=-1$, the equation holds, and the difference of any two
such solutions would be an $F$ eigenvector below $E_*$. This proves
existence and uniqueness. The finite-energy expansion (1.6) gives
(6.1) and positivity near the source. The negative part vanishes
there and belongs to $\mathcal Q$. Testing its equation by this part,
using $q_F-E>0$, proves nonnegativity everywhere. Local positivity
on the connected punctured cylinder gives $U_E>0$.

Apply (1.6) to $U_E,U_{E'}$, whose traces are $(\eta(E),-1)$ and
$(\eta(E'),-1)$. It gives the third identity in (6.2), with the
displayed positive sign. Resolvent subtraction gives its first
identity, and substitution gives its second. Analyticity and the
derivative follow.

For each $\eta$, Proposition 5.2 supplies a compact semibounded form
containing $\mathcal Q$ and agreeing with $q_F$ on it. Its minimum
is at most $E_*$. If it equalled $E_*$, the normalized minimizer
$f_*\in\mathcal Q$ would also be an operator ground of $F_\eta$,
contradicting its traces $(a_*,0)$ and (5.3).
Hence its minimum is strictly below $E_*$. Modulus decreases the
weighted kinetic form; local positivity gives a positive minimizer.
The exact transform by this positive ground shows simplicity.
Its logarithmic trace is nonzero, or it would be an $F$ eigenvector
below $E_*$. Positivity makes that coefficient negative. Normalize
it to $-1$ and apply (6.4); its source condition yields
$\eta(E_\eta)=\eta$.
This proves surjectivity without a frozen exterior finite part or a
large-negative-energy approximation. Strict monotonicity proves
uniqueness, and normalization gives (6.3).

As an orientation and normalization check, pairing $U_E$ with $f_*$
in (1.6) gives

$$
(E-E_*)\langle U_E,f_*\rangle=-Ka_*.
\tag{6.5}
$$

In particular the response is that of the entire killed native model,
not a universal source-local energy constant. $\square$

## 7. Equality selection by both variational directions and actual amplitude

**Theorem 7.1 (cap-selected equality ground).** Define

$$
\eta_b=\log b-\kappa_{\rm cap},\qquad
E_D=E_{\eta_b},\qquad a_D=a_{\eta_b},\qquad f_D=f_{\eta_b}.
\tag{7.1}
$$

For the original fixed family at $\lambda=\lambda_D$,
$E_{\epsilon,\lambda_D}\to E_D$ and
$f_{\epsilon,\lambda_D}\to f_D$ strongly in $L^2(\mu)$.
The positive ground projections converge in norm, with no source or
exterior norm lost, and the states converge smoothly on compact
interior sets away from $o$. The selected ground belongs to
$D(F_{\eta_b})$ and satisfies

$$
f_D/h=a_D(-\log R+\eta_b)+O(R^\gamma),\qquad
\mathcal A+\eta_b\mathcal B=0.
\tag{7.2}
$$

It is outside both $\mathcal Q$ and $\mathcal F_A$, and differs from
$f_*$. Equivalently, its source line is
$\mathcal A/\mathcal B=\kappa_{\rm cap}-\log b$.
Its energy always satisfies $E_D<E_*$. If $E_*\le0$, then $E_D<0$.
If $E_*>0$, the sign of $E_D$ is negative, zero or positive according
as $\eta_b$ is smaller than, equal to, or larger than the genuine
global $\eta(0)$.

Proof. On every fixed punctured compact set, $H_\epsilon$ and
$W_\epsilon$ converge to $H_{\eta_b}$ and $W_{\eta_b}$.
Consider any sequence with bounded shifted $q_{\epsilon,\lambda_D}$
and weak $L^2$ limit. Equations (4.11)–(4.12) give collective strong
$L^2$ compactness. Locally, the quotients have weak horizontal
derivative limits. Lower semicontinuity gives the kinetic lower
inequality; the $R^{-1}$ tail estimate and strong local convergence
pass the entire potential term, including its signed part.
The limit has finite weighted energy and hence belongs to the
natural domain of §5. This proves the lower form inequality.

For recovery first take a dense natural quotient $v$ smooth away
from the point and constant on a source ball. Its product
$H_\epsilon v$ is in the original $\mathcal F_A$: the core is
source-regular, its free kinetic energy is finite at each fixed
resolution, and the quotient retains outer killing.
Derivative energies converge away from the ball, where $v$ is
constant inside. Norm and potential tails are uniformly negligible
by (4.12). Thus its norm and full energy converge.
Diagonal approximation gives recovery for every $q_{\eta_b}$ vector.
These are both directions for the original forms and their actual
minima, not just a trial upper bound.

Compact min-max at the lowest eigenvalue and the simple positive
ground of Theorem 6.1 give the stated energy and normalized-vector
limits. Modulus and local positivity fix the sign. Norm convergence
of the rank-one projections follows directly. The actual equations
and local hypoelliptic estimates upgrade the convergence on
punctured interior compact sets. Formula (7.2), its domain
distinction, and the sign classification follow from §§5–6.

We also need a stronger tail fact than mere boundedness.
Put $v_\epsilon=f_\epsilon/H_\epsilon$. The potential terms
converge by the same $R^{-1}$ tail argument. Since the actual
energies converge, their total transformed kinetic energies converge
to that of $f_D/H_{\eta_b}$. Local lower semicontinuity on complements
of shrinking balls therefore yields

$$
\lim_{d\downarrow0}\limsup_{\epsilon\downarrow0}
       \mathcal E_\epsilon[v_\epsilon;R<d]=0.
\tag{7.3}
$$

This is convergence and exhaustion of the varying-reference energy.
It is not convergence in the fixed critical form norm. $\square$

**Proposition 7.2 (actual equality source amplitude).** At equality,

$$
A_\epsilon\longrightarrow a_D,\qquad
\epsilon f_\epsilon(\Psi^{-1}\delta_\epsilon x)
                         \longrightarrow a_D Z(x).
\tag{7.4}
$$

The second convergence is locally uniform and strong in local
horizontal $W^{1,2}$ through the source and the cap interface.
It is smooth on compact sets off $R=1$. In particular
$\epsilon f_\epsilon(o)\to a_DZ(0)$.

Proof. The $c\phi^2$ mean of $v_\epsilon$ has derivative controlled
by $\int w_\epsilon^2|p'|^2$. Between a fixed scaled exterior collar
$y=\log(R/\epsilon)=T$ and a fixed small original radius $d$, its
reciprocal resistance is uniformly bounded. More precisely the
exact sine part gives

$$
\int_{\log\epsilon+T}^{\log d}w_\epsilon^{-2}dt
\le C\{(T+\kappa_{\rm cap})^{-1}
                           +(-\log d+\eta_b)^{-1}\}.
\tag{7.5}
$$

Indeed the relevant primitive is a difference of $q_L$ cotangents:
integrate $q_L^2\csc^2(q_L(t-\log\epsilon)+\delta(q_L))$.
The lower and upper endpoint asymptotics give the two terms.
Choose $T$ beyond the initial exterior collars so the complement
is controlled; the finitely many remaining core collars contribute
only a bounded resistance. Angular factors are uniformly comparable.

The fixed outer mean is bounded by Theorem 7.1. Cauchy–Schwarz,
(7.5), and the bounded shifted energy bound the inner mean.
Harnack on the cap ball and the actual normalized core theorem
identify the quotient on each fixed scaled collar as
$A_\epsilon(1+o(1))$, because $Z_{z_L}\to Z$.
This first proves that the actual $A_\epsilon$ is bounded.
Now use the exhausted energy tail (7.3) in the same
Cauchy–Schwarz estimate. It gives

$$
\lim_{d\downarrow0}\limsup_{\epsilon\downarrow0}
 |A_\epsilon-\mathcal Mv_\epsilon(\log d)|=0.
\tag{7.6}
$$

The outer mean tends to that of $f_D/H_{\eta_b}$ and then, by (7.2),
to $a_D$. This proves the first limit in (7.4).
The actual normalized core and its strong horizontal convergence
then prove the second. Only the identified limiting maximal
solution receives the traces in (7.2). $\square$

## 8. The negative equality correction, including a zero limiting energy

**Theorem 8.1 (sharp equality energy).** For each fixed model and fixed
admissible $b$,

$$
E_{\epsilon,\lambda_D}
   =E_D-\frac{K a_D^2\beta_{\rm ang}\pi^2}{L}+o(L^{-1}).
\tag{8.1}
$$

The correction coefficient is strictly negative. In particular, if
the genuine response root $E_D$ is zero, then
$E_{\epsilon,\lambda_D}\sim-Ka_D^2\beta_{\rm ang}\pi^2/L$.

Proof. At fixed punctured source radii the exact sine in (1.8), (4.1)
and $\delta(q)=\kappa_{\rm cap}q+O(q^3)$ give

$$
\frac{\Xi_\epsilon}{h}
=-\log R+\eta_b-\frac{\beta_{\rm ang}\pi^2}{L}
             +O\bigl(L^{-2}(1+|\log R|)^3\bigr).
\tag{8.2}
$$

The same statement holds with every fixed rescaled derivative,
including all angular directions. To see the sign, put
$x=\log(R/b)$ and expand the exact argument
$q_L(L+x)+\delta(q_L)$ about $\pi$.
Its excess is $q_L(x+\kappa_{\rm cap})+
\beta_{\rm ang}\pi^3/L^2+O(L^{-3}(1+|x|))$.
The sine divided by $q_L$ has the negative intercept in (8.2).
The phase beyond $\kappa_{\rm cap}q_L$, the factor $A(q_L)-1$
and $\phi_{z_L}-\phi$ contribute only at order $L^{-2}$ here.
Thus a fixed-$y$ Taylor expansion has not been used on an interval
of length $L$.

Set

$$
\eta_L=\eta_b-\beta_{\rm ang}\pi^2/L,\qquad
v_L=f_{\eta_L}/H_{\eta_L}.
\tag{8.3}
$$

Use a smooth common positive interpolation for the $H_\eta$.
The actual global response is analytic for $\eta$ near $\eta_b$.
Its source expansion and source condition give, uniformly there,

$$
v_L=a_{\eta_L}+O(R^\gamma),\qquad
|Xv_L|\le CR^{\gamma-1}
\tag{8.4}
$$

with rescaled derivatives. The legitimate free-domain trial is
$H_\epsilon v_L$, subsequently normalized. It is in $\mathcal F_A$:
$v_L$ is bounded near the source with the derivative bound (8.4),
and $H_\epsilon$ is source-regular for fixed $\epsilon$.
The local integrals of the resulting free derivatives are finite;
free zero-capacity cutoff removes the point, and the outer domain
is inherited.

Here a quantitative comparison in the full form dual is necessary.
Fix $r_L=L^{-p}$ with $p$ large, and split at $r_L$. On
$R\ge r_L$ the reference ratios and their rescaled derivatives
from (8.2) differ by
$O(L^{-2}(1+|\log R|)^j)$ for fixed finite $j$.
Crucially, cancel the frozen equations before comparing residual
potentials. On the exterior cap region they give exactly

$$
W_\epsilon=\Xi_\epsilon^{-1}\mathcal R\Xi_\epsilon
                                    -g_{\epsilon,\lambda_D}G_1,
\qquad
W_{\eta_L}=H_{\eta_L}^{-1}\mathcal R H_{\eta_L}
                                    -g_{\mathrm c}G_1.
\tag{8.5}
$$

The principal coefficients of $\mathcal R$ are $O(R)$, its drift
is $O(1)$, and $G_1=O(R^{-1})$. The derivative comparisons therefore
give

$$
|W_\epsilon-W_{\eta_L}|
\le C L^{-2}(1+|\log R|)^j/R,\qquad r_L\le R<d.
\tag{8.6}
$$

There is no uncontrolled $L^{-2}R^{-2}$ term. Away from the small
reference ball the interpolation and bounded Green multiplier give
the ordinary $O(L^{-2})$ comparison. Weighted Cauchy–Schwarz and
(4.10)–(4.12) bound the exterior coefficient, potential and mass
errors by $CL^{-2}(\log L)^j$ in the dual of
$\mathfrak N_\epsilon$.

An arbitrary test quotient for the finite cap need not be in the
limiting full weighted test space. Insert an inner cutoff at $r_L$
before using the $q_{\eta_L}$ equation. The terms from conversion
of the test spaces contain $Xv_L$ and the cutoff derivative.
By (8.4) they are $O(r_L^\delta(1+|\log r_L|)^j)$ in that dual,
for some $\delta>0$. On $R<2r_L$ use
$H_\epsilon\le Ch(1+|\log R|)$, (8.4), and the $p=1$ tail in
(4.12); they give the same bound for the kinetic, potential and
bounded spectral terms. The constant part of $v_L$ contributes no
singular gradient flux. These estimates explain why the two full
test spaces were not silently identified.

After normalization the trial, denoted $t_{\epsilon,L}$, has norm
correction of the same small order and residual

$$
\|(q_{\epsilon,\lambda_D}-E_{\eta_L})t_{\epsilon,L}\|_
                                             {\mathfrak N_\epsilon'}
\le C\{L^{-2}(\log L)^j+r_L^\delta(\log L)^j\}
=o(L^{-1})
\tag{8.7}
$$

when $p\delta>1$. All powers and exponents here are fixed;
they do not depend on $L$.

Theorem 7.1 gives overlap
$\langle t_{\epsilon,L},f_{\epsilon,\lambda_D}\rangle\to1$,
and (4.11) uniformly bounds the latter state's shifted norm.
Pair the residual with that actual ground. Selfadjointness gives

$$
(E_{\epsilon,\lambda_D}-E_{\eta_L})
 \langle t_{\epsilon,L},f_{\epsilon,\lambda_D}\rangle=o(L^{-1}).
\tag{8.8}
$$

This proves both energy directions, without differentiating a
remainder or relying on a trial bound alone.
Finally (6.3) gives $dE_\eta/d\eta=Ka_\eta^2$.
Insert (8.3) and use continuity of $a_\eta$ to obtain (8.1).
Since $\beta_{\rm ang}>0$ and $a_D>0$, its coefficient remains
nonzero even at $E_D=0$. $\square$

## 9. The equality profile and the divergent separate resources

**Theorem 9.1 (actual equality profile and costs).** On
$R=\epsilon e^{sL}$, the full unrestricted angular state satisfies

$$
\frac{f_{\epsilon,\lambda_D}}{Lh}
       \longrightarrow\frac{a_D}{\pi}\sin(\pi s)
                       \quad\text{in }L^2(\phi^2ds\,da\,d\theta).
\tag{9.1}
$$

Its $c\phi^2$ slice mean converges to the same scalar function in
$H^1(0,1)$. On intermediate logarithmic scales the rescaled
Cartesian-annulus convergence is smooth. The original total costs are

$$
\begin{aligned}
\frac{V_{\rm raw}[f_\epsilon]}{L^3},\quad
\frac{V_{\rm cap}[f_\epsilon]}{L^3}
       &\longrightarrow\frac{a_D^2M}{8\pi^2},\\
\frac{T_A[f_\epsilon]}{L^3}
       &\longrightarrow\frac{g_{\mathrm c}a_D^2M}{8\pi^2},\\
\frac{T_A[f_\epsilon]-g_{\mathrm c}V_{\rm cap}[f_\epsilon]}L,\quad
\frac{T_A[f_\epsilon]-g_{\mathrm c}V_{\rm raw}[f_\epsilon]}L
       &\longrightarrow\frac{Ka_D^2}{2}.
\end{aligned}
\tag{9.2}
$$

The actual moving-cap costs and linear charge have finite limits:

$$
\begin{aligned}
(V_{\rm raw}-V_{\rm cap})[f_\epsilon]
       &\longrightarrow\frac{a_D^2I}{2\pi},\\
\int_{\mathcal C_\epsilon}\Gamma f_\epsilon^2d\mu
       &\longrightarrow\frac{a_D^2J_{\rm raw}}{2\pi},\\
\int_{\mathcal C_\epsilon}\Gamma_\epsilon f_\epsilon^2d\mu
       &\longrightarrow\frac{a_D^2J_{\rm cap}}{2\pi},\\
T_A[f_\epsilon;\mathcal C_\epsilon]
       &\longrightarrow m_0a_D^2J_T,\\
g_{\mathrm c}\int_{\mathcal C_\epsilon}\Gamma_\epsilon f_\epsilon^2d\mu
       &\longrightarrow m_0a_D^2N=Ka_D^2/2,\\
Q_\epsilon&\longrightarrow Ka_*a_D.
\end{aligned}
\tag{9.3}
$$

In particular finite detuned energy does not give bounded kinetic or
attraction resources. These states cannot converge in the fixed
critical form norm. All assertions are for the fixed model and $b$.

Proof. Let $v_\epsilon=f_\epsilon/H_\epsilon$.
The amplitude proof, the resistance estimate (7.5) and the exhausted
inner energy (7.3) make its quotient mean tend to $a_D$ on every
intermediate logarithmic interval. The full weighted collar Poincaré
inequality controls its entire angular remainder. This is not a
projection of the actual equation onto a presumed scalar solution.
Positive-state Harnack on fixed rescaled annuli bounds the quotient
by its mean, uniformly on successive collars. The core estimate and
the fixed outer smooth limit extend the bound to the two ends.

On the exterior part of the reference, its exact slow factor is

$$
A(q_L)\frac{\sin(q_L\log(R/\epsilon)+\delta(q_L))}{q_L}.
\tag{9.4}
$$

After division by $L$ it tends to $\sin(\pi s)/\pi$.
The angular eigenfunction tends to $\phi$; the complementary term
decays away from the fixed scaled core. The preceding quotient
bounds dominate both end collars, so their rescaled contributions
vanish as the collars shrink. The weighted angular energy makes the
whole complementary squared norm $o(L^3)$ in the unscaled
$dt\,da\,d\theta$ profile integral. This proves the full $L^2$ limit.

For the derivative of the normalized slice mean, differentiate the
exact slow factor, retaining its sine on the full growing interval.
Its derivative tends to $\cos(\pi s)$. The term containing the
quotient derivative has squared rescaled norm bounded by
$C\mathcal E_\epsilon[v_\epsilon]/L=o(1)$.
The angular collar inequality controls the complementary derivatives.
The fixed outer interval has length $O(L^{-1})$ in $s$ and bounded
derivatives after normalization; core and adjacent collars have
the same negligible rescaled cost. These estimates give the
asserted $H^1$ convergence. Interior estimates for the actual
rescaled equation give smooth convergence on intermediate
Cartesian annuli, including their axis.

Use the actual density (3.13). The main integral in the logarithmic
region is

$$
\frac1{8\pi}(2\pi)M
       \frac{a_D^2L^3}{\pi^2}\int_0^1\sin^2(\pi s)\,ds
                =\frac{a_D^2M L^3}{8\pi^2}.
\tag{9.5}
$$

The weighted angular remainder is $o(L^3)$.
Uniform logarithmic bounds and a fixed-$d$ cutoff make the $O(R)$
density/full-Green error $o(L^3)$ as well. The fixed exterior
attraction is $O(1)$ since $\Gamma$ is bounded there.
The actual core theorem and (7.4) give an $O(1)$ core cost.
Thus (9.5) is an actual-state equivalent with both upper and lower
directions.

The normalized core theorem with $A_\epsilon\to a_D$ proves the
first three finite costs in (9.3). Its factors are the state square
$A_\epsilon^2\epsilon^{-2}$, multiplier $c_G\epsilon^{-2}$, and
measure $\epsilon^4m(\delta_\epsilon x)dq$, leaving
$m_0c_G=1/(2\pi)$. Hence $V_{\rm raw}-V_{\rm cap}=O(1)$ and the
same $L^3$ equivalent holds for the capped total.
Strong local horizontal convergence, smooth coefficient convergence
and the changed-set sandwich
$\{R<\epsilon(1-C\epsilon)\}\subset\mathcal C_\epsilon
\subset\{R<\epsilon(1+C\epsilon)\}$
give the moving kinetic limit. Strong energy convergence controls
the shrinking collar at $R=1$. The identity
$\lambda_0J_{\rm cap}=N$ proves its displayed capped-core
consequence. The linear charge follows from its actual
amplitude-normalized limit in §1.

Finally use (3.14), with no subtraction of infinite quantities:

$$
\frac{T_A-g_{\mathrm c}V_{\rm cap}}L
 =\frac{E_\epsilon}L+
       g_{\mathrm c}\lambda_D\,\frac{V_{\rm cap}}{L^3}
\longrightarrow
\frac{g_{\mathrm c}\lambda_Da_D^2M}{8\pi^2}
=\frac{Ka_D^2}{2}.
\tag{9.6}
$$

The raw version differs by $O(1)/L$. This proves (9.2), including
the kinetic equivalent. Since each capped state lies in
$\mathcal F_A\subset\mathcal Q$, its critical form value is the
finite difference $T_A-g_{\mathrm c}V_{\rm raw}$.
That value diverges linearly and positively by (9.6), excluding
fixed-$\mathcal Q$ convergence despite the finite limit of its
detuned total energy. $\square$

## 10. The threshold precision window

**Corollary 10.1 (order-one response to third-order relative detuning).**
Evaluate the same family (1.2), with the same fixed model and $b$, at

$$
\lambda(L)=\lambda_D+\sigma/L,\qquad \sigma\in\mathbb R\text{ fixed}.
\tag{10.1}
$$

Put

$$
\eta_\sigma=\log b-\kappa_{\rm cap}
                         -\frac{\alpha\sigma}{2\pi^2}.
\tag{10.2}
$$

Its actual positive normalized ground converges strongly in
$L^2(\mu)$ to $f_{\eta_\sigma}$ from (6.3), with smooth punctured
interior convergence and norm convergence of the rank-one ground
projection. Its energy tends to $E_{\eta_\sigma}$, and its actual
source amplitude tends to $a_{\eta_\sigma}$.
The $L^3$ total resource limits in the first two lines of (9.2)
hold with $a_D$ replaced by $a_{\eta_\sigma}$.
These statements are uniform for $\sigma$ in each compact real
set, with model and $b$ fixed.

Proof. Invert the same angular eigenvalue series:

$$
q_LL=\pi+\frac{\alpha\sigma}{2\pi L}+O(L^{-2}).
\tag{10.3}
$$

Inserting this into the exact response (9.4), at fixed source
radii, changes its finite intercept by
$-\alpha\sigma/(2\pi^2)$. Thus the positive reference tends to
$h(-\log R+\eta_\sigma)$.
On a compact $\sigma$ set choose a single small reference ball
below all first zeros. The weight-ratio, all-angular tail and
compactness estimates of §4 hold uniformly there. The natural
domain, lower inequality and recovery of §§5 and 7 identify the
actual limit. The resistance and exhausted-energy argument
identifies its amplitude, and the profile integration of §9 gives
the $L^3$ resource constants. The parameters $\eta_\sigma$ lie in a
compact real interval; their response roots lie in a compact
subset of $(-\infty,E_*)$ by Theorem 6.1. All constants required
in these arguments can therefore be chosen uniformly.

A fixed nonzero change $\Delta\sigma$ changes the actual relative
coupling by $\Delta\sigma/L^3$ and the selected parameter by
$-\alpha\Delta\sigma/(2\pi^2)$. Its finite energy limit changes by
a nonzero amount through the strictly increasing response.
The fixed $\lambda_D$ family is exactly $\sigma=0$.
This corollary does not classify arbitrary varying-$\lambda$
sequences, and does not extend the first correction (8.1) to
nonzero $\sigma$. $\square$

## 11. Source covariance, primary correspondence and ground-state scope

Every coefficient above uses the exact native inverse Jacobian
$1/(2r)$, graded covariance factor $\det A(o)$, full $2\pi$ angular
period and polar Jacobian $1/4$. In particular

$$
m_0c_G=\frac1{2\pi},\qquad
K=m_0\frac\pi2C,\qquad
\mathsf K=a_*^2K,\qquad
g_{\mathrm c}\lambda_D\frac{a_D^2M}{8\pi^2}
   =\frac{Ka_D^2}{2}
   =\frac{g_{\mathrm c}a_D^2J_{\rm cap}}{2\pi}.
\tag{11.1}
$$

The retained coefficient and equality coefficient are respectively
$\mathsf K$ and $Ka_D^2$. Neither can be replaced by the other.
The cap law uses $A_\epsilon$, never hypothetical maximal traces of
finite-cap states. The uncapped traces are assigned only to the
actual identified limiting maximal solutions.

There is a second check of the source orientation. The exact mixed
finite-resolution eigenvalue identity is

$$
(E_\epsilon-E_*)\langle f_\epsilon,f_*\rangle
=Q_\epsilon-\frac{g_{\mathrm c}\lambda_D}{L^2}
                       \int\Gamma_\epsilon f_*f_\epsilon d\mu
\tag{11.2}
$$

at equality. The mixed version of the actual profile integration gives

$$
\frac{g_{\mathrm c}\lambda_D}{L^2}
                    \int\Gamma_\epsilon f_*f_\epsilon d\mu
\longrightarrow
\frac{g_{\mathrm c}\lambda_DMa_*a_D}{4\pi}
                    \int_0^1\sin(\pi s)ds
=2Ka_*a_D.
\tag{11.3}
$$

Together with (9.3), this agrees with
$(E_D-E_*)\langle f_D,f_*\rangle=-Ka_*a_D$ from (6.5).
It fixes the sign against the original full-Green normalization
and not merely against a convention for a scalar extension.

Under $\rho\mapsto c_1\rho$, $c_1>0$, the exact source law gives
$m_0,K,g_{\mathrm c}\mapsto c_1(m_0,K,g_{\mathrm c})$ and
$\Gamma\mapsto\Gamma/c_1$.
Normalized $a_*,a_D,A_\epsilon$ divide by $\sqrt{c_1}$.
The response $\eta$, its roots, and the energies are unchanged;
energy and kinetic coefficients are invariant, while raw and capped
attraction coefficients divide by $c_1$. Equations (2.6), (8.1)
and (9.2)–(9.3) have exactly this covariance.
All constants and uniformities refer to the original covariance
$2A\,dt$ and a fixed admissible model.

For primary correspondence, Derkach–Hassi–Malamud–de Snoo,
[Proposition 4.2 and Theorem 7.2](https://arxiv.org/html/math/0610299v1),
give ordinary boundary-triplet and Weyl/resolvent tools under their
range, Green identity and resolvent/invertibility hypotheses.
The native pair supplying those hypotheses is Native Green stability,
Theorem 21.1. The response used here is instead explicitly constructed
by (6.4) and determined by the actual inherited-wall resolvent.
The abstract formula alone determines neither $\eta_b$ nor
$\eta_\sigma$.

Vázquez–Zographopoulos,
[the critical weighted-completion and hidden-energy setting](https://arxiv.org/html/1102.5661),
provide Euclidean critical-Hardy context.
Felli–Ferrero,
[Theorem 2.1 and Corollaries 2.2–2.3](https://arxiv.org/html/1209.4852v1),
give borderline Euclidean Hardy asymptotics for their specified
solution space. Their domains and spherical operators are not those
in (1.1)–(1.6); no native cap parameter or raw-source coefficient is
extracted from them. Here the all-angular tail estimates, natural
positive-capacity domain, both variational directions, and form-dual
residual estimates establish the native transfer explicitly.
Closed-form representation, the form-small-potential theorem and
compact min-max are intermediate tools applied with the particular
bounds proved above, as in Native Green stability, §12.

The exactly critical selection and resources remain those of Native
Green stability, §§14–19; the $\lambda_Z$ cancellation remains its
Theorem 25.2. Its §26 distinguishes the moving-time multiplier,
real-cover weak-binding and added-kinetic-law families.
None replaces the unchanged cylinder, full unit source, literal
spatial minimum cap or original free closure in (1.2).
Auxiliary balls are proof localizations and frozen rotational
functions are comparison objects; actual coefficients and states
have no imposed angular symmetry or global smallness restriction.

The convergence statements here concern normalized positive grounds
and their rank-one projections. Identifying the natural equality
operator by its source condition does not assert an all-real-parameter
operator convergence theorem. Arbitrary complex spectral response,
other spectral subspaces and resonant reference energies require
their own global transfer analysis. No extension is presumed in
order to select the ground: its source line follows from the
weighted-domain and cap limit proofs above.

## 追加锚（本行以下为增补区）

## 12. The all-real-parameter operator limit

Retain exactly the data, chart and family (1.1)–(1.5). In particular,
the domain of each capped operator is the original $D(L_A)$, its form
domain is $\mathcal F_A$, and the full killed unit-source Green field
is capped by a spatial minimum. All preparations, controls, guards,
grouping, periodic phases and the two killed height endpoints remain
fixed. No angular symmetry of the actual coefficients or states is
assumed. Constants below may depend on this one fixed smooth positive
$\rho$, smooth horizontal SPD $A$, source and admissible $b$.

Use the genuine inherited-wall pair $\mathcal A,\mathcal B$ of Native
Green stability, Theorem 21.1, with scalar product linear in its first
variable. Write $S_{\min}=S_{D,\min}$ and $S_{\max}=S_{D,\max}$ for
that theorem's operators, and set

$$
\begin{aligned}
G_\kappa&=S_{\max}|_{\{u:\mathcal A(u)=\kappa\mathcal B(u)\}},
                      &&\kappa\in\mathbb R,\\
F&=S_{\max}|_{\ker\mathcal B},&
\kappa_b&=\kappa_{\rm cap}-\log b,\\
\lambda_n&=\frac{n^2\pi^2}{\alpha},&&n=1,2,\ldots .
\end{aligned}
\tag{12.1}
$$

All these realizations retain the original outer domain. Here
$\lambda_1=\lambda_D$, and $G_\kappa=F_{-\kappa}$ in the source-line
notation of §§5–7. The boundary pairing is

$$
[u,v]=K\{\mathcal B(u)\overline{\mathcal A(v)}
                  -\mathcal A(u)\overline{\mathcal B(v)}\},\qquad
K=m_0\frac\pi2 C,\quad C=\int_Jc\phi^2da.
\tag{12.2}
$$

In particular $K$ has no factor $a_*^2$. General maximal vectors have
the angular-$L^2$/weighted-graph source expansion of that theorem,
rather than a uniform pointwise expansion of the whole maximal domain.
The source coordinates in (12.1) will be evaluated only on actual
limiting maximal vectors.

**Theorem 12.1 (the realization selected at every fixed real detuning).**
For every fixed model just specified, every fixed admissible $b$ and
every fixed real $\lambda$, let

$$
K_{\epsilon,\lambda}=L_A-g_{\mathrm c}(1+\lambda/L^2)\Gamma_\epsilon,
\qquad L=\log(b/\epsilon),\qquad D(K_{\epsilon,\lambda})=D(L_A).
\tag{12.3}
$$

The multiplier $\Gamma_\epsilon$ is bounded and real for each fixed
$\epsilon$, so this is a selfadjoint bounded multiplication
perturbation of $L_A$ on exactly $D(L_A)$.

As $\epsilon\downarrow0$, these selfadjoint operators converge in
strong resolvent sense to

$$
H_\lambda=
\begin{cases}
F,&\lambda\notin\{\lambda_n:n\ge1\},\\
G_{\kappa_b},&\lambda=\lambda_n\text{ for some }n\ge1.
\end{cases}
\tag{12.4}
$$

Explicitly, for every $f\in L^2(\mu)$ and every
$z\in\mathbb C\setminus\mathbb R$,

$$
\|(K_{\epsilon,\lambda}-z)^{-1}f-(H_\lambda-z)^{-1}f\|_2
\longrightarrow0.
\tag{12.5}
$$

This includes every $\lambda\le0$, every positive nonresonant value,
all derivative zeros of the slow wave, and every positive resonance
$\lambda_n$. In particular $\lambda_Z$ is not an exceptional operator
parameter. Inputs may be complex or sign-changing, and all angular and
spectral channels are included.

For fixed $f$, model and $b$, convergence is uniform for $\lambda$ in
any compact subset of $\mathbb R\setminus\{\lambda_n:n\ge1\}$ and
$z$ in any compact subset of $\mathbb C\setminus\mathbb R$.
There is no model-uniform assertion over $\rho,A$, or uniformity
through an unscaled resonance.

For a fixed $n\ge1$, replace the relative coupling in (12.3) by

$$
\frac{\widetilde g_\epsilon}{g_{\mathrm c}}
 =1+\frac{\lambda_n}{L^2}+\frac{\eta}{L^3}+r_L(\eta),
\qquad r_L(\eta)=o(L^{-3}).
\tag{12.6}
$$

For every fixed real $\eta$ the strong-resolvent limit is

$$
G_{\kappa_b+\eta/(2\lambda_n)}.
\tag{12.7}
$$

Convergence is uniform on compact $\eta$ sets, for each fixed $f$ and
compact nonreal $z$ set, when the remainder in (12.6) is uniform on
those $\eta$ sets. The parameter $\eta$ in (12.6) is the third-order
relative detuning; it is distinct from the global response function
$\eta(E)$ of §6.

A zero eigenvalue or any other real eigenvalue of a selected global
realization leaves (12.4)–(12.7) unchanged. The conclusions concern
nonreal resolvents and do not require a global Weyl denominator to be
nonzero at a prescribed real energy. They assert neither norm-resolvent
convergence nor a quantitative rate, all-level eigenvalue count or
classification of arbitrary varying-$\lambda$ sequences.

The proof in §§13–19 constructs one source-singular graph-core vector
for each selected line. It first solves a full-angular weighted frozen
problem and then corrects that solution to the exact native local
equation. It does not assume a bound on arbitrary actual resolvent
trace amplitudes or on an outer return map. The ground and resource
theorems remain the separate results identified in §20.

## 13. Common weighted cylinder spaces and the graph-core criterion

Put $t=\log R$ and write a physical function as $u=R^{-1}v$.
On cylinder functions let $D_i=RZ_i$, with $(Z_1,Z_2)=(U,V)$.
Their coefficients in $(t,a,\theta)$ are independent of $t$.
The polar description always means the closure inherited from smooth
Cartesian annular functions; the collapsed polar endpoints introduce
no extra boundary condition. For a positive weight $\delta$ define

$$
\begin{aligned}
Y_\delta&=L^2(e^{-2\delta t}dt\,da\,d\theta),\\
\|v\|_{X_\delta}^2
 &=\|v\|_{Y_\delta}^2+\sum_i\|D_iv\|_{Y_\delta}^2
                         +\sum_{i,j}\|D_iD_jv\|_{Y_\delta}^2.
\end{aligned}
\tag{13.1}
$$

The derivatives are distributional, and the last sum includes every
ordered pair. These are fixed Hilbert spaces, common to all cap
positions and all sufficiently small detunings. Equivalently their
norms are obtained on bounded-overlap unit logarithmic slabs, using a
slightly larger slab for local estimates and the same exponential
weight. Translation in $t$ multiplies both norms by the same scalar.

The fields $D_i$ and their commutator span all tangent directions on
each fixed Cartesian annulus. Ordinary first derivatives there are
bounded combinations of $D_i$ and ordered $D_iD_j$. Thus $X_\delta$
controls local ordinary $H^1$ and embeds compactly into local $L^2$.
This also gives the continuous angular-$L^2$ slice representatives
needed when comparing source expansions.

For the frozen expression put

$$
P_\gamma=R^3(-\Delta_H-\gamma R^{-2})R^{-1},\qquad
P_\gamma^{\rm cap}=R^3(-\Delta_H-\gamma\min(R^{-2},1))R^{-1}.
\tag{13.2}
$$

The normalized cylinder form of $P_\gamma$ is

$$
\mathfrak a_\gamma[v]=\int
 \{c|v_t+\tan a\,v_\theta|^2
       +4c|v_a+v_\theta/2|^2+(c-\gamma)|v|^2\}
                       dt\,da\,d\theta.
\tag{13.3}
$$

This follows from Native Green stability, (10.10), by integrating the
$-v$ cross term. For $P_\gamma^{\rm cap}$ replace $\gamma$ in the last
term by $\gamma\min(1,e^{2t})$. A cap at $t=a_0$ is the translate of
this expression. Its zeroth-order cylinder coefficient is bounded
uniformly in position and in $\gamma$ near $\lambda_0$.

The horizontal maximal estimate of Native Green stability, (21.4)–(21.5),
therefore gives

$$
\|v\|_{X_\delta}\le C_\delta
 \{\|P_{\gamma,a_0}^{\rm cap}v\|_{Y_\delta}
                                      +\|v\|_{Y_\delta}\},
\tag{13.4}
$$

uniformly in $a_0$ and in a fixed sufficiently small
$\gamma$ neighbourhood; the analogous uncapped estimate holds.
Indeed, move the bounded cap multiplication to the $L^2$ right side
of the smooth free local estimate on each enlarged slab. Conjugate by
$e^{\delta t}$, compare the weights on that slab and sum with bounded
overlap. The distributional extension is the local regularization
argument in that maximal estimate. This requires no derivative of the
minimum across its interface. Horizontal graph estimates and weak
equations will be used at that interface throughout.

**Lemma 13.1 (a sufficient operator graph-core test).** Let $H_j,H$ be
selfadjoint operators on one Hilbert space. Suppose $\mathcal D$ is
an operator graph core of $H$, and for each $v\in\mathcal D$ there
are $v_j\in D(H_j)$ such that $v_j\to v$ and $H_jv_j\to Hv$ in
norm. Then $H_j$ converges to $H$ in strong resolvent sense.

Proof. Fix nonreal $z$, put $f=(H-z)v$ and
$f_j=(H_j-z)v_j$, and write

$$
(H_j-z)^{-1}f=v_j+(H_j-z)^{-1}(f-f_j).
\tag{13.5}
$$

The selfadjoint bound $\|(H_j-z)^{-1}\|\le|\operatorname{Im}z|^{-1}$
gives convergence on $(H-z)\mathcal D$. This set is dense because
$\mathcal D$ is a graph core and $H-z$ maps $D(H)$ onto the Hilbert
space. Density and the same resolvent bound give convergence for every
input. No uniform lower spectral bound is required. $\square$

Let $\mathcal D_0$ be the domain of $D(F)$ vectors vanishing on some
source neighbourhood, as in Native Green stability, (21.1). Its graph
closure is $D(S_{\min})$. The direct-sum maximal decomposition gives

$$
\begin{aligned}
D(F)&=D(S_{\min})\dotplus\operatorname{span}\{p\},\\
D(G_\kappa)&=D(S_{\min})\dotplus
                              \operatorname{span}\{\kappa p+\zeta\}.
\end{aligned}
\tag{13.6}
$$

Consequently $\mathcal D_0$ plus any one genuine maximal vector of
trace $(1,0)$ or $(\kappa,1)$ is a graph core for the corresponding
realization. A different choice with the same trace differs by a
minimal vector. It suffices to approximate one such chosen vector;
no estimate for arbitrary actual capped boundary traces is part of
this criterion.

## 14. A full-angular weighted right inverse for the frozen cap

**Lemma 14.1 (uniform capped right inverse).** There exist
$0<\delta<1$ and a neighbourhood of $\lambda_0$ such that the frozen
capped expression has a bounded right inverse

$$
\mathcal G_\gamma:Y_\delta\longrightarrow X_\delta,\qquad
P_\gamma^{\rm cap}\mathcal G_\gamma=I,
\qquad \sup_\gamma\|\mathcal G_\gamma\|<\infty.
\tag{14.1}
$$

Its translate $\mathcal G_{a_0,\gamma}$ has the same bound when the
cap is at $a_0$. The capped expression has a scattering kernel;
(14.1) is a right inverse, not a bijection.

Proof. Split the frozen operator into its $\theta$ average and the
orthogonal complement. This uses rotational invariance of the frozen
expression only; neither the forcing nor the native coefficients will
be restricted to rotational functions.

On the nonzero-$\theta$ complement, Native Green stability, the proof
of Theorem 22.1 using (20.6)–(20.7), supplies $\eta_*>0$ such that
the uncapped form at $\gamma=\lambda_0$ bounds
$\eta_*\|v\|_{L^2(dt\,da\,d\theta)}^2$. The bound is uniform over
every nonzero integer Fourier mode. The capped form adds the
nonnegative term
$\gamma(1-\min(1,e^{2t}))|v|^2$. For $v=e^{\delta t}y$,
direct integration gives

$$
\operatorname{Re}\langle e^{-\delta t}P_\gamma^{\rm cap}
                          e^{\delta t}y,y\rangle
 =\mathfrak a_\gamma^{\rm cap}[y]
                                  -\delta^2\int c|y|^2.
\tag{14.2}
$$

The terms linear in $\delta$ are skew, since
$\partial_t+\tan a\,\partial_\theta$ is skew for cylinder measure.
Take $\delta^2<\eta_*/4$ and shrink the $\gamma$ neighbourhood.
The right side retains a fixed positive unweighted mass bound.
It controls the free cylinder energy too: that energy equals the cap
form plus $\gamma\int\min(1,e^{2t})|y|^2$.
The endpoint inequality in Native Green stability, (12.10), applied
after the fibre phase $e^{-ina/2}$, bounds unweighted angular mass by
the free energy with constants independent of $n$. The conjugated
form is continuous on the free-energy completion; its extra
first-order terms are bounded by that energy and the $c$-weighted
mass. Lax–Milgram gives a unique weighted energy solution for every
nonzero-$\theta$ forcing in $Y_\delta$, with uniform bound.
Estimate (13.4) upgrades it to $X_\delta$. The uniform coercivity
allows summation of all modes. This is a whole-cylinder inverse on
that complement, with no arbitrary-trace Poisson assertion.

For the rotational sector use precisely the trace spaces of Native
Green stability, Theorem 22.1:

$$
\begin{gathered}
\mathsf H=L^2(J,c\,da),\qquad
\mathsf V=\{b:\int_Jc(|b'|^2+|b|^2)da<\infty\},\\
T_0\text{ has form }\int_J(4c|b'|^2+c|b|^2)da
                         \text{ on }\mathsf H,\qquad
\mathsf X=D(T_0^{1/4}).
\end{gathered}
\tag{14.3}
$$

Here $\mathsf X$ is a boundary trace space, distinct from the full
cylinder space $X_\delta$. Its dual below is the anti-dual for the
first-variable-linear pairing. Spectral minimization of free
half-cylinder energy gives this trace space and a bounded lifting,
which can be cut off to a fixed boundary collar.

Write $\Lambda(\sigma)=\gamma$ for the analytic signed dispersion
parameter near zero. The operator $\mathsf A_\gamma$ on $\mathsf H$
has form

$$
\int_J\{4c|b'|^2+(c-\gamma)|b|^2\}da.
\tag{14.4}
$$

It has simple eigenpair $(-\sigma,\phi_\sigma)$ and a uniformly
positive complementary spectrum. Let $P_\sigma$ be its
$\mathsf H$-orthogonal projection onto $\phi_\sigma$,
$Q_\sigma=I-P_\sigma$, and
$D_\sigma=\sqrt{\mathsf A_\gamma|_{Q_\sigma}}$, extended by zero
on $P_\sigma$. The normalized interior conormal map
$N_\gamma:\mathsf X\to\mathsf X^*$ and

$$
\mathsf M_\sigma=N_\gamma+D_\sigma:
                              \mathsf X\longrightarrow\mathsf X^*
\tag{14.5}
$$

are the analytic maps constructed there. The sum is coercive and
boundedly onto, with uniformly bounded inverse near zero. The
projections are bounded on the energy and trace spaces. Choose
$\delta$ also smaller than the square root of the complementary
gap and small enough for the interior coercivity used next.

Let $\mathfrak f\in Y_\delta$ be rotational forcing. On $t<0$ solve
the forced interior equation with zero boundary value. The interior
form is

$$
\mathfrak B_\gamma[W]=\int_{t<0}\int_J
 \{c|W_t|^2+4c|W_a|^2+(c-\gamma e^{2t})|W|^2\}da\,dt.
\tag{14.6}
$$

Its free-energy coercivity is proved in Native Green stability,
(22.8): use $W=\phi v$, the positive
$\lambda_0(1-e^{2t})\phi^2|v|^2$ term on $t<-1$, the fundamental
theorem on the last unit collar, and the angular endpoint inequality.
Conjugation subtracts only $\delta^2\|W\|_{\mathsf H}^2$ from the
real part, so coercivity persists for small $\delta$. A bounded
trace lifting supported in $-1<t<0$ gives the same weighted estimate
for arbitrary trace in $\mathsf X$. Denote the zero-boundary forced
solution by $d(\mathfrak f)$ and its normalized increasing-$t$
conormal at zero by $j(\mathfrak f)\in\mathsf X^*$. The variational
Green formula against such liftings gives

$$
\|d(\mathfrak f)\|_{\rm weighted\ energy}
       +\|j(\mathfrak f)\|_{\mathsf X^*}
                                  \le C\|\mathfrak f\|_{Y_\delta}.
\tag{14.7}
$$

These conormals are functionals, with no classical normal trace
assigned at a characteristic polar endpoint.

The endpoint inequality $\mathsf V\hookrightarrow L^2(J,da)$ means
that an $L^2(da)$ forcing acts in $\mathsf V^*$. Define its slow
projection and complementary functional by

$$
\begin{aligned}
C_\sigma&=\int_Jc\phi_\sigma^2da,\\
f_s(t)&=\frac{\int_J\mathfrak f(t,a)\phi_\sigma(a)da}{C_\sigma},\\
\mathfrak f_Q&=\mathfrak f-c\phi_\sigma f_s.
\end{aligned}
\tag{14.8}
$$

Thus $\mathfrak f_Q$ annihilates $\phi_\sigma$ as a functional.
The scalar $f_s$ has the corresponding weighted $L^2$ bound. There
is no assertion that $c^{-1}\mathfrak f$ belongs to $\mathsf H$.
On $t>0$, solve the forced complementary equation with forcing
$\mathfrak f_Q$, zero boundary value and the weighted condition.
The positive complementary gap, after subtraction of $\delta^2$
mass, gives a unique solution $y(\mathfrak f)$. Its weighted energy
and normalized increasing-$t$ conormal
$k(\mathfrak f)=y_t(0)\in\mathsf X^*$ are bounded by
$C\|\mathfrak f\|_{Y_\delta}$. To obtain the conormal estimate,
integrate the weak Green formula against a bounded trace lifting in
a fixed exterior collar; its form and forcing terms have exactly
these bounds. This is again a form/anti-dual construction.

Choose the slow derivative datum at $t=0$ to be zero, and solve

$$
\mathsf M_\sigma f=k(\mathfrak f)-j(\mathfrak f),\qquad
C_0=\langle f,\phi_\sigma\rangle_{\mathsf H}/C_\sigma.
\tag{14.9}
$$

The exterior solution is

$$
\begin{aligned}
W_+(t)={}&\phi_\sigma
 \left\{C_0c_\sigma(t)-\int_0^t s_\sigma(t-s)f_s(s)ds\right\}\\
 &+e^{-tD_\sigma}Q_\sigma f+y(\mathfrak f)(t),
\end{aligned}
\tag{14.10}
$$

where $c_\sigma,s_\sigma$ are the entire functions in (1.8).
The interior solution is the harmonic extension of $f$ plus
$d(\mathfrak f)$. Their values at zero agree. Their normalized
derivatives agree because (14.9) says precisely

$$
N_\gamma f+j(\mathfrak f)=-D_\sigma f+k(\mathfrak f).
\tag{14.11}
$$

The physical conormal on each side subtracts the same identity term
from the normalized one, as in Native Green stability, (22.8)–(22.9).
It cancels in matching. The glued weak solution therefore creates no
interface delta distribution.

After conjugation the scalar retarded kernel in (14.10) is
$s_\sigma(r)e^{-\delta r}$ for $r\ge0$. It and its first derivative
have uniformly bounded $L^1$ norms when
$|\operatorname{Im}\sqrt\sigma|<\delta/2$. Young's inequality
gives the weighted energy bound for the forced slow part. The
homogeneous cosine belongs to the weighted half-line energy too.
The complementary semigroup, its forced solution and the interior
extension have the bounds just proved. Consequently the glued
solution lies in $Y_\delta$ with uniform energy bound, and (13.4)
upgrades it to $X_\delta$. Together with the nonzero-$\theta$
solution this defines (14.1) on every full-angular forcing.

For zero forcing a free slow derivative $D_0$ instead gives boundary
value $\mathsf M_\sigma^{-1}(\phi_\sigma D_0)$, and hence $D_0$
times the source-regular scattering solution of Native Green
stability, Theorem 22.1. It belongs to the weighted space for the
chosen small parameter neighbourhood. The choice $D_0=0$ specifies
the right inverse while retaining this kernel. Finally translation
$t\mapsto t-a_0$ multiplies the $X_\delta$ and $Y_\delta$ norms by
the same scalar. The translated right inverse therefore has the same
uniform bound. $\square$

## 15. The uncapped inverse and the local native perturbation

For the same sufficiently small positive $\delta$, the uncapped
critical expression is a bijection

$$
P_{\lambda_0}:X_\delta\longrightarrow Y_\delta,
\qquad \mathcal G_0=P_{\lambda_0}^{-1}.
\tag{15.1}
$$

Indeed, the nonzero-$\theta$ coercivity in §14 applies without the
cap addition. In the rotational sector the complementary problem
is the positive full-cylinder form problem. For its slow part the
equation is $-x''=f_s$, with unique weighted solution

$$
x(t)=-\int_{-\infty}^t(t-s)f_s(s)ds.
\tag{15.2}
$$

The conjugated convolution kernel is $re^{-\delta r}$, $r\ge0$,
whose $L^1$ norm is $\delta^{-2}$. This proves existence and its
weighted bound; (13.4) gives the $X_\delta$ bound. Constants and
linear homogeneous slow solutions fail the positive-weight
condition at $-\infty$. Every complementary homogeneous exponential
fails it at one end. Together with nonzero-$\theta$ uniqueness this
proves injectivity. This explicit construction agrees with the
weighted inversion of Native Green stability, Theorem 21.1; no
Laurent functional with reversed scalar-product orientation is used.

Choose an auxiliary radius $r_0>0$ inside the injective source chart,
with $2r_0$ still in that chart. It may be smaller than $b$, which
remains fixed in the physical family. On $R<2r_0$ write

$$
\begin{aligned}
R^3K_{\epsilon,\lambda}R^{-1}
 &=P_{\gamma_\epsilon,\log\epsilon}^{\rm cap}+Q_\epsilon,\\
\gamma_\epsilon&=\frac{g_{\epsilon,\lambda}}{2\pi m_0}
                         =\lambda_0(1+\lambda/L^2).
\end{aligned}
\tag{15.3}
$$

The exact chart estimates of Native Green stability, (11.1)–(11.3),
give $C(q)-I=O(R)$, $m(q)/m_0-1=O(R)$, bounded horizontal first
coefficient derivatives and
$|\Gamma-c_GR^{-2}|\le C_1/R$. Thus the principal and first-order
cylinder coefficients in $Q_\epsilon$ are $O(R)$.
The minimum is $1$-Lipschitz in its first argument, so

$$
|\Gamma_\epsilon-c_G\min(R^{-2},\epsilon^{-2})|
                                      \le C_1/R.
\tag{15.4}
$$

Multiplication by $R^2$ makes the corresponding cylinder potential
error $O(R)$ too. No derivative across the cap is needed.

Extend these perturbation coefficients by a fixed smooth cutoff
equal to one for $R<r_0$ and zero for $R>2r_0$. This defines an
auxiliary operator $Q_\epsilon$ on the full cylinder with

$$
\|Q_\epsilon v\|_{Y_\delta}\le C_2r_0\|v\|_{X_\delta}.
\tag{15.5}
$$

The extension agrees with the actual expression on $R<r_0$; no
physical boundary or operator is changed. On each fixed punctured
annulus it tends to the corresponding critical $Q_0$, and the
coefficients remain uniformly $O(R)$. Dominated convergence gives
$Q_\epsilon v\to Q_0v$ in $Y_\delta$ for each fixed
$v\in X_\delta$. Outside the eventual cap the coefficients have
their smooth annular convergence.

Fix the inverse norms from §§14–15 first and then shrink $r_0$ so
that

$$
C_2r_0\max\{\sup_\gamma\|\mathcal G_\gamma\|,
                                      \|\mathcal G_0\|\}<\tfrac12.
\tag{15.6}
$$

This is local analysis for each arbitrary fixed smooth model, not
a small-global-perturbation condition. The weight can also be chosen
below the positive source-corrector exponent in Native Green
stability, Theorem 21.1. All these choices are independent of
$\epsilon$ and of parameters in the compact sets used below.

## 16. Normalizing the exact frozen column at all detunings

Let $\sigma_\epsilon$ be the small real solution of
$\Lambda(\sigma_\epsilon)=\gamma_\epsilon$. Since
$\Lambda'(0)=C/M$, the exact analytic dispersion gives

$$
\sigma_\epsilon=\frac{\alpha\lambda}{L^2}+O(L^{-4}),
\tag{16.1}
$$

uniformly on compact real $\lambda$ sets. Set
$\ell=-\log\epsilon=L-\log b$. In the chart, for a point $x$ with
$R(x)=e^t$, define the translated frozen cylinder solution

$$
W_\epsilon(t,a,\theta)
 =R(x)\epsilon^{-1}
                    Z_{\sigma_\epsilon}(\delta_{1/\epsilon}x).
\tag{16.2}
$$

It solves $P_{\gamma_\epsilon,\log\epsilon}^{\rm cap}W_\epsilon=0$.
The exact scattering representation (1.8), referred to $t=\log R$,
has slow column

$$
\begin{aligned}
U_\epsilon&=s_{\sigma_\epsilon}(\ell)
                          +a(\sigma_\epsilon)c_{\sigma_\epsilon}(\ell),\\
V_\epsilon&=c_{\sigma_\epsilon}(\ell)
             -\sigma_\epsilon a(\sigma_\epsilon)
                                      s_{\sigma_\epsilon}(\ell),\\
W_{\epsilon,\rm slow}(t)
 &=\phi_{\sigma_\epsilon}
       \{U_\epsilon c_{\sigma_\epsilon}(t)
                              +V_\epsilon s_{\sigma_\epsilon}(t)\}.
\end{aligned}
\tag{16.3}
$$

These are coordinates of a frozen solution, not uncapped maximal
traces of a finite-$\epsilon$ capped vector.

For $\lambda>0$ write $\mu=\sqrt{\alpha\lambda}$, and for
$\lambda<0$ write $\nu=\sqrt{-\alpha\lambda}$. Then

$$
\frac{U_\epsilon}{L}\longrightarrow
\begin{cases}
\sin\mu/\mu,&\lambda>0,\\
1,&\lambda=0,\\
\sinh\nu/\nu,&\lambda<0.
\end{cases}
\tag{16.4}
$$

At zero the exact value is
$U_\epsilon=L-\log b+\kappa_{\rm cap}$. For every fixed
$\lambda\notin\{\lambda_n:n\ge1\}$ the appropriate limit in
(16.4) is nonzero, while $V_\epsilon$ is bounded. Normalize by

$$
d_\epsilon=U_\epsilon^{-1},\qquad
w_\epsilon=d_\epsilon W_\epsilon.
\tag{16.5}
$$

On every fixed annulus $w_\epsilon\to w_0=\phi$. The normalization
does not divide by $V_\epsilon$, so zeros of $\cos\mu$ cause no
exception.

At $\lambda=\lambda_n$, put $q_\epsilon=\sqrt{\sigma_\epsilon}>0$.
Equation (16.1) and analyticity of $a$ give

$$
\begin{gathered}
q_\epsilon=n\pi/L+O(L^{-3}),\qquad
a(\sigma_\epsilon)=\kappa_{\rm cap}+O(L^{-2}),\\
U_\epsilon\longrightarrow(-1)^n\kappa_b,\qquad
V_\epsilon\longrightarrow(-1)^n.
\end{gathered}
\tag{16.6}
$$

Use $d_\epsilon=V_\epsilon^{-1}$ instead. This gives

$$
w_\epsilon\longrightarrow w_0=\phi(\kappa_b+t)
\tag{16.7}
$$

on fixed annuli, including when $\kappa_b=0$. The complementary
scattering remainder vanishes there by its exterior exponential
decay. Both choices of $d_\epsilon$ stay bounded.

The needed forcing bound is stronger than fixed-annulus convergence
but does not concern an arbitrary actual trace. On every unit slab
with $t<T=\log(2r_0)$, the $L^2$ slab norms of $w_\epsilon$, its
first $D_i$ derivatives and all ordered $D_iD_j$ derivatives are at
most

$$
C_3(1+|t|),
\tag{16.8}
$$

uniformly as $\epsilon\downarrow0$ in each of the stated parameter
ranges. To see this outside the cap, keep the exact sine or
hyperbolic column. In the nonresonant case $d_\epsilon=O(L^{-1})$
and $|s_{\sigma_\epsilon}(t-\log\epsilon)|\le C_4L$ for
$\log\epsilon\le t\le T$. In the resonant case use the bounded
$U_\epsilon/V_\epsilon$ representation and
$|s_{\sigma_\epsilon}(t)|\le C_4|t|$ for $|t|\le L+O(1)$.
The complementary part is bounded at the first core collars and
decays exponentially farther out. Inside the core source smoothness
of $Z_\sigma$ gives the sharper bound
$C_4|d_\epsilon|e^{t-\log\epsilon}$ for the function. The frozen
cap equation and (13.4) give the local horizontal graph bounds,
including the interface collars. No Cartesian smoothness across the
literal cap interface is asserted.

Together with the $O(e^t)$ coefficients of $Q_\epsilon$, (16.8)
proves

$$
Q_\epsilon w_\epsilon\longrightarrow Q_0w_0
                                      \quad\hbox{in }Y_\delta.
\tag{16.9}
$$

For an explicit dominating series, on a slab indexed by
$j\to-\infty$ the unweighted forcing norm is at most
$C_5e^j(1+|j|)$. The squared weighted majorant is
$C_6e^{2(1-\delta)j}(1+|j|)^2$, which is summable because
$\delta<1$. The source-core collars obey the same bound as they
move to $-\infty$. Fixed annuli give convergence of the forcing
there, so dominated convergence proves (16.9).

## 17. Exact native correction, physical tails and limiting source traces

Let $\mathcal G_\epsilon$ be the translated right inverse of §14
at $\gamma_\epsilon$ and cap position $\log\epsilon$. In the common
space $X_\delta$ solve

$$
\begin{aligned}
r_\epsilon&=-\mathcal G_\epsilon
                                  Q_\epsilon(w_\epsilon+r_\epsilon),\\
r_\epsilon&=-(I+\mathcal G_\epsilon Q_\epsilon)^{-1}
                                  \mathcal G_\epsilon Q_\epsilon w_\epsilon.
\end{aligned}
\tag{17.1}
$$

By (15.6) this is a strict contraction. Equations (14.1) and (16.9)
give $\|r_\epsilon\|_{X_\delta}\le C_7$. Applying the actual
right-inverse identity, not an inverse identity for the capped
kernel, yields

$$
(P_{\gamma_\epsilon,\log\epsilon}^{\rm cap}+Q_\epsilon)
                               (w_\epsilon+r_\epsilon)=0.
\tag{17.2}
$$

Therefore
$u_\epsilon=R^{-1}(w_\epsilon+r_\epsilon)$ solves the exact original
native capped zero-energy equation on $R<r_0$. Actual coefficients
may break every angular symmetry; their effects are in
$Q_\epsilon$ and the full-angular correction $r_\epsilon$.

Take any weakly convergent $X_\delta$ subsequence of $r_\epsilon$.
Pass in (17.2) against compactly supported punctured-cylinder tests.
The local coefficient convergence and (16.9) give for its weak limit
$r$

$$
P_{\lambda_0}r=-Q_0(w_0+r),\qquad
r=-(I+\mathcal G_0Q_0)^{-1}\mathcal G_0Q_0w_0.
\tag{17.3}
$$

Weak closedness places $r$ in $X_\delta$, and (15.1), (15.6) make
(17.3) unique. Every subsequence has this same limit. Local compactness
of $X_\delta$ gives strong local $L^2$ convergence. On each fixed
punctured annulus the cap is eventually absent, the coefficients
converge smoothly, and the functions solve homogeneous native
equations. Iterated local subelliptic estimates give convergence
with every fixed smooth derivative on smaller annuli. This controls
the cutoff commutators below. No strong or norm convergence of the
translated right inverses is assumed in this argument.

There is also strong physical $L^2(\mu)$ convergence on every
smaller whole source ball. The polar Jacobian and comparable actual
density give

$$
\|R^{-1}v\|_{L^2(\mu;\,t<S)}^2
                       \asymp\int_{t<S}e^{2t}|v|^2dt\,da\,d\theta.
\tag{17.4}
$$

The bounded correction norm implies

$$
\int_{t<S}e^{2t}|r_\epsilon|^2dt\,da\,d\theta
                            \le C_8e^{2(1+\delta)S}.
\tag{17.5}
$$

For the frozen part (16.8) gives the uniform tail bound
$C_8\int_{-\infty}^S e^{2t}(1+|t|)^2dt$. Both tails tend to zero
as $S\to-\infty$. Strong convergence on the remaining compact
annulus proves the whole-ball assertion, with the original density.

The limit $u_0=R^{-1}(w_0+r)$ is $L^2$ and solves the actual
uncapped critical equation on the punctured ball. After a compact
cutoff its critical image is $L^2$, so it is genuinely in the native
maximal domain. Its source coordinates are exactly

$$
(\mathcal A,\mathcal B)=
\begin{cases}
(1,0),&\lambda\notin\{\lambda_n:n\ge1\},\\
(\kappa_b,1),&\lambda=\lambda_n.
\end{cases}
\tag{17.6}
$$

Here is the trace justification in the required graph topology.
Choose $\delta$ below the source-corrector exponent of Native Green
stability, Theorem 21.1. The corrected $p,\zeta$ differ in cylinder
coordinates from $\phi,t\phi$ by elements of $X_\delta$ locally
near $-\infty$; the graph-minimal remainder is in $X_1$ and hence
in $X_\delta$ there. Subtract that theorem's maximal decomposition
of a cutoff of $u_0$ from $w_0+r$. The difference between the
proposed and genuine trace coefficients would give
$\phi(A+Bt)$ in $X_\delta$ near $-\infty$. Positive exponential
weight makes this impossible unless $A=B=0$. This proves (17.6).
The ordered-derivative control in (13.1) also supplies its continuous
angular-$L^2$ slice interpretation. At no step are uncapped maximal
traces evaluated on $u_\epsilon$ or another finite-cap vector.

## 18. Original-domain graph approximants and all nonreal resolvents

For each fixed $\epsilon$ the constructed local $u_\epsilon$ has
finite original free horizontal energy through the source. For the
correction and $a_0=\log\epsilon$, positivity of $\delta$ gives

$$
\int_{t<a_0}\left(|r_\epsilon|^2+\sum_i|D_ir_\epsilon|^2\right)
                                    dt\,da\,d\theta
                \le e^{2\delta a_0}\|r_\epsilon\|_{X_\delta}^2<\infty.
\tag{18.1}
$$

In the physical derivative of $R^{-1}r_\epsilon$, the cylinder
derivative differs from $D_ir_\epsilon$ by a bounded multiple of
$r_\epsilon$. The polar factors cancel in the free kinetic integral,
as in Native Green stability, (10.10). Thus (18.1) is finite free
energy, and (17.4) gives finite physical norm. The frozen part is
source-regular and has the same property. On the remaining compact
collars the horizontal graph estimate supplies the required energy.

The free horizontal point capacity is zero: cutoffs on source scale
$s$ have horizontal energy $O(s^2)$ in homogeneous volume exponent
four. Test the finite-energy weak equation with these cutoffs and
let $s\downarrow0$. Since $\Gamma_\epsilon$ is bounded for fixed
$\epsilon$, its product with $u_\epsilon$ is locally $L^2$; the
puncture contributes no distribution. The cap is constant on a
source neighbourhood. Local hypoellipticity then makes
$u_\epsilon$ smooth there. Through a literal cap interface the
equation remains weak with horizontal maximal regularity; no
smoothness across that interface is required.

Take a fixed smooth $\chi$ compactly supported in $R<r_0$ and equal
to one on a smaller ball. Extend
$g_\epsilon=\chi u_\epsilon$ by zero to the original cylinder.
It belongs to the original $\mathcal F_A$, and its weak image is

$$
L_Ag_\epsilon=g_{\epsilon,\lambda}\Gamma_\epsilon g_\epsilon
                                      +[L_A,\chi]u_\epsilon\in L^2(\mu).
\tag{18.2}
$$

The identity extends from compact smooth form tests to
$\mathcal F_A$ by form-core density, since its left form and right
$L^2$ functional are continuous there. The closed-form representation
criterion therefore puts $g_\epsilon$ in actual $D(L_A)$. A formal
differential image alone would not suffice for this domain assertion.
For the capped operator its image is exactly the commutator.

Put $g_0=\chi u_0$. It is a genuine inherited-wall maximal vector
with the trace in (17.6), and
$S_{\max}g_0=[L_A,\chi]u_0$. These commutators are first-order and
supported on one fixed smooth source-avoiding annulus. Whole-ball
norm convergence and smooth annular convergence from §17 give

$$
g_\epsilon\longrightarrow g_0,\qquad
K_{\epsilon,\lambda}g_\epsilon
                          \longrightarrow S_{\max}g_0
                                  \quad\hbox{in }L^2(\mu).
\tag{18.3}
$$

The support of $g_\epsilon,g_0$ lies inside the original source
chart; they respect the actual outer killing and phases. They are
graph-core vectors, with no assertion that the local zero-energy
solution is a global eigenfunction.

For $v\in\mathcal D_0$, localization away from the source places
$v$ in the original free operator domain $D(L_A)$. The full Green
field is bounded on its support and eventually equals its cap
there. Hence

$$
K_{\epsilon,\lambda}v
      =Fv-\frac{g_{\mathrm c}\lambda}{L^2}\Gamma v
                                      \longrightarrow Fv\quad\hbox{in }L^2.
\tag{18.4}
$$

This uses the inherited-wall localization of Native Green stability,
Theorem 21.1; it does not replace that domain by the absolute
adjoint of a punctured compact core. By (13.6),
$\mathcal D_0+\operatorname{span}\{g_0\}$ is an operator graph core
for the selected $H_\lambda$. Equations (18.3)–(18.4) supply all its
graph approximants in $D(L_A)$. Lemma 13.1 proves (12.5), on the
original full Hilbert space and for every nonreal spectral parameter.

Only local zero-energy equations were separated in the frozen
construction. A nonzero-energy rotational native equation need not
stay in its slow angular eigenspace: the nonconstant $c(a)$ in
Native Green stability, Proposition 22.4, precludes that reduction.
Here no $Ee^{2t}$ term of an actual finite-energy equation is dropped.
The selfadjoint graph-core argument, rather than scalar separation
of a resolvent equation, supplies all complex resolvents and inputs.

## 19. All positive resonances, third-order selection and uniformity

The only positive zeros of the limiting quotient in (16.4) are
$\sqrt{\alpha\lambda}=n\pi$, $n\ge1$. The hyperbolic quotient
and its continuous value at zero have no zero. At each positive
zero, $V_\epsilon$ has the nonzero limit in (16.6). The inverse on
all nonzero-$\theta$ modes and the rotational complementary inverse
in §14 show that no angular branch was omitted. This exhausts the
fixed-real-parameter cases, without dividing by a slow derivative
which can vanish at half waves.

For (12.6), analytic inversion of the same dispersion gives

$$
q_\epsilon L=n\pi+
                \frac{\alpha\eta}{2n\pi L}+o(L^{-1}).
\tag{19.1}
$$

In particular

$$
\frac{s_{\sigma_\epsilon}(L-\log b)}
     {c_{\sigma_\epsilon}(L-\log b)}
       \longrightarrow\frac{\eta}{2\lambda_n}-\log b,
\qquad
\frac{U_\epsilon}{V_\epsilon}
       \longrightarrow\kappa_b+\frac{\eta}{2\lambda_n}.
\tag{19.2}
$$

Normalize by $V_\epsilon$ as at (16.7). It stays bounded away from
zero on compact $\eta$ sets, and the limiting frozen vector becomes
$\phi(\kappa_b+\eta/(2\lambda_n)+t)$. The slab majorant, forcing
convergence, contraction, physical tails and original-domain graph
approximants of §§16–18 apply with this vector. They prove (12.7).
This derives the $L^{-3}$ relative-coupling precision and the
selected line, instead of choosing an extension in advance.

The sign and the fixed reference radius can be checked in two ways.
Writing the genuine source expansion using $\log(R/b)$ changes its
constant to

$$
\mathcal A_b=\mathcal A+\mathcal B\log b.
\tag{19.3}
$$

Alternatively put $b'=be^d$ and $L'=L+d$. The exactly resonant
coupling written in the old convention satisfies

$$
\frac{\lambda_n}{(L+d)^2}
 =\frac{\lambda_n}{L^2}-\frac{2\lambda_nd}{L^3}+O(L^{-4}).
\tag{19.4}
$$

It is the window coefficient $\eta=-2\lambda_nd$, so (19.2)
changes $\kappa_b$ by $-d$, precisely to
$\kappa_{\rm cap}-\log b'$. These are compatible descriptions of
the actual family. At $n=1$, Corollary 10.1 has
$\eta_\sigma=-\kappa_b-\sigma/(2\lambda_D)$, with its
$\sigma$ equal to the third-order coefficient in (12.6).
Thus its positive-ground source line agrees with (12.7).

For completeness the compact-parameter assertions require the
following uniform argument. On a compact nonresonant $\lambda$
set, (16.4) gives $|U_\epsilon|\ge c_1L$ and bounded
$V_\epsilon$ uniformly. Every sequence of parameters in that set
has the same limiting $w_0=\phi$. The majorant and the contraction
constants are uniform. The weak-subsequence uniqueness and compactness
argument of §17 then proves uniform graph approximation to the
same $g_0$. Formula (18.4) is uniform too. Apply the density estimate
(13.5) on a finite approximation of each fixed input; the resolvent
bound is parameter independent on a compact nonreal $z$ set. First
this gives uniform convergence at one nonreal $z$, and the resolvent
identity and compactness give it on the whole compact set.

For the refined window assume the remainder in (12.6) is uniform on
the compact $\eta$ set. Along any $\eta_\epsilon\to\eta$, the
same construction converges to the vector for
$\kappa=\kappa_b+\eta/(2\lambda_n)$. At the limit the correction
(17.3) is linear in $w_0=\phi(\kappa+t)$, so the graph-core vector
$g_0(\kappa)$ and its maximal image depend affinely on $\kappa$.
Using (13.6) and Lemma 13.1 once more, now for
$G_{\kappa_j}$ with $\kappa_j\to\kappa$, proves strong-resolvent
continuity in $\kappa$. Compactness of the $\eta$ set gives the
uniform convergence to the corresponding $G_{\kappa(\eta)}$ for
every fixed input. The same resolvent identity handles compact
nonreal $z$ sets. No operator-norm convergence is inferred from
this fixed-input argument.

Uniformity through a resonance in the unscaled $\lambda$ variable
would be false. For any fixed nonzero $\eta$, take
$\lambda(\epsilon)=\lambda_n+\eta/L$. These are nonresonant for
small $\epsilon$, so their pointwise limiting operator from (12.4)
would be $F$, whereas the actual sequence has the limit
$G_{\kappa_b+\eta/(2\lambda_n)}$ just proved. The onto source pair
distinguishes every finite line from $\mathcal B=0$ and distinguishes
different finite $\kappa$ lines. Their resolvents therefore differ
on some fixed input. This establishes the parameter-limit distinction;
it is not a classification of every varying-$\lambda$ sequence.
$\square$

## 20. Source covariance, ground-state compatibility and proof scope

The coefficient in (16.1) is fixed by the unit source and angular
dispersion, not by a radial analogue:

$$
\gamma=\frac g{2\pi m_0},\qquad
\Lambda'(0)=\frac CM,\qquad
\alpha=\frac{\lambda_0M}{C}.
\tag{20.1}
$$

The polar Jacobian $1/4$ and actual angle period $2\pi$ give the
source flux coefficient $K=m_0(\pi/2)C$ in (12.2). No normalized
ground amplitude enters that source-line ratio, and the clock with
covariance $2A\,dt$ supplies no additional factor $1/2$.
Under $\rho\mapsto c_1\rho$, the Green field and its cap divide by
$c_1$ while $m_0,g_{\mathrm c},K$ multiply by $c_1$. The product
$g\Gamma_\epsilon$ and the differential operator are unchanged
under the natural unitary identification of the two $L^2$ spaces.
The source coefficients scale together, preserving
$\mathcal A/\mathcal B$ and the selected $\kappa$.

The full auxiliary cylinder, its right inverse, the small radius
$r_0$, the extension of $Q_\epsilon$ and the final cutoff are proof
devices. They yield one compactly supported actual graph-core vector
and change no physical source, wall, phase, kinetic form, quotient or
domain. Their choices do not affect the resulting realization: the
limiting correction lies in positive-weight $X_\delta$ and adds no
constant or logarithmic source term; vectors with the same genuine
trace differ by a graph-minimal vector.

Theorem 12.1 adds an operator statement across all spectral channels.
Its ground-state consequences must be read together with the already
established ground theorems at their exact scopes. For
$\lambda<\lambda_D$, Theorem 2.2 gives retention of $f_*$ and the
actual divergent separate-resource laws, including their compact
subthreshold uniformity. The $\lambda_Z$ cancellation and finite
parts are Native Green stability, Theorem 25.2. At $\lambda_D$,
Theorems 7.1–9.1 give the finite $G_{\kappa_b}$ ground, its sharp
energy correction, profile and $L^3$ separate resources; Corollary
10.1 gives the stated first-threshold ground window. For every fixed
$\lambda>\lambda_D$, including $\lambda_n$ with $n\ge2$, Native
Green stability, Theorem 24.1, gives actual ground collapse, its
concentration profile and sharp separate-resource laws, uniformly on
compact subsets of that open range for a fixed model and $b$.
Those laws are not inferred from strong-resolvent convergence and
are not new energy or resource conclusions of Theorem 12.1.

Deep ground collapse is compatible with either limit in (12.4).
The graph-core proof uses only
$\|(K_{\epsilon,\lambda}-z)^{-1}\|\le|\operatorname{Im}z|^{-1}$,
with no uniform lower spectral bound. If the ground energy tends
to $-\infty$, the norm of its contribution to the resolvent applied
to $f$ is at most
$\|f\|/|E_{\epsilon,\lambda}-z|$, which tends to zero. The
collapsing normalized states from Theorem 24.1 concentrate at the
source and converge weakly to zero; their moving negative energies
do not obstruct the finite nonreal resolvent limit. The operator
theorem does not retain those normalized grounds or bound their
kinetic, raw-attraction or capped-attraction resources. A finite
total energy at equality likewise does not remove the separate
$L^3$ divergences in §9.

The source-specific analytic ingredients used here are the genuine
maximal pair and horizontal graph estimate of Native Green stability,
Theorem 21.1, and its Theorem 22.1's analytic dispersion, scattering
column, trace-space maps, interior coercivity and all-mode gap.
The additional inferences are the forced full-angular right inverse,
the bounded local native correction, the physical tail and trace
identification, and the original-domain graph approximants. All
inverse bounds used for these inferences follow from the displayed
coercivity, convolution and graph estimates. No stronger
cap-to-fixed-radius operator-norm matching estimate, arbitrary actual
trace amplitude bound or outer-return estimate is a premise.

For bounded primary correspondence, Derkach–Hassi–Malamud–de Snoo,
[Proposition 4.2 and Theorem 7.2](https://arxiv.org/html/math/0610299v1),
provide boundary-triplet/Weyl and resolvent tools under their stated
range, Green identity and invertibility hypotheses. They do not
select this spatial-cap parameter, and their formula is not needed
in the graph-core proof. Dereziński–Richard,
[Theorem 5.5 and the selfadjoint half-line families](https://arxiv.org/html/1604.03340v2),
treat scalar inverse-square endpoints with specified boundary
parameters. Neither their Bessel constants nor a chosen half-line
extension is substituted for the full-angular native construction.
Lax–Milgram, weighted energy conjugation, Young's convolution
inequality, local compactness and Lemma 13.1 are the standard
analytical tools instantiated in the proof above.

The neighbouring repository families retain the distinctions in
Native Green stability, §26: the moving-time multipliers and changed
carrier of Critical cutoff, Definition 31.1 and Theorems 32.2–33.1;
the real-cover threshold source and different infinity in Weak
binding, Definition 70.1 and Proposition 70.2; and the bounded-cap
and added-kinetic-law settings of Continuation III, Specification
82.7 and Theorem 87.4. None is a supplier of (12.4) for the unchanged
periodic killed unit-source spatial minimum. This is a bounded
correspondence, with no exhaustive-search or priority assertion.

The all-fixed-real-parameter operator classification and its stated
precision windows do not assert norm-resolvent rates, all-level
counts, model-uniformity, new resource finite parts or the outcome
of the broader why-three programme. Finite normalized-law task
information, binary-task Bayes risk and zero-one loss provide no
native Green law or acquisition map here. Homogeneous volume
exponent four, growth $(2,3)$, current-ray dimension three, direct
rank two and physical Euclidean dimension retain their distinct
meanings.

## 追加锚（本行以下为增补区）

## 21. Scope reconciliation for the combined source

The final paragraph of §11 describes the scope of §§1–11 alone:
their normalized-ground and rank-one conclusions do not themselves
establish convergence on other spectral subspaces. Its description of
the all-real operator limit and resonant transfer as still requiring
analysis is superseded and void as a statement about the complete
source. The operator supplier is Theorem 12.1, proved in §§13–19;
the ground suppliers remain those identified in §20.

For the unchanged family (1.1)–(1.5), the replacement is precisely
(12.4)–(12.5), for each fixed admissible model, fixed $b$, every fixed
real $\lambda$, every fixed $L^2(\mu)$ input and every nonreal $z$.
All angular and spectral channels and all $\lambda_n$ are included.
The third-order resonant window is (12.6)–(12.7), with a remainder
uniform on compact window-parameter sets when compact uniformity is
claimed. Unscaled compact-$\lambda$ uniformity is only away from
the resonances; both uniformities allow compact nonreal-$z$ sets for
each fixed input. The capped domains remain $D(L_A)$, with form domain
$\mathcal F_A$; the limiting inherited-wall realizations and their
selected source conditions are exactly (12.1) and (12.4).

The definitions, theorems and proofs of §§1–11 retain their stated
hypotheses and conclusions. Their ground, profile and separate-resource
laws are distinct from Theorem 12.1: ground collapse above
$\lambda_D$ can coexist with its finite nonreal-resolvent limit, as
§20 explains. No stronger cap-to-fixed-radius operator-norm response
or arbitrary actual trace bound is supplied or needed by the
graph-core proof (§20). A real eigenvalue of a reference realization
does not exclude that parameter from Theorem 12.1; real-pole spectral
bookkeeping is not thereby supplied. Norm-resolvent convergence,
quantitative rates, all-level counts, arbitrary varying-$\lambda$
sequences, model-uniformity and new resource finite parts remain
outside the conclusions, as specified in Theorem 12.1 and §20.

## 追加锚（本行以下为增补区）
