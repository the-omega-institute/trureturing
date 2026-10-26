# Native two-control Green attraction, critical stability and periodic binding

> This reference volume uses the `generic-v1` theorem/proof shape. Once
> published, its existing text is preserved; corrections and extensions belong
> after the final append anchor. The mathematical statements below are ordinary
> proofs, not Lean-kernel-certified declarations.

## 1. Source, added analysis and the question being answered

**Definition 1.1 (the fixed native source).** Let [N] denote
[Auric FIB atom probability, phase transport and holonomy](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md).
Use exactly [N, Definitions 2.1, 2.3, 3.1 and 8.1]. In mode order
$(0,1,2,3,13)$, put

$$
r=1-Z,
\qquad p_k=(r-X-Y+k,X-k,Z,Y-k,k),
\qquad d=(1,-1,0,-1,1)^{\mathsf T},
$$

$$
0<Z<1,\quad 0<X,Y<r,\qquad
J_b=(\max(0,X+Y-r),\min(X,Y)).
$$

The means are fixed. The preparation height and all preparation phases are
fixed but arbitrary. Representatives have the negative convention
$\psi_s=\sqrt{p_s}\,e^{-i\theta_s}$. The original controls satisfy
$\dot p=d\dot k$, $\dot\theta=w(k)\dot\chi$, with

$$
\mathcal I(k)=\sum_{s\in\{0,1,3,13\}}p_s(k)^{-1},
\qquad w_s(k)=\frac{d_s}{p_s(k)\mathcal I(k)}.
$$

They are the finite-variation, absolutely continuous or piecewise $C^1$
histories of [N, Definition 3.1]. No mean selector is added.

Write $E_-=\{X+Y=r\}$ and $E_+=\{X=Y\}$. With
$m=4-\mathbf1_{E_-}-\mathbf1_{E_+}$, group equal increments as in [N, §8]:
$h_2=0$, $h_0=h_{13}$ on $E_-$, and $h_1=h_3$ on $E_+$.
These are equalities of increments, not restrictions on preparation phases.
The current-ray source is

$$
\mathcal M_b=J_b\times\mathbb T^m,
\qquad \mathbb T=\mathbb R/(2\pi\mathbb Z).
$$

[N, Theorem 8.2] supplies exact finite native realizations of every point.
The direct fields, with one coordinate for each pole group, are

$$
P=\partial_k,
\qquad Q=\sum_{a=1}^m w_a(k)\partial_{h_a},
\qquad w_a(k)=\frac1{\mathcal I(k)(k-\lambda_a)}.
\tag{1.1}
$$

The distinct $\lambda_a$ are obtained by grouping the four poles
$X+Y-r,X,Y,0$; their multiplicities remain in $\mathcal I$.
A common relative command $(a(t),b(t))$ has the original guard
$k+a(t)\in J_b$ for every $t$ and phase increment
$\int w(k+a(t))\,db(t)$, exactly as in [N, Definition 9.1].
Restricting a path to an interior cylinder imposes an additional restriction
on that guard. Neither an arbitrary height displacement nor a phase rotation
is promoted to an everywhere-defined native operation.

**Definition 1.2 (four regimes and separate quantities).** The source data
consumed from [N, Theorem 10.3] are

| Fixed means | Current-ray dimension | Direct rank | Growth vector | Weights | $Q_{\rm vol}$ |
| --- | --- | --- | --- | --- | --- |
| Neither wall | $5$ | $2$ | $(2,3,4,5)$ | $(1,1,2,3,4)$ | $11$ |
| $E_-$ only | $4$ | $2$ | $(2,3,4)$ | $(1,1,2,3)$ | $7$ |
| $E_+$ only | $4$ | $2$ | $(2,3,4)$ | $(1,1,2,3)$ | $7$ |
| Both walls | $3$ | $2$ | $(2,3)$ | $(1,1,2)$ | $4$ |

These hold at every height in the indicated open fiber. The estimates below
fix one row and one mean; no uniformity across a wall or a probability
endpoint is implicit. The abbreviation $Q_v$ means $Q_{\rm vol}$ and is not
the vector field $Q$. The number $m$ is not the attractive coupling $g$.
Current-ray dimension, direct rank, growth, predictive capacity and physical
axes have different definitions. In particular [N, Theorem 9.8]'s infinite
all-future affine capacity is not an infinite-dimensional ray manifold.

**Definition 1.3 (common closed operator, measure and clock).** Choose
$I=(l,u)\Subset J_b$, $\Omega=I\times\mathbb T^m$, and a source
$o\in\Omega$. Explicitly assume a real smooth positive density $\rho$ and a
real smooth symmetric positive definite $2\times2$ matrix $A$ on an open
neighbourhood of $\overline\Omega$. Set

$$
d\mu=\rho\,dk\,dh_1\cdots dh_m,
\quad X_1=P,\quad X_2=Q,
\quad T_A[f]=\int_\Omega\sum_{i,j}a^{ij}(X_jf)\overline{X_if}\,d\mu.
\tag{1.2}
$$

The phase measure here is unnormalized angular measure. Let $\mathcal F_A$
be the closure of $C_c^\infty(\Omega)$ in
$(\|f\|_2^2+T_A[f])^{1/2}$. This is the horizontal Dirichlet form domain;
it is not asserted to be the ordinary isotropic $H^1_0$ domain. Its associated
operator is specified completely by

$$
\begin{aligned}
D(L_A)&=\{f\in\mathcal F_A:\ \exists F\in L^2(\mu),
 T_A(f,v)=\langle F,v\rangle\text{ for every }v\in\mathcal F_A\},\\
L_Af&=F,
\qquad L_A=\left(\sum_{i,j}X_i^*(a^{ij}X_j)\right)_{F,\Omega},
\qquad X_i^*=-X_i-\operatorname{div}_\mu X_i.
\end{aligned}
\tag{1.3}
$$

The inner product and polarized form are linear in the first slot.
The boundary is periodic in every actual phase and Dirichlet at $k=l,u$.
Both height faces are noncharacteristic because $Pk=1$.
The analytic clock is fixed by $H_t=e^{-tL_A}$: its instantaneous control
covariance is $2A\,dt$. There is no independent rescaling of the field clock.
Define, initially as a nonnegative extended integral,

$$
\Gamma_{A,o}(q)=\int_0^\infty p_t^\Omega(o,q)\,dt,
\qquad
V_{A,o}[f]=\int_\Omega\Gamma_{A,o}|f|^2\,d\mu,
\qquad q_{A,g}[f]=T_A[f]-gV_{A,o}[f],\quad g>0.
\tag{1.4}
$$

The heat kernel and $\Gamma$ use precisely (1.2)--(1.3), including its density,
boundary and clock. In particular $\Gamma$ is the full killed Green field of
the free kinetic operator, not the Green field of the already perturbed
operator. The unit-source convention is
$\int\Gamma_{A,o}L_A\varphi\,d\mu=\varphi(o)$.
Density, covariance, clock, killing, attraction and the analytic state space
$L^2(\Omega,\mu)$ are added structure. An analytic function on ray space is
not a prepared five-mode ray or an acquisition procedure.

## 2. Full Green prerequisites on the actual cylinders

**Proposition 2.1 (closedness, gap, heat and compact free form).** For every
row of Definition 1.2 and every choice in Definition 1.3, the form is
closable, densely defined and Markovian. Its closure is nonnegative and has
a positive spectral gap. Its heat kernel is symmetric, smooth and strictly
positive for $t>0$ and interior pairs. The embedding
$\mathcal F_A\hookrightarrow L^2(\Omega,\mu)$ is compact.

**Proof.** Write $A=\Sigma\Sigma^{\mathsf T}$ using its smooth positive
square root and $Y_a=\sum_i\Sigma_{ia}X_i$. Then
$T_A[f]=\sum_a\|Y_af\|_2^2$. If $f_n\to0$ and $Y_af_n\to v_a$ in $L^2$,
testing against a compactly supported smooth $\varphi$ gives
$\langle v_a,\varphi\rangle=\lim\langle f_n,Y_a^*\varphi\rangle=0$.
This proves closability. Smooth compactly supported functions are dense in
$L^2$; the chain rule for real normal contractions gives the Markov property.
The representation of a closed nonnegative form gives (1.3).

On the compact closure choose constants
$0<\rho_-\le\rho\le\rho_+$ and $A\ge a_-I_2$, with $a_->0$.
One-dimensional Dirichlet Poincaré on each phase fiber yields

$$
\|f\|_2^2\le\frac{\rho_+}{\rho_-}
\frac{(u-l)^2}{a_-\pi^2}T_A[f],
\qquad L_A\ge\lambda_A:=
\frac{\rho_-a_-}{\rho_+}\frac{\pi^2}{(u-l)^2}>0.
\tag{2.1}
$$

This passes to the form closure. It uses $P=\partial_k$, so it does not
require a global flow box for the phase coordinates.

For the differential generator the exact expression is

$$
-L_A=\sum_aY_a^2+Y_0,
\qquad Y_0=\sum_a(\operatorname{div}_\mu Y_a)Y_a.
\tag{2.2}
$$

There is no smooth potential, and the drift is horizontal. The invertible
smooth frame change preserves the bracket flag: expanding a bracket adds
coefficient multiples of earlier brackets, and the inverse frame change
gives the reverse inclusion. Thus strong Hörmander generation, constant
ranks and bounded step $m$ hold on a neighbourhood of the closure.
The contraction semigroup, smooth density and these hypotheses are precisely
the free-heat hypotheses in [H, §3.1.2]. Interior smoothness follows there.
Bracket accessibility on the connected cylinder and the strong positivity
principle give strict positivity; locally accessible components are open, so
there is only one such component. No third diffusion input is used.

For compactness choose a slightly larger height interval
$I'\Subset J_b$ on which the same smooth positive $A,\rho$ are defined,
with $\overline I\subset I'$, and let $\Omega'=I'\times\mathbb T^m$.
Both forms are closures of their compact cores for the identical expression.
Killing on the smaller open set gives domain domination
$0\le p_t^\Omega(q,q')\le p_t^{\Omega'}(q,q')$; this is equivalently the
Markov process stopped sooner, or Dirichlet-form domain monotonicity.
For each $t>0$ the latter smooth kernel is bounded on the compact set
$\overline\Omega\times\overline\Omega$. Since $\mu(\Omega)<\infty$,
$H_t$ is Hilbert--Schmidt and therefore compact.
The resolvent integral
$(L_A+1)^{-1}=\int_0^\infty e^{-t}H_t\,dt$ is a norm limit of compact
operators: the omitted interval $(0,\delta)$ has norm at most $\delta$,
and the far tail at most $e^{-R}$. The compact positive resolvent has compact
square root. Its square root maps $L^2$ boundedly onto $\mathcal F_A$ with
the form norm, proving compactness of the stated embedding. This argument
uses an interior extension only to prove estimates; it changes neither the
chosen cylinder nor its killed operator. $\square$

**Proposition 2.2 (finite positive unit-source full Green).** In the same
contract, $\Gamma_{A,o}$ is strictly positive, finite and smooth off $o$,
belongs to $L^1(\Omega,\mu)$, and is bounded on
$\Omega\setminus U$ for every neighbourhood $U$ of $o$ with compact
closure in $\Omega$. At $o$ the integral is infinite. For all
$\varphi\in C_c^\infty(\Omega)$,

$$
\int_\Omega\Gamma_{A,o}L_A\varphi\,d\mu=\varphi(o).
\tag{2.3}
$$

In particular (1.4) is finite on
$\mathcal D_o=C_c^\infty(\Omega\setminus\{o\})$ before any attraction
claim is made.

**Proof.** The sub-Markov property bounds the heat row mass by one.
For $t\ge1$, the semigroup identity and (2.1) give

$$
p_t^\Omega(o,q)\le e^{-\lambda_A(t-1)}
\sqrt{p_1^\Omega(o,o)p_1^\Omega(q,q)}.
\tag{2.4}
$$

Indeed the two time-$1/2$ rows have squared $L^2$ norms equal to their
time-one diagonals, and the intervening semigroup has the displayed norm.
For the row mass, pairing one time-$1/2$ row with $H_{t-1/2}1$ gives

$$
\int_\Omega p_t^\Omega(o,q)\,d\mu(q)
\le \mu(\Omega)^{1/2}e^{-\lambda_A(t-1/2)}
\sqrt{p_1^\Omega(o,o)}\quad(t\ge1).
\tag{2.5}
$$

Tonelli and the small-time mass bound prove $\Gamma\in L^1$.
Away from $o$, the heat kernel extended by zero to $t<0$ solves the
homogeneous parabolic equation across $t=0$; parabolic hypoellipticity makes
it smooth and flat there. This is [H, §3.2.1]'s off-diagonal flatness,
$O_K(t^N)$ for every $N$ on each off-source interior compact $K$.
Together with (2.4) it proves finite off-source values, locally uniform
convergence, and positivity. Integrating
$-\partial_t(H_t\varphi)(o)=(H_tL_A\varphi)(o)$ gives (2.3).
The initial value is $\varphi(o)$; the terminal value is zero by smoothing
and the gap. Absolute interchange follows from $\Gamma\in L^1$ and bounded
$L_A\varphi$. Spatial hypoellipticity in (2.3) gives smoothness off $o$.

Apply the same argument on $\Omega'$ from Proposition 2.1. Domain domination
bounds $\Gamma_{A,o}^\Omega$ by $\Gamma_{A,o}^{\Omega'}$. The latter is
bounded on the off-source compact $\overline\Omega\setminus U$.
This establishes the bound all the way towards the original killed boundary,
without presuming a boundary regularity theorem.
Finally the local diagonal result of [N, Theorem 10.7], with the hypotheses
checked in Proposition 2.1, is
$p_t(o,o)\sim c_ot^{-Q_v/2}$, $c_o>0$. All four $Q_v\ge4$, so its integral
at zero diverges. A point value of infinity does not contradict the proved
spatial $L^1$ property. $\square$

## 3. Concentration on both single walls and off both walls

**Theorem 3.1 (native supercritical concentration).** Fix either single-wall
regime or the neither-wall regime. For every operator in Definition 1.3,
every $o\in\Omega$ and every $g>0$, there are normalized
$f_s\in\mathcal D_o$, $s\downarrow0$, such that

$$
T_A[f_s]\le C s^{-2},\qquad
V_{A,o}[f_s]\ge c s^{2-Q_v},\qquad
q_{A,g}[f_s]\longrightarrow-\infty.
\tag{3.1}
$$

Here $Q_v=7$ on either single wall and $Q_v=11$ off both. No semibounded
closed form can agree with these energies on all of $\mathcal D_o$.
The same statement holds with any fixed positive coefficient multiplying
$T_A$.

**Proof.** Use the actual privileged chart of [N, (10.6a)], centered at
$o=(k_o,h_o)$:

$$
x=k-k_o,\qquad z=W_{k_o}^{-1}(h-h_o),\qquad
W_{k_o}=\left(\frac{w^{(j)}(k_o)}{j!}\right)_{0\le j<m}.
\tag{3.2}
$$

The native grouped-pole determinant makes $W_{k_o}$ invertible at every
allowed height. In a real phase chart the rescaling is

$$
\delta_s(x,z_0,\ldots,z_{m-1})
=(sx,sz_0,s^2z_1,\ldots,s^mz_{m-1}),
\quad \widehat P=\partial_x,
\quad \widehat Q=\sum_{j=0}^{m-1}x^j\partial_{z_j}.
\tag{3.3}
$$

Its determinant is $s^{Q_v}$. The Taylor calculation in [N, (10.8a)] gives
$P=\partial_x$, $Q=\sum_j(x^j+O(x^m))\partial_{z_j}$, with smooth
rescaled convergence on compacts. In particular this is a checked
privileged chart, not ordinary isotropic shrinking in $m+1$ coordinates.
For $Y_a$ in (2.2), the rescaled fields converge to
$\widehat Y_a=\sum_i\Sigma_{ia}(o)\widehat X_i$, where
$(\widehat X_1,\widehat X_2)=(\widehat P,\widehat Q)$.
The rescaled density is

$$
j_s(\xi)\,d\xi
=\rho\bigl(\Phi_o^{-1}(\delta_s\xi)\bigr)|\det W_{k_o}|\,d\xi
\longrightarrow j_0\,d\xi,
\qquad j_0=\rho(o)|\det W_{k_o}|>0.
\tag{3.4}
$$

For clarity, every hypothesis for [H, Theorem B, (2.8)] is present:
the vector fields and density are smooth near the chart closure; $A$ has a
smooth invertible square root; the step is bounded by $m$; the actual flag
is regular; the drift (2.2) is horizontal and disappears after multiplying
by $s^2$ and rescaling; there is no potential; and the Friedrichs semigroup
is a contraction. Theorem 3.2 of [H] localizes from a larger interior
realization to the killed one, with identical expression and density and
bounded semigroup norms. Thus

$$
s^{Q_v}p_{s^2t}^\Omega(o,\Phi_o^{-1}(\delta_s\xi))
\longrightarrow\widehat p_o(t,0,\xi)
\tag{3.5}
$$

uniformly on compact positive-time intervals and compact coordinate sets.
The tangent density is (3.4), not an independently normalized Lebesgue
kernel. The polynomial fields in (3.3) bracket-generate at every point:
$\widehat Q,\partial_x\widehat Q,\ldots,
\partial_x^{m-1}\widehat Q$ form a triangular vertical basis.
The tangent heat kernel is strictly positive. These facts do not require
calling the tangent a rank-three group.

Choose a nonzero smooth $F$ supported in a compact annulus
$K\Subset\mathbb R^{m+1}\setminus\{0\}$ small enough for these coordinates.
Positivity and continuity give
$\min_{[1,2]\times K}\widehat p_o(t,0,\xi)>0$.
Consequently, for all small $s$, the full nonnegative Green integral obeys

$$
\begin{aligned}
\Gamma_{A,o}(\Phi_o^{-1}(\delta_s\xi))
&\ge\int_{s^2}^{2s^2}p_t^\Omega(o,\Phi_o^{-1}(\delta_s\xi))\,dt\\
&\ge c s^{2-Q_v}\qquad(\xi\in K).
\end{aligned}
\tag{3.6}
$$

This is a lower bound on the full Green field. It neither replaces that
field by a time window nor exchanges an infinite time integral with the
local limit (3.5).

Let $Z_s=\int|F(\xi)|^2j_s(\xi)\,d\xi$, so $Z_s\to Z_0>0$, and put

$$
f_s(\Phi_o^{-1}(\delta_s\xi))
=s^{-Q_v/2}Z_s^{-1/2}F(\xi),
\tag{3.7}
$$

with zero extension elsewhere. The support stays in an injective actual
phase chart and a compact positive height interval for all sufficiently
small $s$. It avoids $o$. Smoothness of the zero extension follows from
compact support of $F$. These are genuine members of the declared analytic
test domain, of norm exactly one. Writing $Y_a^{(s)}$ for the rescaled fields,

$$
T_A[f_s]=s^{-2}Z_s^{-1}
\sum_a\int|Y_a^{(s)}F|^2j_s\,d\xi\le Cs^{-2}.
\tag{3.8}
$$

Their smooth convergence proves the bound; (3.6) and normalization prove
the potential bound. Since $2-Q_v=-5$ or $-9$, the negative term dominates
$s^{-2}$ for every fixed positive coupling. All test supports consist of
actual current-ray points; this does not assert a native preparation of
the analytic amplitude $f_s$. The proof checks the rank-two source directly;
the rank-three implications in [C, §§82--83] are not applied. $\square$

## 4. Exact double-wall local model and the actual full field

**Definition 4.1 (constant-density anisotropic family).** For the remainder
of the stability and binding construction take $X=Y=r/2$, fix
$I\Subset(0,r/2)$, and retain the complete phase torus of [N, (8.17)]:

$$
\alpha=u_0-v_0\pmod{2\pi},\qquad \beta=u_0\pmod{2\pi}.
$$

Here $u_0,v_0$ denote the two grouped phase increments, not the height
endpoint $u$. The integer change of coordinates has determinant one and
inverse $(u_0,v_0)=(\beta,\beta-\alpha)$. Thus $\alpha$ and $\beta$ are
independent $2\pi$ circles; a relation angle $2\alpha$ would discard
information. Set

$$
P=\partial_k,\qquad
Q=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta,
\qquad d\mu=dk\,d\alpha\,d\beta,
\qquad A_\varepsilon=\operatorname{diag}(\varepsilon^2,1),\quad\varepsilon>0.
\tag{4.1}
$$

Write $T_\varepsilon,L_\varepsilon,\mathcal F_\varepsilon,
\Gamma_{\varepsilon,o}$ for precisely Definition 1.3 with these choices.
Both fields are divergence free, so
$L_\varepsilon=-(\varepsilon^2P^2+Q^2)_{F,\Omega}$.
The family changes only added covariance, not $P,Q$, the source or its
available native commands. Every assertion fixes a strictly positive
$\varepsilon$; there is no operator assertion at $\varepsilon=0$.

**Proposition 4.2 (normalized full-Green singular part).** Fix
$o=(k_o,\alpha_o,\beta_o)$ and set $c_o=1/2-k_o/r$. In the real local chart

$$
x=k-k_o,\quad y=2(\alpha-\alpha_o),\quad
z=-r\{\beta-\beta_o-c_oy\},
\qquad
\xi=x/\varepsilon,\quad\eta=y,\quad\zeta=z/\varepsilon,
\tag{4.2}
$$

one has exactly

$$
\varepsilon P=\partial_\xi=:U,\qquad
Q=\partial_\eta+\xi\partial_\zeta=:V,\qquad
 d\mu=\frac{\varepsilon^2}{2r}\,d\xi\,d\eta\,d\zeta.
\tag{4.3}
$$

Let $L_H=-(U^2+V^2)$ on the full real Heisenberg group with ordinary
Lebesgue Haar measure, and let
$G_H=\int_0^\infty p_t^H(0,\cdot)\,dt$ be its positive unit-source
fundamental solution. Then for $q\ne o$ in a sufficiently small neighbourhood
of $o$,

$$
\Gamma_{\varepsilon,o}(q)=K_\varepsilon(q)+R_\varepsilon(q),
\qquad K_\varepsilon(q)=\frac{2r}{\varepsilon^2}
G_H(\xi,\eta,\zeta),
\qquad |R_\varepsilon(q)|\le C_\varepsilon.
\tag{4.4}
$$

The remainder admits a bounded extension across $o$ for this fixed parameter.
The field in (4.4)
is still the full killed periodic Green kernel.

**Proof.** Direct differentiation gives (4.3); the absolute coordinate
Jacobian is $\varepsilon^2/(2r)$. The group law can be taken as

$$
(\xi,\eta,\zeta)(\xi',\eta',\zeta')
=(\xi+\xi',\eta+\eta',\zeta+\zeta'+\xi\eta').
\tag{4.5}
$$

It has left-invariant fields $U,V$, $[U,V]=\partial_\zeta$, and dilations
$(\xi,\eta,\zeta)\mapsto(s\xi,s\eta,s^2\zeta)$ of homogeneous dimension
four. [R, §2, (2.1), (2.6)--(2.7)] supplies $G_H=I_2=F_2$, since
$\Gamma(2/2)=1$: it is positive, smooth off zero, homogeneous of degree
$-2$, and $L_HG_H=\delta_0$ with respect to this Haar measure.
Multiplying by $2r/\varepsilon^2$ is necessary to obtain a unit source
relative to the measure in (4.3). This factor cannot be absorbed into an
unmentioned coupling convention.

There is also a direct integrated comparison. In the local coordinates the
full-space and cylinder differential expressions are identical, with the
same density (4.3) and the same clock. Their semigroups are contractions.
Use [H, Theorem 3.2] first between the cylinder and a small chart Dirichlet
realization, and then between that realization and the full group. On a
smaller compact chart this gives

$$
p_t^\Omega(o,q)-\frac{2r}{\varepsilon^2}
 p_t^H(0,(\xi,\eta,\zeta))=O_\varepsilon(t^N)
\tag{4.6}
$$

for every $N$ as $t\downarrow0$, uniformly including the source in the
spatial compact. This application is local: it does not identify the global
torus with the real group. The integral of the difference over $(0,1)$ is
bounded, using smoothness for times bounded away from zero. The cylinder
large-time integral is bounded there by (2.4). On the full group,
$p_t^H(0,q)\le p_t^H(0,0)=t^{-2}p_1^H(0,0)$ by Cauchy--Schwarz and
homogeneity, so its integral over $(1,\infty)$ is bounded as well.
Subtracting the two convergent integrals off the source proves (4.4).
No uncontrolled infinite-time limit of a tangent asymptotic was used.

The global identifications in the unscaled chart are the lattice generated
by $(\Delta y,\Delta z)=(4\pi,4\pi r c_o)$ and $(0,-2\pi r)$.
After scaling, the central entries are divided by $\varepsilon$.
They are not two arbitrarily chosen standard periods in a rectangular
$(y,z)$ chart. Only the original $(\alpha,\beta)$ torus is used in all
global formulas. $\square$

**Proposition 4.3 (unweighted relative form strength).** There is a finite
constant $C_H>0$, independent of $r,I,o,\varepsilon$, chosen for the
Lebesgue-normalized group in Proposition 4.2, such that for every fixed
$\varepsilon>0$ there is a finite $B_\varepsilon\ge0$ with

$$
V_{\varepsilon,o}[f]
\le\frac{2r C_H}{\varepsilon^2}T_\varepsilon[f]
+B_\varepsilon\|f\|_2^2
\qquad(f\in\mathcal F_\varepsilon).
\tag{4.7}
$$

The constant is sufficient, not sharp. The multiplier on the left is
unweighted $\Gamma_{\varepsilon,o}$, including all times and all phases.

**Proof.** Choose a continuous homogeneous norm $N$ on the group (4.5).
Positivity, smoothness and degree $-2$ give
$G_H\le C_N N^{-2}$ by taking a maximum on the compact unit sphere.
The unweighted Hardy inequality [R, Corollary 3.2] applies with
$p=2$, $\alpha=1$ and homogeneous dimension $4$; its strict condition is
$0<1<4/2$. Since
$\|L_H^{1/2}v\|_2^2=\|Uv\|_2^2+\|Vv\|_2^2$, it supplies a finite $C_H$
for which

$$
\int_{\mathbb R^3}G_H|v|^2\,d\xi\,d\eta\,d\zeta
\le C_H\int_{\mathbb R^3}(|Uv|^2+|Vv|^2)\,d\xi\,d\eta\,d\zeta
\quad(v\in C_c^\infty).
\tag{4.8}
$$

An alternative direct supplier is [B, Theorem 1.2] with $d=1$, $N=4$ and
$s=1$. Its fields are $\partial_a+b\partial_c$,
$\partial_b-a\partial_c$. The coordinate map
$(a,b,c)=(\xi,\eta,\xi\eta-2\zeta)$ sends $U,V$ exactly to these two
fields; its absolute Jacobian is $2$. Its gauge is
$((a^2+b^2)^2+c^2)^{1/4}$. The fixed factor $2$ occurs on both sides of
the inequality and cancels. Thus the cited inequality has the required
unweighted, horizontal one-derivative meaning in precisely our conventions.
Neither supplier inserts a vanishing horizontal-gradient factor into the
potential.

Choose smooth real $\chi,\vartheta$ with $\chi^2+\vartheta^2=1$,
$\chi=1$ near $o$, and $\chi$ supported in the chart of (4.4).
For example take $\chi=\cos\theta$, $\vartheta=\sin\theta$, with
$\theta=0$ near $o$ and $\theta=\pi/2$ outside the chart. On this support
(4.4) controls the remainder; where $\vartheta$ is nonzero away from a
smaller source neighbourhood Proposition 2.2 bounds the full Green field.
Consequently, for a compact smooth test,

$$
V_{\varepsilon,o}[f]
\le \int K_\varepsilon|\chi f|^2\,d\mu+C_\varepsilon'\|f\|_2^2
\le \frac{2rC_H}{\varepsilon^2}T_\varepsilon[\chi f]
+C_\varepsilon'\|f\|_2^2.
\tag{4.9}
$$

The second inequality uses (4.3), (4.8) and zero extension of the compact
chart function; it keeps the source normalization factor. The horizontal
localization identity is

$$
T_\varepsilon[\chi f]+T_\varepsilon[\vartheta f]
=T_\varepsilon[f]+\int
\bigl(\varepsilon^2|P\chi|^2+|Q\chi|^2
+\varepsilon^2|P\vartheta|^2+|Q\vartheta|^2\bigr)|f|^2\,d\mu.
\tag{4.10}
$$

It follows by expanding squares and differentiating
$\chi^2+\vartheta^2=1$. Dropping the nonnegative second localized energy
proves (4.7) on the smooth core. All cutoff coefficients are bounded for
fixed $\varepsilon$.
For a core sequence converging in $\mathcal F_\varepsilon$, (4.7) applied
to differences makes it Cauchy also in $L^2(\Gamma_{\varepsilon,o}\,d\mu)$.
A subsequence converges almost everywhere in ordinary $L^2$, identifying
that weighted limit with the same function. Thus every member of
$\mathcal F_\varepsilon$ has finite potential integral and (4.7) passes
to it. There is no claim that $B_\varepsilon$ is bounded as
$\varepsilon\downarrow0$. $\square$

## 5. Strict semiboundedness, domains and attainment

**Theorem 5.1 (a nonempty strict stability regime).** In Definition 4.1,
choose

$$
0<\gamma<(2rC_H)^{-1},\qquad
 g=\gamma\varepsilon^2,\qquad\varepsilon>0.
\tag{5.1}
$$

The actual full-Green form

$$
q_{\varepsilon,\gamma}[f]
=T_\varepsilon[f]-\gamma\varepsilon^2
\int_\Omega\Gamma_{\varepsilon,o}|f|^2\,d\mu
\tag{5.2}
$$

is closed and semibounded on exactly $\mathcal F_\varepsilon$ and satisfies

$$
q_{\varepsilon,\gamma}[f]
\ge(1-2rC_H\gamma)T_\varepsilon[f]
-\gamma\varepsilon^2B_\varepsilon\|f\|_2^2.
\tag{5.3}
$$

Its associated selfadjoint operator has compact resolvent, and its lowest
energy on the unit $L^2$ sphere is finite and attained. The strict margin
in (5.3), rather than positivity of the lowest energy, is the meaning of
strict stability here.

**Proof.** Proposition 4.3 makes the negative potential a Hermitian form on
$\mathcal F_\varepsilon$, with relative bound at most
$a=2rC_H\gamma<1$ and additive bound
$b=\gamma\varepsilon^2B_\varepsilon$. Apply [T, Theorem 6.24 (KLMN)]
to the closed nonnegative form $T_\varepsilon$. The resulting domain is
$\mathcal F_\varepsilon$ and the lower bound is (5.3). This proves
closedness as well as semiboundedness; finiteness of the potential alone
would not prove either assertion.

For any $c>b+1$, (5.3) and $q\le T_\varepsilon$ show that
$q+c\|\cdot\|_2^2$ and $T_\varepsilon+\|\cdot\|_2^2$ give equivalent
Hilbert norms. Proposition 2.1 therefore makes the new form-domain
embedding compact too. Its resolvent factors through this embedding,
hence is compact. Equivalently, for a normalized minimizing sequence the
lower estimate bounds the form norm. A weakly convergent subsequence in
the new Hilbert form norm converges strongly in $L^2$ by compactness, so its
limit still has norm one. Weak lower semicontinuity of the positive shifted
form shows that the limit attains the infimum. The Euler--Lagrange identity
for arbitrary form-domain variations puts this minimizer in the associated
operator domain and makes it an eigenvector at the lowest energy.
No compactness of the critical potential multiplier was presumed.
$\square$

**Proposition 5.2 (availability of punctured tests and phase-constant
states).** On the double-wall cylinder,
$C_c^\infty(\Omega\setminus\{o\})$ is a core for $T_\varepsilon$ and for
every form in Theorem 5.1. If $\phi\in H^1_0(I)$, then
$f(k,\alpha,\beta)=\phi(k)/(2\pi)$ belongs to
$\mathcal F_\varepsilon$, has norm $\|\phi\|_{L^2(I)}$, and

$$
T_\varepsilon[f]=\varepsilon^2\int_I|\phi'(k)|^2\,dk.
\tag{5.4}
$$

These are analytic admissibility statements and not native state-preparation
statements.

**Proof.** In the scaled group chart choose a smooth cutoff $\eta_s$ equal
to one on a dilated neighbourhood of zero and supported in a slightly
larger dilation of size $s$. Group homogeneity and (4.3) give, for fixed
$\varepsilon$,

$$
\|\eta_s\|_2^2=O_\varepsilon(s^4),\qquad
T_\varepsilon[\eta_s]=O_\varepsilon(s^2).
\tag{5.5}
$$

For each compact smooth $f$, the product rule bounds
$T_\varepsilon[f\eta_s]$ by a constant times
$\|f\|_\infty^2T_\varepsilon[\eta_s]$ plus the energy of $f$ on the
shrinking support. Both tend to zero, as does the $L^2$ norm.
Thus $f(1-\eta_s)$ approximates $f$ in the free form norm, avoids the
source, and remains compactly supported. Density followed by a diagonal
choice proves the first free-core assertion. Equivalent form norms in
Theorem 5.1 prove the perturbed-core assertion. This also explains why
removing one point imposes no extra boundary condition in this strict
regime; it does not decide any critical extension problem.

Approximate $\phi$ in $H^1_0(I)$ by compactly supported smooth height
functions. Their phase-constant lifts are smooth compactly supported on
$I\times\mathbb T^2$, and $Qf=0$, $Pf=\phi'/(2\pi)$.
The exact phase area is $(2\pi)^2$, proving the norm and (5.4) by passage
to the form limit. Proposition 4.3 gives finite potential energy for the
same states, including ones nonzero at the source. $\square$

## 6. Global periodic contribution and an attained negative family

**Proposition 6.1 (exact phase average of the full killed field).** Define

$$
G_I(k_o,k)=\frac{(\min(k_o,k)-l)(u-\max(k_o,k))}{u-l}.
\tag{6.1}
$$

For every $\varepsilon>0$, in the normalization (4.1),

$$
\int_{\mathbb T^2}\Gamma_{\varepsilon,o}(k,\alpha,\beta)
\,d\alpha\,d\beta
=\varepsilon^{-2}G_I(k_o,k),
\tag{6.2}
$$

as an $L^1(I)$ identity, with the nonnegative integral representative where
defined. In particular

$$
\int_\Omega\Gamma_{\varepsilon,o}\,d\mu
=\frac{(k_o-l)(u-k_o)}{2\varepsilon^2}.
\tag{6.3}
$$

**Proof.** On phase-independent functions the exact generator is
$\varepsilon^2\partial_k^2$. More explicitly, with independent real
Brownian motions, the added process has

$$
dK_t=\sqrt2\varepsilon\,dB_t^1,
\quad d\alpha_t=\frac1{\sqrt2}\,dB_t^2,
\quad d\beta_t=\sqrt2(1/2-K_t/r)\,dB_t^2.
\tag{6.4}
$$

There is no Itô correction since $Qk=0$ and $Q$ annihilates its
$k$-dependent coefficients. Wrap the actual two phases and kill exactly
at exit of $K_t$ from $I$. Its generator and boundary are precisely
(4.1), so uniqueness of the corresponding killed semigroup gives, for
bounded Borel height tests,

$$
H_t(f\circ\pi_k)(o)
=(e^{t\varepsilon^2\partial_k^2}_{D,I}f)(k_o).
\tag{6.5}
$$

Comparing kernel densities proves that the phase integral of the heat
kernel is the one-dimensional killed heat kernel. Tonelli integrates this
identity over all $t>0$. The inverse of
$-\varepsilon^2\partial_k^2$ has kernel $\varepsilon^{-2}G_I$:
(6.1) vanishes at the endpoints, is affine on either side of $k_o$, and
has derivative jump $-1$. This proves (6.2). Its integral in $k$ is
$(k_o-l)(u-k_o)/2$, proving (6.3).
The factor in (6.2) is an integral over phases, not their normalized
average; the normalized average is smaller by $4\pi^2$.
No deterministic Definition 3.1 history is equated with a Brownian path.
$\square$

**Theorem 6.2 (strictly stable attained-negative anisotropic family).**
Fix any double-wall source, any nonempty $I\Subset(0,r/2)$ and any
$o\in\Omega$. Choose $\gamma$ as in (5.1). Put $L=u-l$ and

$$
\phi_1(k)=\sqrt{2/L}\sin\frac{\pi(k-l)}L,
\qquad M_o=\int_I G_I(k_o,k)|\phi_1(k)|^2\,dk>0.
\tag{6.6}
$$

Every positive $\varepsilon$ satisfying

$$
\varepsilon^2<\frac{\gamma M_o L^2}{4\pi^4}
\tag{6.7}
$$

gives a closed strictly semibounded form (5.2) whose lowest normalized
energy is attained and strictly negative. The interval in (6.7) is
nonempty. The potential is the actual unit-source full killed Green kernel
of the same $L_\varepsilon$, with $g=\gamma\varepsilon^2$.

**Proof.** The function $G_I(k_o,k)$ is strictly positive for interior
$k,k_o$, and $\phi_1$ is positive on $I$, so $0<M_o<\infty$.
By Proposition 5.2 the phase-constant
$f_1=\phi_1/(2\pi)$ is an admissible normalized form state. Using the full
field identity (6.2), not a local singular approximation, gives

$$
\begin{aligned}
V_{\varepsilon,o}[f_1]&=\frac{M_o}{4\pi^2\varepsilon^2},\\
q_{\varepsilon,\gamma}[f_1]
&=\varepsilon^2\frac{\pi^2}{L^2}-\frac{\gamma M_o}{4\pi^2}.
\end{aligned}
\tag{6.8}
$$

Condition (6.7) makes the last quantity negative. Independently, (5.1)
and Proposition 4.3 give the strict local relative form margin in (5.3)
for every fixed $\varepsilon>0$. Theorem 5.1 then supplies a finite attained
infimum at most (6.8). This verifies sign, stability and attainment as
three separate assertions.

The local source coefficient grows as $\varepsilon^{-2}$, but its product
with the coupling remains $2r\gamma$ times the fixed group form strength.
The full phase-average field also grows as $\varepsilon^{-2}$; its coupled
contribution in (6.8) stays positive in magnitude while the height kinetic
cost is $O(\varepsilon^2)$. These two exact facts, on the actual torus,
make the construction possible. No statement at zero covariance, no lower
bound uniform as $\varepsilon\downarrow0$, and no identity-covariance
negative-energy assertion is needed. $\square$

## 7. Local threshold, global sign and limits of localization

**Proposition 7.1 (large-coupling local obstruction on the double wall).**
Fix the constant-density family and any nonzero
$v\in C_c^\infty(\mathbb R^3\setminus\{0\})$. Write

$$
\mathcal T(v)=\int(|Uv|^2+|Vv|^2),\qquad
\mathcal V(v)=\int G_H|v|^2>0.
$$

If

$$
2r\gamma\mathcal V(v)>\mathcal T(v),
\tag{7.1}
$$

then for $g=\gamma\varepsilon^2$ and each fixed $\varepsilon>0$ the
actual cylinder energies on normalized punctured tests are unbounded below.
Thus sufficiently large coupling does collapse even in the double-wall
row, whereas (5.1) supplies a nonempty strict stable range.

**Proof.** Rescale $v$ by the exact group dilation to
$v_s=s^{-2}v(\delta_{1/s}\cdot)$, transport it through (4.2), and divide
by $\sqrt{\varepsilon^2/(2r)}\|v\|_2$ to normalize in the actual density.
For small $s$ its compact support is in an injective interior chart and
avoids $o$. Equations (4.3)--(4.4) give

$$
q_{\varepsilon,\gamma}[f_s]
=s^{-2}\frac{\mathcal T(v)-2r\gamma\mathcal V(v)}{\|v\|_2^2}
+O_{\varepsilon,\gamma}(1).
\tag{7.2}
$$

The bounded remainder follows from the full-Green remainder in (4.4), not
from discarding long times. Condition (7.1) makes the leading term negative.
The finite ratio for any one such $v$ proves a large-coupling obstruction.
No optimization of that ratio, equality case or sharp constant is asserted.
$\square$

**Proposition 7.2 (what the distinction does and does not select).** Within
the added common-operator contract, $Q_v=7,11$ force concentration collapse
for every positive coupling, while the double-wall periodic cylinder
admits the strictly stable attained-negative family of Theorem 6.2.
Neither statement identifies physical spatial axes, implements analytic
state preparation, or supplies noncompact physical localization.

**Proof.** The first assertion is Theorem 3.1. The second uses both (4.7)
and (6.2), so it is stronger than a local exponent count. The logical
limits follow from their domains and inputs. The same native direct rank
is two in all rows. Every $(k,h)$ used is an actual current-ray point, but
the normalized eigenfunction belongs to the newly declared Hilbert space
of functions on those points. The original five-mode ray lives in a
different space and obeys the finite-variation native control law.
No map between these state classes is part of the definitions.

Moreover the finite cylinder already has compact free resolvent, so its
free lowest eigenstate is attained even at $g=0$. The negative energy in
Theorem 6.2 is measured relative to the specified zero of the free operator;
it is not an energy below an essential-spectrum threshold of a noncompact
physical Hamiltonian. Removing the height killing, extending towards
probability endpoints, decompactifying phases or changing density requires
new operator and Green estimates. The local lower bound (3.6) and local
comparison (4.4) do not establish any all-scale homogeneous law.

The source-to-spatial contract [C, §81.5] requires a common actual map,
measure, domain, boundary and clock correspondence for field and kinetic
laws. None is supplied by counting the three double-wall coordinates.
[C, Definitions 82.1 and 83.1] assume three independent horizontal fields;
our source has only two. Their rank-three implication $Q\ge5$ in higher
ambient dimension therefore has no application to the double wall.
The full-Green finite-window mechanism in [C, Theorem 83.2] is reused with
its prerequisites explicitly rechecked in §§2--3, not with its rank-three
conclusion.

The acquired-reference source [A, Definitions 1.1--1.4 and 2.5] separates
authentic source history, acquired records, retained resources and a passive
decoder. Its calibration is a discrete source-update count, not a covariance,
metric or analytic-time calibration for (1.2). The finite-affine-factor
classification [F, §10] concerns guarded native continuations and their
quotients; it supplies neither a diffusion nor a Green-energy state class.
These existing results consequently add no actuator, noise direction,
reset, free rotation, mean selection or preparation guarantee to the
construction. $\square$

**Definition 7.3 (unsettled boundaries).** The following questions are left
open here: the optimal local coupling constant; its equality case and
possible critical form domains; the exact global sign boundary for a
fixed cylinder and covariance; negative energy at identity covariance;
any limit of ground states or lower bounds uniform in $\varepsilon$; and
localization on a separately specified noncompact physical realization.
The proof of strict stability is for the explicit constant-density diagonal
family (4.1). It does not classify all variable $A,\rho$ allowed in §1.
The off-wall collapse theorem does cover those variable coefficients under
the stated positive smooth closure assumptions. None of these results is
a rule selecting the means $X=Y=r/2$ or a completion of a why-three
investigation.

## 8. Primary supplier correspondence and mathematical contribution

**Mathematical citation 8.1 (directly used literature).** The following
are literature-attested intermediate inputs, not new general theorems of
this volume.

| Reference | Exact supplied result and correspondence |
| --- | --- |
| [H] Y. Colin de Verdière, L. Hillairet, E. Trélat, *Small-time asymptotics of hypoelliptic heat kernels near the diagonal, nilpotentization and related results*, Annales Henri Lebesgue 4 (2021), 897--971, [DOI 10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf) | §3.1.2 supplies the free semigroup/heat setting; Theorem B, (2.8), pp.915--916, gives the rescaled positive-time local kernel limit for a bounded-step privileged chart and horizontal drift. Theorem 3.2, p.921, compares identical local expressions and densities with bounded semigroup norms. Our generator is (2.2), with smooth positive $\rho,A$ near the compact closure; the drift is horizontal, the potential zero, and the two fields bracket-generate. The applications are (3.5) and the integrable kernel difference (4.6); the theorem is not an infinite-time Green convergence assertion. |
| [R] P. Ciatti, M. G. Cowling, F. Ricci, *Hardy and uncertainty inequalities on stratified Lie groups*, [arXiv:1308.2373v1](https://arxiv.org/html/1308.2373v1), [DOI 10.1016/j.aim.2014.12.040](https://doi.org/10.1016/j.aim.2014.12.040) | §2, (2.1) and (2.6)--(2.7): $I_2=\int_0^\infty p_t\,dt$ is the positive degree $2-Q$ unit-source kernel. Theorem A/Corollary 3.2: $\|N^{-\alpha}v\|_p\le C\|L^{\alpha/2}v\|_p$ for $0<\alpha<Q/p$. We use $p=2,\alpha=1,Q=4$, $L=L_H$, Haar measure $d\xi\,d\eta\,d\zeta$, then the explicit density conversion (4.3). No sharp constant is imported. |
| [B] H. Bahouri, J.-Y. Chemin, I. Gallagher, *Refined Hardy inequalities*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (5) V (2006), 375--391, [primary PDF](https://www.numdam.org/item/ASNSP_2006_5_5_3_375_0.pdf) | Theorem 1.2, p.377, supplies the unweighted Heisenberg estimate for $s\in(0,N/2)$. Our choice is $d=1,N=4,s=1$; Definition 1.1 identifies its $\dot H^1$ norm with horizontal energy. The explicit map $(\xi,\eta,\zeta)\mapsto(\xi,\eta,\xi\eta-2\zeta)$ matches both horizontal fields and accounts for Haar Jacobian $2$. This is an alternative supplier of the intermediate inequality (4.8). |
| [T] G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99, 2009 edition, [author's text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorem 6.24 (KLMN), §6.5, p.150 | The input is the closed form $T_\varepsilon$, with perturbation $-\gamma\varepsilon^2V_{\varepsilon,o}$ and verified relative bound $2rC_H\gamma<1$. It yields closedness and semiboundedness on the same form domain. Compactness comes separately from Proposition 2.1 and norm equivalence; attainment is proved in Theorem 5.1. |

The gradient-weighted Hardy potential sometimes written
$|\nabla_H N|^2/N^2$ is not substituted for $G_H$ or for
$\Gamma_{\varepsilon,o}$. The horizontal-gradient factor can vanish in
central directions, whereas $G_H$ is positive off its pole. Such a weighted
estimate alone does not bound the unweighted multiplier needed in (4.7).

**Mathematical citation 8.2 (repository correspondence and new application).**
[N, §§2--4,8--10] supplies the native probability fiber, arbitrary fixed
preparation phases, exact current-ray torus, common-command guards, fields,
flag and local heat hypotheses. [C] is
[Recursive holographic boundary geometry, Continuation III](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md),
§§81--83. [A] is
[Adaptive acquired-reference frontier](RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md).
[F, §10] is the finite-affine-factor classification in the immutable source
[Native continuation affine obstruction and approximation](https://github.com/the-omega-institute/trureturing/blob/17b7165cce4/docs/develop/theory/FIB_NATIVE_CONTINUATION_AFFINE_OBSTRUCTION_AND_APPROXIMATION.md).

The repo-derived contribution is the full rank-two source application in
Theorem 3.1 and the new double-wall combination (4.4), (4.7), (6.2) and
(6.8): actual killed-periodic Green control, normalized anisotropic local
strength, exact global phase contribution, and a nonempty strictly stable
attained-negative family. The common-domain and finiteness arguments make
those applications well-defined. The separate sufficient stable and
unstable conditions do not determine a sharp threshold. No general Hardy,
heat, KLMN or compact-resolvent theorem is claimed as new, and no worldwide
originality claim or physical realization follows from this composition.

## 追加锚（本行以下为增补区）

## 9. Added phase cover and unchanged native histories

**Definition 9.1 (native source and covering contract).** Retain Definition
4.1, with $0<Z<1$, $r=1-Z$, $H=r/2$, $X=Y=H$ and probabilities
$(k,H-k,Z,H-k,k)$ in the original mode order. Preparation phases remain
arbitrary and fixed, and the amplitudes retain the negative phase
convention. Write

$$
\widetilde\Omega=I\times\mathbb R^2,\qquad
I=(l,u),\quad 0<l<k_o<u<H,\qquad
\varpi(k,A,B)=(k,[A]_{2\pi},[B]_{2\pi}).
\tag{9.1}
$$

Here $A,B$ denote real phase coordinates. This is additional
covering structure over $\Omega=I\times\mathbb T^2$, not a replacement of
its current-ray torus. The deck transformations are
$(A,B)\mapsto(A+2\pi n,B+2\pi m)$, $(n,m)\in\mathbb Z^2$.
The unimodular change in Definition 4.1 fixes these two actual periods.
Lift the same fields, with the same notation,

$$
P=\partial_k,\qquad Q=\tfrac12\partial_A+
c(k)\partial_B,\qquad c(k)=\tfrac12-k/r,\qquad
d\widetilde\mu=dk\,dA\,dB.
\tag{9.2}
$$

For an original numerical absolutely continuous or piecewise $C^1$
command $(a,b)$ starting at zero, put $J_t=\int_0^t a\,db$.
The exact lifted path from $(k,A_0,B_0)$ is

$$
(k+a_t,\ A_0+b_t/2,\
 B_0+c(k)b_t-J_t/r).
\tag{9.3}
$$

Its original whole-height guard remains $k+\min a>0$ and
$k+\max a<H$. Requiring this path to remain in $I$ adds precisely
$k+\min a>l$ and $k+\max a<u$. Neither endpoint membership nor taking a
lift changes these extrema conditions. Formula (9.3) directly reuses
[N, Theorems 9.2--9.3] and the full-path correspondence in
[Native guarded lift limits and diffusion selection, §§2.2--2.4](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md).
No new control, mean selector, phase reset or unrestricted rotation is
included.

**Definition 9.2 (one fixed free and attractive analytic realization).**
Fix $\varepsilon>0$ and a lifted pole
$o=(k_o,A_o,B_o)$. Let

$$
\begin{aligned}
\widetilde T[f]&=\int_{\widetilde\Omega}
  (\varepsilon^2|Pf|^2+|Qf|^2)\,d\widetilde\mu,\\
\widetilde{\mathcal F}&=
 \overline{C_c^\infty(\widetilde\Omega)}^{(\|\cdot\|_2^2+\widetilde T)^{1/2}},
 \qquad \widetilde L=-(\varepsilon^2P^2+Q^2)_{F,\widetilde\Omega},\\
\widetilde G_o(q)&=\int_0^\infty\widetilde p_t(o,q)\,dt,\qquad
\widetilde V[f]=\int_{\widetilde\Omega}\widetilde G_o|f|^2\,d\widetilde\mu,
 \qquad \widetilde q_g=\widetilde T-g\widetilde V .
\end{aligned}
\tag{9.4}
$$

The free operator is the operator represented by the closed free form:
$f\in D(\widetilde L)$ exactly when $f\in\widetilde{\mathcal F}$ and
$\widetilde T(f,v)=\langle F,v\rangle$ for some $F\in L^2$ and every
$v\in\widetilde{\mathcal F}$, in which case $\widetilde Lf=F$.
This specifies height Dirichlet killing and no phase boundary.
The semigroup clock is $e^{-t\widetilde L}$, with control covariance
$2\operatorname{diag}(\varepsilon^2,1)\,dt$. The field in (9.4) is the
full unshifted Green field of this free operator, with unit source
relative to $d\widetilde\mu$. No threshold shift is made in its definition.
The closed horizontal form domain, rather than isotropic $H^1_0$, is used.

## 10. Same-field noncompact Green stability and attained binding

**Theorem 10.1 (native cover localization at every fixed positive
covariance parameter).** In Definitions 9.1--9.2 let $C_H$ be the
Lebesgue-normalized constant already supplied by (4.8), and set

$$
g_*=\frac{\varepsilon^2}{2rC_H},\qquad
d=u-l,\qquad \lambda_D=\frac{\varepsilon^2\pi^2}{d^2}.
\tag{10.1}
$$

The free form is closed and Markovian after closure, and
$\widetilde T\ge\lambda_D\|\cdot\|_2^2$. Its killed heat law projects
under $\varpi$ to precisely the periodic free law of Definition 4.1.
For original phase representatives $q=(k,A,B)$,

$$
\begin{aligned}
p_t^\Omega(\varpi o,\varpi q)
 &=\sum_{(n,m)\in\mathbb Z^2}
 \widetilde p_t(o,(k,A+2\pi n,B+2\pi m)),\\
\Gamma_{\varepsilon,\varpi o}(\varpi q)
 &=\sum_{(n,m)\in\mathbb Z^2}
 \widetilde G_o(k,A+2\pi n,B+2\pi m).
\end{aligned}
\tag{10.2}
$$

The Green sum is interpreted as a nonnegative sum, including infinite
values at projected poles. The cover field is positive, finite and smooth
off $o$, integrable, bounded outside every relatively compact
neighbourhood of $o$, and tends to zero uniformly in $k\in I$ as
$|(A-A_o,B-B_o)|\to\infty$. It has unit source:

$$
\int_{\widetilde\Omega}\widetilde G_o\widetilde L\varphi\,
 d\widetilde\mu=\varphi(o)\quad(\varphi\in C_c^\infty(\widetilde\Omega)).
\tag{10.3}
$$

With $G_I$ exactly as in (6.1), its phase marginal and mass are

$$
\int_{\mathbb R^2}\widetilde G_o(k,A,B)\,dA\,dB
 =\varepsilon^{-2}G_I(k_o,k),\qquad
\int_{\widetilde\Omega}\widetilde G_o\,d\widetilde\mu
 =\frac{(k_o-l)(u-k_o)}{2\varepsilon^2}.
\tag{10.4}
$$

The marginal equality is an $L^1(I)$ identity with the nonnegative
integral representative. For every $0<g<g_*$ the attractive form is closed
on exactly $\widetilde{\mathcal F}$ and satisfies

$$
(1-g/g_*)\widetilde T[f]\le\widetilde q_g[f]\le\widetilde T[f].
\tag{10.5}
$$

If $\widetilde H_g$ denotes its represented operator, then

$$
\begin{gathered}
\inf\sigma_{\rm ess}(\widetilde L)
 =\inf\sigma_{\rm ess}(\widetilde H_g)=\lambda_D,\\
0<(1-g/g_*)\lambda_D\le
E_g:=\inf_{\|f\|_2=1}\widetilde q_g[f]<\lambda_D.
\end{gathered}
\tag{10.6}
$$

There is a finite admissible test with Rayleigh quotient below
$\lambda_D$. The bottom $E_g$ is attained by a normalized member of
$D(\widetilde H_g)$ and is an isolated eigenvalue of finite multiplicity.
Every normalized minimizing sequence has a subsequence converging in the
free form norm. Thus the assertion includes absence of mass escape and
concentration loss, while its absolute energy remains positive.

Proof. Use (4.2) globally on the real cover:

$$
\xi=(k-k_o)/\varepsilon,\quad
\eta=2(A-A_o),\quad
\zeta=-r\{B-B_o-c(k_o)\eta\}/\varepsilon.
\tag{10.7}
$$

This maps the cover onto the slab
$D=((l-k_o)/\varepsilon,(u-k_o)/\varepsilon)\times\mathbb R^2$ in
the group (4.5). Equations (4.3) hold globally:
$\varepsilon P=U$, $Q=V$ and
$d\widetilde\mu=j\,d\xi\,d\eta\,d\zeta$, $j=\varepsilon^2/(2r)$.
The form is therefore exactly the constant-density Dirichlet restriction
of $L_H$, with unchanged time, not a tangent approximation.
Integration by parts proves closability as in Proposition 2.1; the
contraction chain rule proves the Markov property. Height Poincaré on
each real phase fiber proves the stated lower bound and passes to closure.

The full-group heat and Green suppliers are [R, §2, (2.1), (2.6)--(2.7)].
Killing that process on exit from $D$, and accounting for $j$, gives

$$
0\le\widetilde p_t(o,q)\le j^{-1}p_t^H(0,(\xi,\eta,\zeta)),
\qquad
0\le\widetilde G_o(q)\le j^{-1}G_H(\xi,\eta,\zeta).
\tag{10.8}
$$

This is domination by earlier killing, with neither a reflection image
formula nor any change to the attractive field. The bracket
$[U,V]=\partial_\zeta$ and connected slab give interior hypoellipticity
and strict heat positivity. In particular horizontal rectangles at
interior heights generate central displacements, and height and $V$ legs
connect all points without crossing a height face. Such finite paths can
be traversed in any prescribed positive time. The usual positive
Hörmander heat setting is [H, §3.1.2]; these fields are smooth, divergence
free, bracket generating of step two, with zero drift and potential.

Choose a proper continuous homogeneous norm $N$ on (4.5).
The supplied smooth degree $-2$ kernel satisfies
$G_H\le C_NN^{-2}$. For example one may use a constant multiple of
$((\xi^2+\eta^2)^2+(2\zeta-\xi\eta)^2)^{1/4}$.
As the two real phases diverge with $\xi$ in this bounded slab,
$N\to\infty$ uniformly. Consequently (10.8) proves the claimed uniform
tail bound and every global off-pole bound, including near the height
faces. It also proves off-pole finiteness and local integrability at the
pole; homogeneous dimension four makes $N^{-2}$ locally integrable.

For the marginal and projection, the exact real process is

$$
dK_t=\sqrt2\varepsilon\,dW_t^1,\qquad
dA_t=2^{-1/2}dW_t^2,\qquad
dB_t=\sqrt2c(K_t)\,dW_t^2,
\quad \tau=\inf\{t:K_t\notin I\}.
\tag{10.9}
$$

The Brownian motions $W^1,W^2$ are independent. The Stratonovich and Itô formulas
agree because $Qk=0$; the generator before killing is
$\varepsilon^2P^2+Q^2$. Wrapping both real phases gives the same unique
killed free diffusion as (6.4), including its lifetime. Integration of
its real kernel over both phases is therefore the height Dirichlet heat
kernel for $\varepsilon^2\partial_k^2$. Tonelli and the one-dimensional
inverse computed in Proposition 6.1 prove (10.4), hence global
integrability. Integration of
$-\partial_t(e^{-t\widetilde L}\varphi)(o)$ proves (10.3): the initial
value is $\varphi(o)$ and the terminal value is zero, since
$\mathbb P_o(\tau>t)\to0$. Absolute interchange follows from (10.4) and
bounded $\widetilde L\varphi$. Spatial hypoellipticity of (10.3) proves
smoothness off $o$. Strict heat positivity proves $\widetilde G_o>0$.
At $o$ the value is infinite: [H, Theorem 3.2] compares the slab and
full-group kernels on an interior compact containing zero with error
$O(t^N)$ for every $N$, whereas $p_t^H(0,0)=t^{-2}p_1^H(0,0)$.
Both realizations here are selfadjoint contractions of the identical
smooth expression and density, as required by that comparison theorem.

Projection of (10.9) also proves the heat equality (10.2) as equality of
densities. It holds pointwise for positive time: the full-group Schwartz
heat bound in (10.8), also for general starting points, makes the lattice
sum locally uniformly convergent; its continuous sum agrees with the
periodic density almost everywhere and hence everywhere. Tonelli gives
the Green equality. Ordinary continuous path lifting with fixed initial
representatives, already used in the supplied full-path correspondence,
is consistent with this law and with (9.3); it adds no Brownian history
to the original numerical command class.

For $f$ in the smooth compact core, zero extension of its image under
(10.7) is a full-group test. Apply exactly (4.8), supplied by
[R, Corollary 3.2], with $p=2$, $\alpha=1$, $Q_{\rm vol}=4$.
The condition $0<1<4/2$ holds. Write $v$ for that zero extension.
Keeping the factor $j$ gives

$$
\widetilde V[f]\le
\int_{\mathbb R^3}G_H|v|^2\,d\xi\,d\eta\,d\zeta
\le j^{-1}C_H\widetilde T[f]=g_*^{-1}\widetilde T[f].
\tag{10.10}
$$

The Hardy estimate is unweighted; no horizontal-gradient factor is
inserted. Apply (10.10) to differences of a free-core sequence. Its
weighted $L^2$ limit agrees almost everywhere with its ordinary $L^2$
limit, so every $f\in\widetilde{\mathcal F}$ has finite potential energy
and (10.10) holds there. [T, Theorem 6.24 (KLMN)] now applies with relative
bound $g/g_*<1$ and additive bound zero. It proves (10.5), closedness and
equivalence of the attractive and free form norms on exactly the same
domain. More explicitly,
$f\in D(\widetilde H_g)$ exactly when $f\in\widetilde{\mathcal F}$ and
$\widetilde q_g(f,v)=\langle F,v\rangle$ for some $F\in L^2$ and all
$v\in\widetilde{\mathcal F}$, and then $\widetilde H_gf=F$.
This is the operator domain used below; no point condition or different
selfadjoint extension at the pole is imposed.

We next verify the local compactness needed for the actual essential
threshold. For any finite-measure set $E\subset\widetilde\Omega$ and
$t>0$, symmetry, the semigroup identity and group domination give

$$
\|{\bf1}_E e^{-t\widetilde L}\|_{\rm HS}^2
=\int_E\widetilde p_{2t}(q,q)\,d\widetilde\mu(q)
\le j^{-1}p_{2t}^H(0,0)\,\widetilde\mu(E)<\infty.
\tag{10.11}
$$

Thus the localized heat operator is compact. Apply
[Lenz--Stollmann--Wingert, Theorem 1.3(iv)--(v)] to the nonnegative
selfadjoint $\widetilde L$ and bounded multiplier $\mathbf1_E$.
Restriction $\widetilde{\mathcal F}\to L^2(E)$ is compact. In particular
this includes $E=I\times\{|s|\le R\}$, where
$s=(A-A_o,B-B_o)$; the statement controls sequences
approaching either height face as well as interior sequences.

Choose smooth phase cutoffs $\chi_R,\vartheta_R$ with
$\chi_R^2+\vartheta_R^2=1$, $\chi_R=1$ for $|s|\le R$,
$\chi_R=0$ for $|s|\ge2R$, and horizontal squared derivative sum at most
$C/R^2$. Such cutoffs are obtained as cosine and sine of a smooth radial
transition; $P\chi_R=P\vartheta_R=0$ and $c(k)$ is bounded on $I$.
Here $\widetilde G_o(k,s)$ abbreviates the field at $(k,A_o+s_1,B_o+s_2)$.
Put $m_R=\sup_{k\in I,\ |s|\ge R}\widetilde G_o(k,s)$, so $m_R\to0$.
The exact IMS identity (4.10), now with real phases and the same potential
on both pieces, together with (10.5), yields

$$
\widetilde q_g[h]\ge
(\lambda_D-gm_R)\|\vartheta_Rh\|_2^2
-CR^{-2}\|h\|_2^2.
\tag{10.12}
$$

The discarded interior form is nonnegative by (10.5), including its
critical singularity. If $h_n$ is free-form bounded, weakly zero in $L^2$,
and $\|h_n\|_2^2\to b$, (10.11) makes $\chi_Rh_n\to0$ strongly for fixed
$R$. Taking the lower limit in (10.12), then $R\to\infty$, proves

$$
\liminf_n\widetilde q_g[h_n]\ge\lambda_Db.
\tag{10.13}
$$

These arguments include $g=0$. If a spectral subspace below
$\lambda_D-\delta$ were infinite dimensional, an orthonormal sequence
in it would be free-form bounded by (10.5), weakly zero, and contradict
(10.13). Hence every such spectral subspace is finite dimensional.

For the opposite essential bound let
$\phi(k)=\sqrt{2/d}\sin(\pi(k-l)/d)$ and take a real normalized
$v\in C_c^\infty(\mathbb R^2)$. Products
$f_R(k,s)=\phi(k)R^{-1}v(s/R)$ belong to
$\widetilde{\mathcal F}$ by height and phase approximation, and satisfy

$$
\|f_R\|_2=1,\qquad
\widetilde T[f_R]=\lambda_D+O(R^{-2}).
\tag{10.14}
$$

Indeed the height contribution is exactly $\lambda_D$ and the remaining
term is $\int_I\phi^2\int|(\tfrac12,c(k))\cdot\nabla(R^{-1}v(s/R))|^2$.
Infinitely many disjoint phase translates of this fixed-size support
have the same free energy. Their span has attractive Rayleigh quotient
at most $\lambda_D+C/R^2$, since $\widetilde q_g\le\widetilde T$ and
all cross forms between disjoint supports vanish. The form version of
[T, Theorem 4.10] gives essential bottom at most this number. Letting
$R\to\infty$, and combining with the preceding finite-dimensional
spectral-subspace conclusion, proves both essential equalities in (10.6).
This uses only local compactness, not compactness of the full critical
Green multiplier or a Persson or extended-Kato premise.

For a finite below-threshold witness fix $a>0$ and $R>a$. Let $v_R(s)$
be one on $|s|\le a$, equal to $\log(R/|s|)/\log(R/a)$ for
$a<|s|<R$, and zero outside. This compactly supported $H^1(\mathbb R^2)$
function has $\int|\nabla v_R|^2=2\pi/\log(R/a)$. Put

$$
M=\int_I\phi(k)^2|(\tfrac12,c(k))|^2\,dk,\qquad
W_a=\int_{I\times\{|s|\le a\}}\phi(k)^2\widetilde G_o\,d\widetilde\mu .
\tag{10.15}
$$

Here $0<W_a<\infty$ by positivity and (10.4), and $M<\infty$.
The same product approximation makes $F_R(k,s)=\phi(k)v_R(s)$
admissible. It has finite nonzero norm, and (10.10) makes its potential
finite. Directly in the original fields,

$$
\widetilde q_g[F_R]-\lambda_D\|F_R\|_2^2
\le \frac{2\pi M}{\log(R/a)}-gW_a<0
\quad\hbox{if }\log(R/a)>\frac{2\pi M}{gW_a}.
\tag{10.16}
$$

Thus a finite $R$ suffices for each fixed $g>0$ in the strict form range.
Core approximation and continuity in the equivalent form norm also give
a smooth compactly supported witness with the same strict inequality.
The logarithmic cutoff is the classical two-dimensional weak-binding
mechanism, used here only after evaluating its energy and admissibility
for the actual native fields and full $\widetilde G_o$.

Finally let $f_n$ be any normalized minimizing sequence for $E_g$.
The lower bound (10.5) gives free-form boundedness; extract a weak
free-form limit $f$. For $h_n=f_n-f$, put $m=\|f\|_2^2\le1$.
Weak convergence and continuity of the polarized forms give

$$
\|h_n\|_2^2\to1-m,\qquad
\widetilde q_g[f_n]=\widetilde q_g[f]+\widetilde q_g[h_n]+o(1).
\tag{10.17}
$$

By (10.13) and the definition of $E_g$,
$E_g\ge E_gm+\lambda_D(1-m)$. Since (10.16) gives $E_g<\lambda_D$,
necessarily $m=1$. Equation (10.17) then gives
$\widetilde q_g[f]=E_g$ and $\widetilde q_g[h_n]\to0$; (10.5) implies
strong convergence in the free form norm. Variation of this minimum
gives $f\in D(\widetilde H_g)$ and $\widetilde H_gf=E_gf$.
The finite-dimensional spectral-subspace conclusion makes this bottom
isolated and of finite multiplicity. The remaining energy bounds are
immediate from (10.5) and height Poincaré. $\square$

## 11. Observation information, suppliers and limits of the increment

**Proposition 11.1 (what the noncompact conclusion observes).** The
covering law and localization of Theorem 10.1 retain the native
current-observation distinction, and add no physical spatial directions
or acquisition procedure.

Proof. Every original present-ray observable pulls back to a
$2\pi\mathbb Z^2$-invariant function. Distinct deck translates therefore
give identical original current observations. A supplied entire continuous
wrapped path and initial representatives determine its unique lift;
for original numerical histories (9.3) computes that lift already.
These assertions require path information, not just its terminal ray.
Neither assertion provides an observer with freely acquired unwrapped
phases. The analytic diffusion (10.9) remains additional stochastic
structure, not an absolutely continuous native command.

A nonzero periodic amplitude cannot belong to $L^2(\widetilde\Omega)$:
its identical nonzero squared mass would repeat over infinitely many
fundamental cells. The attained nonperiodic amplitude is consequently
an analytic state on the added cover, not a prepared five-mode ray or an
original current-ray observable. A single lifted source is also
additional information: its positive field tends to zero at phase
infinity and so is not deck invariant. Only the periodized sum (10.2)
recovers the original torus source. In particular the single-source
attractive operator does not descend as the original periodic attraction.
The free law does descend, with exactly the same killing and clock.

The strict range compares the attractive bottom with its own actual
essential bottom, both for that single full field. It gives positive
absolute energy and a strictly positive gap below $\lambda_D$, without
a sharp coupling, gap asymptotic or estimate uniform as
$\varepsilon\downarrow0$. The state dimension three, two primitive
controls, two lifted phase directions, local homogeneous dimension four
and physical axes remain different quantities. This conclusion supplies
the specified noncompact analytic bridge to §§7.2--7.3; it selects no
means or physical realization and completes no why-three claim.
$\square$

**Mathematical citation 11.2 (scope and exact supplier correspondence).**
The native inputs [N, §§8--9],
[Observation quotient, Definitions 1.1--1.3](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md),
and the guarded-lift source cited in Definition 9.1 are used at immutable
revision $\mathtt{8464cb20c1ef0954d4561a3d5c4855de289c0e5a}$.
They supply the actual torus, arbitrary preparation, numerical histories,
whole-height guards and distinction between current state and path.
Definitions 4.1--4.2 supply the exact fields and normalization; Theorem
5.1 supplies compact-domain stability, not the noncompact conclusion.

| Primary supplier | Applied scope and remaining native work |
| --- | --- |
| [R] Ciatti--Cowling--Ricci, arXiv:1308.2373v1, §2 and Corollary 3.2 | The full-group unit-source heat integral and unweighted Hardy inequality are reused with $U,V$, Haar measure, $Q_{\rm vol}=4$, $p=2,\alpha=1$. The global slab map has density $j$, producing precisely $j^{-1}C_H=2rC_H/\varepsilon^2$. |
| [H] Colin de Verdière--Hillairet--Trélat, DOI 10.5802/ahl.93, §3.1.2 and Theorem 3.2 | Smooth bracket-generating fields, zero drift and potential, identical local density and selfadjoint contraction realizations give the heat setting and local comparison. Domination, integrability and tails here also use the actual global slab and height law. |
| [T] Teschl, 2009 edition, Theorems 6.24 and 4.10 | The verified relative form bound is $g/g_*<1$ with additive bound zero; KLMN preserves precisely $\widetilde{\mathcal F}$. Form min-max is used with the disjoint native product tests after the exterior lower bound is proved. |
| Lenz--Stollmann--Wingert, *Compactness of Schrödinger semigroups*, [arXiv:0903.0280v2](https://arxiv.org/pdf/0903.0280v2), Theorem 1.3 | For bounded $\mathbf1_E$ and nonnegative selfadjoint $\widetilde L$, the verified localized Hilbert--Schmidt heat estimate gives compact restriction of the free form domain. It does not assert compactness of the full Green multiplier. |
| Hoang--Hundertmark--Richter--Vugalter, *Quantitative bounds versus existence of weakly coupled bound states for Schrödinger type operators*, [arXiv:1610.09891v2](https://arxiv.org/pdf/1610.09891v2), Theorem 1.1 and Remarks 1.2 | These are established weak-binding context for scalar Fourier kinetic symbols, with relative form compactness among their hypotheses. Those hypotheses are not imported for the singular native multiplier. The actual height-mode trial and essential-threshold/no-escape estimates are (10.11)--(10.17). |

These literature-attested intermediate facts are not separately proposed
as new general theorems. The repo-derived application is their integrated
same-source noncompact Green/domain/threshold/trial/no-escape
correspondence. It neither substitutes a local singular model for the
full field nor transfers compact-torus attainment. Bounded comparison
with baseline D5, including private declarations, Blueprint, Library and
mathlib revision $\mathtt{db584cd6d46c92f209a44c0f1c829460d327499d}$
did not identify this complete native contract; that comparison is not
an absence proof or a literature-priority claim. All statements here are
ordinary mathematics, without Lean or kernel certification.

## 追加锚（本行以下为增补区）

## 12. A fixed nearby source and its transverse current-ray task

This section retains the native source [N] of Definition 1.1. Its question
is the executed two-control cost of revealing one phase omitted by a
specified observation. The inverse-gap lower mechanism is already
[N, Theorem 3.11 and Proposition 10.2]; the quantitative addition is a
matching full-circle construction with one common finite execution for
variation, length and fixed-time energy. The Green classification in
§§3--7 is a separate, already established result.

**Definition 12.1 (immutable perturbation, actual periods and complete
competitor class).** Fix

$$
0<Z<1,\qquad r=1-Z,\qquad H=r/2,\qquad
I=(l,u),\quad 0<l<k_0<u<H,\qquad T>0,\quad 0<\chi<\pi.
\tag{12.1}
$$

For each sufficiently small real $\kappa$, fix the original source means
$X=Y=H+\kappa$. This parameter is immutable during a history. In the
original mode order $(0,1,2,3,13)$ the probabilities are exactly

$$
p_\kappa(k)=(k-2\kappa,H+\kappa-k,Z,H+\kappa-k,k),
\qquad
J_\kappa=(\max(0,2\kappa),H+\kappa).
\tag{12.2}
$$

For example, $|\kappa|<\min(l/4,(H-u)/2,H/4)$ ensures
$[l,u]\subset J_\kappa$, admissible means and a common positive margin
for all five probabilities. Impose the additional whole-path guard
$k(t)=k_0+a(t)\in I$. Commands $a,b$ start at zero and are the original
finite absolutely continuous or continuous finite piecewise $C^1$ real
profiles on $[0,T]$. They obey, almost everywhere,

$$
dh_s=w_s(k)\,db,\qquad
w_s(k)=\frac{d_s}{p_{\kappa,s}(k)\mathcal I_\kappa(k)},\qquad
\mathcal I_\kappa(k)=\sum_{s\in\{0,1,3,13\}}p_{\kappa,s}(k)^{-1},
\qquad d=(1,-1,0,-1,1)^{\mathsf T}.
\tag{12.3}
$$

Here $h_s(0)=0$ are actual increments relative to arbitrary fixed
preparation phases. Representatives keep the negative convention
$\psi_s=\sqrt{p_{\kappa,s}}e^{-i(\theta_s^{\rm in}+h_s)}$.
The equalities $h_2=0$ and $h_1=h_3=:v$ constrain increments only.
For $\kappa\ne0$, [N, Theorem 8.2] identifies the current leaf as
$(k,[h_0],[h_{13}],[v])$, with independent actual $2\pi$ phase circles.
Declare

$$
q=(k,[h_{13}],[v]),\qquad D=[h_0-h_{13}],\qquad
\delta=h_0-h_{13}\in\mathbb R.
\tag{12.4}
$$

The integer coordinate change
$(h_0,h_{13},v)\mapsto(h_0-h_{13},h_{13},v)$ has determinant one.
Thus $D$ has period $2\pi$, with no relation-angle doubling or finite
quotient. The observation $q$ is declared for this task; it is not the
complete native coherence readout. At $\kappa=0$, $\delta=0$ on every
reachable history and $q$ parametrizes the three-coordinate current leaf.

Let $\mathcal C_\kappa(T,\chi)$ contain **all** profiles just specified
whose endpoints satisfy

$$
a(T)=0,\qquad
h_{13}(T)=2\pi m,\qquad v(T)=2\pi n,\qquad
\delta(T)=\chi+2\pi j,\qquad m,n,j\in\mathbb Z.
\tag{12.5}
$$

There is no bound on winding or finite path complexity and no additional
condition on $b(T)$. All infima below use this same complete class. Define
actual executed costs

$$
\begin{aligned}
\mathsf V(a,b)&=\operatorname{TV}(b)=\int_0^T|\dot b|\,dt,\\
\mathsf L(a,b)&=\int_0^T\sqrt{\dot a^2+\dot b^2}\,dt,\\
\mathsf E(a,b)&=\int_0^T(\dot a^2+\dot b^2)\,dt,
\end{aligned}
\qquad
V_\kappa^\star=\inf_{\mathcal C_\kappa}\mathsf V,\quad
L_\kappa^\star=\inf_{\mathcal C_\kappa}\mathsf L,\quad
E_\kappa^\star=\inf_{\mathcal C_\kappa}\mathsf E.
\tag{12.6}
$$

The identity energy is unhalved and may be infinite for an AC competitor.
It is the declared mathematical command cost of [N, Definition 10.1],
not a calibration of physical energy.

**Calculation 12.2 (native coefficients and prefix charge).** Put
$s_\kappa=H+\kappa$ and $\alpha_\kappa=\kappa s_\kappa/H$. Directly
reducing the original information sum in (12.3) gives

$$
\begin{aligned}
\mathcal I_\kappa(k)
 &=\frac{2H(k-\alpha_\kappa)}{k(k-2\kappa)(s_\kappa-k)},\\
A_\kappa(k):=w_{13}(k)
 &=\frac{(k-2\kappa)(s_\kappa-k)}{2H(k-\alpha_\kappa)},\\
B_\kappa(k):=w_1(k)=w_3(k)
 &=-\frac{k(k-2\kappa)}{2H(k-\alpha_\kappa)},\\
C_\kappa(k):=w_0(k)-w_{13}(k)
 &=\kappa g_\kappa(k),\qquad
 g_\kappa(k)=\frac{s_\kappa-k}{H(k-\alpha_\kappa)}.
\end{aligned}
\tag{12.7}
$$

These functions extend smoothly to $\kappa=0$ on a neighbourhood of
$[l,u]$. In particular

$$
A_0(k)=\frac{H-k}{2H},\qquad B_0(k)=-\frac{k}{2H},\qquad
 g_0(k)=\frac1k-\frac1H.
\tag{12.8}
$$

For every sufficiently small $\kappa$ of either sign, $g_\kappa>0$ and

$$
g_\kappa'(k)=\frac{\alpha_\kappa-s_\kappa}
 {H(k-\alpha_\kappa)^2}<0,\qquad
M_\kappa:=\sup_{k\in I}g_\kappa(k)
 =g_\kappa(l)=\frac{s_\kappa-l}{H(l-\alpha_\kappa)},\qquad
M_0=\frac{H-l}{Hl}.
\tag{12.9}
$$

The endpoint value at $l$ specifies a supremum; the height $l$ itself is
not a legal control height. All these suprema are uniformly bounded for
small $|\kappa|$ because the guard stays strictly inside the probability
fiber.

The source identity $d^{\mathsf T}w=1$ reads
$C_\kappa+2A_\kappa-2B_\kappa=1$. Since all increments start at zero,
every lawful prefix satisfies the real identity

$$
b(t)=\delta(t)+2h_{13}(t)-2v(t).
\tag{12.10}
$$

Consequently (12.5) forces
$b(T)=\chi+2\pi j+4\pi(m-n)$ and $[b(T)]=[\chi]$.
These are closed-visible prefixes of [N, Definition 8.1], not base/phase
loops with $[b(T)]=0$. Adding that loop condition would make this class
empty. The pointwise reciprocal identity underlying [N, Theorem 3.11],
$w_0-w_{13}=(X+Y-r)/(\mathcal I p_0p_{13})$, holds on these prefixes
without any closing condition; (12.7) is its exact specialization with
$X+Y-r=2\kappa$. Thus using it here does not import an unmet loop
hypothesis.

## 13. Sharp joint costs with all winding and travel charged

**Theorem 13.1 (fixed-data transverse exposure envelope).** With all data
in Definition 12.1 fixed, there exist $\kappa_*>0$ and a finite constant
$K$, independent of the sign of $\kappa$, such that for
$0<|\kappa|<\kappa_*$ the class $\mathcal C_\kappa(T,\chi)$ is nonempty.
Set

$$
\mathcal B_\kappa=\frac{\chi}{|\kappa|M_\kappa},\qquad
c=\frac{\chi}{M_0}=\frac{\chi Hl}{H-l}.
\tag{13.1}
$$

The infima over the full class satisfy

$$
\mathcal B_\kappa\le V_\kappa^\star\le L_\kappa^\star
 \le\mathcal B_\kappa+K,\qquad
\frac{\mathcal B_\kappa^2}{T}\le E_\kappa^\star
 \le\frac{(\mathcal B_\kappa+K)^2}{T}.
\tag{13.2}
$$

One family of actual finite profiles in this same class provides every
upper bound jointly, with $\operatorname{TV}(a)\le2(u-l)$. In particular,
as $\kappa\to0$ through either sign,

$$
|\kappa|V_\kappa^\star\longrightarrow c,\qquad
|\kappa|L_\kappa^\star\longrightarrow c,\qquad
\kappa^2E_\kappa^\star\longrightarrow\frac{c^2}{T}.
\tag{13.3}
$$

At $\kappa=0$ the prescribed nonzero-target class is empty. The family
attains the circle targets exactly and saturates the three infima
asymptotically. No assertion of a minimizing optimizer at fixed nonzero
$\kappa$, or of an exact subleading correction to any infimum, is made.

**Proof.** First let $(a,b)$ be any lawful competitor, with any integers
in (12.5). Its real hidden lift obeys

$$
\chi\le|\chi+2\pi j|=|\delta(T)|
 =\left|\kappa\int_0^T g_\kappa(k(t))\dot b(t)\,dt\right|
 \le|\kappa|M_\kappa\mathsf V(a,b).
\tag{13.4}
$$

The first inequality uses $0<\chi<\pi$, and hence covers every hidden
winding. The last one holds for every guarded history, regardless of its
visible windings, signs, reversals or complexity. The coefficients are
bounded on the whole guard, so the weighted integrals are legitimate
for the entire stated regularity class. Pointwise
$|\dot b|\le\sqrt{\dot a^2+\dot b^2}$ and Cauchy--Schwarz give

$$
\mathsf V\le\mathsf L,\qquad \mathsf L^2\le T\mathsf E.
\tag{13.5}
$$

The latter includes infinite energy. This proves all lower bounds in
(13.2), using the existing inverse-gap and norm-comparison mechanism of
[N, §§3.11,10.2], with the exact guarded coefficient $M_\kappa$.
It does not restrict the class to zero real phase lifts.

For the matching construction fix any three distinct heights
$l<z_1<z_2<z_3<u$, independently of $\kappa$, and form the scaled moment
matrix

$$
\mathsf R_\kappa=
\begin{pmatrix}
A_\kappa(z_1)&A_\kappa(z_2)&A_\kappa(z_3)\\
B_\kappa(z_1)&B_\kappa(z_2)&B_\kappa(z_3)\\
g_\kappa(z_1)&g_\kappa(z_2)&g_\kappa(z_3)
\end{pmatrix}.
\tag{13.6}
$$

At $\kappa=0$ its three row functions span $1,k,1/k$ by (12.8).
A linear combination vanishing at $z_1,z_2,z_3$, multiplied by $k$,
is a polynomial of degree at most two with three distinct roots. It is
zero identically. Since $1,k,1/k$ are independent on $I$, the original
combination is zero. Thus $\mathsf R_0$ is invertible. Continuity of
its determinant and adjugate gives, after decreasing $\kappa_*$,

$$
\sup_{|\kappa|<\kappa_*}\|\mathsf R_\kappa^{-1}\|<\infty.
\tag{13.7}
$$

This is a scaled correction matrix, not the four-height determinant of
[N, Theorem 3.10], whose neither-wall assumption fails on $E_+$.

Choose the legal principal-leg height and its real command increment as

$$
y_\kappa=l+\kappa^2,\qquad
\beta_\kappa=\frac{\chi}{\kappa g_\kappa(y_\kappa)}.
\tag{13.8}
$$

Shrink $\kappa_*$ further so that
$l<y_\kappa<\min(k_0,z_1)$. For each fixed nonzero $\kappa$ this is a
finite real increment, with its allowed negative sign when $\kappa<0$.
A phase leg of increment $\beta_\kappa$ at this height produces hidden
lift exactly $\chi$ and visible real increments
$\beta_\kappa A_\kappa(y_\kappa)$ and
$\beta_\kappa B_\kappa(y_\kappa)$.

Choose integers $m_\kappa,n_\kappa$ nearest to these visible increments
divided by $2\pi$, breaking a tie in either way. The wrapped residuals

$$
\begin{aligned}
r_{1,\kappa}&=2\pi m_\kappa-
 \beta_\kappa A_\kappa(y_\kappa),\\
r_{2,\kappa}&=2\pi n_\kappa-
 \beta_\kappa B_\kappa(y_\kappa)
\end{aligned}
\qquad\text{satisfy}\qquad |r_{1,\kappa}|,|r_{2,\kappa}|\le\pi.
\tag{13.9}
$$

Solve the finite real system

$$
\begin{pmatrix}\gamma_{1,\kappa}\\\gamma_{2,\kappa}\\
\gamma_{3,\kappa}\end{pmatrix}
 =\mathsf R_\kappa^{-1}
 \begin{pmatrix}r_{1,\kappa}\\r_{2,\kappa}\\0\end{pmatrix}.
\tag{13.10}
$$

By (13.7) there is a constant $K_1$ such that
$\sum_i|\gamma_{i,\kappa}|\le K_1$ for both small signs.
Executing these three phase increments at the corresponding $z_i$
corrects the visible lifts by exactly $(r_{1,\kappa},r_{2,\kappa})$.
Its hidden increment is exactly
$\kappa\sum_i g_\kappa(z_i)\gamma_{i,\kappa}=0$.
The final hidden lift is therefore $\chi$, while both visible lifts
are actual integer multiples of their original $2\pi$ periods.
Large visible windings are used, rather than discarded. Rounding may be
discontinuous as a function of the immutable parameter $\kappa$; no
continuity in that parameter is required of a lawful individual history.

Execute the following single control polygon, starting at $a=b=0$:
move $k_0$ to $y_\kappa$ at fixed $b$; execute $\beta_\kappa$ there;
move to $z_1$ and execute $\gamma_{1,\kappa}$; move to $z_2$ and execute
$\gamma_{2,\kappa}$; move to $z_3$ and execute $\gamma_{3,\kappa}$;
return to $k_0$ at fixed $b$. Every height move has $db=0$ and hence
adds no phase; every phase move has constant height and the precise
slope (12.3). Convexity of $I$ puts every connecting segment inside
$I$. These are exactly the probability and phase legs of the native
finite-realization supplier [N, Theorem 8.2], with arbitrary preparation
phases restored by translation. No actuator, jump, reset or parameter
motion is introduced. There are at most nine nonzero affine command
legs. The endpoints satisfy (12.5) with $j=0$.

Let $\mathsf V_\kappa^{\rm fam},\mathsf L_\kappa^{\rm fam},
\mathsf E_\kappa^{\rm fam}$ denote this polygon's executed costs.
Because every leg changes only one of $a,b$, literal accounting yields

$$
\begin{aligned}
\mathsf V_\kappa^{\rm fam}
 &=|\beta_\kappa|+\sum_{i=1}^3|\gamma_{i,\kappa}|,\\
\operatorname{TV}(a_\kappa)
 &=(k_0-y_\kappa)+(z_3-y_\kappa)+|z_3-k_0|\\
 &=2\{\max(k_0,z_3)-y_\kappa\}<2(u-l),\\
\mathsf L_\kappa^{\rm fam}
 &=\mathsf V_\kappa^{\rm fam}+\operatorname{TV}(a_\kappa).
\end{aligned}
\tag{13.11}
$$

To execute this very polygon on the prescribed clock, discard only
zero-increment legs. If its remaining leg lengths are $\ell_j>0$, assign
leg $j$ the duration

$$
\tau_j=T\frac{\ell_j}{\mathsf L_\kappa^{\rm fam}}.
\tag{13.12}
$$

All these durations are positive for each nonzero $\kappa$ and sum to
exactly $T$. Traverse each leg affinely in its assigned time. This
changes neither its transport integral nor its variation or length.
The resulting commands are finite continuous piecewise affine numerical
profiles, hence belong to the original regularity class. Each leg has
speed $\mathsf L_\kappa^{\rm fam}/T$, and its unhalved energy is
$\ell_j^2/\tau_j$. Consequently

$$
\mathsf E_\kappa^{\rm fam}
 =\sum_j\frac{\ell_j^2}{\tau_j}
 =\frac{(\mathsf L_\kappa^{\rm fam})^2}{T}.
\tag{13.13}
$$

In particular all intermediate moves and their actual rates are charged.
Their durations may tend to zero as $\kappa\to0$, but none is zero in
any member of this family. There is no instantaneous-pulse execution
and no extra time beyond $T$.

Uniform smoothness and positivity of $g_\kappa$ near $l$ imply

$$
g_\kappa(y_\kappa)=M_\kappa+O(\kappa^2),\qquad
|\beta_\kappa|=\frac{\chi}{|\kappa|M_\kappa}+O(|\kappa|).
\tag{13.14}
$$

The constants depend only on the fixed data and chosen correction
heights. Equations (13.7), (13.11) and (13.14) give
$\mathsf V_\kappa^{\rm fam}\le\mathsf L_\kappa^{\rm fam}
\le\mathcal B_\kappa+K$ with one fixed $K$.
Equation (13.13) supplies the energy upper bound for the same family.
This proves nonemptiness and (13.2). Since $M_\kappa\to M_0>0$,
squeezing gives (13.3), for the family as well as for the three infima.
At $\kappa=0$, (12.7) makes $\delta$ identically zero, proving emptiness
there. Exact target attainment and asymptotic saturation have been
proved; neither an infimum attained at fixed $\kappa$ nor an exact
finite-$\kappa$ correction formula follows from this construction.
$\square$

## 14. Uniform finite resources, native visibility and exact factors

**Proposition 14.1 (uniform hidden-phase suppression).** For every lawful
history under the guard of Definition 12.1, without any endpoint
condition, put
$d_{\mathbb T}([x],0)=\inf_{j\in\mathbb Z}|x-2\pi j|$. Then

$$
\begin{aligned}
\sup_{0\le t\le T}d_{\mathbb T}(D(t),0)
 &\le\min\{\pi,|\kappa|M_\kappa\operatorname{TV}(b)\}\\
 &\le\min\{\pi,|\kappa|M_\kappa\mathsf L\},\\
\sup_{0\le t\le T}d_{\mathbb T}(D(t),0)
 &\le\min\{\pi,|\kappa|M_\kappa\sqrt{T\mathsf E}\}.
\end{aligned}
\tag{14.1}
$$

Thus every fixed variation or length budget suppresses the hidden circle
uniformly as $\kappa\to0$. More generally the same is true for variation
or length $o(|\kappa|^{-1})$, and, at the fixed clock $T$, energy
$o(\kappa^{-2})$. These statements are uniform over all guarded histories
within the indicated resource envelope, not estimates with a separate
history-dependent constant. Two same-preparation histories with the same
retained observation and variation budgets at most $B$ have hidden
circle separation at most
$\min\{\pi,2|\kappa|M_\kappa B\}$.

**Proof.** For every prefix, integrating (12.7) gives
$|\delta(t)|\le|\kappa|M_\kappa\int_0^t|\dot b|$.
Circle distance is at most both $\pi$ and the magnitude of any real lift.
Taking the supremum and using (13.5) proves (14.1).
The constants $M_\kappa$ are uniformly bounded by (12.9).
The two-history assertion follows from the circle triangle inequality.
This proof imposes no endpoint, winding or complexity restriction.
For an arbitrary other finite duration $\tau$, the variation and length
bounds are unchanged and the energy bound uses $\sqrt{\tau\mathsf E}$.
A fixed energy budget alone, with no bounded duration, does not give the
same suppression: stretching the target-attaining polygon to arbitrarily
large duration decreases its energy while leaving its hidden endpoint
unchanged. $\square$

**Interpretation 14.2 (which task is approximated, and which escapes).**
For a fixed source and preparation, the section $D=0$ assigns a current
ray to each $q$: take $[h_0]=[h_{13}]$ and retain the other phases.
It is an actual ray of the nearby leaf by [N, Theorem 8.2]; on the double
wall it is the entire leaf. Compare a guarded history's ray with this
section at its same $q$. In the common middle-fixed gauge their only
different component is mode $0$, and their representative distance is

$$
2\sqrt{p_{\kappa,0}(k)}\left|\sin\frac{\delta}{2}\right|
 \le\sqrt{p_{\kappa,0}(k)}\,d_{\mathbb T}(D,0).
\tag{14.2}
$$

The uniform bound (14.1) therefore gives a precise finite-resolution
meaning to this three-coordinate approximation. It does not assign a
preparation cost to the section or identify it with a separately prepared
$\kappa=0$ source. For two nearby-source rays with the same $q$, the
corresponding bound uses their hidden circle separation. An ideal native
coherence pair involving mode $0$ varies continuously with that same
phase; the other coherence pairs are unchanged.

Theorem 13.1 also specifies the escaped distinction. Compare its endpoint
with the constant history in the same source and preparation. Their
retained observations agree exactly, while only the mode-$0$ phase
circle differs, by $\chi$. Since the positive middle component fixes the
projective gauge, these are different original current rays.
The unchanged doubled-coherence menu of [N, Theorem 8.4], specifically
its $02$ block (8.8), distinguishes them by the Euclidean output distance

$$
\|y_{02}^{\rm fam}-y_{02}^{\rm const}\|
 =4\sqrt{(k_0-2\kappa)Z}\sin(\chi/2)
 \longrightarrow4\sqrt{k_0Z}\sin(\chi/2)>0.
\tag{14.3}
$$

This holds for arbitrary fixed preparation phases with the original
negative convention. It introduces no measurement or phase actuator.
It concerns ideal expectations and supplies no exact finite-shot
acquisition or discrimination guarantee. Exposing this fixed principal
phase requires the inverse-gap variation/length and inverse-squared-gap
fixed-time energy scales of Theorem 13.1; one common actual family
suffices at those scales.

For $q$-only future tasks, however, $q$ is an exact predictive factor at
every fixed $\kappa$. Starting from height $k$ and applying any common
lawful future command $(a_f,b_f)$, its update is precisely

$$
\begin{aligned}
k_f(t)&=k+a_f(t),\\
[h_{13,f}(t)]&=[h_{13}]+\left[\int_0^t
 A_\kappa(k+a_f(s))\,db_f(s)\right],\\
[v_f(t)]&=[v]+\left[\int_0^t
 B_\kappa(k+a_f(s))\,db_f(s)\right].
\end{aligned}
\tag{14.4}
$$

Legality depends only on the height path. Thus equal $q$ gives equal
$q$-responses and equal legal command domains, even when $D$ differs.
The escape (14.3) refutes completeness for the full native readout,
not closure for the declared $q$-only task. Likewise retaining the
controller's circle $[b]$ changes the information comparison: (12.10)
recovers

$$
D=[b]-2[h_{13}]+2[v].
\tag{14.5}
$$

Discarding that record is part of the stated observation task. Neither
its omission nor this reconstruction is a finite-memory-bit theorem or
recovery of the producing control path.

The finite-resource result gives an operational bridge between the
exactly symmetric leaf and nearby-source descriptions at a specified
resolution. It does not reduce the exact nearby current-ray dimension,
or prove that exactly three coordinates are necessary at finite
resolution. Its constants and limits fix $\chi,I,k_0,Z,T$; no uniform
claim as $\chi\downarrow0$, as the guard meets a probability endpoint,
or as the other fixed data vary is included. These are command budgets
in an ideal mathematical source, not physical spatial axes, physical
energy or a rule selecting the means.

**Reuse 14.3 (the all-scale Green boundary).** For every nonzero
$\kappa$ here, $X=Y$ but $X+Y\ne r$: this is exactly the single $E_+$
wall. Definition 1.2 and [N, Theorem 10.3] already give current-ray
dimension $4$, direct rank $2$, growth $(2,3,4)$ and $Q_{\rm vol}=7$.
Theorem 3.1 already makes its point-Green quadratic energy unbounded
below for every positive coupling, under the smooth positive
common-operator hypotheses of Definition 1.3. At $\kappa=0$ the
published strict stability regime is Theorem 5.1: the constant-density
family $A_\varepsilon=\operatorname{diag}(\varepsilon^2,1)$ and
$g=\gamma\varepsilon^2$, with
$0<\gamma<(2rC_H)^{-1}$. Theorem 6.2 supplies its attained-negative
subfamily. This is not a classification of all double-wall coefficients
or couplings.

These are reused all-scale results, not consequences newly proved by
Theorem 13.1. A budget on executed two-control histories is not a spectral
resource restriction on all analytic amplitudes in $L^2(\Omega,\mu)$.
No map from those histories to a restricted analytic test domain has
been supplied. In particular (14.1) neither rules out the concentrating
tests in Theorem 3.1 nor repairs nearby all-scale Green stability.
The operational robustness and exact all-scale nonrobustness have
different quantified objects and coexist without a changed source,
period, guard or analytic clock.

## 15. Exact suppliers, quantitative increment and remaining endpoints

**Mathematical citation 15.1 (native and library overlap).** The native
sources below are used at the immutable published revision
$\mathtt{bb47ab19d04f55319ce314609e191de72a191235}$. [N] is the source
of Definition 1.1 and [L] denotes
[Native guarded lift limits and diffusion selection](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md).
The ordinary results in these volumes are mathematical premises, not
physical certificates or claims of kernel verification for this appendix.

| Supplier | Exact correspondence and retained boundary |
| --- | --- |
| [N, Definitions 3.1, 8.1 and 9.1; Theorems 3.2 and 8.2] | The same means, probabilities, two controls, full-path guard and arbitrary preparations give the actual prefix rays and independent $2\pi$ circles. Exact finite reachability supplies no uniform near-wall cost by itself. The present endpoint closes $q$, without imposing the base/phase-loop closing condition. |
| [N, Theorems 3.10--3.11 and Proposition 10.2] | Reciprocal subtraction, circle-distance lower bounds, conditioning loss, and variation/length/energy comparisons are already supplied. The pointwise subtraction is verified for prefixes in Calculation 12.2. The four-height determinant is not applied on its excluded $E_+$ wall. |
| [FiniteRectangleTransport](https://github.com/the-omega-institute/trureturing/blob/bb47ab19d04f55319ce314609e191de72a191235/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean), `finite_rectangles_realize`, `weight_compatible`, and private `horizontal_leg`, `vertical_leg`, `polygon_admissible`, `rectangle_chain` bodies | Base $(X,Y,Z)$ and mode index $4=13$ reproduce (12.2)--(12.3), affine probability/phase legs and relation charge. The original unit-time rectangle realization, including negative increments, is reused as the leg model. It does not assert (13.3) or a fixed-$T$ optimum. No new Lean or duplicate realization theorem is supplied. |
| [N, Theorem 8.4 and (8.8)] | The original doubled $02$ coherence pair gives (14.3), with positive $Z$, the same preparation, and no added readout or finite-shot claim. |
| [L, Definition 2.1, Proposition 8.1 and Definition 11.2] | The same identity costs charge literal executed segments. For a full leg of increment $(\Delta a,\Delta b)$ and duration $\tau$, variation is $|\Delta b|$, length is $\sqrt{\Delta a^2+\Delta b^2}$ and unhalved energy is $(\Delta a^2+\Delta b^2)/\tau$. This supplies the accounting convention in (13.11)--(13.13), not the present torus-target optimization. |
| Pinned Mathlib revision $\mathtt{db584cd6d46c92f209a44c0f1c829460d327499d}$, [Bochner/Basic](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean) and [Integral/MeanInequalities](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/MeanInequalities.lean) | `norm_integral_le_integral_norm` and Hölder with exponents $2,2$ are the established integral inequalities used in (13.4)--(13.5). Their source availability is not a compiled application or a formal certificate for the ordinary proof. |
| This volume, Definition 1.2, Theorems 3.1, 5.1 and 6.2, Proposition 7.2 and Definition 7.3 | The unchanged single-wall collapse and explicit double-wall stable family are exactly the facts reused in 14.3, with their actual operator conditions and unsettled thresholds. |

**Mathematical citation 15.2 (primary literature and nontransfer).** The
following directly available primary texts identify classical ingredients
and hypotheses that cannot replace the native quantitative proof.

| Primary reference | Supplied framework and exact limit of the correspondence |
| --- | --- |
| Y. de Castro and F. Gamboa, *Exact Reconstruction using Beurling Minimal Extrapolation*, [arXiv:1103.4951v2](https://arxiv.org/pdf/1103.4951v2), p.3, (GME) | Total-variation minimization of a signed measure under finitely many generalized moment constraints is classical. Here $\mu(E)=\int_{\{t:k(t)\in E\}}db(t)$ has $\|\mu\|_{\rm TV}\le\operatorname{TV}(b)$ and moments $(A_\kappa,B_\kappa,\kappa g_\kappa)$. Equality of this relaxed measure cost with executed fuel is not assumed: cancellations and height travel are separate, and (13.11)--(13.13) verify the actual finite witness. No reconstruction or measure-optimizer theorem is imported. |
| F. Jean, *Control of Nonholonomic Systems and Sub-Riemannian Geometry*, [arXiv:1209.4387v2](https://arxiv.org/pdf/1209.4387v2), Theorem 2.2, p.12, and Theorem 3.5/Corollary 3.6, pp.29--30 | Chow reachability and privileged-coordinate Ball--Box estimates give fixed-structure accessibility and local distances. They do not provide a uniform sharp coefficient for a fixed transverse target as this source loses a reachable direction. Native finite synthesis is already supplied by [N]; (13.7) and the executed correction supply the missing uniform bound. |
| G. Antonelli, E. Le Donne and S. Nicolussi Golo, *Lipschitz Carnot--Carathéodory structures and their limits*, [arXiv:2111.06789v1](https://arxiv.org/pdf/2111.06789v1), Definition 1.3 and Theorem 1.4, p.4 | Distance convergence requires an essentially nonholonomic limit structure. On the common four-coordinate ambient leaf the limit fields preserve $D$, so their flow endpoints lie in a codimension-one set and that hypothesis fails. Restricting instead to the three-coordinate limit leaf removes the prescribed transverse target. This theorem therefore supplies no shortcut to (13.3). |
| P. Cannarsa, P. Martinez and J. Vancostenoble, *The cost of controlling strongly degenerate parabolic equations*, [arXiv:1801.01380v1](https://arxiv.org/pdf/1801.01380v1), abstract and §1.1 | Parameter-degenerate controllability costs can have exponential rates for parabolic boundary/distributed controls. Those PDE states, actuators, norms and null targets are not (12.2)--(12.6). The present inverse powers are derived from the native coefficients and cannot be presumed from degeneracy alone. |
| R. Zeier and T. Schulte-Herbrüggen, *Symmetry Principles in Quantum Systems Theory*, [arXiv:1012.5256v3](https://arxiv.org/pdf/1012.5256v3), abstract and §§3,5 | Symmetry constrains Hamiltonian-system controllability. Hamiltonian operations in that framework are not the original probability-phase transport controls. No quantitative actuation-cost or symmetry-breaking theorem is transferred without that missing operation correspondence. |

**Mathematical contribution 15.3 (the uncovered quantitative contract).**
The matched native result is the bounded winding correction preserving
an exact hidden lift, combined with an actual charged height tour and
its fixed-clock execution, yielding the joint sharp limits (13.3).
It is a repository-derived quantitative application. The inverse-gap
floor, finite reachability, original observability, ordinary moment
language and Green classification are reused and are not counted as
new mathematics. Comparison with the cited public and private native
bodies, their Blueprint applications, the pinned library sources and
these primary control references supplies the overlap map above; it
is not a semantic absence proof or a worldwide originality claim.

The result closes the stated fixed-$\chi$, fixed-guard, fixed-clock
asymptotic resource question for both signs, with no restriction of its
full winding class. Existence of fixed-$\kappa$ minimizers, exact
subleading or arithmetic corrections, joint limits with vanishing
$\chi$ or changing guard, acquisition costs, physical calibration and a
map to an analytic spectral resource restriction remain outside the
proved endpoint. No claim of independent priors or model diversity
underwrites the proof. The assertions in §§12--15 are ordinary proofs;
no Lean/kernel status is claimed.

## 追加锚（本行以下为增补区）

## 16. The fixed killed source and its actual transverse circle

**Definition 16.1 (one source law and one lifetime event).** Fix

$$
0<Z<1,\quad r=1-Z,\quad H=r/2,\quad
0<l<k_0<u<H,\quad I=(l,u),\quad
\varepsilon>0,\quad 0<\chi<\pi.
\tag{16.1}
$$

Choose once and for all

$$
0<\bar\kappa<\min\{l/4,(H-u)/2,H/4\}.
\tag{16.2}
$$

For each $|\kappa|\le\bar\kappa$, the means $X=Y=H+\kappa$ are
immutable during the history. Retain precisely (12.2)--(12.4): in original
mode order $(0,1,2,3,13)$,

$$
p_\kappa(k)=(k-2\kappa,H+\kappa-k,Z,H+\kappa-k,k),\qquad
w_s(k)=\frac{d_s}{p_{\kappa,s}(k)\mathcal I_\kappa(k)},\qquad
d=(1,-1,0,-1,1)^{\mathsf T}.
\tag{16.3}
$$

Here $\mathcal I_\kappa=\sum_{s\in\{0,1,3,13\}}p_{\kappa,s}^{-1}$,
with both equal-probability modes retained in the sum.
All five probabilities have a common positive lower bound on
$[-\bar\kappa,\bar\kappa]\times[l,u]$. Each phase has its actual
$2\pi$ period. Fix arbitrary preparation phases and write
$\psi_s(t)=\sqrt{p_{\kappa,s}(K_t)}
e^{-i(\theta_s^{\rm in}+h_s(t))}$, with all increments initially zero.
In particular $h_2=0$ and $h_1=h_3=v$ constrain increments, without
equating preparation phases.

Use Definition 1.3 with the original fields $P=\partial_k$, $Q_\kappa$,
unnormalized angular measure $\rho=1$ and
$A=\operatorname{diag}(\varepsilon^2,1)$. Equivalently, for independent
standard Brownian motions $B^1,B^2$, use the single killed law

$$
\begin{aligned}
K_0&=k_0,& dK_t&=\sqrt2\varepsilon\,dB_t^1,\\
h_s(0)&=0,& dh_s(t)&=\sqrt2 w_s(K_t)\,dB_t^2,\\
\tau_I&=\inf\{t\ge0:K_t\notin I\}.&&
\end{aligned}
\tag{16.4}
$$

The process is alive only for $t<\tau_I$, with Dirichlet killing at
**both** $l$ and $u$. This is the published added analytic model, not a
diffusion supplied by the bare finite-variation transport syntax.
There is no mean actuator or independent phase driver.

Retain the partial current observation and the preparation-relative target

$$
q_t=(K_t,[h_{13}(t)],[v(t)]),\qquad
\delta_t=h_0(t)-h_{13}(t),\qquad D_t=[\delta_t].
\tag{16.5}
$$

Thus $D_t$ subtracts the initial $0$--$13$ phase difference; it is not
the absolute phase difference for an arbitrary preparation. Define

$$
\begin{aligned}
\mathcal A_\kappa(\chi)
 &=\{\exists\,0\le t<\tau_I:
       d_{\mathbb T}(D_t,0)\ge\chi\},\\
P_\kappa(\chi)&=\mathbb P(\mathcal A_\kappa(\chi)).
\end{aligned}
\tag{16.6}
$$

This probability concerns the whole actual lifetime under (16.4).
No survival conditioning, restart or designed control family is used.

**Proposition 16.2 (generator, coefficient and first circle excursion).**
The Itô and Stratonovich versions of (16.4) agree. Their killed generator
is exactly $-L_A=\varepsilon^2P^2+Q_\kappa^2$ on the smooth interior
core, with the boundary and clock of Definition 1.3. Put

$$
\alpha_\kappa=\kappa+\kappa^2/H,\qquad
b_\kappa(k)=\frac{H+\kappa-k}{H(k-\alpha_\kappa)},\qquad
b_0(k)=\frac{H-k}{Hk}.
\tag{16.7}
$$

Then $b_\kappa$ is smooth and strictly positive on the common closed
parameter-height rectangle, and

$$
w_0-w_{13}=\kappa b_\kappa,\qquad
\delta_t=\sqrt2\kappa\int_0^t b_\kappa(K_s)\,dB_s^2.
\tag{16.8}
$$

For $\kappa\ne0$, (16.6) is exactly first hitting of either real level
$\delta=\pm\chi$ before $\tau_I$. At $\kappa=0$ one has $\delta_t=0$
for the entire lifetime, and $P_0(\chi)=0$.

**Proof.** On the single-wall leaf the reduced field is
$Q_\kappa=w_0\partial_{h_0}+w_{13}\partial_{h_{13}}+w_1\partial_v$.
There is one $v$ coordinate, so its coefficient is $w_1$, not $2w_1$.
Both $P$ and $Q_\kappa$ are divergence free for the stated unnormalized
measure. Moreover $Q_\kappa k=0$ and every coefficient depends only on
$k$. Hence the self-corrections $D_PP$ and $D_{Q_\kappa}Q_\kappa$
vanish. The drivers are independent and the covariance diagonal, so
there is no mixed correction. The generator of (16.4) is consequently
$\varepsilon^2P^2+Q_\kappa^2$, with no extra drift. This verifies the
common-operator correspondence, including the factor $\sqrt2$.

Calculation 12.2 gives $w_0-w_{13}=\kappa g_\kappa$ with
$g_\kappa=b_\kappa$ in (16.7). Equivalently, subtracting the two original
reciprocals gives $2\kappa/(\mathcal I_\kappa k(k-2\kappa))$.
The positive information sum and (16.2) ensure that its reduced
denominator has no zero on the closed rectangle. Subtraction of the
two stochastic integrals proves (16.8). The pair $(K,\delta)$ has
interior generator

$$
\varepsilon^2\partial_k^2+
\kappa^2b_\kappa(k)^2\partial_\delta^2.
\tag{16.9}
$$

The integer phase change in (12.4) preserves the actual circle period.
A continuous real lift starting at zero cannot reach circle distance
$\chi<\pi$ without first hitting $+\chi$ or $-\chi$; either first hit
has that circle distance. This proves the event identity, including
all later windings. Equation (16.8) proves the exact zero assertion.
Preparations cancel from increments and do not enter this law. $\square$

## 17. Uniform full-lifetime probability and its spectral rate

**Theorem 17.1 (native killed transverse reliability).** In Definition
16.1 define the regular Dirichlet eigenvalue

$$
\lambda_1(\kappa)=\varepsilon^2
\inf_{0\ne f\in H_0^1(I)}
\frac{\displaystyle\int_I|f'(k)|^2\,dk}
     {\displaystyle\int_I b_\kappa(k)^2|f(k)|^2\,dk}.
\tag{17.1}
$$

It is positive and finite. More explicitly it is the smallest eigenvalue
of

$$
-\varepsilon^2\phi''(k)
 =\lambda b_\kappa(k)^2\phi(k),\qquad \phi(l)=\phi(u)=0.
\tag{17.2}
$$

The following constants specify one uniform pair of bounds. Set

$$
\begin{aligned}
L&=u-l,&
m&=\min_{|\eta|\le\bar\kappa,\,k\in[l,u]} b_\eta(k)>0,&
M&=\max_{|\eta|\le\bar\kappa,\,k\in[l,u]} b_\eta(k)<\infty,\\
c_0&=\frac{\min\{k_0-l,u-k_0\}}{L},&
\Lambda&=\frac{\varepsilon^2\pi^2}{L^2m^2},&
C_0&=\max\left\{e^\Lambda,
 \frac{LM}{\varepsilon\sqrt e}e^{\Lambda/2}\right\}.
\end{aligned}
\tag{17.3}
$$

For every $0<|\kappa|\le\bar\kappa$, through either sign,

$$
0<\frac{c_0}{\cosh(\chi\sqrt{\lambda_1(\kappa)}/|\kappa|)}
\le P_\kappa(\chi)
\le\frac{C_0}{\cosh(\chi\sqrt{\lambda_1(\kappa)}/|\kappa|)},
\qquad P_\kappa(\chi)<1.
\tag{17.4}
$$

To give matching bounds with a fixed limiting exponent, put

$$
\begin{aligned}
B_*&=\max_{|\eta|\le\bar\kappa,\,k\in[l,u]}
       |\partial_\eta\log b_\eta(k)^2|<\infty,\\
J_*&=\tfrac12 B_*\sqrt{\lambda_1(0)}e^{B_*\bar\kappa/2},\\
c_-&=c_0e^{-\chi J_*}>0,\qquad
c_+=2C_0e^{\chi J_*}<\infty.
\end{aligned}
\tag{17.5}
$$

On the same fixed punctured neighborhood,

$$
c_-\exp\left(-\frac{\chi\sqrt{\lambda_1(0)}}{|\kappa|}\right)
\le P_\kappa(\chi)\le
c_+\exp\left(-\frac{\chi\sqrt{\lambda_1(0)}}{|\kappa|}\right).
\tag{17.6}
$$

In particular the sharp scale is $\exp(-\text{constant}/|\kappa|)$ and

$$
\begin{aligned}
\log P_\kappa(\chi)
 &=-\frac{\chi\sqrt{\lambda_1(0)}}{|\kappa|}+O(1),\\
\lim_{\kappa\to0^+}|\kappa|\log P_\kappa(\chi)
 &=\lim_{\kappa\to0^-}|\kappa|\log P_\kappa(\chi)
 =-\chi\sqrt{\lambda_1(0)}.
\end{aligned}
\tag{17.7}
$$

The $O(1)$ is uniform with all data (16.1)--(16.2) fixed: it lies between
$\log c_-$ and $\log c_+$. No asymptotic prefactor, equality of the two
signed probabilities, or uniformity as the other fixed data vary is asserted.

**Proof.** All probability and spectral ingredients used below are
classical; their source correspondence is specified in §19. The application
uses the native coefficient (16.7) and the actual event (16.6).

First condition on the entire height path. Since $B^2$ is independent of
$B^1$, (16.8) is conditionally a centered Gaussian path with covariance
$2\kappa^2\mathscr C_{t\wedge t'}$, where

$$
\mathscr C_t=\int_0^t b_\kappa(K_v)^2\,dv,
\qquad \zeta_\kappa=\mathscr C_{\tau_I}.
\tag{17.8}
$$

Consequently the joint law of height and transverse lift, up to height
death, is exactly the joint law of
$(K_t,\sqrt2\kappa W_{\mathscr C_t})$, where $W$ is a standard Brownian
motion independent of the full height path. This follows by comparing
the conditional Gaussian finite-dimensional distributions and using
continuity. Independence here is proved from the two original drivers;
it is not inferred merely from a martingale time-change theorem.

The original height lifetime is positive and finite almost surely; indeed
$\mathbb E\tau_I=(k_0-l)(u-k_0)/(2\varepsilon^2)$. Also
$m^2\tau_I\le\zeta_\kappa\le M^2\tau_I$. Thus $\mathscr C$ is
continuous and strictly increasing up to death and has finite positive
terminal value. Write

$$
R=\chi/|\kappa|,\qquad
T_R=\inf\{s\ge0:|\sqrt2 W_s|=R\},\qquad
S_\kappa(s;k)=\mathbb P_k(\zeta_\kappa>s).
\tag{17.9}
$$

Proposition 16.2 and the conditional path identity give the exact
full-lifetime formula

$$
P_\kappa(\chi)=\mathbb P(T_R<\zeta_\kappa)
             =\mathbb E[S_\kappa(T_R;k_0)].
\tag{17.10}
$$

This is an equality for the original event, not a survival-conditioned
law. Equality of the two exit times has probability zero: $T_R$ is
atomless and independent of $\zeta_\kappa$. The strict lifetime convention
therefore also agrees with the usual strip exit convention.

For calculating $S_\kappa$, invert $\mathscr C$ before its terminal
value. The time-changed height has generator
$\varepsilon^2b_\kappa^{-2}\partial_k^2$, killed at both endpoints of
$I$. Its positive Dirichlet operator $\mathscr H_\kappa$ is selfadjoint
in the auxiliary space $L^2(I,b_\kappa^2dk)$, with form

$$
\mathfrak h_\kappa[f]=\varepsilon^2\int_I|f'|^2\,dk,
\qquad D(\mathfrak h_\kappa)=H_0^1(I),\qquad
S_\kappa(s;\cdot)=e^{-s\mathscr H_\kappa}1.
\tag{17.11}
$$

For example, the generator follows by applying the original height
martingale problem and $dt=ds/b_\kappa(K_t)^2$ before death. Integration
by parts gives the displayed form and (17.2). Smooth positive bounded
$b_\kappa$ makes this a regular weighted Sturm--Liouville problem.
Its form has compact embedding and positive first eigenvalue. The
one-dimensional Dirichlet Poincaré inequality and a sine test give

$$
\frac{\varepsilon^2\pi^2}{L^2M^2}
\le\lambda_1(\kappa)\le\Lambda.
\tag{17.12}
$$

This auxiliary time and speed measure are only variables in an exact
calculation of (17.10). The source still uses analytic time $t$, density
$\rho=1$, covariance $2A\,dt$, actual phase periods and the original
height killing. No angular normalization or new clock is installed in it.

We next bound the *unconditioned* survival function for every $s\ge0$.
Let $\phi_\kappa$ be the positive first eigenfunction, normalized by
$\max_{[l,u]}\phi_\kappa=1$. Its equation makes it concave. The chords
from a maximum to the two zero endpoints imply
$\phi_\kappa(k_0)\ge c_0$. Positivity preservation and $1\ge\phi_\kappa$
therefore give

$$
S_\kappa(s;k_0)\ge
e^{-s\lambda_1(\kappa)}\phi_\kappa(k_0)
\ge c_0e^{-s\lambda_1(\kappa)}.
\tag{17.13}
$$

For a uniform upper bound, let $\|\cdot\|_\kappa$ be the norm in
$L^2(I,b_\kappa^2dk)$. For $f\in H_0^1(I)$,
$|f(k_0)|\le\sqrt L\|f'\|_{L^2(dk)}$. The spectral theorem and
$\sup_{x\ge0}\sqrt{x}e^{-x/2}=e^{-1/2}$ give

$$
|(e^{-\mathscr H_\kappa/2}g)(k_0)|
\le\frac{\sqrt L}{\varepsilon}
 \|\mathscr H_\kappa^{1/2}e^{-\mathscr H_\kappa/2}g\|_\kappa
\le\frac{\sqrt L}{\varepsilon\sqrt e}\|g\|_\kappa.
\tag{17.14}
$$

For $s\ge1$, apply (17.14) to
$g=e^{-(s-1/2)\mathscr H_\kappa}1$, use
$\|1\|_\kappa\le M\sqrt L$ and (17.12), and obtain
$S_\kappa(s;k_0)\le
(LM/(\varepsilon\sqrt e))e^{\Lambda/2}e^{-s\lambda_1(\kappa)}$.
For $0\le s\le1$, the bound $S_\kappa\le1$ gives the other constant
in (17.3). Together with (17.13), this proves the uniform, all-time estimate

$$
c_0e^{-s\lambda_1(\kappa)}\le S_\kappa(s;k_0)
\le C_0e^{-s\lambda_1(\kappa)},\qquad s\ge0.
\tag{17.15}
$$

It remains to integrate against the actual independent exit time in
(17.10). The classical Brownian interval-exit Laplace transform, with
generator $\partial_y^2$ rather than $\tfrac12\partial_y^2$, is

$$
\mathbb E[e^{-\lambda T_R}]
 =\frac1{\cosh(R\sqrt\lambda)},\qquad \lambda>0.
\tag{17.16}
$$

For completeness its boundary function is
$F(y)=\cosh(\sqrt\lambda y)/\cosh(\sqrt\lambda R)$: it solves
$F''=\lambda F$ and $F(\pm R)=1$. Applying Itô's formula to
$e^{-\lambda(s\wedge T_R)}F(\sqrt2W_{s\wedge T_R})$ and taking
$s\to\infty$ proves (17.16) by bounded convergence. This also fixes
every factor in its exponent. Substitution of (17.15) into (17.10)
now proves (17.4). In particular $P_\kappa>0$. For every $s>0$,
$S_\kappa(s;k_0)<1$, since $\zeta_\kappa\le M^2\tau_I$ and the
original Brownian height has positive probability to exit by $s/M^2$.
As $T_R>0$ almost surely, (17.10) proves $P_\kappa<1$ too.

Finally smoothness in (16.7) gives, pointwise on $[l,u]$,

$$
e^{-B_*|\kappa|}b_0^2\le b_\kappa^2\le e^{B_*|\kappa|}b_0^2.
\tag{17.17}
$$

Applying the same two inequalities to every denominator in (17.1) yields
$e^{-B_*|\kappa|}\lambda_1(0)\le\lambda_1(\kappa)
\le e^{B_*|\kappa|}\lambda_1(0)$, and hence

$$
|\sqrt{\lambda_1(\kappa)}-\sqrt{\lambda_1(0)}|
\le J_*|\kappa|.
\tag{17.18}
$$

Use $e^{-x}\le1/\cosh x\le2e^{-x}$ for $x\ge0$ in (17.4), then
(17.18), to obtain exactly (17.5)--(17.6). Taking logarithms proves
(17.7). No eigenfunction-series remainder or prefactor expansion is
assumed. $\square$

**Specification 17.2 (the limiting scalar problem).** In particular

$$
\lambda_1(0)=\varepsilon^2
\inf_{0\ne f\in H_0^1(I)}
\frac{\int_I|f'|^2\,dk}
 {\int_I ((H-k)/(Hk))^2|f|^2\,dk}.
\tag{17.19}
$$

Equivalently, solve
$-\varepsilon^2F_\lambda''=\lambda((H-k)/(Hk))^2F_\lambda$ with
$F_\lambda(l)=0$, $F_\lambda'(l)=1$; $\lambda_1(0)$ is the smallest
positive root of $F_\lambda(u)=0$. Regular Dirichlet oscillation theory
gives this equivalence. The exponent depends on the whole fixed interval
and this weight, not just its maximum at $l$. The initial height enters
the matching constants, while the leading rate is the same for every
fixed interior $k_0$. The dependence on $\varepsilon$ is explicit:
$\sqrt{\lambda_1(0)}$ is $\varepsilon$ times the square root of the
quotient infimum without $\varepsilon^2$.

## 18. The same-history coherence task and the separate Green boundary

**Proposition 18.1 (what the rare excursion measures).** At every alive
time compare the actual ray with the section $\sigma_\kappa(q_t)$ of
Interpretation 14.2, in the *same* nearby source and preparation. This
section replaces $[h_0]$ by $[h_{13}]$, retaining $K,[h_{13}],[v]$ and
each component's own preparation phase. Write $y_{02}(t)$ and
$y_{02}^{\sigma}(t)$ for their original doubled $02$ coherence pairs.
Then

$$
\begin{aligned}
\|\psi(t)-\psi^{\sigma}(t)\|
 &=2\sqrt{K_t-2\kappa}\,|\sin(\delta_t/2)|,\\
\|y_{02}(t)-y_{02}^{\sigma}(t)\|
 &=4\sqrt{(K_t-2\kappa)Z}\,|\sin(\delta_t/2)|.
\end{aligned}
\tag{18.1}
$$

The first equality uses the common middle-fixed representative gauge.
In particular the lifetime event is exactly

$$
\mathcal A_\kappa(\chi)=
\left\{\exists t<\tau_I:
\frac{\|y_{02}(t)-y_{02}^{\sigma}(t)\|}
 {4\sqrt{(K_t-2\kappa)Z}}\ge\sin(\chi/2)\right\}.
\tag{18.2}
$$

On this event its first excursion time has output separation at least
$4\sqrt{(l-2\bar\kappa)Z}\sin(\chi/2)>0$, independently of the sign
and size of nonzero $\kappa$ in (16.2). On its complement the section
approximates the actual representative and this coherence pair throughout
the entire lifetime, with respective upper bounds
$2\sqrt{u+2\bar\kappa}\sin(\chi/2)$ and
$4\sqrt{(u+2\bar\kappa)Z}\sin(\chi/2)$.
The probability of the exceptional event is exactly Theorem 17.1.

Current $q$ and its complete ideal continuous history have different
information. In fact, if the latter is supplied, let $H_{13}(t)$ be the
unique continuous real lift of its $[h_{13}(t)]$ path starting at zero.
For the law (16.4), almost surely,

$$
\delta_t=\int_0^t\frac{2\kappa}{K_s-2\kappa}\,dH_{13}(s),
\qquad t<\tau_I.
\tag{18.3}
$$

Thus hidden here means omitted by the specified *current* observation;
it does not mean unrecoverable from a complete ideal $q$-history.

**Proof.** Only the mode-$0$ component changes in the section comparison.
Subtract its two complex amplitudes to obtain the first equality in
(18.1). The original output (8.8) of [N, Theorem 8.4] has radius
$2\sqrt{(K_t-2\kappa)Z}$ and angles differing by $\delta_t$; chord
length gives the second equality for every fixed preparation. Since
$|\sin(\delta/2)|=\sin(d_{\mathbb T}([\delta],0)/2)$ and this last
sine is increasing on $[0,\pi]$, (18.2) follows. Continuity and the
uniform positive height margins give the stated bounds. This comparison
neither samples a second independent history nor prepares a symmetric
source; it evaluates the section at the actual history's current $q$.

For (18.3), Calculation 12.2 gives the exact ratio

$$
\frac{w_0(k)-w_{13}(k)}{w_{13}(k)}
 =\frac{2\kappa}{k-2\kappa}.
\tag{18.4}
$$

The denominator and $w_{13}$ are bounded away from zero on the closed
rectangle. Associativity of stochastic integrals in (16.4) proves
(18.3). Also $[K,H_{13}]=0$, so Itô and Stratonovich readings of this
integral agree. Left-point stochastic sums along deterministic refining
partitions converge locally uniformly in probability before death.
A subsequence, chosen on a countable exhaustion by bounded stopped
intervals, gives one almost-sure continuous version for all $t<\tau_I$.
This is a measurable reconstruction from the ideal continuous observed
paths, not ordinary finite-variation integration.

The section comparison uses ideal expectations of an unchanged native
coherence consumer. Neither (18.2) nor (18.3) supplies sensing, retention,
sampling precision, finite-shot discrimination or decoding costs. No
complete history or additional observation is granted by declaring
current $q$. The result is a probability of one specified transverse
approximation error, not a quotient error bound for every task or future
operation. Brownian drivers are almost surely not the finite-variation
commands of Definition 12.1; their deterministic inverse-gap cost bounds
are not probabilities or finite execution costs for (16.4). $\square$

**Reuse 18.2 (current dimension and all-scale instability).** For every
nonzero $\kappa$ in (16.2), the fixed means lie on $E_+$ only.
Definition 1.2, [N, Theorem 10.3] and Theorem 3.1 therefore give exactly
current-ray dimension $4$, direct rank $2$, growth $(2,3,4)$,
$Q_{\rm vol}=7$, and point-Green form unboundedness below for every
positive coupling, for the very same positive smooth common operator.
At $\kappa=0$ both walls hold: the leaf has three current coordinates,
growth $(2,3)$ and $Q_{\rm vol}=4$. For its constant-density diagonal
family, Theorem 5.1 supplies the explicitly strict stable window

$$
g=\gamma\varepsilon^2,\qquad
0<\gamma<(2rC_H)^{-1},\qquad \varepsilon>0,
\tag{18.5}
$$

where $C_H$ is the positive finite unweighted Heisenberg Green--Hardy
constant in (4.8). This means a closed semibounded form with the original
form domain; it does not assert a sharp threshold or settle its equality
case. Theorem 6.2 supplies the separately stated attained-negative family.

These assertions are reused, as in 14.3. The exponentially small
$P_\kappa(\chi)$ concerns histories of a free killed process. Theorem 3.1
quantifies over all analytic form tests on its cylinder. There is no
supplied map restricting those tests by a path-excursion probability.
Hence (17.6) neither removes the concentrating tests nor repairs nearby
all-scale Green instability. Exact invariance at $\kappa=0$ and a small
positive excursion probability at $\kappa\ne0$ also do not change the
exact current-ray dimension, select the means, or identify physical axes.

## 19. Exact mathematical suppliers and the native probability increment

**Mathematical citation 19.1 (source and classical correspondence).**
[N] and [L] have the immutable source meanings specified in 15.1.
Definitions 1.3 and 4.1, Theorems 3.1, 5.1 and 6.2, and §§12--15 are
used with their displayed assumptions. The following table distinguishes
the classical ingredients from their native application.

| Supplier | Exact input and scope of reuse |
| --- | --- |
| [N, Definitions 2.1, 3.1 and 8.1; Theorem 8.2]; this volume, Definition 12.1 and Calculation 12.2 | Fixed means, probabilities, negative amplitudes, arbitrary preparations, actual phase torus and the exact subtraction $w_0-w_{13}=\kappa b_\kappa$ are reused. Exact reachability and the inverse-gap cost theorems do not supply a random lifetime probability. |
| [N, Definition 10.6 and Theorem 10.7]; this volume, Definition 1.3 and (6.4)--(6.5) | The added closed operator uses unnormalized density, covariance $2A\,dt$, one analytic clock, periodic actual phases and two absorbing height faces. Equation (16.4) specializes that framework; Proposition 16.2 verifies its zero correction for the nearby fields. No diffusion is derived from bare FIB syntax. |
| [L, §§4,6--7] | Guarded lift limits, lifetime continuity and explicitly selected diffusion laws distinguish finite executed controls from a Brownian reference law. They justify keeping law selection explicit; their finite-horizon convergence statements are not substituted for (17.10). |
| P. Mörters and Y. Peres, *Brownian Motion*, [author text](https://www.stat.berkeley.edu/~aldous/205B/bmbook.pdf), §7.1 and §7.4, Theorems 7.42--7.43 and (4.3) | Stochastic integration, the killed heat representation and two-sided interval survival are literature-attested. Their standard Brownian generator is $\tfrac12\partial^2$; the transverse process here is $\sqrt2W$, with generator $\partial^2$. The interval is $(-R,R)$ with two absorbing endpoints. Its classical exit transform is (17.16), verified at this normalization within the native proof. Interval exit and separation of variables do not specify the native weight or an independent random lifetime by themselves. |
| G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, [author text](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf), §§5.3--5.5, Theorem 5.11 and Rayleigh--Ritz formula (5.76) | His regular expression $r^{-1}(-(pf')'+qf)$ is used with coefficient $p=\varepsilon^2$, potential $q=0$, weight $r=b_\kappa^2$ and Dirichlet conditions at $l,u$. These $p,q,r$ are Sturm--Liouville coefficients, not the native probabilities, retained observation or $1-Z$. This supplies the discrete spectrum, first eigenfunction and quotient (17.1). The auxiliary weighted measure is not a change of source density. |
| Conditional Gaussian stochastic integrals; positive killed semigroups; the selfadjoint spectral theorem | These are literature-attested tools within the proof of Theorem 17.1, not additional general results of this volume. The conditional covariance and independence needed for the random lifetime are verified after (17.8); (17.13)--(17.15) supply the explicit uniform survival bounds, without conditioning on survival or using separately optimized marginals. |
| [N, Theorem 8.4, (8.8)]; this volume, Interpretation 14.2 | The original doubled $02$ coherence pair gives (18.1)--(18.2) on the same history and preparation. Its use as an ideal mathematical consumer adds no measurement channel or acquisition theorem. |
| This volume, Definition 1.2, Theorems 3.1 and 5.1, Reuse 14.3 | The single-wall collapse and strict double-wall window are reused with their actual operator hypotheses. They are not consequences of the small probability or classifications of physical space. |

The repository's discrete first-passage/reflection application
[PaddedTail](https://github.com/the-omega-institute/trureturing/blob/67f8765551564da4e4693e16708b84ca2aa882fd/D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail.lean),
`padded_increment_tail`, has a discrete Gaussian terminal variable and
supplied first-passage inequalities. It is not an exact continuous strip
exit theorem with the joint lifetime (17.8). The public and private
finite-rectangle bodies cited in 15.1 supply deterministic transport,
not this killed probability law. Neither application is duplicated here.

The pinned Mathlib source
$\mathtt{db584cd6d46c92f209a44c0f1c829460d327499d}$,
[BrownianMotion/Basic](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/BrownianMotion/Basic.lean),
supplies Brownian-process definitions and Gaussian/independence properties;
[Process/HittingTime](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Process/HittingTime.lean)
supplies discrete stopping-time results. The third-party
[RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion/tree/0d5b6eb928e616d3b1f774ad7d233c167d9f42c9)
at the displayed immutable revision supplies Brownian and Gaussian
infrastructure. None of these identified declarations supplies the exact
weighted, killed native application (16.6)--(17.7). This source-scope
comparison is not a semantic absence proof for other declarations or
literature, and no Lean application or kernel status is claimed.

**Mathematical contribution 19.2 (application and retained boundaries).**
The repository-derived increment is the native full-lifetime conclusion
(17.4)--(17.7), with its exact coefficient and weight (16.7), (17.19),
both-sign uniform constants, and the same-source consumer (18.2).
It applies classical strip exit, Gaussian time change and regular
Sturm--Liouville analysis; it does not claim any of those general tools
as new. The necessary bridge preserves the original joint law, verifies
the drift and clock, reduces the actual circle event before death, and
controls the parameter-dependent rate uniformly. A deterministic
inverse-gap cost, local heat exponent or finite-horizon estimate alone
omits that bridge. The source correspondences above delimit the
application without asserting worldwide originality or independent priors.

Every probability in Theorem 17.1 is under the one specified killed
source. Its high-probability three-coordinate approximation is relative
to the section and the prescribed transverse resolution, over that
finite random lifetime. It supplies no all-target factor theorem,
physical stochastic realization, mean-selection rule, paid sensing or
decoder, finite numerical recovery guarantee, or repair of all-scale
analytic instability. A sharper prefactor or a joint limit changing
$\chi,I,k_0,Z,\varepsilon$ would require additional uniform estimates.
The assertions here are ordinary mathematical proofs.

## 追加锚（本行以下为增补区）


## 20. Positive-time regularization of the fixed native point field

**Definition 20.1 (original data and the one changed interaction).**
Fix the data of (16.1)--(16.2), in particular

$$
0<Z<1,\qquad H=(1-Z)/2,\qquad
0<l<k_0<u<H,\qquad \varepsilon>0,\qquad \tau>0.
\tag{20.1}
$$

Both $\varepsilon$ and the regularization time $\tau$ are fixed. The latter
is measured in the original clock of Definition 1.3. For either sign of
sufficiently small nonzero $\kappa$, retain exactly

$$
\begin{gathered}
X=Y=H+\kappa,\qquad
p_\kappa(k)=(k-2\kappa,H+\kappa-k,Z,H+\kappa-k,k),\\
d=(1,-1,0,-1,1),\qquad
\mathcal I_\kappa(k)=\sum_{s\in\{0,1,3,13\}}p_{\kappa,s}(k)^{-1},
\qquad w_s=d_s/(p_{\kappa,s}\mathcal I_\kappa).
\end{gathered}
\tag{20.2}
$$

The preparation is arbitrary and immutable. With increments $h_2=0$,
$h_1=h_3=v$, the representatives are still
$\psi_s=\sqrt{p_{\kappa,s}}e^{-i(\theta_s^{\rm in}+h_s)}$.
Set $\theta=h_{13}$ and $D=h_0-h_{13}$ modulo $2\pi$.
The integer phase change in Definition 12.1 is unimodular. Thus

$$
\Omega_\kappa=I\times\mathbb T_\theta\times\mathbb T_v\times\mathbb T_D,
\quad I=(l,u),\quad
 d\mu=dk\,d\theta\,dv\,dD,\quad o=(k_0,0,0,0),
\tag{20.3}
$$

with the actual $2\pi$ period in every circle and density one. Use
$A_\kappa,B_\kappa$ of (12.7) and $b_\kappa$ of (16.7). The original
controls and the complete free form are

$$
\begin{aligned}
P&=\partial_k,&
Q_\kappa&=A_\kappa(k)\partial_\theta+
 B_\kappa(k)\partial_v+\kappa b_\kappa(k)\partial_D,\\
T_\kappa[f]&=\int_{\Omega_\kappa}
  (\varepsilon^2|Pf|^2+|Q_\kappa f|^2)\,d\mu,&
\mathcal F_\kappa&=
 \overline{C_c^\infty(\Omega_\kappa)}^{(\|\cdot\|_2^2+T_\kappa)^{1/2}}.
\end{aligned}
\tag{20.4}
$$

There is one $v$ coordinate, with coefficient $B_\kappa$, not twice that
coefficient. Let $L_\kappa$ be the free Friedrichs operator of this form.
The height faces are Dirichlet, the phases periodic, the covariance is
$\operatorname{diag}(\varepsilon^2,1)$, and the semigroup is
$e^{-tL_\kappa}$. In particular its diffusion covariance is twice this
matrix times $dt$. Write $p_\kappa(t,x,y)$ for its kernel relative to
$d\mu$ and $\Gamma_{\kappa,o}$ for the original unit point Green field.
Explicitly change the interaction field to

$$
\begin{aligned}
V_{\kappa,\tau}(y)&=\int_\tau^\infty p_\kappa(t,o,y)\,dt,\\
\sigma_{\kappa,\tau}(y)&=p_\kappa(\tau,o,y),\\
\mathfrak q_{\kappa,\tau,g}[f]&=
 T_\kappa[f]-g\int_{\Omega_\kappa}V_{\kappa,\tau}|f|^2\,d\mu,
\qquad
E_{\kappa,\tau}(g)=
 \inf_{\substack{f\in\mathcal F_\kappa\\\|f\|_2=1}}
 \mathfrak q_{\kappa,\tau,g}[f].
\end{aligned}
\tag{20.5}
$$

The last two expressions are used as closed attractive forms and finite
energies only after the boundedness assertion below. This is a free-heat
regularization of the interaction, not the unchanged point-source
multiplier, a different kinetic operator, or a rescaling of its clock.

**Theorem 20.2 (effective source, killed charge and fixed-parameter
minimum).** For every fixed admissible nonzero $\kappa$, the field in
(20.5) is bounded, strictly positive and smooth in the interior, belongs
to $D(L_\kappa)$, and satisfies

$$
V_{\kappa,\tau}=e^{-\tau L_\kappa}\Gamma_{\kappa,o}
 =L_\kappa^{-1}\sigma_{\kappa,\tau},\qquad
L_\kappa V_{\kappa,\tau}=\sigma_{\kappa,\tau}.
\tag{20.6}
$$

The first semigroup action can be interpreted in $L^1$.
Let $\zeta$ be the exit time of
$K_t=k_0+\sqrt2\varepsilon B_t^1$ from $I$, and put
$S(t)=\mathbb P_{k_0}(\zeta>t)$. Then

$$
\begin{aligned}
\int\sigma_{\kappa,\tau}\,d\mu&=S(\tau)\in(0,1),\\
\int V_{\kappa,\tau}\,d\mu&=
 \int_\tau^\infty S(t)\,dt=\mathbb E_{k_0}(\zeta-\tau)_+,\\
0<\int V_{\kappa,\tau}\,d\mu&<
 \mathbb E_{k_0}\zeta=
 \frac{(k_0-l)(u-k_0)}{2\varepsilon^2}.
\end{aligned}
\tag{20.7}
$$

These quantities are independent of $\kappa$. The effective source has
surviving charge $S(\tau)$; the field mass in the second line is a
remaining-lifetime integral, not that charge.

For every fixed $g>0$, (20.5) is a closed semibounded form on exactly
$\mathcal F_\kappa$. Its operator is

$$
H_{\kappa,\tau,g}=L_\kappa-gM_{V_{\kappa,\tau}},\qquad
D(H_{\kappa,\tau,g})=D(L_\kappa).
\tag{20.8}
$$

It has compact resolvent, and its finite bottom $E_{\kappa,\tau}(g)$
is attained by a normalized member of this operator domain. The completed
form domain is the horizontal domain (20.4), with zero height trace;
no ordinary isotropic $H^1_0$ identification or pole boundary condition
is imposed.

Proof. Propositions 2.1--2.2 already supply the free operator, its smooth
positive kernel, compact free form embedding and integrable unit-source
Green field. Their height estimate gives the parameter-independent gap

$$
T_\kappa[f]\ge\lambda_D\|f\|_2^2,
\qquad \lambda_D=\frac{\varepsilon^2\pi^2}{(u-l)^2}.
\tag{20.9}
$$

To obtain a bound before invoking any attractive operator, use precisely
the larger interior height cylinder of Proposition 2.1. At every fixed
positive $a$, its smooth free kernel bounds the original diagonal
$p_\kappa(a,y,y)$ uniformly for $y\in\Omega_\kappa$. With
$\delta=\tau/4$, the semigroup identity, symmetry and the free spectral
gap imply, for $t\ge\tau$,

$$
p_\kappa(t,o,y)\le
 e^{-\lambda_D(t-2\delta)}
 \sqrt{p_\kappa(2\delta,o,o)p_\kappa(2\delta,y,y)}.
\tag{20.10}
$$

Integrating proves boundedness of $V_{\kappa,\tau}$. Constants at this
stage may depend on $\kappa$. The same argument bounds
$\sigma_{\kappa,\tau}$; finite volume makes it an $L^2$ function.
The free spectral theorem now gives
$\int_\tau^\infty e^{-tL_\kappa}\delta_o\,dt
=L_\kappa^{-1}\sigma_{\kappa,\tau}$ in $L^2$, with the initial point row
first smoothed at $\tau$. More explicitly,
$\sigma_{\kappa,t}=e^{-(t-\tau)L_\kappa}\sigma_{\kappa,\tau}$ for
$t\ge\tau$, and its $L^2$ integral equals the same inverse.
This proves membership in $D(L_\kappa)$ and the second identity (20.6).
Tonelli, symmetry and the free semigroup law applied to the nonnegative
$L^1$ field $\Gamma_{\kappa,o}$ give the first identity. Interior
hypoellipticity and the smooth right side give smoothness; heat positivity
gives strict positivity. Equivalently, for every compactly supported
smooth $\varphi$,

$$
\int V_{\kappa,\tau}L_\kappa\varphi\,d\mu
 =\int\sigma_{\kappa,\tau}\varphi\,d\mu
 =(e^{-\tau L_\kappa}\varphi)(o).
\tag{20.11}
$$

The free process has exactly the height component in the statement,
by Proposition 16.2. Its death therefore depends only on $K$.
Integrating its kernel gives $S(t)$, and Tonelli proves (20.7).
A one-dimensional Brownian motion starting in the interior has positive
probability both to survive and to exit by each fixed positive time;
hence $0<S(\tau)<1$. The expected exit time is the solution of
$-\varepsilon^2m''=1$, $m(l)=m(u)=0$, namely
$m(k)=(k-l)(u-k)/(2\varepsilon^2)$. Strict positivity of $S(t)$ and of
$\int_0^\tau S(t)dt$ proves the strict field-mass inequalities.

Bounded multiplication has relative form bound zero. The bounded case
of the classical KLMN theorem, [T, Theorem 6.24], applies only now, with
additive constant $g\|V_{\kappa,\tau}\|_\infty$. It leaves the form
domain unchanged and yields
$\mathfrak q_{\kappa,\tau,g}\ge
\lambda_D-g\|V_{\kappa,\tau}\|_\infty$ on its unit sphere.
Bounded selfadjoint perturbation gives (20.8). Adding a sufficiently
large multiple of the squared norm makes its form norm equivalent to
the free form norm. The compact free embedding from Proposition 2.1
therefore proves compact resolvent and attainment, either by the direct
method on a minimizing sequence or the selfadjoint compact-resolvent
spectral theorem. The $P$ part controls the height $H^1$ norm with values
in angular $L^2$; closure of the compact height core gives zero traces
at both faces. These arguments use only the free semigroup until the
bounded multiplier has been proved. $\square$

## 21. Resolving the shrinking hidden phase without changing the clock

**Definition 21.1 (comparison cover and exact Hilbert factors).** For
$\kappa\ne0$, put

$$
a=|\kappa|,\qquad \ell_\kappa=2\pi/a,\qquad
x=D/\kappa,\qquad
\nu=dk\,d\theta\,dv\,dx.
\tag{21.1}
$$

The rescaled circle has period $\ell_\kappa$, also when $\kappa<0$.
On $I\times\mathbb T^2\times\mathbb R$ define the auxiliary free fields

$$
\widetilde P=\partial_k,\qquad
\widetilde Q_\kappa=
 A_\kappa(k)\partial_\theta+B_\kappa(k)\partial_v+
 b_\kappa(k)\partial_x.
\tag{21.2}
$$

They are defined also at $\kappa=0$. Close the corresponding free form
with measure $\nu$, covariance $\operatorname{diag}(\varepsilon^2,1)$
and the original height killing. Denote its real-$x$ kernel by
$\widetilde p_\kappa$ and the kernel after quotienting $x$ by a period
$\ell$ by $p^{(\ell)}_\kappa$. The point in either comparison space is
$\widetilde o=(k_0,0,0,0)$. These are comparison realizations, not a new
native leaf at zero. The quotient with $\ell=\ell_\kappa$ is exactly a
coordinate representation of the nonzero-parameter native free operator.
Indeed,

$$
\begin{aligned}
d\mu&=a\,d\nu,&
(U_\kappa f)(k,\theta,v,x)&=a^{1/2}f(k,\theta,v,\kappa x),\\
\|U_\kappa f\|_{L^2(\nu)}&=\|f\|_{L^2(\mu)},&
\widetilde T_\kappa[U_\kappa f]&=T_\kappa[f],\\
p_\kappa(t,o,(k,\theta,v,\kappa x))
 &=a^{-1}p^{(\ell_\kappa)}_\kappa(t,\widetilde o,(k,\theta,v,x)).
\end{aligned}
\tag{21.3}
$$

The form identity extends by completion. The factor $a^{-1}$ in the
kernel is the Jacobian of the original unit point charge, not a choice
to increase that charge. Neither time nor the two visible periods changes.

**Theorem 21.2 (uniform comparison estimates and original field height).**
There is a single $\kappa_*>0$ such that all the following assertions
hold for $|\kappa|\le\kappa_*$. For every fixed $t_0>0$, the kernels
$p^{(\ell)}_\kappa(t_0,y,z)$ are bounded on the original height cylinder
by one finite constant independent of $\kappa$ and of every $\ell\ge4$.
For the real-$x$ cover,

$$
\widetilde p_\kappa\longrightarrow\widetilde p_0
\quad\hbox{locally uniformly on }
(0,\infty)\times
 (I\times\mathbb T^2\times\mathbb R)^2.
\tag{21.4}
$$

Its limiting kernel is strictly positive there. Consequently, for each
fixed $\tau>0$ there is $C_\tau<\infty$ such that, for every
$0<|\kappa|\le\kappa_*$ and every original point $y$,

$$
0<V_{\kappa,\tau}(y)\le\frac{C_\tau}{|\kappa|}.
\tag{21.5}
$$

For each nonempty compact $K\subset I\times\mathbb T^2\times\mathbb R$ there
are $c_{\tau,K}>0$ and $\kappa_K>0$ such that, on its injective image
$D=\kappa x$ and for either sign $0<|\kappa|\le\kappa_K$,

$$
V_{\kappa,\tau}(k,\theta,v,\kappa x)
 \ge\frac{c_{\tau,K}}{|\kappa|}
\quad\hbox{for almost every }(k,\theta,v,x)\in K.
\tag{21.6}
$$

The constants fix $I,k_0,Z,\varepsilon,\tau$; no joint limit of these
data is asserted.

Proof. Choose a slightly larger height interval
$I'=(l',u')$ with $0<l'<l<u<u'<H$. Shrink the two-sided parameter
interval so that the probabilities and coefficients are smooth on a
neighbourhood of $\overline I'$, with common positive margins.
Writing $a_\kappa(k)=(A_\kappa(k),B_\kappa(k),b_\kappa(k))$ for this
proof only, (12.8) and (16.7) give

$$
a_0(k)=\left(\frac{H-k}{2H},-\frac{k}{2H},\frac1k-\frac1H\right),
\qquad
\det(a_0,a_0',a_0'')=-\frac1{2Hk^3}.
\tag{21.7}
$$

Thus $\widetilde P,\widetilde Q_\kappa,
[\widetilde P,\widetilde Q_\kappa],
[\widetilde P,[\widetilde P,\widetilde Q_\kappa]]$ form a uniformly
nondegenerate frame on the compact parameter-height rectangle after a
further shrink. All coefficient derivatives are uniformly bounded.
Multiplying $\widetilde P$ by the fixed $\varepsilon>0$ retains these
properties. The local uniform strong Hörmander condition has step three,
including at the comparison value $\kappa=0$.

Here is a local argument for the asserted bound that does not assume a
uniform sum of cover tails or a compact space of bounded total volume.
On the larger cylinder with height $I'$, for each finite $\ell\ge4$,
take its free Friedrichs heat kernel $h_{\kappa,\ell}$. Its semigroup is
symmetric and sub-Markov, by integration by parts and the contraction
chain rule exactly as in Proposition 2.1. The same local Hörmander
argument gives a smooth interior kernel. On fixed-size coordinate
patches $U_1,U_2$ and a fixed compact positive-time interval $J$, positivity
and the sub-Markov property give the uniform initialization

$$
\int_J\int_{U_1}\int_{U_2}
 h_{\kappa,\ell}(t,y,z)\,d\nu(z)\,d\nu(y)\,dt
 \le |J|\,\nu(U_1).
\tag{21.8}
$$

The patches and their nested enlargements have bounded volume and fixed
margins independent of $\ell$. In the $x$ direction they can be chosen
inside intervals of length less than $4$; phase translations identify
all such charts. The visible torus needs only a fixed finite collection
of charts. Heights in $\overline I$ have a fixed distance from
$\partial I'$. All local coefficients on translated charts are identical.
A compactly supported measure of bounded mass in these space-time-pair
charts is bounded in $H^{-s}$ for any fixed sufficiently large $s$.
This follows directly by dual Sobolev embedding into the continuous
functions. Apply it to (21.8).

The kernel satisfies the homogeneous equation

$$
\left(\partial_t-\tfrac12\Delta_{\kappa,y}
                     -\tfrac12\Delta_{\kappa,z}\right)h_{\kappa,\ell}=0,
\qquad \Delta_\kappa=\varepsilon^2\partial_k^2+
 \widetilde Q_\kappa^2.
\tag{21.9}
$$

The separate spatial fields in $y$ and $z$, together with the time
field, satisfy the uniform weak Hörmander hypothesis for this operator.
The uniform local subelliptic estimate [H, Theorem B.1, pp.953--955]
applied with nested cutoffs therefore increases the initial negative
Sobolev order by a fixed positive amount at every iteration. Iteration
and Sobolev embedding give a uniform $C^0$ bound on smaller charts, and
also bounds for any fixed finite number of derivatives. This is the
local smoothing argument of [H, Corollary B.3]; (21.8) supplies its
initialization independently of the circle length. The estimate applies
to distributional solutions by smooth approximation in its local
Sobolev norms. Only the fixed charts, coefficient bounds, bracket lower
bound, and positive-time margins enter its constants. No factor equal
to the number of $x$ charts enters a pointwise supremum. This proves a
uniform bound for the larger-cylinder kernel at any fixed positive
time. Killing at $l,u$ earlier gives the claimed bound for
$p^{(\ell)}_\kappa$ by domain domination.

The same comparison fields on the real-$x$ cover are divergence free
and have selfadjoint contraction realizations on one common open
cylinder for all $\kappa$, including zero. Their coefficients depend
smoothly on $\kappa$ and satisfy (21.7). They meet the hypotheses of
[H, §3.2.2, Theorem 3.5, pp.922--923]: fixed open manifold and boundary
conditions, smooth parameter-dependent fields and positive measure,
uniform strong Hörmander generation, zero potential, and uniform
$L^2$ semigroup norm at most one. It gives (21.4), in fact with all
interior derivatives on compact positive-time sets. One can also
identify its semigroup limit directly: drive all parameters by the
same $K$ and independent $B^2$, integrate
$\sqrt2(A_\kappa,B_\kappa,b_\kappa)(K_s)dB_s^2$, wrap only the first
two phase coordinates, and kill at the same $\zeta$. Uniform convergence
of the coefficients gives convergence in probability of these finite-time
increments; local smoothing upgrades the resulting weak kernel limit.

For completeness, strict heat positivity holds also on this cover.
The three coefficient vectors at a suitable three interior heights are
independent, by (21.7). Height travel and signed phase legs there realize
any three real phase displacements. They stay inside $I$ and can be
traversed in any prescribed positive time. This is the same
bracket-accessibility and positive free-heat principle used in
Proposition 2.1, now before wrapping $x$. The connected cover is one
accessible component; its smooth killed kernel is strictly positive.

Projecting this very killed process by $x\mapsto[x]_{\ell}$ gives its
quotient process, with exactly the same death time. Hence its transition
measure is the pushforward of the cover measure. Relative to $\nu$ this
means

$$
p^{(\ell)}_\kappa(t,\widetilde o,(k,\theta,v,[x]_{\ell}))
 =\sum_{n\in\mathbb Z}
 \widetilde p_\kappa(t,\widetilde o,(k,\theta,v,x+n\ell))
\quad\hbox{almost everywhere}.
\tag{21.10}
$$

This is a nonnegative sum, justified by testing against nonnegative
functions on a fundamental cell. It requires no exchange of a signed
series or convergence of differentiated series. The original-circle
version follows using (21.3). This reuses the covering method of
(10.2), not its double-wall group formula for the different fields here.

For the upper Green bound use the uniform diagonal estimate just proved
at time $2\delta$, where $\delta=\tau/4$. Height Poincaré gives the same
$\lambda_D$ on every quotient, irrespective of $\ell$. The semigroup
calculation (20.10), now in measure $\nu$, gives

$$
p^{(\ell)}_\kappa(t,y,z)
 \le C_{\tau/2}e^{-\lambda_D(t-\tau/2)}
 \qquad(t\ge\tau,\ \ell\ge4).
\tag{21.11}
$$

Its integral is bounded by one finite $C_\tau$.
Ensure $\ell_\kappa\ge4$ by shrinking $\kappa_*$ if needed.
The exact Jacobian (21.3) proves (21.5) on the whole original cylinder,
including uniformly as a point approaches a height face.

For the lower bound, positivity and continuity give

$$
m_{\tau,K}:=
 \min_{\substack{\tau\le t\le\tau+1\\z\in K}}
 \widetilde p_0(t,\widetilde o,z)>0.
\tag{21.12}
$$

By (21.4), the corresponding kernels for both small signs are at least
$m_{\tau,K}/2$ on this compact set. The $n=0$ summand of (21.10), (21.3)
and integration over this fixed original-time interval imply (21.6),
with $c_{\tau,K}=m_{\tau,K}/2$. A compact $K$ has bounded $x$, so its
image lies in the injective chart $|D|<\pi$ for all small $a$.
The lower bound uses only a positive portion of the full field; the
field itself remains the entire integral in (20.5). $\square$

## 22. Full-domain inverse-parameter instability after regularization

**Theorem 22.1 (normalized native witnesses and matching ground-energy
order).** In (20.1)--(20.5) there are $C_\tau<\infty$, $c_\tau>0$,
$C_F<\infty$ and a single $\kappa_1>0$ such that, for every
$0<|\kappa|\le\kappa_1$ and every $g>0$,

$$
\lambda_D-\frac{gC_\tau}{|\kappa|}
 \le E_{\kappa,\tau}(g)
 \le C_F-\frac{gc_\tau}{|\kappa|}.
\tag{22.1}
$$

The lower inequality holds for every normalized state in the completed
original full form domain. The upper inequality is realized as an
inequality on explicit normalized smooth native full-domain states whose
free energies are bounded by $C_F$. In particular, for each fixed $g>0$,
through both signs,

$$
E_{\kappa,\tau}(g)\longrightarrow-\infty,
\qquad
\frac{gc_\tau}{2|\kappa|}
 \le -E_{\kappa,\tau}(g)
 \le\frac{gC_\tau}{|\kappa|}
\quad\hbox{for all sufficiently small }|\kappa|.
\tag{22.2}
$$

Thus no fixed nonempty strict positive coupling window has a finite
full-state lower bound independent of nonzero $\kappa$ on any two-sided
neighbourhood of zero. The matching order concerns the full ground
energy, not only the value of a selected trial sequence.

Proof. An explicit fixed bump is available. Put
$r_k=\tfrac12\min(k_0-l,u-k_0)$, $r_\theta=\pi/4$, and

$$
\eta(s)=
\begin{cases}e^{-1/(1-s^2)},&|s|<1,\\0,&|s|\ge1,\end{cases}
\qquad J_\eta=\int_{-1}^1\eta(s)^2ds>0.
\tag{22.2a}
$$

In the actual visible phase representatives $(-\pi,\pi)$ take

$$
F(k,\theta,v,x)=
\frac{\eta((k-k_0)/r_k)\eta(\theta/r_\theta)
      \eta(v/r_\theta)\eta(x)}
 {\sqrt{r_kr_\theta^2J_\eta^4}},
\tag{22.2b}
$$

with smooth zero extension and periodic continuation in $\theta,v$.
Then $F\in C_c^\infty(I\times\mathbb T^2\times\mathbb R)$ and
$\int|F|^2d\nu=1$ exactly. Write $K=\operatorname{supp}F$ and take
$R=2$, so $K\subset\{|x|<R\}$. At every sufficiently small nonzero parameter,
using the representative $D\in(-\pi,\pi)$, set

$$
f_\kappa(k,\theta,v,D)=
 |\kappa|^{-1/2}F(k,\theta,v,D/\kappa),
\tag{22.3}
$$

and extend by zero outside this image of the support. Require
$|\kappa|R<\pi$. The function vanishes near the circle seam and the
height faces, so it is a genuine member of
$C_c^\infty(\Omega_\kappa)\subset\mathcal F_\kappa$, with the actual
periods and unchanged boundary conditions. For negative $\kappa$ the
orientation reverses but the measure Jacobian is still $|\kappa|$.
Consequently

$$
\begin{aligned}
\|f_\kappa\|_{L^2(\mu)}^2&=\int|F|^2d\nu=1,\\
T_\kappa[f_\kappa]&=
 \int\left(\varepsilon^2|\partial_kF|^2+
 |A_\kappa\partial_\theta F+B_\kappa\partial_vF+
                  b_\kappa\partial_xF|^2\right)d\nu\le C_F.
\end{aligned}
\tag{22.4}
$$

Here $C_F$ is the supremum of the displayed finite expression over a
compact two-sided parameter interval. In particular it is independent
of $g$ and of small nonzero $\kappa$. The cancellation
$(\kappa b_\kappa)\partial_D=b_\kappa\partial_x$ verifies the energy
in the original two controls; no isotropic kinetic surrogate is used.
By Theorem 21.2 on $K$ and the same exact normalization,

$$
\int V_{\kappa,\tau}|f_\kappa|^2d\mu
 =\int V_{\kappa,\tau}(k,\theta,v,\kappa x)|F|^2d\nu
 \ge c_{\tau,K}/|\kappa|.
\tag{22.5}
$$

Set $c_\tau=c_{\tau,K}$ and shrink $\kappa_1$ to satisfy all previous
bounds. This proves the upper inequality in (22.1). Conversely,
(21.5) and (20.9), now applied to every member of the completed domain,
give its lower inequality. These two statements compare admissible
full-state energies of the identical regularized field.

Since $C_F>0$, further imposing
$|\kappa|\le gc_\tau/(2C_F)$ proves (22.2). If a fixed interval of
couplings is bounded away from zero, the same parameter restriction
can use its positive lower endpoint, and the divergence is uniform on
that interval. More generally any nonempty positive window contains a
fixed $g>0$, for which (22.2) already contradicts a proposed common finite
lower bound. The conclusion is a counterexample with actual normalized
states, not an inference from a failed estimate or the change of rank.
No parameter-dependent small-coupling window is used to settle it.
$\square$

## 23. Surviving-charge normalization, marginal fields and the zero leaf

**Theorem 23.1 (charge normalization does not repair uniformity).**
Normalize the effective source, if desired, by

$$
\sigma^\#_{\kappa,\tau}=S(\tau)^{-1}\sigma_{\kappa,\tau},\qquad
V^\#_{\kappa,\tau}=S(\tau)^{-1}V_{\kappa,\tau}.
\tag{23.1}
$$

Then $L_\kappa V^\#_{\kappa,\tau}=\sigma^\#_{\kappa,\tau}$,
$\int\sigma^\#_{\kappa,\tau}d\mu=1$, and
$\sigma^\#_{\kappa,\tau}d\mu$ is the original free distribution at
$\tau$ conditional on survival. The complete form and operator domains
are unchanged, and

$$
E^\#_{\kappa,\tau}(g)=E_{\kappa,\tau}(g/S(\tau)).
\tag{23.2}
$$

For every fixed $g>0$ it has the same two-sided inverse-$|\kappa|$
negative divergence. The total mass of $V^\#_{\kappa,\tau}$ is
$\mathbb E(\zeta-\tau)_+/S(\tau)$, not necessarily one.

Proof. Theorem 20.2 gives the source equation, its charge, and the
strictly positive constant $S(\tau)$ independent of the parameter.
Division proves (23.1) and (23.2). Conditional probability identifies
the normalized source measure; applying the free inverse to that measure
gives the stated field. The conditioning is at $\tau$ only; propagation
after that time retains the original killing. In particular its field
mass is $\mathbb E(\zeta-\tau\mid\zeta>\tau)$. Theorem 22.1 applies
with the fixed coupling
$g/S(\tau)$. No killed mass is silently restored in (20.5): restoring
unit effective charge is the explicitly different normalization (23.1).
$\square$

**Definition 23.2 (the retained $q$ factor and its native zero limit).**
Put $B=I\times\mathbb T_\theta\times\mathbb T_v$ and
$d\nu_B=dk\,d\theta\,dv$. Let

$$
\begin{aligned}
\overline Q_\kappa&=A_\kappa\partial_\theta+B_\kappa\partial_v,\\
\overline T_\kappa[h]&=\int_B
 (\varepsilon^2|\partial_kh|^2+|\overline Q_\kappa h|^2)d\nu_B,\\
\overline{\mathcal F}_\kappa&=
 \overline{C_c^\infty(B)}^{(\|\cdot\|_2^2+\overline T_\kappa)^{1/2}},
\qquad \overline L_\kappa\text{ its Friedrichs operator},\\
\overline V_{\kappa,\tau}(q)&=
 \int_\tau^\infty\overline p_\kappa(t,q_0,q)dt,
\qquad q_0=(k_0,0,0).
\end{aligned}
\tag{23.3}
$$

At $\kappa=0$ the actual native leaf is $B$, since $D=0$ for all original
histories. Its free operator is $L_0=\overline L_0$ with its own measure
$d\nu_B$ and unit pole $q_0$. Its regularized field is
$V_{0,\tau}=\overline V_{0,\tau}$. This is different from the
four-coordinate comparison operator $\widetilde L_0$ of (21.2).

**Theorem 23.3 (exact marginal factors, zero-limit convergence and its
energy boundary).** For every small nonzero $\kappa$,

$$
\begin{aligned}
\int_{\mathbb T_D}p_\kappa(t,o,(q,D))dD
 &=\overline p_\kappa(t,q_0,q),\\
\int_{\mathbb T_D}V_{\kappa,\tau}(q,D)dD
 &=\overline V_{\kappa,\tau}(q),\\
\frac1{2\pi}\int_{\mathbb T_D}V_{\kappa,\tau}(q,D)dD
 &=\frac{\overline V_{\kappa,\tau}(q)}{2\pi}.
\end{aligned}
\tag{23.4}
$$

The first identity is an identity of smooth positive-time densities;
the remaining ones hold for the nonnegative integral representatives.
The isometry $Jh=(2\pi)^{-1/2}h(q)$ identifies the complete free
$D$-independent subspace with $L^2(B,\nu_B)$, including

$$
\begin{aligned}
\mathcal F_\kappa\cap\operatorname{Ran}J
 &=J\overline{\mathcal F}_\kappa,\\
\mathfrak q_{\kappa,\tau,g}[Jh]
 &=\overline T_\kappa[h]
  -\frac{g}{2\pi}\int_B\overline V_{\kappa,\tau}|h|^2d\nu_B.
\end{aligned}
\tag{23.5}
$$

The marginal regularized fields are uniformly bounded and converge
locally uniformly, and in every finite $L^p(B,\nu_B)$, to $V_{0,\tau}$.
The free marginal kernels converge smoothly on compact interior
positive-time sets to the actual native zero-leaf kernel. In particular,
for each fixed smooth normalized $h$ in the base core, the energy in
(23.5) tends to

$$
\overline T_0[h]-\frac{g}{2\pi}\int_B V_{0,\tau}|h|^2d\nu_B.
\tag{23.6}
$$

These sector energies have a lower bound uniform in small $\kappa$ for
all normalized members of their complete sector domains. In contrast,
the complete four-coordinate minima diverge as in (22.2). The actual
zero-leaf regularized energy, with unit charge and coupling $g$, is a
finite attained minimum on $\overline{\mathcal F}_0$ and uses $g$, not
$g/(2\pi)$.

Proof. The projected killed process forgets only $D$. Its drift-free
fields are $\partial_k,\overline Q_\kappa$, driven by exactly the same
two Brownian motions and killed at the same height exit. Uniqueness of
this smooth diffusion identifies its semigroup with that of
$\overline L_\kappa$. Integrating the full kernel against base tests
therefore proves the first identity in (23.4); smoothness upgrades the
density equality from almost everywhere to every interior base point.
Tonelli proves the field identities. In particular integration and
averaging differ by the actual hidden-circle volume $2\pi$.

Core pullback gives $T_\kappa[Jh]=\overline T_\kappa[h]$ and the norm
isometry. Conversely average any approximating full-core sequence over
$D$. The averaging projection is contractive in $L^2$ and in the free
form norm: Jensen applies to both horizontal derivatives, and the
periodic $D$ derivative integrates to zero. For a limit in
$\operatorname{Ran}J$ its averaged approximants converge to the same
limit. This proves the completed-domain equality. Substituting
$|Jh|^2=|h|^2/(2\pi)$ and (23.4) proves (23.5), first on the core and
then throughout the domain by boundedness of the fields.

At zero,

$$
\det\begin{pmatrix}A_0&A'_0\\B_0&B'_0\end{pmatrix}
 =-\frac1{4H}.
\tag{23.7}
$$

Thus the base family satisfies a uniform step-two strong Hörmander
condition on the same larger height interval $I'$, after a common
parameter shrink. The uniform local smoothing argument of
(21.8)--(21.9), now on the fixed base torus, supplies uniform
positive-time diagonal bounds. The free height gap supplies their
uniform exponentially decreasing time tails. The parameter-dependent
kernel theorem [H, Theorem 3.5] gives smooth convergence on compact
interior positive-time sets. Splitting the integral in (23.3) at a
large fixed time and bounding the remaining tail as in (21.11) proves
local uniform convergence of the regularized marginal fields and a
uniform bound on all of $B$. Since $\nu_B(B)<\infty$, dominated
convergence proves every asserted finite $L^p$ convergence.
Coefficient convergence and this field convergence prove (23.6).
The uniform multiplier bound gives the uniform sector lower bound
$\lambda_D-(g/(2\pi))\sup_\kappa\|\overline V_{\kappa,\tau}\|_\infty$.
At zero, the fixed-leaf bounded-field and compact-embedding argument of
Theorem 20.2 applies on the actual three-coordinate cylinder, so its
unit-charge minimum is finite and attained for every fixed $g>0$.

There is an exact analytic source distinction behind (23.5).
Averaging the full fixed-pole field over translations of $D$ equals
$\overline V_{\kappa,\tau}(q)/(2\pi)$. Before smoothing its source is
$\delta_{q_0}\otimes dD/(2\pi)$, and after smoothing its source density
is $\overline p_\kappa(\tau,q_0,q)/(2\pi)$. This follows from free
translation symmetry and (23.4), exactly as for the marginal/source
correspondence in the observation-quotient volume, Theorem 3.1.
It does not identify the original fixed-pole multiplier with its average.
The full witnesses (22.3) depend on $D$ and are allowed by the original
form domain. Their energies cannot be bounded by restricting the
infimum to $\operatorname{Ran}J$. Nor is a four-dimensional Lebesgue
heat density at $\kappa=0$ used anywhere: the comparison density in
(21.4) belongs to a different auxiliary operator. $\square$

**Proposition 23.4 (height marginal and the boundary charge balance).**
Let $h_I(t;k_0,k)$ be the Dirichlet heat kernel of
$-\varepsilon^2\partial_k^2$ on $I$, relative to $dk$, and set
$v_\tau(k)=\int_\tau^\infty h_I(t;k_0,k)dt$. Then

$$
\begin{aligned}
\int_{\mathbb T^3}V_{\kappa,\tau}(k,\theta,v,D)
 d\theta\,dv\,dD&=v_\tau(k),\\
-\varepsilon^2v_\tau''(k)&=h_I(\tau;k_0,k),\qquad
 v_\tau(l)=v_\tau(u)=0,\\
\varepsilon^2\{v_\tau'(l)-v_\tau'(u)\}&=S(\tau).
\end{aligned}
\tag{23.8}
$$

On the native zero leaf the corresponding integral is over
$\mathbb T^2$, with the same right side. Therefore the effective charge
and its absorbing height flux are consistent with the original killing
and angular measures on both leaves.

Proof. Integrating the transition law over all phases leaves precisely
the height Brownian motion, with no angular normalization factor. Tonelli
and the one-dimensional Dirichlet semigroup prove the first line and
the differential equation. Positive $\tau$ gives smooth scalar boundary
data, so integration of that equation over $I$ gives the last line.
Its right side is $\int_Ih_I(\tau;k_0,k)dk=S(\tau)$.
This scalar flux statement does not require assuming pointwise normal
derivatives of a full nonsmoothed Green singularity. $\square$

## 24. Mathematical dependencies and the finite-resolution boundary

**Proposition 24.1 (exact supplier correspondence and additional native
content).** The positive-time fixed-source and uniform full-state
statements above have the following dependency correspondence. The
classical intermediate results are used with their stated hypotheses;
the additional native conclusion is (22.1)--(22.2) with the source,
Jacobian and domain identities (20.6)--(23.8).

| Mathematical supplier | Reused scope and distinction from the additional conclusion |
| --- | --- |
| [N, Definitions 2.1, 3.1, 8.1 and Theorem 8.2; Theorem 10.3 and Definition 10.6] | Original probabilities, arbitrary fixed preparations, negative phase convention, two native controls, actual circles, grouped leaves, horizontal brackets and the added free analytic contract. These do not already imply a uniform near-wall regularized energy bound or its negation. |
| This volume, Propositions 2.1--2.2 and Theorem 3.1 | Fixed-leaf free heat, gap, compact form embedding, unit point Green and unregularized full collapse for every nonzero nearby parameter and every $g>0$. The unregularized collapse is reused, not reproved or transferred to a smoothed field by assertion. |
| This volume, (12.7)--(12.9), Proposition 16.2 and Theorem 17.1 | The exact smooth coefficients and $w_0-w_{13}=\kappa b_\kappa$, original covariance and killed height law. The full-lifetime excursion estimate concerns a different random-history event and supplies no variational bound over all normalized states. |
| This volume, (10.2) and its killed-process proof | Pushforward of the actual free cover law gives nonnegative periodization. Its double-wall group kernel, Hardy constant and noncompact attractive theorem are not applied to the different rescaled step-three fields. Equation (21.10) verifies the needed cover law directly. |
| [Observation quotient, Theorems 2.1 and 3.1](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md) and [Free diffusion quotient rigidity, §§2--3](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md) | Completed-domain pullback, hidden integration versus averaging, and source smearing are established methods for their specified double-wall factors. Equations (23.3)--(23.7) verify the new nearby $q$ factor; their older bottom-observation factor is not silently identified with this three-coordinate $q$. |
| [Continuation III, Specification 82.7](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md) | A fixed bounded truncation $\min(\Gamma,M)$ gives the elementary bound $-gM$. It neither supplies a parameter-independent bound for $V_{\kappa,\tau}$ nor preserves this heat-regularized source equation. |
| [Continuation IV, §§100--102](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md) | Centered finite occurrence-tree screening, its source-size crossover and its propagation-realization assumptions concern a different counting operator and source. They supply no replacement for the continuous native killed cylinder. |
| [H] Colin de Verdière--Hillairet--Trélat, [DOI 10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf), Theorem B.1, Corollary B.3 and Theorem 3.5 | Literature-attested uniform local subelliptic estimates, local smoothing and positive-time parameter continuity. The verified determinant (21.7), bounded local mass initialization (21.8), larger height cylinder, uniform gap and exact Jacobian are necessary native inputs. No Gaussian theorem for a different isotropic or globally homogeneous operator is substituted. |
| [T] G. Teschl, *Mathematical Methods in Quantum Mechanics*, [author text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorems 6.24 and 4.10 | Literature-attested bounded form perturbation and variational spectral facts. They apply after the actual regularized multiplier is bounded and the free form embedding is compact. They provide no parameter-uniform multiplier constant by themselves. |

Proof. Equations (20.2)--(20.4) specialize the supplied source without
changing its controls, periods or analytic kinetic contract. The
semigroup law proves its new effective source equation; the independent
height component proves the killed charge. The nonvanishing determinant
(21.7) supplies a regular comparison family on the resolved hidden
coordinate, while (21.3) retains the original Hilbert and point-charge
normalizations. The uniform local estimates and the fixed height gap
then give the whole-domain lower bound. The positive cover kernel and
the explicitly normalized original-domain states (22.3) give the
opposite bound with the same parameter order. Thus the substantive
repository-derived application is the uniform native two-sided
inverse-parameter conclusion, rather than a new general heat-kernel,
periodization, perturbation or variational theorem. The rows distinguish
which classical or published native statements enter each step. This
correspondence makes no literature-priority or formal-kernel claim.
$\square$

**Proposition 24.2 (analytic and operational interpretation).** Fixed
positive original-clock heat smoothing removes the fixed-parameter
unbounded-below point attraction but does not remove its parameter-uniform
full-state instability near this wall. Conditional surviving-charge
normalization does not change that verdict. Free marginal convergence,
a restriction to $D$-independent amplitudes, and the three-coordinate
native zero leaf are each compatible with the full-state divergence.
None of these conclusions supplies a physical smoothing, projection,
preparation, reset, acquisition capability, physical spatial axes or a
mean-selection mechanism.

Proof. Theorem 3.1 gives the already established unregularized
fixed-nonzero-parameter collapse. Theorem 20.2 proves a bounded
regularized multiplier and a finite attained minimum at each such
parameter. Theorem 22.1 proves failure of the original uniform target
with actual states from its complete domain, and also its matching
inverse-$|\kappa|$ order. Theorem 23.1 preserves that order after restoring
unit surviving charge. Theorem 23.3 proves the different marginal and
sector statements with the factors required by their Hilbert spaces,
and identifies the actual zero-leaf problem separately. The lost
uniformity is therefore a source/phase-volume effect that persists at
fixed analytic resolution: on a hidden strip of width of order
$|\kappa|$, the regularized field generated by the original point charge
has height of order $|\kappa|^{-1}$, and admissible analytic amplitudes can use that
width with bounded horizontal free energy. These statements follow
from (21.5)--(22.5), without asserting a sharp coefficient or a limiting
profile. The definitions supply only analytic semigroups and states on
ray space; no map or lawful physical operation realizing them is an
assumption. Their existence cannot establish any of the listed physical
or operational conclusions. $\square$

## 追加锚（本行以下为增补区）


## 25. Moving resolution with the original killed source

**Definition 25.1 (fixed data, complete domains and the two charges).**
Fix, before choosing a parameter neighbourhood or a time family,

$$
0<Z<1,\quad H=(1-Z)/2,\quad
0<l<k_0<u<H,\quad \varepsilon>0,\quad \tau_{\min}>0.
\tag{25.1}
$$

For every sufficiently small nonzero real $\kappa$ of either sign use
exactly Definition 20.1. Thus $X=Y=H+\kappa$, the probabilities are

$$
(k-2\kappa,H+\kappa-k,Z,H+\kappa-k,k),
\tag{25.2}
$$

all preparation phases are arbitrary and immutable, the amplitude
convention is negative, and the increments satisfy $h_2=0$, $h_1=h_3=v$.
The unimodular coordinates are $\theta=h_{13}$, $D=h_0-h_{13}$ and $v$,
each of actual period $2\pi$. The full cylinder, measure and pole are

$$
\Omega=I\times\mathbb T_\theta\times\mathbb T_v\times\mathbb T_D,
\quad I=(l,u),\quad d\mu=dk\,d\theta\,dv\,dD,
\quad o=(k_0,0,0,0).
\tag{25.3}
$$

Retain $P=\partial_k$ and the original $Q$ with
$d=(1,-1,0,-1,1)$, $\mathcal I_\kappa=
\sum_{s\in\{0,1,3,13\}}p_{\kappa,s}^{-1}$ and
$w_s=d_s/(p_{\kappa,s}\mathcal I_\kappa)$.
For subsequent estimates write its already supplied coefficients as

$$
\begin{aligned}
s_\kappa&=H+\kappa,& \alpha_\kappa&=\kappa+\kappa^2/H,\\
A_\kappa&=\frac{(k-2\kappa)(s_\kappa-k)}{2H(k-\alpha_\kappa)},&
B_\kappa&=-\frac{k(k-2\kappa)}{2H(k-\alpha_\kappa)},&
b_\kappa&=\frac{s_\kappa-k}{H(k-\alpha_\kappa)},\\
Q_\kappa&=A_\kappa\partial_\theta+B_\kappa\partial_v
                 +\kappa b_\kappa\partial_D.
\end{aligned}
\tag{25.4}
$$

There is one $v$ coefficient. Let $T_\kappa$, $\mathcal F_\kappa$ and
$L_\kappa$ be the complete free form, its horizontal closure and its
Friedrichs operator in (20.4). The covariance is
$\operatorname{diag}(\varepsilon^2,1)$, with diffusion covariance twice
this matrix times $dt$. The original clock is $e^{-tL_\kappa}$.
Both height faces are absorbing and every phase is periodic.
Put

$$
d_I=u-l,\qquad \lambda=\frac{\varepsilon^2\pi^2}{d_I^2},\qquad
\phi(k)=\sqrt{2/d_I}\sin\frac{\pi(k-l)}{d_I}.
\tag{25.5}
$$

For every $\tau\ge\tau_{\min}$ define, in that clock,

$$
V_{\kappa,\tau}(y)=\int_\tau^\infty p_\kappa(t,o,y)dt,
\qquad S(\tau)=\mathbb P_{k_0}(\zeta>\tau),
\tag{25.6}
$$

where $\zeta$ is the first exit from $I$ of
$K_t=k_0+\sqrt2\varepsilon B_t^1$. The source equation, both deaths
and its charge are those of Theorem 20.2:

$$
L_\kappa V_{\kappa,\tau}=p_\kappa(\tau,o,\cdot),\qquad
\int p_\kappa(\tau,o,y)d\mu(y)=S(\tau)\in(0,1).
\tag{25.7}
$$

Compare exactly the two fields

$$
W_{\rm raw}=V_{\kappa,\tau},\qquad
W_{\rm unit}=V_{\kappa,\tau}/S(\tau).
\tag{25.8}
$$

The second has effective source $p_\kappa(\tau,o,\cdot)/S(\tau)$ of
charge one; propagation in its inverse $L_\kappa^{-1}$ still has both
height deaths. It is not a reset source or the Green field of a
survival-conditioned free generator. Theorem 20.2 and Theorem 23.1,
applied at each fixed pair $(\kappa,\tau)$, give bounded positive
multipliers before the following attractive forms are used. They are
closed on exactly $\mathcal F_\kappa$, have operator domain
$D(L_\kappa)$, compact resolvent, and attained finite minima

$$
E_\sigma(\kappa,\tau;g)=
\inf_{\substack{f\in\mathcal F_\kappa\\\|f\|_2=1}}
\left(T_\kappa[f]-g\int W_\sigma|f|^2d\mu\right),\qquad g>0.
\tag{25.9}
$$

Here the infimum is over the entire original domain. The unregularized
full point-field collapse of Theorem 3.1 remains a different, reused
statement. No attractive evolution is a premise of any estimate below.

## 26. All-time native heat bounds and the actual circle gap

**Theorem 26.1 (joint heat estimate and hidden-circle mixing).**
For the fixed data (25.1), there is one $\kappa_*>0$ and constants
$c,C>0$, independent of $\kappa,t,\tau$ and $g$, such that, for both
signs $0<|\kappa|\le\kappa_*$ and every $t\ge\tau_{\min}$,

$$
0<p_\kappa(t,o,y)\le
 C e^{-\lambda t}\left(1+\frac1{|\kappa|\sqrt t}\right)
\qquad(y\in\Omega).
\tag{26.1}
$$

In particular, throughout that same neighbourhood and for all
$\tau\ge\tau_{\min}$,

$$
\|V_{\kappa,\tau}\|_\infty\le
 C e^{-\lambda\tau}\left(1+\frac1{|\kappa|\sqrt\tau}\right).
\tag{26.2}
$$

The lowest free eigenvalue is exactly $\lambda$, with normalized
positive eigenfunction $(2\pi)^{-3/2}\phi(k)$. If
$\delta_\kappa$ is the gap above it, then

$$
c\kappa^2\le\delta_\kappa\le C\kappa^2.
\tag{26.3}
$$

For $t\ge\max(\tau_{\min},|\kappa|^{-2})$ one also has, uniformly
in every actual phase and every height,

$$
\left|e^{\lambda t}p_\kappa(t,o,y)
 -\frac{\phi(k_0)\phi(k)}{(2\pi)^3}\right|
 \le C e^{-c\kappa^2t}.
\tag{26.4}
$$

Thus (26.1) includes winding and mixing at times of order
$|\kappa|^{-2}$ and beyond. The additive constant in its factor
$1+(|\kappa|\sqrt t)^{-1}$ is the actual-circle saturation of the
hidden heat factor.

Proof. The argument uses the actual phase Fourier series and scalar
Dirichlet operators; it does not assume a uniform hypoelliptic heat
constant. Choose a closed two-sided parameter interval on which all
probabilities on a slightly larger height interval have positive
margins. The coefficients in (25.4) and their derivatives are then
uniformly bounded on $[l,u]$, and $0<m\le b_\kappa\le M<\infty$.
All subsequent parameter restrictions are fixed independently of time.

Write $a_\kappa(k)=(A_\kappa(k),B_\kappa(k),b_\kappa(k))$.
For $\eta\in\mathbb R^3$ let

$$
H_{\kappa,\eta}=-\varepsilon^2\partial_k^2+
                 |\eta\cdot a_\kappa(k)|^2
\quad\hbox{on }H_0^1(I),\qquad
\beta_\kappa(\eta)=\inf\sigma(H_{\kappa,\eta}).
\tag{26.5}
$$

The phrase ``on $H_0^1$'' specifies its form domain; the operator is
the scalar Dirichlet Friedrichs realization. We prove the uniform bound

$$
\beta_\kappa(\eta)\ge\lambda+c\Psi(|\eta|),\qquad
\Psi(r)=\begin{cases}r^2,&0\le r\le1,\\r^{2/3},&r\ge1.\end{cases}
\tag{26.6}
$$

The following elementary one-dimensional estimates are intermediate
steps in this native Fourier calculation. For $|e|=1$, the numerator
of $v_{\kappa,e}=e\cdot a_\kappa$ with denominator
$2H(k-\alpha_\kappa)$ is the quadratic polynomial

$$
P_{\kappa,e}(k)=e_1(k-2\kappa)(s_\kappa-k)
                 -e_2k(k-2\kappa)+2e_3(s_\kappa-k).
\tag{26.7}
$$

At zero its coefficient vector is
$(2He_3,He_1-2e_3,-e_1-e_2)$. The map from $e$ to these three
coefficients is invertible. By continuity its inverse remains uniformly
bounded after a single parameter shrink. The denominator is bounded
above and below by positive constants. Hence, uniformly in $\kappa,e$,

$$
\|v_{\kappa,e}\|_\infty\le M_1,\qquad
|\{k\in I:|v_{\kappa,e}(k)|\le s\}|\le C_1\sqrt s
\quad(0<s\le1).
\tag{26.8}
$$

For the second inequality, a measurable set of length $b>0$ contains
three points whose successive distances are at least $b/4$, up to an
arbitrarily small reduction. If a quadratic is bounded there by $C s$,
its Lagrange interpolation formula bounds its coefficient norm by
$C' s/b^2$, since $I$ is bounded. The uniform lower coefficient norm
in (26.7) gives $b\le C''\sqrt s$. Applying this to the sublevel set
proves (26.8), including linear and constant polynomial cases.

For normalized $f\in H_0^1(I)$ put

$$
\mathcal E=\varepsilon^2\|f'\|_2^2+
 r^2\|v_{\kappa,e}f\|_2^2,\qquad r>0.
$$

One-dimensional Sobolev and Dirichlet Poincare give
$\|f\|_\infty^2\le2\|f'\|_2\le2\sqrt{\mathcal E}/\varepsilon$
and $\mathcal E\ge\lambda$. Splitting its unit norm over the sublevel
set in (26.8) and its complement yields

$$
1\le C\sqrt{s\mathcal E}+\frac{\mathcal E}{r^2s^2}.
\tag{26.9}
$$

Choose $s=c_0/\mathcal E$, where $c_0\le\lambda$ is fixed small
enough to make the first term at most $1/2$. It follows that
$\mathcal E\ge c_1 r^{2/3}$, uniformly for every normalized $f$.
This proves the needed large-frequency growth without a boundary
subelliptic estimate.

For small frequencies, compactness of the parameter interval and unit
sphere and the polynomial independence give

$$
m_1:=\inf_{\kappa,|e|=1}\int_I
             |v_{\kappa,e}|^2\phi^2dk>0.
\tag{26.10}
$$

Indeed a zero integral would make the polynomial (26.7) identically
zero. Decompose $f=z\phi+h$, $h\perp\phi$. The next scalar Dirichlet
height eigenvalue is $4\lambda$. If
$\mathfrak d=\mathcal E-\lambda$, then
$\|h\|_2^2\le\mathfrak d/(3\lambda)$. When $\mathfrak d\le d_0$ for a sufficiently
small fixed $d_0>0$, the triangle inequality, (26.8) and (26.10) give

$$
\|v_{\kappa,e}f\|_2
 \ge |z|\sqrt{m_1}-M_1\sqrt{\mathfrak d/(3\lambda)}
 \ge\tfrac12\sqrt{m_1}.
$$

Thus $\mathfrak d\ge m_1r^2/4$. If $\mathfrak d>d_0$ and $r\le1$, instead
$\mathfrak d\ge d_0r^2$. This proves (26.6) for $r\le1$. For each fixed
$\kappa,e$, the scalar variational bottom is nondecreasing in $r$.
It therefore has a uniform positive gap above $\lambda$ for $r\ge1$.
Combining that gap on a bounded range with
$\beta_\kappa(re)\ge c_1r^{2/3}$ on the large range proves (26.6)
for all $r$. This proof also applies to complex $f$, by the same norm
inequalities.

Let $K_{\kappa,\eta}(t;k,k')$ be the scalar kernel of (26.5), and
$h_I$ the original killed height kernel. Positivity and domination give

$$
0\le K_{\kappa,\eta}(t;k,k')\le h_I(t;k,k').
\tag{26.11}
$$

For attribution, this is the elementary bounded nonnegative-potential
case of the Trotter product formula [T, Theorem 5.11]: alternate the
height heat semigroup and multiplication by
$\exp(-t|\eta\cdot a_\kappa|^2/n)$. Every product is positive and
dominated by the height semigroup, and its strong limit has the same
property. At each fixed $\eta$ the potential is bounded and the scalar
operator is selfadjoint with the same Dirichlet domain, exactly the
hypotheses of that theorem. No uniform bound on that potential is assumed.

Fix $\delta=\tau_{\min}/4$. The height sine series bounds
$\sup_kh_I(2\delta;k,k)$ by a finite constant. Splitting the scalar
semigroup at times $\delta,t-2\delta,\delta$, and using its spectral
norm and (26.11), gives for $t\ge\tau_{\min}$

$$
\begin{aligned}
|K_{\kappa,\eta}(t;k,k')|
&\le C_\delta e^{-\beta_\kappa(\eta)(t-2\delta)}\\
&\le C e^{-\lambda t}\exp(-c t\Psi(|\eta|)).
\end{aligned}
\tag{26.12}
$$

Here $t-2\delta\ge t/2$; this fixed positive smoothing interval
loses no fraction of the height death exponent $\lambda$.

Use the orthonormal angular modes
$(2\pi)^{-3/2}e^{i(n\theta+mv+jD)}$, for $(n,m,j)\in\mathbb Z^3$.
Parseval for the raw measure gives the exact scalar potential
$(nA_\kappa+mB_\kappa+\kappa j b_\kappa)^2$.
Consequently the completed free form is the orthogonal sum of (26.5)
with $\eta=(n,m,\kappa j)$. More explicitly, for the orthonormal
expansion $f=\sum f_{nmj}(k)(2\pi)^{-3/2}e^{i(n\theta+mv+jD)}$,

$$
\begin{aligned}
\mathcal F_\kappa=\biggl\{f\in L^2(\mu):\;&
 f_{nmj}\in H_0^1(I)\text{ for all }n,m,j,\\
&\sum_{n,m,j}\left(\varepsilon^2\|f'_{nmj}\|_2^2+
 \|(nA_\kappa+mB_\kappa+\kappa j b_\kappa)f_{nmj}\|_2^2\right)
 <\infty\biggr\},
\end{aligned}
$$

and $T_\kappa$ is precisely that sum. Phase convolution commutes with
both fields and converges in the form norm. Finite Fourier truncation
and scalar height approximation show conversely that every sequence in
the displayed domain is a limit of the original core. This proves the
decomposition for the complete domain. In particular

$$
p_\kappa(t,o,(k,\theta,v,D))=
\frac1{(2\pi)^3}\sum_{n,m,j\in\mathbb Z}
 e^{i(n\theta+mv+jD)}
 K_{\kappa,(n,m,\kappa j)}(t;k_0,k).
\tag{26.13}
$$

Absolute convergence follows from (26.12) and the summation estimate
below. Thus this kernel identity follows from the orthogonal-sum
semigroup first, and then holds pointwise by continuity. It is not a
formal Fourier density at $\kappa=0$.

Set $a=|\kappa|\le1$. Monotonicity of $\Psi$ gives

$$
\Psi(\sqrt{n^2+m^2+a^2j^2})
 \ge\tfrac13\{\Psi(|n|)+\Psi(|m|)+\Psi(a|j|)\}.
$$

For $t\ge\tau_{\min}$ the first two one-dimensional sums are
bounded independently of $t$. For the third, comparison with an
integral gives

$$
\begin{aligned}
\sum_{j\in\mathbb Z}e^{-c t\Psi(a|j|)}
&\le1+\frac2a\int_0^\infty e^{-c t\Psi(r)}dr\\
&\le C\left(1+\frac1{a\sqrt t}\right).
\end{aligned}
\tag{26.14}
$$

On $(0,1)$ the integral is bounded by $C t^{-1/2}$; on $(1,\infty)$
comparison with the full $r^{2/3}$ integral gives $C t^{-3/2}$,
which is at most a fixed multiple of $t^{-1/2}$ on this time range.
The Fourier sum, (26.12) and (26.14) prove (26.1) on the entire original
cylinder. Integrating it for $t\ge\tau$, and using
$t^{-1/2}\le\tau^{-1/2}$, proves (26.2).

For the gap, the zero angular mode has bottom $\lambda$ and next
eigenvalue $4\lambda$. Every nonzero angular mode has
$|(n,m,\kappa j)|\ge a$, so (26.6) gives a gap at least $c a^2$
when $a\le1$. The normalized test
$(2\pi)^{-3/2}\phi(k)e^{iD}$ is orthogonal to the ground state and has
energy

$$
\lambda+a^2\int_I b_\kappa(k)^2\phi(k)^2dk\le\lambda+Ca^2.
\tag{26.15}
$$

It belongs to the completed form domain by height approximation.
The variational principle [T, Theorem 4.10] proves (26.3); the same
Fourier decomposition proves simplicity of the ground state. This
derives the gap rather than importing one from a different diffusion.

Finally, omit the zero triple in (26.13). Each remaining frequency
satisfies $\Psi(|\eta|)\ge a^2$. Remove half of its exponential as
$e^{-c a^2t/2}$, and sum the other half by (26.14). For $t\ge a^{-2}$
that sum is bounded. The zero triple is $h_I(t;k_0,k)$, whose sine
series differs from $e^{-\lambda t}\phi(k_0)\phi(k)$ by at most
$C e^{-4\lambda t}$ on $t\ge\tau_{\min}$. After decreasing $c$,
these statements give (26.4). The integer lattice in (26.13) is exactly
the actual $2\pi$ lattice; neither a changed angular Haar mass nor a
noncompact approximation was used. $\square$

## 27. Full-state witnesses at every resolution

**Theorem 27.1 (joint variational lower witnesses).** After a fixed
shrink of the same two-sided neighbourhood, there exist $c,C_0>0$ and,
for every $0<|\kappa|\le\kappa_*$ and $\tau\ge\tau_{\min}$,
a real normalized $f_{\kappa,\tau}\in C_c^\infty(\Omega)$ such that

$$
\begin{aligned}
T_\kappa[f_{\kappa,\tau}]&\le C_0,\\
\int V_{\kappa,\tau}|f_{\kappa,\tau}|^2d\mu
 &\ge c e^{-\lambda\tau}
              \left(1+\frac1{|\kappa|\sqrt\tau}\right).
\end{aligned}
\tag{27.1}
$$

These are actual full-domain witnesses for the original point-generated
field. They remain valid when the cutoff depends arbitrarily on the
parameter, including in the circle-mixing range.

Proof. Fix a compact interval $J\Subset I$ with nonempty interior.
The killed height kernel satisfies

$$
h_I(t;k_0,k)\ge c_J e^{-\lambda t}
\quad(t\ge\tau_{\min},\ k\in J).
\tag{27.2}
$$

To verify uniformity in time, use its strictly positive continuous
kernel on a compact time interval, and then its sine series: the leading
term is $e^{-\lambda t}\phi(k_0)\phi(k)$, with a positive minimum on
$J$, while the remaining terms are $O(e^{-4\lambda t})$. Thus (27.2)
uses the same two absorbing height faces and the same clock.

Integrate out both visible angles, rather than assume an independent
hidden driver. Proposition 16.2 gives the original real hidden lift

$$
\delta_t=\sqrt2\kappa\int_0^t b_\kappa(K_s)dB_s^2.
\tag{27.3}
$$

The same $B^2$ drives the visible angles. Conditional on the entire
height path, which depends only on the independent $B^1$, its hidden
variance is $2\kappa^2\mathcal A_t$, where

$$
\mathcal A_t=\int_0^t b_\kappa(K_s)^2ds,
\qquad m^2t\le\mathcal A_t\le M^2t
\quad\hbox{on }\{\zeta>t\}.
\tag{27.4}
$$

These deterministic bounds hold on that very surviving path; they do
not combine different realizations. The conditional characteristic
function follows by the Gaussian stochastic integral with the now
fixed integrand. On reducing $\delta_t$ modulo its actual $2\pi$
period, its conditional density is

$$
G_{\kappa^2\mathcal A_t}(D),\qquad
G_s(D)=\frac1{\sqrt{4\pi s}}
 \sum_{r\in\mathbb Z}e^{-(D+2\pi r)^2/(4s)}.
\tag{27.5}
$$

This is a conditional formula for the original law, not a new clock,
a new source, or a new diffusion input. In particular the exact visible
integral is

$$
\begin{aligned}
M_\kappa(t;k,D)
&:=\int_{\mathbb T^2}p_\kappa(t,o,(k,\theta,v,D))d\theta dv\\
&=h_I(t;k_0,k)\,
 \mathbb E\!\left[G_{\kappa^2\mathcal A_t}(D)
        \mid K_t=k,\ \zeta>t\right].
\end{aligned}
\tag{27.6}
$$

Disintegration is with respect to the killed height endpoint measure.
It holds almost everywhere, which suffices for all following integrals.
It is obtained by integrating the joint transition law, not by multiplying
independent visible and hidden densities.

Put $a=|\kappa|$, $r_\tau=\min(1,a\sqrt\tau)$, and fix
$0<\eta_0<1/4$. If $a\sqrt\tau\le1$, then for
$t\in[\tau,\tau+1]$ the variance parameter $s$ in (27.5) lies between
$m^2a^2\tau$ and $M^2(1+1/\tau_{\min})a^2\tau$.
The single summand with $r=0$ proves
$G_s(D)\ge c/(a\sqrt\tau)$ on $|D|\le\eta_0r_\tau$.
If $a\sqrt\tau\ge1$, instead $s\ge m^2$.
There is a common strictly positive lower bound for $G_s(D)$ for all
$s\ge m^2$ and all $D\in\mathbb T$: on any bounded positive time
interval use the positive periodized Gaussian, and for large $s$ use
its Fourier series
$(2\pi)^{-1}\sum_{j\in\mathbb Z}e^{-j^2s}e^{ijD}$,
whose coefficients are obtained by a Gaussian integral over the
periodized real line.
Together these facts and (27.2) give

$$
M_\kappa(t;k,D)\ge c e^{-\lambda t}
       \left(1+\frac1{a\sqrt\tau}\right)
\tag{27.7}
$$

for $t\in[\tau,\tau+1]$, $k\in J$ and
$|D|\le\eta_0r_\tau$. All constants are independent of $\kappa,\tau$.
This lower estimate already includes every hidden winding in the
large-time case.

Choose real $\chi\in C_c^\infty(\operatorname{int}J)$ and
$F\in C_c^\infty((-\eta_0,\eta_0))$ with
$\int_I\chi^2dk=\int_{\mathbb R}F^2dx=1$.
For the actual representative $D\in(-\pi,\pi)$ set

$$
f_{\kappa,\tau}(k,\theta,v,D)=
 \frac1{2\pi}\chi(k)r_\tau^{-1/2}F(D/r_\tau).
\tag{27.8}
$$

Extend by zero through the phase seam and periodically. Since
$r_\tau\le1$ and $\eta_0<1/4$, this is smooth on the actual torus
and compactly supported away from the height faces. The raw Jacobian
is $dD=r_\tau dx$; the visible volume is $(2\pi)^2$. Therefore
$\|f_{\kappa,\tau}\|_2=1$ exactly, and direct application of the two
original fields gives

$$
T_\kappa[f_{\kappa,\tau}]
 =\varepsilon^2\|\chi'\|_2^2
  +\frac{a^2}{r_\tau^2}\|F'\|_2^2
                    \int_I b_\kappa^2\chi^2dk\le C_0.
\tag{27.9}
$$

Indeed $a^2/r_\tau^2$ is either $1/\tau\le1/\tau_{\min}$ or
$a^2\le\kappa_*^2$. No isotropic derivative in $D$ was substituted
for $Q_\kappa$.

For their potential expectation, Tonelli gives the exact full-space
identity

$$
\begin{aligned}
\int V_{\kappa,\tau}|f_{\kappa,\tau}|^2d\mu
=\frac1{(2\pi)^2}\int_{I\times\mathbb T}
 \chi(k)^2r_\tau^{-1}F(D/r_\tau)^2
 \left(\int_\tau^\infty M_\kappa(t;k,D)dt\right)dkdD.
\end{aligned}
\tag{27.10}
$$

Use the positive time window $[\tau,\tau+1]$ in this entire field,
then (27.7) and the exact normalization. This proves (27.1).
The trial amplitudes depend on $D$. Their use of a marginal in
(27.10) computes their original full energy; it neither changes the
point source nor identifies the full infimum with a marginal infimum.
The upper estimate in Theorem 26.1, in contrast, holds for every full
state. $\square$

## 28. Necessary and sufficient scales for arbitrary cutoff families

**Theorem 28.1 (complete-state joint stability classification).**
For the fixed data (25.1), take one neighbourhood supplied by Theorems
26.1 and 27.1. There are constants $0<c\le C<\infty$ and
$C_0<\infty$, independent of both parameter signs and all
$\tau\ge\tau_{\min}$, such that for every fixed $g>0$,

$$
\begin{aligned}
R(a,\tau)&=e^{-\lambda\tau}
                   \left(1+\frac1{a\sqrt\tau}\right),&
U(a,\tau)&=1+\frac1{a\sqrt\tau},\\
\lambda-CgR(a,\tau)&\le E_{\rm raw}(\kappa,\tau;g)
 \le\min\{\lambda,C_0-cgR(a,\tau)\},\\
\lambda-CgU(a,\tau)&\le E_{\rm unit}(\kappa,\tau;g)
 \le\min\{\lambda,C_0-cgU(a,\tau)\},& a&=|\kappa|.
\end{aligned}
\tag{28.1}
$$

Let $\tau(\kappa)\ge\tau_{\min}$ be any deterministic family, without
continuity, measurability or monotonicity assumptions. On this fixed
two-sided neighbourhood the complete-state energies have a common
finite lower bound if and only if, respectively,

$$
\begin{array}{ll}
\mathrm{raw}:&
\displaystyle\liminf_{\kappa\to0,\ \kappa\ne0}
 |\kappa|\sqrt{\tau(\kappa)}\,e^{\lambda\tau(\kappa)}>0,\\[4pt]
\mathrm{unit}:&
\displaystyle\liminf_{\kappa\to0,\ \kappa\ne0}
 \kappa^2\tau(\kappa)>0.
\end{array}
\tag{28.2}
$$

A liminf of $+\infty$ satisfies the condition. Failure of either
condition produces a sequence $\kappa_n\to0$ and the actual normalized
states (27.8), at $\tau=\tau(\kappa_n)$, whose corresponding energies
tend to $-\infty$. If the condition fails on only one sign, the sequence
may be chosen on that sign; no regularity across signs is required.

Equivalently, writing $L_a=\log(1/a)$, the sharp raw lower scale is

$$
\tau(\kappa)\ge
 \frac{L_a-\tfrac12\log L_a}{\lambda}-O(1),
\qquad a\downarrow0,
\tag{28.3}
$$

where $O(1)$ means one bounded constant, common to the entire two-sided
family. The unit-charge scale is $\tau(\kappa)\ge c_*/a^2$ eventually
for some fixed $c_*>0$. The assertion is for every fixed positive
coupling; it uses no coupling that shrinks with the parameter.

Proof. First the killed height law gives

$$
c_S e^{-\lambda t}\le S(t)\le C_S e^{-\lambda t}
\qquad(t\ge\tau_{\min}).
\tag{28.4}
$$

For completeness, its sine expansion has a strictly positive first
coefficient and the higher terms decay faster; positivity and continuity
on a remaining compact time interval complete the bounds. The exact
expansion and charge cost are given in (29.1). This is the survival
probability of (25.6), not an assumed unit mass.

Theorem 26.1 and height Poincare prove the raw lower bound in (28.1)
on the complete domain. Theorem 27.1 gives its upper bound with the
same $R$. Dividing the field by (28.4) gives both unit bounds with
$U$. This also retains the exact identity
$E_{\rm unit}(\kappa,\tau;g)=E_{\rm raw}(\kappa,\tau;g/S(\tau))$
at each parameter, but a fixed-coupling fixed-time conclusion alone
would not have supplied the joint estimates.
The test $(2\pi)^{-3/2}\phi(k)$ has free energy $\lambda$ and a
nonnegative attractive expectation, so both energies are at most
$\lambda$. It is admissible by height approximation, and the fields
are bounded at each parameter. This proves all of (28.1).

For an arbitrary family, the first line of (28.2) is precisely eventual
boundedness of $e^{-\lambda\tau}/(a\sqrt\tau)$, and $e^{-\lambda\tau}$
is already bounded. The raw lower estimate thus gives sufficiency.
If it fails, choose a sequence along which
$a\sqrt\tau e^{\lambda\tau}\to0$. Then $R\to\infty$ and (27.8)
has raw energy at most $C_0-cgR\to-\infty$. This proves necessity
by admissible states, not by the failure of a supremum estimate.
Likewise the second line is precisely eventual boundedness of
$1/(a\sqrt\tau)$; its failure gives $U\to\infty$ along a sequence
and the same states give unit energy tending to $-\infty$.

These eventual criteria are equivalent to boundedness on the whole
chosen punctured neighbourhood. Indeed on every annulus
$a\ge a_0>0$, both $R$ and $U$ are bounded solely by
$a_0,\tau_{\min}$, even for an arbitrarily discontinuous or unbounded
time family. Thus no further local uniformity assumption away from zero
is missing. If a scale diverges only along a subsequence, the conclusion
is unboundedness below along that subsequence; it need not be a limit
of the energies along every parameter.

To verify the endpoint in (28.3), the logarithm of the first product
in (28.2) is

$$
\lambda\tau+\tfrac12\log\tau-L_a.
\tag{28.5}
$$

The strictly increasing function $F(t)=\lambda t+\tfrac12\log t$
has derivative at least $\lambda$. Its solution $t_a$ to $F(t_a)=L_a$
satisfies

$$
t_a=\frac{L_a-\tfrac12\log L_a}{\lambda}+O(1).
\tag{28.6}
$$

For example substituting the expression on the right without $O(1)$
leaves $-\tfrac12\log\lambda+o(1)$ in $F(t)-L_a$, and the derivative
bound controls its distance from the root. A common lower bound on
(28.5) implies $\tau\ge t_a-C/\lambda$. Conversely a common bound
$\tau\ge t_a-C'$ bounds (28.5) below, since $t_a\to\infty$ and
$F'$ is bounded above on $[t_a-C',t_a]$. This proves the equivalence,
including families with arbitrarily large times. $\square$

**Proposition 28.2 (distinct stability scales and the mixing endpoint).**
The two interaction conventions have genuinely different stability
criteria. For $a$ sufficiently small let
$\tau(\kappa)=L_a/\lambda$, extending it by $\tau_{\min}$ when
needed. Then

$$
E_{\rm raw}(\kappa,\tau(\kappa);g)\longrightarrow\lambda,
\qquad
E_{\rm unit}(\kappa,\tau(\kappa);g)\longrightarrow-\infty.
\tag{28.7}
$$

For any fixed $b>0$, the family $\tau=b/a^2$ instead has uniformly
bounded unit-charge energies. For
$\tau=(L_a-\tfrac12\log L_a)/\lambda+s$ with fixed real $s$,

$$
R(a,\tau)\longrightarrow\sqrt\lambda\,e^{-\lambda s}.
\tag{28.8}
$$

Thus the logarithmic correction in (28.3) cannot be discarded when
classifying arbitrary families up to bounded energy.

Proof. At $\tau=L_a/\lambda$ one has $e^{-\lambda\tau}=a$,
so $R=a+1/\sqrt\tau\to0$ while $U\to\infty$.
Both conclusions (28.7) follow directly from (28.1), including the
full-state lower bound for the first and normalized witnesses for the
second. At $\tau=b/a^2$ one has $U=1+b^{-1/2}$, which gives the
asserted uniform bound. Finally
$e^{-\lambda\tau}=a\sqrt{L_a}e^{-\lambda s}$ and
$\tau\sim L_a/\lambda$, proving (28.8).
The heat factor in (26.1) is of order $1/(a\sqrt\tau)$ before
mixing and of order one after it; the actual gap (26.3) gives the
same transition scale. $\square$

## 29. Survival cost, potential mass and the actual zero leaf

**Proposition 29.1 (exact source charge and large-cutoff cost).**
Put $\xi_0=\pi(k_0-l)/d_I$ and $C_o=4\sin\xi_0/\pi>0$.
For the same original source and both absorbing height faces,

$$
\begin{aligned}
S(t)&=\frac4\pi\sum_{j=0}^\infty
 \frac{\sin((2j+1)\xi_0)}{2j+1}
 e^{-(2j+1)^2\lambda t},\\
\mathcal M(t):=\int_\Omega V_{\kappa,t}d\mu
&=\frac4{\pi\lambda}\sum_{j=0}^\infty
 \frac{\sin((2j+1)\xi_0)}{(2j+1)^3}
 e^{-(2j+1)^2\lambda t}.
\end{aligned}
\tag{29.1}
$$

In particular these are independent of $\kappa$, and as $t\to\infty$,

$$
S(t)=C_oe^{-\lambda t}(1+O(e^{-8\lambda t})),\qquad
\mathcal M(t)=\frac{C_o}{\lambda}e^{-\lambda t}
                                  (1+O(e^{-8\lambda t})).
\tag{29.2}
$$

The raw effective source charge is $S(t)$; the unit convention has
source charge one and potential mass

$$
\int_\Omega W_{\rm unit}d\mu
 =\mathcal M(t)/S(t)
 =\mathbb E(\zeta-t\mid\zeta>t)
 \longrightarrow1/\lambda.
\tag{29.3}
$$

Every raw-stable family in Theorem 28.1 has $\tau\to\infty$ and

$$
S(\tau(\kappa))\le C a\sqrt{\log(1/a)}
\quad\hbox{eventually}.
\tag{29.4}
$$

For the raw endpoint in (28.8) the more precise cost is

$$
S(\tau)=C_o a\sqrt{L_a}e^{-\lambda s}(1+o(1)).
\tag{29.5}
$$

Every unit-stable family has $\tau\ge b/a^2$ eventually for some
$b>0$, hence $S(\tau)\le C e^{-\lambda b/a^2}$. At the fixed multiple
$\tau=b/a^2$ its exact asymptotic cost is

$$
S(\tau)=C_o e^{-\lambda b/a^2}(1+o(1)).
\tag{29.6}
$$

Proof. Integrating the full free heat law over all three actual phases
leaves the killed height kernel, by (23.8). That scalar kernel, relative
to $dk$, is

$$
h_I(t;k_0,k)=\frac2{d_I}\sum_{n=1}^\infty
 \sin(n\xi_0)\sin\frac{n\pi(k-l)}{d_I}\,e^{-n^2\lambda t}.
$$

For positive time its absolutely convergent sine series can be integrated
in height. The even terms vanish and the odd integrals give the first
line of (29.1). Tonelli for the nonnegative heat kernel gives
$\mathcal M(t)=\int_t^\infty S(r)dr$; integrating the absolutely
convergent series gives its second line. The first omitted odd mode is
$n=3$, with exponent $9\lambda$, proving (29.2). Conditional remaining
lifetime and (25.7)--(25.8) prove (29.3). No angular averaging factor
enters this charge calculation.

Raw stability forces $\tau\to\infty$, since a bounded subsequence of
times makes the product in (28.2) tend to zero. Its equivalent lower
bound (28.3), together with (29.2), gives (29.4).
Substitution gives (29.5). The unit criterion and (29.2) give (29.6)
and its stated upper bound for arbitrary unit-stable families.
Thus raw stabilization at logarithmic times can occur while
$a\sqrt\tau\to0$, because the original source charge has decreased
to the scale of that shrinking width. Division by $S$ removes that
attenuation; bounded unit-charge fields require spreading to a hidden
width bounded away from zero, on the original circle scale. This is a
mathematical comparison of effective source conventions, not a supplied
operation restoring lost particles or preparing a conditioned process.
$\square$

**Proposition 29.2 (marginal and zero-leaf boundaries at moving times).**
The exact marginal and completed-domain identities (23.4)--(23.5)
continue to hold at every moving cutoff. Moreover, uniformly in the
same neighbourhood and all $\tau\ge\tau_{\min}$,

$$
\|\overline V_{\kappa,\tau}\|_\infty\le Ce^{-\lambda\tau},\qquad
\|\overline V_{\kappa,\tau}/S(\tau)\|_\infty\le C.
\tag{29.7}
$$

Thus the energies on the complete $D$-independent sector have a uniform
lower bound for both conventions and every cutoff family, even when the full-state
criterion (28.2) fails. Their effective coupling to the base field
remains $g/(2\pi)$ under the isometry $Jh=(2\pi)^{-1/2}h$.
The actual native zero-parameter leaf is
$I\times\mathbb T_\theta\times\mathbb T_v$ with its own raw measure,
unit source and coupling $g$. Its two regularized conventions have
uniformly bounded fields for all $\tau\ge\tau_{\min}$.

Proof. Integration in $D$ selects $j=0$ in (26.13). Its factor becomes
$(2\pi)^{-2}$, and (26.12)--(26.14), now summed only over $n,m$,
give $\overline p_\kappa(t,q_0,q)\le Ce^{-\lambda t}$.
Time integration and (28.4) prove (29.7). The completed-domain and
same-field energy factors are exactly (23.5), so bounded multiplication
and height Poincare give the sector assertion.

At zero the actual original law has $D=0$ throughout its lifetime,
by (16.8). It is the three-coordinate operator of Definition 23.2;
its Fourier modes involve only $nA_0+mB_0$. The same $j=0$ calculation
therefore proves (29.7) on that actual leaf. It does not construct a
four-dimensional Lebesgue heat density at zero. In particular the
auxiliary four-coordinate operator in Definition 21.1, defined by
resolving $x=D/\kappa$ before taking a coefficient limit, is still a
different comparison object. The full witnesses (27.8) retain a hidden
coordinate for every nonzero parameter and have no implication of
an available projection, amplitude preparation, acquisition procedure,
mean selector or empirical spatial-dimension theorem. $\square$

## 30. Mathematical supplier correspondence for the joint law

**Proposition 30.1 (scoped premises and the joint native conclusion).**
The all-time estimates (26.1)--(26.4), the full-state witnesses
(27.8)--(27.10), and the necessary and sufficient arbitrary-family
criteria (28.2)--(28.3) have the following mathematical dependencies.
The elementary polynomial, Fourier and variational steps in their proofs
are supporting methods; their native joint conclusion is the additional
content, rather than a new general heat or perturbation theorem.

| Supplier | Exact mathematical scope used |
| --- | --- |
| [N, Definitions 2.1, 2.3, 3.1 and 8.1; Theorems 8.2 and 10.3](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md) | Original probabilities, preparations, phase convention, two controls, actual grouped leaves and finite native realization. No physical amplitude preparation follows from finite ray realization. |
| This volume, Propositions 2.1--2.2 and Theorem 3.1 | Completed free forms, killed free heat and compactness at each nonzero parameter, and unregularized full point-field collapse. The collapse is reused, not applied to the regularized multiplier. |
| This volume, (12.7), Proposition 16.2 and §§20--24, at [the published source through §24](https://github.com/the-omega-institute/trureturing/blob/28695dc3c5b8fc9106f1648e021792233e355c31/docs/develop/theory/FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md) | Exact coefficients, common two-driver killed law, effective source equation, original charge and mass identities, fixed-parameter minima, fixed-time inverse-gap estimates, and completed marginal factors. The constants in the fixed-time estimates do not supply the moving-cutoff criterion. |
| [FiniteRectangleTransport](https://github.com/the-omega-institute/trureturing/blob/0bfa84f27ca531cca721a1c90d35ded2a51c0738/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean), including `polygon_admissible`, `horizontal_leg`, `vertical_leg`, `rectangle_chain`, `weight_compatible`, `finite_rectangles_realize` | Finite original probability/phase paths and compatibility. These statements contain no heat kernel, all-time circle gap or attractive-energy classification. |
| Pinned mathlib [BrownianMotion.Basic](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/BrownianMotion/Basic.lean) and [Fourier.AddCircleMulti](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Fourier/AddCircleMulti.lean) | Generic Brownian and Fourier tools, not the native joint conclusion. The latter file uses unit-circle probability Haar measure; (26.13) instead states explicitly the raw $2\pi$ angular factors required here. No formal-library theorem is asserted to certify the ordinary proof. |
| [Observation quotient, Theorem 3.1](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md); [Free diffusion quotient rigidity, §§2--3](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md) | Hidden integration, averaging, source smearing and complete free-domain pullbacks at their stated factors. They do not identify a marginal energy with the full attractive minimum. The present $q$ factor is exactly the one already verified in §23. |
| [Continuation III, Specification 82.7](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md); [Continuation IV, §§100--102](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md) | Bounded truncation and the different finite occurrence-tree screening problem, respectively. Neither supplies the native killed-cylinder moving-time classification. |
| [H] Colin de Verdiere--Hillairet--Trelat, *Small-time asymptotics of hypoelliptic heat kernels near the diagonal, nilpotentization and related results*, Ann. H. Lebesgue 4, 897--971, [DOI 10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf), Theorem B.1, Corollary B.3 and Theorem 3.5 | Literature-attested uniform local smoothing and positive-time parameter continuity used in the published fixed-time supplier. They are not an assumed all-time estimate for the degenerating original torus. The all-time bound here follows from (26.7)--(26.14). |
| [T] G. Teschl, *Mathematical Methods in Quantum Mechanics*, GSM 99, online version February 12, 2009, [author text](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorems 5.11, 6.24 and 4.10 | Literature-attested Trotter domination for each bounded scalar nonnegative potential, bounded form perturbation after the actual multiplier is bounded, and min-max. None supplies the native parameter/time constants without the coefficient and source calculations. |

Proof. The original contract and the fixed-time source/domain results
are the cited published premises. Formula (26.7) verifies the specific
uniform polynomial nondegeneracy needed for (26.6), including the resolved
coefficient at zero without introducing a zero-parameter four-dimensional
law. The actual Fourier lattice then yields both the joint full-space
supremum and the native circle gap, with its large-time constant mode.
The same killed height path and the same $B^2$ in (27.3) yield the hidden
marginal estimate, from which exactly normalized original full-domain
states have bounded kinetic energy and the matching potential expectation.
Their combination proves necessity as well as sufficiency in (28.2).
The sine expansion independently fixes the charge cost and distinguishes
it from field mass. Thus the all-time native classification is a
repository-derived ordinary mathematical result with the stated mature
attribution, not a literature-priority claim or a physical selection
mechanism. $\square$

## 追加锚（本行以下为增补区）

## 31. Complete free traces and the resolved density

**Definition 31.1 (trace, fibres and independent constants).**
Retain exactly Definition 25.1, including fixed $\varepsilon>0$, both
height deaths, raw $2\pi$ phase measures, completed free domain and clock.
Write $a=|\kappa|$, $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$ and

$$
\begin{aligned}
Z_\kappa(t)&=\operatorname{Tr}e^{-tL_\kappa},\\
T_\kappa(t;n,m,\xi)&=\operatorname{Tr}_{L^2(I,dk)}
 e^{-tH_{\kappa,(n,m,\xi)}},\\
F(t)&=\sum_{n,m\in\mathbb Z}\int_{\mathbb R}
                    T_0(t;n,m,\xi)\,d\xi,\\
\beta&=\int_I b_0(k)^2\phi(k)^2\,dk>0,\qquad
\Theta_\beta(z)=\sum_{j\in\mathbb Z}e^{-\beta zj^2}.
\end{aligned}
\tag{31.1}
$$

The fibres are precisely (26.5), with scalar form domain $H_0^1(I)$.
The coefficient $\beta$ is the one in
[Critical cutoff, Definition 31.1 and (32.4)](FIB_NATIVE_CRITICAL_CUTOFF_SPECTRAL_LIMITS.md),
not an additional adjustable coefficient. On $\mathbb R^4$ with raw
Lebesgue measure define the canonical operator and its heat constant by

$$
\mathcal E=-\left[\partial_r^2+
 (\partial_y+r\partial_z+\tfrac12r^2\partial_w)^2\right],
\qquad c_E=p_{\mathcal E}(1;0,0)>0.
\tag{31.2}
$$

Here $\mathcal E$ is the Friedrichs realization of its compactly
supported smooth-core form. Its complete homogeneous bracket-generating
fields give a finite smooth positive heat density; this is the
nilpotent heat kernel in [H, Theorems A and B]. Its normalization is
$e^{-t\mathcal E}$, with no factor $1/2$ in the generator. Set

$$
C_7=(2\pi)^3\varepsilon^{-4}
                 \frac{H(u^4-l^4)}2\,c_E>0.
\tag{31.3}
$$

**Theorem 31.2 (all-mode fixed-clock limit and exact density factor).**
For every $t>0$ and all sufficiently small nonzero $\kappa$,
$Z_\kappa(t)<\infty$, and
$0<F(t)<\infty$. Through either sign of $\kappa\to0$,

$$
aZ_\kappa(t)\longrightarrow F(t)
\tag{31.4}
$$

uniformly on every compact subinterval of $(0,\infty)$.
The resolved real-$x$ cover of Definition 21.1 at $\kappa=0$ has
trace density per unit raw $x$ length exactly $F(t)/(2\pi)$.

Proof. Let $E_{\kappa,h}(\eta)$, $h\ge1$, denote every scalar height
eigenvalue, in increasing order. Scalar min-max and (26.6) give
$E_{\kappa,h}\ge\lambda h^2$ and
$E_{\kappa,h}\ge\lambda+c\Psi(|\eta|)$. Averaging these bounds yields

$$
T_\kappa(t;n,m,\xi)\le
 e^{-\lambda t}S(t)e^{-ct\Psi(\sqrt{n^2+m^2+\xi^2})/2},\qquad
S(t)=\sum_{h\ge1}e^{-\lambda t(h^2-1)/2}.
\tag{31.5}
$$

This estimate includes every height level, is uniform on the closed
small parameter interval including zero, and holds for all $t>0$.
The right side is summable in $(n,m)$ and integrable in $\xi$ on each
positive compact time interval. The exact completed-domain Fourier
sum in (26.13) therefore gives the trace-class identity

$$
Z_\kappa(t)=\sum_{n,m,j\in\mathbb Z}
                      T_\kappa(t;n,m,\kappa j).
\tag{31.6}
$$

For bounded $(n,m,\xi)$ the scalar potentials converge uniformly as
$\kappa\to0$. Min-max bounds the change of every height eigenvalue
by the supremum change of the potential. The lower bound $\lambda h^2$
then gives locally uniform convergence of the scalar traces, also in
$t$ on positive compact intervals. On a bounded frequency box the
Riemann sums $a\sum_j$ converge to $\int d\xi$, uniformly in these
$t$; the sign reverses the lattice without changing the sum.
For the complement use (31.5) and
$\Psi(|\eta|)\ge[\Psi(|n|)+\Psi(|m|)+\Psi(|\xi|)]/3$.
Integral comparison of the decreasing last factor bounds its weighted
lattice tails uniformly for $0<a\le1$; the first two factors have
summable tails. Thus box removal is uniform, proving (31.4).

Fourier transformation of the smooth core and then form closure give
the cover as the direct integral of these same Dirichlet fibres.
On the cover, the two visible orthonormal modes have factor $(2\pi)^{-1}$,
and the real Fourier transform has inverse measure $d\xi/(2\pi)$.
Consequently its diagonal kernel, integrated over $I\times\mathbb T^2$
at any fixed $x$, is $F(t)/(2\pi)$. Equivalently the exact quotient
length is $2\pi/a$, and $a$ times that length is $2\pi$.
These factors follow from the raw measures, not normalized Haar
measure. Positivity follows, for example, from the positive scalar
trace on $n=m=0$ and any bounded nonempty $\xi$ interval. $\square$

## 32. A joint short-time law with both absorbing faces

**Theorem 32.1 (joint wall and short-time trace).**
For every simultaneous $\kappa\to0$, $t\downarrow0$, without any
relation between $a$ and $t$, and for both signs,

$$
a t^{7/2}Z_\kappa(t)\longrightarrow C_7.
\tag{32.1}
$$

Moreover $t^{7/2}F(t)\to C_7$ as $t\downarrow0$.

Proof. Choose fixed intervals $\overline I\subset J\Subset(0,H)$
with positive margins, and a closed two-sided parameter interval so
all original probabilities remain positive on $\overline J$.
By (21.7), after shrinking that parameter interval once,

$$
D_\kappa(s)=\det(c_\kappa(s),c_\kappa'(s),c_\kappa''(s)),\qquad
\inf_{\kappa,s\in\overline J}|D_\kappa(s)|>0,
\quad D_\kappa(s)=-\frac{H^2-\kappa^2}
 {2H^3(s-\alpha_\kappa)^3},
\quad D_0(s)=-\frac1{2Hs^3}.
\tag{32.2}
$$

For the determinant formula, put the three coefficients over the common
denominator $2H(s-\alpha_\kappa)$. The determinant of their constant,
linear and quadratic coefficient rows is $-2(H^2-\kappa^2)$;
differentiating twice gives the additional factor two, while the
derivatives of the common denominator cancel in the alternating
determinant. All derivatives are bounded on a slightly larger rectangle.
Unwrap all
three resolved phase coordinates, writing $q\in\mathbb R^3$, and let
$g_\kappa^U(t;s,s';q)$ be the killed kernel on $U\times\mathbb R^3$
for $U=I,J$, with raw $ds\,dq$, generator
$\varepsilon^2\partial_s^2+(c_\kappa(s)\cdot\partial_q)^2$.
We first establish the uniform local estimate actually needed:

$$
t^{7/2}g_\kappa^J(t;s,s;0)\longrightarrow
 \frac{c_E}{\varepsilon^4|D_\kappa(s)|}
\quad\text{uniformly for }(\kappa,s)\in[-\kappa_*,\kappa_*]\times[l,u].
\tag{32.3}
$$

Here is a parameter-uniform justification, rather than an appeal to
positive-time continuity in unscaled coordinates. Put $h=\sqrt t$ and,
centering the pole at $(s,0)$, make the linear privileged change

$$
s'=s+\varepsilon h r,\qquad
q=h c_\kappa(s)y+\varepsilon h^2c_\kappa'(s)z
                       +\varepsilon^2h^3c_\kappa''(s)w.
\tag{32.4}
$$

Its absolute Jacobian is $\varepsilon^4|D_\kappa(s)|h^7$.
The rescaled generator is $\partial_r^2+(v_{\kappa,s,h}(r)
\cdot\partial_{y,z,w})^2$, where Taylor expansion in this basis gives

$$
v_{\kappa,s,h}(r)\longrightarrow(1,r,r^2/2)
\quad\text{in }C^\infty\text{ on every bounded }r\text{ interval},
\tag{32.5}
$$

uniformly in $(\kappa,s)$. The inverse basis matrices are uniformly
bounded by (32.2). The rescaled height is $\sqrt2 B^1$ and the three
rescaled phase increments are $\sqrt2\int v_{\kappa,s,h}
(\sqrt2B^1_\tau)dB^2_\tau$, in unit rescaled time.
Stop first when $|\sqrt2B^1_\tau|$ reaches $R$. The stopped stochastic
integrals converge uniformly in probability, by the Itô isometry and
(32.5). The complementary probability is the ordinary Brownian
supremum tail, uniformly in the parameters. Killing at $\partial J$
has probability tending to zero because its rescaled height distance
is at least a fixed positive constant divided by $h$. Thus the
rescaled transition measures converge weakly to the canonical ones,
for every convergent parameter sequence and every fixed positive time.

To upgrade this statement to densities at unit time, use
Colin de Verdière--Hillairet--Trélat, *Small-time asymptotics of
hypoelliptic heat kernels near the diagonal, nilpotentization and
related results*, [DOI 10.5802/ahl.93](https://doi.org/10.5802/ahl.93),
[H, Theorem B.1 and Corollary B.3] on fixed rescaled space-time boxes. The limiting
fields $\partial_r$, $\partial_y+r\partial_z+(r^2/2)\partial_w$ and
their brackets have determinant one. By (32.5) the fields on every
such box satisfy one uniform strong Hörmander condition of step three,
with bounded coefficient derivatives. They are divergence free, have
zero potential and drift, smooth constant positive density, and
selfadjoint sub-Markov realizations. Their kernel measures have total
mass at most one. On a compact positive-time box this bounds the
initial distribution in a fixed negative Sobolev norm, by dual Sobolev
embedding. The local parabolic subelliptic estimate, with nested
cutoffs, iterates to uniform bounds on all derivatives on smaller
boxes, exactly the smoothing argument of (21.8)--(21.9).
Weak convergence and compactness in these norms identify the unique
smooth limit as $p_{\mathcal E}$. At unit time and the origin this
proves (32.3), including uniformity: any contrary parameter sequence
has a convergent subsequence and the same limiting argument.
This is the leading nilpotent mechanism of [H, Theorem B], with the
compact parameters and rescaled mass initialization explicitly retained.

For $s$ in any fixed closed subinterval of $I$, the identical argument
applies to $g_\kappa^I$. For all $s\in I$, domain domination and (32.3)
on the larger interval give instead the uniform bound

$$
0\le g_\kappa^I(t;s,s;0)\le g_\kappa^J(t;s,s;0)
                                  \le C t^{-7/2}\quad(0<t\le t_0).
\tag{32.6}
$$

Both endpoints are therefore controlled even though a local interior
expansion is not asserted uniformly at the absorbing faces.
Alternatively their interior agreement follows from the uniform
localization theorem [H, Theorem 3.2, p.921]: common smooth fields and density,
uniform brackets, fixed interior margins, and selfadjoint contraction
semigroups are its hypotheses here. No boundary asymptotic is imported.

It remains to control every winding, including visible windings.
Condition on a height Brownian bridge from $s$ to $s$ in time $t$,
and retain its event of survival in $U$. The phase law is centered
Gaussian with covariance $2M$, where

$$
M=\int_0^t c_\kappa(K_\tau)c_\kappa(K_\tau)^{\mathsf T}d\tau,
\qquad 0<M\le M_0t\,\mathrm{Id}.
\tag{32.7}
$$

It is positive definite almost surely: the bridge is nonconstant,
its range contains an interval, and (26.7) forbids a nonzero linear
combination of $c_\kappa$ vanishing on an interval. Its Gaussian density
is $(4\pi)^{-3/2}(\det M)^{-1/2}e^{-q^{\mathsf T}M^{-1}q/4}$.
The upper covariance bound holds on the same survived path, so taking
bridge expectations gives the exact useful comparison

$$
0\le g_\kappa^U(t;s,s;q)\le
 e^{-|q|^2/(4M_0t)}g_\kappa^U(t;s,s;0).
\tag{32.8}
$$

These formulas hold first as Gaussian-mixture densities; smoothness
identifies them pointwise. Finite inverse-determinant expectation at
$q=0$ follows as well from the finite smooth kernel: Gaussian mixtures
are bounded above by their value at zero, and Fatou along points tending
to zero bounds that value by the continuous kernel's value.

Projecting the same killed process onto periods $(2\pi,2\pi,2\pi/a)$
now gives, by nonnegative periodization and the exact unitary (21.3),

$$
aZ_\kappa(t)=(2\pi)^3\int_I
 \sum_{n,m,j\in\mathbb Z}
 g_\kappa^I(t;s,s;(2\pi n,2\pi m,2\pi j/a))\,ds.
\tag{32.9}
$$

For $0<a\le1$, every nonzero lattice vector here has length at least
$2\pi$, and (32.8) bounds the sum of its exponentials by
$Ce^{-c/t}$ for $t\le t_0$, independently of $a$. Equations
(32.6)--(32.9) therefore control the entire winding sum, not a finite
truncation. In particular its nonzero part, multiplied by $t^{7/2}$,
is uniformly $O(e^{-c/t})$ after height integration.

For a fixed $\delta>0$, integrate the uniform local limit on
$[l+\delta,u-\delta]$. The two remaining height strips have total
contribution at most $C\delta$ by (32.6), also after periodization;
the limiting integrand has the same bound by (32.2). Let $t\downarrow0$
and then $\delta\downarrow0$. This proves the stronger uniform estimate

$$
\sup_{0<|\kappa|\le\kappa_*}
\left|a t^{7/2}Z_\kappa(t)
 -(2\pi)^3c_E\varepsilon^{-4}\int_l^u\frac{ds}{|D_\kappa(s)|}
\right|\longrightarrow0.
\tag{32.10}
$$

Continuity of the determinant and (32.2) give (32.1), since
$\int_l^u2Hs^3ds=H(u^4-l^4)/2$.
For $F$, Fourier inversion in Theorem 31.2 gives

$$
F(t)=(2\pi)^3\int_I\sum_{n,m\in\mathbb Z}
                          g_0^I(t;s,s;(2\pi n,2\pi m,0))\,ds.
\tag{32.11}
$$

The same proof applies, with only the two visible winding indices.
Thus its small-time coefficient is exactly $C_7$. Neither conclusion
uses an exchange of an ordered wall limit with a short-time limit.
All covariances in this proof are twice the form coefficients; the
factor $\varepsilon^4$, the three raw $2\pi$ factors and the original
clock are fixed by (32.4), (32.7), and (32.9). $\square$

## 33. Full mixing and simultaneous intermediate clocks

**Theorem 33.1 (complete circle-mixing trace).**
For every $0<z_0<z_1<\infty$, through both signs,

$$
\sup_{z\in[z_0,z_1]}
\left|e^{\lambda z/a^2}Z_\kappa(z/a^2)-\Theta_\beta(z)\right|
\longrightarrow0.
\tag{33.1}
$$

Proof. The perturbation supplied by [Critical cutoff, (32.4)] for the
visible zero block is

$$
\Lambda_\kappa(q)=\lambda+\beta_\kappa q^2+O(q^4),\qquad
\beta_\kappa=\int_I b_\kappa^2\phi^2\,dk\longrightarrow\beta,
\tag{33.2}
$$

uniformly near $q=0$. We use its eigenvalue, not its fixed-pole
kernel coefficient. In a trace each normalized scalar eigenfunction
contributes one, so no $\phi(k_0)$ or source charge can occur.
For each fixed $j$, (33.2) with $q=\kappa j$ gives the limiting first
height contribution $e^{-\beta zj^2}$ uniformly on $[z_0,z_1]$.
All higher height contributions vanish there: their eigenvalues are
at least $\lambda h^2$, $h\ge2$.

To justify the complete sum, note that for $a\le1$,
$\Psi(a|j|)/a^2\ge\Psi(|j|)$. Equation (31.5) therefore bounds the
compensated visible zero trace by $Ce^{-c z_0\Psi(|j|)/2}$, a summable
sequence. This also dominates its higher height part, whose individual
$j$ limits are zero. The nonzero visible blocks obey, by (31.5) and
exactly the separation used in (26.14), for $t\ge1$,

$$
e^{\lambda t}\sum_{(n,m)\ne(0,0),j}
 T_\kappa(t;n,m,\kappa j)
 \le Ce^{-dt}(1+(a\sqrt t)^{-1}),\qquad d>0.
\tag{33.3}
$$

This tends to zero uniformly at $t=z/a^2$. Uniform dominated summation
proves (33.1). The scalar estimate is the bounded selfadjoint
multiplication perturbation with a uniform isolated height ground;
its derivation and classical attribution are those of the cited
(32.4), with both Dirichlet faces unchanged. $\square$

**Theorem 33.2 (simultaneous intermediate equivalent and endpoints).**
On every path $\kappa\to0$, $t\to\infty$, $a^2t\to0$, with either sign,

$$
Z_\kappa(t)\sim
 e^{-\lambda t}\frac{\sqrt{\pi/\beta}}{a\sqrt t}.
\tag{33.4}
$$

The limiting cover expression and theta function have endpoints

$$
\begin{aligned}
F(t)&\sim C_7t^{-7/2} &&(t\downarrow0),\\
F(t)&\sim e^{-\lambda t}\sqrt{\pi/\beta}\,t^{-1/2}
                                                    &&(t\to\infty),\\
\Theta_\beta(z)&\sim\sqrt{\pi/(\beta z)} &&(z\downarrow0),\\
\Theta_\beta(z)&=1+2e^{-\beta z}+O(e^{-4\beta z}) &&(z\to\infty).
\end{aligned}
\tag{33.5}
$$

Proof. Put $r=a\sqrt t\to0$. The nonzero visible part times
$r e^{\lambda t}$ tends to zero by (33.3), independently of the
relative rates. In the remaining blocks put $x_j=rj$, so
$q^2=x_j^2/t$. On $|x_j|\le R$, (33.2) gives, uniformly,

$$
t(\Lambda_\kappa(\kappa j)-\lambda)
 =\beta_\kappa x_j^2+O(R^4/t)\longrightarrow\beta x_j^2.
\tag{33.6}
$$

The compensated sum of all heights above the first on this set is
at most $C e^{-3\lambda t}$ per $j$, using
$E_h\ge\lambda h^2$; its $r$-weighted sum tends to zero.
Since $r$ times the number of these lattice points is bounded,
(33.6) reduces the central sum to the Gaussian Riemann sum.
For $|x_j|>R$ and $a|j|\le1$, (31.5) bounds the $r$-weighted
trace by the lattice Gaussian tail $Cr\sum_{|rj|>R}e^{-c(rj)^2}$,
which is uniformly small as $R\to\infty$, along $r\to0$.
For $a|j|>1$, integral comparison bounds the remaining sum by

$$
Cr e^{-ct}+C\sqrt t\int_1^\infty e^{-ct x^{2/3}}dx\longrightarrow0.
\tag{33.7}
$$

Thus $r e^{\lambda t}Z_\kappa(t)\to
\int_{\mathbb R}e^{-\beta x^2}dx=\sqrt{\pi/\beta}$, proving (33.4)
with its simultaneous quantifiers and every height retained.
For the large-$t$ law of $F$, the same argument uses the continuous
variable $x=\sqrt t\,\xi$ at $\kappa=0$; (31.5) gives exactly the
same tails and visible suppression. Its small-$t$ law was proved
in Theorem 32.1. Finally elementary Fourier coefficients of the
periodized Gaussian give

$$
\Theta_\beta(z)=\sqrt{\frac\pi{\beta z}}
       \sum_{h\in\mathbb Z}e^{-\pi^2h^2/(\beta z)}.
\tag{33.8}
$$

This proves the small-$z$ endpoint, with exponentially small relative
error; the original theta series gives the large-$z$ endpoint.
In particular substituting $z=a^2t$ matches the intermediate
coefficient but does not prove (33.4); its uniform tail proof above
does. Positive-time parameter continuity alone also does not supply
these joint limits: [H, the remark following Theorem 3.5] gives the
explicit elliptic-to-contact counterexample with different short-time
powers. Here the resolved fields remain uniformly of step three,
and (32.6)--(32.10) and (33.3)--(33.7) supply the additional global
controls. All displayed large-time equivalents retain the height death
factor $e^{-\lambda t}$. $\square$

## 34. The four comparison objects and the weight omitted by a quotient

**Theorem 34.1 (complete quotient weight and distinct zero objects).**
Let $\overline L_\kappa$ be the complete $j=0$ free operator on
$B=I\times\mathbb T_\theta\times\mathbb T_v$ with raw measure, and
put $\overline Z_\kappa(t)=\operatorname{Tr}e^{-t\overline L_\kappa}$.
For small nonzero $\kappa$ it is the reducing sector under
$Jh=(2\pi)^{-1/2}h$, not the full operator. Uniformly on positive
compact time intervals,

$$
\begin{aligned}
\overline Z_\kappa(t)&\longrightarrow Z_{\rm leaf}(t)
 :=\operatorname{Tr}e^{-t\overline L_0}<\infty,\\
a[Z_\kappa(t)-\overline Z_\kappa(t)]&\longrightarrow F(t),\qquad
\frac{\overline Z_\kappa(t)}{Z_\kappa(t)}
 \sim a\frac{Z_{\rm leaf}(t)}{F(t)}.
\end{aligned}
\tag{34.1}
$$

At the mixing clock, uniformly on compact positive $z$ intervals,

$$
\begin{aligned}
e^{\lambda z/a^2}\overline Z_\kappa(z/a^2)&\longrightarrow1,\\
e^{\lambda z/a^2}[Z_\kappa(z/a^2)-\overline Z_\kappa(z/a^2)]
 &\longrightarrow\Theta_\beta(z)-1,\\
\frac{Z_\kappa(z/a^2)-\overline Z_\kappa(z/a^2)}{Z_\kappa(z/a^2)}
 &\longrightarrow1-\Theta_\beta(z)^{-1}.
\end{aligned}
\tag{34.2}
$$

On every intermediate path of Theorem 33.2 the omitted trace is
asymptotic to the full trace, while
$\overline Z_\kappa(t)\sim e^{-\lambda t}$.
The actual zero leaf has direct rank two and homogeneous heat dimension
four. The resolved real-$x$ cover has finite positive trace density
$F(t)/(2\pi)$, homogeneous heat dimension seven, and infinite total
positive-time trace. The enlarged four-coordinate operator at zero,
with $D$ frozen and unchanged raw $dD$, has infinite multiplicity and
infinite positive-time trace. These are distinct realizations.

Proof. The completed free reduction and its exact isometry are
(23.5), (26.13), and
[Observation quotient, (10.7)](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md).
Thus $\overline Z_\kappa=\sum_{n,m}T_\kappa(t;n,m,0)$ exactly.
Equation (31.5) gives the complete summable dominator, and scalar
min-max convergence gives its first limit in (34.1). Theorem 31.2
then gives the other two, with positive continuous limiting functions.
The constant block has spectrum $\lambda h^2$; the nonzero visible
blocks have a uniform positive bottom gap above $\lambda$ by (26.6).
Consequently, uniformly in small $\kappa$, for $t\ge1$,

$$
e^{\lambda t}\overline Z_\kappa(t)=1+O(e^{-dt})
\tag{34.3}
$$

for a fixed $d>0$, by (31.5). Combine this with Theorems 33.1 and
33.2 to obtain (34.2) and the intermediate assertions. There is no
factor $2\pi$ in a sector trace: $J$ is an isometry and preserves
multiplicities. The factor $1/(2\pi)$ in the cover density instead
comes from continuous Fourier inversion and its noncompact length.

At $\kappa=0$ the actual original motion has $D=0$ throughout,
as in Proposition 29.2; its leaf operator is $\overline L_0$ on $B$.
Its finite trace has just been proved, and its rank and $Q=4$ are the
existing native conclusions of
[N, Theorem 10.3](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md),
not new dimension claims. Resolving $x=D/\kappa$ before the limit
instead gives $c_0\cdot\partial_{\theta,v,x}$, with the nonzero
$x$ coefficient $b_0$ and determinant (32.2). Its local $Q=7$ is the
resolved version of the existing step-three flag; Theorems 31.2 and
32.1 supply its finite trace density and coefficient. Translation
invariance in $x$ makes its diagonal integral over the entire real
line infinite. More intrinsically, compressing its heat operator to
$|x|<R$ has trace $2R F(t)/(2\pi)$, which increases without bound.

Finally retaining all four coordinates while merely setting
$\kappa=0$ in the unrescaled operator gives
$\overline L_0\otimes\mathrm{Id}_{L^2(\mathbb T_D,dD)}$.
Every eigenvalue of $\overline L_0$ then has the countably infinite
multiplicity of the frozen $D$ Fourier modes; the heat trace diverges
for every $t>0$. It is neither the actual zero leaf nor the resolved
cover. In all four objects the supplied instantaneous controls have
rank two. None of these trace identities changes that rank, supplies
an elliptic Euclidean three-dimensional diffusion, or identifies the
full spectrum with physical Euclidean space. In particular $Q=4$ and
$Q=7$ concern the stated horizontal operators and measures, rather
than a count of physical spatial axes. $\square$

## 追加锚（本行以下为增补区）

## 35. Variable-coefficient fixed-model companion

The complete smooth-density/SPD-covariance double-wall extension, its
fixed-model weak-coupling iff, and its finite large-coupling collapse
obstruction are proved in [the native variable-coefficient companion](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md).

## 追加锚（本行以下为增补区）
