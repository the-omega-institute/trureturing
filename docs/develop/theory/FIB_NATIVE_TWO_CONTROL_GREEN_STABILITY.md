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
