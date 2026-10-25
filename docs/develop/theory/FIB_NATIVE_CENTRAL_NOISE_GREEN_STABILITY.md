# Native central-noise full Green propagation and attractive stability

> This companion uses the generic-v1 definition/theorem/proof shape.
> Published bytes are preserved; extensions follow the final append anchor.
> All proofs below are ordinary mathematical proofs, without Lean certification.

## 1. Fixed source, conditional law and the matched operator

**Definition 1.1 (source and supplier correspondence).** All repository
references in this volume are fixed at
797e634f2e07a0d2f6bcafbd76b21ecf628e1a8a. Write N for
[Probability, phase transport and holonomy](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md),
K for [Guarded lift limits](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md),
O for [Paid-point observation tracking](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md),
V for [Variable-coefficient Green stability](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md),
and G for [Two-control Green stability](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md).
Use N's original full-support double-wall source, as specified in K,
Definitions 2.1–2.2 and 11.1–11.2. In particular, fix
$0<Z<1$, $r=1-Z$, $H=r/2$, $X=Y=H$ and
$I=(l,u)\Subset(0,H)$, with arbitrary fixed preparation phases.
The probabilities in mode order $(0,1,2,3,13)$ are
$(k,H-k,Z,H-k,k)$ and the convention is
$\psi_s=\sqrt{p_s}e^{-i\theta_s}$.
The grouped increment coordinates give the actual source
$\Omega=I\times\mathbb T^2$, where both circles have period $2\pi$.
Preparation phases are not required to agree when increments agree.
Fix any interior pole $o=(k_o,\alpha_o,\beta_o)$.
If a preliminary history reaches this pole from the immutable initial
preparation, its original legality and resources remain separate charges.

Set raw density $\rho=1$, horizontal covariance matrix $A=I_2$, and

$$
d\mu=dk\,d\alpha\,d\beta,\qquad
P=\partial_k,\quad Q=\tfrac12\partial_\alpha+c(k)\partial_\beta,
\quad c(k)=\tfrac12-k/r,\quad Z_c=-r^{-1}\partial_\beta.
\tag{1.1}
$$

The measure is not probability-normalized. The subscript on $Z_c$
distinguishes a central vector field from the fixed probability $Z$.
For any fixed $\nu\ne0$, put $\epsilon=|\nu|$.
On one persistent probability space take the independent covariance-$2$
Brownian motions $W^1,W^2,C$ of K, Definition 33.1, and specialize its
area drift to $\lambda=0$:

$$
\begin{aligned}
J_t&=\int_0^t W^1_s\,dW^2_s+\nu C_t,&
\tau&=\inf\{t:k_o+W^1_t\notin I\},\\
q_t&=\bigl(k_o+W^1_t,\,
 [\alpha_o+W^2_t/2],\,
 [\beta_o+c(k_o)W^2_t-J_t/r]\bigr),\quad t<\tau .
\end{aligned}
\tag{1.2}
$$

Use the held boundary state after $\tau$ when a held path is needed,
and the isolated cemetery for the killed path. Restriction to
$[0,T]$ is exactly K's target with $S=T\wedge\tau$.
The Brownian law and independent central covariance are supplied analytic
premises. They are not deductions from bare FIB or a third primitive
command. In particular, the ordinary finite-command chronology is still
$j=\int a\,db$, with no free central input.

**Definition 1.2 (one kinetic operator and its own field).** For
$\epsilon>0$, define the closed form and its domain by

$$
T_\epsilon[f]=\|Pf\|_2^2+\|Qf\|_2^2+\epsilon^2\|Z_cf\|_2^2,\qquad
\mathcal F_\epsilon=\overline{C_c^\infty(\Omega)}
 ^{(\|\cdot\|_2^2+T_\epsilon)^{1/2}} .
\tag{1.3}
$$

Here $C_c^\infty(\Omega)$ is periodic in the actual phases, with compact
height support. Each fixed $\epsilon>0$ gives precisely the periodic
$H^1$ domain with zero trace at the two height faces. At $\epsilon=0$
use the horizontal closure $\mathcal F_0$, not an asserted isotropic
$H^1$ domain. The associated positive operator is

$$
\begin{aligned}
L_\epsilon&=-(P^2+Q^2+\epsilon^2Z_c^2)_{F,\Omega},\\
D(L_\epsilon)&=\{f\in\mathcal F_\epsilon:
 \exists F\in L^2(\mu),\
 T_\epsilon(f,v)=\langle F,v\rangle\ (\forall v\in\mathcal F_\epsilon)\}.
\end{aligned}
\tag{1.4}
$$

Its clock is $H^\epsilon_t=e^{-tL_\epsilon}$ without retiming.
Write $p^\Omega_\epsilon(t,o,q)$ for its kernel relative to $d\mu$ and set

$$
\Gamma_{\epsilon,o}(q)=\int_0^\infty
 p^\Omega_\epsilon(t,o,q)\,dt,\qquad
V_\epsilon[f]=\int_\Omega\Gamma_{\epsilon,o}|f|^2\,d\mu,\qquad
q_{\epsilon,g}=T_\epsilon-gV_\epsilon,\quad g>0 .
\tag{1.5}
$$

This is the free kinetic operator's full unit-source Green field.
There is no time cutoff, source averaging, survival normalization,
attractive diffusion drift or change of coupling in (1.5).

**Theorem 1.3 (original-clock identification and the complete tail).**
The killed process (1.2) has exactly the semigroup (1.4).
Its covariance is $2(P\otimes P+Q\otimes Q+\epsilon^2Z_c\otimes Z_c)dt$.
For every bounded Borel function $F$,

$$
\mathbb E_o\int_0^\tau F(q_t)\,dt
 =\int_\Omega\Gamma_{\epsilon,o}F\,d\mu,\qquad
\int_\Omega\Gamma_{\epsilon,o}\,d\mu
 =\frac{(k_o-l)(u-k_o)}2 .
\tag{1.6}
$$

For each $t_0>0$, constants independent of $\epsilon\ge0$ satisfy
$p^\Omega_\epsilon(t,q,q')\le C_{t_0}e^{-\lambda_I t}$ for $t\ge t_0$,
where $\lambda_I=\pi^2/(u-l)^2$. The Green field is positive, finite
and smooth off the pole, and

$$
\int_\Omega\Gamma_{\epsilon,o} L_\epsilon\varphi\,d\mu=\varphi(o),
\qquad \varphi\in C_c^\infty(\Omega).
\tag{1.7}
$$

**Proof.** Itô's formula in (1.2) gives the three fields $P,Q,\nu Z_c$
and no added drift: $[W^1,W^2]=0$.
They have zero divergence for the raw measure. Their sum of squares is
the generator $-L_\epsilon$ with the prescribed killing and periodicity.
For fixed $\epsilon>0$ smooth elliptic uniqueness identifies the killed
semigroup; at zero the horizontal diffusion supplies the same
identification by its smooth-coefficient SDE. The frame
$P,Q,[P,Q]=Z_c$ spans every tangent space, so positive-time smoothing
also holds at zero.

The central heat operator commutes with the horizontal one and its
boundary condition. On the actual torus,

$$
H^\epsilon_t=H^0_t
 \exp\bigl(t\epsilon^2r^{-2}\partial_\beta^2\bigr).
\tag{1.8}
$$

The second factor is a probability convolution. Hence any uniform
positive-time kernel bound for $H^0$ also bounds $H^\epsilon$.
Such a bound follows from the step-two heat estimates used in G, §2,
or directly from §2's whole-group kernel after periodization and killing.
Height alone is covariance-$2$ Brownian motion killed on $I$, independently
of $\epsilon$. Its interval heat expansion gives
$\sup_k\mathbb P_k(\tau>t)\le C_{t_0}e^{-\lambda_I t}$ for $t\ge t_0$.
Splitting the kernel into a fixed positive-time smoothing factor and
the remaining killed evolution proves the stated full kernel tail.
The same interval calculation solves $-m''=1$, $m(l)=m(u)=0$, giving
the mass in (1.6). Tonelli first proves (1.6) for nonnegative $F$;
the finite mass proves the bounded signed case. Integrating
$-\partial_t H^\epsilon_t\varphi(o)$ from zero to infinity proves
(1.7), with the tail just established. Positivity follows from the
connected killed diffusion and the local positive heat kernel.
Off-pole smoothness follows from the heat estimates and local elliptic
regularity (hypoelliptic regularity at zero). $\square$

## 2. The local model, its metric and the source normalization

**Definition 2.1 (exact chart and covering group).** On an injective
neighbourhood of the fixed pole set

$$
x=k-k_o,\quad y=2(\alpha-\alpha_o),\quad
z=-r(\beta-\beta_o-c(k_o)y),\quad \theta=z-\tfrac12xy.
\tag{2.1}
$$

In first-kind coordinates $\xi=(x,y,\theta)$ the fields and measure
are exactly

$$
U=\partial_x-\tfrac y2\partial_\theta,\quad
V=\partial_y+\tfrac x2\partial_\theta,\quad Z_H=\partial_\theta,\quad
d\mu=m_0\,d\xi,\qquad m_0=\frac1{2r}.
\tag{2.2}
$$

In particular $P=U$, $Q=V$, $Z_c=Z_H$.
Use the Heisenberg group law
$(x,y,\theta)(x',y',\theta')=
(x+x',y+y',\theta+\theta'+(xy'-yx')/2)$.
On the whole group let $h_\epsilon(t,\xi)$ be the Lebesgue kernel of
$-(U^2+V^2+\epsilon^2Z_H^2)$ and
$\mathcal G_\epsilon(\xi)=\int_0^\infty h_\epsilon(t,\xi)\,dt$.
The latter is a comparison kernel, not a replacement for (1.5).
The actual phase deck transformations, in second-kind coordinates, are

$$
(x,y,z)\longmapsto
 (x,y+4\pi n,z+4\pi r c(k_o)n-2\pi r m),\qquad (n,m)\in\mathbb Z^2.
\tag{2.3}
$$

They preserve all three fields and Lebesgue measure. In first-kind
coordinates the accompanying shear of $\theta$ must be retained.

Let $d_\epsilon$ be the whole-group length distance for the orthonormal
frame $(U,V,\epsilon Z_H)$ when $\epsilon>0$, and let $d_0$ be the
horizontal Carnot–Carathéodory distance.
These are intrinsic diffusion distances. They are not K's complete wrapped
tracking metric $D_{\max}$, its isolated-cemetery metric, or its
two-control execution distance. Write $d=d_\epsilon(0,\xi)$.

The mature whole-group comparison estimates used in Theorem 3.1
have the following form. For each fixed $\epsilon_0<\infty$,
uniformly over $0\le\epsilon\le\epsilon_0$,

$$
\begin{aligned}
d_\epsilon(0,\xi)&\asymp
 \left(x^2+y^2+\min\{|\theta|,\theta^2/\epsilon^2\}\right)^{1/2},\\
|B_\epsilon(0,s)|&\asymp s^3(\epsilon+s),\\
h_\epsilon(t,\xi)&\asymp
 \frac{\exp(-c\,d_\epsilon(0,\xi)^2/t)}
 {t^{3/2}(\epsilon+\sqrt t)} .
\end{aligned}
\tag{2.4}
$$

The two heat inequalities allow different positive constants in their
exponents. At zero use the horizontal interpretation of the minimum.
Native ball volumes in an injective chart have the additional factor
$m_0$. Moreover, for $\delta_s(x,y,\theta)=(sx,sy,s^2\theta)$,

$$
\mathcal G_\epsilon(\delta_s\xi)
 =s^{-2}\mathcal G_{\epsilon/s}(\xi),\qquad
\mathcal G_0(\xi)=\frac1{2\pi}R(\xi)^{-2},
\quad R=((x^2+y^2)^2+16\theta^2)^{1/4},
\tag{2.5}
$$

and $\mathcal G_\kappa\to\mathcal G_0$ uniformly on compact annuli
away from zero as $\kappa\downarrow0$.

For their application to this source, the mature intermediates are
the uniform ball and heat
estimates of Capogna–Citti–Manfredini, arXiv:1212.6665v2,
§2, (2.2)–(2.3), Propositions 2.1–2.2.
Here their group is exactly the group in Definition 2.1, the scaled basis
is $U,V,\epsilon Z_H$, and their constant coefficient matrix is $I_3$.
Thus all coefficient coercivity constants are fixed.
Capogna–Citti, arXiv:1504.04762v1, §2.3, Lemma 2.13,
gives the explicit regularized gauge; its ball box has horizontal
width $s$ and central width comparable to $s^2+\epsilon s$.
Multiplying these widths proves the displayed volume, retaining the raw
factor $m_0$ when returning to the native chart.
In that paper's displayed Heisenberg example the coordinate map is
$(x_1,x_2,x_3)=(x,y,2\theta)$ and its regularization parameter is
$2\epsilon$. Thus no factor two is silently transferred to the native
clock. Theorem 1.3 and Proposition 5.2 there give an alternative local
heat supplier; their scope is not a periodic killed Green theorem.

Field homogeneity and the determinant $s^4$ give
$h_\epsilon(s^2t,\delta_s\xi)=s^{-4}h_{\epsilon/s}(t,\xi)$,
which proves the Green scaling. The value of $\mathcal G_0$ with
Lebesgue measure is V, Theorem 10.2, not a new fundamental-solution
claim. Positive-time kernel convergence is also supplied by
1212.6665v2, Proposition 2.2, (2.11).
On a compact annulus $K$, $d_\kappa(0,K)$ has a positive lower bound
for $0\le\kappa\le1$. The upper heat bound is then
$Ct^{-2}e^{-c_K/t}$ at small time and $Ct^{-2}$ at large time.
Both are integrable in their respective ranges.
Dominated integration, uniform on $K$, proves the last convergence
needed in Theorem 5.1. These whole-group estimates are attributed
intermediates for the native statements below.

## 3. Native killed propagation and the full Green crossover

**Theorem 3.1 (uniform local propagation with the actual tail).**
Fix $\epsilon_0>0$. There are an injective neighbourhood $U_o$,
$t_o>0$ and positive constants, depending on the fixed source, pole
and $\epsilon_0$, such that for $q=\Phi_o(\xi)\in U_o$,
$0<t\le t_o$ and $0\le\epsilon\le\epsilon_0$,

$$
\frac{c\,e^{-C d^2/t}}{m_0t^{3/2}(\epsilon+\sqrt t)}
 \le p^\Omega_\epsilon(t,o,q)
 \le\frac{C\,e^{-c d^2/t}}{m_0t^{3/2}(\epsilon+\sqrt t)}.
\tag{3.1}
$$

Here $\Phi_o$ is the inverse chart. There is also a finite $B$,
independent of these $\epsilon$, with

$$
\left|\Gamma_{\epsilon,o}(\Phi_o(\xi))
      -m_0^{-1}\mathcal G_\epsilon(\xi)\right|\le B
 \quad(\Phi_o(\xi)\in U_o\setminus\{o\}).
\tag{3.2}
$$

After shrinking $U_o$ if necessary, the full field satisfies

$$
\Gamma_{\epsilon,o}(\Phi_o(\xi))
 \asymp \frac1{m_0\,d(\epsilon+d)} .
\tag{3.3}
$$

Thus the short-time on-diagonal law changes from
$(m_0\epsilon t^{3/2})^{-1}$ at $t\ll\epsilon^2$ to
$(m_0t^2)^{-1}$ at $\epsilon^2\ll t\le t_o$.
The Green law changes from $(m_0\epsilon d)^{-1}$ at $d\ll\epsilon$
to $(m_0d^2)^{-1}$ at $\epsilon\ll d$ within the chart.
As $\epsilon\downarrow0$, the native kernels converge uniformly on
compact positive-time intervals and compact interior pairs, and
$\Gamma_{\epsilon,o}\to\Gamma_{0,o}$ locally uniformly off the pole.

**Proof.** Lift the cylinder to the height strip in the group of §2
and first remove height killing. Periodize its whole-group heat kernel
over precisely (2.3); the factor $m_0^{-1}$ converts its kernel
to raw native measure. A nontrivial deck image of a sufficiently small
fixed source chart has distance from zero bounded below in
$d_{\epsilon_0}$, hence also in every $d_\epsilon$ in this range.
The number of deck images in a $d_{\epsilon_0}$ ball grows at most
polynomially: (2.3) bounds $|n|$ by a constant times its radius and
$|m|$ by a constant times the radius plus its square.
Consequently (2.4) sums all nontrivial images, for $t\le t_o$, to
at most $Ct^{-2}e^{-a/t}$, with $a>0$ independent of $\epsilon$.

Let $\sigma$ be the actual first height exit of this periodic free
process. The strong Markov identity for its kernel is

$$
p^{\rm per}_\epsilon(t,o,q)-p^\Omega_\epsilon(t,o,q)
 =\mathbb E_o\bigl[
  \mathbf1_{\{\sigma<t\}}\,
  p^{\rm per}_\epsilon(t-\sigma,q_\sigma,q)\bigr].
\tag{3.4}
$$

For $q\in U_o$, its height is separated by a fixed positive distance
from each exit face. Since $d_\epsilon$ dominates height displacement,
the same Gaussian estimate, summed over the deck images, bounds
the right side by $Ct^{-2}e^{-a'/t}$.
One may take the supremum over $0<t-\sigma\le t$ here:
$s^{-2}e^{-a/s}\le Ct^{-2}e^{-a/(2t)}$ for small $t$.
This does not assume an exit-time density or a bridge independent of
the source. Choose $U_o$ so small in $d_0$ that its free lower Gaussian
exponent is strictly smaller than the boundary/image error exponent.
Since $d_\epsilon\le d_0$ and
$t^{3/2}(\epsilon+\sqrt t)\le C_{\epsilon_0}t^{3/2}$ on this range,
the exponential error is absorbed into half the free lower bound for
small $t_o$. The upper bound follows by domination by the periodic
free kernel and the same absorption. This proves (3.1).

The errors in (3.4) and in periodization are integrable uniformly from
zero to $t_o$. From $t_o$ to infinity the native kernel has the
uniform exponentially decaying tail of Theorem 1.3.
The whole-group kernel has the integrable uniform upper tail $Ct^{-2}$.
Integrating these three estimates proves (3.2). This explicitly retains
the complete native time integral; no whole-group theorem supplies
the killed tail.

Finally integrating (2.4), using $s=\sqrt t$, gives

$$
\int_0^\infty
 \frac{e^{-c d^2/t}\,dt}{t^{3/2}(\epsilon+\sqrt t)}
 \asymp\int_d^\infty\frac{ds}{s^2(\epsilon+s)}
 \asymp\frac1{d(\epsilon+d)} .
\tag{3.5}
$$

The constants are independent of $\epsilon,d>0$.
For instance split the last integral at $\epsilon$ when $d<\epsilon$;
when $d\ge\epsilon$ it is comparable to $\int_d^\infty s^{-3}ds$.
The exponentially suppressed portion $s<d$ satisfies the same bound
by dyadic intervals. The bounded error (3.2) is absorbed by shrinking
the chart, because $1/[d(\epsilon+d)]$ tends uniformly to infinity
as $d\to0$ with $\epsilon\le\epsilon_0$.
The zero-noise formula follows by the same estimates.
For the last convergence assertion, (1.8) is an approximate identity
in the central circle at positive time; the smooth horizontal kernel
makes this convergence uniform on the stated compact sets.
On a compact set away from the pole, the small-time upper bound is
$Ct^{-2}e^{-c_K/t}$ uniformly for $\epsilon\le\epsilon_0$.
Together with the common exponential tail it permits dominated
integration, proving the asserted full Green convergence. $\square$

The exponent three at the inner regularized scale and exponent four
at the outer horizontal scale belong to diffusion volume and heat
propagation. The state manifold remains three-dimensional, the native
actuator rank remains two, and the horizontal growth vector remains
$(2,3)$. None of these identifies a physical spatial dimension or
a predictive-state capacity.

## 4. Every nonzero-noise matched form and a uniform sufficient condition

**Theorem 4.1 (actual domain, closure and attained minimum).**
For every fixed $\epsilon>0$ and every $g>0$,
$q_{\epsilon,g}$ is closed and semibounded on exactly
$\mathcal F_\epsilon$. Its sufficiently shifted norm is equivalent
to the norm in (1.3), its self-adjoint operator has compact resolvent,
and

$$
E_\epsilon(g)=
 \min_{\substack{f\in\mathcal F_\epsilon\\ \|f\|_2=1}}
 q_{\epsilon,g}[f]
\tag{4.1}
$$

is finite and attained. There is no assertion that this minimum is
negative for every $g$. For any fixed $\epsilon_*>0$ and $g>0$,
a lower bound and a relative form bound less than one can be chosen
uniformly over all $\epsilon\ge\epsilon_*$.

**Proof.** For fixed nonzero $\epsilon$, the frame in (2.2) is elliptic.
On the compact cylinder its form norm is equivalent to the stated
periodic $H^1$ norm. The local estimate (3.3) is a Coulomb singularity
in its smooth elliptic metric; it does not have the horizontal
inverse-square strength. Here is a quantitative proof of its required
form smallness, which will also be used for the small-noise bound.

For $0<\epsilon\le1$, (3.1), periodization and the tail prove a bound
uniform over both kernel variables:

$$
\sup_{q,q'}p^\Omega_\epsilon(t,q,q')
 \le \frac{C}{t^{3/2}(\epsilon+\sqrt t)}
 \quad(0<t\le1),\qquad
 \le Ce^{-\lambda_I t}\quad(t\ge1).
\tag{4.2}
$$

The upper bound near a face only improves under killing.
For $a>0$ let $R_{\epsilon,a}=(L_\epsilon+a)^{-1}$ and put
$K_\epsilon(a)=\|R_{\epsilon,a}\Gamma_{\epsilon,o}\|_\infty$.
Symmetry, the semigroup identity and Tonelli give

$$
R_{\epsilon,a}\Gamma_{\epsilon,o}(q)
 =\int_0^\infty\frac{1-e^{-av}}a\,
             p^\Omega_\epsilon(v,o,q)\,dv .
\tag{4.3}
$$

For $a\ge\epsilon^{-2}$ split this integral at
$a^{-1},\epsilon^2,1$. With (4.2), the four pieces are bounded by
constants times, respectively,
$1/(\epsilon\sqrt a)$,
$1/(\epsilon\sqrt a)$,
$1/(a\epsilon^2)$ and $1/a$.
The last two are at most constants times the first. Thus

$$
K_\epsilon(a)\le \frac{C}{\epsilon\sqrt a},
\qquad a\ge\epsilon^{-2},\quad0<\epsilon\le1 .
\tag{4.4}
$$

For clarity, the form implication needed here does not presume the
desired semiboundedness. Truncate $V=\Gamma_{\epsilon,o}$ by $V_N$.
The symmetric positive kernel of
$V_N^{1/2}R_{\epsilon,a}V_N^{1/2}$ has weighted Schur bound
$K_\epsilon(a)$, using weight $V_N^{1/2}$, since
$R_{\epsilon,a}V_N\le R_{\epsilon,a}V$.
Duality with $(L_\epsilon+a)^{-1/2}$ then gives
$\int V_N|f|^2\le K_\epsilon(a)(T_\epsilon[f]+a\|f\|_2^2)$.
Monotone convergence proves

$$
V_\epsilon[f]\le K_\epsilon(a)
       (T_\epsilon[f]+a\|f\|_2^2),\qquad f\in\mathcal F_\epsilon .
\tag{4.5}
$$

For each fixed $\epsilon$, $K_\epsilon(a)\to0$.
The argument for an arbitrary larger fixed $\epsilon$ is the same,
or follows by central convolution from any smaller positive value.
KLMN, in Teschl, Theorem 6.24, applies with relative bound
$gK_\epsilon(a)<1$, on exactly the free form domain.
Inequality (4.5) and $q_{\epsilon,g}\le T_\epsilon$ give shifted
norm equivalence. Compact $H^1\hookrightarrow L^2$ embedding on the
periodic bounded cylinder gives compact form embedding, hence compact
resolvent and an attained normalized lowest energy.

For the uniform assertion, if $\epsilon\ge\epsilon_*$, central
commutation gives
$H^\epsilon_t=H^{\epsilon_*}_t
 \exp(t(\epsilon^2-\epsilon_*^2)r^{-2}\partial_\beta^2)$.
The kernel supremum is therefore no larger than that at $\epsilon_*$.
Using this bound in (4.3) gives a common quantity tending to zero as
$a\to\infty$, independently of $\epsilon\ge\epsilon_*$.
The same Schur argument proves a uniform relative bound and lower
bound. Compactness and attainment hold for each member; no uniform
upper bound on its ellipticity constants is asserted. $\square$

## 5. The supercritical small-noise energy rate

**Theorem 5.1 (two-sided failure of uniform attractive stability).**
Let $\lambda_0$ be exactly V, Definition 10.1's lowest angular
eigenvalue, with its natural endpoint domain. For the raw density
and identity covariance in this volume the existing horizontal
threshold is

$$
g_{\rm c}=2\pi m_0\lambda_0=\frac{\pi\lambda_0}{r}.
\tag{5.1}
$$

For every fixed $g>g_{\rm c}$, every fixed native datum of
Definition 1.1, all arbitrary fixed preparation phases and every
fixed interior pole, there exist constants
$0<c_g\le C_g<\infty$ and $\epsilon_g>0$ such that

$$
-\frac{C_g}{\epsilon^2}\le E_\epsilon(g)
 \le-\frac{c_g}{\epsilon^2}<0,\qquad 0<\epsilon<\epsilon_g .
\tag{5.2}
$$

The constants may depend on the listed fixed source data and $g$,
but not on small $\epsilon=|\nu|$ or its sign.
The field and kinetic energy in every $E_\epsilon$ use the same
$L_\epsilon$, raw source measure, actual periodic cylinder and clock.

**Proof.** Choose $A_g\ge1$ so large that $gC/\sqrt{A_g}\le1/2$ in
(4.4), and set $a=A_g/\epsilon^2$ for $0<\epsilon\le1$.
Equation (4.5) gives

$$
q_{\epsilon,g}[f]\ge
 \tfrac12T_\epsilon[f]-\frac{A_g}{2\epsilon^2}\|f\|_2^2 .
\tag{5.3}
$$

This proves the lower bound on the entire actual form domain,
rather than only on localized trial functions.

For the upper bound reuse V, Theorem 10.2 and the annular witness
in the proof of Theorem 13.1. There is a single real
$v\in C_c^\infty(\mathbb R^3\setminus\{0\})$, nonzero, for which

$$
\mathcal A_0:=
 \frac{\int(|Uv|^2+|Vv|^2)\,d\xi
       -(g/m_0)\int\mathcal G_0|v|^2\,d\xi}{\|v\|_{L^2(d\xi)}^2}<0 .
\tag{5.4}
$$

This is exactly their condition
$m_0\int|\nabla_Hv|^2-(g/2\pi)\int R^{-2}|v|^2<0$.
It consumes their sharp threshold and full angular test class,
without reproving them. By §2's dominated Green convergence and smoothness of this fixed
annular $v$,

$$
\mathcal A_\kappa:=
 \frac{\int(|Uv|^2+|Vv|^2+\kappa^2|Z_Hv|^2)\,d\xi
       -(g/m_0)\int\mathcal G_\kappa|v|^2\,d\xi}{\|v\|_2^2}
 \longrightarrow\mathcal A_0 .
\tag{5.5}
$$

Fix one $\kappa>0$ with $\mathcal A_\kappa=-b_g<0$.
It remains fixed as $\epsilon\downarrow0$. Put $s=\epsilon/\kappa$;
for sufficiently small $\epsilon$, $\delta_s\operatorname{supp}v$
lies in the injective chart of Theorem 3.1, and define

$$
f_\epsilon(\Phi_o(\delta_s\xi))
 =m_0^{-1/2}s^{-2}v(\xi)/\|v\|_2 ,
\tag{5.6}
$$

with zero extension outside the chart. This is a normalized smooth
punctured-core function, so belongs to the actual $\mathcal F_\epsilon$.
Exact field homogeneity, the constant density and (3.2) give

$$
\begin{aligned}
T_\epsilon[f_\epsilon]
 &=s^{-2}
 \frac{\int(|Uv|^2+|Vv|^2+\kappa^2|Z_Hv|^2)}{\|v\|_2^2},\\
V_\epsilon[f_\epsilon]
 &=s^{-2}m_0^{-1}
 \frac{\int\mathcal G_\kappa|v|^2}{\|v\|_2^2}+O(1),\\
q_{\epsilon,g}[f_\epsilon]
 &=-b_gs^{-2}+O(1)
  =-b_g\kappa^2\epsilon^{-2}+O(1).
\end{aligned}
\tag{5.7}
$$

The $O(1)$ is uniform in small $\epsilon$ by (3.2); it includes the
whole native periodic and killed tail. No truncated-time potential or
horizontal field is substituted for $\Gamma_{\epsilon,o}$.
Taking $\epsilon_g$ smaller absorbs this remainder into half the
negative leading term. With $c_g=b_g\kappa^2/2$ and a suitable $C_g$,
(5.3) and the variational principle prove (5.2). $\square$

The original-problem consumer is the already supplied central-noise
target of K, §33. Full ellipticity at every nonzero noise is compatible
with a diverging attractive ground energy when the noise is removed:
for every supercritical horizontal coupling the precise order is
$|\nu|^{-2}$. A claim of stable propagation uniform in this limit
therefore needs an additional condition, such as noise bounded away
from zero as in Theorem 4.1. No exact asymptotic coefficient, critical
coupling crossover, or all-regime control redesign is asserted.

## 6. Lawful realization and the bounded occupation bridge

**Definition 6.1 (two different supplied observation contracts).**
For a finite horizon retain K, §33's one joint source, ideal stopped
real histories, independently enlarged initial seed, and finite numerical
issuance class. Its §§34–39 supply original two-control inward
rectangles, stopping-time suffix service, prefix guards, own killing
and coupled lifetime convergence. Their field is not a free primitive
central actuator. All actual prefixes have height in
$[l,u]\Subset(0,H)$, and the same numerical relative command at another
start still has domain
$(-\min a,H-\max a)$; an illegal start is refused.
At actual own exit the command holds. Target death or an interrupted
suffix is not a reset of chronology, initial phases or own death.

The four resources remain the unhalved original-time quantities

$$
V^a=\int|\dot a|\,dt,\quad V^b=\int|\dot b|\,dt,\quad
L=\int\sqrt{\dot a^2+\dot b^2}\,dt,\quad
E=\int(\dot a^2+\dot b^2)\,dt .
\tag{6.1}
$$

K, Theorems 33.2 and 38.1 supply, for each fixed $\nu\ne0$,
matching orders $\eta^{-2}$ for both variations and length and
$\eta^{-4}$ for energy in the ideal-history almost-sure hard-tube
class. All movement until own death or the horizon is charged.

Alternatively use precisely K, Definition 41.1's paid wrapped
current-point interface and acquired filtration, without ideal
history access. Every future Read time is selected from the past paid
records and clock, not from an unseen threshold crossing.
O, Theorems 48.1–48.2 supply positive risk $\delta$, finite issuances,
no premature own death, and, for fixed $\nu\ne0$,

$$
\mathbb EM=O\!\left(\eta^{-2}\log\frac{e}{\eta\delta}\right),\quad
\mathbb EV^a,\mathbb EV^b,\mathbb EL=O(\eta^{-2}),\quad
\mathbb EE=O(\eta^{-4}) .
\tag{6.2}
$$

The constants here are not asserted uniform as $\nu\to0$.
For fixed positive risk the Read order is sharp.
Zero risk is excluded by K, Theorem 41.2. The sensor is an additional
exact-real interface, not a native or finite-bit acquisition theorem.

**Theorem 6.2 (the bounded occupation actually implied by tracking).**
For either supplied family, let $S_N=T\wedge\tau_N$ be its actual
censored own lifetime, $S=T\wedge\tau$, and let $\bar q_N,\bar q$
be its same-source held paths. For
$F\in C(\overline I\times\mathbb T^2)$ put
$M=\|F\|_\infty$ and let $\omega_F$ be its modulus for $D_{\max}$.
Under the ideal-history supplier,

$$
\left|\mathbb E\int_0^{S_N}F(\bar q_N(t))dt
 -\mathbb E\int_0^S F(\bar q(t))dt\right|
 \le T\omega_F(\eta)+M d_\eta,\qquad d_\eta\downarrow0 .
\tag{6.3}
$$

Here $d_\eta$ is exactly K, (37.2)'s terminal duration $\rho^2$.
Under the paid supplier, its good event and
$e_\rho\le2\rho^2$ of O, Theorem 48.2 give instead

$$
\left|\mathbb E\int_0^{S_N}F(\bar q_N(t))dt
 -\mathbb E\int_0^S F(\bar q(t))dt\right|
 \le T\omega_F(\eta)+M e_\rho+2MT\delta .
\tag{6.4}
$$

Thus with decreasing positive risks $\delta\to0$, for each fixed $T$
both contracts give bounded continuous occupation convergence.
Taking first this approximation limit and then $T\to\infty$ gives
the full Green occupation (1.6) for these tests. No fixed positive-risk
convergence, all-Borel-test transfer or uniform native lifetime tail
is inferred from path tracking.

**Proof.** On the common live interval, the native hard tube bounds
the integrand difference by $\omega_F(\eta)$. The remaining interval
has length $|S_N-S|$ and contribution at most $M|S_N-S|$.
The ideal supplier gives $0\le S_N-S\le d_\eta$ pathwise.
On the paid good event it gives the tube and delay at most $e_\rho$.
Off that event use the deterministic bound $2MT$ and probability
at most $\delta$, including all unsuccessful paths. This proves
(6.3)–(6.4) without time-changing either execution or integration.
The target tail is bounded by
$M\mathbb E(\tau-T)_+\le C M e^{-\lambda_I T}$.
Consequently the indicated iterated limit is (1.6).
Each finite-horizon native approximation uses its own prescribed
horizon; the tail argument is for the limiting target, not an
unproved uniform tail for those approximations. $\square$

## 7. Singular occupation and the remaining realization limits

**Proposition 7.1 (the source-field test still needs a cap or a separate
integrability proof).** For fixed $\epsilon>0$ the target's own
uncapped point-field occupation is finite:

$$
\mathbb E_o\int_0^\tau\Gamma_{\epsilon,o}(q_t)\,dt
 =\int_\Omega\Gamma_{\epsilon,o}^2\,d\mu<\infty .
\tag{7.1}
$$

Nevertheless Theorem 6.2 transfers only a fixed cap
$\Gamma_{\epsilon,o}\wedge B$ directly. It does not transfer (7.1)
to the native command families without uniform integrability.
Even among lawful native histories converging to a continuous path,
uncapped occupation of this field can be infinite at every stage.

**Proof.** For fixed $\epsilon$, (3.3) and the local volume
$|B_\epsilon(0,s)|\asymp\epsilon s^3$ at $s\ll\epsilon$
make the integral of $\Gamma_{\epsilon,o}^2$ finite near zero:
the radial majorant is a constant times
$\epsilon^{-1}\int_0^{c\epsilon}ds$.
Off a pole neighbourhood the field is bounded on the closed cylinder.
Tonelli and (1.6) prove (7.1).
The capped field extends continuously at the pole by value $B$ and
at the killed boundary by zero, so Theorem 6.2 applies.
Indeed the pole is interior, and near either face the fixed elliptic
Green field is homogeneous-harmonic with smooth zero Dirichlet data;
boundary regularity gives that continuous zero extension.

For the final assertion, start at this same pole, hold both original
controls for a positive duration $h_n\downarrow0$, then follow a
fixed lawful smooth command which first moves in height and exits at
$u$ inside a finite horizon. These paths converge uniformly, with
convergent lifetimes, to that command without its initial hold.
Every prefix remains in $[l,u]\Subset(0,H)$ and has finite resources.
Yet every held path spends time $h_n>0$ at the pole, where
$\Gamma_{\epsilon,o}=+\infty$, so its uncapped occupation is infinite.
This counterexample does not identify those histories with a supplied
Brownian tracking family; it disproves a deduction from path/lifetime
convergence alone. The same obstruction applies whenever a proposed
realization includes a positive initial hold at the pole.
The stronger family-specific singular occupation results in
[Singular occupation and command-cap limits](FIB_NATIVE_SINGULAR_OCCUPATION_AND_COMMAND_CAP_LIMITS.md)
concern their prescribed horizontal source and command laws.
Their thresholds are not transferred to (1.2) without a new joint
occupation estimate. $\square$

**Definition 7.2 (scope of the bridge).** Theorems 1.3–5.1 concern the
full free target law and the same operator's matched attractive form;
they do not construct a native attractive-process sampler or a physical
Hamiltonian. The finite-command suppliers give lawful approximations
under their stated observations and diverging charged resources.
Theorems 6.2–7.1 identify precisely the occupation transfer used here.
For an uncapped attractive observable, convergence of the corresponding
singular occupations remains an additional obligation.
For a physical spatial interpretation, a source-preserving realization
of distances, measurements, clocks and operations remains an additional
obligation. Neither current-ray dimension three, stochastic covariance
rank three at $\nu\ne0$, the horizontal exponent four, nor bounded
predictive observations supply that realization. The rank-three Carnot
and source-collapse results in
[Continuation III, §§81–87 and 90–93](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md)
have different carrier/source contracts; none replaces the periodic
double-wall calculation above. Likewise the prepared-observer contract
in
[Observer, §§27–30](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)
does not supply the acquired filtration of Definition 6.1.

## 8. Primary attribution and the source-specific mathematical increment

**Definition 8.1 (literature and reuse boundary).** The load-bearing
external intermediates and their exact scope are:

| Primary source | Supplied intermediate and boundary |
| --- | --- |
| Capogna–Citti–Manfredini, *Uniform Gaussian bounds for subelliptic heat kernels and an application to the total variation flow of graphs over Carnot groups*, [arXiv:1212.6665v2](https://arxiv.org/html/1212.6665v2), §2, Propositions 2.1–2.2 | literature-attested: uniform doubling, whole-group regularized Gaussian bounds and positive-time convergence for the constant scaled frame. The coefficient choice is $I_3$. The actual killed periodic source, full-time remainder and attractive energy rate are not their conclusion. |
| Capogna–Citti, *Regularity for subelliptic PDE through uniform estimates in multi-scale geometries*, [arXiv:1504.04762v1](https://arxiv.org/pdf/1504.04762v1), Theorem 1.3, §2.3, Proposition 5.2 | literature-attested: the regularized gauge and uniform local heat estimates. Definition 2.1's $x_3=2\theta$, parameter $2\epsilon$, and constant raw Jacobian specify the correspondence. Local/whole-space fundamental solutions do not themselves control the native killed long-time tail. |
| Teschl, *Mathematical Methods in Quantum Mechanics*, public online edition, version February 12, 2009, [§6.5, Theorem 6.24](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf) | literature-attested: KLMN for a closed semibounded form with perturbation relative bound less than one. The concrete bound (4.5) is supplied here before applying it. |

The repository suppliers are N's guarded chronology and preparation;
K, §§33–41's conditional target and ideal-history/paid-interface
distinction; O, §§42–49's acquisition and execution bounds; and V,
§§10–13's raw-source sharp horizontal constant and annular witnesses.
Their parameters are fixed by (1.1)–(2.2), not inferred from a shared
name or dimension. G, Definition 1.3 supplies the same-field convention.
V, §29's variable-coefficient finite-sign law has different sampling
capabilities and no independent central noise; it is not substituted
for either contract in §6.

The source-specific statements are repo-derived: identification of
K's declared law with its own killed generator, the bounded full-time
native remainder (3.2), the local crossover on its actual periodic
source, the quantitative matched lower bound on the full domain,
and the two-sided supercritical rate (5.2), together with the bounded
occupation consumer and its cap boundary. Whole-group regularization,
KLMN, the horizontal threshold and the native connector constructions
are reused intermediates. No worldwide novelty or formal certification
is asserted.

## 追加锚（本行以下为增补区）

## 9. Fixed central noise and exact local Euclidean compatibility

**Definition 9.1 (the original source and the candidate comparison).**
Retain Definitions 1.1–1.2 and 2.1, with fixed $\epsilon=|\nu|>0$.
In particular, $0<Z<1$, $r=1-Z$, $H=r/2$, $X=Y=H$,
$0<l<u<H$, and $\Omega=(l,u)\times\mathbb T^2$.
For arbitrary fixed preparation phases $\theta_s^0$, the signed native
representative, in mode order $(0,1,2,3,13)$, is

$$
\psi(k,\alpha,\beta)=\left(
 \sqrt{k}e^{-i(\theta_0^0+\beta)},\,
 \sqrt{H-k}e^{-i(\theta_1^0+\beta-\alpha)},\,
 \sqrt Z e^{-i\theta_2^0},\,
 \sqrt{H-k}e^{-i(\theta_3^0+\beta-\alpha)},\,
 \sqrt{k}e^{-i(\theta_{13}^0+\beta)}\right).
\tag{9.1}
$$

Both increment coordinates have period $2\pi$; equal increments do not
identify the preparation phases. The raw measure is
$d\mu=dk\,d\alpha\,d\beta$. The immutable initial preparation and the
fixed interior pole $o=(k_o,\alpha_o,\beta_o)$ of (1.5) remain specified.
The conditional law is exactly (1.2): three independent covariance-$2$
Brownian motions, area drift zero, signed central coefficient $\nu$,
and killing at the first hit of either $k=l$ or $k=u$.
Its interior generator and symbol are

$$
\begin{aligned}
G_\epsilon&=P^2+Q^2+\epsilon^2Z_c^2=-L_\epsilon\quad
                       \text{on interior smooth tests},\\
\mathsf A_\epsilon&=P\otimes P+Q\otimes Q+
                         \epsilon^2Z_c\otimes Z_c,\\
P&=\partial_k,\quad Q=\tfrac12\partial_\alpha+
                  (\tfrac12-k/r)\partial_\beta,\quad
Z_c=-r^{-1}\partial_\beta .
\end{aligned}
\tag{9.2}
$$

The clock is $H_t^\epsilon=e^{-tL_\epsilon}$, with no survival
normalization. Let $g_\epsilon$ be the Riemannian metric whose
orthonormal frame is $(P,Q,\epsilon Z_c)$; equivalently,
$g_\epsilon^{-1}=\mathsf A_\epsilon$.
In the exact first-kind chart (2.1)–(2.2),

$$
\begin{aligned}
g_\epsilon&=dx^2+dy^2+\epsilon^{-2}
       (d\theta+\tfrac y2dx-\tfrac x2dy)^2,\\
d\mu&=m_0\,dx\,dy\,d\theta,\qquad m_0=(2r)^{-1}.
\end{aligned}
\tag{9.3}
$$

Its local length distance is the distance $d_\epsilon$ of Definition
2.1, restricted to sufficiently small normal neighbourhoods. It is a
kinetic distance, not a task-output error or a primitive-command cost.

For a nonempty interior open set $U\subset\Omega$, a candidate exact
comparison consists of a smooth map $F:U\to V$, with
$V\subset\mathbb R^3$ open, a smooth scalar $a:U\to(0,\infty)$,
an arbitrary smooth source vector field $B$ on $U$, and

$$
\mathcal A_{\mathsf D,b}f
 =\sum_{i,j=1}^3\mathsf D^{ij}\partial_i\partial_j f
       +\sum_{i=1}^3 b^i\partial_i f,
\qquad \mathsf D=\mathsf D^{\mathsf T}>0\text{ constant},
\quad b\in C^\infty(V,\mathbb R^3).
\tag{9.4}
$$

Thus $2\mathsf D\,dt$ is the target diffusion covariance, and its
constant kinetic metric is $\mathsf D^{-1}$. Isotropic diffusion is the
special case $\mathsf D=cI_3$, $c>0$. The factor $a$ and both drifts
are analytical relaxations in this comparison. They do not change the
law (1.2), supply a clock service, or add a central native command.
Native histories still have $j=\int a_{\rm cmd}\,db_{\rm cmd}$,
the original extrema guard, and all four unhalved resources (6.1).
Here $a_{\rm cmd}$ is the height control, distinct from the scalar $a$.

**Theorem 9.2 (no exact full-test constant-diffusion readout).**
For every fixed $\epsilon>0$ and every nonempty interior open $U$,
there is no candidate of Definition 9.1 satisfying

$$
(aG_\epsilon+B)(f\circ F)
       =(\mathcal A_{\mathsf D,b}f)\circ F
             \quad\text{on }U,\qquad f\in C_c^\infty(V).
\tag{9.5}
$$

No rank, injectivity or inverse assumption on $F$ is needed.
The obstruction concerns the exact rank-three kinetic symbol, even
with variable positive scalar retiming and arbitrary first-order drifts.

Proof. At $q\in U$, choose a compactly supported test with zero gradient
and arbitrary symmetric Hessian at $F(q)$. The second-order chain rule
in (9.5) forces

$$
a(q)\,dF_q\,\mathsf A_\epsilon(q)\,dF_q^{\mathsf T}
                 =\mathsf D .
\tag{9.6}
$$

Since $\mathsf D$ is positive definite, $dF_q$ has rank three at
every $q$. The inverse function theorem therefore supplies local
inverse branches; this conclusion has not been assumed.
Inverting (9.6) on any branch gives

$$
F^*(\mathsf D^{-1})=a^{-1}g_\epsilon .
\tag{9.7}
$$

The left side is flat. Hence (9.5) would require $g_\epsilon$ to
be conformally flat on a nonempty open set. First-order coefficients
cannot change this requirement. More explicitly, the remaining
coefficient equations are just
$aG_\epsilon F^i+BF^i=b^i\circ F$. If a local diffeomorphism
satisfied (9.6), these equations could always be met locally by
$B=(dF)^{-1}(b\circ F-aG_\epsilon F)$. Thus the contradiction below
is in the symbol, rather than a restriction on available drift choices.

Here is the geometric calculation with one fixed convention. Put
$E_1=P$, $E_2=Q$, $E_3=\epsilon Z_c$ and $h=\epsilon^{-1}$.
Then $[E_1,E_2]=hE_3$ and the other two brackets vanish.
Use

$$
\begin{aligned}
R(X,Y)Z&=\nabla_X\nabla_YZ-\nabla_Y\nabla_XZ-\nabla_{[X,Y]}Z,\\
\operatorname{Ric}(Y,Z)&=\sum_i g_\epsilon(R(E_i,Y)Z,E_i),\\
S&=\operatorname{Ric}-\tfrac14\operatorname{Scal}\,g_\epsilon,\\
C(X,Y,Z)&=(\nabla_XS)(Y,Z)-(\nabla_YS)(X,Z).
\end{aligned}
\tag{9.8}
$$

The last line specifies a covariant three-tensor, antisymmetric in its
first two slots; no Cotton–York dualization is being used. Koszul's
formula gives the full connection table, with row $i$, column $j$
equal to $\nabla_{E_i}E_j$:

$$
\begin{pmatrix}
0&\frac h2E_3&-\frac h2E_2\\
-\frac h2E_3&0&\frac h2E_1\\
-\frac h2E_2&\frac h2E_1&0
\end{pmatrix}.
\tag{9.9}
$$

For example the formula used is
$2g_\epsilon(\nabla_{E_i}E_j,E_k)
 =g_\epsilon([E_i,E_j],E_k)-g_\epsilon([E_j,E_k],E_i)
  +g_\epsilon([E_k,E_i],E_j)$.
Substitution of (9.9) into (9.8) gives

$$
\begin{aligned}
R(E_1,E_2)E_2&=-\tfrac{3h^2}4E_1,&
R(E_1,E_3)E_3&=\tfrac{h^2}4E_1,&
R(E_2,E_3)E_3&=\tfrac{h^2}4E_2,\\
\operatorname{Ric}&=\operatorname{diag}(-h^2/2,-h^2/2,h^2/2),&
\operatorname{Scal}&=-h^2/2,&
S&=\operatorname{diag}(-3h^2/8,-3h^2/8,5h^2/8).
\end{aligned}
\tag{9.10}
$$

All off-diagonal Ricci entries vanish by the same table. The entries
of $S$ are constant in this frame, but its covariant derivative is not
zero. In particular,

$$
\begin{aligned}
(\nabla_{E_1}S)(E_2,E_3)
 &=-S(\tfrac h2E_3,E_3)-S(E_2,-\tfrac h2E_2)=-h^3/2,\\
(\nabla_{E_2}S)(E_1,E_3)
 &=-S(-\tfrac h2E_3,E_3)-S(E_1,\tfrac h2E_1)=h^3/2,\\
C(E_1,E_2,E_3)&=-h^3=-\epsilon^{-3}\ne0 .
\end{aligned}
\tag{9.11}
$$

The classical three-dimensional conformal-curvature criterion says
that a conformally flat smooth metric has zero covariant Cotton tensor.
Its conformal invariance and this necessary condition are supplied by
García–Hehl–Heinicke–Macías, *The Cotton tensor in Riemannian
spacetimes*, [§§IV–V, (86), (95)](https://arxiv.org/html/gr-qc/0309008v2).
Our derivative-slot convention is that of Kişisel–Sarıoğlu–Tekin,
*Cotton flow*, [Appendix B, (43)–(46)](https://arxiv.org/html/0803.1603v2);
(9.8) also fixes the curvature sign used for every entry above.
The nonzero component was computed from (9.9), not transferred from a
differently indexed Cotton or Cotton–York component. Only vanishing is
used from the conformal criterion.
Equation (9.11) holds at every point of the native chart. Such charts
exist about every interior point, with the same brackets. Consequently
no nonempty interior open subset can satisfy (9.7), contradicting
(9.6) and proving the theorem. $\square$

**Corollary 9.3 (the exact intrinsic-distance comparison also fails).**
For fixed $\epsilon>0$, let $a>0$ be any smooth function on a nonempty
interior open $U$, and let $d_{a^{-1}g_\epsilon}$ be its Riemannian
length distance. No smooth $F:U\to\mathbb R^3$ and constant
$\mathsf D>0$ can preserve the lengths of every local smooth curve
from $a^{-1}g_\epsilon$ to $\mathsf D^{-1}$. Nor can they satisfy

$$
d_{a^{-1}g_\epsilon}(q,q')
 =\big((F(q')-F(q))^{\mathsf T}\mathsf D^{-1}
                              (F(q')-F(q))\big)^{1/2}
\tag{9.12}
$$

for every sufficiently close pair in every neighbourhood of $U$.
In particular this excludes an exact local Euclidean kinetic-distance
readout for the original clock $a=1$.

Proof. Length preservation on all short curve restrictions, followed
by division by their parameter length, gives
$g_\epsilon(v,v)/a=(dFv)^{\mathsf T}\mathsf D^{-1}dFv$
for every tangent vector $v$. Under the distance hypothesis the same
identity follows from
$d_g(q,\gamma(t))/|t|\to\sqrt{g_q(\dot\gamma(0),\dot\gamma(0))}$
for a smooth curve through $q$, applied to $g=a^{-1}g_\epsilon$.
Polarization gives (9.7); positivity forces $dF$ to be invertible.
The calculation (9.8)–(9.11) and the conformal criterion contradict
(9.7) exactly as in Theorem 9.2. $\square$

## 10. The original-clock full-response consumer

**Definition 10.1 (all-start killed response, with its test class).**
For each analytic starting point $q\in\Omega$, use (1.2) with that
starting point, the same fixed source parameters, and the same two
absorbing height faces. This defines the transition family
$H_t^\epsilon$ of Theorem 1.3. Varying the analytic starting point
supplies no actual reset or preparation operation. The point-source
field (1.5) still has its single specified pole $o$.

Let $D\subset\mathbb R^3$ be open, $\mathsf D$ a constant symmetric
positive definite matrix, and $b$ smooth on $D$. Let $S_t^D$ be the
transition semigroup of a diffusion with generator
$\mathcal A_{\mathsf D,b}$, killed on first exit from $D$, with no
interior killing or survival conditioning. Assume the diffusion exists
and has no explosion before that exit. Send each cemetery to a
cemetery and give every test value zero there.
A proposed full-response correspondence consists of one smooth
$F:\Omega\to D$ for which, on a nonempty interior open $U$, for some
$t_*>0$,

$$
H_t^\epsilon(f\circ F)(q)=S_t^D f(F(q)),\qquad
q\in U,\quad 0<t<t_*,\quad f\in C_c^\infty(D).
\tag{10.1}
$$

In particular any correspondence of all-start killed transition laws,
or all-start killed path laws, with the same clock and readout contains
(10.1): apply equality of the time-$t$ distributions to the indicated
bounded tests. A bounded-Borel full-test identity is stronger than the
displayed requirement. No $L^2$-only or exceptional-start interpretation
is included in (10.1).

For a target with a Lebesgue transition density, (10.1) means exactly

$$
\int_\Omega p^\Omega_\epsilon(t,q,q')f(F(q'))\,d\mu(q')
 =\int_D p^D_{\mathsf D,b}(t,F(q),y)f(y)\,dy .
\tag{10.2}
$$

The left kernel uses the unnormalized raw measure and both original
absorbing faces. There is no adjustment of pole strength, Jacobian,
lifetime, or time integral implicit in this formula.

**Theorem 10.2 (full killed response would force the excluded identity).**
For every fixed $\epsilon>0$, Definition 10.1's original-clock
full-response correspondence is impossible. More precisely, (10.1)
would imply the pointwise interior identity

$$
G_\epsilon(f\circ F)(q)
       =(\mathcal A_{\mathsf D,b}f)(F(q)),\qquad
q\in U,\quad f\in C_c^\infty(D),
\tag{10.3}
$$

which is the forbidden case $a=1$, $B=0$ of (9.5).
This implication does not require $f\circ F$ to be in the global
Dirichlet generator domain, or any a priori rank or global injectivity
of $F$.

Proof. Fix $q\in U$ and $f\in C_c^\infty(D)$. The function
$u=f\circ F$ is bounded and smooth in $\Omega$, but its trace at a
height face need not vanish. Choose nested interior coordinate balls
about $q$, and a smooth compactly supported cutoff $\chi$ which is
one on the larger of those balls. Then $v=\chi u\in C_c^\infty(\Omega)$,
with $G_\epsilon v(q)=G_\epsilon u(q)$.

Let $\sigma$ be the source diffusion's first exit from the smaller
ball. Before $\sigma$ the local Itô coefficients are bounded on its
closure. The fourth-moment martingale maximal estimate, together with
the bounded drift, gives
$\mathbb E_q\sup_{s\le t}|X_{s\wedge\sigma}-q|^4
 \le C(t^2+t^4)$ in these coordinates.
At exit the displacement has a fixed positive radius; hence
$\mathbb P_q(\sigma\le t)=O(t^2)=o(t)$.
Paths cannot reach either native absorbing face without this exit.
Since $u=v$ before exit and both are bounded, their killed expectations
at time $t$ differ by $o(t)$. Itô's formula for the compactly supported
$v$, with value zero at the cemetery, gives

$$
\lim_{t\downarrow0}
 \frac{H_t^\epsilon u(q)-u(q)}t
   =G_\epsilon v(q)=G_\epsilon u(q).
\tag{10.4}
$$

For completeness, the martingale estimate used here is the classical
fourth-moment maximal inequality
$\mathbb E\sup_{s\le t}|M_s|^4\le C\mathbb E[M]_t^2$;
local bounded diffusion coefficients make its right side $O(t^2)$,
and the drift supremum contributes $O(t^4)$. This is localization
within the fixed covariance-$2$ law, not a change of clock or a
conditioning on remaining alive.

The same interior localization for the target, whose drift is bounded
on a compact ball around $F(q)$ and whose diffusion covariance is
$2\mathsf D$, gives

$$
\lim_{t\downarrow0}
 \frac{S_t^D f(F(q))-f(F(q))}t
       =\mathcal A_{\mathsf D,b}f(F(q)).
\tag{10.5}
$$

Subtract the common time-zero value in (10.1), divide by $t$ and
use (10.4)–(10.5). This proves (10.3) at every $q\in U$ for every
indicated test. Theorem 9.2 gives the contradiction. The passage from
killed path-law equality to (10.1) uses only its time-$t$ marginal
and the fixed zero value at death, so it needs no reconstruction from
one Green field. $\square$

## 11. Correspondence, attribution and the surviving realization boundary

**Definition 11.1 (classical suppliers and source-specific consequence).**
The conformal-curvature facts in the proof of Theorem 9.2 are
literature-attested intermediates, with the following precise uses.

| Primary source | Mathematical correspondence and scope |
| --- | --- |
| García–Hehl–Heinicke–Macías, *The Cotton tensor in Riemannian spacetimes*, [arXiv:gr-qc/0309008v2](https://arxiv.org/html/gr-qc/0309008v2), §§IV–V | The three-dimensional conformal invariance and the necessity of vanishing Cotton for conformal flatness, particularly (86) and (95). They are applied to the smooth positive metric (9.3) and its hypothetical conformal rescaling (9.7); only the zero-tensor criterion is transferred. |
| Kişisel–Sarıoğlu–Tekin, *Cotton flow*, [arXiv:0803.1603v2](https://arxiv.org/html/0803.1603v2), §§2–3, §5 and §5.5, Appendices A–B | Classical Cotton and homogeneous Nil geometry, with the covariant derivative-slot convention of Appendix B, (43)–(46). Our orthonormal frame has sole bracket $[E_1,E_2]=\epsilon^{-1}E_3$. Using their §5 bracket convention, their Nil choice $(\lambda,\mu,\nu)=(-1,0,0)$ and metric coefficients $A=(2\epsilon)^{-1}$, $B=C=\sqrt{2\epsilon}$ have $ABC=1$; the orthonormal frame $(F_2/\sqrt B,F_3/\sqrt C,-F_1/\sqrt A)$ has precisely our bracket. These supplier symbols are unrelated to the central-noise coefficient $\nu$ in (1.2). No flow equation or borrowed numerical Cotton component enters the proof. |
| Capogna–Citti, *Regularity for subelliptic PDE through uniform estimates in multi-scale geometries*, [arXiv:1504.04762v1](https://arxiv.org/html/1504.04762v1), §2.3, Lemma 2.13 and Remark 2.16 | Regularized intrinsic-distance comparability and local Euclidean bi-Lipschitz behaviour, not an exact constant-symbol identification. Their displayed fields have $(x_1,x_2,x_3)=(x,y,2\theta)$ and regularization parameter $2\epsilon$: the pushforwards of $(U,V,\epsilon Z_H)$ are exactly $(X_1,X_2,2\epsilon\partial_{x_3})$. No time rescaling is made. |

The source-specific consequence is repo-derived: on the original
five-mode cylinder, (9.6) forces a local inverse and the conformal
relation (9.7), which the nonzero tensor (9.11) forbids. Corollary 9.3
translates this to exact kinetic lengths and distances; Theorem 10.2
translates the original-clock all-start full response to the same
necessary operator identity. Homogeneous Nil curvature is a classical
supplier within this argument, not a separate new conclusion.
No literature novelty or Lean certification is asserted.

For comparison with the existing native consumers,
N, Theorem 10.5 concerns two-field generators of the form
$\sum_{i,j\le2}a^{ij}X_iX_j+\sum_{i\le2}b^iX_i$, with
$(X_1,X_2)=(P,Q)$. Its symbol has rank two, so its no-ellipticity proof
does not apply to $G_\epsilon$ at fixed $\epsilon>0$.
K, Definition 33.1 and Proposition 40.1 supply the independent central
noise and rank-three covariance. Here their area drift is zero,
$\nu^2=\epsilon^2$, and their killing, signs and preparations are exactly
(9.1)–(9.2). The rank-three gap is exact local constant-symbol geometry;
it is closed by (9.6)–(9.11), without undoing that supplied noise.
The all-start test distinction is the one used in
[Native free diffusion descent and hidden-circle rigidity, Definition
2.3 and Theorem 3.1](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md):
its carrier and target are the full cylinder and its two-dimensional
bottom quotient, whereas (10.1) asks for a three-dimensional constant-SPD
target. Its lower-dimensional descent is not contradicted.
The long-time tensor in
[Long-time native phase diffusion, §40](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md)
is an occupation-averaged winding limit of a different rank-two law,
not (9.5) on a fixed interior neighbourhood.

The carrier in
[Acquisition of a persistent global port orientation, Definitions
1.1–1.3 and Theorem 3.1](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md)
is a free ordered substitution algebra with one unknown bijection
between physical port names and semantic address names. Its acquired
adapter acts on paid literal-address bits; it supplies no map satisfying
(9.6), no diffusion law on (9.1), and no kinetic-distance or clock
identification. It therefore does not discharge the hypotheses of
(9.5) or (10.1).

**Definition 11.2 (the exact excluded contract and its limits).**
An exact flat kinetic realization in this section means a smooth
three-dimensional readout satisfying (9.5), or the exact length/distance
contract of Corollary 9.3. An exact full propagation realization in the
original clock means a correspondence containing Definition 10.1's
all-start, full-test killed-semigroup identity. A realization which also
claims to identify the full kinetic-plus-Green response must in
particular meet this free propagation requirement; such a joint
contract is therefore excluded by Theorem 10.2.

Equality of a single fitted scalar field $\Gamma_{\epsilon,o}$, or
one pole's integrated occupation data, is not (10.1) or (9.5); no
exclusion is inferred here from that weaker premise. In particular
Theorem 6.2's fixed-start bounded-continuous occupation transfer is not
upgraded to all-start generator correspondence. A nonempty open family
of starts and the full local test class enter Theorem 10.2 explicitly.

The symbols and metrics being compared are the kinetic ones in
(9.2)–(9.4). The conclusions impose no ban on variable anisotropic
coefficients in Euclidean coordinates, curved three-manifolds,
lower-dimensional factors, local or asymptotic metric comparability,
or homogenized Euclidean limits. Nor do they identify an arbitrary
task metric with $g_\epsilon$. The scalar $a$ in Theorem 9.2 grants
no execution retiming: (1.2), (1.5), (6.1) and (10.1) retain their
original clock. Source and target drifts in (9.5) are relaxed comparison
data; the actual law still has no such added drift.

The matched attractive form remains precisely $q_{\epsilon,g}$ of
(1.5), with the same raw unit-source Green field, fixed pole,
periodicity and both absorbing faces. For every fixed $\epsilon>0$
and every $g>0$, its closure, semiboundedness and attained finite
minimum are those of Theorem 4.1. The supercritical small-noise rate is
still Theorem 5.1; nonflatness supplies no additional instability
statement. Physical spatial identification would require its own
source, law, measurement, geometry, clock, operation and resource
correspondence. Equality of dimensions supplies none of those premises.

## 追加锚（本行以下为增补区）

## 12. Fixed-noise capped functionals of the actual paid execution

**Definition 12.1 (joint source, executions and response tests).**
The repository suppliers in §§12–14 are the versions in the snapshot
7fb0a20a7a0335607420e5b87dd79216271b2efd. Retain Definitions 1.1–1.2:
$0<Z<1$, $r=1-Z$, $H=r/2$, $0<l<k_o<u<H$, arbitrary fixed
preparation phases, both actual $2\pi$ periods, the original
probabilities and negative amplitude convention, and the raw measure
$d\mu=dk\,d\alpha\,d\beta$ on $\Omega=(l,u)\times\mathbb T^2$.
Fix the interior pole $o$, signed $\nu\ne0$, $\epsilon=|\nu|$,
$g>0$ and $0<T<\infty$. The target is exactly (1.2), with zero
area drift, the persistent independent covariance-$2$ triple and its
original height killing. Write $E_0=[l,u]\times\mathbb T^2$.
Use K, Definition 13.1's actual coordinate metric

$$
\begin{aligned}
d_{\max}(q,q')
 &=\max\{|k-k'|,d_{\mathbb T}(\alpha,\alpha'),
                         d_{\mathbb T}(\beta,\beta')\},\\
d_{\mathbb T}([a],[b])&=\min_{m\in\mathbb Z}|a-b-2\pi m|,
\qquad D_{\max}(x,y)=\sup_{0\le t\le T}d_{\max}(x_t,y_t).
\end{aligned}
\tag{12.1}
$$

For each deterministic allowed tolerance $\eta$ and risk
$0<\delta<1/4$, take the *actual issued execution* of O,
Definitions 50.1–52.1 and Theorems 51.3, 52.2, 53.1.
Choose a fixed $\bar\nu\ge|\nu|$ for that supplier. Its paid times
are $t_i=ih$, $h=T/n$, with $n$ exactly O, (52.3); its seed is
independent of the entire persistent triple. Its acquired filtration
is K, Definition 41.1's paid wrapped current points, seed, known law,
known own execution and clock. The internal generation in O does not
replace the actual target in any functional below. Let $\bar q_N$
be its actual held path, $\tau_N$ its actual own height exit, and
$q_N^\dagger$ its path sent to the cemetery at that exit. The label
$N$ denotes this parameterized family member. Keep the original
ordinary chronology $j_N=\int a_N\,db_N$, whole-height extrema guard,
source domain and all four unhalved costs (6.1). Own boundary holds,
initial zero hold, interrupted final legs and rejected-input holds
are exactly those of O, Definition 51.2; no leg is accelerated.

Let $\bar q$ and $q^\dagger$ denote the corresponding held and killed
actual target, and put $S=T\wedge\tau$, $S_N=T\wedge\tau_N$.
In O, (51.1), $\vartheta=\eta/4$, so write

$$
d_\eta=(\eta/(4\Gamma))^2,\qquad
 e_\eta=2h+d_\eta\le C\eta^2,
\tag{12.2}
$$

where $\Gamma$ is that supplier's fixed controller constant. On its
probability-one regular event, O supplies unconditionally
$0\le S_N-S\le e_\eta$; on its supplied good event $G$ it also
supplies $D_{\max}(\bar q_N,\bar q)\le\eta$ and
$\mathbb P(G^c)\le\delta$. No independence of $G$ is assumed.

Set $V=\Gamma_{\epsilon,o}$, with $V(o)=+\infty$ and zero extension
to both absorbing faces and to the cemetery. For $B>0$, let
$V_B=\min(V,B)$ in the interior, $V_B(o)=B$, with the same zero
boundary and cemetery values. Define, on the actual coupling,

$$
\begin{aligned}
A&=\int_0^S V(\bar q_t)dt,&
 A_B&=\int_0^S V_B(\bar q_t)dt,&
 A_{NB}&=\int_0^{S_N}V_B(\bar q_N(t))dt,\\
W&=e^{gA},& W_B&=e^{gA_B},& W_{NB}&=e^{gA_{NB}}.
\end{aligned}
\tag{12.3}
$$

These are original-time integrals, without survival normalization or
conditioning on success. For an analytic starting point $x$, use
$A^x,A_B^x$ for the same killed target integrals with that start and
with the *unchanged pole* $o$. Such starts are analytic probes, not
additional preparation operations. Let $\mathcal F_1$ be the real
continuous functions on $E_0$ which vanish at both faces, have
$\|f\|_\infty\le1$ and $\operatorname{Lip}_{d_{\max}}f\le1$;
set $f(\dagger)=0$. Let $\mathsf H$ be the self-adjoint operator of
the already closed form $q_{\epsilon,g}$ in Theorem 4.1, namely the
form realization of $L_\epsilon-gV$.

**Theorem 12.2 (quantitative paid response to the uncapped matched form).**
Under Definition 12.1, the expectation

$$
R(f)=\mathbb E_o[Wf(q^\dagger(T))]
       =(e^{-T\mathsf H}f)_{\rm canonical}(o)
\tag{12.4}
$$

is the value at $o$ of the unique continuous representative on $E_0$
with zero boundary values of $e^{-T\mathsf H}f$. In particular the
pole value is canonical, rather than an arbitrary value of an
almost-everywhere representative. Put
$R_{NB}(f)=\mathbb E[W_{NB}f(q_N^\dagger(T))]$.
There are $B_0\ge1$, $K\ge1$ and $C<\infty$, depending only on
the fixed data in Definition 12.1 and the fixed supplier constants,
such that for every $B\ge B_0$ and allowed $\eta,\delta$ satisfying

$$
 gK(B^2\eta+B e_\eta)\le1,
\tag{12.5}
$$

one has

$$
\mathbb E|W_{NB}-W|
 +\sup_{f\in\mathcal F_1}|R_{NB}(f)-R(f)|
 \le C\left[B^{-1}+B^2\eta+B e_\eta
                    +\sqrt\delta+\delta e^{gBT}\right].
\tag{12.6}
$$

All quantities in this inequality are Borel measurable for the actual
paid policy, and all unsuccessful outcomes remain in its expectations.
Constants need not remain bounded as $\epsilon\downarrow0$ or
$T\to\infty$.

**Proof.** First establish the analytic estimates for the actual killed
target. Write
$\mathcal G(x,y)=\int_0^\infty p^\Omega_\epsilon(t,x,y)dt$.
For this fixed positive $\epsilon$, (2.4), the exact deck action (2.3),
killed-kernel domination and Theorem 1.3's tail give

$$
\begin{aligned}
\sup_{x,y}p^\Omega_\epsilon(t,x,y)&\le C t^{-3/2}
                                      &&(0<t\le1),\\
\mathcal G(x,y)&\le C(1+d_{\max}(x,y)^{-1})
                                      &&(x\ne y).
\end{aligned}
\tag{12.7}
$$

Here is the spatial content of the second estimate. Center (2.1) at
any point of the compact closed cylinder. For fixed $\epsilon>0$,
the smooth elliptic metric and the wrapped coordinate metric are
locally comparable, with constants uniform over a finite chart cover.
The identity deck image therefore has small-time bound
$Ct^{-3/2}\exp(-c d_{\max}(x,y)^2/t)$ for close pairs. Every other
image is separated in these charts and their polynomial counting
bound in Theorem 3.1 sums their contributions to
$Ct^{-2}e^{-a/t}$. For separated pairs the same estimate is integrable
uniformly. Killing can only reduce these free periodic bounds, also
in charts meeting a face. Integration of the close-pair bound gives
$C/d_{\max}(x,y)$; integration of the image error and of the full
large-time tail gives the constant. This proves (12.7) for both
kernel variables, without substituting a whole-space tail. All raw
Jacobian factors are those in (2.2).

Symmetry, the semigroup identity and Tonelli imply, for $s>0$,

$$
 (H_s^\epsilon V)(x)=\int_s^\infty
                    p^\Omega_\epsilon(v,o,x)dv.
\tag{12.8}
$$

Consequently, for $0<t\le1$,

$$
\sup_{x\in\Omega}\mathbb E_x
 \int_0^{t\wedge\tau}V(q_s)ds\le C\sqrt t.
\tag{12.9}
$$

This is the all-start small-time Kato bound for this killed law,
including the start $x=o$. Indeed (12.7) and the tail bound the
right side of (12.8) by $C(1+s^{-1/2})$ for $s\le1$;
integrate in $s$. Boundary starts can be included as already killed.
The value $+\infty$ at the initial single time has zero Lebesgue
measure. The same argument ensures that the nonnegative occupation
is finite almost surely at every start on a finite horizon.

For completeness, the classical Khas'minskii moment argument yields
all the fixed-coupling strength needed here, without an exceptional
starting set. Given $a>0$, choose $t_a>0$ with the left side of
(12.9), multiplied by $a$, at most $1/2$. Extend the killed target
by an absorbing cemetery with potential zero. Ordering the $m$ time
variables in its $m$th occupation moment, and conditioning successively
on the target's past, bounds the moment by $m!(1/2)^m$ on an interval
of length at most $t_a$. This first holds for bounded caps and passes
to $V$ by monotone convergence. The exponential series and the Markov
property of this *target* then give

$$
M_a(T):=\sup_{x\in\Omega}\mathbb E_x e^{a A^x}
                   \le2^{\lceil T/t_a\rceil}<\infty.
\tag{12.10}
$$

The notation $A^x$ here uses horizon $T$ as in (12.3). This is the
classical argument in Güneysu, *On generalized Schrödinger semigroups*,
[arXiv:1109.0151v3, Proposition 2.5 and its proof](https://arxiv.org/html/1109.0151v3).
In particular (12.10) bounds the exponential of the occupation stopped
at death even on paths that die before $T$, not just its product with
a survival indicator. It asserts no Markov property for $\bar q_N$.

We next need a tail estimate stronger than a first moment at $o$.
Choose a small injective Euclidean coordinate ball about $o$ and let
$\rho(y)$ be coordinate radius there. Theorem 3.1 at fixed $\epsilon$
and local metric equivalence give
$c/\rho(y)\le V(y)\le C/\rho(y)$ in a smaller punctured ball.
Off that ball $V$ is bounded, including its zero boundary collars.
For all sufficiently large $B$, therefore,

$$
U_B:=(V-B)_+\le C\rho^{-1}
          \mathbf1_{\{\rho<C/B\}},\qquad
 m_B:=\sup_x\int_\Omega\mathcal G(x,y)U_B(y)d\mu(y)
                    \le C/B.
\tag{12.11}
$$

To verify the supremum, set $b=C/B$. For $x$ in a fixed small pole
chart, (12.7) reduces the singular part to a constant times
$\int_{|y|<b}|x-y|^{-1}|y|^{-1}dy$. If $|x|\le2b$,
Cauchy–Schwarz bounds it by

$$
\left(\int_{|y|<b}|x-y|^{-2}dy\right)^{1/2}
\left(\int_{|y|<b}|y|^{-2}dy\right)^{1/2}\le Cb;
\tag{12.12}
$$

the first integration region translates into $|x-y|<3b$.
If $|x|>2b$, the bound is $Cb^2/|x|\le Cb$. Starts outside that
chart have positive separation from the support and give $Cb^2$.
The nonsingular kernel term also gives $Cb^2$. The smooth coordinate
Jacobian is bounded (and (2.2)'s Jacobian is constant), so these are
bounds for the raw measure, uniformly in all starts.

Put $D_B^x=A^x-A_B^x=\int_0^{T\wedge\tau}U_B(q_s)ds$.
The first-moment bound in (12.11) is valid for every remaining horizon,
since it uses the entire killed Green kernel. Ordering two time
variables and using the target Markov property gives

$$
\sup_x\mathbb E_xD_B^x\le m_B,\qquad
\sup_x\mathbb E_x(D_B^x)^2\le2m_B^2\le C B^{-2}.
\tag{12.13}
$$

Truncate $U_B$ first if necessary, and pass monotonically; hence this
argument does not assume the second moment it proves. Since
$1-e^{-z}\le z$ for $z\ge0$, Cauchy–Schwarz, (12.10) at $2g$ and
(12.13) yield the weighted estimate

$$
\sup_x\mathbb E_x|e^{gA^x}-e^{gA_B^x}|
 \le g\sup_x\mathbb E_x[e^{gA^x}D_B^x]
 \le gM_{2g}(T)^{1/2}\sup_x\|D_B^x\|_2
 \le C/B.
\tag{12.14}
$$

Thus the unweighted singular-tail occupation and the exponentially
weighted cap error both have the required uniform $B^{-1}$ rate.

We also require regularity in the *tracking* metric. In the pole chart,
let $R=V-m_0^{-1}\mathcal G_\epsilon$. The two terms have exactly
the same distributional unit source for the raw measure, by (1.7)
and (2.2). Their difference is locally integrable and satisfies the
smooth elliptic homogeneous equation distributionally across the pole.
Classical interior elliptic regularity therefore makes $R$ smooth
across it, with bounded first derivatives on a smaller chart. This
step uses its equation; boundedness of (3.2) alone is not differentiated.
The whole-group first-derivative heat estimate of
Capogna–Citti–Manfredini,
[arXiv:1212.6665v2, Proposition 2.2, (2.9)](https://arxiv.org/html/1212.6665v2),
applied to $(U,V,\epsilon Z_H)$ with coefficient matrix $I_3$,
has integrable derivative bound $Ct^{-2}e^{-c\rho^2/t}$ for
$0<t\le1$ and $Ct^{-5/2}$ for $t\ge1$, at fixed $\epsilon$.
Its integral is at most $C(1+\rho^{-2})$. Conversion from this frame
to coordinate derivatives has bounded coefficients on the chart,
with constants allowed to depend on $\epsilon$. Consequently

$$
|\nabla V|\le C\rho^{-2}\quad\text{near }o.
\tag{12.15}
$$

On each of the two boundary collars the pole is absent. The field
solves the homogeneous smooth uniformly elliptic Dirichlet equation
with zero smooth data. Classical boundary regularity, as used in
Proposition 7.1, gives bounded first derivatives up to each face.
The rest of the closed cylinder outside the pole chart is compact
and smooth in finitely many periodic charts.

For $V<B$ near $o$, the lower bound $V\ge c/\rho$ forces
$\rho\ge c/B$, so (12.15) bounds the derivative there by $CB^2$.
Where $V>B$ the cap is constant; it is constant also on an actual
neighbourhood of $o$. Across a level $V=B$, composition with the
one-Lipschitz scalar truncation preserves local Lipschitz continuity.
The compact region and both boundary collars have the same $CB^2$
bound after increasing $B_0,C$. Join any two wrapped states by the
straight height segment and shortest circle arcs, using the finite
periodic chart cover. This path has sum of coordinate variations at
most $3d_{\max}(q,q')$; the derivative bounds apply to its restrictions,
also at transitions to the pole plateau or to a face. Hence

$$
\operatorname{Lip}_{d_{\max}}(V_B)\le CB^2
                         \quad(B\ge B_0).
\tag{12.16}
$$

We now identify the singular response with the *existing* form operator.
Let $\mathsf H_B$ be the operator of
$T_\epsilon-g\int V_B|u|^2d\mu$ on $\mathcal F_\epsilon$.
For bounded $V_B$, expansion of the exponential in ordered times and
the killed target Markov property give the norm-convergent Duhamel
series for the bounded multiplication perturbation. Therefore at every
interior start, for $f\in C(E_0)$ with zero boundary values,

$$
(e^{-T\mathsf H_B}f)(x)
 =\mathbb E_x[e^{gA_B^x}f(q^\dagger(T))],
\tag{12.17}
$$

with the continuous zero-boundary representative on the left. To see
continuity, the original Dirichlet elliptic heat family preserves
continuous zero-boundary functions, and so does each term of this
uniformly convergent bounded-potential series. The height faces are
regular absorbing faces; there is no exceptional pole for a bounded
continuous cap.

Here is a form-level check that these operators approach precisely
Theorem 4.1's $\mathsf H$. The free inverse $L_\epsilon^{-1}$ exists
by the positive height Dirichlet gap. Its positive symmetric kernel is
$\mathcal G$. Weighted Schur, exactly as in (4.5), now with
$U_B$ and that inverse, gives

$$
\int U_B|u|^2d\mu\le m_B T_\epsilon[u]
       \le (C/B)T_\epsilon[u],\qquad u\in\mathcal F_\epsilon.
\tag{12.18}
$$

One can first truncate $U_B$ and use the Schur weight equal to its
square root on its positive support, then pass monotonically.
Theorem 4.1 gives one fixed shift $a>0$ for which
$q_{\epsilon,g}+a\|\cdot\|_2^2$ is coercive in the free form norm.
Every capped form plus this shift is at least that form. The positive
tail's polarization in (12.18) bounds the difference of their
sesquilinear forms by $C/B$ times the two free form norms.
Subtracting the two variational resolvent equations and testing on
their difference gives

$$
\|(\mathsf H_B+a)^{-1}-(\mathsf H+a)^{-1}\|_{2\to2}\le C/B.
\tag{12.19}
$$

For detail, each variational solution has free form norm at most
$C\|F\|_2$ for right side $F$; the equation for their difference
has right side the tail form evaluated on one solution. Coercivity
and (12.18) bound its free form norm by $CB^{-1}\|F\|_2$.
The common lower spectral bound and the continuous functional calculus
then imply $e^{-T\mathsf H_B}\to e^{-T\mathsf H}$ in $L^2$ operator
norm: write $e^{-T\lambda}$ as a continuous function of
$(\lambda+a)^{-1}$ on the common bounded spectral interval, with
value zero at inverse spectral value zero, and approximate by polynomials.

By (12.14), the right sides of (12.17) converge uniformly over all
starts to $\mathbb E_x[e^{gA^x}f(q^\dagger(T))]$.
This uniform limit is continuous on $E_0$, zero at the faces, and
by (12.19) represents $e^{-T\mathsf H}f$ in $L^2(\mu)$.
Since the raw measure has full support in the interior, two continuous
representatives of that class agree everywhere in the interior, and
zero boundary extension determines their boundary values. This proves
(12.4), including its canonical value at the pole.

The scalar Feynman–Kac principle used in this identification is
literature-attested in Güneysu, Theorem 2.9. Its statement is an
almost-everywhere formula, not a choice of pole representative;
(12.14)–(12.19) supply that additional choice here. In his
$-\Delta/2$ convention, take the analytic metric $g_\epsilon/2$
from (9.2)–(9.3): its volume is the constant
$2^{-3/2}(2r/\epsilon)d\mu$, and
$-\Delta_{g_\epsilon/2}/2=L_\epsilon$. Thus the potential is exactly
$-gV$ with the same clock, not a retimed operator or a probability
renormalization of its unit source. Theorem 2.9 itself requires no
geodesic completeness. The complete-manifold $L^p$ sufficient criterion
in his Theorem 2.2 is not used for this open killed cylinder;
(12.9) verifies its actual Kato obligation directly. The bounded-cap
and variational proof above also checks the prescribed Dirichlet
realization without relying on an unverified completeness assumption.

It remains to compare the actual issued path, not an internally
generated marginal. On the supplied event $G$, (12.16) through the
common live interval and the unconditional own-delay bound give

$$
|A_{NB}-A_B|\le CTB^2\eta+B(S_N-S)
       \le K(B^2\eta+B e_\eta)=:\xi.
\tag{12.20}
$$

There is no change of variables in either occupation integral. On
$G$, (12.5) and $W_B\le W$ imply

$$
 |W_{NB}-W_B|\le(e^{g\xi}-1)W_B\le e g\xi W.
\tag{12.21}
$$

On $G^c$, every actual capped path still satisfies
$0\le A_{NB}\le BT$, regardless of its accuracy or extra holds.
Thus, without a success-independence premise,

$$
\begin{aligned}
\mathbb E[\mathbf1_{G^c}|W_{NB}-W_B|]
 &\le\delta e^{gBT}+\mathbb E[\mathbf1_{G^c}W]\\
 &\le\delta e^{gBT}+\sqrt\delta M_{2g}(T)^{1/2}.
\end{aligned}
\tag{12.22}
$$

Combining (12.14), (12.20)–(12.22) proves

$$
\mathbb E|W_{NB}-W|
 \le C[B^{-1}+B^2\eta+B e_\eta+\sqrt\delta+\delta e^{gBT}].
\tag{12.23}
$$

For the terminal tests, the zero boundary condition is essential.
On every input, $f(q_N^\dagger(T))=f(\bar q_N(T))$, and the analogous
target identity holds, since a killed path's held endpoint is on a
face where $f$ vanishes. Hence on $G$, even if exactly one process
has died, the terminal discrepancy is at most $\eta$ by (12.1).
On $G^c$ it is at most two. Therefore

$$
\begin{aligned}
|R_{NB}(f)-R(f)|
 &\le\mathbb E|W_{NB}-W|
       +\mathbb E[W|f(q_N^\dagger(T))-f(q^\dagger(T))|]\\
 &\le\mathbb E|W_{NB}-W|
       +\eta M_g(T)+2\sqrt\delta M_{2g}(T)^{1/2}.
\end{aligned}
\tag{12.24}
$$

This bound is uniform in $\mathcal F_1$. Since $B\ge1$, the extra
$\eta$ is absorbed into $B^2\eta$. Equations (12.23)–(12.24)
prove (12.6). In particular no isolated-cemetery uniform tube and
no equality of own and target lifetimes have been assumed.

Finally, these are lawful measurable functionals of the stated paid
execution. O, Definitions 50.2, 51.2 and Theorem 51.3 provide Borel
kernel selections, parameter choices, continuous lifts, finite
piecewise affine profile validation and the irrevocable-hold defaults
on exceptional inputs. With the deterministic finite grid, every
issued numerical profile is measurable in the already acquired records,
seed and clock; at most $n+1$ are issued on every input. Joins,
whole-height guards, the ordinary chronological integral and own
cutoff remain those of the supplier. The resulting held path is a
Borel random element of $C([0,T];E_0)$, and its first height hit and
killed endpoint are Borel. As $V_B$ is continuous on $E_0$,
$A_{NB}=\int_0^T V_B(\bar q_N(t))dt$ is a Borel functional, with
the equality using its zero value on an own boundary hold.
Target occupations are monotone limits of their bounded Borel caps;
(12.9)–(12.10) prove their almost-sure finiteness and the needed
moments. All weight and response expectations are consequently defined.
The null fallback set has a lawful bounded capped integral, while
positive-probability failed tracking outcomes are charged in (12.22)
and in O's unconditional execution bounds. No native Markov property,
unseen source-dependent interruption, continuous actual observation
or changed source law has entered the comparison. $\square$

## 13. A simultaneous cap schedule and its original resources

**Corollary 13.1 (one quantitative diagonal with charged execution).**
Under Definition 12.1, choose a fixed sufficiently small $c>0$ and,
for all sufficiently large $B$, put

$$
\eta=cB^{-3},\qquad \delta=\exp(-(gT+1)B).
\tag{13.1}
$$

For the same actual paid family the left side of (12.6) is $O(B^{-1})$.
Its deterministic Read count and unconditional expected actuator
charges satisfy

$$
\begin{aligned}
M&=O(B^7),\\
\mathbb EV^a,\ \mathbb EV^b,\ \mathbb EL
     &=O(B^3+\epsilon^2B^6),\\
\mathbb EE&=O(B^6+\epsilon^4B^{12}).
\end{aligned}
\tag{13.2}
$$

All constants have the fixed-data scope of Theorem 12.2.

**Proof.** Equation (12.2) gives $e_\eta=O(B^{-6})$, so
$B^2\eta=c/B$ and $Be_\eta=O(B^{-5})$. In particular (12.5),
O's tolerance restriction and $0<\delta<1/4$ hold for all sufficiently
large $B$. Moreover
$\delta e^{gBT}=e^{-B}$ and
$\sqrt\delta=e^{-(gT+1)B/2}$; (12.6) proves the error order.
O, Theorem 52.2 gives, for this very family,

$$
\begin{aligned}
M&\le C\eta^{-2}\log\frac e{\eta\delta},\\
\mathbb EV^a,\ \mathbb EV^b,\ \mathbb EL
 &\le C(\eta^{-1}+\nu^2\eta^{-2}),\\
\mathbb EE&\le C(\eta^{-2}+\nu^4\eta^{-4}).
\end{aligned}
\tag{13.3}
$$

Here $\log(e/(\eta\delta))=1-\log c+3\log B+(gT+1)B=O(B)$.
Substitution proves (13.2). These are O's actual unconditional charges
through own death or the horizon, with all failed outcomes and partial
terminal legs. No success-conditioned resource estimate is substituted.
$\square$

## 14. Mathematical correspondence and remaining stronger contracts

**Definition 14.1 (content and applicability of the cap bridge).**
The source-specific conclusion of Theorem 12.2 is the quantitative
map from O's actual paid execution on the persistent source to the
exact uncapped response of its *matched* form $q_{\epsilon,g}$,
including the pole representative, its own lifetimes and all outcomes.
Theorem 4.1's closure and domain, O's controller and Borel replay,
Capogna–Citti–Manfredini's whole-group kernel bounds, classical smooth
elliptic interior and boundary regularity, Schur's test, the
Khas'minskii moment argument and the scalar Feynman–Kac principle are
reused intermediates. Güneysu's Proposition 2.5 and Theorem 2.9 supply
the credited moment and semigroup principles with their stated
almost-everywhere scope; the quantitative actual-execution comparison,
weighted tail rate and canonical pole limit are derived in (12.7)–(12.24).
This is repo-derived composition with an explicit parameter and
source correspondence, without a literature-novelty or Lean claim.

The observables in (12.3) are capped in the field at each finite stage;
there is no second cap on the total weight. Their exact limiting target
remains $W=e^{gA}$ and (12.4). The original paid rule issues a positive
initial zero hold of duration $h$ at $o$. It therefore retains
Proposition 7.1's obstruction: its literal uncapped native exposure
is infinite for each such family member, even though (12.6) holds.
No uncapped-exposure or uniform-integrability claim for that producer
is part of the cap bridge.

The resource orders in (13.2) count analytic native variations, length,
energy and Reads under K's existing AC-profile permission and O's
exact-real paid interface. They bound neither arithmetic, seed bits,
field evaluation, profile generation nor a total service tariff.
Equation (12.4) is an attractive weighted response of the free killed
law, not a sampler for an attractive diffusion and not a changed-law
finite service. It provides no operation to reset an analytic start,
no physical spatial identification, and no removal of the fixed-noise
or finite-horizon conditions. The exact flat-geometry and all-start
constant-symbol obstructions of §§9–11 concern their stronger
correspondence contracts and remain compatible with this fixed-start
same-source capped response limit.

## 追加锚（本行以下为增补区）

## 15. The unit whole-group model for the fixed native source

**Definition 15.1 (source, domains and dimensionless coupling).** Repository
suppliers in §§15–17 follow Definition 1.1's fixed revision, except the
crossover supplier explicitly pinned in Corollary 17.2. The fixed-noise
paid response of Theorem 12.2 and Corollary 13.1 keeps Definition 12.1's
supplier revision and finite-horizon scope.
Retain exactly Definitions 1.1–1.2: $0<Z<1$, $r=1-Z$, $H=r/2$,
$0<l<k_o<u<H$, arbitrary fixed preparation phases, both actual
$2\pi$ phase periods, the pole $o$, and the raw measure
$d\mu=dk\,d\alpha\,d\beta$ on $\Omega=(l,u)\times\mathbb T^2$.
The target has the covariance-$2$ law (1.2), zero area drift, independent
central coefficient $\nu$ with $\epsilon=|\nu|$, first-exit killing at
both height faces and original clock $e^{-tL_\epsilon}$.
The potential is the full unit-source field $\Gamma_{\epsilon,o}$ of
(1.5), without source averaging, a time cutoff or survival normalization.
For every $\epsilon>0$ use the entire original domain
$\mathcal F_\epsilon$ of (1.3), including its periodicity and both zero
height traces. At zero noise $\mathcal F_0$ is the horizontal closure;
no identification with a positive-noise domain is made.

In the exact chart (2.1),

$$
x=k-k_o,\quad y=2(\alpha-\alpha_o),\quad
\theta=-r\{\beta-\beta_o-c(k_o)y\}-xy/2,
\qquad d\mu=m_0\,d\xi,\quad m_0=(2r)^{-1},
\tag{15.1}
$$

where $\xi=(x,y,\theta)$ and $(P,Q,Z_c)=(U,V,Z_H)$ as in (2.2).
All whole-group integrals below use Lebesgue measure $d\xi$, not
$d\mu$. Define the closed free unit-noise form and its associated
positive operator $\mathcal L_1$ by

$$
\begin{aligned}
\mathcal T_1[u]&=\|Uu\|_2^2+\|Vu\|_2^2+\|Z_Hu\|_2^2,\\
\mathcal H_1&=\overline{C_c^\infty(\mathbb R^3)}
 ^{(\|\cdot\|_2^2+\mathcal T_1)^{1/2}},\\
\mathcal Q_\gamma[u]&=\mathcal T_1[u]
 -\gamma\int_{\mathbb R^3}\mathcal G_1|u|^2\,d\xi,\\
e(\gamma)&=\inf_{u\in\mathcal H_1,\ \|u\|_2=1}
                         \mathcal Q_\gamma[u],\qquad \gamma>0.
\end{aligned}
\tag{15.2}
$$

The derivative closure is the whole-group form domain; it is not
asserted to be the isotropic Euclidean $H^1(\mathbb R^3)$ domain.
The coupling corresponding to the native form is $\gamma=g/m_0$.
The intrinsic metric remains $d_\epsilon$, with the exact-comparison
boundaries of Theorem 9.2, Corollary 9.3, Theorem 10.2 and Definition
11.2: local constant-symbol readout, exact intrinsic Euclidean distance,
and original-clock all-start full killed response are the respective
excluded contracts. The local model (15.1) is the Heisenberg model of
§2, with its actual deck transformations, not an exact Euclidean
replacement for any of those contracts.

**Proposition 15.2 (the unit variational problem and uniform native
localization).** For every $\gamma>0$, $\mathcal Q_\gamma$ is closed
and semibounded on exactly $\mathcal H_1$, has a form norm equivalent
to a sufficiently shifted free norm, and

$$
-\infty<e(\gamma)\le0.
\tag{15.3}
$$

Its normalized infimum can be taken over $C_c^\infty(\mathbb R^3)$.
For each fixed finite $\epsilon_0>0$, a fixed injective source chart
$U_o$ has the remainder bound (3.2), uniformly for
$0<\epsilon\le\epsilon_0$. For every fixed neighbourhood $N$ of $o$
there is $C_N<\infty$ such that

$$
\sup_{0<\epsilon\le\epsilon_0}\,
\sup_{q\in\Omega\setminus N}\Gamma_{\epsilon,o}(q)\le C_N.
\tag{15.4}
$$

**Proof.** The whole-group estimate (2.4), with unit noise, gives

$$
\sup_\xi h_1(t,\xi)\le
                  \frac{C}{t^{3/2}(1+\sqrt t)}.
\tag{15.5}
$$

This is the constant-coefficient scaled-frame application of
Capogna–Citti–Manfredini, [arXiv:1212.6665v2, Proposition 2.2,
(2.8), (2.11)](https://arxiv.org/html/1212.6665v2), with matrix $I_3$,
combined with the ball volume in §2. The regularized gauge is the
Capogna–Citti [Lemma 2.13](https://arxiv.org/html/1504.04762v1)
intermediate, with coordinates $(x_1,x_2,x_3)=(x,y,2\theta)$ and
regularization parameter $2\epsilon$. These correspondences do not
rescale the original clock.

Write $R_a=(\mathcal L_1+a)^{-1}$. Positivity, convolution of the
whole-group heat kernels and Tonelli give

$$
R_a\mathcal G_1(\xi)
 =\int_0^\infty\frac{1-e^{-at}}a h_1(t,\xi)\,dt.
\tag{15.6}
$$

For $a\ge1$, split at $a^{-1}$ and $1$, and use
$(1-e^{-at})/a\le\min(t,a^{-1})$. The three bounds are

$$
\begin{aligned}
\|R_a\mathcal G_1\|_\infty
&\le C\left\{\int_0^{a^{-1}}t^{-1/2}dt
 +a^{-1}\int_{a^{-1}}^1t^{-3/2}dt
 +a^{-1}\int_1^\infty t^{-2}dt\right\}\\
&\le C_1a^{-1/2}.
\end{aligned}
\tag{15.7}
$$

For $W_M=\mathcal G_1\wedge M$, the positive symmetric kernel of
$W_M^{1/2}R_aW_M^{1/2}$ has Schur bound $C_1a^{-1/2}$ with weight
$W_M^{1/2}$: its weighted kernel integral is
$W_M^{1/2}R_aW_M\le C_1a^{-1/2}W_M^{1/2}$.
The adjoint operator gives the other Schur inequality. Equivalently,
$\|W_M^{1/2}(\mathcal L_1+a)^{-1/2}\|^2\le C_1a^{-1/2}$.
Apply this to $(\mathcal L_1+a)^{1/2}u$ and then let $M\uparrow\infty$.
Monotone convergence proves, on the entire free domain,

$$
\int\mathcal G_1|u|^2\,d\xi
 \le C_1a^{-1/2}
            \{\mathcal T_1[u]+a\|u\|_2^2\},
\qquad u\in\mathcal H_1.
\tag{15.8}
$$

Thus the potential is infinitesimally form bounded. The classical KLMN
theorem, Teschl, [*Mathematical Methods in Quantum Mechanics*, §6.5,
Theorem 6.24](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf),
applies with $\gamma C_1a^{-1/2}<1$. It gives closedness and
semiboundedness on the same domain. The two form norms are equivalent,
so the defining smooth free core is also a core for $\mathcal Q_\gamma$.
Potential integrals converge along that core by (15.8) and
Cauchy–Schwarz in the weighted $L^2$ space. In particular their Rayleigh
quotients converge, proving the core assertion and $e(\gamma)>-\infty$.

For normalized $u\in C_c^\infty(\mathbb R^3)$ put
$D_su=s^{-2}u\circ\delta_{1/s}$. The Jacobian is $s^4$, and exact
homogeneity gives

$$
\|D_su\|_2=1,\qquad
\mathcal T_1[D_su]
=s^{-2}(\|Uu\|_2^2+\|Vu\|_2^2)+s^{-4}\|Z_Hu\|_2^2\longrightarrow0
\quad(s\to\infty).
\tag{15.9}
$$

Since $\mathcal G_1\ge0$, $e(\gamma)\le\mathcal Q_\gamma[D_su]
\le\mathcal T_1[D_su]$. This proves $e(\gamma)\le0$ without an
attainment assertion on the whole group.

The uniform native remainder is Theorem 3.1, including its periodic
image estimate and full killed-time tail. To verify (15.4), take a
smaller smooth source neighbourhood $B\Subset N\cap U_o$ containing
$o$. On $\partial B$, (3.2) and (2.4) bound the field uniformly:
the compact boundary has $d_{\epsilon_0}(0,\cdot)>0$ and
$d_\epsilon\ge d_{\epsilon_0}$ for $\epsilon\le\epsilon_0$.
For each fixed positive $\epsilon$, the field is $L_\epsilon$-harmonic
on $\Omega\setminus\overline B$, periodic in the actual phases,
continuous with zero trace at both height faces, and smooth elsewhere
there. The elliptic maximum principle bounds it by its inner-boundary
supremum. This bound is independent of $\epsilon$; no uniform
ellipticity constant is required by this application for each member.
It proves (15.4), including near the killed faces. $\square$

## 16. Exact small-noise coefficient, critical coupling and concentration

**Theorem 16.1 (the coefficient on the full native form domain).** For
every fixed $g>0$ and all fixed native data of Definition 15.1,

$$
\lim_{\epsilon\downarrow0}\epsilon^2E_\epsilon(g)=e(g/m_0).
\tag{16.1}
$$

For each fixed finite $\epsilon_0>0$ there is $C_g<\infty$, depending
also on those fixed data and $\epsilon_0$, such that

$$
E_\epsilon(g)\ge\epsilon^{-2}e(g/m_0)-C_g,
\qquad 0<\epsilon\le\epsilon_0.
\tag{16.2}
$$

**Proof.** For normalized $u\in C_c^\infty(\mathbb R^3)$ and small
$\epsilon$, define a native function by

$$
f_\epsilon(\Phi_o(\delta_\epsilon\xi))
       =m_0^{-1/2}\epsilon^{-2}u(\xi),
\tag{16.3}
$$

and extend it by zero outside the source chart. Its support is compact
inside that chart for sufficiently small $\epsilon$. Hence
$f_\epsilon\in\mathcal F_\epsilon$ with both wall traces zero and
$\|f_\epsilon\|_{L^2(\mu)}=1$. Exact field homogeneity and (2.5) give

$$
\begin{aligned}
T_\epsilon[f_\epsilon]&=\epsilon^{-2}\mathcal T_1[u],\\
V_\epsilon[f_\epsilon]
 &=m_0^{-1}\epsilon^{-2}\int\mathcal G_1|u|^2\,d\xi+O(1),\\
q_{\epsilon,g}[f_\epsilon]
 &=\epsilon^{-2}\mathcal Q_{g/m_0}[u]+O_g(1).
\end{aligned}
\tag{16.4}
$$

The second line uses the full native remainder (3.2), whose error
integral is at most $B\|f_\epsilon\|_2^2=B$.
It retains all native deck images, both killing walls and the complete
time integral. Taking the limsup and then the infimum over this core,
as justified by Proposition 15.2, proves the upper bound in (16.1).

For the lower bound, choose smooth real $\chi,\psi$ on the cylinder
with $\chi^2+\psi^2=1$, $\chi=1$ near $o$,
$\operatorname{supp}\chi\Subset U_o$, and $\psi=0$ near $o$.
One construction is $\chi=\cos a$, $\psi=\sin a$, where $a=0$ near
$o$ and $a=\pi/2$ outside a compact subset of $U_o$.
Multiplication by either cutoff preserves every $\mathcal F_\epsilon$.
The product rule and $\chi D\chi+\psi D\psi=0$ for each of
$D=P,Q,Z_c$ give the IMS form identity

$$
\begin{aligned}
q_{\epsilon,g}[f]
 &=q_{\epsilon,g}[\chi f]+q_{\epsilon,g}[\psi f]
                   -\int B_\epsilon|f|^2\,d\mu,\\
B_\epsilon&=|P\chi|^2+|P\psi|^2+|Q\chi|^2+|Q\psi|^2
                +\epsilon^2(|Z_c\chi|^2+|Z_c\psi|^2).
\end{aligned}
\tag{16.5}
$$

The classical IMS identity is Teschl, [Lemma 11.3, (11.12)–(11.13)](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf).
Here the displayed product calculation applies it to the actual three
vector fields. First it holds on the native smooth core; Theorem 4.1's
form continuity and cutoff continuity extend it to the full
$\mathcal F_\epsilon$. Moreover
$\|B_\epsilon\|_\infty\le C_{\rm IMS}$ uniformly for
$0<\epsilon\le\epsilon_0$.

For arbitrary $f\in\mathcal F_\epsilon$, form the zero-extended
whole-group function

$$
u_\epsilon(\xi)=m_0^{1/2}\epsilon^2
                         (\chi f)(\Phi_o(\delta_\epsilon\xi)).
\tag{16.6}
$$

It belongs to $\mathcal H_1$. Indeed, multiplying a native smooth-core
approximation by $\chi$ gives compact chart support, and the same
pullback maps it into $C_c^\infty(\mathbb R^3)$ with convergence in the
whole-group form norm. Its squared norm is $\|\chi f\|_2^2$, and
exact scaling gives $T_\epsilon[\chi f]=\epsilon^{-2}
\mathcal T_1[u_\epsilon]$. Consequently (3.2) implies

$$
q_{\epsilon,g}[\chi f]
 \ge\epsilon^{-2}\mathcal Q_{g/m_0}[u_\epsilon]
                         -gB\|\chi f\|_2^2
 \ge\epsilon^{-2}e(g/m_0)\|\chi f\|_2^2-gB\|\chi f\|_2^2.
\tag{16.7}
$$

By (15.4) and kinetic nonnegativity,
$q_{\epsilon,g}[\psi f]\ge-gC_{\rm out}\|\psi f\|_2^2$.
Thus for every normalized member of the entire native domain,

$$
q_{\epsilon,g}[f]
 \ge\epsilon^{-2}e(g/m_0)\|\chi f\|_2^2-C_g
 \ge\epsilon^{-2}e(g/m_0)-C_g,
\tag{16.8}
$$

where one can take $C_g=g\max(B,C_{\rm out})+C_{\rm IMS}$.
The last inequality uses $e(g/m_0)\le0$ and $\|\chi f\|_2^2\le1$.
Taking the infimum proves (16.2). Multiplying by $\epsilon^2$ gives
the lower bound in (16.1), completing the proof. $\square$

**Definition 16.2 (unit Rayleigh threshold and the horizontal supplier).**
Set

$$
\Lambda_*=
 \inf_{0\ne u\in\mathcal H_1}
       \frac{\mathcal T_1[u]}{\int\mathcal G_1|u|^2\,d\xi},
\qquad g_*=m_0\Lambda_*.
\tag{16.9}
$$

Every denominator is finite by (15.8) and strictly positive because
$\mathcal G_1>0$ almost everywhere. Let $\lambda_0$ be precisely
V, Definition 10.1 and Theorem 10.2's full-angular horizontal Hardy
constant, with its natural, non-Dirichlet endpoint domain. In the
present identity-covariance coordinates its angular form is

$$
\begin{aligned}
J&=(-\pi/2,\pi/2),\quad c(a)=\cos a,\\
\mathcal H_c&=\{b\in L^2(J):b\in AC_{\rm loc}(J),\
                                   \sqrt c\,b'\in L^2(J)\},\\
S b&=-4(cb')'+cb,\qquad S\phi=\lambda_0\phi,\quad\phi(0)=1,
\end{aligned}
\tag{16.10}
$$

where $\phi$ is the positive smooth regular endpoint branch and
$c\phi'\to0$ at both endpoints. The supplied inequality and optimality
are

$$
\|Uu\|_2^2+\|Vu\|_2^2
 \ge\lambda_0\int R^{-2}|u|^2\,d\xi,
\qquad u\in C_c^\infty(\mathbb R^3\setminus\{0\}),
\quad\lambda_0>0.
\tag{16.11}
$$

They impose no angular symmetry on $u$. The corresponding horizontal
native coupling is $g_{\rm c}=2\pi m_0\lambda_0$, as in (5.1).

**Theorem 16.3 (sharp uniform semiboundedness, including equality).**
For the fixed source and every $g>0$,

$$
\begin{gathered}
0<\Lambda_*\le2\pi\lambda_0,\qquad 0<g_*\le g_{\rm c},\\
e(g/m_0)=0\quad\Longleftrightarrow\quad g\le g_*,\\
e(g/m_0)<0\quad\Longleftrightarrow\quad g>g_*.
\end{gathered}
\tag{16.12}
$$

For every fixed finite $\epsilon_0>0$,

$$
\inf_{0<\epsilon\le\epsilon_0}E_\epsilon(g)>-\infty
            \quad\Longleftrightarrow\quad g\le g_*.
\tag{16.13}
$$

In particular $g=g_*$ has a uniform lower bound. No equality
$\Lambda_*=2\pi\lambda_0$, numerical value of $\Lambda_*$, attainment
of its quotient, or identification of a zero-noise critical completed
domain with $\mathcal F_\epsilon$ is asserted.

**Proof.** Integrating (2.4) at unit noise gives the whole-group bound
$\mathcal G_1\le C/[d_1(1+d_1)]$, as in (3.5). The gauge comparison
in §2 gives $d_1\ge cR^2$ when $R\le1$, and $d_1\ge cR$ when
$R\ge1$. For the first assertion use
$d_1\asymp\sqrt{x^2+y^2+\theta^2}$ in this bounded region and
$R^2\asymp x^2+y^2+|\theta|$; the latter is at most a constant times
the former there. The second assertion follows directly from the
regularized gauge when $|\theta|\ge1$, and by compactness and the
horizontal displacement bound in the remaining region $R\ge1$,
$|\theta|\le1$. It follows that

$$
\mathcal G_1\le C'R^{-2},\qquad
\int\mathcal G_1|u|^2\,d\xi
 \le\frac{C'}{\lambda_0}(\|Uu\|_2^2+\|Vu\|_2^2)
 \le\frac{C'}{\lambda_0}\mathcal T_1[u].
\tag{16.14}
$$

Here (16.11) extends to $\mathcal H_1$ by form approximation and
Fatou. To pass first from punctured tests to all smooth tests, cut out
a Euclidean ball of radius $b$ about zero. On a fixed compact set the
three fields have bounded coefficients, so the extra squared-gradient
integral is $O(b)$ for a cutoff with derivative $O(b^{-1})$ in a
ball of volume $O(b^3)$. This tends to zero, and Fatou gives the
weighted inequality. Then use the defining whole-group core for every
$u\in\mathcal H_1$. Thus (16.14) proves $\Lambda_*>0$.

For the opposite bound, use the actual annular witnesses of V,
(10.12)–(10.13), rather than a purely radial test class. In V's polar
coordinates

$$
x=R\sqrt{\cos a}\cos\omega,\quad
y=R\sqrt{\cos a}\sin\omega,\quad
4\theta=R^2\sin a,
\tag{16.15}
$$

choose nonzero real $\zeta\in C_c^\infty(\mathbb R)$ and set
$v_L=R^{-1}\phi(a)\zeta(\log R/L)$, $L>0$.
For each finite $L$ this is an actual smooth compact annular function
on the full punctured group, including the central axis, by the
regular endpoint branch of $\phi$. The supplied calculation is

$$
\frac{\|Uv_L\|_2^2+\|Vv_L\|_2^2}
     {\int R^{-2}|v_L|^2\,d\xi}
=\lambda_0+
 \frac{\int_Jc\phi^2\,da}{\int_J\phi^2\,da}
 \frac{\int_{\mathbb R}|\zeta'|^2\,dt}
      {L^2\int_{\mathbb R}|\zeta|^2\,dt}.
\tag{16.16}
$$

For any one of these fixed functions $v=v_L$, exact dilation gives

$$
\frac{\mathcal T_1[D_sv]}{\int\mathcal G_1|D_sv|^2\,d\xi}
=\frac{\|Uv\|_2^2+\|Vv\|_2^2+s^{-2}\|Z_Hv\|_2^2}
       {\int\mathcal G_{1/s}|v|^2\,d\xi}
\longrightarrow
2\pi\frac{\|Uv\|_2^2+\|Vv\|_2^2}{\int R^{-2}|v|^2\,d\xi}.
\tag{16.17}
$$

The convergence uses (2.5) uniformly on that fixed compact annulus.
First let $s\to\infty$ for fixed $L$, then $L\to\infty$ in (16.16).
The definition of $\Lambda_*$ proves $\Lambda_*\le2\pi\lambda_0$.

By (16.9), $\mathcal Q_\gamma[u]\ge0$ for every $u$ when
$0<\gamma\le\Lambda_*$, including $\gamma=\Lambda_*$. Together
with the spreading argument (15.9) this gives $e(\gamma)=0$.
If $\gamma>\Lambda_*$, some quotient in (16.9) is strictly below
$\gamma$, so its normalized $\mathcal Q_\gamma$ value is negative
and $e(\gamma)<0$. Semiboundedness in Proposition 15.2 rules out
$e(\gamma)=-\infty$. This proves (16.12), without assuming a
minimizer at the threshold.

For $g\le g_*$, (16.2) now reads $E_\epsilon(g)\ge-C_g$,
including at equality. For $g>g_*$, (16.1) gives
$\epsilon^2E_\epsilon(g)\to e(g/m_0)<0$, hence
$E_\epsilon(g)\to-\infty$. This proves (16.13).
Theorem 4.1 also bounds the remaining range $\epsilon\ge\epsilon_0$
uniformly for each fixed positive $\epsilon_0$, if the family is taken
over all positive noises. $\square$

**Corollary 16.4 (source concentration of near minimizers).** Suppose
$g>g_*$ and, for each positive $\epsilon$ tending to zero,
$f_\epsilon\in\mathcal F_\epsilon$, $\|f_\epsilon\|_2=1$, satisfy

$$
q_{\epsilon,g}[f_\epsilon]
             =E_\epsilon(g)+o(\epsilon^{-2}).
\tag{16.18}
$$

Then for every fixed neighbourhood $N$ of the pole,

$$
\int_{\Omega\setminus N}|f_\epsilon|^2\,d\mu\longrightarrow0.
\tag{16.19}
$$

The normalized ground states of Theorem 4.1 satisfy this conclusion.
It asserts neither a unique rescaled profile nor strong convergence
of rescaled profiles.

**Proof.** Choose the cutoffs in (16.5) with
$\operatorname{supp}\chi\Subset N\cap U_o$. Put
$e=e(g/m_0)<0$ and $m_\epsilon=\|\chi f_\epsilon\|_2^2$.
The first inequality in (16.8) gives

$$
\epsilon^2q_{\epsilon,g}[f_\epsilon]
 \ge e m_\epsilon-C_g\epsilon^2
 =e+|e|(1-m_\epsilon)-C_g\epsilon^2.
\tag{16.20}
$$

By (16.1) and (16.18) its left side tends to $e$. Since
$0\le m_\epsilon\le1$, we obtain $m_\epsilon\to1$.
The mass outside $N$ is at most $1-m_\epsilon$, proving (16.19).
The constants may depend on $N$; no shrinking-neighbourhood or profile
compactness assertion follows from this estimate alone. $\square$

## 17. Full self-field occupation and its fixed-source coefficient

**Theorem 17.1 (complete occupation with the uniform square-difference
estimate).** For the same source, clock and pole define

$$
J_\epsilon=\mathbb E_o\int_0^\tau
                       \Gamma_{\epsilon,o}(q_t^\epsilon)\,dt
           =\int_\Omega\Gamma_{\epsilon,o}^2\,d\mu,
\qquad\epsilon>0.
\tag{17.1}
$$

Each $J_\epsilon$ is finite. As $\epsilon\downarrow0$,

$$
\frac{J_\epsilon}{\log(1/\epsilon)}\longrightarrow\frac1{8m_0},
\qquad
J_\epsilon=\frac1{8m_0}\log(1/\epsilon)
                         +o(\log(1/\epsilon)).
\tag{17.2}
$$

The final remainder in (17.2) is not asserted to be $O(1)$.

**Proof.** Proposition 7.1 gives finiteness at each positive noise.
Its full-time identity follows also from Theorem 1.3 by monotone
approximation of the nonnegative test $\Gamma_{\epsilon,o}$; it uses
the full killed semigroup, not a time-truncated occupation. Fix finite
$\epsilon_0>0$ and a gauge radius $b>0$ such that the closure of
$B_b=\{\xi:R(\xi)<b\}$ lies in the injective source chart.
Write $A_b=\Phi_o(B_b)$ and

$$
M=\frac{(k_o-l)(u-k_o)}2
 =\int_\Omega\Gamma_{\epsilon,o}\,d\mu,
\qquad w_\epsilon(\Phi_o(\xi))=m_0^{-1}\mathcal G_\epsilon(\xi).
\tag{17.3}
$$

Here $|B_b|$ denotes Lebesgue chart volume and
$\mu(A_b)=m_0|B_b|$ denotes native raw volume.
Theorem 3.1 gives $|\Gamma_{\epsilon,o}-w_\epsilon|\le B$ on
$A_b\setminus\{o\}$, with $B$ independent of
$0<\epsilon\le\epsilon_0$. Positivity and (17.3) give the explicit
uniform $L^1$ estimate

$$
\begin{aligned}
\int_{B_b}\mathcal G_\epsilon\,d\xi
 &=\int_{A_b}w_\epsilon\,d\mu\\
 &\le\int_{A_b}\Gamma_{\epsilon,o}\,d\mu+B\mu(A_b)\\
 &\le M+B m_0|B_b|.
\end{aligned}
\tag{17.4}
$$

In particular there is no extra factor $m_0$ in the first equality:
the kernel factor $m_0^{-1}$ and measure factor $m_0$ cancel.
It follows, without assuming a uniform square integral, that

$$
\begin{aligned}
\int_{A_b}|\Gamma_{\epsilon,o}^2-w_\epsilon^2|\,d\mu
 &\le B\int_{A_b}(\Gamma_{\epsilon,o}+w_\epsilon)\,d\mu\\
 &\le2BM+B^2m_0|B_b|.
\end{aligned}
\tag{17.5}
$$

Let $C_b$ be the off-source bound (15.4) for
$\Omega\setminus A_b$. Then
$\int_{\Omega\setminus A_b}\Gamma_{\epsilon,o}^2d\mu\le C_bM$.
Consequently the precise bounded-error reduction is

$$
\left|J_\epsilon-m_0^{-1}\int_{B_b}\mathcal G_\epsilon^2\,d\xi\right|
 \le (2B+C_b)M+B^2m_0|B_b|,
\qquad0<\epsilon\le\epsilon_0.
\tag{17.6}
$$

All constants here belong to the same full native field and its fixed
raw volume; (17.4) is the uniform $L^1$ calculation needed for
the square-difference step. It is an $L^1$ bound on the deterministic
spatial kernels, not a uniform-integrability theorem for random native
command occupations.

Now $\mathcal G_\epsilon(\delta_\epsilon\xi)
=\epsilon^{-2}\mathcal G_1(\xi)$ and the dilation Jacobian is
$\epsilon^4$. Thus the powers cancel in the square integral and
(17.6) becomes

$$
J_\epsilon=m_0^{-1}\int_{R<b/\epsilon}\mathcal G_1^2\,d\xi+O(1).
\tag{17.7}
$$

On the compact unit gauge sphere $R(\zeta)=1$, (2.5) gives
$\mathcal G_\kappa(\zeta)\to(2\pi)^{-1}$ uniformly as
$\kappa\downarrow0$. For $\xi=\delta_s\zeta$, $s=R(\xi)$,
exact scaling yields

$$
\mathcal G_1(\xi)=s^{-2}\mathcal G_{1/s}(\zeta)
                  =\frac{1+o(1)}{2\pi R(\xi)^2},
\qquad R(\xi)\to\infty,
\tag{17.8}
$$

uniformly over all directions, including the central axis.
The unit gauge-ball volume in Lebesgue coordinates is

$$
\begin{aligned}
|B_1|
 &=2\pi\int_0^1\rho\,\frac12\sqrt{1-\rho^4}\,d\rho\\
 &=\frac\pi2\int_0^1\sqrt{1-t^2}\,dt
 =\frac{\pi^2}{8},\qquad |B_s|=s^4|B_1|.
\end{aligned}
\tag{17.9}
$$

Here $\rho=\sqrt{x^2+y^2}$ and $t=\rho^2$; the vertical interval has
length $\frac12\sqrt{1-\rho^4}$. Integration against the radial volume
function therefore gives, for $0<A<L$,

$$
\int_{A<R<L}R^{-4}\,d\xi
 =4|B_1|\log(L/A)=\frac{\pi^2}{2}\log(L/A).
\tag{17.10}
$$

This is the same shell normalization used by [Singular occupation and
command-cap limits, Theorem 2.1, (2.3)–(2.4)](FIB_NATIVE_SINGULAR_OCCUPATION_AND_COMMAND_CAP_LIMITS.md).
There it concerns a spatially truncated horizontal field. Here the
consumer is the complete positive-noise field in (17.7).

For completeness, $\mathcal G_1^2$ is integrable on each fixed ball:
near zero (2.4) is the three-dimensional unit elliptic estimate
$\mathcal G_1\le C/d_1$, with local volume comparable to $s^3$;
its radial square majorant is $C\int_0^{s_0}ds<\infty$.
Off zero it is smooth. Given $a\in(0,1)$, choose a fixed $A\ge1$
so that, for every $R\ge A$, (17.8) bounds $\mathcal G_1$ between
$(1-a)/(2\pi R^2)$ and $(1+a)/(2\pi R^2)$.
For $L>A$, (17.10) sandwiches the outer integral between

$$
\frac{(1-a)^2}{8}\log(L/A)
 \quad\hbox{and}\quad
\frac{(1+a)^2}{8}\log(L/A).
\tag{17.11}
$$

The fixed inner-ball integral divided by $\log L$ tends to zero.
First let $L\to\infty$ and then $a\downarrow0$ to obtain
$\int_{R<L}\mathcal G_1^2d\xi/\log L\to1/8$.
Substitute $L=b/\epsilon$ into (17.7), and use
$\log(b/\epsilon)/\log(1/\epsilon)\to1$. This proves (17.2).
The bounded localization error in (17.7) does not give a bounded final
error: (17.8) supplies uniform convergence without a rate, and its
integrated error is only $o(\log L)$ by this argument. $\square$

**Corollary 17.2 (source parameters and the native consumer boundary).**
For every fixed datum of Definition 15.1,

$$
\lim_{\epsilon\downarrow0}\epsilon^2E_\epsilon(g)=e(2rg),
\qquad g_*=\frac{\Lambda_*}{2r},\qquad
\lim_{\epsilon\downarrow0}\frac{J_\epsilon}{\log(1/\epsilon)}=
\frac r4.
\tag{17.12}
$$

At fixed $r$, these leading quantities are independent of the pole,
fixed preparation phases and wall positions. The bounded localization
constants are allowed to depend on those fixed data, as are finite-noise
quantities. This assertion is for fixed interior poles and fixed
separated walls. It asserts no uniform bound when a pole approaches a
wall, the interval degenerates or $r$ tends to zero.

For a native finite-command consumer, retain Definition 6.1's actual
two-control chronology, extrema guards, own death and original-time
charges. For fixed $\epsilon>0$, Theorem 6.2 supplies occupation
convergence for the fixed continuous spatial cap
$\Gamma_{\epsilon,o}\wedge K$ under its stated ideal-history or
decreasing-positive-risk paid-point hypotheses. Removing that cap
requires a separate tail estimate, for example, for nonnegative total
occupations $X_n=\int_0^{S_n}\Gamma_{\epsilon,o}(q_n(t))dt$, the
uniform-integrability condition

$$
\lim_{K\to\infty}\sup_n
       \mathbb E[X_n\mathbf1_{\{X_n>K\}}]=0,
\tag{17.13}
$$

together with convergence in probability of the uncapped $X_n$ to the
corresponding target occupation. Neither hypothesis is supplied merely
by (17.12) or bounded-continuous path tracking. Alternatively a direct
uniform tail estimate for the spatially capped integrals suffices to
pass from their convergent expectations to the uncapped expectation.
Infinite-time or joint noise/cap limits retain the corresponding
uniform tail requirements as well.

**Proof.** Substitute $m_0=(2r)^{-1}$ in (16.1), (16.9) and (17.2).
The unit model and its $e,\Lambda_*$ are independent of the fixed
native pole and walls; the exact chart and raw Jacobian (15.1) account
for all leading source parameters. The proofs locate the remaining
source dependence precisely in the fixed chart, the bound $B$,
$C_{\rm out}$, $C_{\rm IMS}$, $C_b$ and the Green mass $M$.

The fixed-cap conclusion is Theorem 6.2 and Proposition 7.1.
Convergence in probability plus (17.13) implies convergence of
expectations by truncating total occupations at a fixed level and then
letting that level increase. For the alternative spatial-tail route,
write $X_{n,K}=\int_0^{S_n}(\Gamma_{\epsilon,o}\wedge K)(q_n(t))dt$.
The conditions
$\lim_{K\to\infty}\sup_n\mathbb E(X_n-X_{n,K})=0$ and the analogous
target tail, combined with convergence of $\mathbb EX_{n,K}$ at each
fixed $K$, give the uncapped result by the triangle inequality.
For the actual paid family of Definition 12.1, Theorem 12.2 and
Corollary 13.1 already provide the fixed-positive-noise, finite-horizon
capped weighted response, including its simultaneous cap schedule and
unconditional charged execution. Those results concern the spatially
capped field at every finite stage and allow constants to depend on
$\epsilon,T$; they establish neither (17.13) nor an uncapped-exposure
limit or a uniform joint noise/cap limit. In particular, Definition
14.1's positive initial hold at the pole makes the literal uncapped
occupation of that paid family infinite. More generally, Proposition
7.1's lawful positive hold at the pole makes $X_n$ infinite despite
path and lifetime convergence, so that convergence alone cannot remove
the obligation. The horizontal finite-sign
producer and its capped laws in [Singular occupation and command-cap
limits, §9](FIB_NATIVE_SINGULAR_OCCUPATION_AND_COMMAND_CAP_LIMITS.md)
have different source and execution hypotheses and do not supply
(17.13) for this independent-central-noise target.

For the following crossover citation only, the repository revision is
`08b8b995f0fd5b1e08c03e5f153282687ba8e15d`, qualifying
Definition 1.1's reference convention for this supplier.

The resource correspondence is the existing one of [Uniform joint
noise and tolerance native resource crossover, Definitions 1.2–1.4 and
Theorems 5.1, 6.1](FIB_NATIVE_UNIFORM_JOINT_NOISE_TOLERANCE_RESOURCE_CROSSOVER.md).
Precisely, it fixes a finite horizon $T>0$ and a bounded noise range
$|\nu|\le\bar\nu$, one persistent covariance-$2$ Wiener triple,
zero area drift and the same stopped target. Its ideal stopped-history
filtration may have an initially independent seed. An issuer chooses
entire numerical absolutely continuous two-control profiles at stopping
times; interruptions replace only unexecuted suffixes, joins are
continuous, and issuance counts through own death or $T$ are almost
surely finite, without a fixed dwell, speed or count cap. The native
chronology is $j=\int a\,db$, and all prefixes retain the original
height guard and their acquired numerical command domains. Own death
is actual height exit, not target death or interruption. The class
requires the complete held-path tube $D_{\max}\le\eta$ almost surely
and $0\le S^{\rm N}-S\le\eta$, for each deterministic parameter pair.

With $\epsilon=|\nu|$, let $\mathsf C_x$ be the respective infima of
expected unhalved costs in that precise class. Their supplied orders,
uniform for sufficiently small $\eta>0$ and bounded $\epsilon$, are

$$
\begin{aligned}
\mathsf C_x(\eta,\epsilon)
 &\asymp\eta^{-1}+\epsilon^2\eta^{-2},\qquad x=a,b,L,\\
\mathsf C_E(\eta,\epsilon)
 &\asymp\eta^{-2}+\epsilon^4\eta^{-4}.
\end{aligned}
\tag{17.14}
$$

The actual charges are
$V^a=\int|\dot a|dt$, $V^b=\int|\dot b|dt$,
$L=\int\sqrt{\dot a^2+\dot b^2}dt$ and
$E=\int(\dot a^2+\dot b^2)dt$, including interrupted or aborted
movement and movement after target death until own death or the
horizon. Holds after own death cost zero. The supplier realizes all
four upper orders with one simultaneous family; these are infimum
orders, not sharp constants or exact attainment of the infima.
Its bounded/capped occupation limit takes the approximation limit
first and then $T\to\infty$, with any total cap removed afterwards.
It does not transfer an uncapped singular source field.

Under Definition 1.1's supplier revision, the paid-point interface is
Definition 6.1 and O, Theorems 48.1–48.2: future paid Read times are chosen from past
paid records and the clock, with no ideal-history observation. At fixed
nonzero noise and positive risk $\delta$, it has
$\mathbb EM=O(\eta^{-2}\log(e/(\eta\delta)))$,
$\mathbb EV^a,\mathbb EV^b,\mathbb EL=O(\eta^{-2})$ and
$\mathbb EE=O(\eta^{-4})$. These are not uniform small-noise prices;
zero-risk finite paid tracking is excluded by K, Theorem 41.2.
Neither observation interface is acquired by the analytic spectral
calculation. The executed resource $E$, the form infimum
$E_\epsilon(g)$ and the diffusion occupation $J_\epsilon$ are distinct
objects. The exact symbol, distance and full-response boundaries
cited in Definition 15.1 continue to apply to the native source;
none of these scalar asymptotics supplies an excluded realization.
$\square$

## 追加锚（本行以下为增补区）

## 18. The simple unit-cell ground state in the fixed supercritical regime

**Definition 18.1 (fixed data, free norm and adapted cutoff comparison).**
In §§18–20 retain Definition 15.1 and its supplier conventions.
Fix $0<Z<1$, $r=1-Z$, $H=r/2$, $0<l<k_o<u<H$, the pole
$o=(k_o,\alpha_o,\beta_o)$ and arbitrary preparation phases.
The probabilities and signed amplitudes remain those of Definitions
1.1 and 9.1, both phase periods are $2\pi$, and
$d\mu=dk\,d\alpha\,d\beta$ on
$\Omega=(l,u)\times\mathbb T^2$ is unnormalized. Fix
$g>g_{\rm c}=2\pi m_0\lambda_0$, where $m_0=(2r)^{-1}$ and
$\lambda_0$ is exactly Definition 16.2's horizontal constant.
Only $\epsilon=|\nu|\downarrow0$ varies, with either sign of $\nu$.
The law is (1.2), with its persistent independent covariance-$2$
triple, zero area drift, both first-exit absorbing faces and original
clock. The field is the full unit-source $\Gamma_{\epsilon,o}$,
and the native domain is the entire complex $\mathcal F_\epsilon$.

Use, without changing its domain, the unit problem of (15.2), and write

$$
\gamma=g/m_0,\qquad W=\mathcal G_1,\qquad
e_g=e(\gamma),\qquad
\|v\|_{\mathcal H_1}^2=\|v\|_2^2+\mathcal T_1[v],
\qquad \langle v,w\rangle=\int\overline v w\,d\xi .
\tag{18.1}
$$

Thus all cell integrals use $d\xi=dx\,dy\,d\theta$ and
$\mathcal Q_\gamma=\mathcal T_1-\gamma\int W|\cdot|^2$.
Choose once a nonnegative smooth partition $\chi,\psi$ as in
(16.5): $\chi^2+\psi^2=1$, $\chi=1$ near $o$,
$\operatorname{supp}\chi\Subset U_o$, and $\psi=0$ near $o$.
It is independent of the state and $\epsilon$. Define

$$
\begin{aligned}
(\mathcal B_\epsilon f)(\xi)
 &=m_0^{1/2}\epsilon^2
                 (\chi f)(\Phi_o(\delta_\epsilon\xi)),\\
\delta_\epsilon(x,y,\theta)&=(\epsilon x,\epsilon y,\epsilon^2\theta),
\qquad
d\mu(\Phi_o(\delta_\epsilon\xi))=m_0\epsilon^4\,d\xi .
\end{aligned}
\tag{18.2}
$$

Extend the pullback by zero outside the rescaled chart. It is exactly
(16.6), with a name for this fixed choice of cutoff. The chart is
(15.1), including $\theta=z-xy/2$ and
$z=-r\{\beta-\beta_o-c(k_o)y\}$. An uncut periodic lift and an
isotropic three-coordinate dilation are different maps.

**Theorem 18.2 (attainment, complex simplicity and free-form coercivity
for the matched cell).** Under Definition 18.1, $-\infty<e_g<0$.
Its infimum is attained by a unique normalized positive real function
$h_g\in\mathcal H_1$, where positive means strictly positive almost
everywhere. Every normalized complex minimizer is $\zeta h_g$ with
one spatially constant $|\zeta|=1$. The bottom eigenvalue is isolated,
and there is $c_g>0$ such that, for every complex $v\in\mathcal H_1$,

$$
\mathcal Q_\gamma[v]-e_g\|v\|_2^2
 \ge c_g\|v-\langle h_g,v\rangle h_g\|_{\mathcal H_1}^2.
\tag{18.3}
$$

Proof. Closedness, semiboundedness and the free-domain equivalence are
Proposition 15.2. Theorem 16.3 gives $e_g<0$, since
$g>g_{\rm c}\ge g_*$. These existing results supply the variational
problem and the strict sign; what is needed here is compactness and
its spectral consequences.

Integration of (2.4), as in (3.5), at unit noise gives

$$
0<W(\xi)\le
 \frac{C}{d_1(0,\xi)(1+d_1(0,\xi))}.
\tag{18.4}
$$

Locally at zero $d_1(0,\xi)\asymp|\xi|$. Its bounded closed balls are
compact by the regularized gauge in (2.4), so $W$ tends uniformly to
zero at infinity and is bounded outside every pole neighbourhood.
The whole-group heat input here is the classical
Capogna–Citti–Manfredini,
[arXiv:1212.6665v2, Propositions 2.1–2.2,
(2.8)](https://arxiv.org/html/1212.6665v2).
The group is precisely Definition 2.1's step-two group, the scaled
frame is $(U,V,\kappa Z_H)$ and the coefficient matrix is $I_3$;
here $\kappa=1$. Their (2.11), used for the existing zero-noise
suppliers, is positive-time kernel convergence, not a ground-state
or native killed-tail theorem. The native tail remains Theorem 1.3.

The free domain also equals the space of $L^2$ functions whose three
weak derivatives $Uv,Vv,Z_Hv$ are in $L^2$. To check the direction
needed for Sobolev operations, such derivatives imply local Euclidean
$H^1$, because
$\partial_x=U+(y/2)Z_H$,
$\partial_y=V-(x/2)Z_H$ and $\partial_\theta=Z_H$.
For a fixed compact smooth cutoff $\kappa$ equal to one near zero,
put $\kappa_R=\kappa\circ\delta_{1/R}$. Its horizontal derivatives
are bounded by $C/R$ and its central derivative by $C/R^2$.
The product rule and dominated convergence give
$\kappa_Rv\to v$ in the free norm. Each compactly supported
$\kappa_Rv$ can then be smoothed in a fixed larger compact set in
ordinary $H^1$, hence in the frame norm. This puts $v$ in the closure
(15.2). The reverse direction follows by weak derivative closure.
Consequently the local Sobolev chain rule, compact local Rellich
embedding and multiplication by the cutoffs used below apply on
exactly $\mathcal H_1$, without a global Euclidean $H^1$ assumption.

Here is control of the pole in the compactness argument. Take a fixed
smooth coordinate cutoff $\zeta$ equal to one on a small ball about
zero. The classical three-dimensional Hardy inequality gives

$$
\int |\xi|^{-2}|\zeta v|^2\,d\xi
 \le4\int|\nabla(\zeta v)|^2\,d\xi
 \le C\|v\|_{\mathcal H_1}^2.
\tag{18.5}
$$

For compact smooth functions its first inequality follows by
integrating
$\operatorname{div}(\xi/|\xi|^2)=|\xi|^{-2}$
against $|\zeta v|^2$ and applying Cauchy–Schwarz; the boundary
term on a removed radius-$s$ sphere tends to zero as $s\downarrow0$.
Density extends it to the local $H^1$ functions just obtained.
The second inequality uses the bounded frame coefficients on the
cutoff support. Thus (18.4) implies

$$
\int_{|\xi|<s}W|v|^2\,d\xi
                  \le Cs\|v\|_{\mathcal H_1}^2
                  \qquad(0<s<s_0).
\tag{18.6}
$$

Multiplication $J:v\mapsto W^{1/2}v$ is therefore compact from
$\mathcal H_1$ to $L^2$. Indeed, restricting it to a bounded region
separated from zero gives a bounded multiplier after compact local
Rellich restriction. The squared operator norm of the omitted pole
part is $O(s)$ by (18.6). Outside a sufficiently large $d_1$ ball
it is at most the supremum of $W$ there, which tends to zero by
(18.4). The full $J$ is an operator-norm limit of these compact
restrictions.

This uses the classical form-domain compactness criterion of
Lenz–Stollmann–Wingert,
[arXiv:0903.0280v2, Theorem 1.3(v),
(vii)](https://arxiv.org/html/0903.0280v2) in its precise bounded
multiplier scope: their semibounded self-adjoint $H$ is
$\mathcal L_1$, and each truncated multiplier
$B=\mathbf1_K W^{1/2}$, with $K$ bounded and separated from zero,
is bounded on $L^2$. Their (v) is compactness on the form domain,
and (vii) gives norm convergence on form-bounded weakly zero
sequences. The full singular $W^{1/2}$ is not a bounded $L^2$
multiplier; (18.6) and the decaying exterior supply the required
norm-limit step. No compactness of the free global form embedding
is asserted.

Let $v_n$ be any normalized cell minimizing sequence.
Equation (15.8), with its parameter large enough to make the relative
bound at most $1/2$, bounds $v_n$ in $\mathcal H_1$.
Pass to a weakly convergent subsequence there, with limit $v$.
Compactness of $J$ gives $Jv_n\to Jv$. Lower semicontinuity, the
definition of the bottom also for nonunit vectors, and $e_g<0$ give

$$
e_g\ge\mathcal Q_\gamma[v]
       \ge e_g\|v\|_2^2\ge e_g.
\tag{18.7}
$$

The last inequality uses $\|v\|_2\le1$.
Equality forces $\|v\|_2=1$, so $v_n\to v$ in $L^2$.
Furthermore
$\mathcal T_1[v_n]=\mathcal Q_\gamma[v_n]+\gamma\|Jv_n\|_2^2
 \to\mathcal Q_\gamma[v]+\gamma\|Jv\|_2^2=\mathcal T_1[v]$.
Weak convergence of the derivative vector and equality of its norm
give convergence in the full free norm. This proves attainment and
subsequential free-norm compactness of every normalized minimizing
sequence, including complex ones. Variation gives the weak eigenvalue
equation on all of $\mathcal H_1$.

The Sobolev chain rule gives $|v|\in\mathcal H_1$ and
$\mathcal T_1[|v|]\le\mathcal T_1[v]$, so a normalized nonnegative
minimizer exists. To prove strict positivity without an assumed
pointwise eigenfunction regularity, let $\mathsf A_g$ be the operator
of $\mathcal Q_\gamma$, and set $W_N=W\wedge N$.
The free heat kernel is strictly positive by (2.4).
The bounded-potential Duhamel series, whose terms preserve
nonnegativity, gives on the positive cone

$$
e^{-t(\mathcal L_1-\gamma W_N)}
                   \ge e^{-t\mathcal L_1},\qquad t>0.
\tag{18.8}
$$

This domination passes to $\mathsf A_g$. In detail, (18.4) puts
$\{W>N\}$ inside $|\xi|<C/N$ for large $N$, and (18.6) yields

$$
0\le\int(W-W_N)|v|^2\,d\xi
                    \le C N^{-1}\|v\|_{\mathcal H_1}^2.
\tag{18.9}
$$

Polarization by weighted Cauchy–Schwarz bounds the corresponding
sesquilinear tail by $C/N$ times the two free norms.
Proposition 15.2 provides one common shift making every capped form
and the full form coercive in that norm. Their variational resolvent
solutions for a right side $F\in L^2$ have free norm at most
$C\|F\|_2$. Subtract their equations and test on the difference;
(18.9) bounds that difference in free norm by $CN^{-1}\|F\|_2$.
Thus the shifted resolvents converge in operator norm on $L^2$.
Their spectra have a common lower bound. On that half-line
$e^{-t\lambda}$ is a continuous function of the shifted inverse,
with value zero at inverse value zero. Polynomial approximation in
this bounded inverse interval gives operator-norm convergence of
the semigroups at every $t>0$. Since the positive cone is closed,
(18.8) holds with the full operator on the left. A nonzero
nonnegative minimizer $h$ therefore satisfies

$$
h=e^{te_g}e^{-t\mathsf A_g}h
       \ge e^{te_g}e^{-t\mathcal L_1}h>0
                         \quad\hbox{almost everywhere}.
\tag{18.10}
$$

For a real ground eigenfunction, locality of the weak derivatives
splits its form and squared norm into those of its positive and
negative parts. Each part has energy at least $e_g$ times its squared
norm. If both were nonzero, equality of the sum would make both
normalized parts nonnegative minimizers. Both would then be strictly
positive almost everywhere by (18.10), contradicting their disjoint
supports. Thus every nonzero real ground eigenfunction has one sign.
Two independent real ground eigenfunctions would give a nonzero real
one orthogonal to a positive one, which is impossible. The real
eigenspace is one dimensional. The form is real, so the real and
imaginary parts of any complex ground eigenfunction belong to that
real eigenspace. This proves complex simplicity, uniqueness of the
normalized positive $h_g$ and the constant-phase description.

If the infimum of $\mathcal Q_\gamma[p]$ over normalized
$p\perp h_g$ were $e_g$, its minimizing sequence would, by (18.7),
have a strongly convergent subsequence with unit ground-state limit
still orthogonal to $h_g$. Simplicity excludes this. Hence there
is $\delta_g>0$ with

$$
\mathcal Q_\gamma[p]-e_g\|p\|_2^2
                       \ge\delta_g\|p\|_2^2
                    \qquad(p\perp h_g).
\tag{18.11}
$$

The spectral theorem makes the bottom isolated. Also (15.8) gives
$\mathcal Q_\gamma[p]\ge\frac12\mathcal T_1[p]-C\|p\|_2^2$.
Combining this with (18.11) bounds $\|p\|_{\mathcal H_1}^2$ by a
constant times its energy deficit. For
$v=\langle h_g,v\rangle h_g+p$, the weak eigenvalue equation
cancels the cross terms in that deficit. This proves (18.3).
All compactness, positivity and spectral arguments above are
classical intermediates applied to this matched unit cell. $\square$

## 19. Bounded native energy remainder and a coercive exterior estimate

**Theorem 19.1 (bounded comparison with the complete native field).**
Under Definition 18.1 there are $C<\infty$ and $\epsilon_g>0$,
depending only on the fixed source data, partition and $g$, such that

$$
\left|E_\epsilon(g)-\epsilon^{-2}e_g\right|\le C,
                       \qquad 0<\epsilon<\epsilon_g.
\tag{19.1}
$$

For every complex $f\in\mathcal F_\epsilon$ in that range, putting
$w=\mathcal B_\epsilon f$, one also has

$$
\begin{aligned}
\epsilon^2q_{\epsilon,g}[f]-e_g\|f\|_2^2
 \ge{}&\mathcal Q_\gamma[w]-e_g\|w\|_2^2
                    +\epsilon^2T_\epsilon[\psi f]\\
 &+\tfrac12|e_g|\|\psi f\|_2^2
                    -C\epsilon^2\|f\|_2^2 .
\end{aligned}
\tag{19.2}
$$

Proof. The lower half of (19.1) is already (16.2).
Use the full-domain cutoff and IMS facts in (16.5)–(16.7).
In the notation (18.2), their exact norm and kinetic identities and
the two-sided version of the local remainder are

$$
\begin{aligned}
\|w\|_2^2&=\|\chi f\|_2^2,&
\mathcal T_1[w]&=\epsilon^2T_\epsilon[\chi f],\\
\left|\epsilon^2q_{\epsilon,g}[\chi f]
                  -\mathcal Q_\gamma[w]\right|
 &\le gB\epsilon^2\|\chi f\|_2^2 .
\end{aligned}
\tag{19.3}
$$

These are statements on the whole original domain, not additional
localization hypotheses on $f$. For the last line, (3.2) bounds
the error pointwise by $B$, while (2.5) and the raw Jacobian
$m_0\epsilon^4$ turn the comparison potential into
$\gamma\int W|w|^2$. This gives the absolute bound, rather than only
the lower inequality used in (16.7).
For domain passage, multiply a native smooth-core approximation
by the fixed $\chi$, zero extend and rescale exactly as in (16.6).
It converges in the cell free norm by the kinetic identity.
Equation (15.8) makes its cell potential integrals converge, and
the bounded remainder makes the native potential integrals converge
as well. Thus (19.3) requires no pointwise regularity of $f$.
The same transfer identities hold for any native form function
supported compactly in this chart, with its direct pullback.

On $\operatorname{supp}\psi$ use exactly the existing bound (15.4),
say $\Gamma_{\epsilon,o}\le C_{\rm out}$ for $0<\epsilon\le1$.
It includes both boundary collars. The fixed IMS coefficient in
(16.5) has $0\le B_\epsilon\le C_{\rm IMS}$ there.
Retaining the exterior kinetic term, that identity and (19.3) give

$$
\begin{aligned}
\epsilon^2q_{\epsilon,g}[f]-e_g\|f\|_2^2
 \ge{}&\mathcal Q_\gamma[w]-e_g\|w\|_2^2
                   +\epsilon^2T_\epsilon[\psi f]\\
 &+(|e_g|-gC_{\rm out}\epsilon^2)\|\psi f\|_2^2
                   -(gB+C_{\rm IMS})\epsilon^2\|f\|_2^2 .
\end{aligned}
\tag{19.4}
$$

Here $\|f\|_2^2=\|w\|_2^2+\|\psi f\|_2^2$ exactly.
Choose $\epsilon_g$ small enough to retain half of $|e_g|$.
This proves (19.2), with all native wall and exterior contributions
present. Its cell deficit is nonnegative, and (18.3) controls it in
the fixed free norm.

To supply the upper half of (19.1), let
$\widehat\chi=\chi\circ\Phi_o$, zero extended to the group, and put
$\varphi_\epsilon=\widehat\chi\circ\delta_\epsilon$.
It is compactly supported, tends pointwise to one, and satisfies

$$
|U\varphi_\epsilon|+|V\varphi_\epsilon|\le C\epsilon,
\qquad |Z_H\varphi_\epsilon|\le C\epsilon^2.
\tag{19.5}
$$

The weak ground-state equation of Theorem 18.2 can be tested against
$\varphi_\epsilon^2h_g\in\mathcal H_1$.
For each of the three fields the product rule cancels the cross
term against that equation. Summing gives the exact identity

$$
\begin{aligned}
\mathcal Q_\gamma[\varphi_\epsilon h_g]
          -e_g\|\varphi_\epsilon h_g\|_2^2
 &=\int\bigl(|U\varphi_\epsilon|^2+|V\varphi_\epsilon|^2
                  +|Z_H\varphi_\epsilon|^2\bigr)h_g^2\,d\xi\\
 &\le C\epsilon^2.
\end{aligned}
\tag{19.6}
$$

All products belong to the established free domain, and all integrals
are finite by (15.8). Dominated convergence gives
$\|\varphi_\epsilon h_g\|_2\to1$.
For small $\epsilon$ define the normalized native trial

$$
F_\epsilon(\Phi_o(\delta_\epsilon\xi))
 =m_0^{-1/2}\epsilon^{-2}
      \frac{\varphi_\epsilon(\xi)h_g(\xi)}
           {\|\varphi_\epsilon h_g\|_2},
\tag{19.7}
$$

with zero extension. Its support is compact inside the injective
chart. Compactly supported cell free-domain approximation, or local
$H^1$ smoothing on that support followed by the inverse chart,
puts it in the full native $\mathcal F_\epsilon$ with both zero
wall traces and the prescribed periodicity. Applying the supported
version of (19.3) directly to $F_\epsilon$, followed by (19.6), gives
$q_{\epsilon,g}[F_\epsilon]\le\epsilon^{-2}e_g+C$.
The variational principle and (16.2) prove (19.1).
No rate for the tail of $h_g$ was assumed: its weak equation and
the derivative bound (19.5) provide the bounded remainder. $\square$

## 20. Universal complex profiles and the exact consumer boundary

**Theorem 20.1 (all near-minimizers, no lost mass and quantitative
free-form profile).** Under Definition 18.1 let
$f_\epsilon\in\mathcal F_\epsilon$ be any family of normalized
complex states, for all sufficiently small positive $\epsilon$, with

$$
D_\epsilon=\epsilon^2
       (q_{\epsilon,g}[f_\epsilon]-E_\epsilon(g))\longrightarrow0.
\tag{20.1}
$$

There are $C<\infty$, $d>0$ and $\epsilon_g>0$, depending only on
the fixed data and partition, such that whenever
$0<\epsilon<\epsilon_g$ and $D_\epsilon\le d$, one can choose a
single spatially constant phase $|\zeta_\epsilon|=1$ for that state
so that

$$
\|\zeta_\epsilon^{-1}\mathcal B_\epsilon f_\epsilon
                         -h_g\|_{\mathcal H_1}^2
 +\|\psi f_\epsilon\|_2^2
 +\epsilon^2T_\epsilon[\psi f_\epsilon]
                         \le C(D_\epsilon+\epsilon^2).
\tag{20.2}
$$

In particular the cutoff pullbacks converge strongly to $h_g$
modulo those phases along the entire family, and the exterior
scaled kinetic energy disappears. There is no extra eigenfunction,
regularity, tail or tightness assumption on $f_\epsilon$.
For $B_1(R)=\{\xi:d_1(0,\xi)<R\}$, every fixed $R>0$ satisfies

$$
\begin{aligned}
\lim_{\epsilon\downarrow0}
 \int_{\Phi_o(\delta_\epsilon B_1(R))}|f_\epsilon|^2\,d\mu
     &=\int_{B_1(R)}h_g^2\,d\xi,\\
\lim_{R\to\infty}\limsup_{\epsilon\downarrow0}
 \int_{\Omega\setminus\Phi_o(\delta_\epsilon B_1(R))}
                          |f_\epsilon|^2\,d\mu&=0 .
\end{aligned}
\tag{20.3}
$$

For fixed $R$ these chart images are used only for sufficiently small
$\epsilon$, when they lie where $\chi=1$.
The full native kinetic and matched-potential coefficients obey

$$
\epsilon^2T_\epsilon[f_\epsilon]\longrightarrow\mathcal T_1[h_g],
\qquad
\epsilon^2gV_\epsilon[f_\epsilon]
                  \longrightarrow\gamma\int W h_g^2\,d\xi .
\tag{20.4}
$$

Proof. Set $w_\epsilon=\mathcal B_\epsilon f_\epsilon$ and
$r_\epsilon=\mathcal Q_\gamma[w_\epsilon]
                         -e_g\|w_\epsilon\|_2^2\ge0$.
Equations (19.1)–(19.2) give

$$
r_\epsilon+\epsilon^2T_\epsilon[\psi f_\epsilon]
       +\tfrac12|e_g|\|\psi f_\epsilon\|_2^2
                           \le D_\epsilon+C\epsilon^2 .
\tag{20.5}
$$

Write $c_\epsilon=\langle h_g,w_\epsilon\rangle$ and
$p_\epsilon=w_\epsilon-c_\epsilon h_g$.
Coercivity (18.3) and the exact raw norm identity (19.3) imply

$$
\|p_\epsilon\|_{\mathcal H_1}^2\le C r_\epsilon,\qquad
|c_\epsilon|^2
   =1-\|\psi f_\epsilon\|_2^2-\|p_\epsilon\|_2^2 .
\tag{20.6}
$$

Fix $d$ and $\epsilon_g$ small enough that the right side is positive,
and choose $\zeta_\epsilon=c_\epsilon/|c_\epsilon|$.
This is one scalar, constant over space.
Since $|c_\epsilon|\le1$,

$$
\begin{aligned}
\zeta_\epsilon^{-1}w_\epsilon-h_g
 &=\zeta_\epsilon^{-1}p_\epsilon+(|c_\epsilon|-1)h_g,\\
(1-|c_\epsilon|)^2
 &\le1-|c_\epsilon|^2
   =\|\psi f_\epsilon\|_2^2+\|p_\epsilon\|_2^2 .
\end{aligned}
\tag{20.7}
$$

The triangle inequality squared in the free Hilbert norm,
(20.5) and (20.6) prove (20.2).
Thus (20.1) implies the stated strong convergence without extracting
a subsequence. An $\epsilon$-dependent constant phase is essential:
multiplying any normalized recovery family by $e^{i/\epsilon}$
leaves all its energies unchanged.

For each fixed $R$, properness of $d_1$ implies the bounded ball is
eventually mapped into $\chi=1$.
Its native raw mass is then exactly
$\int_{B_1(R)}|w_\epsilon|^2\,d\xi$.
Strong $L^2$ convergence modulo phase gives
$\||w_\epsilon|^2-h_g^2\|_1\to0$, proving the first line of (20.3).
The total native mass and $\int h_g^2$ are both one; letting
$R\to\infty$ proves the second line. This excludes mass loss
both outside the fixed source chart and at infinity in the expanding
cell coordinates.

The kinetic IMS identity from (16.5) and (19.3) give

$$
\epsilon^2T_\epsilon[f_\epsilon]
 =\mathcal T_1[w_\epsilon]
       +\epsilon^2T_\epsilon[\psi f_\epsilon]+O(\epsilon^2).
\tag{20.8}
$$

The first term converges by (20.2), and the second tends to zero
by (20.5). For the potential, the partition splits its integral
exactly, and (3.2) and (15.4) give

$$
\begin{aligned}
\epsilon^2gV_\epsilon[\chi f_\epsilon]
       &=\gamma\int W|w_\epsilon|^2\,d\xi+O(\epsilon^2),\\
0\le\epsilon^2gV_\epsilon[\psi f_\epsilon]
       &\le gC_{\rm out}\epsilon^2\|\psi f_\epsilon\|_2^2 .
\end{aligned}
\tag{20.9}
$$

Multiplication by $W^{1/2}$ is continuous in the fixed free norm by
(15.8); hence the first integral converges to $\int W h_g^2$.
This proves (20.4) on the entire native form domain.
The native ground states of Theorem 4.1 are included by taking
$D_\epsilon=0$, but no ground-state equation for a native state
was used. $\square$

**Definition 20.2 (supplier correspondence and remaining realization
obligations).** The coefficient and domain in (18.1) are those already
defined and proved in Definition 15.1 and Proposition 15.2.
The leading limit and uniform lower remainder are Theorem 16.1,
the sharp uniform threshold is Theorem 16.3, and fixed-neighbourhood
mass concentration is Corollary 16.4. Theorems 18.2–20.1 add the
matched cell's simple isolated ground state and free-form coercivity,
the bounded upper remainder in (19.1), and the universal quantitative
profile with full-domain exterior and coefficient control. They
retain the fixed $g>g_{\rm c}$ regime; the existence of $g_*$ does
not change that scope. The self-field occupation in §17 has its
separate consumer and is not identified with a form-domain profile.

The ordinary compactness and spectral intermediates in Theorem 18.2
are credited there to the precise whole-group Gaussian and bounded
multiplier criteria, together with classical local Hardy, Rellich,
closed-form representation, positive Duhamel expansion and the
spectral theorem. Their application, the weak-equation cutoff
remainder and the exact native profile transfer are repo-derived
composition for this fixed source. No worldwide novelty or Lean
certification is part of these statements.

A native operational realization continues to mean the same
two-control chronology $j=\int a\,db$, original extrema guards,
numerical command domains, actual own death, original clock, and
unhalved charges (6.1). The analytic amplitudes $f_\epsilon$ and
$h_g$ are variational variables, not additional preparation or
actuation operations; choosing their comparison phase is not a
sensing operation. Definition 6.1's ideal-history and paid-point
observation contracts remain distinct. In the paid contract future
Read times use only acquired paid records and the clock, its seed
is independent of the persistent target drivers, and all failed
outcomes and executed partial legs retain their charges. The exact
finite-horizon capped family, positive initial hold, response and
resources are Definitions 12.1 and 14.1, Theorem 12.2 and
Corollary 13.1, with their fixed-positive-noise constants.
Equations (19.1)–(20.4) supply no uniform service constants for that
family and do not remove its uncapped-exposure obstruction.

The adapted chart does not identify three physical Euclidean axes.
The exact symbol, kinetic-distance and all-start original-clock
full-response exclusions of §§9–11 remain applicable.
A physical spatial correspondence still requires its common-source
law, geometry, clock, observations, operations, service costs and
recursive gluing maps. The spectral profile supplies no attractive
sampler, copies or reset operation, finite-bit evaluator, total
tariff, or recursive gluing construction. Equality of dimensions
does not provide any of these missing correspondences.

## 追加锚（本行以下为增补区）

## 21. Global native kinetic distances on the profile core

**Definition 21.1 (fixed source and the distance comparison).** In
§§21–25 retain exactly Definitions 15.1 and 18.1, including
$g>g_{\rm c}=2\pi m_0\lambda_0$, the fixed $Z,r,H,l,u,o$,
arbitrary fixed preparation phases, both actual $2\pi$ periods,
raw $d\mu=dk\,d\alpha\,d\beta$, and the entire complex
$\mathcal F_\epsilon$. Only $\epsilon=|\nu|\downarrow0$ varies;
either nonzero sign is allowed. The conditional law remains (1.2),
with its persistent independent covariance-$2$ triple, zero area drift,
original clock, and first-exit absorption at both height faces.
The form is $q_{\epsilon,g}=T_\epsilon-gV_\epsilon$, with its own
full unit-source matched Green field and bottom $E_\epsilon(g)$.
For a normalized complex $f\in\mathcal F_\epsilon$ put

$$
D_\epsilon(f)=\epsilon^2(q_{\epsilon,g}[f]-E_\epsilon(g))\ge0,
\qquad \iota_\epsilon=\Phi_o\circ\delta_\epsilon,
\qquad \lambda_g(d\xi)=h_g(\xi)^2\,d\xi .
\tag{21.1}
$$

Here $h_g$ is exactly Theorem 18.2's normalized cell minimizer,
not a new native preparation. Fix the source-adapted partition of
Definition 18.1 once; its choice depends only on the fixed source.
Write $w_\epsilon=\mathcal B_\epsilon f$. The measure $\lambda_g$
is a probability measure, whereas the raw native measure is not.
A genuine near-minimizer family means $D_\epsilon(f_\epsilon)\to0$,
as in Theorem 20.1; no positivity, eigenfunction or tail hypothesis
is included in that phrase.

Let $d_\epsilon^\Omega$ be the **global** intrinsic length distance
of the kinetic metric $g_\epsilon$ in (9.3): take the infimum of
lengths of all piecewise smooth curves in the periodic open cylinder
$\Omega$ joining the two points. The metric has orthonormal frame
$(P,Q,\epsilon Z_c)$. Neither the absorbing faces nor the isolated
cemetery are additional roads in this definition. Curves can explore
the entire cylinder, including its phase periods. This is distinct
from the wrapped tracking metric, command distance and command prices.
On the whole group write $d_1$ for Definition 2.1's unit-noise length
distance and $K_R=\{\xi:d_1(0,\xi)\le R\}$.

**Proposition 21.2 (exact global localization, including all deck
classes).** For every fixed finite $R>0$, $K_R$ is compact. For all
sufficiently small $\epsilon>0$, $\iota_\epsilon$ is injective on
$K_R$, its image is contained in $\{\chi=1\}\Subset\Omega$, and

$$
\begin{aligned}
d_\epsilon^\Omega(\iota_\epsilon\xi,
                     \iota_\epsilon\eta)&=\epsilon d_1(\xi,\eta)
                     &&(\xi,\eta\in K_R),\\
B_{d_\epsilon^\Omega}(o,\epsilon R)
                     &=\iota_\epsilon(B_{d_1}(0,R)),\\
\iota_\epsilon^*g_\epsilon&=\epsilon^2g_1,
\qquad \iota_\epsilon^*d\mu=m_0\epsilon^4d\xi .
\end{aligned}
\tag{21.2}
$$

The same conclusions hold simultaneously for any finite collection
of fixed radii. They concern the original-cylinder global distance,
not a distance artificially restricted to the displayed core.

Proof. Properness of $d_1$ is the regularized gauge estimate (2.4):
bounded $d_1$ bounds $x,y,\theta$, and the smooth positive metric has
the ordinary coordinate topology. Thus its closed balls are compact.
Direct substitution of $\delta_\epsilon(x,y,\theta)
=(\epsilon x,\epsilon y,\epsilon^2\theta)$ into (9.3) gives the
metric identity in (21.2); the determinant and (15.1) give the raw
measure identity. Images of fixed compact sets eventually lie in the
fixed injective source chart and in $\{\chi=1\}$.

To verify that global curves cannot shorten the distance, use the
cover with height $x\in(l-k_o,u-k_o)$ and unwrapped $y,\theta$.
The fields, metric and deck action there are exactly (2.2)–(2.3).
For a curve of $g_\epsilon$ speed $v$, its coordinate derivatives
satisfy

$$
|\dot x|,|\dot y|\le v,\qquad
|\dot\theta|\le\epsilon v+
                  \tfrac12(|y|\,|\dot x|+|x|\,|\dot y|).
\tag{21.3}
$$

Choose $A$ bounding the absolute coordinates on $K_R$, and a fixed
$L>2R+1$. A lifted curve starting at $\delta_\epsilon\xi$,
$\xi\in K_R$, of length at most $\epsilon L$ obeys

$$
\begin{aligned}
\sup(|x|\vee|y|)&\le\epsilon(A+L),\\
\sup|\theta|&\le\epsilon^2\{A+L+(A+L)L\} .
\end{aligned}
\tag{21.4}
$$

This follows by integrating (21.3), including the initial coordinate
bounds $|x|,|y|\le\epsilon A$, $|\theta|\le\epsilon^2A$.
All these lifted curves stay in one fixed injective neighbourhood
for small $\epsilon$. In particular their heights are strictly
between the two faces, whose distances in the height coordinate
from the pole are fixed positive numbers.

For completeness, a cylinder curve ending at
$\iota_\epsilon\eta$ could lift to a deck translate of
$\delta_\epsilon\eta$. A nonzero $n$ in (2.3) changes $y$ by
$4\pi n$, contradicting (21.4). When $n=0$, a nonzero $m$ changes
$\theta$ by $-2\pi r m$, also contradicting (21.4).
The shear for $n\ne0$ has not been discarded: that case was already
excluded by its $y$ displacement. Consequently every curve of
length less than $\epsilon L$ joining core points has the direct
lift. Scaling that lift gives length divided by $\epsilon$ in
$g_1$, and hence a lower bound $\epsilon d_1(\xi,\eta)$.
Curves of length at least $\epsilon L$ satisfy this lower bound
as well, since $d_1(\xi,\eta)\le2R<L$.

Conversely, unit-group curves with length arbitrarily close to
$d_1(\xi,\eta)$ can be chosen with length less than $L$.
The unit version of (21.3) bounds their coordinates in a fixed
compact set. Their dilations therefore lie entirely inside the
source chart and strictly inside both faces for small $\epsilon$.
Their native lengths are exactly $\epsilon$ times their unit
lengths. Taking infima proves the first line of (21.2).
Finally any cylinder curve starting at $o$ of length less than
$\epsilon R$ obeys the same coordinate bound, so its endpoint has
one chart representative whose scaled unit distance is less than
$R$. Conversely every unit point of distance less than $R$ is
reached by such a dilated curve. This proves the ball equality,
also for endpoints not initially assumed to lie in the chart.
There is no boundary or deck shortcut left in the infimum.
No change of the stochastic clock was made. $\square$

## 22. A positive Hilbert chord-error floor for the actual profile

**Theorem 22.1 (uniform truncated pair error on one fixed native
core).** Under Definition 21.1 there are a fixed $R\ge1$,
$K=K_R$, constants $c_0,d_0,\epsilon_0>0$, and corresponding
original-source cores $C_\epsilon=\iota_\epsilon K$, depending
only on the fixed source and $g$, with the following property.
For every $0<\epsilon<\epsilon_0$, every normalized complex
$f\in\mathcal F_\epsilon$ with $D_\epsilon(f)\le d_0$, every
separable real Hilbert space $\mathscr H$, and every Borel
$F:C_\epsilon\to\mathscr H$, set

$$
\begin{aligned}
\mu_f(dq)&=|f(q)|^2d\mu(q),\qquad
 M_\epsilon=\mu_f(C_\epsilon),\\
\ell_{\epsilon,F}(q,q')
 &=\min\left\{1,\left(
 \frac{\|F(q)-F(q')\|_{\mathscr H}-d_\epsilon^\Omega(q,q')}
      {\epsilon}\right)^2\right\},\\
I_{\epsilon,f}(F)
 &=\int_{C_\epsilon}\int_{C_\epsilon}
            \ell_{\epsilon,F}(q,q')\,\mu_f(dq)\mu_f(dq').
\end{aligned}
\tag{22.1}
$$

Then, uniformly in all these choices,

$$
\tfrac12\le M_\epsilon\le1,\qquad
 I_{\epsilon,f}(F)\ge c_0,\qquad
 \frac{I_{\epsilon,f}(F)}{M_\epsilon^2}\ge c_0 .
\tag{22.2}
$$

The first integral is the unnormalized restriction of the pair
probability $\mu_f\otimes\mu_f$ to the core. The last expression
uses the core-conditioned probability
$(\mu_f|_{C_\epsilon}/M_\epsilon)^{\otimes2}$.
The map can depend on $f$ and $\epsilon$; its image, derivatives,
rank, injectivity and output dimension have no imposed bounds.

Proof. We first extract a strict finite configuration from the
already computed native metric; this is an intermediate step in the
profile statement, not a new general embedding classification.
At unit noise, (9.10) gives
$\langle R(U,Z_H)Z_H,U\rangle=1/4$ at zero, with the convention
(9.8). In a sufficiently small convex normal neighbourhood set

$$
a_1=\operatorname{Exp}_0(tU),\quad
 a_2=\operatorname{Exp}_0(-tU),\quad
 a_3=\operatorname{Exp}_0(tZ_H),\quad
 a_4=\operatorname{Exp}_0(-tZ_H),\qquad
 (s_1,s_2,s_3,s_4)=(1,1,-1,-1).
\tag{22.3}
$$

Here $t>0$ is fixed below, independently of $\epsilon$.
The classical normal-coordinate distance expansion used is

$$
d_1(\operatorname{Exp}_0v,\operatorname{Exp}_0w)^2
 =|v-w|^2-\tfrac13\langle R(v,w)w,v\rangle
                      +O((|v|+|w|)^5).
\tag{22.4}
$$

A primary supplier is Xavier Pennec, *Curvature effects on the
empirical mean in Riemannian and affine Manifolds: a non-asymptotic
high concentration expansion in the small-sample regime*,
[arXiv:1906.07418v1, §3.3, (9)](https://arxiv.org/html/1906.07418v1#S3.SS3).
Its curvature definition in §2, (1), is exactly (9.8).
Its fourth-order term is
$\langle R(w,v)w,v\rangle/3$, equal to the negative term in
(22.4); its displayed fifth-order term is absorbed in the remainder.
Only this local deterministic expansion is used, with no statistical
sampling or empirical-mean hypothesis transferred from that paper.

The two opposite radial distances in (22.3) are exactly $2t$.
Each of the four cross squared distances is
$2t^2-t^4/12+O(t^5)$. Thus

$$
\begin{aligned}
S(a_1,a_2,a_3,a_4)
 &:=\sum_{i,j=1}^4s_is_jd_1(a_i,a_j)^2\\
 &=2\{4t^2+4t^2-4(2t^2-t^4/12)\}+O(t^5)
   =\tfrac23t^4+O(t^5)>0
\end{aligned}
\tag{22.5}
$$

for one sufficiently small fixed $t$. These are global $d_1$
distances: the normal neighbourhood is chosen small enough that its
short radial and cross segments realize the ordinary Riemannian
distance. Choose disjoint open neighbourhoods $A_i$ of these four
points, with compact closures. By continuity, after shrinking them
there is $\sigma>0$ such that

$$
S(\xi_1,\xi_2,\xi_3,\xi_4)\ge\sigma
                  \quad(\xi_i\in A_i).
\tag{22.6}
$$

Choose $R\ge1$ large enough that their closures lie inside $K_R$
and $\lambda_g(K_R)\ge3/4$; this uses only $\int h_g^2=1$.
Write $K=K_R$. Strict almost-everywhere positivity in Theorem 18.2
gives

$$
b=\min_{1\le i\le4}\lambda_g(A_i)>0,\qquad
 a=b/2,\qquad
 \tau=\min\{1/2,\sigma/[24(4R+1)]\}>0.
\tag{22.7}
$$

For any four vectors $v_i$ in any real Hilbert space, expansion of
the squares and $\sum s_i=0$ give the elementary negative-type identity

$$
\sum_{i,j}s_is_j\|v_i-v_j\|^2
                  =-2\left\|\sum_i s_iv_i\right\|^2\le0 .
\tag{22.8}
$$

This is the necessary Hilbert squared-distance condition associated
with the classical metric-embedding theory of I. J. Schoenberg,
[*Metric spaces and positive definite functions*, Trans. Amer.
Math. Soc. 44, 522–536](https://doi.org/10.1090/S0002-9947-1938-1501980-0).
The identity above proves the precise necessity used here directly;
no sufficiency or dimension bound from that theory is needed.
If for a tuple in $\prod_i A_i$ all six errors
$|\|v_i-v_j\|-d_1(\xi_i,\xi_j)|$ were less than $\tau$, then
$d_1(\xi_i,\xi_j)\le2R$ would imply

$$
\left|\|v_i-v_j\|^2-d_1(\xi_i,\xi_j)^2\right|
       <\tau(4R+1),\qquad
 |S(\xi_1,\ldots,\xi_4)-S_{\mathscr H}(v_1,\ldots,v_4)|
       <12\tau(4R+1)\le\sigma/2 .
\tag{22.9}
$$

This contradicts (22.6) and (22.8). Consequently at least one of
the six errors is at least $\tau$ for every tuple and every choice
of its four images.

We now use the actual near-minimizer density, rather than postulating
that $f$ has a chosen shape. Theorem 20.1 gives constants $C_{20},d$
and $\epsilon_g$, and a spatially constant phase, with
$\|\zeta^{-1}w_\epsilon-h_g\|_2^2
\le C_{20}(D_\epsilon(f)+\epsilon^2)$ when its stated bounds hold.
Since $\|w_\epsilon\|_2\le1$, Cauchy–Schwarz gives

$$
\big\||w_\epsilon|^2-h_g^2\big\|_1
 \le2\sqrt{C_{20}(D_\epsilon(f)+\epsilon^2)}
 =:\eta_\epsilon(f).
\tag{22.10}
$$

Choose $d_0\le d$ and $\epsilon_0\le\epsilon_g$ small enough that
Proposition 21.2 applies to $K$ and
$\eta_\epsilon(f)\le\min(b/16,1/16)$ whenever
$D_\epsilon(f)\le d_0$, $\epsilon<\epsilon_0$.
On $K$, $\chi\circ\iota_\epsilon=1$, so the exact raw-density
identity is

$$
\iota_\epsilon^*(\mu_f|_{C_\epsilon})
       =\mathbf1_K|w_\epsilon|^2d\xi=:\nu_\epsilon(d\xi),
\quad
\nu_\epsilon(A_i)\ge b-\eta_\epsilon\ge a,
\quad M_\epsilon\ge3/4-\eta_\epsilon\ge1/2 .
\tag{22.11}
$$

Define $G(\xi)=\epsilon^{-1}F(\iota_\epsilon\xi)$. By (21.2),
the integrand of (22.1) pulls back exactly to
$\ell_G(\xi,\eta)=\min\{1,(\|G(\xi)-G(\eta)\|-d_1(\xi,\eta))^2\}$.
For every tuple in $\prod_i A_i$, (22.9) yields
$\sum_{i<j}\ell_G(\xi_i,\xi_j)\ge\tau^2$.
Integrate against the product of the four probabilities
$\nu_\epsilon|_{A_i}/\nu_\epsilon(A_i)$. Tonelli gives

$$
\tau^2\le\sum_{i<j}
 \frac{\int_{A_i\times A_j}\ell_G\,d\nu_\epsilon d\nu_\epsilon}
      {\nu_\epsilon(A_i)\nu_\epsilon(A_j)}
 \le a^{-2}\sum_{i<j}
       \int_{A_i\times A_j}\ell_G\,d\nu_\epsilon d\nu_\epsilon .
\tag{22.12}
$$

The six rectangles and their reverses are disjoint. Symmetry therefore
implies $I_{\epsilon,f}(F)\ge2a^2\tau^2=:c_0>0$.
Division by $M_\epsilon^2\le1$ gives the conditional bound.
All functions integrated here are Borel and bounded; separability
ensures the usual product-measurability of the Hilbert-valued pair
map. No continuity or integrability of $F$ was used. The argument
also applies to restrictions of Borel maps defined on all of $\Omega$.
$\square$

## 23. Optimal RMS order and retention of almost all profile mass

**Corollary 23.1 (sharp order at the collapse scale).** With the
constants and quantifiers of Theorem 22.1, define the possibly infinite
unnormalized RMS and its core-conditioned version by

$$
\begin{aligned}
\mathcal R_{\epsilon,f}(F)^2
 &=\int_{C_\epsilon\times C_\epsilon}
    (\|F(q)-F(q')\|-d_\epsilon^\Omega(q,q'))^2
                          \,\mu_f(dq)\mu_f(dq'),\\
\mathcal R^{\rm cond}_{\epsilon,f}(F)
 &=\mathcal R_{\epsilon,f}(F)/M_\epsilon .
\end{aligned}
\tag{23.1}
$$

For either choice $\mathcal R^\star\in
\{\mathcal R,\mathcal R^{\rm cond}\}$,

$$
\sqrt{c_0}\,\epsilon
 \le\inf_{\mathscr H,F}\mathcal R^\star_{\epsilon,f}(F)
 \le2R\epsilon .
\tag{23.2}
$$

The infimum ranges over all separable real Hilbert spaces and all
Borel maps as above. The upper bound is realized as a comparison
bound by one constant map into $\mathbb R$; it is not an asserted
optimal coefficient. The same two bounds hold for the infimum over
maps into any one fixed nonempty separable real Hilbert space.

Proof. Pointwise, the squared untruncated error divided by
$\epsilon^2$ is at least the truncated loss. Hence (22.2) proves
the lower bounds, including maps whose untruncated integral is
infinite. For a constant map, its error is exactly
$d_\epsilon^\Omega(q,q')\le2R\epsilon$ by (21.2).
Its unnormalized RMS is at most $2R\epsilon M_\epsilon$ and its
conditioned RMS is at most $2R\epsilon$. This proves the uniform
upper bounds and the order claim. In particular absolute best error
vanishes with $\epsilon$; the strictly positive floor is after
normalization by the actual collapse length $\epsilon$. $\square$

**Theorem 23.2 (deleting vanishing profile mass preserves the actual
retained-pair floor).** Keep the same $K,c_0,d_0,\epsilon_0$.
Let $A_\epsilon\subset C_\epsilon$ be any Borel retained set and
put

$$
\delta_\epsilon=\mu_f(C_\epsilon\setminus A_\epsilon),\qquad
 M_{\epsilon,A}=\mu_f(A_\epsilon),\qquad
 \delta_0=\min(b/8,1/8),
\tag{23.3}
$$

where $b$ is (22.7). If $\delta_\epsilon\le\delta_0$, then
$M_{\epsilon,A}\ge1/2$ and, for every Borel Hilbert map on the
retained set,

$$
\begin{aligned}
\int_{A_\epsilon\times A_\epsilon}
       \ell_{\epsilon,F}\,d\mu_f d\mu_f&\ge c_0,\\
M_{\epsilon,A}^{-2}
 \int_{A_\epsilon\times A_\epsilon}
       \ell_{\epsilon,F}\,d\mu_f d\mu_f&\ge c_0 .
\end{aligned}
\tag{23.4}
$$

The two sharp-order RMS bounds (23.2) also hold with the core replaced
by $A_\epsilon$ and conditioning by $M_{\epsilon,A}$.
This applies to arbitrary retained sets depending on $f,\epsilon$
and even on the proposed map. In particular it applies eventually
when the deleted actual mass is $o(1)$. It also applies eventually
if the deleted **profile** mass
$\lambda_g(\iota_\epsilon^{-1}(C_\epsilon\setminus A_\epsilon))$
is $o(1)$, uniformly for the states in Theorem 22.1.
For genuine near-minimizer families these two notions of deleted
mass differ by $o(1)$.

Proof. Restrict $\nu_\epsilon$ in (22.11) to the pullback of the
retained set. Each witness neighbourhood now has mass at least
$b-\eta_\epsilon-\delta_\epsilon\ge b/2=a$.
The retained core has mass at least
$3/4-1/16-1/8>1/2$.
The tuple inequality remains pointwise true, so (22.12) and its
symmetric-rectangle argument prove exactly the same constant $c_0$.
The truncated-to-untruncated lower bound and the constant-map upper
bound are unchanged. No extension or regularity of a retained-set
map is needed.

For a deleted pullback set $B_\epsilon\subset K$, (22.10) gives

$$
|\mu_f(\iota_\epsilon B_\epsilon)-\lambda_g(B_\epsilon)|
              \le\eta_\epsilon(f)\le\delta_0/2.
\tag{23.5}
$$

Thus deleted profile mass at most $\delta_0/2$ implies the required
actual deletion bound. If $D_\epsilon(f_\epsilon)\to0$, then
$\eta_\epsilon(f_\epsilon)\to0$, proving the last statement.
The pair measure in (23.4) is precisely
$(\mu_f|_{A_\epsilon})\otimes(\mu_f|_{A_\epsilon})$:
both actual points must be retained. If the original core mass is
$M_\epsilon$, the removed pair mass is exactly

$$
M_\epsilon^2-M_{\epsilon,A}^2
        =2M_\epsilon\delta_\epsilon-\delta_\epsilon^2
        \le2\delta_\epsilon .
\tag{23.6}
$$

This is not a permission to delete selected bad pairs while retaining
their individual points. The product is an integration convention;
it grants no independent copies, resampling or observation service.
$\square$

## 24. Vanishing mass in a smaller kinetic tangent window

**Theorem 24.1 (a flat tangent window cannot contain a nonvanishing
near-minimizer mass).** Under Definition 21.1, let
$D_\epsilon(f_\epsilon)\to0$ and let $s_\epsilon>0$ satisfy
$s_\epsilon/\epsilon\to0$. Then

$$
\int_{B_{d_\epsilon^\Omega}(o,s_\epsilon)}
                   |f_\epsilon|^2d\mu\longrightarrow0 .
\tag{24.1}
$$

The same conclusion holds for the image under the kinetic exponential
map at $o$ of a tangent ball of $g_\epsilon(o)$-radius
$s_\epsilon$, and for the frozen-symbol coordinate ellipsoid

$$
\Phi_o\{(x,y,\theta):x^2+y^2+\epsilon^{-2}\theta^2
                                      \le s_\epsilon^2\}.
\tag{24.2}
$$

These windows are centered at the specified pole. No claim about
windows centered elsewhere, or about fixed positive scaled defect,
is included in this vanishing-mass statement.

Proof. Fix any radius $R>0$. For sufficiently small $\epsilon$,
$s_\epsilon<\epsilon R$. Proposition 21.2, and the same direct-lift
argument for any smaller radius, identify the ball in (24.1) exactly
with $\iota_\epsilon B_{d_1}(0,s_\epsilon/\epsilon)$.
It lies in $\{\chi=1\}$. Consequently (22.10) yields

$$
\int_{B_{d_\epsilon^\Omega}(o,s_\epsilon)}|f_\epsilon|^2d\mu
 \le\lambda_g(B_{d_1}(0,s_\epsilon/\epsilon))
                         +\eta_\epsilon(f_\epsilon)\longrightarrow0 .
\tag{24.3}
$$

The first term tends to zero because $h_g^2\in L^1(d\xi)$ and
these shrinking balls have intersection $\{0\}$, which has zero
Lebesgue measure; the second tends to zero by the genuine
near-minimizer hypothesis. Closed balls give the same bound.
Each radial exponential curve has length equal to its initial tangent
norm, so the tangent image lies in the corresponding closed intrinsic
ball. It is defined here for small radii inside the local normal
chart, as follows also by the homothety in (21.2) from the unit metric.
Finally (24.2) pulls back under $\iota_\epsilon$ to the ordinary
coordinate ball $x^2+y^2+\theta^2\le(s_\epsilon/\epsilon)^2$.
The same $L^1$ discrepancy and absolute continuity prove its vanishing
mass. Thus a window on which the rescaled geometry tends to its flat
tangent cannot replace the fixed profile core while retaining a
positive fraction of a genuine near-minimizer's mass. $\square$

## 25. Correspondence and the remaining spatial-realization contract

**Definition 25.1 (attribution and the precise consumer).** The
classical deterministic intermediates in Theorem 22.1 are the
normal-coordinate distance expansion attributed there to Pennec,
§2, (1), and §3.3, (9), and the Hilbert squared-distance negative-type
identity (22.8), within Schoenberg's classical metric-embedding
framework. The necessary identity is proved directly and its
sufficiency is not invoked. The metric, mixed sectional curvature,
raw-density normalization and source dilation are the existing
Definitions 2.1, 9.1, 15.1, 18.1 and (9.10). The positive profile and
its full-complex-domain uniform approximation are Theorems 18.2 and
20.1, not new variational or spectral claims.

The additional source-specific composition is the global periodic
killed-cylinder distance localization (21.2), the positive average
error on its actual near-minimizer density (22.2), its retained-pair
and sharp-order consequences, and the smaller-window mass exclusion.
These are repo-derived ordinary mathematical results. They carry no
worldwide novelty, experimental or Lean/kernel certification claim.
Their named spatial consumer is the kinetic-distance branch of
Definition 11.2: the exact smooth comparison of Corollary 9.3 is now
supplemented by a quantitative average test for arbitrary Borel
Euclidean or Hilbert **chord** readouts on the actual collapse core.
The analytic error is normalized by $\epsilon$ and weighted by the
actual $|f|^2d\mu$, rather than an imposed uniform coordinate density.

A candidate common-source realization may require this distance
contract in addition to its own law, clock and operations; if it does,
Theorem 22.1 excludes vanishing normalized pair error under the stated
near-minimizer conditions. It selects no physical spatial dimension.
In particular an obstruction to all Hilbert chord targets does not
prefer one Hilbert dimension over another. Curved targets, variable
target metric, intrinsic submanifold distance, a specified task metric,
coarser absolute error tolerances and a separately justified
homogenization limit are different contracts. Theorems 22.1–24.1
make no identification with any of them. The upper bound (23.2)
explicitly permits absolute error tending to zero.

The original law (1.2) and the raw full-field occupation in Theorem
1.3 and §17 are distinct from the analytic variational probability
$|f|^2d\mu$. That probability is neither a Brownian occupation law nor
an acquired data source. Spatial dilation and multiplication of the
comparison map by $\epsilon^{-1}$ in the proof install no clock or
control operation. All native $P,Q$ chronologies remain
$j=\int a_{\rm cmd}\,db_{\rm cmd}$, with the original extrema,
whole-command and prefix guards, numerical domains, actual own death,
and four unhalved original-time charges (6.1). The signed central
noise remains a supplied independent law, not a third primitive.
No charge or guard is inferred from the auxiliary kinetic lengths.

The paid finite-report consumer in
[Paid-point observation tracking, Definitions 55.1–55.2, Theorems
57.2–57.3 and 58.2](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md#55-finite-reports-under-the-installed-exact-point-interface)
retains its installed paid exact-point Read, finite-message dependence,
wrapped held-path accuracy, fixed-field-cap response and separately
charged primitive execution. It is not physical finite-bit sensing;
postprocessing an acquired exact point supplies no sensing precision
or arithmetic/memory tariff. Its probabilities and metric are not
(22.1), and its initial-hold obstruction to uncapped native exposure
is not removed by a variational profile. Neither consumer supplies
an attractive sampler, native preparation of $h_g$, reset, copies,
independent resampling, finite arithmetic or memory, total service
tariff, or recursive spectral gluing. A complete why-three
correspondence still needs its common-source spatial map with a
justified geometry, the preserved path law and original clock,
actual paid acquisition and operation/resource accounting, and
compatible recursive gluing maps on that same realization. Equality
of dimensions or a product pair integral supplies none of these
missing premises.

## 追加锚（本行以下为增补区）

## 26. A common analytic seam in the original free cylinder

**Definition 26.1 (fixed laws, raw seam and slab operators).** Retain
Definitions 1.1–1.2 verbatim, including $r=1-Z>0$, $c(k)=1/2-k/r$,
both $2\pi$ periods, raw $d\mu=dk\,d\alpha\,d\beta$, the pole $o$,
zero area drift, covariance-$2$ independent Brownian motions and the
original clock. Fix $h\in(l,u)\setminus\{k_o\}$ and write

$$
\begin{aligned}
\Sigma&=\{h\}\times\mathbb T^2,&d\sigma&=d\alpha\,d\beta,\\
\Omega_-&=(l,h)\times\mathbb T^2,&
\Omega_+&=(h,u)\times\mathbb T^2,\\
\ell_-&=h-l,&\ell_+&=u-h,\qquad
\ell=\ell_-+\ell_+,\quad d=\min(\ell_-,\ell_+),\\
A_0&=\ell_-^{-1}+\ell_+^{-1},&
\mathscr H&=L^2(\Omega,d\mu;\mathbb C),\quad
\mathscr K=L^2(\Sigma,d\sigma;\mathbb C).
\end{aligned}
\tag{26.1}
$$

All pairings are linear in the first argument; in particular
$\langle g,v\rangle_\Sigma=\int g\overline v\,d\sigma$.
For each separately fixed supplied law $\epsilon=|\nu|>0$, let
$L_{\epsilon,D,\pm}$ be the same differential expression as (1.4)
on $\Omega_\pm$, with zero Dirichlet data at both its height faces.
Put $L_{\epsilon,D}=L_{\epsilon,D,-}\oplus L_{\epsilon,D,+}$ on
$\mathscr H$. The artificial Dirichlet condition at $h$ defines a
comparison operator; it does not change the actual killing in (1.2).
The variable $s\ge0$ below is a resolvent parameter, not time, a
command, an area drift or a coupling. Varying $\epsilon$ compares
supplied laws and grants no change-of-law operation.

**Definition 26.2 (modal lift and summed outward flux).** Use the
orthonormal basis for the raw seam measure

$$
e_{mn}(\alpha,\beta)=(2\pi)^{-1}e^{i(m\alpha+n\beta)},\qquad
b=n/r,\quad t=|b|,\quad q=m/2+c(h)n,\qquad (m,n)\in\mathbb Z^2.
\tag{26.2}
$$

In the height coordinate $x=k-h$, the exact mode expression is

$$
-\frac{d^2}{dx^2}+V_{mn}(x),\qquad
V_{mn}(x)=(q-bx)^2+\epsilon^2b^2+s.
\tag{26.3}
$$

Let $\phi_{mn,-}$ on $[-\ell_-,0]$ and $\phi_{mn,+}$ on
$[0,\ell_+]$ solve $-\phi''+V_{mn}\phi=0$, with value $1$ at
$0$ and value $0$ at the other endpoint. These are the unique
energy minimizers with those endpoint values. Join them continuously
at $0$, calling the resulting function $\phi_{mn}$. Define

$$
\begin{aligned}
a_{mn}^\epsilon(s)
 &=\phi'_{mn,-}(0)-\phi'_{mn,+}(0)\\
 &=\min_{\substack{v\in H_0^1(-\ell_-,\ell_+)\\v(0)=1}}
   \int_{-\ell_-}^{\ell_+}
        \bigl(|v'|^2+V_{mn}|v|^2\bigr)\,dx,\\
P_sg&=\sum_{m,n}g_{mn}\phi_{mn}(k-h)e_{mn}(\alpha,\beta),
\qquad g_{mn}=\langle g,e_{mn}\rangle_\Sigma,\\
\mathscr T_s&=\left\{g\in\mathscr K:
                   \sum_{m,n}a_{mn}^\epsilon(s)|g_{mn}|^2<\infty\right\},\\
D(N_\epsilon(s))&=\left\{g\in\mathscr K:
                   \sum_{m,n}(a_{mn}^\epsilon(s))^2|g_{mn}|^2<\infty\right\},\\
N_\epsilon(s)g&=\sum_{m,n}a_{mn}^\epsilon(s)g_{mn}e_{mn},
\qquad C_\epsilon(s)=N_\epsilon(s)^{-1}.
\end{aligned}
\tag{26.4}
$$

The common-trace DtN form is
$\mathfrak n_s(g,v)=\sum a_{mn}^\epsilon(s)g_{mn}\overline{v_{mn}}$
on $\mathscr T_s$. For smooth traces its operator is exactly
$\partial_k(P_sg)|_{h-}-\partial_k(P_sg)|_{h+}$: the two
outward conormal derivatives sum, rather than cancel. The fields
$Q,Z_c$ are tangent to $\Sigma$ and the height coefficient is one,
so the pairing is the raw $d\sigma$, without a probability or chart
Jacobian factor. The diagonal form and operator in (26.4) specify
also the nonsmooth domains. The subscript $s$ on $P_s,\mathscr T_s$
suppresses dependence on the same fixed $\epsilon,h$.

**Proposition 26.3 (bounded Poisson realization).** The series for
$P_s$ extends from finite Fourier sums to a bounded map
$\mathscr K\to\mathscr H$, uniformly for every $s\ge0$ and
$\epsilon>0$, and

$$
a_{mn}^\epsilon(s)\ge A_0,\qquad
\|P_s\|_{\mathscr K\to\mathscr H}^2\le\ell/3,
\qquad \|C_\epsilon(s)\|\le A_0^{-1}.
\tag{26.5}
$$

At $s=0$ the bound on $P_s$ is an equality. For fixed
$\epsilon>0,s\ge0$, the trace form domain is $H^{1/2}(\mathbb T^2)$
and the strong DtN domain is $H^1(\mathbb T^2)$; these last norm
equivalences are not asserted uniformly as $\epsilon\downarrow0$.
For $g$ in the trace domain, $P_sg$ is the energy-minimizing
piecewise harmonic $H^1$ function with common trace $g$ and zero
outer-face trace. For arbitrary $g\in\mathscr K$ it is the bounded
$L^2$ Poisson realization, without an assertion of finite $H^1$
energy for every such $g$.

Proof. On each affine endpoint space the one-dimensional energy is
coercive and strictly convex. Its unique minimizer satisfies the ODE;
integration by parts identifies its energy with the outward flux in
(26.4). The derivative energy of any admissible mode is at least
$\ell_-^{-1}+\ell_+^{-1}$ by Cauchy–Schwarz on the two intervals.
The real ODE maximum principle gives $0\le\phi_{mn,\pm}\le1$;
for example testing a negative part or an excess above $1$ in the
variational equation proves these inequalities. Since
$\phi''=V_{mn}\phi\ge0$, each half is bounded above by its linear
endpoint interpolant. Thus
$\int|\phi_{mn}|^2dx\le\ell/3$. Parseval proves the bounded
extension and (26.5); $m=n=s=0$ has exactly those interpolants.
The positive diagonal form is closed, and its associated operator
and bounded inverse are exactly (26.4). The domain and trace
identifications follow from the full-lattice estimate proved next:
for fixed $\epsilon,s$, its weight is equivalent to
$\sqrt{1+m^2+n^2}$. Parseval then identifies its form and operator
domains with $H^{1/2}$ and $H^1$. Summing the modal minimum identity
gives exactly $T_\epsilon[P_sg]+s\|P_sg\|_2^2=\mathfrak n_s(g,g)$.
The fixed-$\epsilon$ kinetic norm is equivalent to $H^1$; the common
modal endpoint values give its actual trace. Conversely any $H^1$
competitor with that trace has at least each modal minimum, proving
the asserted minimization and uniqueness. $\square$

## 27. Uniform full-lattice native seam flux

**Theorem 27.1 (all modes, including turning modes).** Define the
explicit constants

$$
c_*=(19+A_0^{-1})^{-1},\qquad C_*=4+2/d,
\qquad M=1+\sqrt s+|m/2+c(h)n|+\sqrt{|n|/r}
                          +\epsilon|n|/r.
\tag{27.1}
$$

For all $(m,n)\in\mathbb Z^2$, $s\ge0$ and $\epsilon>0$,

$$
c_*M\le a_{mn}^\epsilon(s)\le C_*M.
\tag{27.2}
$$

In particular the constants are uniform for
$0<\epsilon\le\epsilon_0<\infty$, with no dependence on
$\epsilon_0,s,m,n$, the pole, preparation phases or the sign of
$\nu$. Their geometry dependence is only the two fixed slab lengths;
$r$ and $c(h)$ occur explicitly in the weight. No lower bound on
$|q|/\sqrt t$ and no exclusion of a zero of $q-bx$ is imposed.
The exact $n=0$ calibration is

$$
a_{m0}^\epsilon(s)=\omega\bigl[\coth(\omega\ell_-)
                         +\coth(\omega\ell_+)\bigr],
\qquad \omega=\sqrt{s+m^2/4}.
\tag{27.3}
$$

Its value at $\omega=0$ is the continuous limit $A_0$.

Proof. Write $E$ for the energy of an arbitrary admissible $v$ in
(26.4), extended by zero to $\mathbb R$. The elementary full-line
trace inequality is

$$
1=|v(0)|^2\le\|v'\|_2\|v\|_2.
\tag{27.4}
$$

Indeed integrate $(|v|^2)'$ on each half-line, add the two absolute
bounds and use Cauchy–Schwarz. The endpoint derivative bound gives
$E\ge A_0$. With $\kappa=\sqrt{s+\epsilon^2t^2}$, (27.4) and
$E\ge\|v'\|_2^2+\kappa^2\|v\|_2^2$ give
$E\ge2\kappa$, hence $\sqrt s\le E/2$ and
$\epsilon t\le E/2$.

For $t>0$ put $w(x)=tx-\operatorname{sgn}(b)q$. Completing the
classical harmonic-oscillator square, with the zero endpoint traces,
gives

$$
0\le\int|v'+wv|^2dx
 =\int\bigl(|v'|^2+(q-bx)^2|v|^2\bigr)dx-t\|v\|_2^2.
\tag{27.5}
$$

Consequently $t\|v\|_2^2\le E$; combined with (27.4) this gives
$\sqrt t\le E$. The same bound is trivial when $t=0$.
If $|q|\ge\sqrt t$ and $q\ne0$, set $\delta_q=1/(2|q|)$.
On $[0,\delta_q]$, $|q-bx|\ge|q|/2$. The zero extension is valid
also when this interval crosses the outer face. For each such $x$,

$$
1\le2|v(x)|^2+2\delta_q\int_0^{\delta_q}|v'|^2dy.
$$

Averaging in $x$ and using the potential lower bound gives

$$
1\le\frac2{\delta_q}\int_0^{\delta_q}|v|^2dx+2\delta_q E
 \le\frac{17E}{|q|}.
\tag{27.6}
$$

If instead $|q|<\sqrt t$, (27.5) already gives $|q|\le E$.
Thus in all cases $|q|\le17E$. Adding the five bounds proves
$M\le(19+A_0^{-1})E$, and minimization proves the lower inequality.
These arguments use no distance from a turning point.

For the upper inequality set $\delta=\min(d,M^{-1})$ and use the
admissible tent $v(x)=(1-|x|/\delta)_+$. Its integrals are

$$
\int|v'|^2=2/\delta,\qquad \int|v|^2=2\delta/3,
\qquad \int x^2|v|^2=\delta^3/15.
\tag{27.7}
$$

Since $t\le M^2$ and
$2q^2+s+\epsilon^2t^2\le2M^2$, its energy is at most

$$
\frac2\delta+\frac43M^2\delta+\frac2{15}t^2\delta^3
 \le2/d+\frac{52}{15}M\le C_*M.
\tag{27.8}
$$

For $n=0$ the two elementary solutions are
$\sinh(\omega(x+\ell_-))/\sinh(\omega\ell_-)$ and
$\sinh(\omega(\ell_+-x))/\sinh(\omega\ell_+)$.
Their outward derivatives give (27.3); their linear limits give
$A_0$. Finally, for fixed $\epsilon,s$, the inequalities
$|n|\le rM/\epsilon$ and
$|m|\le2|q|+2|c(h)||n|$ bound
$1+|m|+|n|$ by a fixed multiple of $M$. The reverse bound follows
from (27.1), using $\sqrt{|n|}\le1+|n|$.
This proves the fixed-parameter domain equivalences used above,
without changing their nonuniformity at zero noise. $\square$

## 28. Exact linear approximation rank and its noise crossover

**Theorem 28.1 (optimal complex-linear seam approximation).** For
$\eta>0$ let $d_\epsilon(\eta;s)$ be the minimum complex rank of a
bounded complex-linear $B:\mathscr K\to\mathscr K$ such that
$\|C_\epsilon(s)-B\|\le\eta$. Then

$$
d_\epsilon(\eta;s)
 =\#\{(m,n)\in\mathbb Z^2:(a_{mn}^\epsilon(s))^{-1}>\eta\}.
\tag{28.1}
$$

This is an exact count, with multiplicities in the original complex
Fourier basis. A mode with $(a_{mn}^\epsilon(s))^{-1}=\eta$ need
not be retained for this non-strict error contract. For the contract
$\|C_\epsilon(s)-B\|<\eta$, the exact count instead uses
$(a_{mn}^\epsilon(s))^{-1}\ge\eta$. No finite rank gives zero
error.

Fix $\epsilon_0\in(0,\infty)$ and $S_0\in[0,\infty)$, and set

$$
\eta_0=\frac1{4C_*(1+\sqrt{S_0})},\qquad
K_- =\frac{r}{32C_*^3},\qquad
K_+=\frac{5(1+\epsilon_0+4r)}{c_*^3}.
\tag{28.2}
$$

For all $0<\epsilon\le\epsilon_0$, $0\le s\le S_0$ and
$0<\eta\le\eta_0$,

$$
\frac{K_-}{\eta^2(\eta+\epsilon)}
 \le d_\epsilon(\eta;s)
 \le\frac{K_+}{\eta^2(\eta+\epsilon)}.
\tag{28.3}
$$

Thus the uniform sharp order is $\eta^{-3}$ when $\eta\ge\epsilon$
and $\epsilon^{-1}\eta^{-2}$ when $\eta\le\epsilon$, within this
tolerance range. Both bounds include $\eta=\epsilon$ and every
fixed comparable ratio. These are order bounds, not a leading
coefficient, and their constants depend only on $r,\ell_-,\ell_+$
and the displayed upper noise bound. The tolerance threshold also
depends on $S_0$. No Diophantine hypothesis on $c(h)$ is needed.

Proof. Theorem 27.1 makes $a_{mn}^\epsilon(s)\to\infty$ off finite
lattice sets, so $C_\epsilon(s)$ is compact, positive and diagonal
with eigenvalues $1/a_{mn}^\epsilon(s)$. Keep precisely those
eigenvalues greater than $\eta$, setting the rest to zero. This
bounded finite-rank operator attains error at most $\eta$.
Conversely a map of smaller rank has a nonzero kernel vector in
the span of the retained modes. On that finite-dimensional span
$\|C_\epsilon(s)v\|>\eta\|v\|$, contradicting the proposed error
bound on such a vector. This is the classical spectral-truncation
and rank-nullity argument, not an additional approximation mechanism.
Using the span with eigenvalues at least $\eta$ proves the lower
bound for strict error. Keeping that span gives strict error because
the compact positive diagonal has a largest omitted eigenvalue,
strictly below $\eta$. Every mode has positive eigenvalue, proving
the zero-error assertion.

For the upper count put $R=(c_*\eta)^{-1}\ge1$. By (27.2), a
mode counted in (28.1) must have

$$
|q|<R,\qquad |n|<r\min(R^2,R/\epsilon)
                \le\frac{2rR^2}{1+\epsilon R}.
\tag{28.4}
$$

There are at most $1+4rR^2/(1+\epsilon R)$ possible integers $n$.
For each of them the interval $|m/2+c(h)n|<R$ contains at most
$4R+1\le5R$ integers $m$, regardless of its translation.
Since $R\ge1$ and $\epsilon\le\epsilon_0$,
$1\le(1+\epsilon_0)R^2/(1+\epsilon R)$. Therefore

$$
d_\epsilon(\eta;s)
 \le5(1+\epsilon_0+4r)\frac{R^3}{1+\epsilon R}
 \le\frac{K_+}{\eta^2(\eta+\epsilon)}.
\tag{28.5}
$$

For the lower count put $L=(C_*\eta)^{-1}$ and
$T=rL^2/[16(1+\epsilon L)]$. The threshold (28.2) ensures
$L\ge4(1+\sqrt{S_0})$. Retain every integer $n$ with $|n|\le T$
and every integer $m$ with $|q|\le L/4$. For all these modes,

$$
1+\sqrt s\le L/4,\qquad \sqrt t\le L/4,\qquad
\epsilon t\le L/16,\qquad M\le13L/16<L.
\tag{28.6}
$$

Thus $a_{mn}^\epsilon(s)<C_*L=\eta^{-1}$, with a strict margin
even on the endpoints of the retained integer intervals.
There are $2\lfloor T\rfloor+1\ge T$ choices of $n$.
For each, the closed interval for $m$ has length $L$, hence at
least $L-1\ge L/2$ integer points. It follows that

$$
d_\epsilon(\eta;s)\ge\frac{rL^3}{32(1+\epsilon L)}
 \ge\frac{r}{32C_*^3\eta^2(\eta+\epsilon)}.
\tag{28.7}
$$

Here $C_*\ge1$, $c_*\le1$ justify the last rescalings in (28.5)
and (28.7). The shifts $c(h)n$ were retained in every integer
interval, including turning modes. $\square$

## 29. Native resolvent, raw unit-pole Green and clock correspondence

**Definition 29.1 (the exact consumer of the seam estimate).** Put
$R_\epsilon(s)=(L_\epsilon+s)^{-1}$ and
$R_{\epsilon,D}(s)=(L_{\epsilon,D}+s)^{-1}$. They exist also at
$s=0$: the height Dirichlet bound for the original operator is
$\pi^2/\ell^2$, and the slab bounds are at least this large.
For every $s\ge0$ the native correspondence is

$$
R_\epsilon(s)=R_{\epsilon,D}(s)
                       +P_sC_\epsilon(s)P_s^*.
\tag{29.1}
$$

This is the consumed common-trace resolvent formula of Olaf Post,
[*Boundary pairs associated with quadratic forms*,
arXiv:1210.4707v2](https://arxiv.org/pdf/1210.4707v2),
Theorem 4.3(ii) and Proposition 5.6(ii),(v), not a new general
gluing theorem. Its exact substitutions are boundary space
$\mathscr K$ with raw pairing, spectral variable $z=-s$, the two
slab forms with their outer Dirichlet data, common trace at $h$,
solution operator $P_s$, DtN operator $N_\epsilon(s)$ and decoupled
operator $L_{\epsilon,D}$. The common trace range $H^{1/2}$ is
dense in $\mathscr K$; Proposition 26.3 verifies the bounded
$L^2$ solution realization required for Post's elliptic regularity.
Both spectra exclude $-s$, including $s=0$. Thus the strong
$L^2$ formula, not merely a formal boundary identity, applies.

For the signs, the related elliptic coupling formulas in
Alpay–Behrndt, [arXiv:0807.0095v1](https://arxiv.org/pdf/0807.0095v1),
§4, (52)–(53), Theorem 4.4(ii), use the negative summed outward
flux $Q$. On smooth traces their convention corresponds to
$Q(-s)=-N_\epsilon(s)$, and their Dirichlet-minus-coupled resolvent
difference has the opposite sign to (29.1). Their whole-space
geometric hypotheses are not substituted for this periodic bounded
cylinder; Post's abstract form statement is the supplier used here.

For completeness, the variational correspondence can be checked
directly on the native domains. Given $F\in\mathscr H$, set
$u_D=R_{\epsilon,D}(s)F$, $g=C_\epsilon(s)P_s^*F$ and
$u=u_D+P_sg$. The first term has zero seam trace and the second
has the common trace $g\in D(N_\epsilon(s))\subset\mathscr T_s$;
hence $u$ belongs to the original unsplit form domain.
Every test $v$ in that domain decomposes as $v_D+P_s\gamma v$,
where $v_D$ has zero seam trace and $\gamma v\in\mathscr T_s$.
The harmonic equation gives zero cross terms with $v_D$ and
$u_D$. With $T_{\epsilon,s}=T_\epsilon+s\langle\cdot,\cdot\rangle$,

$$
\begin{aligned}
T_{\epsilon,s}(u,v)
 &=\langle F,v_D\rangle
       +\mathfrak n_s(g,\gamma v)\\
 &=\langle F,v_D\rangle+\langle P_s^*F,\gamma v\rangle_\Sigma
 =\langle F,v\rangle.
\end{aligned}
\tag{29.2}
$$

Coercivity proves (29.1) with its positive sign. In particular an
arbitrary complex $L^2$ seam forcing $f$ gives the analytic response
$g=C_\epsilon(s)f$, $P_sg$; it is not an acquired force, sensor
value, boundary actuator or admissible native action.

For every bounded complex-linear $B:\mathscr K\to\mathscr K$,
retaining the exact slab resolvents gives the uniform bulk bound

$$
\left\|R_\epsilon(s)
 -\bigl(R_{\epsilon,D}(s)+P_sBP_s^*\bigr)\right\|_{\mathscr H\to\mathscr H}
 \le\frac\ell3\|C_\epsilon(s)-B\|_{\mathscr K\to\mathscr K}.
\tag{29.3}
$$

This follows by factoring the difference and (26.5), for all
$s\ge0,\epsilon>0$. In particular the truncation in (28.1) gives
error at most $\ell\eta/3$ on the bulk unit ball. Neither (29.3)
nor (28.3) is a sharp bulk-rank bound: the exact slab inverses are
retained, and their ranks have not been replaced by zero or charged
to $d_\epsilon$.

Let $\Gamma_{\epsilon,D,o}$ be the raw unit-pole Green function in
the one slab containing $o$, extended by zero on the other slab.
Let $K_0(q,z)$ be the Poisson kernel of $P_0$ relative to
$d\sigma(z)$. All modal functions in (29.4)–(29.7) are taken at
$s=0$. Define the smooth seam function

$$
\begin{aligned}
f_o(z)&=\overline{K_0(o,z)}
       =\sum_{m,n}\phi_{mn}(k_o-h)
                    \overline{e_{mn}(\alpha_o,\beta_o)}e_{mn}(z)\\
 &=-\partial_{n_-}\Gamma_{\epsilon,D,o}|_{\Sigma,-}
   -\partial_{n_+}\Gamma_{\epsilon,D,o}|_{\Sigma,+}.
\end{aligned}
\tag{29.4}
$$

The unused slab has zero contribution. Then the original complete
Green field, with its original pole and raw normalization, is

$$
\Gamma_{\epsilon,o}(q)=\Gamma_{\epsilon,D,o}(q)
                              +(P_0C_\epsilon(0)f_o)(q).
\tag{29.5}
$$

Here $P_0^*\delta_o$ means precisely (29.4), not an application of
a bounded $L^2$ operator to an $L^2$ point mass. To justify its
regularity without a zero-noise trace assertion, fix $\epsilon>0$
and set $c_I=\max_{k\in[l,u]}|c(k)|$. On the whole height interval,

$$
(m/2+c(k)n)^2+\epsilon^2n^2/r^2
 \ge\kappa_\epsilon(m^2+n^2),\qquad
\kappa_\epsilon=\bigl[8+(8c_I^2+1)r^2/\epsilon^2\bigr]^{-1}>0.
\tag{29.6}
$$

Indeed $m^2\le8(m/2+c(k)n)^2+8c_I^2n^2$, while
$n^2\le r^2[(m/2+c(k)n)^2+\epsilon^2n^2/r^2]/\epsilon^2$.
Comparing the positive modal solution with the constant-potential
hyperbolic-sine solution shows, whenever
$\sqrt{\kappa_\epsilon(m^2+n^2)}\,d\ge(\log2)/2$,

$$
0\le\phi_{mn}(k_o-h)
 \le2\exp\bigl(-\sqrt{\kappa_\epsilon(m^2+n^2)}\,|k_o-h|\bigr).
\tag{29.7}
$$

For this comparison use the slab containing $o$ and its same two
endpoint values; the constant-potential solution is a supersolution
for (26.3). The stated threshold makes its denominator
$1-e^{-2\sqrt{\kappa_\epsilon(m^2+n^2)}\ell_\pm}$ at least $1/2$.
The positive pole-to-seam distance makes (29.4) smooth by absolute
convergence of all tangential derivatives. Division by $a_{mn}$
preserves this decay. The ODE, $0\le\phi\le1$, and its polynomial
coefficients bound each fixed-order height derivative by a polynomial
in $1+|m|+|n|$, so the harmonic correction is smooth on each closed
slab. For the first derivative this follows from a difference
quotient on a fixed half-interval and the bound on $\phi''=V\phi$;
higher derivatives follow by differentiating that ODE. These
smoothness bounds are for fixed positive $\epsilon$ and fixed
positive pole-to-seam distance, without a uniform zero-noise claim.

The one-dimensional Green identity with $\phi_{mn}$ gives exactly
the negative outward-derivative equality in (29.4). Indeed its
Dirichlet Green mode $G^D_{mn}(x,x_o)$ satisfies
$(-\partial_x^2+V_{mn})G^D_{mn}=\delta_{x_o}$; integrating against
$\phi_{mn}$ gives
$-\partial_nG^D_{mn}(0,x_o)=\phi_{mn}(x_o)$.
The raw torus delta is
$\sum e_{mn}(\alpha,\beta)\overline{e_{mn}(\alpha_o,\beta_o)}$,
so this also fixes every $2\pi$ factor in (29.4).
In (29.5) the traces agree across $h$, and the summed flux is
$-f_o+N_\epsilon(0)C_\epsilon(0)f_o=0$.
There is therefore no seam delta; the only source is the unchanged
raw unit delta at $o$, with zero outer data. This proves (29.5)
mode by mode and hence in distributions. Uniqueness of the inverse
of the positive Dirichlet operator identifies it with (1.5), and
with its smooth representative off the pole. Equivalently one can
apply (29.1) to smooth unit-mass sources supported near $o$ and
pass to their distributional limit. No point-pole approximation
error follows from the bulk norm bound (29.3).

Finally, for every $s>0$, the original semigroup satisfies

$$
R_\epsilon(s)=\int_0^\infty e^{-st}H_t^\epsilon\,dt.
\tag{29.8}
$$

The integral converges in operator norm by the height gap. Theorem
1.3 identifies this $H_t^\epsilon$ with the original covariance-$2$
killed path. Equation (29.1) for all $s>0$ reconstructs these very
Laplace transforms; uniqueness of the scalar Laplace transform of
the continuous bounded functions
$\langle H_t^\epsilon F,G\rangle$ determines the semigroup on the
original time parameter. For instance under $x=e^{-t}$, vanishing
transforms at all positive integers imply vanishing integrals
against all polynomials on $[0,1]$, then against all continuous
functions, proving scalar uniqueness; strong continuity removes
the exceptional times. No clock rescaling is present.

## 30. Source-specific content and the remaining realization bridges

**Definition 30.1 (supplier subtraction and contract).** Common-trace
coupling, addition of outward DtN forms and the resolvent correction
are the classical Post suppliers applied in (29.1)–(29.2), with the
Alpay–Behrndt sign correspondence stated there. The square completion,
one-dimensional trace estimate and spectral-truncation rank argument
are classical intermediates proved explicitly above. The additional
repository synthesis is the jointly uniform full-lattice bound
(27.2), its native translated-lattice count (28.3), and the exact
correspondence of that analytic seam to this cylinder's raw full
Green field and original-clock law. These are ordinary mathematical
results, with no worldwide-priority or Lean-certification claim.
Local anisotropic trace orders or fixed-noise elliptic estimates
alone do not supply their jointly uniform lattice count.

The internal suppliers in §§1–25 keep their stated source pins.
For the external repository consumers below use revision
`951f5e04989107543a170dfadab4674a99a5e0b6`; the three acquisition
and memory additions are instead read at
`fe080f1052e2c5800b8b005064522a0b75565754` as linked below.
These explicit correspondences specify the versions for §§26–30.

The named original-source consumer is Definition 25.1's missing
same-source analytic cut: (29.5) joins exact free slab responses to
the already specified unit-pole field, and (29.8) retains its path
law and clock. This does not replace Theorems 18.2–20.1's attractive
profile, Theorem 22.1's Hilbert chord floor or their actual-density
contracts. The seam result concerns bounded complex-linear spatial
response approximation; it is not the scalar autonomous temporal
rank of [Future Response, Theorem 57.7](RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md),
the acquired finite-report death certificates of [Paid-point
Tracking, §§60–65](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md),
or the fixed full-$H$ qutrit-channel stability of [Sharp Task,
Theorem 13.3](RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md).
A finite number of complex coefficients is a finite linear rank,
not a finite information capacity or a sensing-precision tariff.

The arithmetic acquisition-and-behavior-return results in
[Arithmetic Acquisition Return, §§10–12](https://github.com/the-omega-institute/trureturing/blob/fe080f1052e2c5800b8b005064522a0b75565754/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_ACQUISITION_RETURN.md),
the unknown-source acquisition in [Finite-start Predictive Memory,
§§19–22](https://github.com/the-omega-institute/trureturing/blob/fe080f1052e2c5800b8b005064522a0b75565754/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md),
and the initialized generated-law characterization in
[Self-generated Predictive Memory, §§17–20](https://github.com/the-omega-institute/trureturing/blob/fe080f1052e2c5800b8b005064522a0b75565754/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md)
retain their own sources, read interfaces and continuation contracts.
Their memory or arithmetic correspondences do not identify their
sources with the Brownian cylinder or grant this analytic seam an
acquisition/actuation service.

In particular (26.4) supplies no source sample, forcing right,
reset, copy, actual seam read or actuator. The original acquired
filtration, failures, holds, numerical command domains, native guards
and chronology $j=\int a_{\rm cmd}\,db_{\rm cmd}$ retain their
contracts. Every prefix keeps all four unhalved charges (6.1).
There is no additional primitive central command, no physical unit
identification and no selection of a spatial dimension by (28.3).
The unresolved full correspondence still requires physical spatial
realization and why-three selection; actual paid seam acquisition
and actuation with a whole-service resource map; a map from original
recursive occurrences to these analytic cuts; and attractive
spectral gluing with infinite-depth uniform stability. The free
positive-resolvent identities prove none of those additional premises.

## 追加锚（本行以下为增补区）

## 31. One lower face and the horizontal closed trace form

**Definition 31.1 (one-face data and energy closure).** Retain the
source, raw measures, fields and covariance-$2$ clock of §1. Write
$h_I=u-l$, $x=k-l$, $\theta=(\alpha,\beta)$, and identify the lower
face with $\mathscr K=L^2(\mathbb T^2,d\alpha\,d\beta;\mathbb C)$.
Here $h_I$ is the interval length, distinct from §26's seam height.
Allow $\epsilon=0$ by setting $\nu=0$ in (1.2), retaining the same
two Brownian controls and removing only the central Brownian term.
The upper-face trace is zero. Let $\mathcal V_\epsilon$ be the
closure of smooth periodic functions on $[l,u]\times\mathbb T^2$
vanishing at $u$, in the norm $(T_\epsilon+\|\cdot\|_2^2)^{1/2}$.
This uses horizontal energy at zero noise. Its exact modal description,
in the raw orthonormal basis (26.2), is

$$
\begin{aligned}
a&=m/2+c(l)n,&b&=n/r,&t&=|b|,\\
\mathcal V_\epsilon
 &=\left\{v:\ v_{mn}\in H^1(0,h_I),\ v_{mn}(h_I)=0,\right.\\
 &\hspace{16mm}\left.\sum_{m,n}\int_0^{h_I}
 \bigl(|v'_{mn}|^2+[1+(a-bx)^2+\epsilon^2b^2]|v_{mn}|^2\bigr)dx
 <\infty\right\}.
\end{aligned}
\tag{31.1}
$$

The trace $\gamma_l v=\sum v_{mn}(0)e_{mn}$ is defined in
$\mathscr K$; $\|\gamma_l v\|_2^2\le h_I\|Pv\|_2^2$.
The kernel of $\gamma_l$ is exactly $\mathcal F_\epsilon$ in (1.3).
Indeed finite Fourier truncation converges in (31.1), and each finite
collection is approximated in its one-dimensional $H^1$ norms by
smooth functions with the stated endpoint values. When both endpoint
values vanish, compact-height approximations give (1.3). This proves
the closure and kernel identifications also at $\epsilon=0$.
For positive noise $\mathcal V_\epsilon$ is periodic $H^1$ with
zero upper trace; no such isotropic identification is imposed at zero.
The height inequality $\|v\|_2^2\le h_I^2\|Pv\|_2^2/2$ holds on
$\mathcal V_\epsilon$ by integrating from its zero upper endpoint.

**Definition 31.2 (native one-face response).** For $s\ge0$ let
$\psi_{mn}$ minimize

$$
\lambda_{mn}^\epsilon(s)
 =\min_{\substack{v\in H^1(0,h_I)\\v(0)=1,\ v(h_I)=0}}
 \int_0^{h_I}\bigl(|v'|^2+[(a-bx)^2+\epsilon^2b^2+s]|v|^2\bigr)dx.
\tag{31.2}
$$

Thus $-\psi''+[(a-bx)^2+\epsilon^2b^2+s]\psi=0$,
$\psi(0)=1$, $\psi(h_I)=0$, and
$\lambda_{mn}^\epsilon(s)=-\psi'_{mn}(0)$.
Define the lower-face Poisson map and trace form by

$$
\begin{aligned}
\mathcal P_{\epsilon,s}g&=\sum g_{mn}\psi_{mn}(x)e_{mn}(\theta),\\
\mathcal T_{\epsilon,s}
 &=\{g\in\mathscr K:\ \sum\lambda_{mn}^\epsilon(s)|g_{mn}|^2<\infty\},\\
\mathfrak l_{\epsilon,s}(g,z)
 &=\sum\lambda_{mn}^\epsilon(s)g_{mn}\overline{z_{mn}},\\
D(\Lambda_\epsilon(s))
 &=\{g\in\mathscr K:\ \sum(\lambda_{mn}^\epsilon(s))^2|g_{mn}|^2<\infty\},\\
\Lambda_\epsilon(s)g&=\sum\lambda_{mn}^\epsilon(s)g_{mn}e_{mn},
\qquad \mathcal C_\epsilon(s)=\Lambda_\epsilon(s)^{-1}.
\end{aligned}
\tag{31.3}
$$

All pairings retain the complex convention of §26. These definitions
include the constant mode. They are the classical trace-energy and
associated-operator construction, here on the native modal closure;
see Arendt–ter Elst, [arXiv:1005.0875](https://arxiv.org/abs/1005.0875),
and the DtN framework surveyed by Girouard–Polterovich,
[arXiv:1411.6567](https://arxiv.org/abs/1411.6567). The native weights
and their zero-noise domains are specified by the following theorem.

## 32. Uniform one-sided mode energy, including every turning point

**Theorem 32.1 (native one-face energy and domains).** For every
$(m,n)\in\mathbb Z^2$, $s\ge0$ and $\epsilon\ge0$, put

$$
M_l=h_I^{-1}+\sqrt s+|a|+\sqrt t+\epsilon t,
\qquad c_l=1/37,\qquad C_l=2.
\tag{32.1}
$$

Then $c_lM_l\le\lambda_{mn}^\epsilon(s)\le C_lM_l$.
The constants are absolute; $r,l,h_I$ occur only in $M_l$.
There is no restriction on the slope $c(l)$ or on a turning point
$a-bx=0$. The form in (31.3) is densely defined and closed, with
the displayed positive selfadjoint operator. Moreover

$$
\begin{aligned}
\gamma_l\mathcal V_\epsilon&=\mathcal T_{\epsilon,s},\qquad
(T_\epsilon+s\|\cdot\|_2^2)[\mathcal P_{\epsilon,s}g]
 =\mathfrak l_{\epsilon,s}(g,g),\quad g\in\mathcal T_{\epsilon,s},\\
\|\mathcal P_{\epsilon,s}\|^2&\le h_I/3,\qquad
\|\mathcal C_\epsilon(s)\|
 =\bigl[\sqrt s\coth(h_I\sqrt s)\bigr]^{-1}\le h_I.
\end{aligned}
\tag{32.2}
$$

The continuous value of the square bracket at $s=0$ is $h_I^{-1}$.
For fixed positive $\epsilon$, the trace and operator domains are
$H^{1/2}(\mathbb T^2)$ and $H^1(\mathbb T^2)$, respectively.
At zero they are exactly the weighted domains in (31.3), with weights
$M_l$ and $M_l^2$, respectively, without an elliptic $H^1$ premise.
On $D(\Lambda_\epsilon(s))$ the weak lower outward conormal of the
lift is $-\partial_k\mathcal P_{\epsilon,s}g=\Lambda_\epsilon(s)g$.

Proof. Write $E$ for any competitor's energy in (31.2) and extend
it by zero beyond $h_I$. Cauchy–Schwarz gives $h_I^{-1}\le E$.
The half-line trace inequality
$1\le2\|v'\|_2\|v\|_2$, proved by integrating $(|v|^2)'$,
gives $E\ge\sqrt{s+\epsilon^2t^2}$. Thus both $\sqrt s$ and
$\epsilon t$ are at most $E$.
If $|a|\ge\sqrt t$ and $a\ne0$, use
$\delta=(2|a|)^{-1}$. On $[0,\delta]$ one has
$|a-bx|\ge|a|/2$. Averaging
$1\le2|v(x)|^2+2\delta E$ there gives
$1\le17E/|a|$, exactly by the local calculation (27.6).
The zero extension makes this valid even if $\delta>h_I$.
Consequently $|a|,\sqrt t\le17E$ in this case.
If $|a|<\sqrt t$, put $\delta=t^{-1/2}$. On
$[2\delta,3\delta]$, $|a-bx|\ge\sqrt t$ for either sign of $b$.
For every point of this interval,
$1\le2|v(x)|^2+6\delta E$. Its average gives
$1\le2E/(\delta t)+6\delta E=8E/\sqrt t$.
Hence $|a|,\sqrt t\le8E$. The remaining case $a=t=0$ is immediate.
Adding the five bounds gives $M_l\le37E$.

For the upper bound use the one-sided tent
$v(x)=(1-x/\delta)_+$ with $\delta=M_l^{-1}\le h_I$.
Its derivative, mass and second-moment integrals are
$\delta^{-1}$, $\delta/3$, $\delta^3/30$.
Using $(a-bx)^2\le2a^2+2t^2x^2$ and $t\le M_l^2$ gives

$$
E\le M_l+\frac{2a^2+s+\epsilon^2t^2}{3M_l}
               +\frac{t^2}{15M_l^3}
 \le\frac{26}{15}M_l<2M_l.
\tag{32.3}
$$

Minimization proves both bounds. The one-dimensional maximum principle
and convexity give $0\le\psi_{mn}(x)\le1-x/h_I$, so Parseval
proves the Poisson bound. Summing the modal minimum proves the energy
identity, the trace range and its minimizing property: any competitor
has at least that sum, and the modal lift attains it in (31.1).
The positive diagonal form is closed and gives precisely (31.3).
Integration by parts against any $v\in\mathcal V_\epsilon$ gives
$T_{\epsilon,s}(\mathcal P_{\epsilon,s}g,v)
=\mathfrak l_{\epsilon,s}(g,\gamma_l v)$, first for finite modes
and then by energy continuity. This defines the weak conormal.
For $n=0$ the exact solution is
$\sinh(\omega(h_I-x))/\sinh(\omega h_I)$,
$\omega=\sqrt{s+m^2/4}$, with its linear zero-frequency limit.
Every potential is at least $s$, so every modal minimum is at least
$\lambda_{00}^\epsilon(s)=\sqrt s\coth(h_I\sqrt s)$.
This proves the inverse norm, including its attained constant mode.
The fixed-positive-noise domain comparison follows as in Theorem 27.1
with $a=m/2+c(l)n$; at zero retain the actual weights. $\square$

## 33. One-face best rank through the zero-noise crossover

**Theorem 33.1 (uniform native boundary approximation capacity).** Let
$d^l_\epsilon(\eta;s)$ be the least complex rank among all bounded
complex-linear $B:\mathscr K\to\mathscr K$ with
$\|\mathcal C_\epsilon(s)-B\|\le\eta$. Then, for $\eta>0$,

$$
d^l_\epsilon(\eta;s)
 =\#\{(m,n):\lambda_{mn}^\epsilon(s)<\eta^{-1}\}.
\tag{33.1}
$$

For strict error $<\eta$ replace the inequality in this count by
$\lambda_{mn}^\epsilon(s)\le\eta^{-1}$. Both counts are finite;
no finite rank gives error zero. Fix $\epsilon_0\in[0,\infty)$,
$S_0\in[0,\infty)$ and define

$$
\begin{aligned}
\eta_l&=[4C_l\max(1,h_I^{-1}+\sqrt{S_0})]^{-1},\\
K_l^-&=r/(32C_l^3),\qquad
K_l^+=5(1+\epsilon_0+4r)/c_l^3.
\end{aligned}
\tag{33.2}
$$

For $0\le\epsilon\le\epsilon_0$, $0\le s\le S_0$ and
$0<\eta\le\eta_l$, including equality at the tolerance endpoints,

$$
\frac{K_l^-}{\eta^2(\eta+\epsilon)}
 \le d^l_\epsilon(\eta;s)
 \le\frac{K_l^+}{\eta^2(\eta+\epsilon)}.
\tag{33.3}
$$

The same order bounds hold for the strict-error count. The constants
have only the displayed $r,\epsilon_0$ dependence; the tolerance
threshold also depends on $h_I,S_0$. Neither a phase slope, a pole
nor a Diophantine condition enters them. At zero noise this is
$\eta^{-3}$; below the positive-noise scale it is
$\epsilon^{-1}\eta^{-2}$, as an order comparison of linear ranks.

Proof. Theorem 32.1 makes the inverse positive and compact, also
at zero noise. Apply the spectral-truncation and rank-nullity proof
of (28.1) to its actual eigenvalues; it covers every bounded
complex-linear approximant, with exactly the stated strictness.
For the lattice count use (28.4)–(28.7) with
$q=a$, $c_*=c_l$, $C_*=C_l$, and replace $1+\sqrt s$ by
$h_I^{-1}+\sqrt s$. The new threshold ensures
$L=(C_l\eta)^{-1}\ge4\max(1,h_I^{-1}+\sqrt{S_0})$.
Thus the same lower rectangle has $M_l\le13L/16<L$, while the
upper intervals have $R=(c_l\eta)^{-1}\ge1$ and
$|n|<2rR^2/(1+\epsilon R)$. These expressions and the integer
counts remain valid at $\epsilon=0$ without division by noise.
The strict lower margin also works for the strict-error contract;
closed upper intervals have the same $4R+1$ and
$1+4rR^2/(1+\epsilon R)$ bounds. This proves (33.3).
The count is derived from the native boundary energy, independently
of bulk volume growth. $\square$

## 34. The original killed source, its exit flux and the one-face inverse

**Theorem 34.1 (same-source conormal and Poisson correspondence).**
Let $R_\epsilon(s)=(L_\epsilon+s)^{-1}$ retain both original
Dirichlet faces, and let $\Gamma_{\epsilon,s,o}$ be its raw unit-pole
kernel. In particular $\Gamma_{\epsilon,0,o}=\Gamma_{\epsilon,o}$
in (1.5). For every $\epsilon,s\ge0$, its lower trace is zero,
whereas its negative outward conormal is the smooth boundary function

$$
\begin{aligned}
f^l_{\epsilon,s,o}(z)
 &:=-\partial_{n_l}\Gamma_{\epsilon,s,o}(z)
   =\sum_{m,n}\psi_{mn}(k_o-l)
                 \overline{e_{mn}(\theta_o)}e_{mn}(z),\\
(\mathcal P_{\epsilon,s}g)(o)
 &=\int_{\mathbb T^2}f^l_{\epsilon,s,o}(z)g(z)\,d\sigma(z),\\
\partial_{n_l}R_\epsilon(s)F&=-\mathcal P_{\epsilon,s}^*F,
\qquad F\in\mathscr H,\qquad \partial_{n_l}=-\partial_k.
\end{aligned}
\tag{34.1}
$$

For energy solutions conormal traces are defined by Green's identity
on the energy domains. For a unit pole use that identity distributionally
against smooth tests; the Fourier normal derivatives give precisely
this distribution, without a finite-energy assertion at the pole.
For positive noise these agree with the classical conormal traces.
The lower Poisson response uses the actual killed law:

$$
(\mathcal P_{\epsilon,s}g)(o)
 =\mathbb E_o[e^{-s\tau}g(q_\tau)\mathbf1_{\{k_\tau=l\}}].
\tag{34.2}
$$

For $g\in\mathscr K$ the right side is its boundary-density integral;
it is well defined for every fixed interior $o$. Write
$f^u_{\epsilon,s,o}=-\partial_k\Gamma_{\epsilon,s,o}|_{k=u}$
for the corresponding upper exit density. The actual lower and upper
discounted exit masses, without survival normalization, are

$$
\begin{aligned}
\int f^l_{\epsilon,s,o}\,d\sigma
 &=\frac{\sinh(\sqrt s(u-k_o))}{\sinh(\sqrt s h_I)},\\
\int f^u_{\epsilon,s,o}\,d\sigma
 &=\frac{\sinh(\sqrt s(k_o-l))}{\sinh(\sqrt s h_I)}.
\end{aligned}
\tag{34.3}
$$

At $s=0$ these are $(u-k_o)/h_I$ and $(k_o-l)/h_I$ and sum
to one. The constant boundary mode is retained, with inverse response
$\mathcal C_\epsilon(0)e_{00}=h_I e_{00}$.

Proof. Each Dirichlet Green mode $G_{mn}(x,y)$ solves
$(-\partial_x^2+V_{mn})G_{mn}(x,y)=\delta_y$ on $(0,h_I)$,
with zero endpoint values and
$V_{mn}=(a-bx)^2+\epsilon^2b^2+s$.
Integrating against $\psi_{mn}$ gives
$\partial_xG_{mn}(0,y)=\psi_{mn}(y)$, with positive sign.
The torus delta is $\sum e_{mn}(\theta)\overline{e_{mn}(\theta_o)}$,
fixing the raw normalization in (34.1). Mode pairing gives both
the Poisson kernel and $\partial_{n_l}R_\epsilon(s)F
=-\mathcal P_{\epsilon,s}^*F$. Alternatively the latter follows
from $T_{\epsilon,s}(R_\epsilon(s)F,\mathcal P_{\epsilon,s}g)=0$
and Green's identity. This defines its $L^2$ weak conormal for every
$F\in\mathscr H$, including at zero noise.

Here convergence at an interior pole can be justified without an
elliptic trace theorem. The nonnegative convex $\psi_{mn}$ is decreasing.
For $0<y<h_I$ put $N=|a|+ty$. There is an interval
$J\subset[0,y]$ of length $y/4$ on which $|a-bx|\ge N/24$.
If $|a|\ge2ty$ this holds on the whole interval with a stronger
constant. Otherwise the interval where $|a-bx|<ty/8$ has length
at most $y/4$, and one complementary component has length at least
$3y/8$; use any length-$y/4$ subinterval of it. The case $N=0$
is harmless. On $J$, compare $\psi$ with the constant-potential
solution having both endpoint values one. At its midpoint this gives
$\psi\le1/\cosh(Ny/192)$; monotonicity then yields

$$
0\le\psi_{mn}(y)\le2\exp[-y(|a|+ty)/192].
\tag{34.4}
$$

For each fixed $y>0$, $|a|+ty$ controls $|m|+|n|$ up to a
fixed geometry constant. Thus the series in (34.1), with every
tangential derivative, converges absolutely, uniformly in
$\epsilon,s\ge0$. It defines a smooth density and a bounded
evaluation functional on boundary $L^2$. The reality relation under
$(m,n)\mapsto(-m,-n)$ identifies it with the Poisson integral's
kernel rather than its complex conjugate. No $L^2$ point mass was
inserted into an $L^2$ adjoint.

For finite Fourier boundary data the lift is smooth and bounded on
the closed cylinder and solves $(L_\epsilon+s)v=0$. Itô's formula
for (1.2), stopped at $\tau$, gives (34.2). Its generator is
$-L_\epsilon$ also when $\nu=0$, and the height exit is almost
surely finite. Uniform approximation first extends the identity to
continuous data, establishing positivity of the smooth density;
its $L^2$ density then extends it to boundary $L^2$ data.
For the constant datum the exact zero mode is
$\psi_{00}(y)=\sinh(\sqrt s(h_I-y))/\sinh(\sqrt s h_I)$.
The upper datum gives the other mass in (34.3). At $s=0$ the
zero Green mode is
$\min(x,y)(h_I-\max(x,y))/h_I$; its height integral is
$y(h_I-y)/2$, exactly the original Green mass (1.6).
These computations retain all raw $2\pi$ factors and the original
covariance-$2$ time scale. $\square$

**Theorem 34.2 (what the inverse response reconstructs).** For
$f\in\mathscr K$, $w=\mathcal P_{\epsilon,s}\mathcal C_\epsilon(s)f$
is the unique member of $\mathcal V_\epsilon$ satisfying

$$
T_{\epsilon,s}(w,v)=\langle f,\gamma_l v\rangle_\Sigma
\quad(v\in\mathcal V_\epsilon).
\tag{34.5}
$$

Its lower trace is $\mathcal C_\epsilon(s)f$, its upper trace is
zero and its lower outward conormal is $f$. This is an analytic
forcing-family problem for the same differential expression. If
$A_{\epsilon,N}$ is the associated operator on $\mathcal V_\epsilon$
with natural lower condition and zero upper trace, then

$$
(A_{\epsilon,N}+s)^{-1}
 =R_\epsilon(s)+\mathcal P_{\epsilon,s}\mathcal C_\epsilon(s)
                                     \mathcal P_{\epsilon,s}^*.
\tag{34.6}
$$

In particular the original-pole field has the same-source identity
$\Gamma_{\epsilon,s,o}+\mathcal P_{\epsilon,s}\mathcal C_\epsilon(s)
f^l_{\epsilon,s,o}$ for this mixed Green kernel. Its lower flux
vanishes, since the original killed contribution has flux $-f^l$
and the harmonic correction has flux $+f^l$. The source remains
the same raw unit delta. The mixed realization is distinct from the
original process killed at both faces.

Proof. The trace identity in Theorem 32.1 and the coercive height
inequality prove (34.5) and uniqueness. Decompose every
$v\in\mathcal V_\epsilon$ as
$v_D+\mathcal P_{\epsilon,s}\gamma_l v$, with
$v_D\in\mathcal F_\epsilon$. The orthogonality and variational
calculation (29.2), now with only one trace, prove (34.6) with its
positive sign. This is the same classical Post form-resolvent
supplier already used in §29; (31.1) supplies the domains even at
zero noise. For a pole, the smooth $f^l$ in (34.1) and its modal
Green identity give the asserted distributional unit source and
boundary fluxes, without treating $\delta_o$ as $L^2$ data.
The killed resolvent itself remains
$\int_0^\infty e^{-st}H_t^\epsilon dt$ as in (29.8), on the
original clock; it has zero boundary value throughout.

Finally, continuous dependence in each scalar ODE gives
$\psi^\epsilon_{mn}\to\psi^0_{mn}$ and
$\lambda^\epsilon_{mn}\to\lambda^0_{mn}$ as $\epsilon\downarrow0$.
The uniform Poisson and inverse bounds in (32.2) give strong
convergence of those operators by Fourier truncation. The same
argument for the Dirichlet mode inverses uses the fixed height gap.
Equation (34.4) gives convergence of every fixed-pole exit density
in each tangential smooth norm. These are direct horizontal-domain
extensions, without a uniform elliptic $H^1$ assumption. $\square$

## 35. Boundary-family contract and dimensional scope

**Definition 35.1 (linear capacity and correspondence limits).** The
input family of (33.3) is the entire complex $L^2$ unit ball of
lower conormal forcings; the output is its lower $L^2$ trace under
$\mathcal C_\epsilon(s)$, with raw surface measure, fixed geometry
and the declared resolvent range. The approximation is by arbitrary
bounded complex-linear maps in the operator norm. Its cubic
zero-noise rank order and quadratic positive-noise order quantify
that analytic family. They specify neither finite-bit acquisition
nor a physical spatial dimension. A single fixed pole supplies one
particular smooth $f^l$ in this family after normalization, and the
family rank lower bound is not a lower bound for that one datum.
The internal-seam identity (29.1) reconstructs the original killed
resolvent; the one-face identity (34.6) instead compares it with a
different lower-boundary realization. Neither installs native forcing,
measurement, reset or actuation. The original command, filtration,
four unhalved charges and law/clock contracts in §30 remain in force.
Infinite recursive gluing, attractive spectral stability, physical
realization and why-three selection require their additional stated
bridges. Classical trace/DtN, best-rank and resolvent tools are the
intermediates cited in §§26–31; the native one-sided uniform energy,
its full-lattice zero-noise composition and the unchanged-source exit
correspondence are the mathematical synthesis here. No global
priority or Lean certification is asserted.

## 追加锚（本行以下为增补区）
