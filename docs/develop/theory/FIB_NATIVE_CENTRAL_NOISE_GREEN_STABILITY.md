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
