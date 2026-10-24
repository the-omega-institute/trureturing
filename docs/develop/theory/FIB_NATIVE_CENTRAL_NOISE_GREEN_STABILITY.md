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
