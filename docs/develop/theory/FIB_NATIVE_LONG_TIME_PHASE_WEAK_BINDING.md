# Native full-state weak binding on the three-real-phase cover

## 70. A fixed cutoff threshold interaction

**Definition 70.1 (fixed interaction and admissible states).** Let L denote
[Native long-time phase diffusion](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md)
and G denote [Native two-control Green stability](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md).
Retain exactly L Definition 35.1 and G Definition 25.1. Fix one admissible
signed $\kappa\ne0$, the pole $(k_0,0)$, and numbers $a>0$ and $\tau>0$.
Every limit below varies only $g>0$. Write $M=M_\kappa$, $\phi_0=\phi(k_0)$,
$d(q)=\sqrt{q^{\mathsf T}M^{-1}q}$ and $S=B_\kappa-\lambda\ge0$.
The Hilbert space is the complex space $\mathcal H=L^2(I\times\mathbb R^3,dk\,dq)$.
Its entire native form domain $\mathcal Q=D(S^{1/2})$ is L (48.2), with
both actual height Dirichlet faces and every real phase frequency.
Set

$$
F(t;k,q)=e^{\lambda t}g_\kappa^I(t;k_0,k;q),\qquad
W_\tau(k,q)=\int_\tau^\infty F(t;k,q)\,dt,
\qquad T[\psi]=\|S^{1/2}\psi\|_2^2,
\tag{70.1}
$$

$$
V_\tau[\psi]=\int W_\tau|\psi|^2\,dk\,dq,\qquad
\mathfrak e_g[\psi]=aT[\psi]-gV_\tau[\psi],\qquad
E_\tau(g)=\inf_{\psi\in\mathcal Q,\ \|\psi\|_2=1}\mathfrak e_g[\psi].
\tag{70.2}
$$

Thus the changed interaction is a positive-time-regularized threshold
field. It is neither the original killed Green nor the unregularized
point field. Its heat clock is that of $B_\kappa$, independently of $a$.

**Proposition 70.2 (field, source, domains and compactness).** There are
constants depending on the fixed data, including $\tau$, such that

$$
0\le W_\tau(k,q)\le\frac{C_\tau\phi_0\phi(k)}{1+|q|},\qquad
W_\tau(k,q)=\frac{\phi_0\phi(k)}{4\pi\sqrt{\det M}\,d(q)}
                  +O(\phi_0\phi(k)|q|^{-3})\quad(|q|\to\infty).
\tag{70.3}
$$

The error is uniform in height. In distributions, its exact source is

$$
SW_\tau=\rho_\tau:=F(\tau;\cdot),\qquad
\int\rho_\tau\,dk\,dq=e^{\lambda\tau}\mathbb P_{k_0}(\zeta>\tau),
\qquad \int\phi(k)\rho_\tau(k,q)\,dk\,dq=\phi_0.
\tag{70.4}
$$

The bounded multiplier $W_\tau$ is compact from $\mathcal Q$, with its
form norm, to $\mathcal H$; the same holds for $W_\tau^{1/2}$.
The form (70.2) is closed and bounded below on precisely $\mathcal Q$.
Its selfadjoint operator is $H_g=aS-gW_\tau$ on precisely $D(S)$,
with the direct-integral operator domain of L §48. Moreover
$\sigma(S)=\sigma_{\rm ess}(S)=[0,\infty)$ and
$\sigma_{\rm ess}(H_g)=[0,\infty)$.

Proof. Integrate the first two bounds of L Lemma 41.2 from the fixed
positive time $\tau$. On bounded $q$ the integral is bounded by
$C_\tau\phi_0\phi(k)$. On $|q|\ge1$ the integral over a bounded time
interval has Gaussian decay, and
$\int_1^\infty t^{-3/2}e^{-c|q|^2/t}dt\le C/|q|$.
L Theorem 42.1 gives the tail in (70.3): removing the interval
$(0,\tau)$ changes its large-$q$ value by an exponentially decaying
quantity, by those same heat bounds. In particular no singular point
value of the unregularized field was used.

The heat equation $\partial_tF=-SF$ and the large-time bound of L (41.2)
give the distributional equation in (70.4) by integration against a
compactly supported smooth test function. Integrating the phase heat
kernel leaves the killed height heat kernel. Its total mass is the
survival probability; pairing it with the height eigenfunction gives
$e^{-\lambda\tau}\phi_0$. This proves both source charges. They are
different charges. The factor $(2\pi)^{-3}$ in L (36.5) is already
included in $4\pi\sqrt{\det M}$ in (70.3). The field itself is not an
$L^2$ vector: its nonzero $|q|^{-1}$ tail has infinite squared integral.
Equation (70.4) is not an assertion that it lies in $D(S)$.

Here is the needed local compactness on the full native domain.
G (26.6), including its complex-test version, and the height part of the
form give, with the unitary phase Fourier transform,

$$
\int_{\mathbb R^3}\Psi(|\eta|)\|\widehat\psi(\eta)\|_{L^2(I)}^2d\eta
 \le CT[\psi],\qquad
\varepsilon^2\|\partial_k\psi\|_2^2\le T[\psi]+\lambda\|\psi\|_2^2,
\tag{70.5}
$$

where $\Psi(r)=r^2$ for $r\le1$ and $r^{2/3}$ for $r\ge1$.
Consequently a bounded set in $\mathcal Q$ is bounded in phase
$H^{1/3}$ and height $H_0^1$. On a bounded phase set its restriction is
precompact in $L^2$: after a smooth spatial cutoff, height translations
are uniformly small by the derivative bound and phase translations by
the fractional Fourier bound. Zero extension in height is allowed by
the Dirichlet trace. The supports are bounded, so the
Fréchet--Kolmogorov compactness criterion applies. This also proves the
claim for restrictions approaching the height faces. Multiplication by
a bounded compactly supported function is therefore compact from
$\mathcal Q$ to $\mathcal H$. Uniform decay in (70.3) approximates
$W_\tau$ and $W_\tau^{1/2}$ in multiplier norm by such functions.
Bounded selfadjoint perturbation and the form representation theorem
now give the stated form and operator domains, without any additional
phase $H^1$ requirement.

For the essential-spectrum statement, the bottom fibre eigenvalue
$\Lambda(re)-\lambda$ is continuous in $r\ge0$, starts at zero and
tends to infinity by G (26.6), for any fixed unit vector $e$.
For any prescribed $\mu\ge0$ choose $\eta_0$ with
$\Lambda(\eta_0)-\lambda=\mu$ and its normalized height eigenfunction
$v_{\eta_0}$. If $\chi\in C_c^\infty(\mathbb R^3)$ is normalized, then
$v_{\eta_0}(k)R^{-3/2}\chi(q/R)e^{i\eta_0\cdot q}$ is in $D(S)$,
tends weakly to zero and has $(S-\mu)$ norm $O(R^{-1})+O(R^{-2})$.
This follows by differentiating only the phase cutoff, since all
coefficients are bounded on $I$. These are Weyl sequences for every
$\mu\ge0$; nonnegativity excludes negative spectrum. Finally the
compactness just proved makes $W_\tau^{1/2}(S+1)^{-1/2}$ compact.
The resolvent identity and Weyl's compact-perturbation theorem give the
same essential spectrum for $H_g$. These are classical spectral and
compactness tools used here after verifying their native hypotheses.
$\square$

## 71. A multiplier estimate on the entire native form domain

**Proposition 71.1 (low-band extraction with a controlled remainder).**
Let

$$
\overline W(q)=\int_I\phi(k)^2W_\tau(k,q)\,dk,\qquad
J_3=\int_I\phi(k)^3dk,\qquad
\beta=\frac{\phi_0J_3}{4\pi\sqrt{\det M}}>0,
\qquad U(z)=\frac{\beta}{d(z)}.
\tag{71.1}
$$

There are fixed $\delta_0>0$ and $C$ such that, for every
$0<\delta\le\delta_0$ and every complex $\psi\in\mathcal Q$, one can
write $\psi=J_\delta f+r$ as an orthogonal spectral decomposition with

$$
\begin{aligned}
\|\psi\|_2^2&=\|f\|_2^2+\|r\|_2^2,&
\|r\|_2^2&\le C\delta^{-2}T[\psi],\\
K[f]&:=\int(\nabla f)^*M\nabla f\,dq\le CT[\psi],&
T[\psi]&\ge(1-C\delta^2)K[f]+T[r],\\
\|J_\delta f-\phi f\|_2&\le C\delta\sqrt{T[\psi]},&
\left|V_\tau[\psi]-\int\overline W|f|^2dq\right|
 &\le C\delta^{-2}T[\psi].
\end{aligned}
\tag{71.2}
$$

Here $f\in H^1(\mathbb R^3)$ has Fourier support in $|\eta|\le\delta$.
For normalized $\psi$ one also has

$$
V_\tau[\psi]\le C\sqrt{T[\psi]}+C\delta^{-2}T[\psi].
\tag{71.3}
$$

Proof. Use throughout the unitary version of L (36.5), namely its raw
transform multiplied by $(2\pi)^{-3/2}$. For $|\eta|\le\delta_0$ let
$v_\eta$ be the positive normalized first fibre eigenfunction of L §36.
Define $\widehat f(\eta)=\mathbf1_{|\eta|\le\delta}
\langle v_\eta,\widehat\psi(\eta)\rangle_{L^2(I)}$ and define
$J_\delta f$ by Fourier transform $v_\eta\widehat f(\eta)$
on the ball and zero outside it.
The remainder is the orthogonal complement of this decomposable
spectral projection, so the norm and kinetic energies split exactly.
On the low-frequency excited subspace the shifted fibre spectrum is
at least $3\lambda$ by min-max. On $|\eta|>\delta$, G (26.6) bounds
it below by $c\delta^2$. These facts give the remainder estimate.
L (36.4), positivity of $M$ and a fixed small $\delta_0$ give both
kinetic inequalities in (71.2). The estimate
$\|v_\eta-\phi\|_2\le C|\eta|^2$ from L (36.7) gives
$\|J_\delta f-\phi f\|_2^2\le C\delta^2K[f]$.

For clarity, Hardy's inequality is used only on these extracted
phase-$H^1$ functions. Its usual three-dimensional statement, applied
also to $L^2(I)$-valued functions by integration in height, is
$\||q|^{-1}h\|_2\le2\|\nabla_qh\|_2$.
It follows directly by integrating
$\operatorname{div}(q/|q|^2)=|q|^{-2}$ and applying Cauchy--Schwarz,
first on smooth functions away from zero and then by density.
By (70.3), Plancherel and (71.2),

$$
\|W_\tau J_\delta f\|_2+\|W_\tau\phi f\|_2
 \le C\sqrt{T[\psi]}.
\tag{71.4}
$$

The cross potential with $r$ is bounded by
$C\sqrt{T[\psi]}\|r\|_2\le C\delta^{-1}T[\psi]$;
its diagonal potential is at most $\|W_\tau\|_\infty\|r\|_2^2$.
Replacing $J_\delta f$ by $\phi f$ in its own potential changes that
potential by at most $C\sqrt{T[\psi]}\|J_\delta f-\phi f\|_2$,
using (71.4) on each term of the difference of quadratic forms.
This proves the last estimate in (71.2).
Finally $\overline W\le C/(1+|q|)$, and Hardy followed by
Cauchy--Schwarz gives
$\int\overline W|f|^2\le C\|f\|_2\|\nabla f\|_2$.
For normalized $\psi$ this proves (71.3). No estimate has asserted
that the original $\psi$ has all phase derivatives in $L^2$.
$\square$

**Proposition 71.2 (uniform rescaled potential comparison).** Put
$U_g(z)=g^{-1}\overline W(z/g)$. On every bounded subset of
$H^1(\mathbb R^3)$,

$$
\sup_h\left|\int(U_g-U)|h|^2dz\right|\longrightarrow0
\quad(g\downarrow0).
\tag{71.5}
$$

Proof. Formula (70.3), integrated against the actual height density
$\phi^2$, gives $\overline W(q)=\beta/d(q)+O(|q|^{-3})$ at infinity.
Thus $U_g\to U$ uniformly on every compact annulus away from zero.
Both $U_g$ and $U$ are bounded by $C/|z|$, since
$U_g(z)\le C/(g+|z|)$ and $d(z)\asymp|z|$.
For a ball of radius $b$, Hardy gives
$\int_{|z|<b}|h|^2/|z|\le4b\|\nabla h\|_2^2$.
Outside a ball of radius $R$ the integral is at most $R^{-1}\|h\|_2^2$.
On the intermediate annulus use uniform convergence. Let first
$g\downarrow0$, then $b\downarrow0$ and $R\to\infty$.
This proves (71.5) without a tightness hypothesis. $\square$

## 72. Negative attainment and the exact weak-coupling energy

**Theorem 72.1 (full-state weak binding).** With precisely the fixed data
of Definition 70.1, $-\infty<E_\tau(g)<0$ for every $g>0$.
It is attained by a normalized vector in $D(S)$, and

$$
\lim_{g\downarrow0}\frac{E_\tau(g)}{g^2}
 =e_*=-\frac{\beta^2}{4a}
 =-\frac{\phi(k_0)^2\left(\int_I\phi^3dk\right)^2}
             {64\pi^2a\det M}.
\tag{72.1}
$$

The limiting Coulomb operator, relative to raw $dz$, is the form
operator on $H^1(\mathbb R^3)$

$$
H_{\rm C}=-a\nabla_z\cdot M\nabla_z-\frac{\beta}{d(z)}.
\tag{72.2}
$$

Proof. Boundedness of $W_\tau$ gives the finite lower bound. For a
normalized smooth $h$ supported in an annulus, set
$\psi_R(k,q)=\phi(k)R^{-3/2}h(q/R)$. This lies in the full native
domain, and its exact kinetic energy is $R^{-2}K[h]$.
By (70.3) its potential energy is
$R^{-1}\int U|h|^2+o(R^{-1})$, with positive leading coefficient.
For every fixed $g>0$, large $R$ therefore gives negative energy.
Proposition 70.2 makes every spectral point below zero discrete;
the finite negative bottom is consequently an eigenvalue in $D(S)$.

The mature scalar Coulomb calculation used here is the square identity
in [H3](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md)
(82.4), with its Lebesgue normalization, as an intermediate only.
Indeed $z=M^{1/2}y$, with the unitary change
$h(z)=(\det M)^{-1/4}u(y)$, turns (72.2) into
$-a\Delta_y-\beta/|y|$. With $\rho=\beta/(2a)$ its form satisfies

$$
 a\|\nabla u\|_2^2-\beta\int\frac{|u|^2}{|y|}dy
       +a\rho^2\|u\|_2^2
 =a\left\|\nabla u+\rho\frac{y}{|y|}u\right\|_2^2.
\tag{72.3}
$$

Hardy controls the form and density justifies integration by parts for
all complex $H^1$ functions. Thus its normalized minimum is $e_*$,
attained only up to a constant complex phase by

$$
h_*(z)=(\det M)^{-1/4}\left(\frac{\rho^3}{\pi}\right)^{1/2}
                      e^{-\rho d(z)}.
\tag{72.4}
$$

Equality in (72.3) forces $e^{\rho|y|}u$ to have zero weak gradient
locally, hence to be constant on connected $\mathbb R^3$.

For the variational upper limit take
$\psi_g(k,q)=\phi(k)g^{3/2}h_*(gq)$.
Its exact kinetic energy is $g^2K[h_*]$. Proposition 71.2 gives
$gV_\tau[\psi_g]=g^2\int U|h_*|^2+o(g^2)$, so
$\limsup E_\tau(g)/g^2\le e_*<0$.

For the lower direction first establish an estimate applying to every
normalized native state with $\mathfrak e_g[\psi]\le0$.
Use (71.3) with a fixed $\delta=\delta_0$ to get
$0\ge(a-Cg)T[\psi]-Cg\sqrt{T[\psi]}$.
For all sufficiently small $g$ this implies $T[\psi]\le Cg^2$.
This is an estimate on the entire form domain.
Now use (71.2) with $\delta=g^{1/4}$ and define
$h_g(z)=g^{-3/2}f(z/g)$. Then

$$
\|h_g\|_2^2=1+O(g^2\delta^{-2}),\qquad K[h_g]\le C,
\qquad
\frac{\mathfrak e_g[\psi]}{g^2}
 \ge a(1-C\delta^2)K[h_g]-\int U_g|h_g|^2dz
                   -C g\delta^{-2}.
\tag{72.5}
$$

The norm error is nonpositive before the $O$ notation.
The final error tends to zero. Proposition 71.2 and (72.3) give a
lower bound $e_*\|h_g\|_2^2-o(1)=e_*-o(1)$.
Apply this to the attained ground states, which have negative energy.
Together with the upper limit this proves (72.1), including its full
variational lower direction. Neither a new effective-model hypothesis
nor a restriction of the native admissible class has been made.
$\square$

## 73. Every near-minimizer has the same macroscopic profile

**Theorem 73.1 (band collapse, phase profile and tightness).** Suppose
$\psi_g\in\mathcal Q$ is complex, $\|\psi_g\|_2=1$, and

$$
\mathfrak e_g[\psi_g]-E_\tau(g)=o(g^2),\qquad g\downarrow0.
\tag{73.1}
$$

There exist numbers $\theta_g\in\mathbb R$ such that

$$
\left\|g^{-3/2}\psi_g(k,z/g)
             -e^{i\theta_g}\phi(k)h_*(z)\right\|_{L^2(dk\,dz)}
 \longrightarrow0.
\tag{73.2}
$$

In particular $T[\psi_g]=O(g^2)$,
$\|(1-P)\psi_g\|_2^2=O(g^2)$ for the actual height projection
$P=|\phi\rangle\langle\phi|$, and the rescaled states are tight about
the fixed source:

$$
\lim_{R\to\infty}\limsup_{g\downarrow0}
 \int_{|gq|>R}|\psi_g(k,q)|^2dk\,dq=0.
\tag{73.3}
$$

No translating centres are required. The conclusion includes every
choice of normalized ground states and allows a varying constant
complex phase.

Proof. Theorem 72.1 makes the energies in (73.1) negative for small
$g$, so its a priori estimate gives $T[\psi_g]=O(g^2)$.
The height gap $H_I-\lambda\ge3\lambda(1-P)$, and nonnegativity of
the phase potential in every fibre, give the asserted height estimate.
Extract $f_g,r_g$ by Proposition 71.1 with $\delta=g^{1/4}$ and
rescale $f_g$ to $h_g$ as in (72.5).
Then $\|h_g\|_2\to1$, $h_g$ is bounded in $H^1$, and (72.5),
(71.5), (72.1) and (73.1) show

$$
 aK[h_g]-\int U|h_g|^2\longrightarrow e_*.
\tag{73.4}
$$

To check compactness rather than assume it, take any subsequence.
A further subsequence converges weakly in $H^1$ to some $h$ and
strongly in $L^2$ on bounded sets. Its Coulomb integrals converge:
near zero use the $4b\|\nabla h_g\|_2^2$ estimate from Proposition
71.2, at infinity use $R^{-1}\|h_g\|_2^2$, and on the intervening
annulus use local strong convergence. Weak lower semicontinuity and
(73.4) give

$$
e_*\ge aK[h]-\int U|h|^2
       \ge e_*\|h\|_2^2\ge e_*.
\tag{73.5}
$$

Because $e_*<0$, equality forces $\|h\|_2=1$, strong $L^2$
convergence and $h=e^{i\theta}h_*$ by (72.3).
The convergence of energies and potential integrals then also forces
$K[h_g]\to K[h]$, hence strong $H^1$ convergence on this subsequence.
Every subsequence has this property. Choosing $\theta_g$ to be the
argument of $\langle h_*,h_g\rangle$, which is nonzero for small $g$,
gives $e^{-i\theta_g}h_g\to h_*$ in $H^1$ for the whole family.

Finally (71.2) gives
$\|r_g\|_2=O(g/\delta)$ and
$\|J_\delta f_g-\phi f_g\|_2=O(\delta g)$.
The rescaling in (73.2) is unitary, so both errors vanish in the full
$L^2$ norm. This proves (73.2). Its limit has unit mass and a fixed
centre; taking the tail of that fixed $L^2$ function proves (73.3).
$\square$

## 74. Source, coordinate and dimension boundaries

**Proposition 74.1 (scope of the variational bridge).** Theorems 72.1
and 73.1 retain the following distinctions. The coefficient $\beta$
uses the raw point-source field and the actual height density; it is
not obtained by replacing the source with a stationary height mixture.
The cutoff $\tau$ does not change $\beta$ but is essential to the
bounded-multiplier argument. There is no conclusion here with
$\tau=0$, on a wrapped threshold cover, on the actual frozen-$D$ zero
leaf, or uniformly as $\kappa\to0$.

For $\kappa\ne0$, let $J_\kappa=\operatorname{diag}(1,1,\kappa)$.
Under the original real lift $D=\kappa x$ the unitary transport of a
wavefunction and the transport of a unit-source kernel are different.
Here $W_\tau^{\rm orig}$ uses the same cutoff and clock, with unit
source relative to $dk\,d\theta\,dv\,dD$ on that real lift:

$$
\psi^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1/2}\psi(k,q),\qquad
W_\tau^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1}W_\tau(k,q).
\tag{74.1}
$$

Thus the multiplier unitarily equivalent to $W_\tau$ is
$|\kappa|W_\tau^{\rm orig}$; a unit-source original-coordinate
coupling is $g_{\rm orig}=|\kappa|g$. The transported tensor is
$J_\kappa M J_\kappa^{\mathsf T}$, with its signed cross terms.
The three coordinates in this theorem are real winding coordinates,
not a deduction of physical three-space or physical $SO(3)$.

Proof. The tail (70.3) is proportional to $\phi_0\phi(k)$.
Multiplication by the limiting density $\phi(k)^2dk$ produces exactly
$\phi_0\int\phi^3$, while (70.4) exhibits the distinct raw and
$\phi$-weighted source charges. A Q kernel would instead carry the
height factors of L Definition 41.1; the killed kernel would have the
additional factor $e^{-\lambda t}$. Neither replacement has occurred.
The fixed-time subtraction has Gaussian spatial decay, proving the
assertion about $\tau$ in $\beta$. At zero cutoff the local
unregularized point-field collapse supplied by G Theorem 3.1 is not
removed by the threshold shift: subtracting a constant from the
kinetic energy is bounded on normalized states, and the threshold
Green is at least the killed Green by positivity. The real-chart
concentration proof G (3.5)–(3.8) uses only a positive
small-time window and therefore applies on this real lift with its raw
source normalization. Thus that unregularized instability is compatible
with, and excluded from, the present result.

L §§39 and 44–45 distinguish the comparison $x$ coordinate at zero
from the actual frozen-$D$ leaf, and establish the logarithmic
threshold divergences on the actual two-real-phase leaf and the
hidden-periodic cover. A positive lower time cutoff does not remove
those large-time divergences. Hence the present finite threshold
multiplier cannot be transferred to those spaces by a parameter
substitution. Formula (74.1) is the absolute-Jacobian change of raw
measure; transporting the multiplication form gives its coupling
factor. L §§39–40 and 46 preserve the distinction between winding
covers, original observations and spatial interpretation.

The native ingredients consumed by the new variational inference are
G (26.6) for the full complex form domain, L §36 for the actual tensor,
low-band eigenfunctions and quartic error, L Lemma 41.2 and Theorem
42.1 for the cutoff field, and L §48 for the full direct-integral
domains. The new inference is (71.2)–(71.5), its full-domain lower
bound (72.5), and the near-minimizer compactness argument (73.5).
Hardy, local Rellich compactness, Weyl's theorem and the Coulomb square
identity are classical intermediate tools, not new standalone results.
No physical realization, observation/preparation/acquisition operation,
resource service, or literature-wide novelty conclusion follows from
these mathematical statements. $\square$

## 追加锚（本行以下为增补区）
