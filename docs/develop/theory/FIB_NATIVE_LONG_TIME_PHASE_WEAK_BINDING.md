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

## 75. Joint weak coupling and a shrinking positive time cutoff

**Definition 75.1 (unchanged native family).** Retain all the data of
Definition 70.1, in particular one fixed admissible signed $\kappa\ne0$,
the original rational vector $c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$ of
G (25.4), $I=(l,u)$, $k_0\in I$, $\varepsilon>0$, $a>0$, and the
all-real cover $\mathcal C=I\times\mathbb R^3$ with raw measure
$dY=dk\,dq$. Write $o=(k_0,0)$,
$B=B_\kappa=-\varepsilon^2\partial_k^2-(c_\kappa\cdot\partial_q)^2$
and $S=B-\lambda\ge0$. Both height endpoints remain Dirichlet.
The unitary phase Fourier transform has factor $(2\pi)^{-3/2}$.
The entire complex form domain is

$$
\mathcal Q=\left\{\psi\in L^2(dY):
\widehat\psi(\cdot,\eta)\in H_0^1(I)\text{ a.e.},\quad
\int_{\mathbb R^3}\int_I
\left(\varepsilon^2|\partial_k\widehat\psi|^2+
 |\eta\cdot c_\kappa(k)|^2|\widehat\psi|^2\right)dk\,d\eta<\infty
\right\}.
\tag{75.1}
$$

Thus $D(B^{1/2})=D(S^{1/2})=\mathcal Q$, and the integral in
(75.1) is $T[\psi]+\lambda\|\psi\|_2^2$. No phase $H^1$ condition
is imposed on $\psi$.
Let $p_t(Y,Z)$ denote the killed heat kernel of $B$ relative to $dZ$.
In the notation of (70.1), $F(t;Y)=e^{\lambda t}p_t(o,Y)$.
For $0<\tau\le1$ put

$$
D_\tau(Y)=W_\tau(Y)-W_1(Y)
       =\int_\tau^1e^{\lambda t}p_t(o,Y)dt,\qquad
\mathfrak e_{g,\tau}[\psi]=aT[\psi]-gV_\tau[\psi].
\tag{75.2}
$$

A joint family consists of $g\downarrow0$ and an arbitrary declared
function $\tau(g)>0$ with $\tau(g)\to0$. Its dimensionless comparison
parameter and energy are

$$
\chi(g)=g\tau(g)^{-3/2},\qquad
E_{\tau(g)}(g)=\inf_{\psi\in\mathcal Q,\ \|\psi\|_2=1}
                  \mathfrak e_{g,\tau(g)}[\psi].
\tag{75.3}
$$

The restriction $\tau\le1$ holds eventually in every such family;
there is no fixed positive lower bound on its cutoff. All constants
below may depend on the fixed native data, including $\kappa$ and
$a$, but not on $g$, $\tau\in(0,1]$, or the tested vector.
The heat clock remains $e^{-tB}$, without rescaling by $a$.

**Proposition 75.2 (source and pointwise fixed-cutoff properties).** For
every positive $\tau$, the source identities are still exactly

$$
SW_\tau=\rho_\tau=e^{\lambda\tau}p_\tau(o,\cdot),\qquad
\int\rho_\tau dY=e^{\lambda\tau}\mathbb P_{k_0}(\zeta>\tau),
\qquad \int\phi(k)\rho_\tau(k,q)dk\,dq=\phi(k_0).
\tag{75.4}
$$

The first charge tends to one as $\tau\downarrow0$; the second is
constant. For each fixed $g>0$ and $\tau>0$, Proposition 70.2 and
Theorem 72.1 apply on precisely $\mathcal Q$ and $D(S)$: the energy
is finite, negative and attained. These assertions do not assert
uniform boundedness of $W_\tau$ as $\tau\downarrow0$.

Proof. The identities are (70.4) at the specified positive time.
Integrating $p_t(o,Y)$ over the real phases leaves the killed height
heat kernel. Hence its raw mass is the survival probability of
$k_0+\sqrt2\varepsilon W_t^1$ in $I$, which tends to one at time
zero because $k_0$ is interior. Pairing instead with the eigenfunction
$\phi$ gives the different charge in (75.4). Boundedness and spatial
decay at each positive cutoff are the hypotheses used in Proposition
70.2 and Theorem 72.1 and remain true separately at every pair
$(g,\tau)$. Their existence conclusion is reused here. $\square$

## 76. Uniform control of the added short-time field

**Proposition 76.1 (all-height heat and killed-resolvent bounds).** There
are constants $C,c>0$ such that for every $Y,Z\in\mathcal C$,

$$
0\le p_t(Y,Z)\le
\begin{cases}
Ct^{-7/2},&0<t\le1,\\
Ce^{-\lambda t}t^{-3/2},&t\ge1.
\end{cases}
\tag{76.1}
$$

Consequently, for $0<\tau\le1$,

$$
\|W_\tau\|_\infty\le C\tau^{-5/2},\qquad
\int D_\tau dY\le C,\qquad
\|B^{-1}D_\tau\|_\infty\le C\tau^{-3/2}.
\tag{76.2}
$$

Here the last expression denotes the nonnegative killed-resolvent
integral. For every complex $u\in\mathcal Q$ it implies

$$
\int D_\tau|u|^2dY
 \le C\tau^{-3/2}\bigl(T[u]+\lambda\|u\|_2^2\bigr).
\tag{76.3}
$$

Proof. The all-height diagonal supplier is G (32.3)--(32.6) on the
real cover. Its hypotheses use the same coefficient vector and an
interval $J$ containing $\overline I$ with positive margins. In
particular

$$
\det(c_\kappa,c_\kappa',c_\kappa'')(k)
 =-\frac{H^2-\kappa^2}{2H^3(k-\alpha_\kappa)^3}\ne0
\tag{76.4}
$$

on that larger interval. The local expansion on $J$ is uniform for
centres $k\in[l,u]$; domination by its killed kernel bounds the kernel
on $I$, including heights approaching either absorbing face, by
$Ct^{-7/2}$ on the diagonal. Phase translation gives the same bound
at every phase. Semigroup contraction extends the bound from small
times to $0<t\le1$. Symmetry and the semigroup Cauchy--Schwarz
inequality give
$p_t(Y,Z)\le\sqrt{p_t(Y,Y)p_t(Z,Z)}$.
This proves the first line of (76.1), rather than inferring an
all-height estimate from an interior diagonal limit alone.
The second line is the large-time bound in L Lemma 41.2, after
removing its factor $e^{\lambda t}$ and bounding the height factors.
The first line of that lemma, whose power is $t^{-6}$, is not used
as a sharp short-time estimate.

Integration of (76.1) against $e^{\lambda t}$ proves the first
inequality of (76.2), since
$\int_\tau^1t^{-7/2}dt\le C\tau^{-5/2}$ and
$\int_1^\infty t^{-3/2}dt<\infty$.
The exact raw mass gives

$$
\int D_\tau dY
 =\int_\tau^1 e^{\lambda t}\mathbb P_{k_0}(\zeta>t)dt
 \le e^\lambda.
\tag{76.5}
$$

This uses the killed semigroup; it does not treat $F$ as a
conservative raw-measure transition density. By Tonelli, symmetry
and the semigroup identity, for $0<\tau<1$,

$$
\begin{aligned}
(B^{-1}D_\tau)(Y)
 &=\int_\tau^1e^{\lambda t}\int_0^\infty
                p_{t+s}(o,Y)ds\,dt\\
 &\le C\int_\tau^1(t^{-5/2}+1)dt
 \le C\tau^{-3/2}.
\end{aligned}
\tag{76.6}
$$

Indeed the inner integral from $t$ to one is bounded by
$C\int_t^1v^{-7/2}dv$, and the remaining killed large-time integral
is uniformly finite by (76.1).

For completeness, the classical weighted Schur test gives precisely
the form consequence needed here. The symmetric positive-kernel
operator $D_\tau^{1/2}B^{-1}D_\tau^{1/2}$ has Schur weight
$D_\tau^{1/2}$: its weighted row integral is
$D_\tau(Y)^{1/2}(B^{-1}D_\tau)(Y)$.
Thus its $L^2$ norm is at most the last bound in (76.2).
For $\tau<1$, positivity of the interior heat kernel makes the weight
positive; at $\tau=1$ the assertion is trivial.
Since $B\ge\lambda>0$, the squared norm of
$D_\tau^{1/2}B^{-1/2}$ is the norm of this Schur operator.
Applying it to $B^{1/2}u$ proves (76.3), also for complex functions.
All operators in this calculation use $B$, whose heat is killed and
sub-Markov, rather than assuming that the shifted heat of $S$ is
Markovian in raw measure. $\square$

**Proposition 76.2 (relative bound at the native threshold).** Uniformly
for $0<\tau\le1$ and every complex $\psi\in\mathcal Q$,

$$
0\le V_\tau[\psi]-V_1[\psi]
 =\int D_\tau|\psi|^2dY
 \le C\tau^{-3/2}T[\psi].
\tag{76.7}
$$

Proof. Fix once a small radius $\delta_0>0$ as in Proposition 71.1,
using there only its spectral and kinetic assertions, which depend
on $S$ and not on the cutoff. Write
$\psi=J_{\delta_0}f+r$ with exact norm and kinetic splitting.
There is a fixed $b_0>0$ such that

$$
T[r]\ge b_0\|r\|_2^2,\qquad
K[f]\le CT[J_{\delta_0}f],\qquad
\sup_{|\eta|\le\delta_0}\|v_\eta\|_{L^\infty(I)}\le C.
\tag{76.8}
$$

The gap follows from G (26.6) on frequencies outside the ball and
the excited height gap inside it. The eigenfunction bound follows
from L (36.7), including its boundary quotient estimate.
Cauchy--Schwarz in the actual three real Fourier variables gives

$$
\begin{aligned}
\|J_{\delta_0}f\|_\infty
 &\le C\int_{|\eta|\le\delta_0}|\widehat f(\eta)|d\eta\\
 &\le C\left(\int_{|\eta|\le\delta_0}|\eta|^{-2}d\eta\right)^{1/2}
          \left(\int|\eta|^2|\widehat f(\eta)|^2d\eta\right)^{1/2}
 \le C\sqrt{T[J_{\delta_0}f]}.
\end{aligned}
\tag{76.9}
$$

The integral of $|\eta|^{-2}$ is finite in dimension three, and
$M>0$ compares its last quadratic integral with $K[f]$.
Thus (76.5) bounds the $D_\tau$ form on $J_{\delta_0}f$ by
$CT[J_{\delta_0}f]$. On the remainder, (76.3) and its fixed gap give

$$
\int D_\tau|r|^2dY
 \le C\tau^{-3/2}(T[r]+\lambda\|r\|_2^2)
 \le C\tau^{-3/2}T[r].
\tag{76.10}
$$

Finally $|J_{\delta_0}f+r|^2\le2|J_{\delta_0}f|^2+2|r|^2$,
$\tau^{-3/2}\ge1$, and exact kinetic splitting prove (76.7).
The low-frequency bound was applied only to the extracted band.
The arbitrary native vector and its remainder were never assumed
to have all phase derivatives. This removes the additive
$\lambda\|\psi\|_2^2$ in (76.3), which by itself would be too large
for the quadratic weak-binding limit. $\square$

## 77. Persistence of the exact Coulomb energy and every profile

**Theorem 77.1 (joint full-domain persistence).** Let Definition 75.1
hold and assume $\tau(g)\to0$ and $\chi(g)\to0$. Then

$$
\frac{E_{\tau(g)}(g)}{g^2}\longrightarrow
 e_*=-\frac{\beta^2}{4a},\qquad
\beta=\frac{\phi(k_0)\int_I\phi^3dk}{4\pi\sqrt{\det M}}.
\tag{77.1}
$$

For every family of normalized complex $\psi_g\in\mathcal Q$ with

$$
\mathfrak e_{g,\tau(g)}[\psi_g]-E_{\tau(g)}(g)=o(g^2),
\tag{77.2}
$$

there are constant phases $\theta_g\in\mathbb R$ such that, with
$\rho=\beta/(2a)$ and the same function as (72.4),

$$
\begin{aligned}
h_*(z)&=(\det M)^{-1/4}(\rho^3/\pi)^{1/2}e^{-\rho d(z)},\\
\left\|g^{-3/2}\psi_g(k,z/g)-e^{i\theta_g}\phi(k)h_*(z)
                                      \right\|_{L^2(dk\,dz)}&\longrightarrow0.
\end{aligned}
\tag{77.3}
$$

Moreover, for the actual height projection $P=|\phi\rangle\langle\phi|$,

$$
T[\psi_g]=O(g^2),\qquad
\|(1-P)\psi_g\|_2^2=O(g^2),\qquad
\lim_{R\to\infty}\limsup_{g\downarrow0}
 \int_{|gq|>R}|\psi_g(k,q)|^2dk\,dq=0.
\tag{77.4}
$$

These conclusions include every normalized ground-state choice.
They require no translation of the fixed source.

Proof. The reference cutoff throughout this proof is exactly one.
By (76.7), for every $\psi\in\mathcal Q$,

$$
0\le\mathfrak e_{g,1}[\psi]-\mathfrak e_{g,\tau}[\psi]
 \le C\chi T[\psi].
\tag{77.5}
$$

Proposition 71.1 at cutoff one and a fixed band radius gives, for
normalized $\psi$, $V_1[\psi]\le C\sqrt{T[\psi]}+CT[\psi]$.
Consequently every normalized native vector of nonpositive joint
energy satisfies

$$
0\ge\mathfrak e_{g,\tau}[\psi]
 \ge(a-C\chi-Cg)T[\psi]-Cg\sqrt{T[\psi]}.
\tag{77.6}
$$

For $g$ and $\chi$ small enough, the coefficient of $T$ is at least
$a/2$, proving $T[\psi]\le Cg^2$ uniformly over all such vectors.
This estimate holds on the full complex domain (75.1).

Monotonicity $W_\tau\ge W_1$ gives $E_\tau(g)\le E_1(g)$.
Apply (77.6) to an attained joint ground state, whose existence and
negative energy are reused from Theorem 72.1 at its positive cutoff.
By (77.5) and the reference variational principle,

$$
E_1(g)-C\chi g^2\le E_\tau(g)\le E_1(g).
\tag{77.7}
$$

The fixed-cutoff conclusion $E_1(g)/g^2\to e_*$ of Theorem 72.1
therefore proves (77.1). The upper direction may also be realized
by the same admissible reference trials
$\phi(k)g^{3/2}h_*(gq)$: their reference energies are
$e_*g^2+o(g^2)$ and their joint energies are no larger.
Both the infimum comparison and the lower estimate use the whole
$\mathcal Q$, rather than a product-state restriction.

Now (77.1), (77.2) and $e_*<0$ make the joint energies of $\psi_g$
negative eventually. Thus (77.6) gives $T[\psi_g]=O(g^2)$, and
(77.5), (77.7) imply

$$
0\le\mathfrak e_{g,1}[\psi_g]-E_1(g)
 \le\mathfrak e_{g,\tau(g)}[\psi_g]-E_{\tau(g)}(g)
                      +C\chi(g)g^2=o(g^2).
\tag{77.8}
$$

Theorem 73.1 now applies directly to this same family on its entire
complex domain, with fixed $a$, source, tensor and reference cutoff
one. Its conclusions are exactly (77.3)--(77.4), including the
actual height projection, source-centred tightness and a single
constant complex phase for each vector. In particular no compactness
of a cutoff-dependent family of potential multipliers is being
assumed. The uniform replacement for it is (76.7). $\square$

**Proposition 77.2 (nonempty shrinking persistence families).** Every
power family $\tau(g)=g^p$ with $0<p<2/3$ satisfies Theorem 77.1.
More generally, $\tau(g)=g^{2/3}L(g)$ does so whenever
$L(g)>0$, $L(g)\to\infty$ and $g^{2/3}L(g)\to0$.
For example $L(g)=(\log(1/g))^r$ with any $r>0$ is allowed.

Proof. The respective values of $\chi$ are
$g^{1-3p/2}$ and $L(g)^{-3/2}$, which tend to zero under the
stated hypotheses; each cutoff stays positive and tends to zero.
$\square$

## 78. Microscopic admissible competitors in the same source chart

**Definition 78.1 (raw privileged scaling at the fixed pole).** Write
$c_j=c_\kappa^{(j)}(k_0)$ for $j=0,1,2$ and
$j_0=\varepsilon^4|\det(c_0,c_1,c_2)|>0$.
For $s>0$ and $\xi=(r,y,z,w)\in\mathbb R^4$ define

$$
\Xi_s(\xi)=\left(k_0+\varepsilon s r,
                 s c_0y+\varepsilon s^2c_1z+\varepsilon^2s^3c_2w\right).
\tag{78.1}
$$

Its absolute raw Jacobian is exactly $j_0s^7$.
Fix a nonzero $f\in C_c^\infty(\mathbb R^4\setminus\{0\})$,
normalized by $\int|f|^2d\xi=1$, and let $K$ be its compact support.
For all sufficiently small $s$ put

$$
\psi_s(\Xi_s(\xi))=j_0^{-1/2}s^{-7/2}f(\xi),
\tag{78.2}
$$

with zero extension outside the image of its compact support.
The support lies in an interior height chart for small $s$ and all
three phase coordinates are real.

**Proposition 78.2 (cutoff-matched concentration witnesses).** The
vectors (78.2) are normalized members of $C_c^\infty(\mathcal C)$,
hence of $\mathcal Q$. There are fixed $s_0,c_0',C_0>0$ such that
for $0<s<s_0$,

$$
T[\psi_s]\le C_0s^{-2},\qquad
V_{s^2}[\psi_s]\ge c_0's^{-5},\qquad
\mathfrak e_{g,s^2}[\psi_s]
       \le aC_0s^{-2}-c_0'gs^{-5}.
\tag{78.3}
$$

Proof. The normalization follows from the exact Jacobian, not a
stationary-height measure. Pulling back $s\varepsilon\partial_k$
and $s(c_\kappa(k)\cdot\partial_q)$ under (78.1) gives
$\partial_r$ and $v_s(r)\cdot\partial_{y,z,w}$, respectively, where
Taylor expansion in the basis $(c_0,c_1,c_2)$ gives

$$
v_s(r)\longrightarrow(1,r,r^2/2)
\quad\hbox{in }C^\infty\hbox{ on bounded }r\hbox{ intervals}.
\tag{78.4}
$$

The term $r^2/2$ is due to the second derivative in (78.1), whose
column has not been divided by two. The determinant (76.4) makes
the change of basis invertible. It follows exactly that

$$
T[\psi_s]+\lambda
 =s^{-2}\int\left(|\partial_rf|^2+
                   |v_s(r)\cdot\partial_{y,z,w}f|^2\right)d\xi
 \le C_0s^{-2}.
\tag{78.5}
$$

The support and smooth extension assertions follow from compact
support of $f$, the invertible linear phase map and $k_0\in I$.
The supports avoid the pole. Thus these are native admissible
microscopic states, rather than merely rescaled measures.

Here the local heat supplier is used only on a finite positive-time
window. Let $p_{\rm E}$ be the heat kernel relative to $d\xi$ of

$$
\partial_r^2+
 \left(\partial_y+r\partial_z+(r^2/2)\partial_w\right)^2
\quad\hbox{on }\mathbb R^4.
\tag{78.6}
$$

Theorem B, (2.8), of Colin de Verdière--Hillairet--Trélat,
*Small-time asymptotics of hypoelliptic heat kernels near the
diagonal, nilpotentization and related results*, Annales Henri
Lebesgue 4, 897--971,
[DOI 10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf),
together with its localization Theorem 3.2, gives in this chart

$$
j_0s^7p_{s^2t}(o,\Xi_s(\xi))
 \longrightarrow p_{\rm E}(t;0,\xi)
\quad\hbox{uniformly for }(t,\xi)\in[1,2]\times K.
\tag{78.7}
$$

These are the real-cover hypotheses already checked in G (3.2)--(3.5)
and (32.2)--(32.5): smooth original fields on a larger height
interval, positive smooth constant raw density, constant flag of
weights $(1,1,2,3)$ and bounded step three, zero drift and potential
for $B$, and selfadjoint contraction realizations. The pole is at
positive distance from both height faces. Theorem 3.2 compares the
identical expression and density on that interior chart and the
actual killed realization. The actual cover is already real, so no
periodic image sum is introduced. The rescaled density is
$j_0d\xi$ before converting to the Lebesgue kernel in (78.7);
this explains its factor $j_0$. Multiplication by the threshold
factor $e^{\lambda s^2t}\to1$ is uniform on this time window.

The two fields in (78.6) and their first two iterated brackets span
at every point. Their heat kernel is smooth and strictly positive;
this is the same tangent positivity used in G Theorem 3.1.
Thus its minimum on $[1,2]\times K$ is positive. With $\tau=s^2$,
positivity of the full threshold field and (78.7) give

$$
\begin{aligned}
W_{s^2}(\Xi_s(\xi))
 &\ge\int_{s^2}^{2s^2}e^{\lambda t}p_t(o,\Xi_s(\xi))dt\\
 &\ge c s^{-5}\qquad(\xi\in K).
\end{aligned}
\tag{78.8}
$$

Normalization then gives the potential inequality in (78.3).
This is a lower bound on the full $W_{s^2}$ from a retained window;
no infinite-time Green limit follows from, or is required of,
(78.7). The factor $a$ multiplies the kinetic energy only after this
same-clock calculation. $\square$

## 79. Genuine failure of the quadratic law for faster shrinking

**Theorem 79.1 (microscopic energy order and divergence).** Suppose
$g\downarrow0$, $\tau(g)\to0$ and $\chi(g)\to\infty$.
There are constants $c,C>0$ such that eventually

$$
-Cg\tau(g)^{-5/2}\le E_{\tau(g)}(g)
                  \le-cg\tau(g)^{-5/2}.
\tag{79.1}
$$

In particular

$$
E_{\tau(g)}(g)\longrightarrow-\infty,\qquad
\frac{E_{\tau(g)}(g)}{g^2}\longrightarrow-\infty.
\tag{79.2}
$$

This contradicts the quadratic Coulomb energy law in this regime
by actual admissible competitors, while each positive-cutoff
problem remains separately bounded below and attained.

Proof. Take $s=\sqrt{\tau(g)}$ in Proposition 78.2. Its normalized
native vector has energy at most

$$
\tau(g)^{-1}\bigl(aC_0-c_0'\chi(g)\bigr).
\tag{79.3}
$$

Once $\chi(g)\ge2aC_0/c_0'$, this is at most
$-(c_0'/2)g\tau(g)^{-5/2}$, giving the upper bound in (79.1).
The independent full-domain lower bound follows from $T\ge0$ and
$\|W_\tau\|_\infty\le C\tau^{-5/2}$ in (76.2).
Since $g\tau^{-5/2}=\chi/\tau\to\infty$, the first limit in
(79.2) follows. Dividing the upper bound by $g^2$ gives
$-c\tau^{-5/2}/g\to-\infty$, proving the second.
Only the order in (79.1) is identified; its bounds do not identify
an exact microscopic coefficient or a microscopic ground profile.
The witness proves a variational upper direction, and the matching
lower order uses the separate all-height heat estimate. Failure of
a sufficient smallness estimate alone was not used as a
counterexample. $\square$

**Proposition 79.2 (explicit faster families and the remaining range).**
Every family $\tau(g)=g^p$ with $p>2/3$ satisfies Theorem 79.1;
its energy has the two-sided order $-g^{1-5p/2}$.
The families $\tau(g)=g^{2/3}L(g)$ with $L(g)>0$ and $L(g)\to0$
also satisfy that theorem. An example is
$L(g)=(\log(1/g))^{-r}$ with $r>0$.
Neither Theorem 77.1 nor Theorem 79.1 classifies families for which
$\chi(g)$ tends to a finite strictly positive constant, or has
neither limit zero nor limit infinity.

Proof. In the power case $\chi=g^{1-3p/2}\to\infty$; in the
second case $\chi=L^{-3/2}\to\infty$ and $\tau\to0$.
Substitution in (79.1) gives the stated power order. The last
assertion specifies the missing hypotheses of the two theorems;
no critical constant or complete crossover classification is
inferred. $\square$

## 80. Native normalization and the scope of the joint conclusions

**Proposition 80.1 (source, Jacobian and limiting scales).** The joint
conclusions retain exactly the Coulomb tensor, source coefficient
and original-coordinate transport of §§70--74. In particular, with
$J_\kappa=\operatorname{diag}(1,1,\kappa)$ and $D=\kappa x$,
for every positive cutoff in either regime,

$$
\psi^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1/2}\psi(k,q),\qquad
W_\tau^{\rm orig}(k,J_\kappa q)=|\kappa|^{-1}W_\tau(k,q),
\qquad g_{\rm orig}=|\kappa|g.
\tag{80.1}
$$

The tensor in original coordinates is
$J_\kappa M J_\kappa^{\mathsf T}$ with its signed cross terms.
The conclusions concern a fixed nonzero $\kappa$, the all-real
threshold cover and positive cutoffs. They assert neither an
unregularized semibounded realization nor an exact microscopic
limiting problem, and do not transfer to a wrapped threshold cover
or the actual zero leaf. They do not select physical space or
physical $SO(3)$.

Proof. The absolute Jacobian is $|\kappa|$, so the unitary
wavefunction factor differs from the unit raw-source kernel factor
exactly as in Proposition 74.1. None of the cutoff estimates changes
this Jacobian or the clock. The macroscopic coefficient remains
$\phi(k_0)\int\phi^3/(4\pi\sqrt{\det M})$: (77.5)--(77.8)
compare directly with the same raw point-source problem at cutoff
one, not a stationary-height source. Formula (75.4) preserves its
distinct raw and $\phi$-weighted charges at every time.

The native joint estimates (76.7), (77.7) and (78.8)--(79.1) are
repo-derived consequences of the specified suppliers. The sharp
all-height short-time input is G §32, the large-time and threshold
inputs are L Lemma 41.2 and §§42--48, and the fixed-reference
variational and profile inputs are §§71--73. G Theorem 3.1 supplies
the privileged concentration mechanism; (78.8) verifies that its
time window survives the present positive cutoff. The cited
Colin de Verdière--Hillairet--Trélat theorems supply local
positive-time kernel convergence and localization only. The
weighted Schur test and Cauchy--Schwarz are classical intermediate
steps, rather than new standalone results or a global Green
asymptotic. These correspondences make no literature-wide novelty
assertion. The exclusions concerning large-time divergence on
wrapped covers and the actual zero leaf are those of Proposition
74.1 and L §§44--45. The different small-time and large-time
scales proved here therefore preserve all those boundaries.
$\square$

## 追加锚（本行以下为增补区）


## 81. The exact microscopic operator and its raw source

**Definition 81.1 (unitary microscopic problem).** Retain Definition
75.1 without changing any datum. In particular $\kappa$ is one fixed
admissible signed nonzero number, $a>0$, the heat clock is that of $B$,
and both height faces are Dirichlet. Put $s=\sqrt\tau$ and use exactly
$\Xi_s$, $c_j$ and $j_0$ of (78.1). Define

$$
\begin{aligned}
I_s&=((l-k_0)/(\varepsilon s),(u-k_0)/(\varepsilon s)),&
\Omega_s&=I_s\times\mathbb R^3,\\
(\mathcal U_s\psi)(\xi)&=(j_0s^7)^{1/2}\psi(\Xi_s(\xi)),&
\mathcal Q_s&=\mathcal U_s\mathcal Q,\\
X&=\partial_r,& Y_s&=v_s(r)\cdot\partial_{y,z,w},\\
b_s[f]&=\|Xf\|_2^2+\|Y_sf\|_2^2,& A_s&=X^*X+Y_s^*Y_s,\\
U_s(\xi)&=s^5W_{s^2}(\Xi_s(\xi)),&
\chi&=g s^{-3}.
\end{aligned}
\tag{81.1}
$$

Here $A_s$ is the Friedrichs operator with form domain $\mathcal Q_s$.
Vectors and potentials on $\Omega_s$ are extended by zero when compared
in $L^2(\mathbb R^4,d\xi)$ or in supremum norm. This extension does not
replace either moving Dirichlet face by a reflecting face. The fields
$v_s$ are the exact pulled-back fields of (78.4), not their Taylor
polynomials. Let

$$
Y=\partial_y+r\partial_z+\tfrac12r^2\partial_w,
\quad b[f]=\|Xf\|_2^2+\|Yf\|_2^2,
\quad \mathcal Q_E=\overline{C_c^\infty(\mathbb R^4)}^{(\|\cdot\|_2^2+b)^{1/2}},
\quad \mathcal E=X^*X+Y^*Y.
\tag{81.2}
$$

This is exactly G (31.2), on unit Lebesgue measure. Write its kernel
as $p_E(t;\eta,\xi)$, and set

$$
V(\xi)=\frac1{j_0}\int_1^\infty p_E(t;0,\xi)dt,
\qquad h_\chi[f]=a b[f]-\chi\int V|f|^2d\xi,
\qquad e(\chi)=\inf_{\substack{f\in\mathcal Q_E\\\|f\|_2=1}}h_\chi[f].
\tag{81.3}
$$

The kernel uses $e^{-t\mathcal E}$, independently of $a$. In particular
(81.3) contains neither $p_E(at;0,\xi)$ nor a unit-source potential
with the factor $1/j_0$ removed.

**Proposition 81.2 (exact conjugacy and source normalization).** The map
$\mathcal U_s$ is unitary onto $L^2(\Omega_s,d\xi)$, and on the entire
complex form domain, for arbitrary norms,

$$
\begin{aligned}
b_s[\mathcal U_s\psi]&=s^2\bigl(T[\psi]+\lambda\|\psi\|_2^2\bigr),\\
s^2\mathfrak e_{g,s^2}[\psi]
 &=a b_s[\mathcal U_s\psi]-\chi\int U_s|\mathcal U_s\psi|^2d\xi
                         -a\lambda s^2\|\psi\|_2^2.
\end{aligned}
\tag{81.4}
$$

The rescaled unit-Lebesgue heat kernel is

$$
P_s(t;\eta,\xi)=j_0s^7p_{s^2t}(\Xi_s(\eta),\Xi_s(\xi)),
\qquad
U_s=\frac1{j_0}\int_1^\infty e^{\lambda s^2t}P_s(t;0,\cdot)dt.
\tag{81.5}
$$

If $\rho_{s^2}$ is the exact source in (75.4), then in distributions
on $\Omega_s$,

$$
(A_s-\lambda s^2)U_s=s^7\rho_{s^2}(\Xi_s(\cdot)),
\qquad
\mathcal E V=\frac1{j_0}p_E(1;0,\cdot).
\tag{81.6}
$$

Moreover, with zero extensions,

$$
j_0s^7\rho_{s^2}(\Xi_s(\cdot))\longrightarrow p_E(1;0,\cdot)
\quad\hbox{in }L^1(d\xi)\hbox{ and locally uniformly}.
\tag{81.7}
$$

Thus the limiting source in (81.6) has Lebesgue mass $1/j_0$; its
native raw-source mass is one. These are the same normalization in
the two different densities.

Proof. The absolute Jacobian is exactly $j_0s^7$, while its
wavefunction factor is its square root. Pulling back $s\varepsilon
\partial_k$ and $s(c_\kappa\cdot\partial_q)$ gives $X,Y_s$.
The smooth-core calculation (78.5) therefore proves (81.4) there;
unitarity and form closure extend it to exactly (75.1). Both height
traces and all real phase frequencies are retained in this closure.
No estimate of an ordinary phase gradient is involved. Changing
variables in the heat semigroup gives the first identity in (81.5);
changing the integration variable in $W_{s^2}$ gives the second.
The native source equation (75.4) then gives the first equation
in (81.6).

The local positive-time blow-up used in (78.7), with its identical
fields, constant density, interior pole and localization away from
both faces, applies on any compact subset of
$(0,\infty)\times\mathbb R^4$. Its supplier is
Colin de Verdière--Hillairet--Trélat, Theorem B (2.8), pp.915--916,
and Theorem 3.2, pp.920--921,
[DOI 10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf).
Consequently

$$
P_s(t;0,\xi)\longrightarrow p_E(t;0,\xi)
\quad\hbox{locally uniformly for }t>0.
\tag{81.8}
$$

The same normalization at $t=1$, multiplied by $e^{\lambda s^2}$,
is the left side of (81.7). Its total integral is exactly
$e^{\lambda s^2}\mathbb P_{k_0}(\zeta>s^2)\to1$ by (75.4).
The canonical heat has mass one: its complete diffusion has height
$\sqrt2 B^1$ and the other coordinates are the finite stochastic
integrals of $1,r,r^2/2$ against $\sqrt2 B^2$ on each finite time
interval. Local convergence, nonnegativity and convergence of total
masses give (81.7), for example by the identity for the integral of
the minimum of two nonnegative densities. This proves source
convergence without renormalizing the surviving source. The second
identity in (81.6) follows by testing the integral (81.3) and
integrating the heat equation; its infinite-time boundary term
vanishes by the bound established below. $\square$

## 82. Uniform control of the complete integrated field

**Lemma 82.1 (canonical geometry and free heat).** The multiplication

$$
(r,y,z,w)(r',y',z',w')=
(r+r',y+y',z+z'+ry',w+w'+rz'+\tfrac12r^2y')
\tag{82.1}
$$

makes $\mathbb R^4$ the step-three Engel group with Haar measure
$d\xi$. Its left invariant fields $X,Y,[X,Y],[X,[X,Y]]$ have determinant
one. The automorphic dilations and homogeneous dimension are

$$
\delta_R(r,y,z,w)=(Rr,Ry,R^2z,R^3w),\qquad Q=7.
\tag{82.2}
$$

Let $d_E$ be its control distance for $X,Y$, with squared control
cost $u^2+v^2$, and put
$N(\xi)=\max(|r|,|y|,|z|^{1/2},|w|^{1/3})$. Then $d_E$ is proper,
$d_E(0,\xi)\ge cN(\xi)$, and

$$
0<p_E(t;\eta,\xi)\le
 C t^{-7/2}\exp[-c d_E(\eta,\xi)^2/t],\qquad t>0.
\tag{82.3}
$$

In particular $V$ is bounded, smooth, strictly positive, and

$$
0<V(\xi)\le C(1+N(\xi))^{-5},\qquad
\sup_\xi p_E(t;0,\xi)\le c_Et^{-7/2},\quad c_E=p_E(1;0,0).
\tag{82.4}
$$

Proof. The semidirect action on $(y,z,w)$ in (82.1) has determinant
one and satisfies $T_rT_{r'}=T_{r+r'}$. This verifies associativity,
Haar measure and the displayed fields. Their two nonzero successive
brackets are $\partial_z+r\partial_w$ and $\partial_w$.
This also checks (82.2) and the identification with G (31.2).
Along a control path of length $L$ from zero, successive integration
gives $|r|,|y|\le L$, $|z|\le L^2$ and $|w|\le L^3/2$.
Thus $N\le CL$. Finite control balls have bounded coordinates;
unit-speed paths in such a ball have uniformly bounded velocities,
and subsequential limits of their bounded controls and paths remain
admissible. Closed control balls are compact. Bracket generation
gives finite distances and the ordinary manifold topology.

Left invariance and dilation covariance give
$p_E(t;\eta,\eta)=c_Et^{-7/2}$, with the exact clock of G (31.2).
The heat is smooth and positive by the same bracket-generating
canonical heat supplier used in (78.7). For the off-diagonal bound
we use Coulhon--Sikora,
*Gaussian heat kernel upper bounds via Phragmén--Lindelöf theorem*,
[arXiv:math/0609429](https://arxiv.org/abs/math/0609429), Theorem 4.1.
Its hypotheses here are nonnegative selfadjoint $\mathcal E$, a
continuous heat kernel, the preceding all-time diagonal estimate
with $D=7$, and the Davies--Gaffney estimate in $d_E$.
To check the last hypothesis, if $h$ is a bounded real horizontal
Lipschitz function with $|Xh|^2+|Yh|^2\le1$, completing the square
in the form gives

$$
\|e^{\alpha h}e^{-t\mathcal E}e^{-\alpha h}\|_{2\to2}
 \le e^{\alpha^2t}.
\tag{82.5}
$$

Take $h$ to be distance from one support, truncated at the distance
between the two supports, and optimize $\alpha$ to obtain
$e^{-d^2/(4t)}$ in the $L^2$ off-diagonal estimate. Bounded horizontal
Lipschitz multipliers and this calculation follow by form closure
from smooth local approximations. Theorem 4.1 gives a polynomial
factor $(1+d^2/(4t))^{7/2}$ times the Gaussian; absorbing it into a
Gaussian with a smaller exponent proves (82.3). No volume-doubling
or Euclidean ellipticity premise is needed.

Semigroup Cauchy--Schwarz gives the second bound in (82.4) with its
stated diagonal constant. Integrating (82.3) over $t\ge1$ gives
$C(1+d_E(0,\xi))^{-5}$, hence the first bound in (82.4).
The weak heat-equation calculation of (81.6) is now justified by
$t^{-7/2}$ at infinity. Hypoellipticity applied to that equation,
whose right side is smooth, proves smoothness of $V$; heat positivity
proves its strict positivity. $\square$

**Lemma 82.2 (native intrinsic estimate and source-centred tails).**
There are fixed $C,c,\delta>0$ such that the native control distance
$d$ for $\varepsilon\partial_k,c_\kappa\cdot\partial_q$ satisfies

$$
p_t(Y,Z)\le Ct^{-7/2}\exp[-c d(Y,Z)^2/t]\quad(t>0),
\tag{82.6}
$$

and, whenever $sR\le\delta$ and $R\ge1$,

$$
\sup_{\substack{\xi\in\Omega_s\\N(\xi)>R}}U_s(\xi)
 \le CR^{-5}+Cs^5.
\tag{82.7}
$$

Both constants are independent of the height of $Y,Z$, including
heights approaching either absorbing face.

Proof. The all-height diagonal estimate (76.1) gives $Ct^{-7/2}$
for $t\le1$. Its killed large-time line also gives this power for
$t\ge1$, because $t^2e^{-\lambda t}$ is bounded. Thus the all-time
diagonal premise of Coulhon--Sikora Theorem 4.1 holds for $B$ on
$(\mathcal C,d,dk\,dq)$, again with $D=7$. The operator is nonnegative
selfadjoint with a smooth interior kernel. Complex-time kernel
continuity, if used in that theorem, follows by factoring the
analytic semigroup between two positive-time smoothing factors.
The calculation (82.5) applies with the native two fields: bounded
multiplication preserves both Dirichlet traces, and the carré du
champ is exactly
$\varepsilon^2|\partial_kh|^2+|c_\kappa\cdot\partial_qh|^2$.
It proves precisely the Davies--Gaffney hypothesis in the native
control distance. This proves (82.6). It does not assume that
$e^{-tS}$ is sub-Markov in raw measure.

Here is the geometric comparison needed for the expanding charts.
For a native path from $o$ of length $L$ smaller than a fixed
$\delta_1>0$, $|k-k_0|\le\varepsilon L$, so it stays in a fixed
interior height interval. Taylor expansion in the fixed basis
$(c_0,c_1,c_2)$ gives the three coefficient functions

$$
1+O(h^3),\qquad h+O(h^3),\qquad h^2/2+O(h^3),\quad h=k-k_0.
\tag{82.8}
$$

Integrating them against the second control, whose absolute
integral is at most $L$, bounds the three phase coefficients by
$CL,C\varepsilon L^2,C\varepsilon^2L^3$, respectively.
Together with the height bound and (78.1), this yields
$N(\Xi_s^{-1}(Y))\le CL/s$ when $d(o,Y)<\delta_1$.
For larger distances retain $d(o,Y)\ge\delta_1$. Consequently, after
fixing a smaller $\delta$, points with $N(\xi)>R$ and $sR\le\delta$
satisfy $d(o,\Xi_s\xi)/s\ge cR$.

For $s^2t\le1$, (82.6) therefore bounds the integrand in (81.5)
by $Ct^{-7/2}e^{-cR^2/t}$, including its bounded threshold factor
$e^{\lambda s^2t}$. Its integral over $1\le t\le s^{-2}$ is at most
$CR^{-5}$. The remaining part is

$$
s^5\int_1^\infty e^{\lambda u}p_u(o,\Xi_s\xi)du\le Cs^5
\tag{82.9}
$$

by (76.1). This proves (82.7). Both moving faces were retained in
the killed heat and in its all-height diagonal bound. $\square$

**Theorem 82.3 (integrated convergence, including infinite time).**
With the zero extension convention of Definition 81.1,

$$
\|U_s-V\|_{L^\infty(\mathbb R^4)}\longrightarrow0,
\qquad \sup_{0<s\le s_0}\|U_s\|_\infty<\infty.
\tag{82.10}
$$

More precisely, finite positive-time windows converge locally
uniformly as in (81.8), and, for every $M\ge1$,

$$
\sup_{\xi\in\Omega_s}\frac1{j_0}
 \int_M^\infty e^{\lambda s^2t}P_s(t;0,\xi)dt
 \le CM^{-5/2}+Cs^5.
\tag{82.11}
$$

The tangent integral over $[M,\infty)$ is at most $CM^{-5/2}$.
These assertions concern the complete integrated threshold field,
including its original infinite-time part.

Proof. On $[1,M]$ use (81.8). Between rescaled times $M$ and $s^{-2}$,
when this interval is nonempty, (76.1) gives the integrable upper
bound $Ct^{-7/2}$, because the threshold factor is bounded there.
For original times at least one use exactly (82.9). If $M>s^{-2}$,
the whole remaining integral is already bounded by that expression.
This proves (82.11); (82.4) gives the tangent assertion.
Thus first $s\to0$ at fixed $M$, then $M\to\infty$, proves locally
uniform convergence of the integrated potentials. It also gives
uniform boundedness. To pass from local to global uniform
convergence, use (82.7) and (82.4) outside the fixed compact box
$\{N\le R\}$. For each fixed $R$ it lies in $\Omega_s$ eventually;
then let $R\to\infty$. Points outside $\Omega_s$ have already been
included by zero extension and the same tangent tail bound.
This proves (82.10). The argument separates a finite-time local
supplier from two explicit integrable time tails and a spatial
tail; no local heat theorem is being used as an infinite Green
interchange. $\square$


## 83. Compactness for the entire complex horizontal domain

**Lemma 83.1 (varying-domain local compactness and the lost mass).**
Suppose $s_n\downarrow0$, $f_n\in\mathcal Q_{s_n}$, and

$$
\sup_n(\|f_n\|_2^2+b_{s_n}[f_n])<\infty.
\tag{83.1}
$$

After a subsequence, their zero extensions converge weakly in
$L^2(\mathbb R^4)$ and strongly in $L^2$ on every compact set to a
vector $f\in\mathcal Q_E$. They satisfy

$$
\begin{aligned}
\|f\|_2&\le\liminf_n\|f_n\|_2,&
b[f]&\le\liminf_n b_{s_n}[f_n],\\
\|U_{s_n}^{1/2}f_n-V^{1/2}f\|_2&\longrightarrow0,&
\int U_{s_n}|f_n|^2&\longrightarrow\int V|f|^2.
\end{aligned}
\tag{83.2}
$$

There is no assumption of tightness in (83.1).

Proof. On every fixed coordinate box, $Y_s\to Y$ in $C^\infty$
by (78.4). The determinant of the four fields
$X,Y_s,[X,Y_s],[X,[X,Y_s]]$ converges uniformly there to one.
Thus these fields have one uniform strong Hörmander bound of step
three on a slightly larger fixed box. The parameter-uniform local
subelliptic estimate of Colin de Verdière--Hillairet--Trélat,
Appendix B, Theorem B.1, pp.953--955, applies to $-A_s$ there: its
coefficient derivatives are uniformly bounded, its drift and
potential vanish, and its density is unit Lebesgue. In particular,
for nested compact cutoffs $\eta,\eta'$ with $\eta'=1$ near
$\operatorname{supp}\eta$, there are $\sigma>0$ and $C$ independent
of small $s$ such that

$$
\|\eta u\|_{H^\sigma}
 \le C\bigl(\|\eta'A_su\|_2+\|\eta'u\|_2\bigr).
\tag{83.3}
$$

We use this operator estimate to obtain form compactness, rather
than assuming an ordinary Sobolev norm for a form-domain vector.
For a fixed $d>0$ set $u_{n,d}=(1+dA_{s_n})^{-1}f_n$. The spectral
theorem and (83.1) give

$$
\|u_{n,d}\|_2\le C,\qquad
\|A_{s_n}u_{n,d}\|_2\le C/d,\qquad
\|f_n-u_{n,d}\|_2^2\le d\,b_{s_n}[f_n].
\tag{83.4}
$$

The local estimate (83.3) applies to these resolvents by its closed
distributional extension; equivalently approximate their right
sides in $L^2$ and use (83.3). Both moving faces lie outside each
fixed box eventually. Hence, at fixed $d$, Rellich compactness
makes $\eta u_{n,d}$ precompact in $L^2$. Letting $d\downarrow0$
in the last bound of (83.4) makes $\eta f_n$ precompact too.
A compact exhaustion and the global $L^2$ bound give a subsequence
with the asserted local strong and global weak convergence.

Extend $Xf_n$ and $Y_{s_n}f_n$ by zero as $L^2$ vectors and take
weakly convergent subsequences. Testing on fixed compact sets,
using $Y_s\to Y$ and their zero divergences, identifies the limits
as $Xf$ and $Yf$. Lower semicontinuity of their joint squared norm
proves the energy inequality in (83.2).
To check membership in the specified Friedrichs form domain, a
vector with these two distributional derivatives in $L^2$ can be
cut off by $\eta_R(\xi)=\eta_1(\delta_{1/R}\xi)$, where $\eta_1$
is compactly supported and one near zero. Its two horizontal
derivatives are bounded by $C/R$, and dominated convergence shows
$\eta_R f\to f$ in horizontal form norm. Smooth group approximate
identities applied to these compactly supported vectors then
converge in the same norm, since the horizontal derivatives are
left invariant. Thus $f\in\mathcal Q_E$, with no boundary condition
at a fictitious finite rescaled height.

Finally (82.10) gives
$\|U_{s_n}^{1/2}-V^{1/2}\|_\infty\to0$. On a fixed compact set use
local strong convergence; on its complement use the vanishing
supremum of $V$ from (82.4) and the uniform $L^2$ bounds. This proves
the last two assertions of (83.2). $\square$

**Proposition 83.2 (full lower inequality and recovery).** If
$\chi_n\to\chi>0$, $s_n\downarrow0$, $\|f_n\|_2\le C$, and the
rescaled forms

$$
q_n[f_n]=a b_{s_n}[f_n]-\chi_n\int U_{s_n}|f_n|^2
                         -a\lambda s_n^2\|f_n\|_2^2
\tag{83.5}
$$

are bounded above, then (83.1) holds. Along every subsequence
realizing a finite lower limit, a further subsequence satisfies

$$
\liminf_n q_n[f_n]\ge h_\chi[f]\ge e(\chi)\|f\|_2^2.
\tag{83.6}
$$

For every $f\in\mathcal Q_E$ there are $f_n\in\mathcal Q_{s_n}$
converging strongly to $f$ with
$q_n[f_n]\to h_\chi[f]$ and $\|f_n\|_2\to\|f\|_2$.
They may be chosen normalized when $f$ is normalized.

Proof. Uniform boundedness of $U_s$, boundedness of $\chi_n$ and
$a>0$ turn the upper energy bound into (83.1). Apply Lemma 83.1.
Its kinetic lower bound and potential convergence give the first
inequality in (83.6); the second is the homogeneous Rayleigh
inequality, including $f=0$.

For recovery first take $f\in C_c^\infty(\mathbb R^4)$. It belongs
to $\mathcal Q_{s_n}$ eventually, both its height traces being zero.
Coefficient convergence gives $b_{s_n}[f]\to b[f]$ and (82.10) gives
the potential convergence. Now approximate an arbitrary $f$ by
this core in the defining norm of $\mathcal Q_E$. Boundedness of
$V$ gives convergence of its potential form. A diagonal choice of
core approximants, each used only once its compact support lies
between the two moving faces and its coefficient error is small,
proves recovery. Renormalizing changes neither limit for a nonzero
normalized target. This is an upper construction on the full native
domain, paired with a lower estimate for every bounded-energy
sequence on that domain. $\square$

## 84. A finite positive tangent binding threshold

**Theorem 84.1 (threshold, exact characterization and spectrum).**
Define the finite positive constant and its critical coupling by

$$
C_* =\sup_{0\ne f\in\mathcal Q_E}
        \frac{\int V|f|^2}{b[f]},\qquad
\chi_c=\frac a{C_*}
       =a\inf_{0\ne f\in\mathcal Q_E}\frac{b[f]}{\int V|f|^2}.
\tag{84.1}
$$

These definitions have no zero denominators. They satisfy

$$
0<C_*\le\frac{4c_E}{15j_0},\qquad
0<\frac{15aj_0}{4c_E}\le\chi_c<\infty.
\tag{84.2}
$$

For every $\chi\ge0$ the operator
$H_\chi=a\mathcal E-\chi V$ is selfadjoint on $D(\mathcal E)$,
with closed form on precisely $\mathcal Q_E$, and

$$
\sigma_{\rm ess}(H_\chi)=[0,\infty),\qquad
\begin{cases}
e(\chi)=0, H_\chi\ge0,&0\le\chi\le\chi_c,\\
e(\chi)<0,&\chi>\chi_c.
\end{cases}
\tag{84.3}
$$

For $0\le\chi<\chi_c$ there is no nonzero $L^2$ zero mode. For
$\chi>\chi_c$, $e(\chi)$ is a simple isolated eigenvalue with a
unique positive normalized eigenfunction $\Phi_\chi$. Its complex
normalized minimizers are exactly $e^{i\theta}\Phi_\chi$ for constant
$\theta\in\mathbb R$. All negative spectrum is discrete, with finite
multiplicities and possible accumulation only at zero.

An operator characterization of exactly the same threshold is
obtained by putting, for $b>0$,

$$
K_b=V^{1/2}(\mathcal E+b)^{-1}V^{1/2},\qquad
K_0=\mathop{\rm s\!\!\!-lim}_{b\downarrow0}K_b.
\tag{84.4}
$$

The strong limit is a bounded positive operator,
$\|K_0\|=C_*$, and $\chi_c=a/\|K_0\|$. If $\chi>\chi_c$, the
unique positive solution $b_\chi$ of

$$
\chi\|K_{b_\chi}\|=a
\tag{84.5}
$$

gives exactly $e(\chi)=-ab_\chi$. Compactness of $K_0$, or a
classification of its threshold eigenvectors, is not part of
these assertions.

Proof. We first prove the finite homogeneous form bound in (84.2).
For the nonnegative heat-resolvent integral, symmetry and the
semigroup law, with Tonelli, give

$$
\begin{aligned}
(\mathcal E^{-1}V)(\xi)
 &=\frac1{j_0}\int_0^\infty\int_1^\infty
                         p_E(t+u;0,\xi)dt\,du\\
 &\le\frac{c_E}{j_0}\int_1^\infty\int_0^\infty(t+u)^{-7/2}du\,dt
   =\frac{4c_E}{15j_0}=:C_0.
\end{aligned}
\tag{84.6}
$$

This notation defines a nonnegative pointwise integral, not a
bounded inverse of $\mathcal E$ on $L^2$. For each $b>0$, the
positive-kernel operator $K_b$ has Schur weight $V^{1/2}$ and
weighted row integral
$V(\xi)^{1/2}((\mathcal E+b)^{-1}V)(\xi)\le C_0V(\xi)^{1/2}$.
Thus $\|K_b\|\le C_0$. The same squared-operator-norm identity used
in (76.3) yields

$$
\int V|f|^2\le C_0\bigl(b[f]+b\|f\|_2^2\bigr).
\tag{84.7}
$$

Let the resolvent parameter $b\downarrow0$. This proves
$\int V|f|^2\le C_0 b[f]$ on all of $\mathcal Q_E$.
Here the integrability of the double time integral uses $Q=7>4$;
it does not follow merely from a positive-time heat limit.
If $b[f]=0$, both horizontal distributional derivatives vanish;
their brackets then show all coordinate derivatives vanish.
An $L^2$ constant on this infinite-volume group is zero.
Strict positivity of $V$ gives a positive potential integral for
every nonzero $f$. A single nonzero compact core vector shows
$C_*>0$. These facts prove (84.1)--(84.2).

Boundedness of $V$ proves the stated form and operator domains.
The fixed-field version of Lemma 83.1 proves local compactness of
$\mathcal Q_E$ in $L^2$; with (82.4) this makes
$V^{1/2}(\mathcal E+1)^{-1/2}$ compact.
The free spectrum is $[0,\infty)$: dilation covariance makes its
nonzero spectrum invariant under every positive scale, and the
operator is nonzero and unbounded. Zero belongs by closure, or by
normalized outward dilations, whose kinetic energy is $R^{-2}b[f]$.
Every free spectral point is essential. Indeed translate approximate
eigenvectors by group left translations tending sufficiently far
to make them weakly zero; the operator commutes with these
translations. Matrix coefficients of translations on $L^2$ vanish
at infinity by approximation with compactly supported functions,
so this construction satisfies Weyl's criterion. The compact form
perturbation just proved and the resolvent identity preserve this
essential spectrum under $-\chi V$. This is the abstract compact
perturbation principle, applied after checking its horizontal
hypotheses; it is not an appeal to a Euclidean Schrödinger theorem.

The definition of $C_*$ gives

$$
h_\chi[f]\ge a(1-\chi/\chi_c)b[f]\quad(0\le\chi\le\chi_c).
\tag{84.8}
$$

On the other hand normalized outward dilations of one compact
core vector have $h_\chi\le aR^{-2}b[f]\to0$, since $V\ge0$.
Thus the bottom is zero in this range. Strict inequality in
$\chi<\chi_c$ and the preceding no-constant argument exclude a
nonzero zero mode. If $\chi>\chi_c$, the supremum defining $C_*$
provides a vector with negative Rayleigh quotient. The essential
spectrum result makes the negative bottom an isolated eigenvalue.
Boundedness below and compactness of the perturbation give the
other assertions concerning the negative spectrum.

For completeness, positivity and simplicity do not require taking
a phase derivative. The convergent bounded-potential Dyson expansion
of $e^{-tH_\chi}$ has nonnegative kernel terms and its first term is
$p_E(at;\eta,\xi)>0$. Hence its kernel is strictly positive.
For any bottom eigenvector $u$, the pointwise triangle inequality
$|e^{-tH_\chi}u|\le e^{-tH_\chi}|u|$ and the spectral norm
$\|e^{-tH_\chi}\|=e^{-te(\chi)}$ force equality in norm and then in
the pointwise inequality. Thus $|u|$ is also a bottom eigenvector,
and equality in the integral triangle inequality with a strictly
positive kernel forces the phase of $u$ to be constant almost
everywhere. Moreover $|u|$ is strictly positive. Two independent
positive real bottom eigenvectors would have a real linear
combination changing sign, contradicting the same argument.
This proves the claimed uniqueness and complex phase orbit.

Finally $K_b$ increases in positive-operator order as $b\downarrow0$,
is uniformly bounded by (84.6), and therefore has the strong limit
in (84.4). For each $b>0$ the squared-norm identity gives

$$
\|K_b\|=\sup_{0\ne f\in\mathcal Q_E}
 \frac{\int V|f|^2}{b[f]+b\|f\|_2^2}.
\tag{84.9}
$$

Taking the supremum over $b\downarrow0$ proves $\|K_0\|=C_*$.
For positive $b$, form compactness makes $K_b$ compact, nonzero and
positive. Its norm is continuous in $b$, tends to zero as
$b\to\infty$, and is strictly decreasing: for $b_1<b_2$ test
$K_{b_1}-K_{b_2}$ on a top eigenvector of $K_{b_2}$ and use strict
positivity of the resolvent difference on the nonzero vector
$V^{1/2}u$. Its limit at zero is $C_*$. These facts give the unique
root (84.5). Form conjugation by $(\mathcal E+b)^{1/2}$ shows
$H_\chi+ab\ge0$ exactly when $\chi\|K_b\|\le a$.
At the root a top eigenvector $u$ of $K_b$ gives the nonzero vector
$f=(\mathcal E+b)^{-1}V^{1/2}u\in D(\mathcal E)$ with
$(H_\chi+ab)f=0$. Thus its energy is the bottom and equals $-ab$.
This proves the operator characterization as well as the Rayleigh
one. $\square$


## 85. The exact native limit and every negative-sector profile

**Theorem 85.1 (two-sided finite-positive-coupling limit).** Let
$g_n>0$, $\tau_n>0$ tend to zero in any manner such that

$$
\chi_n=g_n\tau_n^{-3/2}\longrightarrow\chi_0\in(0,\infty).
\tag{85.1}
$$

On exactly the native domain (75.1), with no restriction to a band,
product vector, real vector or ordinary phase $H^1$ domain,

$$
\boxed{\displaystyle
\lim_n\tau_n E_{\tau_n}(g_n)=e(\chi_0).}
\tag{85.2}
$$

In fact every normalized native sequence $\psi_n\in\mathcal Q$
satisfies

$$
\liminf_n\tau_n\mathfrak e_{g_n,\tau_n}[\psi_n]\ge e(\chi_0),
\tag{85.3}
$$

and normalized admissible recovery sequences attain the upper
limit $e(\chi_0)$.

Proof. Put $s_n=\sqrt{\tau_n}$, $f_n=\mathcal U_{s_n}\psi_n$.
The exact conjugacy (81.4) makes the expression in (85.3) equal to
$q_n[f_n]$ in (83.5). If its lower limit is infinite there is
nothing to prove. Otherwise pass to a subsequence realizing that
lower limit. Uniform boundedness of $U_s$ bounds these forms below
and makes their kinetic energies bounded above along this
subsequence. Proposition 83.2 gives a further subsequence and a
limit $f$ with

$$
\liminf_n q_n[f_n]\ge h_{\chi_0}[f]
             \ge e(\chi_0)\|f\|_2^2\ge e(\chi_0).
\tag{85.4}
$$

The last step uses $\|f\|_2\le1$ and $e(\chi_0)\le0$, established
in Theorem 84.1. In particular mass outside all rescaled compact
sets is allowed. Its absence from $f$ cannot lower (85.4): it loses
the entire compact potential contribution and the discarded
kinetic energy is nonnegative. No assertion of tightness entered
the lower direction.

For the upper direction choose a normalized compact core vector
$f$ with $h_{\chi_0}[f]\le e(\chi_0)+\epsilon$. Such vectors exist
by the defining core and boundedness of $V$. For all large $n$ its
support lies inside both moving height faces, and
$\mathcal U_{s_n}^{-1}f\in\mathcal Q$ is normalized. Its rescaled
energy tends to $h_{\chi_0}[f]$ by Proposition 83.2. Let
$\epsilon\downarrow0$, using a diagonal choice if a single recovery
sequence is desired. Applying (85.3) to normalized infimizing
native vectors and this upper bound proves (85.2). These two
arguments cover every sequence (85.1), not just a power-law path.
$\square$

**Theorem 85.2 (every complex negative-sector near-minimizer).**
Assume (85.1) and $\chi_0>\chi_c$. For every complex normalized
sequence $\psi_n\in\mathcal Q$ satisfying precisely

$$
\tau_n\bigl(\mathfrak e_{g_n,\tau_n}[\psi_n]
                         -E_{\tau_n}(g_n)\bigr)\longrightarrow0,
\tag{85.5}
$$

there are constant phases $\theta_n\in\mathbb R$ such that, with
zero extension outside $\Omega_{s_n}$,

$$
\left\|(j_0s_n^7)^{1/2}\psi_n(\Xi_{s_n}(\cdot))
                  -e^{i\theta_n}\Phi_{\chi_0}\right\|_{L^2(d\xi)}
 \longrightarrow0.
\tag{85.6}
$$

Consequently the entire mass concentrates at the fixed source in
the privileged microscopic scales:

$$
\lim_{R\to\infty}\limsup_n
 \int_{\mathcal C\setminus\Xi_{s_n}(\{N\le R\})}
                            |\psi_n(Y)|^2dY=0.
\tag{85.7}
$$

The intersections with $\mathcal C$ are understood in (85.7).
There are no translations, frequency restrictions or spatially
varying phase adjustments in (85.6). Every choice of normalized
native ground states is included.

Proof. Theorem 85.1 and (85.5) give
$q_n[f_n]\to e(\chi_0)<0$. The kinetic bound of Proposition 83.2
and Lemma 83.1 apply to every subsequence. Along a further
subsequence, (85.4) now gives the chain

$$
e(\chi_0)\ge h_{\chi_0}[f]
       \ge e(\chi_0)\|f\|_2^2\ge e(\chi_0).
\tag{85.8}
$$

All terms are equal. Since $e(\chi_0)<0$, equality forces
$\|f\|_2=1$. Weak convergence of unit vectors is therefore strong
in global $L^2$, and $f$ is a normalized minimizer of $h_{\chi_0}$.
Theorem 84.1 makes it exactly $e^{i\theta}\Phi_{\chi_0}$.
Thus every subsequence has a further subsequence converging to
this one phase orbit. If its distance from the orbit did not tend
to zero, a subsequence bounded away from it would contradict this
conclusion. Choose the phases minimizing that distance; equivalently
use the argument of $\langle f_n,\Phi_{\chi_0}\rangle$ with the
appropriate inner-product convention. This proves (85.6).
Global $L^2$ convergence to a fixed normalized profile gives (85.7).
The source was fixed in the potential and in $\Xi_s$, so there is
no free centre parameter. The phase-orbit result in Theorem 84.1
was proved using positive kernels, and imposes no additional phase
regularity on the native vectors. $\square$

**Theorem 85.3 (subcritical disappearance and the critical weak limit).**
Under (85.1), let $\psi_n$ be any normalized complex native
sequence satisfying (85.5).
If $0<\chi_0<\chi_c$, then, for every compact $K\subset\mathbb R^4$,

$$
\int_{\Xi_{s_n}(K)\cap\mathcal C}|\psi_n|^2dY\longrightarrow0,
\qquad b_{s_n}[\mathcal U_{s_n}\psi_n]\longrightarrow0.
\tag{85.9}
$$

At $\chi_0=\chi_c$, $e(\chi_c)=0$ and $H_{\chi_c}\ge0$.
The rescaled vectors are bounded in kinetic energy and every
subsequence has a further subsequence converging weakly globally
and strongly locally to an $f\in\mathcal Q_E$ such that

$$
\|f\|_2\le1,\qquad
h_{\chi_c}[f]=0,\qquad f\in\ker H_{\chi_c}.
\tag{85.10}
$$

Along that subsequence the potential forms converge as in (83.2)
and the kinetic energies converge to $b[f]$. In particular, if
the tangent critical operator has no nonzero $L^2$ zero mode,
(85.9) also holds at criticality. No existence or absence of such
a critical zero mode, nor selection of a nonzero critical weak
limit, is asserted here.

Proof. In both cases Theorem 85.1 and (85.5) give $q_n[f_n]\to0$.
The compactness argument again applies, and its lower inequality
is $0\ge h_{\chi_0}[f]\ge0$. Below threshold (84.8) forces
$b[f]=0$, whence $f=0$. Every local subsequential limit is zero;
local compactness therefore proves the first assertion of (85.9)
for the whole sequence. The potential convergence in (83.2) then
makes its potential energy tend to zero. The exact identity
(83.5) implies $b_{s_n}[f_n]\to0$, proving the second assertion.

At criticality the same argument gives (85.10)'s form equality.
For a nonnegative selfadjoint operator this equality is
$\|H_{\chi_c}^{1/2}f\|_2^2=0$, which implies membership in its
operator kernel. Combining $q_n[f_n]\to0$ and potential convergence
with (83.5) gives
$a b_{s_n}[f_n]\to\chi_c\int V|f|^2=a b[f]$.
If that kernel is trivial all local limits are zero, and the
preceding subcritical argument applies. Without deciding the
kernel, (85.10) allows both a zero weak limit and lost mass; it
does not force strong convergence or a normalized limiting profile.
$\square$

## 86. Normalization, comparison regimes and the remaining scales

**Proposition 86.1 (scope of the microscopic classification).** The
threshold $\chi_c$ is a finite strictly positive threshold for the
limiting microscopic operator (81.3). For each actual pair
$g,\tau>0$ the native operator still has essential spectrum
$[0,\infty)$ and an attained negative bottom, as in Propositions
70.2 and 75.2. In particular tangent nonnegativity below threshold
is compatible with native binding at a smaller energy scale.

For $\chi_n\to\chi_0>\chi_c$, (85.2) implies
$E_{\tau_n}(g_n)\to-\infty$ and
$E_{\tau_n}(g_n)/g_n^2\to-\infty$.
For $\chi_0\le\chi_c$, it gives only
$E_{\tau_n}(g_n)=o(\tau_n^{-1})$ at the microscopic leading order.
This zero leading coefficient does not identify a finer Coulomb
$g_n^2$ law or an actual native critical-profile selection.
The exact critical tangent zero-mode taxonomy is left undecided.

The raw-coordinate transport remains exactly (80.1), with its
absolute Jacobian $|\kappa|$ and signed tensor
$J_\kappa M J_\kappa^{\mathsf T}$. All statements fix $\kappa\ne0$
and the real cover; none is uniform as $\kappa\to0$, a theorem on
the actual zero leaf or a torus, a cutoff-free realization, or a
selection of physical three-dimensional space or physical $SO(3)$.

Proof. The native spectral statements are reused at each positive
cutoff, with their exact unaltered native hypotheses. If the limit
in (85.2) is strictly negative, division by $\tau_n\to0$ proves the
first divergence. Since
$\tau_ng_n^2=\chi_n^2\tau_n^4\to0$, division by $g_n^2$ proves the
second. If the limit is zero, the displayed little-oh statement
is precisely what division by $\tau_n$ says, and it supplies no
coefficient on the much smaller $g_n^2$ scale. The subcritical
local-mass conclusion is exactly at the scales of $\Xi_s$, not an
identification of a different profile scale. At criticality the
available weak-limit statement is precisely (85.10).

The source correspondence is fixed by (81.5)--(81.7): the limiting
unit-Lebesgue kernel has mass one, the potential has source mass
$1/j_0$, and the unitary wavefunction uses $(j_0s^7)^{1/2}$.
The two native source charges also remain distinct. Explicitly,

$$
\begin{aligned}
\int_{\Omega_s}s^7\rho_{s^2}(\Xi_s\xi)d\xi
 &=j_0^{-1}e^{\lambda s^2}\mathbb P_{k_0}(\zeta>s^2)\to j_0^{-1},\\
\int_{\Omega_s}\phi(k_0+\varepsilon sr)
                       s^7\rho_{s^2}(\Xi_s\xi)d\xi
 &=j_0^{-1}\phi(k_0).
\end{aligned}
\tag{86.1}
$$

Thus no ground-height transform or surviving-charge normalization
has been inserted. Formula (80.1) transports these same conventions
back to the original coordinates without changing the heat clock.

The other named spectral limits have different premise maps.
[Critical cutoff, Definition 31.1](FIB_NATIVE_CRITICAL_CUTOFF_SPECTRAL_LIMITS.md)
retains the actual circles, fixes $g$ and takes $\kappa\to0$ with
large cutoff times. Its scalar operator and limits cannot replace
(81.1)--(81.3), which fix $\kappa$, unwrap the phases and take
$\tau\downarrow0$ with $g\tau^{-3/2}$ fixed.
[Four-dimensional spectral reduction, Definition 1.5 and §3](FIB_NATIVE_FOUR_DIMENSIONAL_SPECTRAL_REDUCTION_AND_ATTAINMENT.md)
concerns affine storage/decoder and minimax contracts; its spectral
family is not the horizontal differential operator in (81.2).
The heat blow-up reused here is the local result of
Colin de Verdière--Hillairet--Trélat with the precise density and
localization correspondence in (81.8). Coulhon--Sikora supplies
the off-diagonal implication only after the explicit diagonal
and Davies--Gaffney verifications in Lemmas 82.1--82.2.
The infinite-time integration, varying-domain compactness,
full-domain variational passage and threshold characterization
are the deductions above from these premises. They make no
literature-wide novelty claim. $\square$

## 追加锚（本行以下为增补区）

## 87. Zero-energy inversion for the fixed microscopic source

**Definition 87.1 (critical notation).** Retain all the fixed data,
operators and full complex domains of Definition 81.1. In particular
the heat semigroup is $P_t=e^{-t\mathcal E}$, the potential is exactly
$V=j_0^{-1}\int_1^\infty p_E(t;0,\cdot)dt$, and $a>0$ is not inserted
into that heat clock. Let $M$ denote multiplication by $V^{1/2}$,
and write

$$
v[f]=\|Mf\|_2^2,\qquad
\|f\|_{\mathcal Q_E}^2=\|f\|_2^2+b[f],\qquad
h_c=h_{\chi_c},\qquad H_c=H_{\chi_c}.
\tag{87.1}
$$

The constants $C_*$ and $\chi_c=a/C_*$ remain those of (84.1).
All $L^p$ spaces in §§87--89 use unit Lebesgue Haar measure on the
real Engel group (82.1).

**Theorem 87.2 (compact zero-energy inverse and its operator domain).**
The following integral converges in operator norm from $L^2$ to
$L^2$:

$$
T=\int_0^\infty P_tM\,dt.
\tag{87.2}
$$

It is compact, maps every $u\in L^2$ into $D(\mathcal E)$, and
satisfies

$$
\mathcal E Tu=Mu,\qquad
(\mathcal E+b)^{-1}M\longrightarrow T\quad
\hbox{in operator norm as }b\downarrow0.
\tag{87.3}
$$

Consequently the specific strong limit $K_0$ of (84.4) is compact
and has the norm-convergent representation

$$
K_0=MT=\int_0^\infty MP_tM\,dt,\qquad
\|K_b-K_0\|\longrightarrow0.
\tag{87.4}
$$

Proof. The box $\{N\le R\}$ has volume $16R^7$ for $R>0$.
The bound (82.4), boundedness near the origin and a dyadic annular
sum therefore give

$$
\int V^{3/2}d\xi<\infty,\qquad
\|V^{1/2}\|_{L^3}<\infty,\qquad
V^{1/2}\in L^\infty,\qquad
V^{1/2}(\xi)\longrightarrow0\quad(N(\xi)\to\infty).
\tag{87.5}
$$

Indeed the summands at radius $2^j$ are bounded by
$C2^{7j}2^{-15j/2}=C2^{-j/2}$. Write $m=V^{1/2}$ for the
function defining $M$. The heat kernel has mass one and
$\|p_E(t;0,\cdot)\|_\infty\le c_Et^{-7/2}$. Thus

$$
\|p_E(t;0,\cdot)\|_{3/2}\le c_E^{1/3}t^{-7/6},\qquad
\|P_tMu\|_2\le c_E^{1/3}t^{-7/6}\|m\|_3\|u\|_2.
\tag{87.6}
$$

The second inequality uses Hölder to put $mu$ in $L^{6/5}$,
then Young convolution with exponents $6/5,3/2,2$.
The precise general supplier is Fischer--Ruzhansky,
*Sobolev spaces on graded groups*,
[arXiv:1311.0192v1, §2.1, (2.2)](https://arxiv.org/html/1311.0192v1#S2.SS1).
Its group-convolution hypothesis holds here: (82.1) is a simply
connected graded nilpotent group, its Haar measure is the specified
Lebesgue measure, and $P_t$ is convolution by its left invariant
heat kernel. The group is unimodular, so either convolution
convention gives this same norm estimate. The identity
$5/6+2/3=1+1/2$ checks the exponents. Only Young's inequality
is imported; no general critical-coupling or Sobolev theorem is
being asserted as a new result.

For $0<t<1$ use instead $\|P_tM\|_{2\to2}\le\|m\|_\infty$.
These bounds prove (87.2) and the two explicit estimates

$$
\left\|\int_0^\epsilon P_tMdt\right\|\le\epsilon\|m\|_\infty,
\qquad
\left\|\int_R^\infty P_tMdt\right\|
 \le6c_E^{1/3}\|m\|_3R^{-1/6}\quad(R\ge1).
\tag{87.7}
$$

Norm measurability follows from norm continuity of $P_t$ for
$t>0$, by the spectral theorem. For each such $t$, $P_tM$ is
compact. To see this, replace $m$ by $m\mathbf1_{\{N\le L\}}$.
The resulting integral operator is Hilbert--Schmidt, since

$$
\int\!\int |p_E(t;\eta,\xi)|^2
                |m(\eta)|^2\mathbf1_{\{N(\eta)\le L\}}d\xi d\eta
 =p_E(2t;0,0)\int_{\{N\le L\}}|m|^2d\eta<\infty.
\tag{87.8}
$$

The omitted multiplier has operator norm at most
$\sup_{N>L}|m|\to0$. Hence $\int_\epsilon^R P_tMdt$ is a
norm limit of compact Riemann sums. Letting $\epsilon\downarrow0$
and $R\to\infty$ in (87.7) proves compactness of $T$.

It remains to justify an actual operator inverse on these right
sides. For $u\in L^2$ set $z_R=\int_0^R P_tMu\,dt$.
Spectral calculus, including the continuous value $R$ of
$(1-e^{-R\lambda})/\lambda$ at $\lambda=0$, gives

$$
z_R\in D(\mathcal E),\qquad
\mathcal E z_R=(1-P_R)Mu.
\tag{87.9}
$$

There is no $L^2$ kernel of $\mathcal E$: its form would force
$Xf=Yf=0$, their brackets force all distributional coordinate
derivatives to vanish, and a constant is not in $L^2$ unless zero,
as in the proof of Theorem 84.1. The spectral theorem consequently
gives $P_RMu\to0$ in $L^2$. Since $z_R\to Tu$ in $L^2$,
closedness of $\mathcal E$ proves (87.3)'s domain and equation.
The resolvent integral
$(\mathcal E+b)^{-1}M=\int_0^\infty e^{-bt}P_tMdt$
converges to (87.2) in norm by (87.6)--(87.7) and dominated
convergence. Multiplication by the bounded $M$ proves (87.4),
identifying it with the strong limit already defined in (84.4).
This proves zero-energy compactness and $L^2$ inversion directly;
compactness of the positive-energy $K_b$ alone is not its premise.
$\square$

## 88. Attained simple critical mode on the full complex domain

**Theorem 88.1 (zero-energy Birman--Schwinger equivalence and attainment).**
The largest eigenvalue of $K_0$ is $C_*>0$ and is attained.
There is a normalized strictly positive real vector
$\Phi_c\in D(\mathcal E)$ with

$$
\mathcal E\Phi_c=C_*^{-1}V\Phi_c,\qquad
H_c\Phi_c=0,\qquad
\mu_c:=v[\Phi_c]>0,\qquad
a b[\Phi_c]=\chi_c\mu_c.
\tag{88.1}
$$

The following equalities and correspondence hold on the specified
complex spaces:

$$
\begin{aligned}
\ker H_c&=\mathbb C\Phi_c,\\
\{f\in\mathcal Q_E:h_c[f]=0\}&=\mathbb C\Phi_c,\\
\{f\in\mathcal Q_E:\|f\|_2=1,\ h_c[f]=e(\chi_c)\}
 &=\{e^{i\theta}\Phi_c:\theta\in\mathbb R\},\\
\ker(K_0-C_*I)&\underset{f\mapsto Mf}{\overset{u\mapsto C_*^{-1}Tu}
 {\rightleftarrows}}\ker H_c.
\end{aligned}
\tag{88.2}
$$

The two displayed arrows are inverse linear bijections. In
particular the extremizers of $v[f]/b[f]=C_*$, among nonzero
$f\in\mathcal Q_E$, are exactly the nonzero multiples of $\Phi_c$.
There is no restriction to real test vectors or to vectors with
an ordinary phase gradient.

Proof. By Theorems 84.1 and 87.2, $K_0$ is compact, selfadjoint,
nonnegative and has norm $C_*>0$. The compact spectral theorem
provides a top eigenvector $u\ne0$. It can be chosen nonnegative:
the nonnegative integral kernels in (87.4) give
$\langle |u|,K_0|u|\rangle\ge\langle u,K_0u\rangle
=C_*\|u\|_2^2$, while the norm bound gives the reverse inequality.
Equality in the Rayleigh bound for a nonnegative selfadjoint
operator makes $|u|$ a top eigenvector. Moreover $Tu$ is strictly
positive almost everywhere. For example, for nonzero $u\ge0$,
each $P_tMu$ is strictly positive by (82.3), and its integral on
$1\le t\le2$ is a positive lower bound for $Tu$.

Put $f=C_*^{-1}Tu$. Theorem 87.2 gives $f\in D(\mathcal E)$,
$Mf=u$, and

$$
\mathcal E f=C_*^{-1}Mu=C_*^{-1}Vf.
\tag{88.3}
$$

In particular $f\ne0$ and $H_cf=0$. Normalize this positive
vector to define $\Phi_c$. Bounded strict positivity of $V$
proves $0<\mu_c<\infty$; pairing (88.3) with $f$ proves (88.1).

Conversely if $f\in\ker H_c$, then
$\mathcal E f=C_*^{-1}Vf$. Both $f$ and $C_*^{-1}TMf$
are in $D(\mathcal E)$ and have the same image under
$\mathcal E$, by (87.3). Its injectivity proved above implies
$f=C_*^{-1}TMf$, hence $K_0Mf=C_*Mf$.
The identities $MC_*^{-1}Tu=u$ on the top eigenspace and
$C_*^{-1}TMf=f$ on the critical kernel prove the bijection.
This also excludes a threshold Birman--Schwinger vector whose
reconstruction would fail to be in $L^2$ or in the operator domain.

Simplicity follows from the positive heat kernel argument in
Theorem 84.1, now at the attained bottom zero. More explicitly,
$S_t=e^{-tH_c}$ has a strictly positive kernel, since its
bounded-potential Dyson series has nonnegative terms and contains
$p_E(at;\eta,\xi)>0$. It is an $L^2$ contraction because
$H_c\ge0$. If $u\in\ker H_c$, then
$|u|=|S_tu|\le S_t|u|$ and contraction forces equality in
$L^2$ norm, hence pointwise almost everywhere. Thus
$S_t|u|=|u|$, and the spectral theorem puts $|u|$ in the same
kernel. Equality in the integral triangle inequality with a
strictly positive kernel makes the phase of a nonzero $u$
constant almost everywhere. It also makes $|u|$ strictly positive.
If the complex kernel had dimension at least two, subtracting
a multiple of $\Phi_c$ would give a nonzero kernel vector
orthogonal to $\Phi_c$. Its constant phase and strictly positive
modulus make this impossible. The kernel is therefore exactly
$\mathbb C\Phi_c$, and the bijection proves the same simplicity
at the top of $K_0$.

Finally the representation theorem for the nonnegative closed
form $h_c$ gives
$h_c[f]=\|H_c^{1/2}f\|_2^2$. Its vanishing on
$\mathcal Q_E$ implies $f\in\ker H_c\subset D(H_c)=D(\mathcal E)$,
by spectral calculus. Conversely a kernel vector has zero form.
Since $e(\chi_c)=0$, these observations prove all of (88.2).
The equality $v[f]=C_*b[f]$ is precisely $h_c[f]=0$;
the nonzero denominators were proved in Theorem 84.1.
$\square$

## 89. Linear threshold onset and every tangent near-minimizer

**Theorem 89.1 (right derivative and horizontal form convergence).**
For the fixed source and clock of Definition 81.1,

$$
e(\chi_c+\delta)=-\mu_c\delta+o(\delta)
\quad(\delta\downarrow0),\qquad \mu_c=\int V|\Phi_c|^2d\xi>0.
\tag{89.1}
$$

For every sequence $\delta_n>0$ tending to zero and every complex
$f_n\in\mathcal Q_E$ with $\|f_n\|_2=1$ and

$$
r_n:=h_{\chi_c+\delta_n}[f_n]-e(\chi_c+\delta_n)
\ge0,\qquad r_n/\delta_n\longrightarrow0,
\tag{89.2}
$$

there are constant phases $\theta_n\in\mathbb R$ such that

$$
\|f_n-e^{i\theta_n}\Phi_c\|_{\mathcal Q_E}\longrightarrow0.
\tag{89.3}
$$

In particular this holds for all the normalized supercritical
ground states of Theorem 84.1 as $\chi\downarrow\chi_c$.
The topology in (89.3) contains the global $L^2$ norm and both
horizontal derivative norms, with no spatially varying phase or
centre adjustment. Also $b_{\chi_c+\delta}/\delta\to\mu_c/a$
for the resolvent root in (84.5).

Proof. Testing on $\Phi_c$ gives
$e(\chi_c+\delta)\le-\mu_c\delta$.
For any sequence (89.2) set $v_n=v[f_n]$. Nonnegativity of $h_c$
and $0\le v_n\le\|V\|_\infty$ give

$$
\begin{aligned}
0\le h_c[f_n]
 &=e(\chi_c+\delta_n)+r_n+\delta_nv_n\\
 &\le\delta_n(v_n-\mu_c)+r_n=O(\delta_n),\\
v_n&\ge\mu_c-r_n/\delta_n.
\end{aligned}
\tag{89.4}
$$

It follows from $a b[f_n]=h_c[f_n]+\chi_cv_n$ that
the sequence is bounded in $\mathcal Q_E$. The fixed-field
compactness used in Lemma 83.1 gives, along every subsequence,
a further subsequence converging weakly in $L^2$, strongly in
local $L^2$, and weakly in its two horizontal derivatives to
$f\in\mathcal Q_E$, with $\|f\|_2\le1$.
For clarity, this use fixes $X,Y$ throughout: local form
compactness follows from the fixed-field subelliptic estimate,
and the global derivative limit and Friedrichs-domain membership
follow from the cutoff and convolution argument in Lemma 83.1.
Since $V$ is bounded and vanishes at infinity, local convergence
and the uniform $L^2$ bound imply $v_n\to v[f]$.
Lower semicontinuity and (89.4) imply $h_c[f]=0$.
Theorem 88.1 therefore gives $f=c\Phi_c$, $|c|\le1$, while
the last line of (89.4) gives

$$
|c|^2\mu_c=v[f]=\lim v_n\ge\mu_c.
\tag{89.5}
$$

Thus $|c|=1$. Weak convergence of unit vectors to a unit vector
is strong in global $L^2$. Moreover (89.4) yields
$b[f_n]\to\chi_c\mu_c/a=b[\Phi_c]$.
Weak convergence of the joint derivative vector
$(Xf_n,Yf_n)$ and equality of its limiting norm yield strong
convergence of both derivatives. Every subsequence consequently
has a further subsequence converging in $\mathcal Q_E$ to the
phase orbit of $\Phi_c$. Its distance from this compact orbit
must tend to zero. Choosing a phase attaining that distance
proves (89.3) for the whole sequence.

Take now $f_n=\Phi_{\chi_c+\delta_n}$, whose existence on exactly
this domain is Theorem 84.1. The preceding argument gives
$v_n\to\mu_c$. On these exact minimizers,

$$
-v_n\le e(\chi_c+\delta_n)/\delta_n\le-\mu_c,
\tag{89.6}
$$

where the lower bound is $h_c[f_n]\ge0$. Since the sequence
$\delta_n\to0$ was arbitrary, (89.6) proves (89.1).
The last assertion follows from $e(\chi)=-ab_\chi$ in (84.5).
The use of the attained critical vector supplies the upper bound;
the compact potential and the original full-domain lower bound
prevent loss of mass in this $o(\delta)$ tangent class.
$\square$

## 90. Exactly the disk of native critical weak profiles

**Theorem 90.1 (all possible profiles and attainability on every path).**
Fix any prescribed positive parameter sequences $g_n,\tau_n\to0$
with $\chi_n=g_n\tau_n^{-3/2}\to\chi_c$, and put
$s_n=\sqrt{\tau_n}$. For every normalized complex native sequence
$\psi_n\in\mathcal Q$ satisfying exactly (85.5), let
$f_n=\mathcal U_{s_n}\psi_n$, extended by zero.
Every subsequence has a further subsequence with a weak global
$L^2(d\xi)$ limit, and every such limit belongs to

$$
\mathcal D_c=\{c\Phi_c:c\in\mathbb C,\ |c|\le1\}.
\tag{90.1}
$$

Along any subsequence with $f_n\rightharpoonup c\Phi_c$, one has

$$
\begin{aligned}
f_n&\longrightarrow c\Phi_c&&\text{in }L^2_{\rm loc},\\
\int U_{s_n}|f_n|^2&\longrightarrow |c|^2\mu_c,&
b_{s_n}[f_n]&\longrightarrow |c|^2b[\Phi_c],\\
\|f_n-c\Phi_c\|_2^2&\longrightarrow1-|c|^2.
\end{aligned}
\tag{90.2}
$$

Conversely, for each $c\in\mathbb C$ with $|c|\le1$ and for
each prescribed original parameter sequence just specified,
there exists a normalized complex sequence in the original
two-face native form domain satisfying (85.5) whose rescaled
vectors converge weakly along the whole sequence to $c\Phi_c$.
Thus (90.1) is both the complete possible-limit set and the
attainable set, without choosing a subsequence of the parameters.
In this construction, and in the necessity assertion, the heat
clock, signed fixed nonzero $\kappa$, density $j_0^{-1}$ and
source centre are unchanged.

Proof. Theorem 85.1 gives $\tau_nE_{\tau_n}(g_n)\to0$.
Condition (85.5) and (81.4) therefore give $q_n[f_n]\to0$,
with $q_n$ exactly (83.5). Theorem 85.3 and Theorem 88.1 identify
every weak limit as $c\Phi_c$, $|c|\le1$, and give the potential
and kinetic conclusions along a convergent subsubsequence.
Local compactness makes those conclusions valid on an entire
weakly convergent subsequence: any failure would have a further
subsequence, and then a compactness subsubsequence with the same
weak limit and the asserted conclusions, a contradiction.
The final line of (90.2) follows by expanding the squared norm,
using $\|f_n\|_2=1$ and weak convergence. In particular global
strong convergence to that limit holds exactly when $|c|=1$.

Here is an upper construction that supplies every point of the
disk. Choose real $u_m\in C_c^\infty(\mathbb R^4)$ with
$\|u_m\|_2=1$ and $u_m\to\Phi_c$ in $\mathcal Q_E$.
Such a sequence is supplied by the defining core, followed by
normalization. Then $h_c[u_m]\to0$ and $v[u_m]\to\mu_c$.
Choose also a fixed normalized smooth compact vector $\zeta$.
Its normalized homogeneous dilation of radius $R$ has kinetic
energy $R^{-2}b[\zeta]$. For each $m$ choose $R$ large enough
to make this at most $1/m$. Translate the result in the central
$w$ coordinate far enough to obtain a vector $z_m$ such that

$$
\|z_m\|_2=1,\qquad b[z_m]\le1/m,\qquad
\operatorname{supp}z_m\subset\{N>m\},\qquad
\operatorname{supp}z_m\cap\operatorname{supp}u_m=\varnothing.
\tag{90.3}
$$

Central translation preserves Haar measure and commutes with
$X,Y$ and every $Y_s$, because their coefficients depend only
on $r$. Each of these supports is compact; making the translation
larger ensures disjoint supports including their closures.
In particular $z_m\rightharpoonup0$ in $L^2$ and
$v[z_m]\le\sup_{N>m}V\to0$.

For each fixed $m$, both vectors belong to $\mathcal Q_{s_n}$
for all sufficiently large $n$: their compact height supports
lie strictly between the two moving Dirichlet faces.
The coefficient convergence in (78.4), uniform potential
convergence (82.10), $\chi_n\to\chi_c$ and $s_n\to0$ imply

$$
q_n[u_m]\longrightarrow h_c[u_m],\qquad
q_n[z_m]\longrightarrow h_c[z_m]
\quad\text{at fixed }m.
\tag{90.4}
$$

Choose increasing indices $n_m$ so that for $n\ge n_m$ both
supports lie inside $\Omega_{s_n}$ and both errors in (90.4)
are at most $1/m$. Let $m(n)\to\infty$ increase slowly enough
that $n\ge n_{m(n)}$. Put $d=(1-|c|^2)^{1/2}$ and, for all
sufficiently large $n$, set

$$
F_n=c u_{m(n)}+d z_{m(n)},\qquad
\psi_n=\mathcal U_{s_n}^{-1}F_n.
\tag{90.5}
$$

The finitely many unused indices may be filled with any normalized
native core vectors. Disjoint supports make the norms and all
the form terms add without cross terms, including the two
horizontal derivative terms. Hence $\|F_n\|_2=1$ exactly,
and (90.3)--(90.4) give

$$
q_n[F_n]=|c|^2q_n[u_{m(n)}]+d^2q_n[z_{m(n)}]\longrightarrow0.
\tag{90.6}
$$

Indeed $h_c[z_m]=ab[z_m]-\chi_cv[z_m]\to0$.
The first term in (90.5) converges strongly to $c\Phi_c$;
the second converges weakly to zero and strongly to zero on
every compact set. Thus the whole rescaled sequence has the
required weak limit. Finally (81.4), (90.6) and
$\tau_nE_{\tau_n}(g_n)\to0$ show

$$
\tau_n\bigl(\mathfrak e_{g_n,\tau_n}[\psi_n]
                     -E_{\tau_n}(g_n)\bigr)
 =q_n[F_n]-\tau_nE_{\tau_n}(g_n)\longrightarrow0.
\tag{90.7}
$$

This is precisely the original near-minimizer condition, including
when $c=0$, $|c|=1$, or the prescribed couplings approach criticality
from different sides. It imposes no detuning rate. $\square$

## 91. Quantitative detuning conditions and the smaller native scale

**Proposition 91.1 (a conditional native selection criterion).**
For prescribed $s_n\to0$ and $\delta_n\downarrow0$ put
$\tau_n=s_n^2$, $g_n=(\chi_c+\delta_n)\tau_n^{3/2}$, and define,
on the unchanged $\mathcal Q_{s_n}$,

$$
\begin{aligned}
v_n[F]&=\int U_{s_n}|F|^2,\\
q_n^c[F]&=a b_{s_n}[F]-\chi_cv_n[F]
                           -a\lambda s_n^2\|F\|_2^2,\\
\epsilon_n^c&=\inf_{\|F\|_2=1}q_n^c[F]
 =\tau_nE_{\tau_n}(\chi_c\tau_n^{3/2}),\\
\epsilon_n&=\tau_nE_{\tau_n}(g_n)
 =\inf_{\|F\|_2=1}\{q_n^c[F]-\delta_nv_n[F]\}.
\end{aligned}
\tag{91.1}
$$

Suppose, in addition to the qualitative hypotheses already proved,
that there are numbers $\alpha_n\ge0$ and normalized
$U_n\in\mathcal Q_{s_n}$ with

$$
\epsilon_n^c\ge-\alpha_n,\qquad
\alpha_n=o(\delta_n),\qquad
q_n^c[U_n]=o(\delta_n),\qquad
v_n[U_n]\longrightarrow\mu_c.
\tag{91.2}
$$

Then $\epsilon_n=-\mu_c\delta_n+o(\delta_n)$. For every normalized
complex native sequence whose rescaled vectors $F_n$ satisfy

$$
q_n^c[F_n]-\delta_nv_n[F_n]-\epsilon_n=o(\delta_n),
\tag{91.3}
$$

there are constant phases with
$\|F_n-e^{i\theta_n}\Phi_c\|_2\to0$.
These are sufficient quantitative conditions; no assertion that
they hold for every coupled native path is included.

Proof. The trial vectors in (91.2) give
$\epsilon_n\le-\mu_c\delta_n+o(\delta_n)$.
The lower bound on $q_n^c$ and (91.3) then give

$$
v_n[F_n]\ge\mu_c-o(1).
\tag{91.4}
$$

These sequences satisfy (85.5), since $o(\delta_n)=o(1)$.
Theorem 90.1 applies. Along any weakly convergent subsubsequence,
$v_n[F_n]\to|c|^2\mu_c$ with $|c|\le1$. Inequality (91.4)
forces $|c|=1$, so the convergence is strong in global $L^2$.
The usual subsequence argument gives distance to the phase orbit
tending to zero for the whole sequence.
For the energy conclusion one may take normalized vectors within
$o(\delta_n)$ of each infimum in (91.1); they exist by the
definition of the infimum. Their potential energies tend to
$\mu_c$, and
$\epsilon_n\ge-\alpha_n-\delta_nv_n[F_n]-o(\delta_n)$.
Together with the trial upper bound this proves the asserted law.
$\square$

**Proposition 91.2 (scope of the critical and detuning conclusions).**
Theorem 88.1 settles the critical tangent zero-mode question left
open in Theorem 84.1 and Proposition 86.1. Theorem 89.1 concerns
the tangent forms on the single fixed domain $\mathcal Q_E$.
Theorem 90.1 classifies the native near-minimizer class (85.5),
and does not select the limit of actual native ground states on
an arbitrary coupled critical path. In particular that class
contains, for each such path, sequences with every limiting
mass $|c|^2\in[0,1]$ and every constant complex phase.

The qualitative suppliers (82.10), Proposition 83.2 and (85.2)
give no error relative to an independently prescribed
$\delta_n\downarrow0$. To obtain selection by the criterion
(91.2)--(91.3), the native critical lower error and a critical-mode
recovery error must be $o(\delta_n)$, and the near-minimizer
excess must also be $o(\delta_n)$ in rescaled energy.
No such universal rates are concluded here. Even when those
additional hypotheses hold, they do not supply a finer native
Coulomb $g_n^2$ coefficient. That coefficient requires control
at the rescaled scale

$$
\tau_ng_n^2=(\chi_c+\delta_n)^2\tau_n^4,
\tag{91.5}
$$

and the appropriate finer asymptotics, rather than just an
$o(1)$ or $o(\delta_n)$ error.

All these results retain the real cover and the same fixed
signed $\kappa\ne0$, both native Dirichlet faces, raw source,
$j_0^{-1}$ density factor and heat clock. They imply no physical
spatial-dimension or physical $SO(3)$ selection, no actual-zero-leaf
or torus result, and no uniformity as $\kappa\to0$.

Proof. The critical statements follow from (88.2), (89.2) and
(90.5)--(90.7). In particular (90.7) only tends to zero; its
ratio to $\delta_n$ has not been bounded. The sufficient argument
in Proposition 91.1 uses exactly the stronger ratios in
(91.2)--(91.3), whereas (85.2) only implies
$\epsilon_n^c\to0$ and qualitative recovery. A quantity tending
to zero need not be little-oh of another prescribed vanishing
quantity. Formula (91.5) follows from the exact definition of
$g_n$; control relative to $\delta_n$ does not in general give
control relative to $\tau_ng_n^2$. These are distinct limits.
The geometric and normalization restrictions are precisely those
in Definition 81.1 and Proposition 86.1 and were used unchanged
in (87.5)--(87.6) and (90.4)--(90.7).

The mathematical suppliers for the deductions are the heat and
source estimates of §§81--82, the full-domain compactness and
recovery of §83, the threshold and positive-kernel arguments of
§84, and the native weak-limit bridge of §85. Fischer--Ruzhansky
(2.2) supplies only the explicitly matched Young convolution
inequality in (87.6). Compact spectral theory and closed-form
representation are used in their usual Hilbert-space senses.
The additional deductions are the zero-energy $L^2$ inverse for
this particular source, critical attainment and simplicity,
the tangent onset and profile law, and the exact attainable
native disk. These correspondences make no literature-wide
novelty claim. $\square$

## 追加锚（本行以下为增补区）

## 92. The fixed original observation on its infinite real fibre

**Definition 92.1 (retained carrier and closed domains).** Retain exactly
Definitions 75.1 and 81.1. In particular the signed nonzero $\kappa$,
source $o$, rational fields, raw measure and two height deaths are fixed.
Write $u=(\theta,v)$, $d(k)=(A_\kappa(k),B_\kappa(k))$, and

$$
\pi(k,u,x)=(k,u),\qquad \mathcal B=I\times\mathbb R^2,
\qquad d\bar Y=dk\,du,\qquad R=d(k)\cdot\partial_u.
\tag{92.1}
$$

The retained free form and its operator are

$$
\bar b[h]=\int_{\mathcal B}
 (\varepsilon^2|\partial_kh|^2+|Rh|^2)d\bar Y,
\quad \bar{\mathcal Q}
 =\overline{C_c^\infty(\mathcal B;\mathbb C)}^{(\|\cdot\|_2^2+\bar b)^{1/2}},
\quad \bar B=-(\varepsilon^2\partial_k^2+R^2)_F.
\tag{92.2}
$$

Equivalently, with the unitary Fourier transform in $u$ and
$T_\eta=-\varepsilon^2\partial_k^2+(\eta\cdot d(k))^2$,

$$
\begin{aligned}
\bar{\mathcal Q}
 &=\left\{h:\widehat h(\cdot,\eta)\in H_0^1(I)\text{ a.e.},\
 \int_{\mathbb R^2}\!\int_I
 (\varepsilon^2|\partial_k\widehat h|^2+
 |\eta\cdot d(k)|^2|\widehat h|^2)dk\,d\eta<\infty\right\},\\
D(\bar B)
 &=\left\{h:\widehat h(\cdot,\eta)\in H^2(I)\cap H_0^1(I)
 \text{ a.e.},\quad \int_{\mathbb R^2}
 \|T_\eta\widehat h(\cdot,\eta)\|_2^2d\eta<\infty\right\}.
\end{aligned}
\tag{92.3}
$$

Here and below a displayed domain includes membership of its underlying
$L^2$ space. Both height traces are Dirichlet, all real frequencies are
allowed, and the spaces are complex. The equivalence follows by
Plancherel and closure of the smooth core: truncate the frequency
variable, approximate in height by its Dirichlet core and then use
smooth spatial cutoffs. On bounded frequency sets the potential is
bounded uniformly on $I$, so this approximation is in form norm.
The associated direct integral has the displayed operator domain,
since each bounded-potential interval operator has domain
$H^2\cap H_0^1$. Thus no isotropic phase $H^1$ hypothesis has been added.
The same height Poincare inequality gives $\bar B\ge\lambda$.

For a finite measure $\mu$ on $\mathcal C$ write $\pi_\#\mu$ for its
pushforward. For an integrable density write
$\mathsf M f(k,u)=\int_{\mathbb R}f(k,u,x)dx$.
Pullback of bounded Borel functions is denoted $\pi^*h=h\circ\pi$;
it is not an embedding of the retained $L^2$ space into the native one.

**Theorem 92.2 (all-start killed transport and the correct Green marginal).**
Let $\bar p_t$ be the killed heat kernel of $\bar B$ in raw measure.
For every $t\ge0$, every bounded Borel $h$ and every original start $Y$,

$$
(e^{-tB}\pi^*h)(Y)=(e^{-t\bar B}h)(\pi Y).
\tag{92.4}
$$

Both semigroups in this equation have their killed Markov extensions.
For every finite signed or complex measure $\mu$,

$$
\pi_\#(\mu e^{-tB})=(\pi_\#\mu)e^{-t\bar B}.
\tag{92.5}
$$

In particular, for every start $Y$ and $t>0$,

$$
\int_{\mathbb R}p_t(Y;(k,u,x))dx
       =\bar p_t(\pi Y;(k,u))
\tag{92.6}
$$

as densities. For every $\tau\ge0$ the unshifted killed fields satisfy

$$
G_\tau(Y)=\int_\tau^\infty p_t(o,Y)dt,\qquad
\mathsf M G_\tau=\bar G_\tau
 :=\int_\tau^\infty\bar p_t(\pi o,\cdot)dt,
\qquad \bar B\bar G_\tau=\bar p_\tau(\pi o,\cdot).
\tag{92.7}
$$

At $\tau=0$ the last right side is the raw unit point source
$\delta_{\pi o}$; the field identities are nonnegative extended-integral
identities and the source equation is distributional. At $\tau>0$ the
source has charge $\mathbb P_{k_0}(\zeta>\tau)$, without division by that
charge. The total mass of either field in (92.7) is
$\int_\tau^\infty\mathbb P_{k_0}(\zeta>t)dt<\infty$.

Proof. Project the actual SDE (35.2) of L, obtaining

$$
dK_t=\sqrt2\varepsilon dW_t^1,\qquad
 du_t=\sqrt2d(K_t)dW_t^2,\qquad t<\zeta.
\tag{92.8}
$$

Its coefficients are smooth and bounded on a larger height interval.
Pathwise uniqueness until height exit holds, and the exit time is exactly
the original one, independently of $x$. The projected solution from $Y$
is therefore the solution from $\pi Y$ driven by the same two Brownian
motions. Taking killed expectations proves (92.4) for every bounded
Borel test, including $t=0$. Its symmetric core generator and form are
(92.2), so this is the specified Friedrichs realization, rather than
another boundary extension. Integrating the all-start equality proves
(92.5), first for positive and then for signed and complex measures.
Taking $\mu=\delta_Y$ gives (92.6). These arguments give equality of
transition measures at every start, not only a stationary starting law.

The retained system has a smooth heat density: putting
$s_\kappa=H+\kappa$ and $\alpha_\kappa=\kappa+\kappa^2/H$, direct
calculation from G (25.4) gives

$$
\det(d(k),d'(k))
 =-s_\kappa\left(\frac{k-2\kappa}
                         {2H(k-\alpha_\kappa)}\right)^2\ne0.
\tag{92.9}
$$

Indeed $d=f(k)(s_\kappa-k,-k)$ and the determinant is $-s_\kappa f^2$.
The allowed fixed parameter interval has $s_\kappa>0$, positive
probabilities and no denominator zero. Thus $\partial_k,R,[\partial_k,R]$
span the retained tangent space. This verifies the local smoothing
hypothesis for this quotient. Density equality (92.6) is sufficient
almost everywhere in the target; all-start factorization itself is the
stronger measure statement (92.4).

Tonelli now proves (92.7)'s field equality. Testing the retained heat
equation against $\varphi\in C_c^\infty(\mathcal B)$ and integrating in
time gives its source equation. The term at infinity vanishes: the
absolute expectation of a bounded test is at most its supremum times
the killed height survival probability, which decays exponentially by
the interval Dirichlet expansion. That expansion also proves the finite
mass assertion and the stated source charge. The limit at time zero is
the point evaluation at $\pi o$. There is no threshold factor in (92.7).
$\square$

**Proposition 92.3 (the infinite-fibre qualification).** On the real cover,
a measurable function constant on almost every entire $x$ fibre is in
$L^2(dY)$ only if it vanishes. The map $\mathsf M$ is a contraction
$L^1(dY)\to L^1(d\bar Y)$, but is unbounded as a proposed map
$L^2(dY)\to L^2(d\bar Y)$, even on compact smooth vectors.
Consequently (92.4)--(92.7) do not assert a nonzero fibre-constant
reducing Hilbert subspace or an autonomous quantum subsystem.

Proof. Fubini gives an infinite fibre norm for any nonzero constant.
The $L^1$ statement is the integral triangle inequality. For normalized
$h\in C_c^\infty(\mathbb R)$ with $\int h\ne0$, put
$h_R(x)=R^{-1/2}h(x/R)$ and take a fixed nonzero compact smooth retained
factor $u$. The norm of $u h_R$ is constant, whereas
$\mathsf M(u h_R)=R^{1/2}(\int h)u$. This proves unboundedness. A
normalized uniform measure on the hidden real line does not exist.
The circle isometries in Q §§2--3 and §§10--12, where Q denotes
[Native observation quotient and Green escape](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md),
therefore cannot be transferred to (92.1). $\square$

## 93. Exact finite-scale fibres of the original observation

**Definition 93.1 (retained chart, shear and density).** Let
$d_j=(A_\kappa^{(j)}(k_0),B_\kappa^{(j)}(k_0))$, $j=0,1,2$.
By (92.9) there are unique real numbers $\beta,\gamma$ such that
$d_2=\beta d_0+\gamma d_1$. Put

$$
D_0=|\det(d_0,d_1)|,\qquad
h_*=b_\kappa''(k_0)-\beta b_\kappa(k_0)-\gamma b_\kappa'(k_0),
\qquad \ell_s=\varepsilon^2s^3h_*.
\tag{93.1}
$$

The determinant (76.4) gives $h_*\ne0$ and
$j_0=\varepsilon^4D_0|h_*|$. For $b=(r,Y,Z)\in I_s\times\mathbb R^2$
define the invertible retained chart and the actual retained map by

$$
\begin{aligned}
\Lambda_s(b)&=(k_0+\varepsilon sr,\ s d_0Y+\varepsilon s^2d_1Z),\\
F_s(r,y,z,w)&=(r,\ y+\varepsilon^2s^2\beta w,
                         \ z+\varepsilon s\gamma w),\\
i_s(b,w)&=(r,Y-\varepsilon^2s^2\beta w,Z-\varepsilon s\gamma w,w),\\
n_s&=(0,-\varepsilon^2s^2\beta,-\varepsilon s\gamma,1),
\qquad J_s=\varepsilon^2D_0s^4.
\end{aligned}
\tag{93.2}
$$

Here $n_s$ includes the zero height component. The limiting map is
$F_0(r,y,z,w)=(r,y,z)$, with $i_0(b,w)=(r,Y,Z,w)$.
The labels $Y,Z$ inside $b$ are scalar chart coordinates, distinct from
native points and from the fixed probability parameter $Z$ in G.

**Theorem 93.2 (exact original-observation correspondence).** For every
$s>0$ and every $\xi\in\Omega_s$,

$$
\pi\Xi_s(\xi)=\Lambda_sF_s(\xi),\qquad
F_s^{-1}(b)=\{i_s(b,w):w\in\mathbb R\},\qquad
\Xi_s(\xi+t n_s)=\Xi_s(\xi)+(0,0,0,t\ell_s).
\tag{93.3}
$$

The last equation is in original coordinates $(k,\theta,v,x)$.
The absolute retained Jacobian is $J_s$, and
$J_s|\ell_s|=j_0s^7$. In coordinates $(b,w)$ the full rescaled density is
exactly $db\,dw$. Thus for every integrable $f$ on $\Omega_s$,

$$
\mathsf M_s f(b)=\int_{\mathbb R}f(i_s(b,w))dw
\tag{93.4}
$$

is its pushforward density under the original observation in this chart.
For every native amplitude $\psi\in L^2(dY)$, with $f=\mathcal U_s\psi$,

$$
J_s\int_{\mathbb R}|\psi(\Lambda_s b,x)|^2dx
                 =\mathsf M_s(|f|^2)(b).
\tag{93.5}
$$

The exact projected scaled fields are $\partial_r$ and

$$
\bar Y_s=
 (v_{s,1}+\varepsilon^2s^2\beta v_{s,3})\partial_Y
 +(v_{s,2}+\varepsilon s\gamma v_{s,3})\partial_Z.
\tag{93.6}
$$

They converge in $C^\infty$ on bounded height intervals to
$\partial_r$ and $\partial_Y+r\partial_Z$. Their tangent quotient is
therefore the three-coordinate Heisenberg heat operator

$$
\bar{\mathcal E}
 =-\partial_r^2-(\partial_Y+r\partial_Z)^2
\tag{93.7}
$$

with its complex Friedrichs horizontal form closure on
$L^2(\mathbb R^3,db)$. Its weights are $(1,1,2)$ and homogeneous
dimension four, while the full Engel weights remain $(1,1,2,3)$
and homogeneous dimension seven.

Proof. Project (78.1) onto its first two phase components and substitute
$d_2=\beta d_0+\gamma d_1$. Factoring $s d_0$ and
$\varepsilon s^2d_1$ gives (93.3)'s first identity. Solving its two
linear equations gives precisely $i_s$. In the full phase space,
$c_2-\beta c_0-\gamma c_1=(0,0,h_*)$; the invertible determinant in
(76.4) proves it is nonzero. This proves the translation identity,
including the sign of $\ell_s$. Taking determinants gives $J_s$ and
$J_s|\ell_s|=j_0s^7$. The shear $(b,w)\mapsto i_s(b,w)$ has determinant
one. Changing variables first along the hidden line and then on the
base proves (93.4)--(93.5), using the exact unitary factor in (81.1).
Applying $\partial_r,Y_s$ to the three components of $F_s$ gives
(93.6); (78.4) gives its stated limit. The two limiting fields and
their bracket $\partial_Z$ span three dimensions, and dilation
$(r,Y,Z)\mapsto(Rr,RY,R^2Z)$ gives the stated weights. This is the
projection of the Engel fields in (81.2), not a redefinition of the
original observation as $F_0$ at positive $s$. $\square$

**Theorem 93.3 (positive-time heat and source correspondence).** Write
$\bar p_H$ for the heat kernel of (93.7) relative to $db$, and set

$$
\bar P_s(t;0,b)=J_s\bar p_{s^2t}(\pi o,\Lambda_s b).
\tag{93.8}
$$

Extend densities by zero outside their moving height intervals.
For every fixed $t>0$,

$$
\bar P_s(t;0,\cdot)=\mathsf M_s P_s(t;0,\cdot)
 \longrightarrow\bar p_H(t;0,\cdot)\quad\hbox{in }L^1(db),
\tag{93.9}
$$

as $s\downarrow0$. The same convergence holds in
$L^1([\delta,T]\times\mathbb R^3)$ for every $0<\delta<T<\infty$,
and after inserting the factor $e^{\lambda s^2t}$.
In particular the pushed rescaled source
$j_0^{-1}e^{\lambda s^2}\bar P_s(1;0,b)$ tends in $L^1$ to
$j_0^{-1}\bar p_H(1;0,b)$. Its total mass tends to $1/j_0$.
The original source before this change of density has charge tending
to one, exactly as in (81.7).

Proof. Formula (92.6), $dx=|\ell_s|dw$ along each fibre, and
$J_s|\ell_s|=j_0s^7$ prove the equality in (93.9). By (81.8),
$P_s(t;0,\xi)\to p_E(t;0,\xi)$ locally uniformly at each $t>0$.
Its total mass is $\mathbb P_{k_0}(\zeta>s^2t)\to1$, while the complete
Engel diffusion has mass one. Nonnegativity and convergence of total
masses therefore upgrade this local convergence to global $L^1$,
by the minimum-of-densities argument used in (81.7).

The shear $i_s$ tends to the identity and preserves four-dimensional
Lebesgue measure. Its pullback converges strongly to the identity on
$L^1$: prove this first for a continuous compactly supported function,
whose sheared supports lie in one compact set, and then use density
and its norm-one action. Consequently

$$
\|\mathsf M_sP_s(t)-\mathsf M_0p_E(t)\|_1
 \le\|P_s(t)-p_E(t)\|_1
       +\|p_E(t)\circ i_s-p_E(t)\|_1\longrightarrow0.
\tag{93.10}
$$

Projecting the complete Engel SDE drops its last stochastic integral
and gives $dr=\sqrt2dW^1$, $dY=\sqrt2dW^2$,
$dZ=\sqrt2r\,dW^2$. Uniqueness and the symmetric core identify its
kernel with $\bar p_H$, proving $\mathsf M_0p_E=\bar p_H$.
The $L^1$ differences above are bounded by two; integration over
$[\delta,T]$ and dominated convergence prove the spacetime assertion.
The threshold factors tend uniformly to one on that interval. At
time one their total mass is
$j_0^{-1}e^{\lambda s^2}\mathbb P_{k_0}(\zeta>s^2)$, which proves
the source statements. This argument controls the entire hidden
fibre for positive finite times through total mass; it does not
integrate a local limit over an uncontrolled fibre. $\square$

## 94. Native divergence and a finite tangent threshold marginal

**Theorem 94.1 (the original threshold marginal is infinite).** Fix any
$\tau>0$, $k\in I$ and $u\in\mathbb R^2$. Let $N$ be the upper
$2\times2$ principal block of the positive tensor $M=M_\kappa$ in L §36.
Then

$$
\int_{-R}^R W_\tau(k,u,x)dx
 =\frac{\phi(k_0)\phi(k)}{2\pi\sqrt{\det N}}\log R+O(1)
 \quad(R\to\infty).
\tag{94.1}
$$

The remainder may depend on the fixed $\tau,k,u$.
In particular $\mathsf M W_\tau(k,u)=+\infty$ at every retained point.
This holds for every fixed positive cutoff, however small, with the
original source and without a surviving-charge renormalization.

Proof. The fixed-cutoff tail (70.3) gives, as $|x|\to\infty$ at fixed $u$,

$$
W_\tau(k,u,x)
 =\frac{\phi(k_0)\phi(k)}
 {4\pi\sqrt{\det M}\sqrt{(M^{-1})_{33}}}\frac1{|x|}
       +O(|x|^{-2}).
\tag{94.2}
$$

Indeed the square of its anisotropic distance is
$(M^{-1})_{33}x^2+O(|x|)+O(1)$, and the error already in (70.3) is
$O(|x|^{-3})$. The field is bounded on the remaining finite interval
because $\tau>0$. Integrate (94.2) on both half-lines. The cofactor
identity $\det M\,(M^{-1})_{33}=\det N$ proves (94.1). Its coefficient
is strictly positive at every interior height. The argument uses the
actual full-field tail, not just a covariance match of projected heat.
$\square$

**Theorem 94.2 (finite tangent marginal and noncommuting limits).** Put

$$
\bar V(b)=\int_{\mathbb R}V(i_0(b,w))dw.
\tag{94.3}
$$

It is finite and positive at every $b\in\mathbb R^3$, and

$$
\bar V(b)=\frac1{j_0}\int_1^\infty\bar p_H(t;0,b)dt,
\qquad \bar{\mathcal E}\bar V=\frac1{j_0}\bar p_H(1;0,\cdot)
\tag{94.4}
$$

in distributions. The right side has Lebesgue mass $1/j_0$.
For every fixed $b$ and every sufficiently small $s>0$,

$$
\int_{\mathbb R}U_s(i_s(b,w))dw
  =\frac{J_s}{j_0s^2}\int_{\mathbb R}
                  W_{s^2}(\Lambda_s b,x)dx=+\infty.
\tag{94.5}
$$

Nevertheless, for every $L<\infty$,

$$
\lim_{s\downarrow0}\int_{-L}^L U_s(i_s(b,w))dw
       =\int_{-L}^L V(i_0(b,w))dw.
\tag{94.6}
$$

Convergence is uniform for $b$ in any fixed compact set. Hence the
iterated limit with $s\downarrow0$ first and then $L\to\infty$ is
$\bar V(b)<\infty$, whereas the opposite order is $+\infty$.
There is no integrable majorant along these full finite-scale fibres
uniformly for small $s$. For each fixed $1<T<\infty$, however, the
fibre marginal of the field restricted to rescaled times $[1,T]$
converges in $L^1(db)$ to
$j_0^{-1}\int_1^T\bar p_H(t;0,b)dt$.

Proof. From (82.4),
$V(r,Y,Z,w)\le C(1+|w|^{1/3})^{-5}$, an integrable function of $w$.
This proves finiteness in (94.3), uniformly in $b$; positivity is strict.
Tonelli and the complete Engel projection in Theorem 93.3 give the
first identity in (94.4). One can check its time tail directly: integrate
(82.3), using $d_E\ge cN$, to obtain

$$
\sup_b\bar p_H(t;0,b)
 \le Ct^{-7/2}\int_{\mathbb R}
          e^{-c|w|^{2/3}/t}dw\le Ct^{-2}.
\tag{94.7}
$$

This is integrable on $[1,\infty)$. Integrating the retained heat
equation against a compact smooth test therefore proves the source
equation in (94.4), with no term at infinity. Its charge uses the
conservative projected heat, already established by its complete SDE.

Change variables along the exact fibre in (93.3). Since
$s^5/|\ell_s|=J_s/(j_0s^2)$, this proves (94.5), whose divergence is
Theorem 94.1 at the actual finite cutoff $s^2$. On a bounded $w$ interval
and a compact set of $b$, the points $i_s(b,w)$ stay in one compact set,
inside both moving faces eventually. Uniform convergence (82.10) and
continuity of $V$ then prove (94.6). Monotone convergence in $L$ gives
the two different iterated limits. An integrable uniform majorant would
make (94.5) finite and is therefore impossible. Finally (81.5), Tonelli
and (93.9) on $[1,T]$ prove the asserted finite-time $L^1$ convergence.
No exchange of infinite time and infinite fibre has entered that claim.
$\square$

**Proposition 94.3 (separate Green conventions).** The finite native
marginal in (92.7) and the infinite marginal in (94.1) concern different
fields of the same free operator. Specifically $BG_\tau=p_\tau(o,\cdot)$,
whereas $(B-\lambda)W_\tau=e^{\lambda\tau}p_\tau(o,\cdot)$.
The finite tangent field in (94.4) is the cutoff field of the complete
Heisenberg quotient, not the fibre integral of any fixed $U_s$.
The finite-time heat convergence in Theorem 93.3 and the full-potential
uniform convergence in (82.10) do not imply the contrary assertion.

Proof. The two source equations are (92.7) and (75.4). Killing makes
$\int_\tau^\infty\mathbb P(\zeta>t)dt$ finite, while the threshold
shift cancels that height gap and (94.1) proves divergence on a single
hidden line. The incompatibility with exchanging the fibre integral
and microscopic limit is the explicit pair of iterated limits in
Theorem 94.2. Thus it persists despite uniform convergence of the
unintegrated fields. $\square$

## 95. No integral transport slice and a scaled interaction escape

**Theorem 95.1 (original transport has no invariant three-dimensional slice).**
There is no nonempty $C^2$ immersed three-dimensional submanifold of
$\mathcal C$ everywhere invariant under both original local transport
flows $P=\partial_k$ and $Q=c_\kappa(k)\cdot\partial_q$.
In particular no section of the fixed observation (92.1) is such a slice.
The original transport does project to $\partial_k,R$ with its original
height legality constraints; a projected transport family is not an
integral slice of the full one.

Proof. A submanifold invariant under the local flows is tangent to
$P,Q$ and to their successive Lie brackets. Locally this follows by
pulling a defining function back to a submanifold chart: its derivatives
along tangent fields vanish, so their commutator is tangent. Alternatively
the four-flow commutator curve has leading displacement equal to the
bracket and stays in the invariant submanifold. Repeating with $P$
gives tangency to

$$
P,\quad Q,\quad [P,Q]=c_\kappa'(k)\cdot\partial_q,
\quad [P,[P,Q]]=c_\kappa''(k)\cdot\partial_q.
\tag{95.1}
$$

Their determinant is the nonzero expression (76.4); their span has
dimension four everywhere. This contradicts a three-dimensional tangent
space. For the bracket iteration on a $C^2$ invariant manifold, one can
also use invariance under the smooth ambient flows directly: conjugating
$Q$ by arbitrary sufficiently small $P$ flows keeps a tangent vector,
and its first and second differences converge to $c'$ and $c''$ in the
closed tangent space at the point. This avoids requiring a third
submanifold derivative. Projection of the original vector fields is
immediate from their coefficients' independence of $x$. A common control
has the same height path for all starts in a fibre, so every intermediate
height refusal is retained. No independent hidden actuator is inferred.
$\square$

**Theorem 95.2 (same original observation and a nonzero scaled energy gap).**
There exist a normalized real $f\in C_c^\infty(\mathbb R^4)$ and one
finite $L>0$ with the following properties. For every sufficiently small
$s>0$ put

$$
f_s^0=f,\qquad f_s^L(\xi)=f(\xi-Ln_s),\qquad
\psi_s^j=\mathcal U_s^{-1}f_s^j\quad(j=0,L).
\tag{95.2}
$$

Both vectors are normalized members of the original smooth compact core,
hence of the entire native form and operator domains. They have exactly
the same original retained probability marginal, the same partial trace
over $L^2(dx)$, the same integrable amplitude marginal and the same
kinetic energy $T$. Their projected free killed probability observations
agree at every subsequent time and for every bounded Borel retained test.
For the unchanged fixed-source potential, there is a number $\Delta>0$
such that

$$
s^5\bigl(V_{s^2}[\psi_s^0]-V_{s^2}[\psi_s^L]\bigr)\longrightarrow\Delta.
\tag{95.3}
$$

In particular, for every prescribed positive coupling family with
$\chi_s=g_s s^{-3}\to\chi_0\in(0,\infty)$,

$$
s^2\bigl(\mathfrak e_{g_s,s^2}[\psi_s^L]
              -\mathfrak e_{g_s,s^2}[\psi_s^0]\bigr)
                      \longrightarrow\chi_0\Delta>0.
\tag{95.4}
$$

This is W's prescribed microscopic energy scale and original
observation, including at $\chi_0=\chi_c$; these vectors are not asserted
to be ground states or near-minimizers.

Proof. Choose any nonzero real compact smooth normalized $f$, with support
away from the origin if desired. Strict positivity of $V$ gives
$v[f]>0$. Its decay in (82.4) and dominated convergence imply

$$
v[f(\cdot-Le_w)]\longrightarrow0\quad(L\to\infty),
\qquad e_w=(0,0,0,1).
\tag{95.5}
$$

Choose a finite positive $L$ for which that value is smaller than
$v[f]/2$, and set $\Delta=v[f]-v[f(\cdot-Le_w)]>0$.
Since $n_s\to e_w$, the vectors in (95.2) have supports in one compact
set for small $s$, strictly between the two moving height faces. They
are smooth, compact and normalized. In original coordinates the exact
relation (93.3) is

$$
\psi_s^L(k,u,x)=\psi_s^0(k,u,x-L\ell_s).
\tag{95.6}
$$

An $x$ translation preserves the raw norm and every horizontal derivative,
so it preserves $T$ on its full closed domain. It leaves both the
probability integral $\int|\psi|^2dx$ and the amplitude integral
$\int\psi dx$ unchanged for this integrable pair. It is a unitary acting
only on the hidden factor in
$L^2(\mathcal B)\otimes L^2(\mathbb R,dx)$, so it also leaves the partial
trace unchanged. The projected probability-future assertion follows
from (92.5), applied to their equal pushed initial probability measures.
It refers to diffusion of those measures, not to squaring a propagated
amplitude. The full free operator commutes with this translation as well.

The exact normalization gives
$s^5V_{s^2}[\psi_s^j]=\int U_s|f_s^j|^2$.
Uniform convergence (82.10), convergence of the compact translations in
$L^2$, and boundedness of $V$ prove (95.3). Equal kinetic energies make
the difference of full energies exactly the attractive difference times
$g_s$ with the sign displayed in (95.4). Multiplying by $s^2$ and using
$g_ss^{-3}\to\chi_0$ proves that formula. Neither the source nor its
centre has been translated; only the trial vector has. $\square$

**Proposition 95.3 (conditional interaction and exact classical descent).**
For a normalized complex $\psi\in\mathcal Q$ and fixed $\tau>0$, set
$m(k,u)=\int|\psi(k,u,x)|^2dx$. On fibres with $m>0$ put
$\nu_{k,u}(dx)=|\psi(k,u,x)|^2dx/m(k,u)$. Then exactly

$$
V_\tau[\psi]=\int_{\mathcal B}m(k,u)
          \left(\int W_\tau(k,u,x)\nu_{k,u}(dx)\right)d\bar Y.
\tag{95.7}
$$

Fibres with $m=0$ contribute zero. Thus a finite conditional field
expectation, rather than the infinite Haar marginal (94.1), supplies
the potential statistic. For any bounded smooth real multiplier $U$
on the original carrier, the killed Feynman--Kac family of
$a(B-\lambda)-gU$, $g>0$, factors through $\pi$ on all bounded Borel tests
and every start if and only if $U$ is constant on every $x$ fibre.
The original $U=W_\tau$ fails this criterion for every $\tau>0$.

Proof. Equation (95.7) is Fubini; boundedness of $W_\tau$ makes it finite
on the entire form domain, without an extra derivative requirement.
If $U=\bar U\circ\pi$, the Feynman--Kac expression is

$$
e^{a\lambda t}\mathbb E_Y
 \left[\exp\left(g\int_0^tU(Y_{av})dv\right)
                      h(\pi Y_{at});\ at<\zeta\right].
\tag{95.8}
$$

The projected path in (92.8) makes it depend only on $\pi Y$.
Conversely take $h=1$. At every interior start its derivative at zero
is $a\lambda+gU(Y)$. To justify it, stop first in a small interior
height interval. The probability of exiting that interval by time $at$
is $o(t)$ by the Brownian reflection bound. Continuity and boundedness
of $U$ then give the derivative by dominated convergence. Thus all-start
factorization forces equal $U$ at all points of each fibre. The original
$W_\tau$ is smooth, bounded and positive by the positive-time heat
regularization; at fixed $k,u$ it tends to zero as $|x|\to\infty$ by
(70.3). It is therefore not fibre constant. This proves a scalar
interacting diffusion-response obstruction for the original field.
The kinetic factor $a$ changes the propagation clock in (95.8), while
the field itself still uses the independent $B$ clock. $\square$

## 96. Quantum futures, suppliers and the remaining realization conditions

**Theorem 96.1 (a separate original-domain quantum obstruction).** Fix any
$g,\tau>0$ and the original selfadjoint
$H=a(B-\lambda)-gW_\tau$ on $D(B)$. There are normalized smooth compact
vectors with the same partial trace over the hidden real line whose
retained quantum position expectations under $e^{-itH}$ differ at
arbitrarily small positive times. This already holds for $g=0$.
It is distinct from classical probability-heat factorization (92.5).

Proof. Choose normalized real
$u\in C_c^\infty(I\times\mathbb R^2)$ and
$h\in C_c^\infty(\mathbb R)$, and put

$$
\Psi_\nu(k,\theta,v,x)=u(k,\theta,v)h(x)e^{i\nu x},
\qquad \nu\in\mathbb R.
\tag{96.1}
$$

All these vectors are in $D(B)=D(H)$, with both height traces zero;
their partial traces are the same rank-one retained state
$|u\rangle\langle u|$. Let $M_\varphi$ multiply by the bounded real
function $\varphi(\theta)=\arctan\theta$. It maps these core vectors
to the core. Use inner products conjugate linear in the first slot.
For a vector in $D(H)$ the derivative of its bounded-observable
expectation is $i\langle\Psi,[H,M_\varphi]\Psi\rangle$, interpreted
as the difference of its two well-defined domain pairings.
Here the potential and the threshold constant commute with
$M_\varphi$. If $Q=A_\kappa\partial_\theta+B_\kappa\partial_v
+b_\kappa\partial_x$, the remaining commutator on the core is

$$
[B,M_\varphi]=-M_{Q^2\varphi}-2M_{Q\varphi}Q,
\qquad Q\varphi=\frac{A_\kappa(k)}{1+\theta^2}.
\tag{96.2}
$$

The height commutator vanishes since $\varphi$ is independent of height.
Integration over $x$ eliminates the real term $\int hh'=0$.
All terms independent of $\nu$ cancel on subtracting the $\nu=0$
expectation. The result is exactly

$$
\left.\frac d{dt}\right|_{t=0}
 \left(\langle e^{-itH}\Psi_\nu,M_\varphi e^{-itH}\Psi_\nu\rangle
      -\langle e^{-itH}\Psi_0,M_\varphi e^{-itH}\Psi_0\rangle\right)
 =2a\nu\int_{\mathcal B}
      \frac{b_\kappa(k)A_\kappa(k)}{1+\theta^2}|u|^2d\bar Y.
\tag{96.3}
$$

On the fixed admissible interval both $b_\kappa$ and $A_\kappa$ in
G (25.4) are strictly positive. The integral is therefore positive.
For any $\nu\ne0$ the derivative is nonzero, while the difference at
time zero is zero, proving separation for all sufficiently small
positive times. This proves failure of a universal autonomous reduced
quantum evolution for this partial trace directly, without inferring it
from an energy difference. It does not claim that the particular
translation pair (95.2) has different reduced quantum futures.
$\square$

**Proposition 96.2 (scalar spectral information for the scaled pair).**
At every sufficiently small fixed $s$, and every $g_s>0$, the two vectors
in (95.2) have different spectral probability measures for the actual
operator $H_s=a(B-\lambda)-g_sW_{s^2}$. Their scalar heat
self-correlations $\langle\psi_s^j,e^{-tH_s}\psi_s^j\rangle$ differ
for all sufficiently small positive $t$ (the time interval may depend
on $s,g_s$). This assertion supplies scalar full-operator future
information, not a reduced-state future claim for that pair.

Proof. Formula (95.3) is positive for all sufficiently small $s$.
The vectors are in $D(H_s)$ and their energy expectations differ by
$g_s(V_{s^2}[\psi_s^0]-V_{s^2}[\psi_s^L])>0$. The first moments of
their spectral measures therefore differ. Since $H_s$ is bounded
below, spectral calculus differentiates each scalar heat correlation
at zero from the right, giving derivative
$-\langle\psi_s^j,H_s\psi_s^j\rangle$.
For example, after shifting $H_s$ to be nonnegative, the difference
quotients are bounded in absolute value by the first spectral moment;
that moment is finite for a vector in $D(H_s)$. The derivative of the
difference is nonzero, proving the assertion. No uniform quantum-time
limit or reduced-density conclusion is used. $\square$

**Definition 96.3 (supplier correspondence and unresolved stronger claims).**
The general mechanisms of quotient heat, hidden interaction and
compressed response belong to Q §§2--8, while Q §§10--13 concern the
four-full/three-retained torus family. The all-start generator criterion
belongs also to [Free diffusion quotient rigidity](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md)
§§3--5. The infinite-Haar-fibre and conditional-energy distinctions in
[Recursive holographic boundary geometry III](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md)
§§81--85 use their different carriers and are not native realization
suppliers for this real-cover family. The full-domain native spectral
statements, Engel integrated-field convergence, critical mode and profile
classification remain precisely §§70--91; none is reproved or strengthened
by taking a retained marginal.

The added source-specific correspondence is (93.1)--(93.6), the positive
finite-time pushforward (93.9), the original logarithmic divergence
versus finite tangent marginal (94.1)--(94.6), and the exact-fibre scaled
escape (95.2)--(95.4). The slice and quantum obstructions use the
unchanged rational native fields, not a generic replacement model.
These are repository-derived deductions. Plancherel, direct integrals,
form representation, Fubini, spectral calculus and stochastic uniqueness
are mature intermediate tools. The primary small-time supplier is exactly
Colin de Verdiere--Hillairet--Trelat, Theorem B and localization
Theorem 3.2, with the field, density, clock and interior-source
hypotheses checked in (78.7) and (81.8). It supplies local positive-time
heat convergence only. The global upgrade in (93.9) additionally uses
convergence of total killed masses; the integrated-field supplier
(82.10) additionally uses its explicit time and spatial tails.
No Folland attribution, general Green-limit transfer, literature-wide
absence, originality or kernel-certification claim is imposed here.

For a native operational application, lawful ray and prefix reachability
from G and its original transport sources remains distinct from preparing
an analytic $L^2$ amplitude or acquiring its conditional density. The
private polygon and rectangle lemmas consumed by
`FiniteRectangleTransport.finite_rectangles_realize` concern individual
finite-dimensional phase/probability transport; they do not prepare
(95.2) or (96.1). The quantum payload fibres and acquisition/absorbing-clock
conditions in [Joint transfer and coherence interface geometry](FIB_NATIVE_JOINT_TRANSFER_COHERENCE_INTERFACE_GEOMETRY.md)
retain their own source contracts and supply no spatial or amplitude
realization for the present differential operator.

The source-to-amplitude preparation/acquisition map, any physical-space
interpretation, uniformity as $\kappa\to0$, the actual zero leaf, a torus
replacement, cutoff removal, a global unshifted-Green microscopic
pushforward limit, and uniform quantum-time or reduced spectral limits
are separate unresolved obligations here. The infinite threshold-fibre
exchange is specifically refuted by Theorem 94.2. The critical detuning
rates and finer native energy obligations remain exactly (91.2)--(91.5).
A retained coordinate count of three, Heisenberg homogeneous dimension
four, Engel homogeneous dimension seven, the rank-three long-time phase
tensor and a three-dimensional isotropic Euclidean physical space are
different predicates. None of the heat, form, transport or quantum
statements above identifies the last predicate with any of the others.

## 追加锚（本行以下为增补区）


## 97. An exact rational comparison and its integrated source error

**Definition 97.1 (comparison coordinates for the same native operator).**
Retain all the data and full complex domains of Definitions 75.1 and
81.1. Put $d_0=k_0-\alpha_\kappa>0$, $\beta_s=\varepsilon s/d_0$,
and, for $z=(y,z_2,w)$, define

$$
L_s=\begin{pmatrix}1&\beta_s&0\\0&1&2\beta_s\\0&0&1\end{pmatrix},
\quad \mathscr L_s(r,z)=(r,L_sz),\quad
(\mathcal T_sF)(r,z)=F(\mathscr L_s(r,z)),\quad
\widetilde U_s=U_s\circ \mathscr L_s.
\tag{97.1}
$$

It preserves Lebesgue measure, fixes the source and both height faces,
and is a constant linear change of the three real phase coordinates.
Write $u(r)=(1,r,r^2/2)$ and
$Y=u(r)\cdot\partial_z$. Then, exactly,

$$
\begin{aligned}
v_s(r)&=(1,r,r^2/[2(1+\beta_sr)]),\\
\widetilde b_s[f]&:=b_s[\mathcal T_s^{-1}f]
 =\int_{\Omega_s}\left(|\partial_rf|^2+
                   (1+\beta_sr)^{-2}|Yf|^2\right)dr\,dz.
\end{aligned}
\tag{97.2}
$$

These are identities of closed forms on
$\mathcal T_s\mathcal Q_s$, not additional regularity assumptions.
In particular no estimate of the three separate phase derivatives
is used. To verify the identities, each component of the original
$c_\kappa(k)$ in G (25.4) is an affine function of $k$ plus a
constant divided by $k-\alpha_\kappa$. Consequently its exact Taylor
identity, with $h=k-k_0$, is

$$
c_\kappa(k_0+h)=c_0+h c_1+
                 \frac{h^2}{2(1+h/d_0)}c_2.
\tag{97.3}
$$

Substitution in (78.1) gives the first line of (97.2), and
$L_su(r)=(1+\beta_sr)v_s(r)$ gives its second line on the smooth
core. Unitarity and closure give the stated full-domain identities.
The denominator stays positive on $I_s$, since the original
admissible interval has $k-\alpha_\kappa>0$.

**Lemma 97.2 (quantitative complete-field comparison in this chart).**
There are constants $C,c_0,s_0>0$, depending only on the fixed native
data, such that for $0<s<s_0$, $R\ge1$ and $sR\le c_0$,

$$
\|\widetilde U_s-V\|_\infty
 \le C(sR+R^{-5}+s^2+s^5).
\tag{97.4}
$$

Both fields are extended by zero according to Definition 81.1 when
appropriate. In particular, choosing $R=s^{-1/6}$ gives

$$
\|\widetilde U_s-V\|_\infty\le Cs^{5/6}.
\tag{97.5}
$$

The heat clock and raw source factor in this estimate remain exactly
$B$ and $j_0^{-1}$. It compares the complete infinite-time fields.

Proof. We give the quantitative step for this rational family.
Let $\widetilde P_s(t;0,(r,z))=P_s(t;0,\mathscr L_s(r,z))$.
The unchanged Jacobian and (81.5) give
$\widetilde U_s=j_0^{-1}\int_1^\infty
 e^{\lambda s^2t}\widetilde P_s(t;0,\cdot)dt$.
Choose $c_0$ small enough that $[-R,R]\subset I_s$ and
$|\beta_s|R\le1/4$. Kill both comparison diffusions also at $r=\pm R$,
and denote their strip kernels by $\widetilde P_s^R$ and $p_E^R$.
This extra killing is used only to compare kernels; the field in
(97.4) retains the original two faces.

Here is the conditional Gaussian comparison, with its constants
independent of $R,t,r,z$. The height path is $H_v=\sqrt2 B_v^1$.
Condition on its bridge from $0$ to $r$ in time $t$ and on its staying
in $(-R,R)$. The independent driver $B^2$ gives the phase covariances
$2M_s$ and $2M_0$, where

$$
M_s=\int_0^t(1+\beta_sH_v)^{-2}u(H_v)u(H_v)^{\mathsf T}dv,
\qquad M_0=\int_0^tu(H_v)u(H_v)^{\mathsf T}dv.
\tag{97.6}
$$

The same height bridge is used in both matrices. They are positive
definite almost surely: a nonconstant continuous bridge has an interval
in its range, and a quadratic polynomial vanishing on that range is
zero. On the survived event,
$(1-C sR)M_0\le M_s\le(1+C sR)M_0$ in matrix order.
For the Gaussian density
$\gamma_M(z)=(4\pi)^{-3/2}(\det M)^{-1/2}
 e^{-z^{\mathsf T}M^{-1}z/4}$ this implies

$$
|\gamma_{M_s}(z)-\gamma_{M_0}(z)|
 \le C sR(\det M_0)^{-1/2}\qquad(z\in\mathbb R^3).
\tag{97.7}
$$

Indeed conjugate the matrices by $M_0^{-1/2}$ and interpolate from
$\mathrm{Id}$ to $M_0^{-1/2}M_sM_0^{-1/2}$. All eigenvalues stay in
one fixed compact subset of $(0,\infty)$. Differentiating the determinant
and exponential bounds the derivative by
$C sR(\det M_0)^{-1/2}(1+|M_0^{-1/2}z|^2)
 e^{-c|M_0^{-1/2}z|^2}$, which proves (97.7).
Averaging over the bridge, including its unnormalized survival
indicator and the free height density, now gives

$$
|\widetilde P_s^R(t;0,(r,z))-p_E^R(t;0,(r,z))|
 \le C sR\,p_E(t;0,(r,0))\le C sR\,t^{-7/2}.
\tag{97.8}
$$

The inverse-determinant expectation is finite by the canonical smooth
kernel bound (82.3). More explicitly the Gaussian-mixture formula
holds almost everywhere in $z$; Fatou along such points tending to zero
bounds the zero-phase mixture by the continuous kernel's value at zero.
This is the same justification used for the native bridge formula
G (32.7)--(32.8), now also for bridges with different terminal heights.
Thus (97.8) does not posit an inverse-moment estimate without evidence.

For completeness, removing the extra strip killing costs, for
$|r|\le R/2$ and $0<t\le s^{-2}$, at most

$$
C t^{-7/2}e^{-cR^2/t}
\tag{97.9}
$$

for each kernel. To see this, split the paths exiting the strip into
those whose first exit occurs before $t/2$ and the remainder. For the
first set, the strong Markov property at exit leaves a kernel with time
at least $t/2$, bounded by $Ct^{-7/2}$ by the rescaled all-height
estimate (76.1), or by (82.3) for the canonical process. The probability
of the height reaching $\pm R$ before $t/2$ is at most
$Ce^{-cR^2/t}$ by the Brownian reflection bound. For the remainder,
reverse the bridge. Symmetry of each Lebesgue kernel makes the reversed
process the same process started at the terminal point, and its height
starts at distance at least $R/2$ from the strip boundary. Apply the
same first-half argument. This bounds the union and proves (97.9).
For the native kernel the further original killing only decreases the
exit probability; its remaining-time bound is valid because
$s^2(t-v)\le1$. No estimate at a moving face is inferred from an
interior expansion.

Combining (97.8)--(97.9) yields, uniformly in all phases and
$|r|\le R/2$,

$$
|\widetilde P_s(t;0,(r,z))-p_E(t;0,(r,z))|
 \le C t^{-7/2}(sR+e^{-cR^2/t}),\qquad 0<t\le s^{-2}.
\tag{97.10}
$$

Integrate on $1\le t\le s^{-2}$. The threshold-factor correction
costs $Cs^2\int_1^{s^{-2}}t^{-5/2}dt\le Cs^2$, since
$|e^{\lambda s^2t}-1|\le Cs^2t$ there. Also
$\int_1^\infty t^{-7/2}e^{-cR^2/t}dt\le CR^{-5}$.
The native infinite-time remainder is $Cs^5$ by (82.9), and the
canonical remainder past $s^{-2}$ is $Cs^5$ by (82.4).
These observations prove (97.4) on $|r|\le R/2$.

On $|r|>R/2$ the height displacement alone gives
$d(o,\Xi_s\mathscr L_s(r,z))\ge s|r|$ and
$d_E(0,(r,z))\ge |r|$. Integrating (82.6) for original times up to
one, and using (82.9) afterwards, bounds the native field by
$CR^{-5}+Cs^5$. The canonical field is bounded by $CR^{-5}$ in the
same way. Outside $I_s$ its native extension is zero and this
canonical bound still applies. This proves (97.4) everywhere and
(97.5) follows by substitution. The bridge, reflection, Gaussian
matrix calculation and integration have all used one common killed
law; no independently optimized covariance or marginal has been
combined with it. $\square$

## 98. Finite native critical errors on the whole complex domain

**Theorem 98.1 (a uniform lower error and explicit critical recovery).**
Let $q_s^c[F]=a b_s[F]-\chi_c\int U_s|F|^2
-a\lambda s^2\|F\|_2^2$ on exactly $\mathcal Q_s$.
There are constants $C,s_0>0$ such that, for every $0<s<s_0$ and
every complex $F\in\mathcal Q_s$,

$$
q_s^c[F]\ge-Cs^{2/3}\|F\|_2^2.
\tag{98.1}
$$

There are normalized $Z_s\in\mathcal Q_s$, defined for every
sufficiently small $s$ without a diagonal parameter choice, such that

$$
|q_s^c[Z_s]|\le Cs^{2/3},\qquad
\int U_s|Z_s|^2\longrightarrow\mu_c,\qquad
\|Z_s-\Phi_c\|_2\longrightarrow0.
\tag{98.2}
$$

In particular the critical infimum of (91.1) obeys
$|\epsilon_s^c|\le Cs^{2/3}$.

Proof. Work first in (97.1), writing $f=\mathcal T_sF$. Choose fixed
smooth real functions $\eta,\zeta$ on the height line with
$\eta^2+\zeta^2=1$, $\eta=1$ on $[-1,1]$, $\eta=0$ outside
$[-2,2]$, and bounded derivatives. Such a smooth quadratic partition
is obtained as $\eta=\cos\vartheta$, $\zeta=\sin\vartheta$, where
$\vartheta$ is zero on the smaller interval and $\pi/2$ outside the
larger interval. Put $\eta_R(r)=\eta(r/R)$ and likewise $\zeta_R$.
Since $Y$ does not differentiate these cutoffs, the exact quadratic
partition identity is

$$
\widetilde q_s^c[f]
 =\widetilde q_s^c[\eta_R f]+\widetilde q_s^c[\zeta_R f]
 -a\int(|\eta_R'|^2+|\zeta_R'|^2)|f|^2,
\quad \widetilde q_s^c=q_s^c\circ\mathcal T_s^{-1}.
\tag{98.3}
$$

It holds by core approximation for the entire complex closed domain.
For $sR$ small, $\eta_R f$ belongs to $\mathcal Q_E$ after zero
extension. On its support, (97.2) gives
$\widetilde b_s[\eta_R f]\ge(1-C sR)b[\eta_R f]$.
This domain assertion follows as well by cutting off native core
approximants and using the two equivalent horizontal norms on the
height strip; no separate phase derivative is introduced.
Nonnegativity of $h_c$ from (84.3), boundedness of $V$, and (97.5)
therefore give

$$
\widetilde q_s^c[\eta_R f]
 \ge-C(sR+s^{5/6}+s^2)\|\eta_R f\|_2^2.
\tag{98.4}
$$

Indeed subtract $(1-C sR)h_c[\eta_R f]$ and bound the remaining
potential multipliers in supremum norm. On the support of
$\zeta_R f$ one has $|r|\ge R$. The height-only tail proved in
Lemma 97.2 and the nonnegative native kinetic form give

$$
\widetilde q_s^c[\zeta_R f]
 \ge-C(R^{-5}+s^5+s^2)\|\zeta_R f\|_2^2.
\tag{98.5}
$$

The last integral in (98.3) is at most $CR^{-2}\|f\|_2^2$.
Set $R=R_s=s^{-1/3}$. The support $|r|\le2R_s$ lies between the
original moving faces for all small $s$. Equations (98.3)--(98.5),
$\|\eta_R f\|_2^2+\|\zeta_R f\|_2^2=\|f\|_2^2$ and unitarity
prove (98.1), independently of the vector's kinetic size.

For recovery use the attained positive critical mode of Theorem 88.1,
and define

$$
f_s=\frac{\eta_{R_s}\Phi_c}{\|\eta_{R_s}\Phi_c\|_2},
\qquad Z_s=\mathcal T_s^{-1}f_s.
\tag{98.6}
$$

The denominator tends to one and is bounded below for all small $s$.
The cutoff mode belongs to the native form domain: first approximate
$\Phi_c$ in the canonical horizontal form core, multiply by the height
cutoff, and use (97.2) on the resulting fixed height strip. This
also proves its original Dirichlet admissibility, while allowing
unbounded phase support in the final limit.
Testing $H_c\Phi_c=0$ with $\eta_{R_s}^2\Phi_c$ gives the exact identity

$$
h_c[\eta_{R_s}\Phi_c]
 =a\int |\eta_{R_s}'|^2|\Phi_c|^2\le CR_s^{-2}.
\tag{98.7}
$$

The test belongs to $\mathcal Q_E$, and the weak eigen-equation and
product rule justify this identity; it is not an assumed tail rate
for $\Phi_c$. Also $b[\eta_{R_s}\Phi_c]\le C$ by the product rule.
Thus (97.2), (97.5), (98.7) and normalization give
$|q_s^c[Z_s]|\le C(R_s^{-2}+sR_s+s^{5/6}+s^2)
\le Cs^{2/3}$. Boundedness of $V$ and dominated convergence give
$v[f_s]\to v[\Phi_c]=\mu_c$; (97.5) gives the potential assertion
in (98.2). Finally $f_s\to\Phi_c$ in $L^2$, and the unitary phase
shears $\mathcal T_s^{-1}$ converge strongly to the identity.
The latter follows first on compact continuous functions from
$L_s\to\mathrm{Id}$ and then on all $L^2$ by density and unitarity.
It proves the last assertion. Taking the infimum in (98.1) and
testing on (98.6) proves the two-sided bound on $\epsilon_s^c$.
$\square$

## 99. An independently prescribed native critical selection window

**Theorem 99.1 (energy onset and actual native phase-orbit selection).**
For every prescribed pair of positive sequences $s_n\downarrow0$ and
$\delta_n\downarrow0$ satisfying

$$
s_n^{2/3}=o(\delta_n),\qquad
\tau_n=s_n^2,\qquad g_n=(\chi_c+\delta_n)s_n^3,
\tag{99.1}
$$

one has, on the unchanged native problem,

$$
\tau_n E_{\tau_n}(g_n)=-\mu_c\delta_n+o(\delta_n).
\tag{99.2}
$$

For every normalized complex $\psi_n\in\mathcal Q$ satisfying

$$
\tau_n\bigl(\mathfrak e_{g_n,\tau_n}[\psi_n]
                         -E_{\tau_n}(g_n)\bigr)=o(\delta_n),
\tag{99.3}
$$

there are constant phases $\theta_n$ such that

$$
\|\mathcal U_{s_n}\psi_n-e^{i\theta_n}\Phi_c\|_2\longrightarrow0.
\tag{99.4}
$$

This includes every choice of actual normalized native ground states.
There is no translation or variable phase adjustment. The explicit
nonempty sufficient window can equivalently be written
$\tau_n^{1/3}=o(\delta_n)$. Examples prescribed before any core
approximation are $\delta(s)=s^p$ for every fixed $0<p<2/3$, or
$\delta(\tau)=\tau^q$ for every fixed $0<q<1/3$, with the indicated
$g=(\chi_c+\delta)\tau^{3/2}$.

Proof. Theorem 98.1 verifies exactly (91.2) with
$\alpha_n=Cs_n^{2/3}$ and $U_n=Z_{s_n}$:
$\alpha_n=o(\delta_n)$, $q_n^c[U_n]=o(\delta_n)$ and
$v_n[U_n]\to\mu_c$. The exact conjugacy (81.4) makes (99.3)
precisely (91.3). Proposition 91.1 therefore gives (99.2) and
(99.4) directly; its selection argument is not a new hypothesis
here. Existence of a normalized native ground state at each pair
is Proposition 75.2, and its excess is zero. Finally each stated
power satisfies (99.1), and $g_n\to0$, so these are original allowed
coupled families, with no diagonal slowing of $s_n$ or $\delta_n$.
$\square$

## 100. The macroscopic branch obstructs unrestricted uncentered onset

**Proposition 100.1 (a finite bound and an allowed very-fine path).**
There are constants $c,C,s_0>0$ such that for $0<s<s_0$ and
$0\le\delta\le1$, with $g=(\chi_c+\delta)s^3$, the actual finite
native infimum satisfies

$$
-C(s^{2/3}+\delta)
 \le s^2E_{s^2}(g)
 \le-c(\chi_c+\delta)^2s^8<0.
\tag{100.1}
$$

Consequently, on every prescribed positive detuning path
$\delta(s)=o(s^8)$,

$$
\frac{s^2E_{s^2}((\chi_c+\delta(s))s^3)}{\delta(s)}
 \longrightarrow-\infty.
\tag{100.2}
$$

In particular $\delta(s)=s^9$, $\tau=s^2$,
$g=(\chi_c+s^9)s^3$ is an explicit original allowed path refuting
an unrestricted assertion of (99.2) without a detuning restriction.
This is an obstruction to that uncentered energy law, not a proof
of failure of the critical profile on the excluded paths.

Proof. The full-domain lower bound (98.1) and uniform boundedness
of $U_s$ give the lower bound in (100.1), by subtracting
$\delta\int U_s|F|^2$ for unit vectors. For the upper direction,
positivity of the added short-time heat gives $W_{s^2}\ge W_1$.
Hence the variational principle and the fixed-cutoff theorem (72.1)
give, for all sufficiently small $g>0$,

$$
E_{s^2}(g)\le E_1(g)\le-cg^2,
\qquad c=|e_*|/2>0.
\tag{100.3}
$$

The smallness threshold for $g$ is uniform in $\delta\in[0,1]$
when $s$ is small. Multiply by $s^2$ to obtain (100.1).
This uses the macroscopic branch only as a trial upper direction;
it does not identify it as the actual minimizing branch at these
parameters. Finiteness and negative attainment also follow separately
from Proposition 75.2. Since $\chi_c>0$, division by any positive
$\delta=o(s^8)$ proves (100.2). The explicit $g(s)$ above is strictly
increasing for $s>0$ and tends to zero, so its inverse also defines
an allowed function $\tau(g)$ of the original formulation (75.3).

More generally, if an uncentered finite-coefficient onset
$s^2E_{s^2}(g)=-\mu_c\delta+o(\delta)$ holds on a positive path,
(100.1) forces $\delta\ge c' s^8$ eventually for some $c'>0$.
This necessary lower size restriction is far weaker than the proved
sufficient window $s^{2/3}=o(\delta)$, and does not establish any
sufficiency in the intervening range. In particular (100.3) is not
a critical lower-error estimate, and supplies no matching coefficient
on the finer scale $s^2g^2=\chi^2s^8$ of (91.5). $\square$

## 101. Correspondence, mechanism and the remaining scales

**Definition 101.1 (scope of the quantitative increment).** The new
source-specific ingredients are the exact rational shear (97.1)--(97.3),
the common-bridge covariance comparison and integrated estimate
(97.4), and the native full-domain error and recovery (98.1)--(98.7).
The selection deduction uses the existing Proposition 91.1, the
critical mode of Theorem 88.1 and the native compactness and profile
suppliers of §§82--90. The macroscopic obstruction reuses Theorem 72.1
and positivity of the same original added heat; it does not repeat
the Coulomb calculation or its generic variational theory.

The conditional Gaussian representation is the one already used in
G (32.7)--(32.8), with the very same independent height and phase
Brownian drivers and unnormalized killed survival indicator.
Only the exact rational identity permits the covariance matrix order
in (97.6) on one common bridge. The strip exit estimate uses the
standard one-dimensional reflection principle with height generator
$\partial_r^2$, corresponding to $\sqrt2 B^1$, and the existing
all-height bound (76.1). The canonical and native spatial Gaussian
bounds are precisely Lemmas 82.1--82.2. Their primary supplier,
Coulhon--Sikora, Theorem 4.1, assumes the Davies--Gaffney estimate
and an all-time diagonal bound $Kt^{-D/2}$; here $D=7$ and those
hypotheses are verified in the owning lemmas, with the original
Lebesgue density and selfadjoint realizations. The theorem's polynomial
Gaussian factor is absorbed there by decreasing the exponent.
No additional global heat expansion is attributed to that theorem.

Colin de Verdière--Hillairet--Trélat, Theorem A, gives smooth
positive-time asymptotics on fixed compact sets; Theorem B and
localization Theorem 3.2 supply the local convergence used in §81.
None of them alone is being used to assert (97.4). Its uniformity in
all real phases, growing height strip, integrated time and original
infinite-time tail is proved above using (97.6)--(97.10) and (82.9).
In particular the field clock is never replaced by the kinetic
clock $aB$, its source is never divided by a surviving mass, and
$\det L_s=1$ leaves the factor $1/j_0$ exactly unchanged.
The original-coordinate correspondence remains (80.1), including
its absolute $|\kappa|$ Jacobian and signed tensor entries.
These are ordinary repository-derived deductions, with no claim
of kernel certification or literature-wide novelty.

The rank-three long-time phase tensor and weak-binding Coulomb profile
of §§72--77 concern the three real phase directions at large scales.
The fixed-domain Engel threshold of §§84--89 concerns the four
coordinate, homogeneous-dimension-seven microscopic tangent operator.
Theorem 99.1 adds an actual finite-native critical window connecting
that fixed-domain onset to native ground states. Proposition 100.1
shows why an unrestricted uncentered law cannot be read off from
fixed-domain onset, even though every positive-cutoff native problem
has a negative attained ground state. These mechanisms are compatible.

The powers $2/3$ and $5/6$ above are sufficient estimates, not asserted
optimal. Critical profile selection for detunings outside (99.1), an
onset law centered at a finite-native critical energy, the exact branch
crossover, and the finer rescaled $\tau g^2$ coefficient in (91.5)
remain unresolved here. Energy-law failure in (100.2) does not resolve
those profile questions. The observation and analytic-preparation
boundaries of §§92--96 are unchanged: retained statistics, lawful finite
transport, and common resource realizations do not prepare these
analytic amplitudes or supply their physical-space interpretation.
No physical spatial dimension, physical $SO(3)$, actual zero leaf,
wrapped phase model, cutoff-free realization or uniformity as
$\kappa\to0$ is selected. The original why-three question therefore
retains its physical realization obligations.

## 追加锚（本行以下为增补区）

## 102. A compact microscopic source forces distant native mass

**Definition 102.1 (actual critical eigenstates and their compact charge).**
Retain all fixed data, raw measures, operators and full complex domains
of Definitions 75.1 and 81.1. In particular $a>0$ and the admissible
signed $\kappa\ne0$ are fixed, both height faces are Dirichlet, and
$W_{s^2}$ uses the heat clock of $B$, independently of $a$. For $s>0$
put

$$
\begin{aligned}
g_s&=\chi_cs^3,& E_s&=E_{s^2}(g_s),&
\epsilon_c(s)&=s^2E_s,\\
m_s&=-E_s/a>0,& r_s&=-\epsilon_c(s)/s^8>0,&
F_s&=\mathcal U_s\psi_s,
\end{aligned}
\tag{102.1}
$$

where $\psi_s$ is any actual normalized complex ground state of
$aS-g_sW_{s^2}$, whose negative attainment in $D(S)$ is Proposition
75.2. Thus $\epsilon_c(s)$ is the critical infimum denoted by
$\epsilon_s^c$ in (91.1), and $m_s=r_ss^6/a$. The symbol $U_s$ below
is the potential in (81.1); $\mathcal U_s$ is the unitary map there.
For a fixed compact Lebesgue measurable $K\subset\mathbb R^4$ of
positive measure define

$$
\begin{aligned}
J_K&=\int_K V(\xi)\Phi_c(\xi)d\xi,\\
\mathfrak A_s(K)&=\int_K
 \phi(k_0+\varepsilon s r)U_s(\xi)F_s(\xi)d\xi,
 \qquad \xi=(r,y,z,w),\\
\mathscr D_m&=I\times\{q\in\mathbb R^3:1\le\sqrt m\,d(q)\le2\},
 \qquad d(q)=\sqrt{q^{\mathsf T}M^{-1}q}.
\end{aligned}
\tag{102.2}
$$

The overlap is used only for sufficiently small $s$ that $K\subset
\Omega_s$. Strict positivity from Theorem 88.1 and Lemma 82.1 gives
$0<J_K<\infty$; finiteness also follows directly from boundedness of
$V$ and local $L^2$ integrability of $\Phi_c$.

**Theorem 102.2 (finite-native mass forced by an actual eigenstate).**
There are constants $C_0,m_0>0$, depending only on the fixed native
data, with the following property. For each $K$ in Definition 102.1
there is $s_K>0$ such that, for every $0<s<s_K$ for which the actual
mass parameter satisfies $m_s\le m_0$, and for every actual normalized
complex ground-state choice,

$$
\int_{\mathscr D_{m_s}}|\psi_s(k,q)|^2dk\,dq
 \ \ge\ C_0\frac{s^4}{\sqrt{-\epsilon_c(s)}}
                    |\mathfrak A_s(K)|^2.
\tag{102.3}
$$

No hypothesis about a microscopic profile or a bound on $r_s$ is
needed for this finite-$s$ inequality. One possible constant is

$$
C_0=\frac{\chi_c^2j_0}{a^{3/2}}b_0^2v_M,\qquad
b_0=\frac{e^{-3}}{24\pi\sqrt{\det M}},\qquad
v_M=\frac{28\pi}{3}\sqrt{\det M}.
\tag{102.4}
$$

Proof. We first justify the use of a positive eigenstate without
restricting the complex admissible domain. For each fixed positive
$s$, $W_{s^2}$ is a bounded nonnegative real multiplier, and the
Hamiltonian $H_s=aS-g_sW_{s^2}$ has operator domain exactly $D(S)$
by Propositions 70.2 and 75.2.
The native heat kernel is strictly positive almost everywhere between
interior full points. Indeed the conditional Gaussian construction
of G (32.7) applies also to a height bridge with different endpoints.
The bridge stays in $I$ with positive probability. Almost surely its
range contains an interval, and the bracket independence of G (26.7)
prevents a nonzero linear combination of $c_\kappa$ from vanishing
on that interval. Its phase covariance is therefore positive definite.
The Gaussian density is positive at every phase displacement; its
mixture with the survived height bridge gives the assertion. These
are precisely the original rational fields and raw density, with no
conditioning normalization in the kernel.

The bounded-potential Dyson series gives a positive kernel for
$e^{-tH_s}$, containing the strictly positive kernel of $e^{-taS}$ as its zeroth term. Its series is bounded above
by $e^{tg_s\|W_{s^2}\|_\infty}$ times that same kernel, so it defines
the usual integral semigroup as well as the $L^2$ operator. Since
$H_s-E_s\ge0$, $T_t=e^{-t(H_s-E_s)}$ is an $L^2$ contraction with a
strictly positive kernel. For any complex ground state $\psi_s$,

$$
|\psi_s|=|T_t\psi_s|\le T_t|\psi_s|,\qquad
\|T_t|\psi_s|\|_2\le\|\psi_s\|_2.
\tag{102.5}
$$

The pointwise inequality and equality of the norms force
$T_t|\psi_s|=|\psi_s|$. Spectral calculus puts $|\psi_s|$ in the
same ground eigenspace and in $D(S)$. Equality in the integral
triangle inequality with the strictly positive kernel makes the
phase of $\psi_s$ constant almost everywhere, and $|\psi_s|$ is
strictly positive almost everywhere. Thus
$\psi_s=e^{i\theta_s}u_s$ for a real $u_s>0$ with $\|u_s\|_2=1$.
This argument uses the entire complex native domain, not an assumed
ordinary phase gradient or a prescribed real variational class.

The actual eigen-equation now gives the exact $L^2$ relation

$$
(S+m_s)u_s=\frac{g_s}{a}W_{s^2}u_s,\qquad
u_s=\frac{g_s}{a}(S+m_s)^{-1}(W_{s^2}u_s).
\tag{102.6}
$$

The resolvent kernel is exactly
$\mathcal G_{\kappa,m_s}$ of L Definition 41.1, relative to raw
$dk'\,dq'$. Phase translation invariance and the centered conditional
Gaussian make this kernel even in the phase displacement, so either
sign of $q-q'$ gives the same kernel. Its nonnegative integral formula
follows from the heat integral and Tonelli. It applies even if
$W_{s^2}u_s$ is not globally $L^1$: truncate that nonnegative $L^2$ function on increasing bounded
sets and in value, use $L^2$ resolvent convergence, and identify the
monotone pointwise limit along an almost everywhere convergent
subsequence. Consequently (102.6) may be bounded below by restricting
its source integral to $\Xi_s(K)$.

Write $\ell=\sqrt{\lambda_{\min}(M)}>0$, so $|h|\ge\ell d(h)$.
By L Theorem 42.1 there is a fixed $C_G$ such that, for all $m\ge0$,
all heights in $I$ and $|h|\ge1$,

$$
\mathcal G_{\kappa,m}(k,k';h)
\ge\phi(k)\phi(k')\left(
 \frac{e^{-\sqrt m\,d(h)}}{4\pi\sqrt{\det M}\,d(h)}
                   -C_G|h|^{-3}\right).
\tag{102.7}
$$

This is the finite native two-endpoint resolvent bound; no inverse
of the tangent operator is substituted for it. Set
$y_0=e^{-3}/(12\pi\sqrt{\det M})=2b_0$ and choose $m_0>0$ with

$$
m_0\le\min(1/4,\ell^2/4),\qquad
8C_G\ell^{-3}m_0\le y_0/2.
\tag{102.8}
$$

Compactness of $K$ and (78.1) give, for $s\le1$,

$$
q'_s(\xi)=s c_0y+\varepsilon s^2c_1z
                        +\varepsilon^2s^3c_2w,\qquad
\sup_{\xi\in K}d(q'_s(\xi))\le L_Ks
\tag{102.9}
$$

for a finite $L_K$. Choose $s_K\le1$ so that $K\subset\Omega_s$
and $L_Ks\le1$ whenever $0<s<s_K$. If $q$ is in the phase shell
of $\mathscr D_m$ and $0<m\le m_0$, the triangle inequality for $d$
therefore gives, uniformly for $\xi\in K$,

$$
\tfrac12\le\sqrt m\,d(q-q'_s(\xi))\le3,\qquad
|q-q'_s(\xi)|\ge\frac{\ell}{2\sqrt m}\ge1.
\tag{102.10}
$$

The Yukawa term in (102.7) is at least $y_0\sqrt m$; its error
is at most $8C_G\ell^{-3}m^{3/2}\le(y_0/2)\sqrt m$.
Thus for all output heights $k\in I$, including arbitrarily near
either face, and all $\xi\in K$,

$$
\mathcal G_{\kappa,m}(k,k_0+\varepsilon s r;
                              q-q'_s(\xi))
 \ge b_0\phi(k)\phi(k_0+\varepsilon s r)\sqrt m.
\tag{102.11}
$$

Let $F_s^+=\mathcal U_su_s=e^{-i\theta_s}F_s$. Positivity of the
weights and the constant phase show that
$|\mathfrak A_s(K)|=\int_K\phi(k_0+\varepsilon s r)U_sF_s^+d\xi$.
The exact Jacobian, potential and wavefunction factors in (78.1)
and (81.1) give

$$
\begin{aligned}
\int_{\Xi_s(K)}\phi(k')W_{s^2}(k',q')u_s(k',q')dk'\,dq'
 &=j_0^{1/2}s^{-3/2}|\mathfrak A_s(K)|,\\
u_s(k,q)&\ge\frac{\chi_c b_0\sqrt{j_0}}a
 s^{3/2}\sqrt{m_s}\,\phi(k)|\mathfrak A_s(K)|
 \quad\text{a.e. on }\mathscr D_{m_s}.
\end{aligned}
\tag{102.12}
$$

The first factor is $j_0s^7\cdot s^{-5}\cdot
j_0^{-1/2}s^{-7/2}$, so no raw-source charge or density factor has
been removed. The second line follows by combining (102.6),
(102.11) and $g_s=\chi_cs^3$. Since $\int_I\phi^2dk=1$ and

$$
\left|\{q:1\le\sqrt m\,d(q)\le2\}\right|=v_Mm^{-3/2},
\tag{102.13}
$$

squaring and integrating (102.12) gives
$\chi_c^2b_0^2j_0v_Ma^{-2}s^3m_s^{-1/2}
|\mathfrak A_s(K)|^2$. Finally
$s^3m_s^{-1/2}=\sqrt a\,s^4/\sqrt{-\epsilon_c(s)}$ proves
(102.3)--(102.4). The cutoff, both native boundary faces, every
real phase frequency and the kinetic operator domain have all
remained those of the actual eigen-equation. This source-specific
connection between the compact microscopic charge and finite-native
mass is `repo-derived`; its heat and Green inputs are exactly
G (32.7) and L (41.1)--(42.2). The bounded-potential semigroup and
spectral-calculus arguments are classical intermediate tools. $\square$

## 103. A quantitative defect for actual profiles at bounded energy scale

**Theorem 103.1 (bounded $r_s$ excludes the unit critical orbit).**
Fix $K$ as in Definition 102.1 and set

$$
\gamma_K=C_0\phi(k_0)^2J_K^2>0.
\tag{103.1}
$$

For every prescribed sequence $s_n\downarrow0$ on the exact path
$g_n=\chi_cs_n^3$, every $B\in(0,\infty)$ for which $r_{s_n}\le B$
eventually, and every choice of actual normalized complex ground
states, every weak global $L^2(d\xi)$ limit of $F_{s_n}$ is
$c\Phi_c$ and satisfies

$$
|c|^2\le\frac{1}{1+\gamma_K/\sqrt B}<1,\qquad
1-|c|^2\ge\frac{\gamma_K}{\sqrt B}|c|^2.
\tag{103.2}
$$

Every subsequence has a weakly convergent further subsequence.
Writing $\mathcal O_c=\{e^{i\theta}\Phi_c:\theta\in\mathbb R\}$,
the whole sequence consequently obeys

$$
\liminf_n\operatorname{dist}_{L^2}(F_{s_n},\mathcal O_c)
\ge\left(2-2(1+\gamma_K/\sqrt B)^{-1/2}\right)^{1/2}>0.
\tag{103.3}
$$

Proof. Actual ground states have zero excess in (85.5), so Theorem
90.1 supplies weak subsequential compactness, the limit $c\Phi_c$,
and strong local $L^2$ convergence along every weakly convergent
subsequence. On such a subsequence Theorem 82.3, the continuity of
$\phi$ at $k_0$ and compactness of $K$ give

$$
\mathfrak A_{s_n}(K)\longrightarrow\phi(k_0)cJ_K.
\tag{103.4}
$$

For detail, the multipliers
$\phi(k_0+\varepsilon s_nr)U_{s_n}$ converge uniformly on $K$ to
$\phi(k_0)V$, and are uniformly bounded. Their product with the
local $L^2$ difference has integral tending to zero by
Cauchy--Schwarz and $|K|<\infty$. Their difference paired with
$c\Phi_c$ is controlled in the same way. No boundary regularity of
$K$ or global $L^1$ bound on $VF_{s_n}$ is required.

Here $m_{s_n}=r_{s_n}s_n^6/a\le Bs_n^6/a\to0$, so Theorem 102.2
applies eventually. Since
$s_n^4/\sqrt{-\epsilon_c(s_n)}=r_{s_n}^{-1/2}\ge B^{-1/2}$,
it gives

$$
\liminf_n\int_{\mathscr D_{m_{s_n}}}|\psi_{s_n}|^2dk\,dq
\ge\frac{\gamma_K}{\sqrt B}|c|^2.
\tag{103.5}
$$

These shell masses are disjoint from every fixed microscopic
compact set for all large $n$. Indeed for a fixed compact
$D\subset\mathbb R^4$, (78.1) gives
$\sup_{\xi\in D}d(q'_{s_n}(\xi))=O_D(s_n)$, whereas on the
shell $d(q)\ge m_{s_n}^{-1/2}\to\infty$. Unitarity therefore yields

$$
1\ge\int_D|F_{s_n}|^2d\xi
       +\int_{\mathscr D_{m_{s_n}}}|\psi_{s_n}|^2dk\,dq
\tag{103.6}
$$

for each fixed compact $D$ and all sufficiently large $n$.
Pass to the limit using local strong convergence and (103.5),
then exhaust $\mathbb R^4$ by compact boxes. Since $\|\Phi_c\|_2=1$,
this gives $1\ge |c|^2+\gamma_KB^{-1/2}|c|^2$, proving (103.2).

Finally, for unit vectors $F$,
$\operatorname{dist}(F,\mathcal O_c)^2=2-2|\langle F,\Phi_c\rangle|$.
If the limsup of the absolute overlap exceeded
$(1+\gamma_K/\sqrt B)^{-1/2}$, weak subsequential compactness would
give a further subsequence with limit $c\Phi_c$ violating (103.2).
This proves (103.3) for the full sequence. $\square$

**Corollary 103.2 (a necessary actual energy scale for no mass loss).**
For any prescribed sequence $s_n\downarrow0$ and any actual normalized
complex ground-state choices on $g_n=\chi_cs_n^3$, strong convergence
to the critical phase orbit implies

$$
\operatorname{dist}_{L^2}(F_{s_n},\mathcal O_c)\longrightarrow0
\quad\Longrightarrow\quad
r_{s_n}=\frac{-s_n^2E_{s_n^2}(\chi_cs_n^3)}{s_n^8}
           \longrightarrow\infty.
\tag{103.7}
$$

Proof. If the positive numbers $r_{s_n}$ did not tend to infinity,
there would be a finite $B>0$ and a subsequence with $r_{s_n}\le B$.
Theorem 103.1 would give the strictly positive lower bound (103.3)
on that subsequence, a contradiction. This argument does not assume
that $m_{s_n}\to0$ on the whole original sequence; that smallness
is forced on the bounded-$r$ subsequence where it is needed.

The conclusions are necessary restrictions on actual eigenstates,
not sufficiency of $r_s\to\infty$. Proposition 100.1 supplies only
$r_s\ge c\chi_c^2>0$ eventually; its trial upper bound on the negative
energy is a lower bound on $r_s$, and cannot provide $r_s\le B$.
Neither an actual bounded-$r_s$ sequence nor $r_s\to\infty$ is
established here for the fixed original data. Thus (103.7) does not
decide whether the actual exact-critical ground states converge to
$\mathcal O_c$. The exact energy coefficient, a matching native
energy-scale bound, a sufficient no-loss estimate, and the centered
crossover remain unresolved. The finite-native resolvent used in
(102.7) is distinct from the fixed-domain inverse in Theorem 87.2;
no positive gap above the tangent zero mode is assumed. The
original-coordinate change and coupling normalization remain (80.1).
The observation and resource statements of §§92--96 supply none of
the analytic-state preparation or physical-space correspondences
needed to strengthen these analytic conclusions. $\square$

## 追加锚（本行以下为增补区）

## 104. Global reconstruction for the original finite-native resolvent

**Definition 104.1 (common-space reconstruction and the native time split).**
Retain Definitions 75.1, 81.1 and 87.1, including the fixed admissible
signed $\kappa\ne0$, raw unit source, both height Dirichlet faces,
all real phase frequencies and the full complex horizontal domains.
On $L^2(\Omega_s,d\xi)$ set

$$
\begin{aligned}
C_s&=A_s-\lambda s^2
     =s^2\mathcal U_sS\mathcal U_s^{-1}\ge0,\\
Q_s(t)&=e^{-tC_s},&R_s(h)&=(C_s+h)^{-1}\quad(h>0),\\
q_s(t;\eta,\xi)&=e^{\lambda s^2t}P_s(t;\eta,\xi),\\
U_s^{<}(\xi)&=s^5D_{s^2}(\Xi_s\xi)
       =\frac1{j_0}\int_1^{s^{-2}}q_s(t;0,\xi)dt,\\
U_s^{>}(\xi)&=s^5W_1(\Xi_s\xi),&U_s&=U_s^{<}+U_s^{>},\\
K_{\rm rec}&=TM=\int_0^\infty P_tV\,dt=\mathcal E^{-1}V.
\end{aligned}
\tag{104.1}
$$

Here $0<s<1$, $P_t=e^{-t\mathcal E}$ and $M$ is multiplication
by $V^{1/2}$ as in §87. An expression such as $P_tV$ means heat
composed with multiplication. All finite-native operators in this
section act on the common complex $L^2(\mathbb R^4,d\xi)$ by
restriction to $\Omega_s$ followed by zero extension. Their operator
domains before extension are $D(C_s)=D(A_s)=\mathcal U_sD(S)$.
The last inverse in (104.1) is only the bounded reconstruction on
the specified right sides, justified by Theorem 87.2; it does not
assert bounded invertibility of $\mathcal E$ on all of $L^2$.
In particular $K_{\rm rec}$ is compact and has range in
$D(\mathcal E)$. The time split occurs at original heat time one,
not at a clock containing the kinetic coefficient $a$.

**Theorem 104.2 (global complex weighted-resolvent estimate).** There
are $C,s_0>0$ depending only on the fixed native data, and numbers
$d_s\ge0$ with $d_s\to0$ as $s\downarrow0$, such that, for every
$0<s<s_0$ and every $0<h\le1$,

$$
\|R_s(h)U_s-K_{\rm rec}\|_{2\to2}
 \le d_s+Ch^{3/4}
       +C\left(\frac{s^8}{h}\right)^{1/4}
       +C\left(\frac{s^8}{h}\right)^{1/2}.
\tag{104.2}
$$

Consequently for every fixed $H>0$ there is
$\eta_H(s)\to0$ such that for all sufficiently small $s$ and all
$0<h\le Hs^{2/3}$ the same estimate holds with its first two
terms replaced by $\eta_H(s)$. One may take
$\eta_H(s)=d_s+CH^{3/4}s^{1/2}$, with the same $C$ independent
of $H,s,h$.

Proof. We first supply the two-endpoint and full-output heat
convergence needed here. For each fixed $t>0$,

$$
q_s(t;\eta,\xi)\longrightarrow p_E(t;\eta,\xi)
\quad\hbox{locally uniformly in }(\eta,\xi)\in\mathbb R^4\times\mathbb R^4.
\tag{104.3}
$$

The primary supplier is exactly Colin de Verdière--Hillairet--Trélat,
[Theorem B, (2.8), pp.915--916, and Theorem 3.2, pp.920--921](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf).
Their statement allows both scaled endpoints to vary on compact
sets. In the present application the fields are the original
$\varepsilon\partial_k,c_\kappa\cdot\partial_q$, their drift and
potential are zero, and their smooth constant density is $dk\,dq$.
The nonzero determinant (76.4) gives constant flag weights
$(1,1,2,3)$ and bounded step three on an interior neighborhood of
the fixed pole. The privileged coordinates are exactly (78.1),
with limiting fields (81.2). The nilpotentized density in that
chart is $j_0d\xi$, so converting the limiting kernel to unit
Lebesgue measure gives precisely $j_0s^7p_{s^2t}=P_s$.
Both endpoints in any fixed compact rescaled set lie in this
interior neighborhood eventually. The localization theorem applies
to the identical differential expression and density there and
to its selfadjoint killed realization, whose heat is a contraction;
it retains both original faces. Finally
$e^{\lambda s^2t}\to1$ on compact positive-time windows. These
checks give (104.3), without a global heat convergence premise.
For a fixed compact set larger than the coordinate neighborhood,
choose a fixed $R$ such that its image under $\delta_{1/R}$ lies
in that neighborhood. The exact identities
$q_s(t;\eta,\xi)=R^{-7}q_{Rs}(t/R^2;
\delta_{1/R}\eta,\delta_{1/R}\xi)$ and the identical canonical
dilation identity reduce its convergence to the checked local
statement. Here $R$ is fixed before $s\downarrow0$.

Symmetry and the semigroup identity give
$\|q_s(t;\eta,\cdot)\|_2^2=q_s(2t;\eta,\eta)$.
Using (76.1) in this identity proves, uniformly over all input
heights and phases,

$$
\begin{aligned}
\|Q_s(t)\|_{2\to2}&\le1,\\
\|Q_s(t)\|_{1\to2}&\le
\begin{cases}
Ct^{-7/4},&0<t\le s^{-2},\\
Cs^2t^{-3/4},&t\ge s^{-2}.
\end{cases}
\end{aligned}
\tag{104.4}
$$

Indeed at original times $2s^2t\le1$ the diagonal is bounded
by $Ct^{-7/2}$, with bounded threshold factor. At
$2s^2t\ge1$ it is bounded by $Cs^4t^{-3/2}$; on the overlap
$t\le s^{-2}$ this is at most $Ct^{-7/2}$. Integration against
an $L^1$ input and the triangle inequality give the stated
$1\to2$ bounds from the column norms. The first line uses
$C_s\ge0$, not a raw-measure Markov property of the shifted heat.
The canonical analog is $\|P_t\|_{1\to2}\le Ct^{-7/4}$ by
(82.4) and the same column identity.

For every fixed $t>0$ and $\eta$, (104.3), (104.4) and that
identity imply the global statement

$$
q_s(t;\eta,\cdot)\longrightarrow p_E(t;\eta,\cdot)
\quad\hbox{in }L^2(\mathbb R^4).
\tag{104.5}
$$

To prove it, local uniform convergence and the uniform column
$L^2$ bound give weak $L^2$ convergence, first against compactly
supported tests and then by density. The squared column norms
converge to $p_E(2t;\eta,\eta)$ by (104.3). This equals the
squared norm of the limiting column. Weak convergence and norm
convergence in the complex Hilbert space give (104.5).
Thus no output tail is discarded in passing from local kernels
to (104.5).

The short potential satisfies

$$
\sup_{0<s<s_0}(\|U_s^{<}\|_\infty+\|U_s^{<}\|_2)<\infty,
\qquad \|U_s^{<}-V\|_2\longrightarrow0.
\tag{104.6}
$$

Its supremum bound follows from $0\le U_s^{<}\le U_s$ and
Theorem 82.3. For its $L^2$ assertions use (104.1), (104.5)
at $\eta=0$, and the column bound $Ct^{-7/4}$ for
$1\le t\le s^{-2}$. Extend that integrand by zero for
$t>s^{-2}$. It converges in $L^2$ at every fixed $t\ge1$
to $p_E(t;0,\cdot)$ and is dominated in $L^2$ norm by an
integrable function $Ct^{-7/4}$. The triangle inequality for
the integrals and dominated convergence prove (104.6), with the
unchanged factor $1/j_0$. Also $V\in L^2$ by (82.4), since
the homogeneous dimension is seven and $V$ decays with power five.

For each fixed $t>0$ we next have operator-norm convergence

$$
\|Q_s(t)U_s^{<}-P_tV\|_{2\to2}\longrightarrow0.
\tag{104.7}
$$

The norm of $Q_s(t)(U_s^{<}-V)$ is bounded by
$Ct^{-7/4}\|U_s^{<}-V\|_2$ for small $s$, by Hölder
from $L^2$ to $L^1$ and (104.4). For the other term first
replace $V$ by $V\mathbf1_K$ on a fixed compact box $K$.
The squared Hilbert--Schmidt norm of
$(Q_s(t)-P_t)V\mathbf1_K$ is

$$
\int_K |V(\eta)|^2
 \|q_s(t;\eta,\cdot)-p_E(t;\eta,\cdot)\|_2^2d\eta
 \longrightarrow0.
\tag{104.8}
$$

Here (104.5) gives pointwise convergence, and (104.4) supplies
the uniform integrable bound on $K$. The omitted multiplier
has $L^2\to L^1$ norm at most
$\|V\mathbf1_{K^c}\|_2$. Applying both heat $1\to2$
bounds and then exhausting by compact boxes proves (104.7).
This controls both input endpoints and output tails on the entire
common space.

Define the norm-convergent finite integral

$$
J_s=\int_0^{s^{-2}}Q_s(t)U_s^{<}\,dt,
\qquad d_s=\|J_s-K_{\rm rec}\|_{2\to2}.
\tag{104.9}
$$

The integrands, extended by zero beyond $s^{-2}$, are bounded
in operator norm by $C$ on $(0,1)$ and by $Ct^{-7/4}$ on
$[1,\infty)$, using (104.4)--(104.6). The canonical
$P_tV$ has the same integrable bound. Equations (104.7) and
dominated convergence therefore prove $d_s\to0$. This
argument also identifies its limiting integral with $TM$ in
(104.1). In particular the time-zero contribution is uniformly
at most $C\delta$ on $(0,\delta)$; the convergence does not
claim uniform local kernel convergence down to time zero.
Norm measurability follows from positive-time norm continuity
of the selfadjoint heat operators, after bounded multiplication.

For $0<h\le1$, the same integrable bounds give

$$
\left\|\int_0^{s^{-2}}(e^{-ht}-1)Q_s(t)U_s^{<}\,dt\right\|
 \le C\int_0^1 ht\,dt+
       C\int_1^\infty\min(ht,1)t^{-7/4}dt
 \le Ch^{3/4}.
\tag{104.10}
$$

Split the last integral at $1/h$ to obtain the last inequality.
The complete remaining native time interval is bounded by

$$
\left\|\int_{s^{-2}}^\infty e^{-ht}Q_s(t)U_s^{<}\,dt\right\|
 \le Cs^2\int_{s^{-2}}^\infty e^{-ht}t^{-3/4}dt
 \le C s^2h^{-1/4}.
\tag{104.11}
$$

The last constant absorbs the finite integral
$\int_0^\infty e^{-u}u^{-3/4}du$. Equations
(104.9)--(104.11) control $R_s(h)U_s^{<}-K_{\rm rec}$.

It remains to control the long potential $U_s^{>}$, whose
Coulomb tail means that its multiplier function is not in $L^2$.
The fixed-cutoff results (70.3), (71.2) and (71.4) at
$\tau=1$, with a fixed $\delta=\delta_0$, imply

$$
\|W_1\psi\|_2\le C\|S^{1/2}\psi\|_2
\qquad(\psi\in\mathcal Q).
\tag{104.12}
$$

In fact the low-band piece has this bound by (71.4), while
the remainder satisfies
$\|W_1r\|_2\le\|W_1\|_\infty\|r\|_2
\le C\sqrt{T[\psi]}$ by (71.2). This uses Hardy only on
the extracted phase-$H^1$ band, and proves (104.12) for
every complex native vector. Spectral calculus now gives, for
every $m>0$,

$$
\|W_1(S+m)^{-1}\|_{2\to2}
 \le C\sup_{x\ge0}\frac{\sqrt x}{x+m}
 \le C m^{-1/2}.
\tag{104.13}
$$

Taking adjoints gives the same bound for $(S+m)^{-1}W_1$.
The exact unitary scaling (104.1), including restriction and
extension, consequently gives

$$
\begin{aligned}
\|R_s(h)U_s^{>}\|_{2\to2}
 &=s^3\|(S+h/s^2)^{-1}W_1\|_{2\to2}\\
 &\le Cs^4h^{-1/2}.
\end{aligned}
\tag{104.14}
$$

The Laplace formula for $R_s(h)$ is valid in operator norm
after either bounded multiplier because $h>0$ and $Q_s$ is
an $L^2$ contraction. Adding (104.9)--(104.11) and
(104.14) proves (104.2). Substituting $h\le Hs^{2/3}$
proves the asserted $\eta_H$. All norm estimates act on the
full complex $L^2$ space and use the original two-face
Friedrichs realization. No positive gap at the tangent threshold,
ordinary isotropic phase regularity, or survival normalization
has entered. The source-specific reconstruction estimate is
`repo-derived`; its classical intermediate tools are spectral
calculus, the Hilbert--Schmidt estimate, Hilbert-space weak/norm
convergence and dominated integration, with the local primary
heat theorem used only in the checked scope (104.3). $\square$

## 105. The actual energy scale is equivalent to critical no-loss

**Theorem 105.1 (sufficiency and equivalence for every actual choice).**
For every prescribed sequence $s_n\downarrow0$ and every choice
of actual normalized complex ground states $\psi_{s_n}$ at
$g_n=\chi_cs_n^3$, retain exactly $F_s,\epsilon_c(s),r_s$
of Definition 102.1. Then

$$
r_{s_n}\longrightarrow\infty
\quad\Longleftrightarrow\quad
\operatorname{dist}_{L^2(\mathbb R^4)}
       (F_{s_n},\mathcal O_c)\longrightarrow0.
\tag{105.1}
$$

Proof. Necessity is Corollary 103.2. For sufficiency the actual
eigen-equation in $D(S)$, transported by (81.4), is exactly

$$
\begin{aligned}
(C_s+h_s)F_s&=\frac{\chi_c}{a}U_sF_s,&
h_s&=-\epsilon_c(s)/a=r_ss^8/a>0,\\
F_s&=\frac{\chi_c}{a}R_s(h_s)U_sF_s.
\end{aligned}
\tag{105.2}
$$

Indeed the source multiplier coefficient before replacing
$W_{s^2}$ by $s^{-5}U_s$ is $s^2g_s/a$, and
$s^2g_ss^{-5}/a=\chi_c/a$. The energy shift is
$s^2m_s=-s^2E_s/a=-\epsilon_c(s)/a$. Thus neither the
kinetic coefficient nor a density factor has been absorbed
into the heat clock. Negative attainment is Proposition 75.2,
and bounded multiplication gives the full operator domain as
in Definition 102.1.

Theorem 98.1 supplies $0<h_s\le Hs^{2/3}$ eventually for
a fixed $H$ depending only on the fixed data. If
$r_{s_n}\to\infty$, Theorem 104.2 and $s_n^8/h_{s_n}=a/r_{s_n}$
therefore give

$$
\left\|F_{s_n}-\frac{\chi_c}{a}K_{\rm rec}F_{s_n}\right\|_2
\longrightarrow0.
\tag{105.3}
$$

Compactness of $K_{\rm rec}$ and $\|F_{s_n}\|_2=1$ make
this sequence precompact in the global $L^2$ norm. Any strong
subsequential limit $F$ has norm one and satisfies
$F=(\chi_c/a)K_{\rm rec}F$. The range assertion in
Definition 104.1 gives $F\in D(\mathcal E)$ and
$\mathcal EF=(\chi_c/a)VF$, so $H_cF=0$.
By Theorem 88.1, $F=e^{i\theta}\Phi_c$. Every subsequence
has a further subsequence of this kind; a subsequence whose
distance to $\mathcal O_c$ stayed positive would contradict
it. This proves sufficiency and hence (105.1) for all the
declared complex ground-state choices.

Equivalence (105.1) leaves the behavior of $r_s$ for the
fixed original family undecided. It supplies no actual bounded-$r_s$
sequence and no proof that $r_s\to\infty$ occurs. The exact
energy coefficient, centered crossover, analytic-state preparation
and physical-space interpretation remain unresolved. The
macroscopic trial of Proposition 100.1 retains only its stated
one-sided energy consequence. The compact inverse in (104.1)
and the actual finite-native resolvent in (105.2) are linked by
(104.2), while remaining different operators on different
underlying domains. The observation and resource results
§§92--96 add no preparation premise to (105.1). $\square$

## 追加锚（本行以下为增补区）

## 106. Weighted critical mode and a smaller admissible cutoff error

**Theorem 106.1 (height moment, weighted horizontal energy and parity).**
Retain exactly the source, clock and complex domains of §§81, 87--88.
For the normalized positive mode $\Phi_c$ of Theorem 88.1,

$$
r\Phi_c\in\mathcal Q_E,\qquad
\int r^2\bigl(|\Phi_c|^2+|X\Phi_c|^2+|Y\Phi_c|^2\bigr)d\xi<\infty,
\qquad h_c[r\Phi_c]=a.
\tag{106.1}
$$

The measure-preserving involution
$\sigma(r,y,z,w)=(-r,y,-z,w)$ fixes $V$ and $\Phi_c$.
For any fixed even height cutoff $\eta$ as in (98.6), put
$\eta_R(r)=\eta(r/R)$. Then

$$
\int |\eta_R'|^2|\Phi_c|^2=o(R^{-4})\quad(R\to\infty).
\tag{106.2}
$$

In particular $R_s=s^{-1/2}$ gives $o(s^2)$ in (106.2), and
$\eta_{R_s}\Phi_c$ is admissible between both original faces for
all sufficiently small original real $s>0$.

Proof. Write $p_t(\xi)=p_E(t;0,\xi)$ and $f=V\Phi_c$.
The decay (82.4), $|r|\le N$ and the volume $16R^7$ of
$\{N\le R\}$ imply
$V,rV\in L^2\cap L^\infty$. Consequently
$f,rf\in L^1\cap L^2$ by Hölder and $\|\Phi_c\|_2=1$.
The first coordinate is additive under (82.1), and its heat
marginal is the law of $\sqrt2 B_t$. Thus

$$
\|r p_t\|_1\le\sqrt{2t},\qquad
\|r p_t\|_2^2\le\|p_t\|_\infty\int r^2p_t\,d\xi
 \le Ct^{-5/2},\qquad \|p_t\|_2\le Ct^{-7/4}.
\tag{106.3}
$$

The convolution form of $P_t$ and Young's inequality, in the
unimodular convention already checked in (87.6), now give

$$
\|rP_tf\|_2\le
\begin{cases}
\|rf\|_2+\sqrt{2t}\|f\|_2,&0<t\le1,\\
Ct^{-7/4}\|rf\|_1+Ct^{-5/4}\|f\|_1,&t\ge1.
\end{cases}
\tag{106.4}
$$

Indeed split the output height as the input height plus their
difference in the kernel integral; the corresponding column norms
are exactly those in (106.3). Both lines are integrable on their
stated intervals. Reconstruction (87.2), (88.3) says
$\Phi_c=(\chi_c/a)\int_0^\infty P_tf\,dt$ in $L^2$.
The same integrals converge in the norm of $L^2$ with weight
$r^2$, by (106.4). Closedness of multiplication by $r$ proves
$r\Phi_c\in L^2$.

For bounded smooth real height multipliers $g$ with bounded derivative,
the weak equation (88.1) gives the product identity used in (98.7),

$$
h_c[g\Phi_c]=a\int |g'|^2|\Phi_c|^2.
\tag{106.5}
$$

The multiplier and its square preserve $\mathcal Q_E$, so the
identity follows by the same form test, without separate phase
regularity. Apply it to $g_R=r\eta_R$, and also to $g_R-g_T$.
The already proved height moment implies that $g_R\Phi_c$ is
Cauchy in $L^2$ and in $L^2(Vd\xi)$. The derivatives $g_R'$ are
uniformly bounded and converge pointwise to one; hence
$(g_R'-g_T')\Phi_c\to0$ in $L^2$. Equation (106.5) makes
$g_R\Phi_c$ Cauchy in $\mathcal Q_E$ as well. Its limit is
$r\Phi_c$, and (106.5) gives $h_c[r\Phi_c]=a$.
The distributional product rules
$X(r\Phi_c)=\Phi_c+rX\Phi_c$ and
$Y(r\Phi_c)=rY\Phi_c$ prove the remaining integrability in (106.1).
Finally

$$
\int |\eta_R'|^2|\Phi_c|^2
 \le CR^{-4}\int_{|r|>R}r^2|\Phi_c|^2=o(R^{-4}).
$$

The admissibility argument is exactly the height-strip core
approximation of (98.6), since $sR_s\to0$.
The involution $\sigma$ sends $X$ to $-X$ and $Y$ to $Y$,
preserves Lebesgue measure and fixes the source. It commutes with
$\mathcal E$ and its heat, so fixes $V$. Simplicity and positivity
in Theorem 88.1 then force $\Phi_c\circ\sigma=\Phi_c$.
This proves the parity assertion and completes the proof. $\square$

## 107. A second-order expansion of the complete rational native field

**Definition 107.1 (same-bridge coefficient fields).** In the exact
chart (97.1), write $\xi=(r,z)$, $z\in\mathbb R^3$,
$u(h)=(1,h,h^2/2)$ and
$h_t(r)=(4\pi t)^{-1/2}e^{-r^2/(4t)}$.
Let $\mathbb E_{0,r}^t$ be expectation for the height bridge of
$\sqrt2 B$ from zero to $r$ in time $t$. On that one bridge put

$$
S_t=\sup_{0\le v\le t}|H_v|,\qquad
M_j=\int_0^t H_v^j u(H_v)u(H_v)^{\mathsf T}dv\quad(j=0,1,2),
\qquad
\gamma_M(z)=(4\pi)^{-3/2}(\det M)^{-1/2}e^{-z^{\mathsf T}M^{-1}z/4}.
\tag{107.1}
$$

Derivatives $D\gamma_M,D^2\gamma_M$ are with respect to the
positive definite matrix $M$, with $z$ fixed. Define

$$
\begin{aligned}
p_0(t;r,z)&=h_t(r)\mathbb E_{0,r}^t[\gamma_{M_0}(z)]
              =p_E(t;0,(r,z)),\\
p_1(t;r,z)&=h_t(r)\mathbb E_{0,r}^t[-2D\gamma_{M_0}(z)[M_1]],\\
p_2(t;r,z)&=h_t(r)\mathbb E_{0,r}^t[
 3D\gamma_{M_0}(z)[M_2]+2D^2\gamma_{M_0}(z)[M_1,M_1]],\\
V_j(\xi)&=j_0^{-1}\int_1^\infty p_j(t;\xi)dt\quad(j=1,2),&
V_{\rm t}(\xi)&=j_0^{-1}\int_1^\infty t p_0(t;\xi)dt.
\end{aligned}
\tag{107.2}
$$

These are coefficients for $\beta_s=\varepsilon s/d_0$, not for
a changed source or a heat clock multiplied by $a$.

**Theorem 107.2 (uniform complete-field remainder).** All expectations
and integrals in (107.2) converge absolutely. There are constants
$C,s_0>0$ depending only on the fixed original data such that

$$
\left\|\widetilde U_s-V-\beta_sV_1-\beta_s^2V_2
                 -\lambda s^2V_{\rm t}\right\|_\infty
 \le Cs^{5/2}\qquad(0<s<s_0).
\tag{107.3}
$$

Here $\widetilde U_s$ has exactly the zero extension of (97.1).
In particular (107.3) is uniform in all real phases, including the
expanding original domain and its complement. Moreover

$$
|V_1(r,z)|\le C(1+|r|)^{-4},\qquad
|V_2(r,z)|+V_{\rm t}(r,z)\le C(1+|r|)^{-3},\qquad V_{\rm t}>0,
\tag{107.4}
$$

and $V_j\circ\sigma=(-1)^jV_j$, $V_{\rm t}\circ\sigma=V_{\rm t}$.

Proof. We first justify the differentiated inverse moments; no
infinite-time exchange is taken from a compact heat expansion.
For every fixed integer $m\ge0$, every $t>0$, $r\in\mathbb R$
and $L\ge0$,

$$
h_t(r)\mathbb E_{0,r}^t[
 (\det M_0)^{-1/2}S_t^m\mathbf1_{\{S_t>L\}}]
 \le C_m t^{(m-7)/2}e^{-c_m L^2/t}.
\tag{107.5}
$$

For $m=0$ and $|r|\le L/2$, the left side is $(4\pi)^{3/2}$
times the difference at zero phase between the full canonical
kernel and the kernel additionally killed at $\pm L$.
The Gaussian-mixture identification, including finiteness at zero
phase, is the one proved in (97.6)--(97.8). The canonical part of
(97.9), whose Markov/reflection proof works for every $t>0$,
bounds this difference by $Ct^{-7/2}e^{-cL^2/t}$.
For $|r|>L/2$ simply bound by the full zero-phase kernel and use
(82.3) with $d_E(0,(r,0))\ge|r|$. This proves the $m=0$
assertion for all endpoints. For $m>0$, layer-cake integration
of that assertion gives

$$
L^mCt^{-7/2}e^{-cL^2/t}
 +Cmt^{-7/2}\int_L^\infty v^{m-1}e^{-cv^2/t}dv
 \le C_m t^{(m-7)/2}e^{-c_mL^2/t},
$$

after absorbing the polynomial factor into a weaker Gaussian.
The case $L=0$ follows by the same integral and the full kernel
bound. This proves (107.5), rather than assuming additional
inverse-determinant moments. Since $S_t\ge|r|$, it also bounds
the full moment by
$C_m t^{(m-7)/2}e^{-c_mr^2/t}$, using $L=|r|/2$.

On a path with $S_t<L$ set
$M(\beta)=\int_0^t(1+\beta H_v)^{-2}u(H_v)u(H_v)^{\mathsf T}dv$.
When $|\beta|L\le1/4$, $M(\beta)$ is comparable to $M_0$ in
matrix order, and

$$
\|M_0^{-1/2}M^{(j)}(\beta)M_0^{-1/2}\|
 \le C_j S_t^j\quad(1\le j\le3).
\tag{107.6}
$$

These inequalities follow directly by differentiating the scalar
factor $(1+\beta H_v)^{-2}$ under the finite path integral.
Conjugating by $M_0^{-1/2}$ in the Gaussian, its first three
$\beta$ derivatives are bounded, uniformly over all $z$, by
$C_jS_t^j(\det M_0)^{-1/2}$.
Indeed matrix differentiation produces a polynomial of bounded
degree in $M_0^{-1/2}z$, times $e^{-c|M_0^{-1/2}z|^2}$;
(107.6) bounds every coefficient. Taylor's theorem therefore gives

$$
\left|\gamma_{M(\beta)}-\gamma_{M_0}
 +2\beta D\gamma_{M_0}[M_1]
 -\beta^2\{3D\gamma_{M_0}[M_2]+2D^2\gamma_{M_0}[M_1,M_1]\}\right|
 \le C|\beta|^3S_t^3(\det M_0)^{-1/2}.
\tag{107.7}
$$

The derivatives at zero in this calculation use
$M'(0)=-2M_1$, $M''(0)=6M_2$; hence their coefficients are
exactly (107.2). By (107.5) the averaged remainder is at most
$C|\beta|^3t^{-2}$. The same argument at zero gives

$$
|p_j(t;r,z)|\le Ct^{(j-7)/2}e^{-cr^2/t}\quad(j=0,1,2).
\tag{107.8}
$$

This proves absolute convergence, boundedness and (107.4) by
integration on $t\ge1$. Positivity of $V_{\rm t}$ follows from
(82.3). Reflection of the same bridge by $H\mapsto-H$ sends
$M_j$ to $(-1)^jJM_jJ$, where $J=\operatorname{diag}(1,-1,1)$.
Changing $z$ to $Jz$ in (107.2) proves all the asserted parities.

We now compare to the original native field, retaining its faces.
Put $T=s^{-2}$ and $L=s^{-1/2}$. For small $s$, the extra strip
$(-L,L)$ lies inside $I_s$, and $|\beta_s|L\le1/4$.
Let $p_j^L$ denote (107.2)'s bridge expectations with the common
indicator $S_t<L$. The exact native strip kernel uses $M(\beta_s)$
on this same event, by (97.6). Thus (107.7) gives its expansion.
For $1\le t\le T$, multiply by the actual threshold factor.
The bounds $|e^{\lambda s^2t}-1|\le Cs^2t$ and
$|e^{\lambda s^2t}-1-\lambda s^2t|\le Cs^4t^2$, together with
(107.8), show that its integrated difference from

$$
p_0^L+\beta_sp_1^L+\beta_s^2p_2^L+\lambda s^2t p_0^L
$$

has supremum norm at most $Cs^3$. For clarity, the integrated
Taylor remainder is bounded by $Cs^3\int_1^Tt^{-2}dt$;
the exponential remainder by $Cs^4\int_1^Tt^{-3/2}dt$;
and the cross terms by
$Cs^3\int_1^Tt^{-2}dt+Cs^4\int_1^Tt^{-3/2}dt$.
These bounds are uniform in the terminal point.

On $|r|\le L/2$, removing the extra native strip killing costs
at most $CL^{-5}$ after integration on $[1,T]$, by (97.9).
For the canonical coefficients, (107.5)--(107.7) give

$$
\int_1^\infty|p_j-p_j^L|dt\le CL^{j-5}\quad(j=0,1,2),\qquad
\int_1^\infty t|p_0-p_0^L|dt\le CL^{-3}.
\tag{107.9}
$$

Indeed integrate $t^{(j-7)/2}e^{-cL^2/t}$ and substitute
$t=L^2v$; the resulting integrals are finite for $j\le2$.
Also (107.8) bounds the canonical tails past $T$ by
$Cs^{5-j}$ and the time-weighted tail by $Cs^3$.
The unchanged native integral past $T$ is $Cs^5$ by (82.9).
Keeping the common factor $1/j_0$, these estimates bound the
remainder on $|r|\le L/2$ by

$$
C\{L^{-5}+sL^{-4}+s^2L^{-3}+s^3+s^5\}\le Cs^{5/2}.
\tag{107.10}
$$

On $|r|>L/2$, the native height tail established in the proof
of Lemma 97.2 is $CL^{-5}+Cs^5$, also after zero extension.
The canonical height tail in that proof bounds $V$ by $CL^{-5}$.
Equation (107.4) bounds the other terms by
$CsL^{-4}+Cs^2L^{-3}$. This proves (107.3) on the entire space.
The two original faces were used in the native kernel and its
long-time bound; the strip served only to estimate that kernel.

The local higher-order supplier, Colin de Verdière--Hillairet--Trélat,
[Theorem A, pp.902--903](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf),
has compact positive-time and endpoint quantifiers. The smooth
rational fields, zero drift, constant density, interior pole and
step-three flag checked in §104 meet those local hypotheses.
The global remainder (107.3) instead follows from the explicit
same-bridge estimates above, not an extension of that local scope.
Its raw density factor, signed fixed $\kappa\ne0$ and $B$ clock
remain exactly (81.5), (97.1)--(97.3). $\square$

## 108. The complete Rayleigh correction for the affine amplitude

**Theorem 108.1 (admissible affine-amplitude trial asymptotic).**
With $\eta$ as in Theorem 106.1, put

$$
\nu=\varepsilon/d_0,\quad R_s=s^{-1/2},\quad w_s(r)=1+\beta_sr,
\quad f_s=\eta_{R_s}w_s\Phi_c,\quad
Z_s=\mathcal T_s^{-1}f_s/\|f_s\|_2,
\tag{108.1}
$$

and define the finite real numbers

$$
A_2=\int r^2|Y\Phi_c|^2d\xi,\quad
J_2=\int(V_2+2rV_1)|\Phi_c|^2d\xi,\quad
J_{\rm t}=\int V_{\rm t}|\Phi_c|^2d\xi>0.
\tag{108.2}
$$

For every sufficiently small original real $s>0$, $Z_s$ is a
normalized admissible real vector in the original complex form
domain $\mathcal Q_s$, and

$$
\frac{q_s^c[Z_s]}{s^2}\longrightarrow
\nu^2\{a(1-A_2)-\chi_cJ_2\}
 -\lambda\{a+\chi_cJ_{\rm t}\}.
\tag{108.3}
$$

This is the Rayleigh asymptotic of the specified trial. No sign of
the complete coefficient or asymptotic equality for the actual
infimum is asserted.
The sign of (108.3) and the actual exact-critical ground-state
profile decision remain unresolved.

Proof. Theorem 106.1 makes (108.2) finite, using boundedness of
$V_1,V_2,V_{\rm t}$ and $r\Phi_c\in L^2$.
The cutoff approximation of (98.6), now multiplied by the smooth
bounded-on-its-strip function $w_s$, proves admissibility.
Both original faces lie outside its height support eventually.
Also $\|f_s\|_2\to1$, by $r\Phi_c\in L^2$ and dominated
convergence. Parity eliminates every integral with an odd height
factor times a $\sigma$-even density.

Use the product identity (106.5) with $g=\eta_{R_s}w_s$.
The linear term in $\beta_s$ vanishes by parity, so

$$
h_c[f_s]=a\int|\eta_{R_s}'|^2|\Phi_c|^2
 +a\beta_s^2\int|\eta_{R_s}+r\eta_{R_s}'|^2|\Phi_c|^2
 =a\beta_s^2+o(s^2).
\tag{108.4}
$$

Here (106.2) bounds the first integral; the multiplier in the
second is uniformly bounded and tends pointwise to one.
The exact rational cancellation in (97.2) gives

$$
a\widetilde b_s[f_s]-a b[f_s]
 =a\int(1-w_s^2)\eta_{R_s}^2|Y\Phi_c|^2
 =-a\beta_s^2A_2+o(s^2).
\tag{108.5}
$$

The linear integral is zero, and (106.1) permits dominated
convergence in the quadratic integral. No ordinary phase
$H^1$ assumption has been made.

Finally (107.3) and its parities give

$$
\int(\widetilde U_s-V)|f_s|^2
 =\beta_s^2J_2+\lambda s^2J_{\rm t}+o(s^2).
\tag{108.6}
$$

To check all weighted terms, the $\beta_sV_1$ term has zero
pairing with $\eta_{R_s}^2|\Phi_c|^2$, and its next term is
$2\beta_s^2\int rV_1\eta_{R_s}^2|\Phi_c|^2$.
Its remaining cubic term is odd and zero. The linear cross
terms from $V_2,V_{\rm t}$ are also odd; their terms containing
$\beta_s^2r^2$ cost $O(s^4)$, since $r\Phi_c\in L^2$.
Dominated convergence handles the displayed integrals, while
(107.3)'s remainder costs $O(s^{5/2})\|f_s\|_2^2$.
Combining (108.4)--(108.6) with the original threshold subtraction
$-a\lambda s^2\|f_s\|_2^2$, and then normalizing, proves (108.3).
The real vector supplies only an upper bound on the infimum over
all complex vectors; it has not been identified with an actual
normalized complex ground state. All three results are ordinary
source-specific deductions using the existing variational,
convolution, heat and parity tools, with no claim of kernel
certification or source-independent novelty. $\square$

## 追加锚（本行以下为增补区）
