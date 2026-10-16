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
