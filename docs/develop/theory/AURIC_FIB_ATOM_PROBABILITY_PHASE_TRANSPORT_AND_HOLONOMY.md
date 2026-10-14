# AURIC FIB-ATOM: Probability, Phase Transport and Holonomy

> The definitions, hypotheses and ordinary proofs in this volume concern a
> declared finite probability source, its pure-state extension and specified
> continuous control and measurement tasks.

## 1. Scope, notation and supplier correspondence

The first proof unit studies probability transport, phase loops and the metric
completion of a fixed-mean quotient. The second determines the exact phase
holonomy group and the information about history retained by specified
measurements. Both use the same five-mode source. Statements about paths always
specify whether the coordinates are real lifts, periodic angles or pure rays.

The following abbreviations refer to existing ordinary mathematical suppliers.
They identify results being consumed, including their hypotheses; they do not
assert that a renamed application is an additional general theorem.

| Abbreviation | Source and supplied result | Correspondence used here |
| --- | --- | --- |
| SP | [Symplectic predictive completion](SYMPLECTIC_PREDICTIVE_COMPLETION.md), §§35.1, 35.3–35.7 | The same five modes, affine fiber, primitive phase quotient and negative phase convention; the metric here is exactly SP's metric. |
| HR | [Hidden relations, statistics, phase and seams](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md), C-2.2, C-4.6, C-13.2–C-14.3 | The normalized affine kernel and phase quotient; old phase equals minus the phase here, old relation angle equals $-\chi$, and this metric is twice the old metric. |
| IE | [Information escape, dynamics and thermodynamic action](AURIC_FIB_PYRAMID_INFORMATION_ESCAPE_DYNAMICS_THERMODYNAMIC_ACTION.md), Definition 14.1 and Theorem 14.2, including its global-coordinate proof | Old modes $(0,2,3,5,25)$ map to $(0,1,2,3,13)$; $\nu=d$, $S=I$, $\theta_{\mathrm h}=\tau$, and the base order $(X,Z,Y)$ is permuted to $(X,Y,Z)$. |
| HRM | HR, C-18.4, especially its weighted least-norm formula and orthogonal-residual argument | Its positive diagonal weight is $P$, relation matrix is $D$, information matrix is $G$, and relation velocity is $d\Phi$; the formula is applied pointwise as the reference probability changes. |

These are complete source correspondences for the claims they supply. In
particular, IE supplies all of the flat Fisher transport assertion in §2.2,
including global existence and uniqueness, rather than just its infinitesimal
orthogonality identity. The variable-reference rectangle in §2.9 uses HRM's
minimizer but requires its own finite-path calculation.

Throughout, $\mathbf1$ is the all-ones column, inner products and transposes are
real unless complex amplitudes are displayed, and $\mathbb T=\mathbb R/2\pi\mathbb Z$.
All logarithms are natural. The symbol $b$ for a metric coefficient in §§2.10–2.14
is distinct from the visible base point $b_{\mathrm{vis}}=(X,Y,Z)$.

## 2. Probability transport, phase loops and cone boundaries

### 2.1 Five modes and the positive affine fiber

**Definition 2.1 (Consumed five-mode source).** The mode order is
$\Sigma=(0,1,2,3,13)$. Its occupation vectors, in the coordinate order $(x,y,z)$,
are

$$
(0,0,0),\quad(1,0,0),\quad(0,0,1),\quad(0,1,0),\quad(1,1,0).
$$

The vector $|0\rangle$ is a normalized basis vector representing the empty
occupation, not the zero vector. Write $r=1-Z$ and assume throughout this proof
unit, except in explicitly stated limits,

$$
0<Z<1,\qquad 0<X,Y<r.
$$

SP §35.1 and HR C-2.2 supply the normalized fiber and its kernel direction:

$$
p_\kappa=(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\qquad d=(1,-1,0,-1,1)^{\mathsf T},
$$

$$
\kappa_-:=\max(0,X+Y-r)<\kappa<\kappa_+:=\min(X,Y),
\qquad \frac{dp_\kappa}{d\kappa}=d.
$$

This interval is nonempty under the displayed hypotheses and is precisely the
full-support part of the fiber. The constraints are total probability one and
$X=p_1+p_{13}$, $Y=p_3+p_{13}$, $Z=p_2$. Their normalized tangent kernel is
$\mathbb R d$. These formulas consume the existing affine reconstruction;
subsequent arguments concern transport on this already specified source.

### 2.2 Flat Fisher probability transport

**Mathematical citation 2.2 (Full use of IE Theorem 14.2).** On the positive
simplex set

$$
I(p)=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}},
\qquad \tau(p)=\log\frac{p_0p_{13}}{p_1p_3},
\qquad g_F(v,u)=\sum_s\frac{v_su_s}{p_s}.
$$

Apply IE Definition 14.1 and Theorem 14.2 with the mode and base permutation in
§1. Its entire positive domain becomes

$$
\mathcal B=\{(X,Y,Z):0<Z<1,\ 0<X,Y<1-Z\}.
$$

The supplied derivative and orthogonality identities become

$$
\partial_\kappa\tau=I>0,\qquad
 d\tau(v)=g_F(d,v),\qquad
 v\perp_{g_F}d\ \Longleftrightarrow\ d\tau(v)=0.
$$

For each $b_{\mathrm{vis}}\in\mathcal B$ and every $\tau_0\in\mathbb R$, there
is exactly one positive solution $\kappa=K(b_{\mathrm{vis}},\tau_0)$ of

$$
\frac{\kappa(r-X-Y+\kappa)}{(X-\kappa)(Y-\kappa)}=e^{\tau_0}.
$$

The endpoint justification is part of that supplier: at the lower endpoint the
numerator tends to zero and the denominator has a strictly positive limit; at
the upper endpoint the denominator tends to zero and the numerator has a
strictly positive limit. Coincident zeros occur only within the numerator at
the lower end or within the denominator at the upper end. Hence the limits are
$-\infty$ and $+\infty$, respectively. The positive derivative gives the smooth
implicit inverse on all of $\mathcal B\times\mathbb R$.

Consequently $(X,Y,Z,\tau)$ are global smooth coordinates on the positive
simplex. For any absolutely continuous base path on a compact parameter
interval and any positive initial law over its initial base point, the unique
Fisher-horizontal lift preserves $\tau$ and is
$p_{K(b_{\mathrm{vis}}(t),\tau_0)}$. A closed base path returns exactly the
initial probability law. This is the flat connection supplied by IE, with all
hypotheses mapped; no additional flatness theorem is asserted here.

Flatness in this statement belongs to the horizontal distribution of the
probability projection. It is not a claim about the Riemannian curvature of
$g_F$. Moving $\kappa$ while holding $(X,Y,Z)$ fixed is a vertical motion for
this projection, not this Fisher-horizontal transport.

### 2.3 Phase convention and the instantaneous optimal lift

**Definition 2.3 (Phase and metric normalization).** On the declared complex
pure-state extension use

$$
\psi_s=\sqrt{p_s}\,e^{-i\theta_s},\qquad
\chi=d^{\mathsf T}\theta\pmod{2\pi}.
$$

Pure rays identify common phase. Along a path, $\theta$ and $\chi$ can be taken
as continuous real lifts, and a winding refers to these lifts. Consume SP
§§35.3–35.7 with precisely its negative exponential and normalization:

$$
\omega=\sum_s d\theta_s\wedge dp_s,
$$

$$
g_{FS}=\frac12\sum_s\frac{dp_s^2}{p_s}
 +2\left[\sum_s p_s\,d\theta_s^2-
             \left(\sum_s p_s\,d\theta_s\right)^2\right].
$$

Against HR's positive exponential the sign map is
$\theta^{\rm HR}=-\theta$, $\Phi^{\rm HR}=-\chi$, and
$g_{FS}=2g_{FS}^{\rm HR}$. A projective line has symplectic area $2\pi$ in
this convention. Probability information alone does not specify this extension.

**Proposition 2.4 (Scalar minimizer and its residual).** At a fixed positive
$p=p_\kappa$, prescribe a real relation velocity $u$. Among phase velocities
$v$ satisfying $d^{\mathsf T}v=u$ and $p^{\mathsf T}v=0$, the unique minimizer
of $\sum_s p_sv_s^2$ is

$$
w_s(\kappa)=\frac{d_s}{p_sI},\qquad v=wu,
\qquad \min\sum_s p_sv_s^2=\frac{u^2}{I}.
$$

Proof. This is the scalar application of HRM and the velocity in SP §35.7.
For the explicit residual correspondence, the formula gives
$d^{\mathsf T}w=1$, $p^{\mathsf T}w=0$, and
$\sum p_sw_s^2=1/I$. Every other feasible vector is $wu+z$ with
$d^{\mathsf T}z=p^{\mathsf T}z=0$. Its cross term is

$$
\sum_s p_sw_sz_s=\frac{d^{\mathsf T}z}{I}=0,
$$

so its cost is $u^2/I+\sum p_sz_s^2$. Full positivity makes the last term
zero only for $z=0$. Without the mean-zero gauge, variance has the same minimum
and the minimizers additionally admit arbitrary common phase velocity. This
is a use of the existing weighted minimizer, not a new generic optimization
result. $\square$

### 2.4 Updating the reference probability

**Theorem 2.5 (The variable-reference phase connection).** At fixed means,
declare transport by

$$
d\theta=w(\kappa)\,d\chi.
$$

Thus a pure $\kappa$ displacement leaves all phases fixed. For derivatives in
this open fiber,

$$
d^{\mathsf T}w'=0,\qquad p_\kappa^{\mathsf T}w'=-1.
$$

The vector-valued connection form and its curvature in this abelian real
phase description are

$$
A=d\theta-w(\kappa)d\chi,
\qquad F=dA=-w'(\kappa)d\kappa\wedge d\chi.
$$

In particular $w'$ is never zero, and there is no potential $f$ on a nonempty
open $(\kappa,\chi)$ rectangle with $df=w\,d\chi$.

Proof. Differentiate the identities of Proposition 2.4, using $p'=d$:

$$
0=(d^{\mathsf T}w)'=d^{\mathsf T}w',\qquad
0=(p^{\mathsf T}w)'=d^{\mathsf T}w+p^{\mathsf T}w'=1+p^{\mathsf T}w'.
$$

The exterior derivative gives $F$. If $df=w\,d\chi$, then
$\partial_\kappa f=0$ and $\partial_\chi f=w$, so equality of mixed partials
would force $w'=0$, a contradiction. The tempting section
$\theta=w(\kappa)\chi$ instead has

$$
d\theta=w\,d\chi+\chi w'\,d\kappa.
$$

Its second term is essential and it does not define the declared transport.
In this five-mode gauge $w_2=w'_2=0$, so a nonzero $w'$ cannot be pure common
phase: a common vector with zero middle component is zero. In the general
matrix setting of §2.9 nonzero ambient curvature can, in contrast, be only
common phase. $\square$

### 2.5 A finite rectangle

**Theorem 2.6 (Exact rectangular residual).** Let $\kappa_0,\kappa_1$ be
interior points of the same fiber and let $\alpha\in\mathbb R$. Traverse the
four legs

$$
(\kappa_0,0)\to(\kappa_1,0)\to(\kappa_1,\alpha)
\to(\kappa_0,\alpha)\to(\kappa_0,0).
$$

The real phase residual is exactly

$$
h=\alpha\bigl(w(\kappa_1)-w(\kappa_0)\bigr),
\qquad d^{\mathsf T}h=0,
\qquad p_{\kappa_0}^{\mathsf T}h=-\alpha(\kappa_1-\kappa_0).
$$

Proof. The first and third legs have $d\chi=0$. The other two legs integrate
to $\alpha w(\kappa_1)$ and $-\alpha w(\kappa_0)$. The relation identity
follows from $d^{\mathsf T}w=1$. Since
$p_{\kappa_0}=p_{\kappa_1}-(\kappa_1-\kappa_0)d$,

$$
p_{\kappa_0}^{\mathsf T}w(\kappa_1)=-(\kappa_1-\kappa_0),
\qquad p_{\kappa_0}^{\mathsf T}w(\kappa_0)=0.
$$

This proves the weighted identity for finite rectangles without replacing the
integral by an infinitesimal approximation. $\square$

### 2.6 A full-interference witness

**Proposition 2.7 (A loop invisible to the reduced task).** There are two
positive pure states with equal reduced coordinates and different
fixed-reference coherence statistics, connected by a transport rectangle.

Proof. Take

$$
X=Y=\frac25,\quad Z=\frac15,\quad
\kappa_0=\frac15,\quad \kappa_1=\frac1{10}.
$$

The two probability vectors and weights are

$$
p_{\kappa_0}=\frac15(1,1,1,1,1),\qquad
p_{\kappa_1}=\left(\frac1{10},\frac3{10},\frac15,\frac3{10},\frac1{10}\right),
$$

$$
w(\kappa_0)=\frac14(1,-1,0,-1,1),\qquad
w(\kappa_1)=\frac18(3,-1,0,-1,3).
$$

Theorem 2.6 therefore gives
$h=\alpha(1,1,0,1,1)/8$. Start with all phases zero and take
$\alpha=4\pi$. The returned probability is uniform, while the output state is

$$
\psi_{\rm out}=\frac1{\sqrt5}(-i,-i,1,-i,-i),\qquad
|\langle\psi_{\rm in},\psi_{\rm out}\rangle|^2
=\left|\frac{1-4i}{5}\right|^2=\frac{17}{25}.
$$

For the explicitly added fixed-reference observable
$A_{02}=|0\rangle\langle2|+|2\rangle\langle0|$, the expectation changes from
$2/5$ to zero, since it is $2\operatorname{Re}(\overline\psi_0\psi_2)$.
Thus the same $(X,Y,Z,\kappa,\chi\bmod2\pi)$ does not determine all full
interference statistics. The task retaining only occupation-phase-symmetry
invariants identifies these states; $A_{02}$ is not invariant under that full
symmetry. Observability here depends on declaring the extra phase reference
and observable, rather than changing the reduced task silently. $\square$

### 2.7 Winding and exact ray return at fixed probability

**Theorem 2.8 (Arithmetic of the fixed-reference optimal lift).** Fix a
positive probability and use $\theta=\theta^{\rm in}+w\chi$ with a continuous
real change $\Delta\chi=2\pi q$, $q\in\mathbb Z_{>0}$. The ray returns if and
only if

$$
qw_s\in\mathbb Z\quad\text{for every }s\in\Sigma.
$$

There is no one-circle return. If all components of $w$ are rational, the least
positive return count is their least common denominator in reduced form. If
any component is irrational, there is no finite integer-circle return.

Proof. Ray return means all factors $e^{-2\pi i qw_s}$ are the same. Because
$p_2>0$ and $w_2=0$, the common factor must be one. This proves both directions
of the integer criterion. The positive components satisfy

$$
0<w_0=\frac{1/p_0}{I}<1,\qquad
0<w_{13}=\frac{1/p_{13}}{I}<1,
$$

so $q=1$ cannot work. A positive integer simultaneously clearing all reduced
denominators is exactly a multiple of their least common multiple. A nonzero
integer times an irrational component cannot be an integer. $\square$

For the uniform law the first return is four circles, $\Delta\chi=8\pi$.
After one circle the state and squared overlap, from initial zero phases, are

$$
\frac1{\sqrt5}(-i,i,1,i,-i),\qquad \frac1{25}.
$$

There is no uniform finite upper bound on the return count, even with fixed
means. Indeed, fix any $r\in(0,1)$ and $X=Y=r/2$, $Z=1-r$. For every integer
$q\ge2$, choose

$$
p_0=p_{13}=\frac{r}{2q},\qquad
p_1=p_3=\frac{r(q-1)}{2q}.
$$

Then $I=4q^2/[r(q-1)]$ and

$$
w_0=w_{13}=\frac{q-1}{2q},\qquad
w_1=w_3=-\frac1{2q},\qquad w_2=0.
$$

The negative component has reduced denominator $2q$ and this count clears all
components, so the least return is exactly $2q$. This is an arithmetic fact
about this continuous lift, not a period statement for an integer automaton.

### 2.8 A broader fixed-probability variational comparison

**Theorem 2.9 (One lifted winding with and without ray closure).** Fix any
positive $p$ and define the dimensionless quadratic action on absolutely
continuous real phase paths on $[0,1]$ by

$$
\mathcal A(\theta)=\int_0^1
\operatorname{Var}_p(\dot\theta(t))\,dt,
\qquad
\operatorname{Var}_p(v)=\sum_s p_sv_s^2-(p^{\mathsf T}v)^2.
$$

Require $d^{\mathsf T}(\theta(1)-\theta(0))=2\pi$ as a real equation.
Without ray closure the minimum is $4\pi^2/I$. With full ray closure the
minimum is

$$
4\pi^2\min_{\substack{k\in\mathbb Z^5\\d^{\mathsf T}k=1}}
\operatorname{Var}_p(k),
$$

and the lattice minimum is attained. These paths are not restricted to the
transport law of Theorem 2.5.

Proof. Put $\bar v=\int_0^1\dot\theta\,dt$. The quadratic identity

$$
\int_0^1\operatorname{Var}_p(\dot\theta)\,dt
=\operatorname{Var}_p(\bar v)
 +\int_0^1\operatorname{Var}_p(\dot\theta-\bar v)\,dt
$$

is obtained by expanding and canceling the mean cross term. Equality with the
first term holds precisely when $\dot\theta-\bar v$ is a common vector almost
everywhere. Thus Jensen equality allows an arbitrary common-phase velocity;
it does not require each component velocity to be constant in a fixed gauge.
Proposition 2.4 applied after subtracting $p^{\mathsf T}\bar v\,\mathbf1$
gives the unconstrained minimum, attained by $\dot\theta=2\pi w$.

Full ray closure is equivalent to

$$
\theta(1)-\theta(0)=2\pi k+\gamma\mathbf1,
\qquad k\in\mathbb Z^5,\quad\gamma\in\mathbb R.
$$

Since $d^{\mathsf T}\mathbf1=0$, the winding condition is exactly
$d^{\mathsf T}k=1$. Variance ignores $\gamma\mathbf1$, and the constant-velocity
path realizes each such endpoint and its Jensen lower bound.

To prove attainment, integer translation by $k_2\mathbf1$ allows $k_2=0$
without changing the constraint or cost. The identity

$$
\operatorname{Var}_p(k)=\sum_{i<j}p_ip_j(k_i-k_j)^2
\ge p_2\sum_{i\ne2}p_i k_i^2
$$

makes every bounded-cost lattice sublevel finite. The admissible set is
nonempty, for example $k=e_0$, so minimizing over the finite sublevel below
that candidate proves attainment. $\square$

At uniform probability, $d^{\mathsf T}k=1$ implies that the integer tuple is
nonconstant. A nonconstant five-tuple has at least four unequal unordered
pairs: a class of size $a\in\{1,2,3,4\}$ and its complement contribute
$a(5-a)\ge4$ pairs. Every unequal integer pair has squared difference at least
one. Hence $\operatorname{Var}_p(k)\ge4/25$, with equality for $e_0$ or
$e_{13}$, and also for $-e_1$ or $-e_3$. Therefore

$$
\mathcal A_{\rm closed}=\frac{16\pi^2}{25},\qquad
\mathcal A_{\rm horizontal}=\frac{\pi^2}{5},\qquad
\frac{\mathcal A_{\rm closed}}{\mathcal A_{\rm horizontal}}=\frac{16}{5}.
$$

The horizontal one-winding path itself is not ray closed. More generally, at
double symmetry the transport law in §3.1 cannot execute any odd-winding ray
return: it keeps the two positive-$d$ phase increments equal and the two
negative-$d$ increments equal, so a ray return with middle increment zero has
even winding. The finite closed minimum above belongs to the larger
variational class. If one required only $\Delta\chi=0\bmod2\pi$ without the
real one-winding condition, a constant path would give zero instead. No
physical energy or time unit is specified by this quadratic action.

### 2.9 Several relation directions

**Theorem 2.10 (Variable matrix reference and its exact rectangle).** Let
$p(\xi)=p^{\rm ref}+D\xi\in\mathbb R^n$ be positive and normalized on an open
parameter domain, where $D\in\mathbb R^{n\times k}$ has full column rank and
$\mathbf1^{\mathsf T}D=0$. Define

$$
P=\operatorname{diag}(p),\qquad G=D^{\mathsf T}P^{-1}D,
\qquad W=P^{-1}DG^{-1},\qquad \Phi=D^{\mathsf T}\theta.
$$

Use real lifted phase coordinates for arbitrary real $D$. Then

$$
D^{\mathsf T}W=I_k,\qquad p^{\mathsf T}W=0,
$$

and HRM's least-norm formula gives the pointwise optimal transport
$d\theta=W(\xi)d\Phi$. For a rectangle moving from $\xi_0$ to
$\xi_1=\xi_0+\delta\xi$ at fixed $\Phi$, then by $a$ in $\Phi$, then back in
$\xi$, then by $-a$, the exact residual satisfies

$$
h=[W(\xi_1)-W(\xi_0)]a,\qquad D^{\mathsf T}h=0,
\qquad p(\xi_0)^{\mathsf T}h=-\delta\xi^{\mathsf T}a.
$$

Proof. Full rank and positivity make $G$ positive definite. The identities
follow by multiplication, with $p^{\mathsf T}P^{-1}=\mathbf1^{\mathsf T}$.
The supplier's algebra is pointwise independent of a choice of cycle labels:
for any residual $z$ with $D^{\mathsf T}z=0$,
$(Wa)^{\mathsf T}Pz=a^{\mathsf T}G^{-1}D^{\mathsf T}z=0$.
Thus it applies to the stated real matrix, including the mean-zero minimizer;
only positivity, rank and normalization are used in this correspondence.

Only the two $\Phi$ legs contribute to the integral. Finally
$p(\xi_0)=p(\xi_1)-D\delta\xi$ gives

$$
p(\xi_0)^{\mathsf T}W(\xi_1)
=-\delta\xi^{\mathsf T},\qquad
p(\xi_0)^{\mathsf T}W(\xi_0)=0,
$$

which proves the rectangle identity. The straight probability legs stay
positive whenever their two endpoints are positive, by convexity. $\square$

If $\operatorname{im}D=\mathbf1^\perp$, then
$\ker D^{\mathsf T}=\mathbb R\mathbf1$. Normalization of the initial
probability therefore sharpens the residual to

$$
h=-(\delta\xi^{\mathsf T}a)\mathbf1,
\qquad \psi_{\rm out}=e^{i\delta\xi^{\mathsf T}a}\psi_{\rm in}.
$$

In this case the ambient phase connection has a common geometric phase but
its residual is trivial on rays. A proper subspace of normalized probability
directions can leave relative phase, as Proposition 2.7 shows. Ambient curvature,
projective holonomy and Riemannian curvature must consequently be separated.

For arbitrary real $D$, $D^{\mathsf T}\theta$ is not automatically an angle
on the standard phase torus: changing $\theta$ by $2\pi z$, $z\in\mathbb Z^n$,
changes $\Phi$ by $2\pi D^{\mathsf T}z$. A map to the standard $k$-torus
requires $D^{\mathsf T}\mathbb Z^n\subseteq\mathbb Z^k$, equivalently integral
entries. Primitive lattice hypotheses are additionally needed for the
associated kernel to be connected. More general period lattices require an
explicit lattice map. SP §35.13 provides an integral relation-coordinate
example; the real theorem here does not assume that every $D$ has that property.

### 2.10 The actual phase quotient and its metric

**Mathematical application 2.11 (Horizontal coefficients of a quotient).**
Fix the means and quotient pure rays by the three occupation phase actions
$\theta_s\mapsto\theta_s+t_Xx_s+t_Yy_s+t_Zz_s$. SP §§35.4–35.7 supply the
positive quotient cylinder with primitive $2\pi$-periodic coordinate $\chi$
and

$$
\omega_{\rm red}=d\chi\wedge d\kappa,\qquad
 g_{\rm red}=\frac I2d\kappa^2+\frac2I d\chi^2.
$$

For the explicit correspondence, the integer inverse formulas are

$$
\theta_1=\theta_0+\vartheta_X,\quad
\theta_3=\theta_0+\vartheta_Y,\quad
\theta_2=\theta_0+\vartheta_Z,\quad
\theta_{13}=\theta_0+\vartheta_X+\vartheta_Y+\chi.
$$

They show that no extra finite quotient changes the period of $\chi$ in the
positive cylinder. The annihilator of $d$ is spanned by
$\mathbf1,x,y,z$, which are independent on the five modes. Thus minimizing
phase variance at fixed $d\chi$ is exactly minimizing over the removed phase
orbit, and Proposition 2.4 gives its coefficient $2/I$. The probability
coefficient is $\tfrac12\sum d_s^2/p_s=I/2$; the full metric has no mixed
probability-phase term. These are quotient metric coefficients, not a
pullback along an integrable section with differential $d\theta=w\,d\chi$.
Theorem 2.5 rules out that proposed section.

Put $b(\kappa)=2/I(\kappa)$. Then

$$
g_{\rm red}=b^{-1}d\kappa^2+b\,d\chi^2,\qquad
\det g_{\rm red}=1,\qquad d\mathrm{Area}=d\kappa\,d\chi.
$$

Here the area is the positive density; the ordered two-form above fixes the
symplectic orientation. Endpoints are treated by metric completion and the
actual orbit strata, not by assuming every closed level is a smooth reduction.

### 2.11 Intrinsic Gaussian curvature

**Theorem 2.12 (Positive Gaussian curvature).** On every positive fixed-mean
quotient cylinder,

$$
K=-\frac12 b''
=\frac{I''}{I^2}-\frac{2(I')^2}{I^3}>0,
$$

where, with $B=\{0,1,3,13\}$,

$$
I'=-\sum_{s\in B}\frac{d_s}{p_s^2},\qquad
I''=2\sum_{s\in B}\frac1{p_s^3}.
$$

More precisely,

$$
K=\frac2{I^3}\sum_{\substack{i<j\\i,j\in B}}
\frac{(p_i-d_id_jp_j)^2}{p_i^3p_j^3}.
$$

Proof. This calculation is intrinsic to the displayed metric. Introduce
meridian arclength $u$ by $du=d\kappa/\sqrt b$ and put $f(u)=\sqrt{b(\kappa(u))}$.
The metric is $du^2+f^2d\chi^2$. Its nonzero Christoffel symbols are
$\Gamma^u_{\chi\chi}=-ff'$ and
$\Gamma^\chi_{u\chi}=\Gamma^\chi_{\chi u}=f'/f$. Substitution in the
Riemann curvature formula gives $R_{u\chi u\chi}=-ff''$, hence
$K=-f''/f$. Derivatives in $u$ obey

$$
\frac{df}{du}=\frac{b'}2,\qquad
\frac{d^2f}{du^2}=\frac{b''\sqrt b}{2}.
$$

This proves $K=-b''/2$. Differentiating $b=2/I$ gives the expression in $I$.
To see its sign, expand the numerator as unordered pairs:

$$
\begin{aligned}
\frac{I^3K}{2}
&=\left(\sum_i\frac1{p_i}\right)
  \left(\sum_j\frac1{p_j^3}\right)
 -\left(\sum_i\frac{d_i}{p_i^2}\right)^2\\
&=\sum_{i<j}
 \left(\frac1{p_ip_j^3}+\frac1{p_jp_i^3}
             -\frac{2d_id_j}{p_i^2p_j^2}\right)\\
&=\sum_{i<j}\frac{(p_i-d_id_jp_j)^2}{p_i^3p_j^3}.
\end{aligned}
$$

The diagonal terms cancel because $d_i^2=1$ on $B$. Opposite-sign pairs have
numerator $(p_i+p_j)^2>0$; such pairs exist, so the sum is strictly positive.
This is Gaussian curvature of a probability-phase quotient, not the
vector-valued $F$ of Theorem 2.5 or a curvature of physical space. $\square$

### 2.12 Endpoint multiplicities and cone angles

**Theorem 2.13 (Metric completion).** At the lower and upper endpoints let
$\nu_-$ and $\nu_+$ count vanishing bottom probabilities. Then

$$
\nu_-=\begin{cases}2&X+Y=r,\\1&X+Y\ne r,\end{cases}
\qquad
\nu_+=\begin{cases}2&X=Y,\\1&X\ne Y.\end{cases}
$$

The two completion cone angles are $2\pi/\nu_-$ and $2\pi/\nu_+$. The four
possibilities are $(2\pi,2\pi)$, $(\pi,2\pi)$, $(2\pi,\pi)$ and $(\pi,\pi)$.

Proof. At the lower end, either $p_{13}$ alone vanishes, or $p_0$ alone
vanishes, or both vanish when $X+Y=r$. At the upper end, either $p_1$ alone,
$p_3$ alone, or both vanish when $X=Y$. All other bottom masses have a positive
limit; the middle mass is the fixed positive number $Z$.

Let $t=\kappa-\kappa_-$ or $t=\kappa_+-\kappa$ be inward distance in the
affine probability coordinate. Each vanishing mass is exactly $t$, so

$$
I=\frac\nu t+O(1),\qquad
b=\frac{2t}{\nu}+O(t^2).
$$

The meridian distance from the end is

$$
\rho=\int_0^t\frac{ds}{\sqrt{b(s)}}
=\sqrt{2\nu t}\,(1+O(t)).
$$

Inverting this expression gives
$t=\rho^2/(2\nu)(1+O(\rho^2))$ and therefore

$$
g_{\rm red}=d\rho^2+
\frac{\rho^2}{\nu^2}(1+O(\rho^2))d\chi^2.
$$

The circumference divided by radius tends to $2\pi/\nu$. Finite meridian
distance and vanishing circle diameter add exactly one point at each end.
On compact subintervals the metric is regular; near each end it is comparable
to the displayed finite cone. The completion is consequently compact, hence
proper, with two endpoint strata and the open cylinder between them. The
rational coefficients have smooth expansions in $t$, so for $\nu=1$ the polar
coefficient has the smooth even expansion with unit initial slope; for
$\nu=2$ it has half that slope and cone angle $\pi$. This metric statement
does not replace the hypotheses for smooth symplectic reduction. $\square$

Both symmetry walls meet the interior of $\mathcal B$. Double zeros at a fiber
endpoint thus need not mean that the visible mean is on the external boundary
of the pyramid. HR C-14.3 supplies the same cone interpretation at its half
metric scale; constant metric rescaling changes lengths and curvature, but not
the angles. Sjamaar–Lerman's stratified reduction framework is appropriate for
singular levels; the concrete angles above follow from the explicit metric.

### 2.13 Curvature integral and area

**Corollary 2.14 (Smooth curvature and endpoint deficits).** The endpoint
slopes and total smooth curvature are

$$
b'(\kappa_-)=\frac2{\nu_-},\qquad
b'(\kappa_+)=-\frac2{\nu_+},
$$

$$
\int_{\rm interior}K\,d\mathrm{Area}
=2\pi\left(\frac1{\nu_-}+\frac1{\nu_+}\right).
$$

Adding the two cone deficits gives $4\pi$. The area is
$2\pi(\kappa_+-\kappa_-)$.

Proof. The endpoint expansions in Theorem 2.13 differentiate to the stated
one-sided slopes; the coefficients are rational smooth functions after the
pole is removed. Integration of $-b''/2$ against $d\kappa\,d\chi$ gives

$$
-\pi\bigl[b'(\kappa_+)-b'(\kappa_-)\bigr]
=2\pi\left(\nu_-^{-1}+\nu_+^{-1}\right).
$$

Each deficit is $2\pi-2\pi/\nu$, and their sum with the smooth integral is
$4\pi$. Integrating the unit area density gives the area formula. In
particular, curvature is strictly positive throughout the interior; it is not
concentrated only at the endpoints. $\square$

### 2.14 The doubly symmetric quotient

**Corollary 2.15 (Constant curvature with two half-angle ends).** If
$X=Y=r/2$, then $p_0=p_{13}=\kappa$ and
$p_1=p_3=r/2-\kappa$. Set

$$
\kappa=\frac r4(1-\cos\vartheta),\qquad 0<\vartheta<\pi.
$$

The reduced metric becomes

$$
g_{\rm red}=\frac r2\left(d\vartheta^2+
                  \frac{\sin^2\vartheta}{4}d\chi^2\right),
\qquad K=\frac2r,\qquad \mathrm{Area}=\pi r.
$$

Proof. Here

$$
I=\frac2\kappa+\frac2{r/2-\kappa}
=\frac r{\kappa(r/2-\kappa)},\qquad
b=\frac{2\kappa(r/2-\kappa)}r.
$$

Substitution and $d\kappa=(r/4)\sin\vartheta\,d\vartheta$ give the metric.
Locally $\varphi=\chi/2$ gives the round metric of squared radius $r/2$;
globally $\varphi$ has period $\pi$, so the completion is the quotient of that
round sphere by its order-two axial rotation. Thus each pole has angle $\pi$.
The curvature follows either from this local round metric or Theorem 2.12,
and the area is $2\pi(r/2)$. This is dimensionless probability geometry.
$\square$

### 2.15 Classical sources and precise authority

The literature supplies methods with explicit normalization and support
conditions. The following uses distinguish that background from the concrete
calculations in this proof unit.

| Source | Passage and authority used |
| --- | --- |
| Miguel Abreu, [Toric Kähler metrics: cohomogeneity one examples of constant scalar curvature in action-angle coordinates](https://arxiv.org/abs/0912.0491) | §3, metric (5) and scalar formula (6), p. 12: the inverse-Hessian description and scalar curvature in action-angle coordinates. Its normalization footnote explicitly distinguishes the earlier convention. |
| Miguel Abreu, [Kähler geometry of toric manifolds in symplectic coordinates](https://www.math.tecnico.ulisboa.pt/~mabreu/preprints/symp-coords.pdf) | §2.2 gives the Hessian/inverse-Hessian metric; equations (3.2)–(3.3), p. 11, have the earlier scalar convention, and Example 3.1 gives scalar value one on its canonical sphere. The Gaussian curvature here is derived in Theorem 2.12. |
| Barry Simon, [Holonomy, the Quantum Adiabatic Theorem, and Berry's Phase](https://authors.library.caltech.edu/records/2pepc-k9f58), Physical Review Letters 51, 2167–2170 | The opening line-bundle construction uses an isolated nondegenerate eigenvalue, and the subsequent parallel-transport discussion identifies the geometric phase with holonomy. This supplies the geometric language, not an adiabatic realization of the present control law. |
| Reyer Sjamaar and Eugene Lerman, [Stratified symplectic spaces and reduction](https://annals.math.princeton.edu/1991/134-2/p05), Annals of Mathematics 134(2), 375–422 | The primary abstract states that the reduction result distinguishes a free regular level from a singular level which is a union of symplectic strata. It supports the stratified viewpoint, not an assumption that a singular quotient is a smooth surface. |

For a direct coordinate match to the Abreu metrics, take $x=\kappa$ and
$y=-\chi$. Then $dx\wedge dy=d\chi\wedge d\kappa$ and the metric is
unchanged by the angle sign. The local symplectic potential
$u(\kappa)=\tfrac12\sum_{s\in B}p_s\log p_s$ has Hessian
$u''=I/2=1/b$, exactly the Hessian block used in those formulas.

In the convention of Abreu's formula (6), the one-dimensional real scalar
curvature is $-b''=2K$. The earlier symplectic-coordinate scalar formula has a
factor $1/2$ in front of the inverse-Hessian second derivative and gives
$-b''/2$ for this matrix. These differently normalized scalar quantities must
not be equated by name. Theorem 2.12 fixes $K$ intrinsically and is independent
of that naming convention.

The cited methods are literature-attested. The finite-path, variational and
curvature applications here are repo-derived ordinary proofs, with the
existing suppliers consumed as specified in §1. This classification assigns
provenance and does not certify priority.

### 2.16 Interpretation of the three geometric objects

The Fisher connection of §2.2 transports probability across visible means
while preserving the real log odds $\tau$. Its global horizontal leaves give
exact probability return. The phase connection of §2.4 instead moves within a
fixed-mean probability fiber and updates the locally optimal phase velocity
$w$. Its finite residual measures the dependence on the chosen control path.
The metric of §2.10 belongs to the quotient by occupation phases; its intrinsic
Gaussian curvature and cone angles describe that quotient's geometry.

These three objects coexist without sharing a curvature assertion. The phase
menu of Proposition 2.7 retains information deliberately removed by the quotient.
The matrix $W$ ties a local least-cost phase response to a finite residual when
the reference probability changes, but an arbitrary real matrix does not
supply a periodic angle lattice. All continuous controls and readouts in this
proof unit are declared mathematical operations; they do not follow from the
finite occupation alphabet alone.

## 3. Exact holonomy groups, symmetry and observable history

### 3.1 Admissible controls and winding sectors

**Definition 3.1 (The transport history model).** Use the full-support fiber,
$d$, $I$, $w$ and negative phase convention of §2, with fixed means. An
admissible control on a compact time interval is a piecewise $C^1$ path
$(\kappa(t),\chi(t))$ in the open fiber times $\mathbb R$, or an absolutely
continuous such path, with finite phase variation. Its state lift satisfies

$$
\dot p=d\dot\kappa,\qquad
\dot\theta=w(\kappa)\dot\chi.
$$

A base/phase loop has $\kappa(T)=\kappa(0)=\kappa_0$ and
$\chi(T)-\chi(0)=2\pi m$ for some $m\in\mathbb Z$. This definition closes the
periodic control base; it does not presume full state or ray return. The
continuous lift $\chi$ keeps its actual integer winding. With the initial
middle phase chosen to be zero, $w_2=0$ keeps $\theta_2=0$.

The real residual and its relation charge are

$$
h=\int_0^T w(\kappa(t))\dot\chi(t)\,dt,
\qquad h_2=0,\qquad d^{\mathsf T}h=2\pi m.
$$

The last identity follows directly from $d^{\mathsf T}w=1$. Continuity on a
compact interval keeps any such positive path in a compact subinterval of the
fiber; thus $w$ is bounded and these integrals exist. Zero winding means
$m=0$, not merely that the physical phase circle is closed. This control law
moves vertically in IE's probability projection and is different from the
Fisher-horizontal motion of §2.2. It is also a restriction of the arbitrary
phase paths used for the variational comparison of §2.8.

### 3.2 The real zero-winding holonomy space

**Theorem 3.2 (Finite constructive reachability).** Write

$$
E_-:\ X+Y=r,\qquad E_+:\ X=Y,
$$

and define the real vector space

$$
V_b=\{h\in\mathbb R^5:h_2=0,\ d^{\mathsf T}h=0,
\ E_-\Rightarrow h_0=h_{13},\ E_+\Rightarrow h_1=h_3\}.
$$

Its dimension is $3-\mathbf1_{E_-}-\mathbf1_{E_+}$. The exact set of
zero-winding residuals is $V_b$. For every chosen $\kappa_0$, at most three
rectangles with heights preselected independently of the target realize every
vector in $V_b$.

Proof. Introduce the four poles

$$
\lambda_0=X+Y-r,\qquad \lambda_1=X,\qquad
\lambda_3=Y,\qquad \lambda_{13}=0.
$$

For bottom modes,

$$
p_s=d_s(\kappa-\lambda_s),\qquad
w_s(\kappa)=\frac1{I(\kappa)(\kappa-\lambda_s)}.
$$

The same-sign poles collide precisely on $E_-$ or $E_+$. An opposite-sign
collision would require one of $X,Y,r-X,r-Y$ to vanish, excluded by the
strict mean hypotheses. Let $g=4-\mathbf1_{E_-}-\mathbf1_{E_+}$ be the number
of distinct pole groups. Components of $w$ are equal within each group. The
space $U_b$ of vectors with zero middle component and these group equalities
has dimension $g$. On it, $d^{\mathsf T}$ is a nonzero functional, so
$V_b=U_b\cap\ker d^{\mathsf T}$ has dimension $g-1$.

Choose any $g$ distinct interior heights, one of them $\kappa_0$. The matrix
with rows indexed by the distinct poles and columns by these heights,

$$
M_{aj}=\frac1{\kappa_j-\lambda_a},
$$

is nonsingular. To prove this directly, suppose a row combination vanishes at
all $g$ heights. The rational function
$R(t)=\sum_a c_a/(t-\lambda_a)$ then has $g$ distinct zeros away from the
poles. Its numerator over $\prod_a(t-\lambda_a)$ has degree at most $g-1$,
so that numerator is identically zero. Evaluating its residue at each pole
gives $c_a\prod_{b\ne a}(\lambda_a-\lambda_b)=0$, hence every $c_a=0$.

Scaling each column by the nonzero number $1/I(\kappa_j)$ preserves
independence. Thus the $g$ vectors $w(\kappa_j)$ are linearly independent in
$U_b$. All lie in the affine hyperplane $d^{\mathsf T}w=1$, and their
$g-1$ differences from $w(\kappa_0)$ are a basis of $V_b$: a linear relation
among these differences would be a linear relation among the $g$ vectors,
while their number is the dimension of $V_b$.

For an arbitrary zero-winding loop,

$$
h=\int_0^T\bigl(w(\kappa(t))-w(\kappa_0)\bigr)\dot\chi(t)\,dt.
$$

Every integrand vector is in $V_b$, proving inclusion. Conversely write an
arbitrary $h\in V_b$ in the basis just constructed:

$$
h=\sum_{j=1}^{g-1}a_j\bigl(w(\kappa_j)-w(\kappa_0)\bigr).
$$

The rectangle of Theorem 2.6 with probability height $\kappa_j$ and real
phase height $a_j$ realizes the corresponding summand. Concatenate the
rectangles at $(\kappa_0,0)$. Negative coefficients are permitted by reversing
the phase leg. This is a finite piecewise linear, hence admissible, path and
realizes the vector exactly. No approximation by a dense subgroup is used.
The construction imposes no uniform speed, energy or phase-height bound.
$\square$

The same argument determines every winding sector, not only zero winding:

$$
\mathcal R_m=2\pi m\,w(\kappa_0)+V_b,\qquad m\in\mathbb Z.
$$

Indeed subtraction of $2\pi m w(\kappa_0)$ gives the integral of
$w-w(\kappa_0)$, hence the inclusion. Conversely first perform $m$ fixed-height
circles, whose residual is $2\pi m w(\kappa_0)$, then the finite rectangle
construction for the desired remainder. Both paths have the same initial and
final periodic base point.

### 3.3 The complete phase group and all-sector sufficiency

**Theorem 3.3 (Exact compact holonomy group).** Map real residuals
componentwise modulo $2\pi$, retaining the middle-fixed gauge. The reachable
group is abelian and is isomorphic to

$$
\mathcal H_b\cong
\begin{cases}
\mathbb T^3,&\text{neither }E_-\text{ nor }E_+,\\
\mathbb T^2,&\text{exactly one of }E_-,E_+,\\
\mathbb T\times\mathbb Z_2,&\text{both }E_-,E_+.
\end{cases}
$$

The image of $V_b$ is the identity component. These are exact reachable
subgroups, not merely their topological closures.

Proof. Let group $a$ contain $m_a$ modes with their common sign
$\varepsilon_a\in\{1,-1\}$. Its common phase is $\phi_a\in\mathbb T$.
Every real reachable vector belongs to $U_b$ and has $d^{\mathsf T}h\in2\pi\mathbb Z$.
Consequently every reachable phase is in the character kernel

$$
\sum_{a=1}^g c_a\phi_a=0\pmod{2\pi},
\qquad c_a=m_a\varepsilon_a.
$$

We prove sufficiency constructively. For any point in this kernel, choose one
real representative $v_a$ of each group phase and copy it to each mode of that
group, setting $v_2=0$. The kernel condition gives
$\sum_a c_av_a=2\pi n$ for an integer $n$. Therefore

$$
v-2\pi n w(\kappa_0)\in V_b.
$$

The all-sector construction of §3.2 realizes this vector after $n$ fixed-height
circles, hence realizes the original phase class exactly. This proves every
candidate is reachable, including nonidentity components.

To determine the identity component, let $q=\gcd(c_1,\ldots,c_g)>0$. Changing
the grouped real representatives by $2\pi\ell_a$ changes $n$ by
$\sum_a c_a\ell_a$, whose possible values are exactly $q\mathbb Z$ by
Bézout's identity. Thus the residue of $n$ modulo $q$ labels the components.
A class has a representative in $V_b$ exactly when this residue is zero:
choose integers $\ell_a$ with $\sum c_a\ell_a=-n$, then the changed
representatives have relation sum zero and are reached by rectangles alone.

For completeness, the elementary integer-character structure follows from
the Euclidean algorithm: integer column operations reduce the coefficient
row $c$ to $(q,0,\ldots,0)$ by a unimodular matrix. The induced invertible
map of $\mathbb T^g$ turns its kernel into
$\{\phi_1:q\phi_1=0\}\times\mathbb T^{g-1}$, namely
$\mathbb Z_q\times\mathbb T^{g-1}$. Its identity component is the image of
the real hyperplane $\sum c_av_a=0$, as also shown constructively above.

In general position the coefficient row is $(1,-1,-1,1)$, with $g=4,q=1$.
For one collision it is $(2,-1,-1)$ up to reordering or overall sign, with
$g=3,q=1$. Both kernels are connected, so zero winding alone reaches their
whole compact group. In double symmetry it is $(2,-2)$, with $g=2,q=2$:

$$
2(\phi_+-\phi_-)=0\pmod{2\pi}.
$$

The two components have $\phi_+-\phi_-=0$ or $\pi$. At any fixed height,
$w_+-w_-=1/2$, so one circle lands in the second component and every integer
winding realizes its parity label.

Concatenation adds the residuals because the coefficients depend only on
$\kappa$, not on the accumulated phase; reversal negates them. All phase
operators are diagonal and commute. This proves the group assertion and its
abelian character. $\square$

### 3.4 Pole collisions and the two endpoint multiplicities

**Corollary 3.4 (Rank and component count in this fiber).** With the endpoint
multiplicities of Theorem 2.13,

$$
\mathcal H_b\cong
\mathbb T^{\,5-\nu_--\nu_+}\times
\mathbb Z_{\gcd(\nu_-,\nu_+)},
$$

where $\mathbb Z_1$ is trivial.

Proof. Here $\nu_-=1+\mathbf1_{E_-}$ and
$\nu_+=1+\mathbf1_{E_+}$. Hence
$g-1=3-\mathbf1_{E_-}-\mathbf1_{E_+}=5-\nu_--\nu_+$.
The grouped coefficients have gcd two exactly in the double-collision case
and gcd one otherwise, which equals $\gcd(\nu_-,\nu_+)$. Theorem 3.3 gives
the formula. The same equalities of masses produce the endpoint cone angles
$2\pi/\nu_-$ and $2\pi/\nu_+$. This correspondence is derived from this
specific four-pole pattern; it is not a universal formula for symplectic
reductions. $\square$

### 3.5 Signed area and the remaining real ambiguity

**Theorem 3.5 (Fixed-area zero-winding fibers).** For a zero-winding loop let

$$
\mathcal A_{\rm s}=\oint\kappa\,d\chi
$$

be its signed coordinate area, and keep the real unwrapped residual $h$.
Then

$$
p_{\kappa_0}^{\mathsf T}h=-\mathcal A_{\rm s}.
$$

For each prescribed real area $A$, the exact set of residuals is
$\{h\in V_b:p_{\kappa_0}^{\mathsf T}h=-A\}$, a nonempty affine space of
dimension $\dim V_b-1$. The dimensions are two, one and zero in the generic,
single-collision and double-collision cases, respectively.

Proof. Along the path,

$$
p_{\kappa_0}=p_\kappa-(\kappa-\kappa_0)d,
\qquad p_{\kappa_0}^{\mathsf T}w(\kappa)=-(\kappa-\kappa_0).
$$

Integration and $\oint d\chi=0$ give the asserted identity. The linear
functional on $V_b$ is nonzero: for any other height $\kappa_1$,

$$
p_{\kappa_0}^{\mathsf T}\bigl(w(\kappa_1)-w(\kappa_0)\bigr)
=-(\kappa_1-\kappa_0)\ne0.
$$

It is consequently onto $\mathbb R$. Each affine level is nonempty and has
codimension one. For any $h$ on it, Theorem 3.2 constructs an exact loop;
the proven identity forces that loop's signed area to be $A$. This proves
sufficiency with the prescribed area as well as necessity. $\square$

Only at double symmetry does the area determine the entire real zero-winding
residual. Passing to phases can identify additional real vectors. In
particular, the real quantity $p_{\kappa_0}^{\mathsf T}h$ is not intrinsically
a function of $h\bmod2\pi$: changing a lift by $2\pi z$ changes it by
$2\pi p_{\kappa_0}^{\mathsf T}z$. Area statements here retain the actual lift.

### 3.6 Equal area with different interference

**Proposition 3.6 (An exact rational pair).** Equal signed area does not
determine a zero-winding endpoint ray at a generic positive base point.

Proof. Take

$$
X=\frac15,\quad Y=\frac25,\quad Z=\frac15,\qquad
\kappa_0=\frac1{20},\quad \kappa_1=\frac1{10},\quad
\kappa_2=\frac3{20}.
$$

The initial law and the three weights, in the fixed mode order, are

$$
p_{\kappa_0}=\frac1{20}(5,3,4,7,1),
$$

$$
\begin{aligned}
w(\kappa_0)&=\frac1{176}(21,-35,0,-15,105),\\
w(\kappa_1)&=\frac1{176}(22,-66,0,-22,66),\\
w(\kappa_2)&=\frac1{176}(15,-105,0,-21,35).
\end{aligned}
$$

These follow by reciprocating the four positive bottom masses and dividing
by their reciprocal sum. Let the first rectangle use height $\kappa_1$ and
phase height two, and the second use $\kappa_2$ and phase height one. Both
signed areas are $1/10$. Their residual difference is

$$
\begin{aligned}
h^{(1)}-h^{(2)}
&=2w(\kappa_1)-w(\kappa_2)-w(\kappa_0)\\
&=\frac1{22}(1,1,0,-1,-1).
\end{aligned}
$$

Its $d$ pairing is zero. Its $p_{\kappa_0}$ pairing is zero because the two
positive entries have total mass $(5+3)/20=2/5$ and the two negative entries
have total mass $(7+1)/20=2/5$. It is not a common phase vector. The overlap
of the two output rays, for the same initial phases, has squared modulus

$$
\left[\frac15+\frac45\cos\left(\frac1{22}\right)\right]^2<1.
$$

Indeed the middle contribution is $1/5$ and the two paired masses give the
two conjugate exponential terms of weight $2/5$. The bracket lies strictly
between zero and one. Equal area therefore fails to determine full
interference even though it determines the weighted real phase in Theorem 3.5. $\square$

### 3.7 Double symmetry: a circle and a parity

**Theorem 3.7 (Exact summary for arbitrary winding).** Assume $X=Y=r/2$ and
put $b_0=(1,1,0,1,1)^{\mathsf T}$. For any admissible winding-$m$ loop define
the real signed integral $A=\int\kappa\,d\chi$. Then

$$
w=\left(\frac12-\frac\kappa r,-\frac\kappa r,0,
                   -\frac\kappa r,\frac12-\frac\kappa r\right),
$$

$$
h=\pi m(e_0+e_{13})-\frac Ar b_0.
$$

Under the three-position embedding of §3.8, let $\widehat b_0$ be the
projector onto the four legal bottom modes and let
$Z_j=e^{-i\pi N_j}$ be the position Pauli operator. This $Z_j$ is distinct
from the probability coordinate $Z=p_2$. On the legal space,

$$
U_{\rm loop}=e^{-it\widehat b_0}(Z_1Z_3)^m,
\qquad t=\pi m-\frac Ar.
$$

The pair $(t\bmod2\pi,m\bmod2)$ is a unique endpoint group summary.

Proof. Substitute the symmetric masses into $w_s=d_s/(p_sI)$ to get the
first expression, then integrate it using $\int d\chi=2\pi m$. On modes
$0,13$ the increment is $t$; on modes $1,3$ it is $t-\pi m$; on mode $2$ it
is zero. The operator displayed gives exactly these negative-phase factors,
since $Z_1Z_3$ is $+1$ on $0,2,13$ and $-1$ on $1,3$.

The phase on mode $0$ determines $t$ modulo $2\pi$, and the ratio of phases
on modes $1$ and $0$ determines $m$ modulo two. The positive middle mass
fixes the otherwise possible common phase, proving uniqueness on rays as
well as in the chosen gauge. Conversely any $t\bmod2\pi$ and parity is
reached by choosing that winding and then a rectangle to set its area, as
Theorem 3.5 or the explicit construction below ensures. $\square$

Area alone does not determine parity, even when the area is fixed exactly as
a real number. To see this constructively, a fixed-$\kappa_0$ winding-one
circle has area $2\pi\kappa_0$. Choose any other interior height $\kappa_a$
and append a zero-winding rectangle with phase height

$$
\alpha=-\frac{2\pi\kappa_0}{\kappa_a-\kappa_0}.
$$

Its area is $-2\pi\kappa_0$, so the concatenation has total area zero and
odd winding. Compare it with the constant loop, or concatenate it to any
loop of area $A$ to obtain another with the same area and opposite winding
parity. All heights are interior and the phase height is finite. The pair
$(A,m)$ determines $h$, but the canonical compact endpoint summary is the
circle variable $t$ and parity. A circle variable is not a finite-bit encoding
of an arbitrary real phase.

### 3.8 The declared three-position tensor product

**Theorem 3.8 (Endpoint local factorization).** Embed the legal five modes in
three binary position factors, ordered low, middle, high, by

$$
|0\rangle=|000\rangle,\quad |1\rangle=|100\rangle,\quad
|2\rangle=|010\rangle,\quad |3\rangle=|001\rangle,\quad
|13\rangle=|101\rangle.
$$

Thus occupation coordinates $(x,y,z)$ are the low, high, middle coordinates,
whereas the tensor factors are ordered low, middle, high. Every loop residual
$h$ of Definition 3.1 induces on this legal subspace a diagonal unitary which
is the restriction of a product of three position unitaries, up to common
phase. Explicitly, set

$$
a=h_1-h_0,\qquad b=h_3-h_0,\qquad c=-h_0.
$$

Then

$$
U(h)=e^{ic}\left[
 e^{-iaN_1}\otimes e^{-icN_2}\otimes e^{-ibN_3}\right]
\quad\text{on the legal space}.
$$

Proof. At modes $0,1,2,3$ one has, respectively,

$$
h_s=ax_s+by_s+cz_s-c.
$$

For mode $13$, the right side is $h_1+h_3-h_0$. The difference from $h_{13}$
is $-2\pi m$, by $d^{\mathsf T}h=2\pi m$, so the same formula holds modulo
$2\pi$. The displayed product has coefficient
$e^{ic}e^{-i(ax_s+cz_s+by_s)}=e^{-ih_s}$ on each legal basis vector. This
proves the equality of operators there, with the signs fixed by the negative
phase convention. $\square$

For any fixed bipartition formed from these three position factors, this
product is a unitary on one side times a unitary on the other. The coefficient
matrix of a pure state is transformed by left and right unitaries, so its
singular values, and hence its Schmidt spectrum, are unchanged. This conclusion
compares the initial and final states at the same probability law; it makes no
claim for an unrelated tensor factorization. Intervening probability control
can change entanglement. For example, the reduced density matrix of the middle
factor, for real positive initial phases at a given probability, is

$$
\rho_2=
\begin{pmatrix}
r&\sqrt{Zp_0}\\
\sqrt{Zp_0}&Z
\end{pmatrix}.
$$

Only modes $000$ and $010$ have the same outer bit pair and contribute to its
off-diagonal entry. Its determinant is $Z(r-p_0)$, which varies with $\kappa$
at fixed means. A pure probability leg with fixed zero phases therefore can
change its Schmidt spectrum. The endpoint theorem does not say otherwise.
Local phase unitaries can also change fixed-reference interference readings;
those readings need not be invariant under the reduced symmetry task.

### 3.9 What vanishes when middle support vanishes

**Proposition 3.9 (A continuous contrast and its support boundary).** At a
positive base point write

$$
|\psi\rangle=\sqrt r\,|B\rangle+\sqrt Z\,|2\rangle,
\qquad \langle B|B\rangle=1,
\qquad \langle2|B\rangle=0,
$$

with the middle phase fixed to zero. The one-parameter subgroup generated by
$b_0$ acts by

$$
|\psi_t\rangle=e^{-it}\sqrt r\,|B\rangle+\sqrt Z\,|2\rangle,
$$

and its squared overlap is

$$
|\langle\psi|\psi_t\rangle|^2
=|re^{-it}+Z|^2
=1-4rZ\sin^2(t/2).
$$

Proof. The vector $b_0$ belongs to $V_b$ in every symmetry case, so these
phases are reachable by Theorem 3.2. Its four bottom entries are one and its
middle entry is zero, giving the state expression. Orthogonality of the two
summands gives the overlap formula and $r+Z=1$ gives its last form. $\square$

As $Z\to0$, this particular continuous bottom-versus-middle contrast becomes
a common phase on the remaining support. In general position it is only a
one-parameter subgroup of the three-dimensional identity component. Even at
double symmetry the parity factor $Z_1Z_3$ can remain observable on bottom
support: if all four bottom amplitudes are nonzero, it gives opposite signs
to modes $0,13$ and modes $1,3$, which cannot be a common phase. Thus loss of
middle support does not assert disappearance of every holonomy component.
The full-support gauge and group proofs use $p_2>0$ and cannot be extended
mechanically to $Z=0$ without taking the new projective equivalence into account.

### 3.10 A determinant for synthesis and its conditioning

**Theorem 3.10 (Four-height determinant).** Assume neither $E_-$ nor $E_+$,
and choose
$\kappa_0<\kappa_1<\kappa_2<\kappa_3$ in the positive fiber. Let $C$ be the
$3\times3$ matrix whose $j$th column is
$(w(\kappa_j)-w(\kappa_0))_{0,1,3}$, $j=1,2,3$. Define

$$
Q_b(\kappa)=XY(r-X-Y)+2XY\kappa-r\kappa^2
=I(\kappa)\prod_{s\in B}p_s(\kappa)>0.
$$

Then

$$
|\det C|=
\frac{XY(r-X)(r-Y)|X-Y|\,|X+Y-r|
 \displaystyle\prod_{0\le i<j\le3}(\kappa_j-\kappa_i)}
 {\displaystyle\prod_{j=0}^3Q_b(\kappa_j)}.
$$

For each $h\in V_b$, the unique rectangle coefficients at these heights are
$a=C^{-1}(h_0,h_1,h_3)^{\mathsf T}$; the remaining entries are recovered by
$h_2=0$ and $h_{13}=h_1+h_3-h_0$.

Proof. Write $A=p_0$, $B_1=p_1$, $C_1=p_3$, $D_1=p_{13}$ temporarily.
Multiplying $I$ by their product groups the four triple products as

$$
B_1C_1(A+D_1)+AD_1(B_1+C_1).
$$

Set $s=X+Y$. This is

$$
(XY-s\kappa+\kappa^2)(r-s+2\kappa)
+\kappa(r-s+\kappa)(s-2\kappa)
=XY(r-s)+2XY\kappa-r\kappa^2,
$$

establishing the formula for $Q_b$ and its positivity without a sign
assumption on $r-X-Y$.

Let $B_4$ be the four-by-four matrix whose columns are the bottom components
of $w(\kappa_j)$ in order $(0,1,3,13)$. Replace its last row by the signed
sum of its rows with coefficients $(1,-1,-1,1)$. This row operation has
determinant one, because the old last row has coefficient one, and its new
entries are all one. Subtract column zero from each of the other columns.
The last row is then $(1,0,0,0)$; expansion along it shows
$|\det B_4|=|\det C|$, with no multiplicative factor.

The Cauchy determinant, in the form of Krattenthaler's equation (2.7), applied
with row variables $-\lambda_s$ and column variables $\kappa_j$, gives

$$
|\det B_4|=
\frac{\displaystyle\prod_{s<t}|\lambda_s-\lambda_t|
      \displaystyle\prod_{i<j}(\kappa_j-\kappa_i)}
 {\displaystyle\prod_j I(\kappa_j)
      \displaystyle\prod_{s,j}|\kappa_j-\lambda_s|}.
$$

Here all poles are distinct and all denominators are nonzero, exactly the
hypotheses needed for that classical identity. The denominator groups as
$\prod_j Q_b(\kappa_j)$, since
$\prod_s|\kappa_j-\lambda_s|=\prod_s p_s(\kappa_j)$. Its pole product is

$$
\prod_{s<t}|\lambda_s-\lambda_t|
=XY(r-X)(r-Y)|X-Y|\,|X+Y-r|.
$$

Substitution proves the determinant formula. It is nonzero in the stated
domain, so solving the first three coordinates gives unique coefficients.
Every difference column and every target in $V_b$ has its last coordinate
determined by the same relation, proving exact recovery of the whole vector.
$\square$

There is a precise singular-limit consequence. Consider a family of these
matrices for which every sampled bottom probability is at least one fixed
$\varepsilon>0$. Their entries are bounded, and their denominators $Q_b$ are
bounded away from zero. If a symmetry gap $X-Y$ or $X+Y-r$ tends to zero, or
two chosen heights coalesce, the determinant formula tends to zero. Thus the
least singular value tends to zero: if it had a positive lower bound, the
product of the three singular values could not tend to zero. Every convergent
matrix subsequence has a singular limit. This is a loss of conditioning of
the chosen exact synthesis coordinates. Without a uniform positive margin,
$Q_b$ can also approach zero; the formula does not imply determinant decay for
all families approaching a probability endpoint.

### 3.11 A variation lower bound near symmetry

**Theorem 3.11 (Cost in phase variation).** Let a loop of Definition 3.1 have
all four bottom masses at least $\varepsilon>0$ throughout the path, and put
$V_\chi=\int_0^T|\dot\chi|\,dt$. Its real residual obeys

$$
|h_1-h_3|\le\frac{|X-Y|r}{16\varepsilon^2}V_\chi,
\qquad
|h_0-h_{13}|\le\frac{|X+Y-r|r}{16\varepsilon^2}V_\chi.
$$

For a fixed nonzero corresponding real target difference and nonzero gap,
these give inverse-gap lower bounds on the necessary phase variation.

Proof. Pointwise reciprocal subtraction yields

$$
w_1-w_3=\frac{X-Y}{Ip_1p_3},\qquad
w_0-w_{13}=\frac{X+Y-r}{Ip_0p_{13}}.
$$

Cauchy–Schwarz applied to the four positive bottom masses of total $r$ gives

$$
I r=\left(\sum_{s\in B}\frac1{p_s}\right)
     \left(\sum_{s\in B}p_s\right)\ge16.
$$

Each denominator product is at least $\varepsilon^2$. Integrate the
pointwise bounds against $|d\chi|$ and apply the triangle inequality. For
example, if $\Delta=h_1-h_3\ne0$ and $X\ne Y$, then

$$
V_\chi\ge\frac{16\varepsilon^2|\Delta|}{r|X-Y|}.
$$

The second bound is identical with its stated pair and gap. On the exact wall
the difference is forced to zero, in agreement with Theorem 3.2. $\square$

For a phase-class target $\phi_1-\phi_3$, one must use an actual chosen lift
or the invariant distance
$\operatorname{dist}(\phi_1-\phi_3,2\pi\mathbb Z)$ in a lower bound: every
real realization has magnitude at least that distance. An arbitrary wrapped
coordinate is not a lower bound on all realizations. The fixed positive
$\varepsilon$ is essential to the estimate, and phase variation here carries
no calibrated energy or elapsed-time claim.

### 3.12 Ideal coherence statistics and history equivalence

**Theorem 3.12 (Exact task quotient for endpoint histories).** Fix the same
positive base probability $p_{\kappa_0}$ and the same initial pure-state
phases for every history. Allow ideal real and imaginary coherence
expectations on the five edges

$$
0\!-\!1,\quad 0\!-\!2,\quad 0\!-\!3,\quad
1\!-\!13,\quad 3\!-\!13.
$$

Two admissible loop histories have all these endpoint statistics equal if and
only if their residuals represent the same element of $\mathcal H_b$.
Thus the exact endpoint history summary for this read menu is three circles,
two circles, or a circle and parity in the respective symmetry regimes.

Proof. On an oriented edge $i\!-\!j$ the two Hermitian observables

$$
A_{ij}=|i\rangle\langle j|+|j\rangle\langle i|,
\qquad
B_{ij}=-i|i\rangle\langle j|+i|j\rangle\langle i|
$$

have expectations $2\operatorname{Re}(\overline\psi_i\psi_j)$ and
$2\operatorname{Im}(\overline\psi_i\psi_j)$, respectively. Since
$|\overline\psi_i\psi_j|=\sqrt{p_ip_j}>0$, these determine the edge phase
difference modulo $2\pi$. If two outputs have the same readings, let
$\delta_s$ be their phase difference in $\mathbb T$. Every measured edge
then gives $\delta_i=\delta_j$. The graph is connected: modes $1,2,3$ join
$0$ directly and mode $13$ joins through $1$ or $3$. Therefore all
$\delta_s$ are one common phase. In the middle-fixed gauge, both histories
have the same unchanged middle phase, so $\delta_2=0$ and every $\delta_s=0$.
Their residual classes are equal.

Conversely, equal residual classes give identical complex amplitudes in this
gauge from the common initial state, hence all the listed readings are equal.
Theorem 3.3 identifies exactly which classes occur, and its constructive
sufficiency ensures that each claimed history-summary value is realized.
$\square$

The proof would use any spanning tree of this graph, with four edges; the
specified five-edge menu is valid without asserting a minimal physical
instrument. Equality here concerns ideal probability laws or exact
expectations. Distinct such laws need not be perfectly distinguishable from
finitely many shots, and no perfect finite-shot discrimination is claimed.

At the same base point, probabilities-only readings identify all loop
histories, since every endpoint has that probability. Schmidt-spectrum-only
readings for fixed partitions of the three declared position factors also
identify all of them by Theorem 3.8. The full coherence menu instead recovers
the compact group element, but not the path: a rectangle followed by its
reverse is a nonconstant history with the same residual as the constant
history. This summary is neither path reconstruction nor an online resource
bound or a replacement for an unbounded counter in a different task.

### 3.13 Classical control and algebraic sources

The direct construction in Theorems 3.2–3.3 is the authority for this model's
reachability. Classical geometric control offers language for a base path,
a connection and a fiber displacement, with its own system-specific
hypotheses. In particular, Tomoki Ohsawa's
[*Geometric Kinematic Control of a Spherical Rolling Robot*, arXiv:1808.10106v2](https://arxiv.org/abs/1808.10106v2),
§§3.1–3.2, writes a robot configuration as
$S^1\times S^1\times SO(3)\times\mathbb R^2$, with wheel angles as the base
and a principal group action on the fiber. That model and its connection are
not the five-mode probability fiber here. Its introduction and geometric-phase
sections supply context for holonomy under prescribed controls, not a
controllability certificate for this model.

The determinant identity in Theorem 3.10 is the standard Cauchy double
alternant, explicitly equation (2.7), p. 6, in Christian Krattenthaler's
[*Advanced Determinant Calculus*, arXiv:math/9902004v3](https://arxiv.org/abs/math/9902004v3).
The substitution $X_s=-\lambda_s$, $Y_j=\kappa_j$ and the nonzero-denominator
condition are the complete match needed here. The elementary rational-function
argument in Theorem 3.2 also shows nonsingularity without requiring the
numerical value of that determinant.

Integer characters of tori, Bézout reduction and diagonal symmetry are
classical algebraic tools. Theorem 3.3 gives the integer-representative
construction explicitly, so connectedness or reachability is not inferred
from a name, a numerical rank or a density observation. Classical tools are
literature-attested; their displayed application to this probability source
is repo-derived ordinary mathematics. No claim of priority is attached to
this distinction.

### 3.14 Scope of the constructive conclusions

The rational pair in Proposition 3.6 exhibits two exact endpoints in one
fixed-area affine fiber of Theorem 3.5. The uniform one-circle state in §2.7
exhibits failure of ray return, whereas the variable-reference rectangle in
Proposition 2.7 exhibits a relative phase after a zero-winding loop. The
odd-winding, zero-area construction in §3.7 isolates a different obstruction:
a discrete component can change while the real area stays fixed.

These instances illustrate distinct statements with distinct hypotheses.
The complete real reachability assertion is supplied by the pole argument and
finite rectangle synthesis of Theorem 3.2. The all-sector integer-lift proof
of Theorem 3.3 supplies every candidate phase class. The determinant of
Theorem 3.10 gives unique synthesis coordinates in general position, with
the stated positive-margin condition on singular limits. Neither an example
nor a rank at one parameter replaces these quantified arguments.

The endpoint product identity holds on every legal basis vector of the
specified tensor product. Theorem 3.12 proves both directions of history
equivalence for every full-support initial state under its declared coherence
menu. It identifies a group element rather than a path, and the broader
variational competitor in Theorem 2.9 is not an execution of the restricted
control law. These domains are part of the conclusions.

### 3.15 Continuous rank, discrete components and the read menu

The pole collisions reduce the dimension of the real zero-winding space.
Separately, their integer multiplicities can make the compact phase kernel
disconnected. For the present source, only the double collision produces a
nontrivial component group, and winding parity detects it. Those same two
collisions govern which fiber endpoint has cone angle $\pi$. This is an exact
relationship between specific probability, pole and lattice data, with
continuous rank and discrete components kept distinct.

Every loop's endpoint phase operation is local under the declared
three-position tensor product. It can therefore preserve all endpoint
Schmidt spectra while changing fixed-reference coherence statistics. The
history equivalence is determined by the read menu: the quotient-symmetry
task forgets these local phases, whereas the connected coherence graph
recovers their exact compact group element. Exact controllability follows
from finite paths with unrestricted real phase heights, not from an
assertion about the available operations of an arithmetic representation.

The model permits continuous probability control and added phase-sensitive
observables. Bounds on speed, variation, preparation or measurement accuracy
would be additional hypotheses for a different resource-constrained problem.
The present proofs preserve their full-support domains, real-lift conditions
and endpoint comparisons under the operations that have actually been defined.

## 追加锚（本行以下为增补区）

## 4. Exact affine capacity of the fixed-base coherence menu

Fix one full-support base point $b_{\mathrm{vis}}=(X,Y,Z)$, one
$\kappa _0$ in the interior of its fiber, and the probability vector
$p=p_{\kappa _0}$ in the mode order $(0,1,2,3,13)$. Prepare this same
probability vector and the same initial phases before every history. The
controls are exactly the admissible base/phase loops of Definition 3.1,
including every integer winding. A readout is the ideal expectation, with no
finite-sample or measurement-resource assertion.

For an oriented edge $e=(i,j)$ in the menu of Theorem 3.12, put
$a_e=2\sqrt{p_ip_j}$ and let $\delta_e^0$ be its fixed initial phase
difference. The two readouts are

$$
y_e(h)=a_e\bigl(\cos(\delta_e^0+h_i-h_j),
                 \sin(\delta_e^0+h_i-h_j)\bigr).
\tag{4.1}
$$

The factor $2$ is part of the source convention: (4.1) is twice the real
and imaginary parts of $\overline\psi_i\psi_j$, hence it is exactly the pair
of ideal expectations in Theorem 3.12. In particular, the subsequent Gram
coefficients use the doubled expectations and not the unscaled complex
product.

**Definition 4.1 (Task-relative affine capacity).** Let $\mathcal D_b$ be
the set of all endpoint residual classes produced from this preparation by
the legal loops, and let $y:\mathcal D_b\to\mathbb R^{10}$ concatenate the
five pairs in (4.1). Define $\operatorname{cap}_{\mathrm{aff}}(b)$ to be the
least $k$ for which there are an arbitrary encoder
$z:\mathcal D_b\to\mathbb R^k$, a fixed vector $c\in\mathbb R^{10}$ and a
fixed linear decoder $D:\mathbb R^k\to\mathbb R^{10}$ with

$$
y(h)=c+D z(h)\qquad(h\in\mathcal D_b).
\tag{4.2}
$$

The encoder may be nonlinear. The decoder and its affine offset may not
depend on the history, the current phase, or the future loop.

The relation constraint in Definition 3.1 gives, for every residual lift,

$$
h_2=0,\qquad h_0-h_1-h_3+h_{13}=2\pi m.
$$

Consequently define the three edge characters

$$
\alpha=h_0-h_1,\qquad \beta=h_0,\qquad \gamma=h_0-h_3\pmod {2\pi}.
\tag{4.3}
$$

The remaining edge differences are

$$
h_1-h_{13}=\gamma,\qquad h_3-h_{13}=\alpha.
\tag{4.4}
$$

Thus the five-edge menu has only the three character pairs

$$
\{0\!-\!1,3\!-\!13\}\rightsquigarrow\alpha,\qquad
\{0\!-\!2\}\rightsquigarrow\beta,\qquad
\{0\!-\!3,1\!-\!13\}\rightsquigarrow\gamma.
\tag{4.5}
$$

### 4.1 Response factorization and the fixed-loop operation contract

For a circle character $\xi$, write

$$
q_\xi=(\sqrt2\cos\xi,\sqrt2\sin\xi)^{\mathsf T}.
\tag{4.6}
$$

For every edge carrying $\xi$, its two coordinates are a fixed orthogonal
rotation of $q_\xi$, multiplied by $a_e/\sqrt2$. If an edge carries
$-\xi$, use the fixed reflection
$J=\operatorname{diag}(1,-1)$ before that rotation. More explicitly, if
$h_i-h_j=s_e\xi$ with $s_e\in\{+1,-1\}$, the corresponding two-by-two
block of $D_b$ is
$B_{e,\xi}=(a_e/\sqrt2)R_{\delta_e^0}J^{(1-s_e)/2}$, and all other
blocks in that edge row are zero. At both walls the bottom edge block is the
fixed column $a_e(\cos\delta_e^0,\sin\delta_e^0)^{\mathsf T}$ multiplying
$\varepsilon$. Thus, in each symmetry regime, the ten outputs factor as

$$
y(h)=c_b+D_bq_b(h),
\tag{4.7}
$$

where all entries of $D_b$ are fixed by $p$ and the initial phases. In
generic position

$$
q_b=(q_\alpha,q_\beta,q_\gamma)\in\mathbb R^6,
$$

on a single wall $q_b=(q_\xi,q_\beta)\in\mathbb R^4$, where $\xi=\alpha$
and $\gamma=\pm\alpha$, and at both walls

$$
q_b=(q_\beta,\varepsilon)\in\mathbb R^3,
\qquad \varepsilon=(-1)^m.
\tag{4.8}
$$

At both walls the four bottom-edge pairs are fixed vectors times
$\varepsilon$, while the middle pair is the $q_\beta$ block; this is the
meaning of the affine offset and decoder in (4.7).

A prescribed later loop $\ell$ has residual increment $u$ and winding
$m_u$. Concatenation adds residuals, so the same finite coordinates update
by

$$
q_b(h+u)=T_b(u)q_b(h),
\tag{4.9}
$$

where

$$
\begin{aligned}
T_{\mathrm{gen}}(u)&=R_{u_\alpha}\oplus R_{u_\beta}\oplus R_{u_\gamma},\\
T_{\mathrm{wall}}(u)&=R_{u_\xi}\oplus R_{u_\beta},\\
T_{\mathrm{dbl}}(u)&=R_{u_\beta}\oplus[(-1)^{m_u}].
\end{aligned}
\tag{4.10}
$$

Here $R_t$ is the planar rotation through $t$, and the last scalar block
multiplies the parity coordinate. The decoder known for the current task is
$D_b$; the decoder for the prescribed future task is the explicitly updated
$D_b[u]=D_bT_b(u)$. It is not required that one unchanged decoder serve
all future outputs. For two prescribed loops $u,v$,

$$
T_b(v+u)=T_b(v)T_b(u),\qquad
D_b[u][v]=D_bT_b(u)T_b(v)=D_bT_b(u+v),
\tag{4.11}
$$

so the fixed-coordinate operation contract is closed under composition. The
same statement applies to the fixed offset $c_b$; it is unchanged because
all updates act on centered character coordinates.

**Theorem 4.2 (Sharp affine capacity and the two symmetry walls).** Under
the fixed-base, fixed-preparation and ideal-readout contract above,

$$
\operatorname{cap}_{\mathrm{aff}}(b)=
\begin{cases}
6,&X+Y\ne 1-Z\ \text{and }X\ne Y,\\
4,&\text{exactly one of }X+Y=1-Z,\ X=Y\ \text{holds},\\
3,&X+Y=1-Z\ \text{and }X=Y.
\end{cases}
\tag{4.12}
$$

In particular, the generic value is six, but it counts three character
circles with two real quadratures each; it is not a spatial dimension.

**Proof.** Theorem 3.3 and (4.3) identify the reachable character domains. In
general position $\mathcal H_b\simeq\mathbb T^3$, and the six coordinates
of $q_b$ have affine hull $\mathbb R^6$. Every edge block in (4.7) is
nonzero and invertible on its character pair because $a_e>0$. Each of the
three characters occurs on at least one edge, so $\operatorname{rank}D_b=6$.
The repeated alpha and gamma edge blocks do give four output-coordinate
relations: two for the pair $0\!-\!1,3\!-\!13$, and two for the pair
$0\!-\!3,1\!-\!13$. Equivalently, $\dim\ker D_b^{\mathsf T}=10-6=4$.
They are allowed in the rank argument; no independence of the ten output
coordinates is asserted. Therefore the affine hull of the outputs has
dimension six.

If $X+Y=1-Z$, then $h_0=h_{13}$ and (4.3) gives $\gamma=-\alpha$; if
$X=Y$, then $h_1=h_3$ and $\gamma=\alpha$. On either single wall,
$q_b=(q_\xi,q_\beta)$ has affine hull $\mathbb R^4$, and every surviving
character has a nonzero edge block, with a possible fixed reflection for the
minus sign. Thus $\operatorname{rank}D_b=4$, including the expected
six-dimensional coordinate kernel.

At both walls, $2\alpha=2\pi m$, so the bottom character is the parity
$\varepsilon=(-1)^m$, while $\beta$ remains a circle coordinate. The
middle block is invertible and the bottom parity vector is nonzero, hence
$\operatorname{rank}D_b=3$. The balanced domain
$\mathbb T\times\mathbb Z_2$ has affine hull $\mathbb R^3$ in the
coordinates $(q_\beta,\varepsilon)$. This proves the three lower bounds
because an affine image of $\mathbb R^k$ has affine-hull dimension at most
$k$, while (4.7) gives matching upper bounds. $\square$

The identity components in Theorem 3.3 have real dimensions three, two and
one in the generic, single-wall and double-wall regimes. Those group
dimensions are not affine capacities. A phase coordinate can be a nonlinear
angle, while the requested coherence expectations require its sine and cosine
quadratures. The all-winding double-wall task therefore has two quadratures
for the circle and one additional scalar for parity.

### 4.2 The zero-winding double-wall source

Restrict the double-wall source to loops with $m=0$. Then $\varepsilon=1$
for every reachable endpoint, so the four bottom-edge pairs are fixed constants
and the only varying character is $\beta$. After absorbing those constants
into $c_b^0$, the same ten-coordinate readout factors as

$$
y(h)=c_b^0+D_b^0q_b^0(h),\qquad
q_b^0=(\sqrt2\cos\beta,\sqrt2\sin\beta).
\tag{4.13}
$$

**Proposition 4.3 (Zero-winding double-wall capacity).** For this restricted
source, $\operatorname{cap}_{\mathrm{aff}}^0(b)=2$.

**Proof.** The middle edge has $a_{0,2}>0$, so its two coordinates give an
invertible two-dimensional block of $D_b^0$. The bottom coordinates are
constant on the zero-winding domain. Thus $\operatorname{rank}D_b^0=2$,
which is both the affine-hull lower bound and the dimension of (4.13). For a
prescribed zero-winding future loop $u$, $m_u=0$ and

$$
q_b^0(h+u)=R_{u_\beta}q_b^0(h),\qquad
D_b^0[u]=D_b^0R_{u_\beta}.
\tag{4.14}
$$

The rotations compose, so this restricted decoder is closed under
zero-winding controls. For every integer winding, odd winding flips parity
and even winding preserves it. Odd winding leaves the $\varepsilon=1$
endpoint component, while even winding preserves that component. The
restriction $m=0$ is imposed on histories and controls: a nonzero even
winding is outside this chosen class, although its endpoint can lie in the
zero-winding reachable image. No closure claim for nonzero-winding controls
is made here. $\square$

## 5. The fixed-base response Gram and the triplet obstruction

The metric statement below fixes the endpoint averaging law. Give the
reachable compact group its normalized Haar measure, and in the double-wall
case give the two parity components equal mass. This is an averaging
convention for the ideal endpoint task; it is not a claim that a laboratory
preparation samples loops with this law.

For each surviving circle character $\xi$, use the normalized quadratures

$$
q_\xi=(\sqrt2\cos\xi,\sqrt2\sin\xi),
\tag{5.1}
$$

so that $\mathbb E[q_\xi q_\xi^{\mathsf T}]=I_2$, and use
$\mathbb E[\varepsilon^2]=1$ with $\mathbb E[\varepsilon]=0$ for balanced
parity. No whitening of the ten outputs is performed. These are normalized
latent coordinates for the stated Haar convention; the output covariance
remains coordinate-dependent through the decoder.

For a fixed initial phase $\delta$, an edge pair is

$$
a_e(\cos(\delta+\xi),\sin(\delta+\xi))
 =\frac{a_e}{\sqrt2}R_\delta q_\xi.
\tag{5.2}
$$

Let $D_b$ and $c_b$ be the response factorization in (4.7), and define

$$
\bar y=\mathbb E[y],\qquad
C_{\mathrm{out}}=\mathbb E[(y-\bar y)(y-\bar y)^{\mathsf T}].
\tag{5.3}
$$

Then

$$
C_{\mathrm{out}}=D_bD_b^{\mathsf T}\quad\text{and}\quad
G_{\mathrm{lat}}=D_b^{\mathsf T}D_b.
\tag{5.4}
$$

The first is the actual $10\times10$ output covariance. Its repeated-edge
cross blocks are generally nonzero, and in generic position its nullity is
four. The second is the latent decoder pullback Gram. The two matrices have
exactly the same nonzero eigenvalues, including multiplicities, but they are
not the same object.

**Theorem 5.1 (Exact response Gram blocks for the actual menu).** In generic
position, the latent pullback Gram in (5.4) is

$$
G_{\mathrm{lat}}
 =\operatorname{diag}(\lambda_\alpha I_2,\lambda_\beta I_2,
                       \lambda_\gamma I_2),
\tag{5.5}
$$

where

$$
\lambda_\alpha=2(p_0p_1+p_3p_{13}),\qquad
\lambda_\beta=2p_0p_2,\qquad
\lambda_\gamma=2(p_0p_3+p_1p_{13}).
\tag{5.6}
$$

For one symmetry wall the two blocks are

$$
\lambda_{\mathrm{bottom}}
 =2(p_0+p_{13})(p_1+p_3),\qquad
\lambda_{\mathrm{middle}}=2p_0p_2.
\tag{5.7}
$$

At both walls the circle block is $2p_0p_2$ and the parity coordinate has
scalar Gram coefficient

$$
\lambda_{\mathrm{parity}}
 =4(p_0p_1+p_0p_3+p_1p_{13}+p_3p_{13}).
\tag{5.8}
$$

The corresponding output covariance is always $C_{\mathrm{out}}=D_bD_b^{\mathsf T}$;
its nonzero spectrum is the spectrum listed above, and its zero multiplicity
is $10-6$, $10-4$, or $10-3$ in the three regimes. Under the
zero-winding double-wall restriction, the bottom contribution is constant and
is removed by centering, so the output covariance has rank two.

**Proof.** Each edge block in (5.2) contributes
$(a_e^2/2)I_2=2p_ip_jI_2$ to $D_b^{\mathsf T}D_b$. Distinct character
blocks are orthogonal under normalized Haar, the standard character-orthogonality
step in the Peter--Weyl theorem (Peter and Weyl, *Mathematische Annalen* 97
(1927), 737--755, [doi:10.1007/BF01447892](https://doi.org/10.1007/BF01447892)),
while repeated edges belonging to one character add in the same latent block.
Equation (4.5) gives (5.6).
On a single wall, the possible sign relation is implemented by the fixed
reflection $J$, so all four bottom edges add to one block and give (5.7).
At both walls the bottom response is a fixed vector times $\varepsilon$, and
summing the four squared norms gives (5.8). Centering removes the constant
$c_b$. Balanced parity has mean zero and variance one, so its random
contribution remains in the centered response. Only in the restricted $m=0$
task is parity deterministic, making its bottom contribution constant and
removable by centering. The equality of the nonzero spectra of $D_bD_b^{\mathsf T}$
and $D_b^{\mathsf T}D_b$ is the singular-value identity. No whitening or
coordinate-independent metric is asserted. $\square$

**Corollary 5.2 (An explicit anisotropic source witness).** The positive source

$$
p=(p_0,p_1,p_2,p_3,p_{13})=(1,2,3,4,5)/15
\tag{5.9}
$$

is in the original fiber domain: it has

$$
(X,Y,Z)=(7/15,9/15,3/15),\qquad
\kappa=5/15,
\qquad \kappa_-=4/15<5/15<7/15=\kappa_+,
\tag{5.10}
$$

and lies on neither symmetry wall. Its latent Gram eigenvalues are

$$
(\lambda_\alpha,\lambda_\beta,\lambda_\gamma)
   =(44/225,\ 6/225,\ 28/225),
\tag{5.11}
$$

all distinct. Therefore the nonzero spectrum of the actual ten-output
covariance has multiplicities $2,2,2$, together with four zeros. A
six-dimensional triplet response would have latent Gram of the form
$A\otimes I_3$, whose nonzero eigenvalue multiplicities are multiples of
three. The source witness cannot be orthogonally equivalent to such a triplet
Gram, nor can padding by the four output null directions change its nonzero
multiplicities. This is a source-realized obstruction to inferring triplet
isotropy from the coherence menu. It supplies neither a physical spatial
metric nor a native $SO(3)$ action.

**Proof.** The domain inequalities and endpoint bounds are the displayed
computations. Applying (5.6) gives

$$
2(2+20)/225=44/225,\qquad 2(3)/225=6/225,\qquad
2(4+10)/225=28/225.
$$

The singular-value identity transfers these values from $G_{\mathrm{lat}}$ to
$C_{\mathrm{out}}$, and orthogonal changes preserve multiplicities. $\square$

The affine predictive terminology is compatible with the source-specific
notion of a state represented by fixed linear readouts of future tests in
Littman, Sutton and Singh, [*Predictive Representations of State*](https://proceedings.neurips.cc/paper/2001/hash/1e4d36177d71bbb3558e43af9577d70e-Abstract.html), NIPS 14
(2001), pp. 1555--1561. The present theorem is narrower: its tests are the five
specified coherence edges, its source is the fixed five-mode FIB fiber, its
controls are Definition 3.1 loops, and its decoder is affine with fixed
coefficients. No predictive-state result is used to infer a dimension here.

This result leaves the physical bridge explicit. The coherence task has an
exact affine capacity and an exact response spectrum under its stated endpoint
law. A physical three-dimensional interpretation would still require a
separate common rotation action, metric identification, and lawful control
realization such as the additional interface hypotheses of Section 9 of
[FIB harmonic-edge load](FIB_LEGAL_EDGE_LOAD_SECOND_ORDER_LOSS_LOCALIZATION_AND_LOCAL_TILT_AVERAGING_OBSTRUCTION.md).
Neither a torus, a character count, a response rank, nor the Gram calculation
supplies those hypotheses.

## 5.99 追加锚

## 6. Full-support triplet locus and the native-operation boundary

This appendix keeps the source, operation and metric contract of §§3–5
unchanged. Thus $p=(p_0,p_1,p_2,p_3,p_{13})$ is positive with total mass one,
the controls are exactly the full Definition 3.1 loops with every integer
winding, the five readouts are the doubled coherence pairs of (4.1), and the
endpoint average is normalized Haar with equal mass on the two components at
the double wall. The Gram matrices below are the source pullback Gram or the
actual ten-output covariance from (5.4); no whitening is introduced.

### 6.1 The complete positive-spectrum classification

Write

$$
\lambda_\alpha=2(p_0p_1+p_3p_{13}),\qquad
\lambda_\beta=2p_0p_2,\qquad
\lambda_\gamma=2(p_0p_3+p_1p_{13}).
\tag{6.1}
$$

In generic position, Theorem 5.1 gives the active Gram
$\operatorname{diag}(\lambda_\alpha I_2,\lambda_\beta I_2,
\lambda_\gamma I_2)$. On one wall it gives two positive $2\times2$ blocks,
and at both walls it gives a circle block with coefficient
$\lambda_{\mathrm{circ}}=2p_0p_2$ and a parity coefficient

$$
\lambda_{\mathrm{par}}=4(p_0p_1+p_0p_3+p_1p_{13}+p_3p_{13}).
\tag{6.2}
$$

**Theorem 6.1 (Triplet multiplicity locus).** For every positive source in
the stated fiber, all positive eigenvalue multiplicities of the active Gram
are divisible by three if and only if

$$
p=(a,b,8b,b,a),\qquad a,b>0,\qquad 2a+10b=1.
\tag{6.3}
$$

On this locus the source is on both symmetry walls and

$$
G_{\mathrm{lat}}=16ab\,I_3=[16ab]\otimes I_3.
\tag{6.4}
$$

Thus the active Gram is orthogonally equivalent to $A\otimes I_3$ with the
one-dimensional positive multiplicity matrix $A=[16ab]$. If one embeds this
active three-dimensional support into six coordinates, the padded expression
$\operatorname{diag}(16ab,0)\otimes I_3$ is only a statement about
multiplicities; it is not a six-dimensional source claim.

**Proof.** In generic position all three coefficients in (6.1) are positive,
and each has multiplicity two. If two coefficients coincide, the positive
multiplicities are $4$ and $2$; if all three coincide, the only positive
multiplicity is $6$. The latter alternative cannot occur in generic position,
because

$$
\lambda_\alpha-\lambda_\gamma
 =2(p_0-p_{13})(p_1-p_3).
\tag{6.5}
$$

Equality would impose $p_0=p_{13}$ or $p_1=p_3$, which are respectively the
walls $X+Y=1-Z$ and $X=Y$. Hence no generic source has the required positive
multiplicities.

On exactly one wall the active support has dimension four and consists of two
positive blocks, each of multiplicity two. The only possible multiplicity
patterns are therefore $(2,2)$ or $(4)$, neither of which is divisible by
three. This conclusion uses the wall formula of Theorem 5.1 and does not
continue a generic Haar formula through the wall.

At both walls, $p_0=p_{13}$ and $p_1=p_3$. Put these common values equal to
$a$ and $b$. The positive multiplicities are $2$ for the circle coefficient
and $1$ for the parity coefficient, so divisibility by three is equivalent to
their equality. Equations (6.2) give

$$
2a p_2=16ab.
\tag{6.6}
$$

Since $a>0$, this is $p_2=8b$. Total mass one then gives
$2a+10b=1$. Conversely, every positive pair satisfying (6.3) has both wall
equalities, and (6.2) becomes $\lambda_{\mathrm{circ}}=
\lambda_{\mathrm{par}}=16ab$, proving (6.4). The existing output covariance
has the same positive spectrum by (5.4); its null directions do not alter any
positive multiplicity. $\square$

Adding the four, six or seven output null directions in the generic, single-
wall or double-wall regimes changes only the multiplicity of the zero
eigenvalue. It cannot repair a positive pattern $(2,2,2)$, $(4,2)$ or $(2,1)$.
The classification is consequently a positive-spectrum statement and makes
no claim about a physical spatial dimension. The compact-group identity
dimensions $(3,2,1)$ and affine capacities $(6,4,3)$ proved in §§3–4 are
different invariants from these eigenvalue multiplicities.

### 6.2 A sharp generic six-dimensional separation

The following comparison is restricted to generic position, where the active
support is six-dimensional. Let $G$ denote the Gram in (5.5), let
$x\le y\le z$ be the sorted values among
$\lambda_\alpha,\lambda_\beta,\lambda_\gamma$, and define

$$
\mathcal T_6=\{Q(A\otimes I_3)Q^{\mathsf T}:Q\in O(6),\;
 A=A^{\mathsf T}\succeq0\text{ is }2\times2\}.
\tag{6.7}
$$

**Proposition 6.2 (Triplet distance and a source lower bound).** With the
single Frobenius norm and the comparison class (6.7),

$$
\operatorname{dist}_F(G,\mathcal T_6)^2
 =\frac23\bigl((y-x)^2+(z-y)^2\bigr).
\tag{6.8}
$$

Every positive generic source also satisfies

$$
\operatorname{dist}_F(G,\mathcal T_6)
 \ge \frac{2}{\sqrt3}\,\bigl|(p_0-p_{13})(p_1-p_3)\bigr|.
\tag{6.9}
$$

The bound is sharp within the actual source domain. For

$$
p_*=(2,3,3,1,1)/10,
\tag{6.10}
$$

one has $(X,Y,Z)=(2/5,1/5,3/10)$, $r=7/10$ and
$0=\kappa_-<\kappa=1/10<\kappa_+=1/5$, so the source is full-support and
generic. Its three block values are

$$
(\lambda_\alpha,\lambda_\beta,\lambda_\gamma)
 = (7/50,3/25,1/10),
$$

so $x=1/10$, $y=3/25$, $z=7/50$, and both sides of (6.9) equal
$1/(25\sqrt3)$.

**Proof.** The eigenvalues of $G$ are
$x,x,y,y,z,z$. By the finite-dimensional real-symmetric spectral matching
theorem of Hoffman and Wielandt, the orthogonal minimization in (6.7) reduces
to matching these ordered eigenvalues to two values, each repeated three
times. The minimizing split is

$$
[x,x,y]\quad\text{and}\quad[y,z,z],
$$

whose least-square representatives are
$\mu=(2x+y)/3$ and $\nu=(y+2z)/3$. They are nonnegative and satisfy
$\mu\le\nu$, so they define an admissible PSD matrix $A$. The residual sum is

$$
2(x-\mu)^2+(y-\mu)^2+(y-\nu)^2+2(z-\nu)^2
 =\frac23\bigl((y-x)^2+(z-y)^2\bigr),
$$
which proves (6.8). This is the standard spectral approximation ingredient,
used here as classical mathematics rather than as a new source theorem.

From (6.5), $|\lambda_\alpha-\lambda_\gamma|=
2|(p_0-p_{13})(p_1-p_3)|$. Also,

$$
(y-x)^2+(z-y)^2\ge\frac12(z-x)^2
 \ge\frac12(\lambda_\alpha-\lambda_\gamma)^2.
$$

Combining this with (6.8) yields (6.9). For (6.10), direct substitution gives
$\lambda_\alpha=14/100$, $\lambda_\beta=12/100$ and
$\lambda_\gamma=10/100$, with equal adjacent gaps $1/50$. Moreover
$(p_0-p_{13})(p_1-p_3)=1/50$, so equality holds in both inequalities. The
displayed fiber coordinates verify that this equality witness is an actual
admissible source, not a freely chosen spectral triple. $\square$

The comparison in Proposition 6.2 is only for the generic six-dimensional
latent support. It does not provide a padded distance formula for the walls,
assert that the comparator is source-realizable, or assign a physical error
to any laboratory task. The citation used for the spectral matching step is
A. J. Hoffman and H. Wielandt, “The variation of the spectrum of a normal
matrix,” *Duke Mathematical Journal* 20(1) (1953), 37–39,
[doi:10.1215/S0012-7094-53-02004-3](https://doi.org/10.1215/S0012-7094-53-02004-3).

### 6.3 Isotropic metric without native rotational control

Take the source-locus point

$$
p_{\mathrm{iso}}=(1,1,8,1,1)/12.
\tag{6.11}
$$

It has $(X,Y,Z)=(1/6,1/6,2/3)$, $r=1/3$ and
$0<\kappa=1/12<1/6$, and lies on both walls. The balanced-parity Haar
convention of §5 gives

$$
G_{\mathrm{lat}}=\frac19 I_3.
\tag{6.12}
$$

The three latent coordinates in (4.8) have the actual endpoint set

$$
\mathscr S=\{q(\beta,\varepsilon)=(\sqrt2\cos\beta,
 \sqrt2\sin\beta,\varepsilon):\beta\in\mathbb T,
 \varepsilon\in\{-1,1\}\},
\tag{6.13}
$$

and the endpoint law is uniform in $\beta$ with the two parity values equally
weighted. Equation (6.12) is therefore a metric symmetry of the pullback
Gram, not an assertion that this law is $SO(3)$-invariant.

There is nevertheless a full ambient orthogonal intertwining for the static
decoder. Let $D_{\mathrm{iso}}$ be the centered $10\times3$ decoder in (4.7),
so that $D_{\mathrm{iso}}^{\mathsf T}D_{\mathrm{iso}}=I_3/9$. It is injective.
For each $Q\in SO(3)$ define on its image

$$
W_Q(D_{\mathrm{iso}}u)=D_{\mathrm{iso}}Qu,
$$

and define $W_Q$ to be the identity on the orthogonal complement of that
image. The Gram identity makes this a well-defined orthogonal map, and the
construction gives a representation with

$$
D_{\mathrm{iso}}Q=W_QD_{\mathrm{iso}}.
\tag{6.14}
$$

Thus the finite static map does satisfy the intertwining form of (9.1) from
[FIB harmonic-edge load](FIB_LEGAL_EDGE_LOAD_SECOND_ORDER_LOSS_LOCALIZATION_AND_LOCAL_TILT_AVERAGING_OBSTRUCTION.md).
What fails is the stronger source
and operation statement that the reachable endpoint set and its law are
preserved by every $Q$ and that every such $Q$ is generated by Definition 3.1
controls.

For an explicit failure, use the proper rotation

$$
Q_x(\pi/2)=
\begin{pmatrix}1&0&0\\0&0&-1\\0&1&0\end{pmatrix}\in SO(3).
\tag{6.15}
$$

The reachable point $q_0=(0,\sqrt2,1)$ is sent to
$Q_x(\pi/2)q_0=(0,-1,\sqrt2)$, whose third coordinate is not a parity value;
it is outside $\mathscr S$. Since $D_{\mathrm{iso}}$ is injective,
$c+D_{\mathrm{iso}}Q_x(\pi/2)q_0$ is outside the actual decoded endpoint set
$c+D_{\mathrm{iso}}\mathscr S$. Theorem 3.3 identifies the native endpoint
group as $\mathbb T\times\mathbb Z_2$, so no lawful loop reaches it. The
endpoint law also changes under this rotation: under the pushforward, the
third coordinate is the continuous variable $\sqrt2\sin\beta$ rather than
the almost-surely discrete variable $\varepsilon$. The update law (4.10),
inherited from the diagonal/product operations in Theorem 3.8, cannot supply
this mixing.

This counterexample does not refute (9.1): (6.14) is precisely a static
intertwining of a linear decoder. It shows that static linear equivariance,
metric isotropy, endpoint-set and law invariance, and lawful control
realization are four different requirements. No physical spatial dimension,
metric transport, native $SO(3)$ action, or complete explanation of why three
is forced follows from this appendix.

## 6.99 追加锚

## 7. Attained common-source error for a prescribed native loop

**Definition 7.1 (Same-history comparison on the positive triplet locus).**
Fix any source in the complete locus of Theorem 6.1,

$$
p=(a,b,8b,b,a),\qquad a,b>0,\qquad 2a+10b=1,
\qquad \lambda=16ab>0.
\tag{7.1}
$$

Keep the fixed initial phases and the five doubled coherence pairs of (4.1).
Write $D=D_b$ and $c=c_b$ for the original decoder and offset in (4.7).
Theorems 3.3 and 3.7 identify the endpoint group with
$\mathbb T\times\mathbb Z_2$ and its coordinate image with the set
$\mathscr S$ in (6.13). Give this group the normalized Haar law $\mu$ of
§5: the angle is uniform and parity is independent and balanced. The random
variable $h$ below is an endpoint residual class with this law; it is not a
uniformly chosen integer winding or a prescribed distribution on loop paths.
For $h=(\beta,\varepsilon)$, the supplied identities (4.7), (4.8), (5.1)
and (6.4) are

$$
\begin{gathered}
q(h)=(\sqrt2\cos\beta,\sqrt2\sin\beta,\varepsilon)^{\mathsf T},
\qquad y(h)=c+Dq(h),\\
\mathbb E_\mu q=0,\qquad
\mathbb E_\mu[qq^{\mathsf T}]=I_3,\qquad
D^{\mathsf T}D=\lambda I_3.
\end{gathered}
\tag{7.2}
$$

Let $\mathcal L_p$ consist of all Definition 3.1 loops based at this source,
on a finite time interval with finite phase variation, including every
integer winding. Write $u$ also for a loop's residual increment and $m_u$
for its integer winding. Equations (4.9)–(4.11) give
$q(h+u)=T(u)q(h)$, where

$$
T(u)=R_{\theta(u)}\oplus[\sigma(u)],\qquad
\theta(u)=u_\beta\pmod{2\pi},\qquad \sigma(u)=(-1)^{m_u}.
$$

The exact native image is therefore the already established group
$\mathcal N=\{R_\theta\oplus[\sigma]:\theta\in\mathbb T,
\ \sigma\in\{-1,1\}\}$. A comparison target is a matrix $Q\in SO(3)$.
Define

$$
\begin{aligned}
y_Q(h)&=c+DQq(h),\\
\mathcal E_p(u,Q)&=
  \mathbb E_{h\sim\mu}\|y(h+u)-y_Q(h)\|_{\mathbb R^{10}}^2,\\
\mathcal E_p^*(Q)&=\inf_{u\in\mathcal L_p}\mathcal E_p(u,Q).
\end{aligned}
\tag{7.3}
$$

Here one loop $u$ is fixed for all $h$. It may be selected using the fixed
source and $Q$, but not using the input history. Both responses in (7.3)
use the same $h$, and the norm is the original ten-output Euclidean norm.
The matrix $Q$ is a comparison target, not an assumed available control;
$y_Q(h)$ need not be a reachable output. No change of coupling, whitening,
history-dependent feedback, sampling procedure or cost is part of this
definition. The separate rotation and physical-interpretation hypotheses of
§9 and common-source continuation factorization of §12 of
[FIB harmonic-edge load](FIB_LEGAL_EDGE_LOAD_SECOND_ORDER_LOSS_LOCALIZATION_AND_LOCAL_TILT_AVERAGING_OBSTRUCTION.md)
are not supplied by (7.1)–(7.3). In particular, these definitions and the
results below establish neither physical spatial dimension, native $SO(3)$
control, nor a common-source map to all harmonic paths.

**Proposition 7.2 (Paired responses identify the lawful action).** Under
Definition 7.1 put $Y(h)=y(h)-c$ and $Y_u(h)=y(h+u)-c$. Their ordered
common-history cross moment satisfies

$$
C_u:=\mathbb E_\mu[Y_u(h)Y(h)^{\mathsf T}]
       =DT(u)D^{\mathsf T},\qquad
T(u)=\lambda^{-2}D^{\mathsf T}C_uD.
\tag{7.4}
$$

Thus $C_u$ determines the native endpoint action of a lawful loop, although
it need not determine that loop's path or full integer winding. The analogous
paired matrix of the comparison response is $C_Q=DQD^{\mathsf T}$, and
$C_u=C_Q$ holds if and only if $T(u)=Q$. The same pairing gives

$$
\mathcal E_p(u,Q)
 =\lambda\|T(u)-Q\|_F^2
 =\lambda\bigl(6-2\operatorname{tr}(T(u)^{\mathsf T}Q)\bigr).
\tag{7.5}
$$

For independent re-preparation, meaning two independent residual classes
$h,h'\sim\mu$ while keeping $u$ fixed, the corresponding identities instead
are

$$
\mathbb E[Y_u(h')Y(h)^{\mathsf T}]=0,\qquad
\mathbb E\|y(h'+u)-y_Q(h)\|_{\mathbb R^{10}}^2=6\lambda.
\tag{7.6}
$$

**Proof.** The supplied update law gives $Y_u(h)=DT(u)q(h)$. Substituting
the common-history second moment in (7.2) proves the first equality of
(7.4). Multiplication on the left by $D^{\mathsf T}$ and on the right by
$D$ gives $\lambda^2T(u)$, proving recovery and, with $T(u)$ replaced by
$Q$, the assertion about $C_Q$. For $M=T(u)-Q$, the same moment gives

$$
\mathbb E\|DMq(h)\|^2
 =\operatorname{tr}(M^{\mathsf T}D^{\mathsf T}DM)
 =\lambda\operatorname{tr}(M^{\mathsf T}M).
$$

Both $T(u)$ and $Q$ are orthogonal $3\times3$ matrices, so expansion gives
(7.5), including odd-winding $T(u)$ of determinant $-1$. This conversion
of a least-squares objective into trace maximization is the classical
orthogonal Procrustes reduction; see J. Lawrence, J. Bernal and
C. Witzgall, *A Purely Algebraic Justification of the Kabsch–Umeyama
Algorithm*, [arXiv:1902.03138v6](https://arxiv.org/html/1902.03138v6), §1.
Here the common-source law and the original decoder fix the trace pairing,
and the optimization domain remains the restricted native image
$\mathcal N$.

For independent $h,h'$, the zero means in (7.2) imply
$\mathbb E[q(h')q(h)^{\mathsf T}]=0$. Hence both the displayed independent
cross moment and the cross term in the independent squared error vanish.
Each of its two squared terms has expectation $3\lambda$, by (7.2) and
orthogonality. This proves (7.6). These are identities for the specified
joint laws, not instructions for acquiring paired data. $\square$

**Theorem 7.3 (Attained optimal error over every lawful winding sector).**
For every source (7.1) and every comparison target $Q\in SO(3)$, put
$z=Q_{33}\in[-1,1]$. Then

$$
\boxed{\mathcal E_p^*(Q)=4\lambda\bigl(1-\max(z,0)\bigr).}
\tag{7.7}
$$

The infimum is attained by an actual finite loop in $\mathcal L_p$, fixed
independently of $h$. More precisely, for each integer $m$, with the same
balanced input law $\mu$ and only the prescribed loop's winding fixed,

$$
\min_{u\in\mathcal L_p:\ m_u=m}\mathcal E_p(u,Q)
 =\begin{cases}
 4\lambda(1-z),&m\text{ even},\\
 4\lambda,&m\text{ odd}.
 \end{cases}
\tag{7.8}
$$

If $z>-1$, a minimizing angle in each sector is uniquely determined modulo
$2\pi$ by

$$
(\cos\theta_*,\sin\theta_*)
 =\frac{(Q_{11}+Q_{22},\ Q_{21}-Q_{12})}{1+z}.
\tag{7.9}
$$

If $z=-1$, every angle minimizes in each sector. For the unrestricted
minimum, the loop has even winding when $z>0$, odd winding when $z<0$,
and either parity when $z=0$. These conditions on angle and parity describe
all minimizing native actions, and every one of them has a finite lawful
loop representative. In particular, the endpoint values are

$$
\begin{array}{c|ccc}
z&\text{minimum in each even sector}&
  \text{minimum in each odd sector}&\mathcal E_p^*(Q)\\ \hline
-1&8\lambda&4\lambda&4\lambda\\
0&4\lambda&4\lambda&4\lambda\\
1&0&4\lambda&0
\end{array}
\tag{7.10}
$$

Zero error occurs exactly for the proper native targets
$Q=R_\theta\oplus[1]$.

**Proof.** Proposition 7.2 reduces the error to a trace on the exact native
image. Write $A=(Q_{ij})_{1\le i,j\le2}$ and put
$x=Q_{11}+Q_{22}$, $v=Q_{21}-Q_{12}$. With the rotation convention of
(4.10),

$$
\operatorname{tr}\bigl((R_\theta\oplus[\sigma])^{\mathsf T}Q\bigr)
 =x\cos\theta+v\sin\theta+\sigma z.
\tag{7.11}
$$

Orthogonality gives
$\|A\|_F^2=2-(Q_{13}^2+Q_{23}^2)=1+z^2$.
Since $Q^{-1}=Q^{\mathsf T}$ and $\det Q=1$, its $(3,3)$ cofactor gives
$\det A=z$. Consequently

$$
x^2+v^2=\|A\|_F^2+2\det A=(1+z)^2.
\tag{7.12}
$$

Because $1+z\ge0$, the maximum of
$x\cos\theta+v\sin\theta$ is $1+z$. For $z>-1$ equality holds exactly
at (7.9); for $z=-1$ both coefficients vanish and every angle attains it.
With $\sigma=(-1)^m$, (7.5) therefore gives the sector value

$$
\lambda\bigl(6-2(1+z+\sigma z)\bigr)
 =4\lambda-2\lambda(1+\sigma)z,
$$

which is (7.8) at the matrix level. Maximizing over both signs replaces
$\sigma z$ by $|z|$, so the maximum trace is
$1+z+|z|=1+2\max(z,0)$. This proves the lower bound in (7.7) and the
listed necessary and sufficient conditions on a minimizing native action.

To realize every such action without passing to a closure, apply the
finite reachability of §§3.2–3.3 and the area formula of Theorem 3.7 as
follows. For the fixed source (7.1),

$$
X=Y=a+b,\qquad Z=8b,\qquad r=2(a+b),\qquad
\kappa_0=a\in(0,a+b).
$$

Choose once and for all the second interior height $\kappa_1=a/2$.
For any desired integer $m$ and any real representative $\theta$ of a
desired angle, concatenate the signed winding-$m$ fixed-height circles
at $\kappa_0$ with one of the zero-winding rectangles of Theorem 2.6,
using probability heights $\kappa_0,\kappa_1$ and phase height

$$
\alpha=
\frac{r(\pi m-\theta)-2\pi m\kappa_0}{\kappa_1-\kappa_0}.
\tag{7.13}
$$

The circle part has signed area $2\pi m\kappa_0$ and the rectangle has
signed area $\alpha(\kappa_1-\kappa_0)$. The total area is therefore
$r(\pi m-\theta)$, so Theorem 3.7 gives $u_\beta=\theta$ and winding
$m$. The rectangle is understood as the same relative control path appended
at the terminal phase lift of the circles. Its phase increment is zero,
so it does not change $m$.

All probability heights traversed lie between $a/2$ and $a$, a compact
subinterval of the positive fiber $(0,a+b)$. The denominator in (7.13) is
nonzero, its numerator is finite, and the concatenation has finitely many
piecewise linear legs and finite phase variation. It begins and ends at
the original source. Its parameters depend only on $p,m,\theta$, not on
$h$. Thus it is a Definition 3.1 loop realizing the desired matrix exactly.
Taking the minimizing angles and parities proves attainment in every
sector and in (7.7), rather than merely approximation by lawful matrices.

The table follows by substitution. Finally (7.7) is zero exactly when
$z=1$. Orthogonality then forces the third row and column to be
$(0,0,1)$, while the upper block is in $SO(2)$ because $\det Q=1$.
Hence $Q=R_\theta\oplus[1]$, and the constructed even-winding loops
realize it. $\square$

**Corollary 7.4 (Complete endpoint-law symmetry can have positive native
error).** Let $\nu=q_*\mu$ be the law on $\mathscr S$ under Definition 7.1.
Its proper linear symmetry group equals the proper symmetry group of its
support, and both are

$$
\{Q\in SO(3):Q_*\nu=\nu\}
 =\{Q\in SO(3):Q\mathscr S=\mathscr S\}
 =\{A\oplus[\det A]:A\in O(2)\}.
\tag{7.14}
$$

Those with $\det A=1$ are native and have zero best error; those with
$\det A=-1$ have best same-history error $4\lambda>0$. In particular,
the proper comparison rotation

$$
Q_*=\operatorname{diag}(1,-1,-1)=Q_x(\pi)
\tag{7.15}
$$

preserves the complete endpoint law and support, both before and after
decoding by $c+Dq$, but satisfies

$$
\min_{u\in\mathcal L_p}\mathcal E_p(u,Q_*)=4\lambda>0.
\tag{7.16}
$$

Every fixed lawful loop has the same single-endpoint output law as this
comparison target. Its common-history paired response nevertheless differs
from that of $Q_*$.

**Proof.** The law $\nu$ has support exactly $\mathscr S$, because uniform
angle gives positive measure to every nonempty circle arc and each parity
has positive mass. A linear orthogonal map is a homeomorphism, so preserving
$\nu$ implies preserving its support. Conversely suppose $Q\mathscr S=
\mathscr S$ and write its third row as $(v_1,v_2,z)$. For a fixed parity
$\varepsilon$, the third coordinate of $Qq(\beta,\varepsilon)$ is

$$
\sqrt2(v_1\cos\beta+v_2\sin\beta)+z\varepsilon\in\{-1,1\}
\qquad(\beta\in\mathbb T).
$$

It is a continuous function on a connected circle with values in a
two-point set, so it is constant. Its values at $0,\pi$ and at
$\pi/2,3\pi/2$ force $v_1=v_2=0$. The third row has unit norm, giving
$z=\pm1$; orthogonality then yields $Q=A\oplus[z]$ with $A\in O(2)$.
The determinant-one condition gives $z=\det A$.
Every such $A$ preserves uniform measure on the planar circle, and
multiplication of parity by $\det A$ preserves balanced parity and its
independence from the angle. Thus these matrices preserve the entire law,
proving (7.14).

When $\det A=1$, $A$ is a planar rotation and the target lies in
$\mathcal N$. When $\det A=-1$, its planar reflection is not a native
planar rotation. Applying Theorem 7.3 with $z=1$ or $z=-1$ proves the
respective zero and $4\lambda$ errors. In (7.15) the action is explicitly
$(\beta,\varepsilon)\mapsto(-\beta,-\varepsilon)$, so it preserves
$\nu$ and $\mathscr S$. Pushing forward by $q\mapsto c+Dq$ proves
equality of the complete ten-output laws and supports as well.

Each native $R_\theta\oplus[\sigma]$ also preserves $\nu$, by angle
translation and parity multiplication. Hence its single-endpoint law agrees
with the target's. But $T(u)\ne Q_*$ for every lawful loop: the planar
block of $T(u)$ has determinant $1$, whereas the planar block of $Q_*$
has determinant $-1$. The recovery identity (7.4) therefore gives
$C_u\ne C_{Q_*}$. This proves the paired-response distinction for the
same source and the same history; (7.16) quantifies it in the stipulated
metric. Independent re-preparation would instead give $6\lambda$ by
(7.6). $\square$

**Corollary 7.5 (The existing isotropic source).** For
$p_{\mathrm{iso}}=(1,1,8,1,1)/12$ from (6.11), all statements above hold
with $\lambda=1/9$. In particular,

$$
\mathcal E_{p_{\mathrm{iso}}}^*(Q)
 =\frac49\bigl(1-\max(Q_{33},0)\bigr),\qquad
\mathcal E_{p_{\mathrm{iso}}}^*(Q_*)=\frac49,
$$

whereas the independent re-preparation error is $2/3$ for every fixed loop
and every proper comparison target. All these minima are attained under the
original doubled-coherence and ten-output metric convention.

**Proof.** Substitute $a=b=1/12$ into $16ab$, Theorem 7.3,
Corollary 7.4 and (7.6). The finite loops constructed in the theorem remain
inside this source's positive fiber. $\square$

## 7.99 追加锚
