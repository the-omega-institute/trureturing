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

## 8. Reachable open-prefix rays and their fixed affine response boundary

### 8.1 The prefix query on the original controls

**Definition 8.1 (Current source task).** Fix the means of Definition 2.1,
one initial height $\kappa_0\in J_b:=(\kappa_-,\kappa_+)$, and arbitrary
fixed preparation phases $\theta^{\rm in}$. Every history starts from this
same preparation. Use exactly Definition 3.1 controls on finite compact
intervals, with finite phase variation and full support throughout. Query
the current ray at any terminal time, without imposing the base/phase
closing condition at that time. This is a new prefix query on the existing
controls; the endpoint query in §§3–7 continues to require its original
closing condition.

Write the real phase increment and real control increment as

$$
h(t)=\theta(t)-\theta^{\rm in},\qquad
L(t)=\chi(t)-\chi(0).
\tag{8.1}
$$

Choose the initial relation lift consistently with
$d^{\mathsf T}\theta^{\rm in}$; only increments will matter. Then
$h_2=0$ and $d^{\mathsf T}h=L$ on every admissible history. A common
constant gauge change makes the middle amplitude positive, with initial
relative phases $\eta_s=\theta_s^{\rm in}-\theta_2^{\rm in}$ and
$\eta_2=0$. It does not set any of the other preparation phases to zero.

Use the walls $E_-:X+Y=r$ and $E_+:X=Y$ and the grouped space $U_b$
from the proof of Theorem 3.2. Thus $h_2=0$, with the additional increment
equalities $h_0=h_{13}$ on $E_-$ and $h_1=h_3$ on $E_+$. Let

$$
g=4-\mathbf1_{E_-}-\mathbf1_{E_+},\qquad
\Lambda_b=U_b\cap 2\pi\mathbb Z^5.
\tag{8.2}
$$

The equalities concern increments, not equality of arbitrary initial
phases. The current source, a history producing it, and the controller's
real lifted record are separate objects in this task.

### 8.2 Exact realization of the entire current-ray domain

**Theorem 8.2 (Open-prefix source manifold).** The exact set of pairs
$(\kappa(T),h(T))$ of real lifted source coordinates obtainable from
Definition 8.1 is $J_b\times U_b$. In particular the exact current-ray
domain, with its inherited smooth structure, is

$$
\mathcal M_b\simeq J_b\times(U_b/\Lambda_b)
\simeq J_b\times\mathbb T^g.
\tag{8.3}
$$

| Fixed mean regime | Exact phase increment domain | Intrinsic current-ray dimension |
| --- | --- | --- |
| Neither wall | $\mathbb T^4$ | $5$ |
| $E_-$ only | $\mathbb T^3$, with $h_0=h_{13}$ | $4$ |
| $E_+$ only | $\mathbb T^3$, with $h_1=h_3$ | $4$ |
| Both walls | $\mathbb T^2$, with both equalities | $3$ |

Every point has an exact finite piecewise linear control realization. At
most $g-1$ of the rectangles already supplied by Theorem 3.2, one
fixed-height phase leg and one probability leg suffice. In the full-support
fixed-mean model, the current-ray domain is three-dimensional if and only
if $X=Y=r/2$.

Proof. For the converse inclusion, $w(\kappa)\in U_b$ at every interior
height by Theorem 3.2. Integrating the original ODE therefore gives
$h(T)\in U_b$ for every admissible history, including absolutely
continuous ones. The endpoint probability coordinate is in $J_b$ by
admissibility. There are no further real constraints from a closing
condition, because the query in Definition 8.1 imposes none.

For sufficiency, prescribe any $\kappa_*\in J_b$ and $v\in U_b$. Set

$$
L_*=d^{\mathsf T}v,\qquad
v_0=v-L_*w(\kappa_0).
\tag{8.4}
$$

The identity $d^{\mathsf T}w=1$ gives $v_0\in V_b$. Theorem 3.2 supplies
an exact zero-winding rectangle menu at $\kappa_0$ with residual $v_0$,
using $g-1$ heights selected independently of $v$. Execute that menu,
then at $\kappa_0$ increase the real control phase by $L_*$, and finally
move $\kappa_0$ to $\kappa_*$ with control phase fixed. The phase leg adds
$L_*w(\kappa_0)$ and the probability leg adds zero phase. Thus the final
real increment is exactly $v$, and the final height is exactly
$\kappa_*$. The control ends with real increment $L_*$, as required by
the integrated ODE.

Here the rectangle construction is consumed, not replaced by an
accessibility or density argument. Its actual continuous realization is
also supplied by
[`finite_rectangles_realize`](https://github.com/the-omega-institute/trureturing/blob/c8dd0930fa71461d0d6ee93c10fb7075e3251a6e/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean).
The correspondence is $b=(X,Y,Z)$, $k_0=\kappa_0$, and menu entries
$(k,a)=(\kappa_j,a_j)$ from Theorem 3.2; its mode index $4$ is mode
$13$ here. Its $\operatorname{phaseWeight}$ is exactly $w$, its
$\operatorname{probability}$ is $p_\kappa$, and its residual is
$\sum_j a_j(w(\kappa_j)-w(\kappa_0))$. Its initial zero phases are
increments $h=0$ here. Translating its control phase by $\chi(0)$ and its
state phase by $\theta^{\rm in}$ preserves the ODE because the
coefficients depend only on $\kappa$. The supplier includes empty menus,
negative or zero coefficients and both walls. The existence of the menu
representing $v_0$ comes from Theorem 3.2, rather than from that supplier.

The two extra legs obey Definition 3.1 directly. Each is an affine
control leg; $w$ is constant on the phase leg and the phase derivative is
zero on the probability leg. Every probability segment stays inside
$J_b$ by convexity. The finite set of heights and finite real phase
increments give a compact positive range and finite total phase
variation. Concatenation consequently gives a lawful finite history,
with no speed, time-budget or uniform variation bound asserted.

It remains to justify that (8.3) describes rays rather than redundant
phase representatives. In the middle-positive gauge the state is

$$
\psi_s(\kappa,h)=\sqrt{p_s(\kappa)}\,
e^{-i(\eta_s+h_s)},\qquad \psi_2=\sqrt Z>0.
\tag{8.5}
$$

Equality of rays forces equality of these representatives: their middle
entries fix the common phase. Equality of moduli then gives equal
$\kappa$, for example from $p_{13}=\kappa$, and equality of phases gives
$h-h'\in\Lambda_b$. Conversely these conditions give the same ray.
Each pole group has one independent real increment and one independent
$2\pi$ period, so $U_b/\Lambda_b\simeq\mathbb T^g$. There is no further
finite quotient. The inverse in the projective chart with nonzero middle
coordinate recovers $\kappa$ and each phase circle smoothly from the
nonzero component ratios. Thus (8.5) is a smooth embedding with the
claimed dimension. The two wall equations hold together precisely when
$X=Y=r/2$. $\square$

**Proposition 8.3 (Containment of prefixes and retained lift information).**
Every actual prefix in Definition 8.1 extends to a Definition 3.1
base/phase loop of any specified integer winding. On a history already
known to be admissible, its current ray tests the endpoint closing
condition by

$$
\kappa=\kappa_0,\qquad e^{i d^{\mathsf T}h}=1.
\tag{8.6}
$$

It does not determine the integer winding, the full lifted control record,
or whether an arbitrary proposed intervening path obeyed the ODE.

Proof. Given the actual terminal lift $L$ of a prefix, first return its
height to $\kappa_0$ at fixed control phase. At $\kappa_0$ append a phase
leg of increment $2\pi m-L$. Both legs are finite and legal, and the
complete history has winding $m$. The existing prefix is preserved, not
replaced by a history with the same endpoint. Thus querying all prefixes
does not add a new kind of legal control.

The quantity $e^{i d^{\mathsf T}h}$ is a well-defined function of the ray
and fixed preparation: $d$ is integral and
$d^{\mathsf T}\mathbf1=0$. For an admissible history it equals $e^{iL}$,
so (8.6) is exactly the original periodic base closing condition. This
conditional test does not certify the preceding evolution.

To exhibit the loss of winding, let group $a$ have multiplicity $m_a$
and sign $\varepsilon_a$, and put $c_a=m_a\varepsilon_a$ as in §3.3.
A returned ray has real grouped increments $2\pi\ell_a$ and hence
winding $m=\sum_a c_a\ell_a$. Conversely every such integer choice is
realized at $\kappa_0$ by Theorem 8.2, and gives the initial ray. The
possible windings of ray-returning loops are consequently
$\gcd(c_1,\ldots,c_g)\mathbb Z$, namely $\mathbb Z$ off the double wall
and $2\mathbb Z$ on it. Nonzero examples have exactly the same current
ray as the constant loop. A path followed by its reverse supplies a
separate ambiguity even with real terminal increments fixed.

For path certification, compare the constant history with the proposed
path $\kappa(t)=\kappa_0$, $\chi(t)=\chi(0)$,
$h(t)=\sin^2(\pi t)(1,1,0,1,1)^{\mathsf T}$ on $[0,1]$. The latter
has full support, the same endpoints, the middle-fixed gauge and
$d^{\mathsf T}h=0$ throughout, including both wall equalities when
applicable. But its nonzero phase derivative violates
$\dot\theta=w\dot\chi=0$ in the interior. Its endpoint ray cannot
distinguish it from the legal constant history. The ray therefore
retains the closing predicate conditional on admissibility while
forgetting integer and path data. $\square$

### 8.3 The unchanged coherence menu observes this same source

**Theorem 8.4 (Current-ray observability over variable probability).**
The ten doubled coherence outputs of Theorem 3.12 separate every pair of
current rays in $\mathcal M_b$. The resulting output map is a smooth
embedding, including on either individual wall and their intersection.

Proof. Keep the oriented edge order

$$
\mathcal E=((0,1),(0,2),(0,3),(1,13),(3,13)).
\tag{8.7}
$$

For $e=(i,j)$ let $\delta_e^0=\theta_i^{\rm in}-\theta_j^{\rm in}$.
The original output pair, with the original factor of two, is

$$
y_e(\kappa,h)=2\sqrt{p_i(\kappa)p_j(\kappa)}
\begin{pmatrix}
\cos(\delta_e^0+h_i-h_j)\\
\sin(\delta_e^0+h_i-h_j)
\end{pmatrix}.
\tag{8.8}
$$

Its middle-reference block recovers the probability coordinate directly:

$$
\|y_{02}\|^2=4Z(r-X-Y+\kappa),\qquad
\kappa=\frac{\|y_{02}\|^2}{4Z}-(r-X-Y).
\tag{8.9}
$$

The strict condition $Z>0$ is used here. Once $\kappa$ is known, all
edge amplitudes in (8.8) are known and nonzero. Normalizing each pair and
removing its fixed preparation phase gives $e^{i(h_i-h_j)}$. Reuse the
connected graph of Theorem 3.12: the $02$ edge fixes $h_0$ relative to
$h_2=0$; edges $01$ and $03$ then fix $h_1,h_3$; edge $1,13$ fixes
$h_{13}$. These are precisely the current phase classes, with any group
equalities already imposed. No new observable has been introduced.

Equation (8.9) and these circle-valued phase reconstructions are smooth
on the positive domain; division is only by nonzero amplitudes. They give
a smooth inverse on the output image, proving the embedding assertion.
The reconstruction is of ideal expectations on the same source; it is
neither recovery of the producing history nor an assertion about exact
finite-shot acquisition. $\square$

### 8.4 One affine decoder across the full prefix family

**Definition 8.5 (Prefix affine capacity).** Apply the contract of
Definition 4.1 to the domain $\mathcal M_b$ instead of the closed-loop
endpoint domain. Thus $\operatorname{cap}^{\rm pre}_{\rm aff}(b)$ is the
least integer $n$ for which

$$
y(\kappa,h)=c+D z(\kappa,h)\qquad((\kappa,h)\in\mathcal M_b)
\tag{8.10}
$$

with an arbitrary encoder into $\mathbb R^n$, one linear
$D:\mathbb R^n\to\mathbb R^{10}$ and one offset $c\in\mathbb R^{10}$.
Both $D$ and $c$ are fixed over all current probabilities, phases and
histories in this fiber. They may depend on the fixed means and fixed
preparation. The output metric is the original Euclidean metric on the
ten doubled expectations. This is a current-output contract, without an
additional linear continuation contract.

**Theorem 8.6 (Exact prefix capacities and the double-wall decoder).**
For Definition 8.5,

$$
\operatorname{cap}^{\rm pre}_{\rm aff}(b)=
\begin{cases}
10,&\text{neither wall},\\
6,&\text{exactly one wall},\\
4,&\text{both walls}.
\end{cases}
\tag{8.11}
$$

All upper bounds use offset zero and one decoder fixed on the whole
variable-probability domain. The lower bounds allow arbitrary fixed
offsets and arbitrary nonlinear encoders.

Proof. Let $\upsilon(t)=(\cos t,\sin t)^{\mathsf T}$,
$J=\operatorname{diag}(1,-1)$, and let

$$
O=\bigoplus_{e\in\mathcal E}R_{\delta_e^0},\qquad
\widetilde y=O^{\mathsf T}y.
\tag{8.12}
$$

This fixed orthogonal change merely exposes the preparation phases in
the proof; the final decoder into the original outputs includes $O$.
It neither whitens nor rescales the output metric.

At no wall the five phase characters are, on the full $\mathbb T^4$,

$$
h_0-h_1,\quad h_0,\quad h_0-h_3,\quad
h_1-h_{13},\quad h_3-h_{13}.
\tag{8.13}
$$

Their integer coefficient vectors, in order $(h_0,h_1,h_3,h_{13})$, are

$$
(1,-1,0,0),\ (1,0,0,0),\ (1,0,-1,0),\
(0,1,0,-1),\ (0,0,1,-1).
\tag{8.14}
$$

They are nonzero and pairwise distinct even up to sign. Fix any interior
$\kappa_*$. Theorem 8.2 realizes the entire phase torus at this one
height; every amplitude in (8.8) is strictly positive. Distinct torus
characters, including the constant and both signs of (8.14), are linearly
independent. Hence the constant and the ten real sine/cosine output
functions on this slice are independent. Its affine hull is all of
$\mathbb R^{10}$, proving the lower bound ten for the whole prefix
family. The identity decoder gives the upper bound.

For $E_-$ only, write $h_0=h_{13}=x$, $h_1=y$, $h_3=z$ and use the
three independent angles

$$
\alpha=x-y,\qquad\beta=x,\qquad\gamma=x-z.
$$

The change of circle coordinates has the integer inverse
$(x,y,z)=(\beta,\beta-\alpha,\beta-\gamma)$. Here
$p_0=p_{13}=\kappa$. Set

$$
z_\alpha=2\sqrt{\kappa(X-\kappa)}\,\upsilon(\alpha),\quad
z_\beta=2\sqrt{\kappa Z}\,\upsilon(\beta),\quad
z_\gamma=2\sqrt{\kappa(Y-\kappa)}\,\upsilon(\gamma).
$$

Then, in the edge order (8.7),

$$
\widetilde y=(z_\alpha,z_\beta,z_\gamma,Jz_\alpha,Jz_\gamma).
\tag{8.15}
$$

This is a fixed rank-six linear map of the three displayed pairs,
independent of $\kappa$. At a fixed interior height the three pairs
range over a product of three circles of positive radii. Its affine hull
is $\mathbb R^6$, giving the matching lower bound.

For $E_+$ only, write $h_0=x$, $h_1=h_3=y$, $h_{13}=z$ and use

$$
\alpha=x-y,\qquad\beta=x,\qquad\gamma=y-z.
$$

Their integer inverse is
$(x,y,z)=(\beta,\beta-\alpha,\beta-\alpha-\gamma)$.
Here $p_1=p_3=X-\kappa$. Define

$$
z_\alpha=2\sqrt{p_0(X-\kappa)}\,\upsilon(\alpha),\quad
z_\beta=2\sqrt{p_0Z}\,\upsilon(\beta),\quad
z_\gamma=2\sqrt{\kappa(X-\kappa)}\,\upsilon(\gamma).
$$

The full response is now

$$
\widetilde y=(z_\alpha,z_\beta,z_\alpha,z_\gamma,z_\gamma).
\tag{8.16}
$$

Again the map is fixed and rank six across every probability, and the
fixed-height three-circle slice proves sharpness. The two individual
walls thus have the same capacity for explicitly different edge
identifications.

At both walls let

$$
B=r/2-\kappa>0,\qquad h_0=h_{13}=u,\quad h_1=h_3=v,
\qquad \alpha=u-v,\quad\beta=u.
\tag{8.17}
$$

The two circle coordinates are independent, with inverse
$(u,v)=(\beta,\beta-\alpha)$. Define four real response coordinates by
the two pairs

$$
z_a=2\sqrt{\kappa B}\,\upsilon(\alpha),\qquad
z_b=2\sqrt{\kappa Z}\,\upsilon(\beta),\qquad z=(z_a,z_b).
\tag{8.18}
$$

With $I_2$ the two-by-two identity, an explicit decoder into the original
ten outputs is

$$
D=O D_0,\qquad
D_0=
\begin{pmatrix}
I_2&0\\
0&I_2\\
I_2&0\\
J&0\\
J&0
\end{pmatrix},\qquad y=Dz,
\qquad D^{\mathsf T}D=4I_2\oplus I_2.
\tag{8.19}
$$

All dependence on the current probability is in the encoder (8.18),
not in $D$ or an offset. The two radii are nonzero at every interior
height. At any such height the full product of two circles is reachable,
so its affine hull is $\mathbb R^4$. Injectivity of $D$ gives a
four-dimensional affine hull of the outputs, proving that no fixed
affine decoder with three input coordinates can serve this domain.

For completeness, the character-independence step is the classical
theorem for distinct homomorphisms to $\mathbb C^\times$, with
$G=\mathbb T^g$, as in Keith Conrad,
[*Linear Independence of Characters*, Theorem 2.1](https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf).
For these characters the same conclusion follows from the torus
orthogonality used in §4: multiply by a conjugate character and integrate
over the phase torus. Sine and cosine are the two linear combinations
of a nonzero character and its inverse. Including the trivial character
rules out a nonzero constant affine relation. This is a test of
functional independence on the realized slice, not an assumption about
the probability distribution of histories.

Finally, the affine hull of $c+D z(\mathcal M_b)$ has dimension at most
$\operatorname{rank}D\le n$, regardless of the encoder. This supplies
all stated lower bounds even when a nonzero fixed offset is allowed.
$\square$

The four coordinates (8.18) carry a three-dimensional curved source
image rather than an open subset of $\mathbb R^4$. Explicitly, if
$a=\|z_a\|^2$ and $b=\|z_b\|^2$, that exact image is

$$
0<b<2rZ,\qquad
a=\frac{rb}{2Z}-\frac{b^2}{4Z^2},
\tag{8.20}
$$

with arbitrary angles of the two nonzero pairs. Indeed
$\kappa=b/(4Z)$, and substitution gives
$a=4\kappa(r/2-\kappa)$; Theorem 8.2 realizes every such point. This
description explains why intrinsic dimension three and affine capacity
four coexist for the same source. Equation (8.19) also retains the
original output distance exactly:

$$
\|y-y'\|^2=4\|z_a-z_a'\|^2+\|z_b-z_b'\|^2.
\tag{8.21}
$$

No additional metric choice is involved in this decoder identity.

### 8.5 The native third direction on the double wall

**Theorem 8.7 (Observable commutator direction of the original law).**
On the actual three-dimensional domain
$\mathcal M_b=(0,r/2)\times\mathbb T^2$ of the double wall, the original
two controls have rank-two distribution

$$
\mathcal D=\operatorname{span}\{P,Q\},\qquad
P=\partial_\kappa,\qquad
Q=\left(\frac12-\frac\kappa r\right)\partial_u
       -\frac\kappa r\partial_v.
\tag{8.22}
$$

Their commutator

$$
C=[P,Q]=-\frac1r(\partial_u+\partial_v)
\tag{8.23}
$$

is a third independent source tangent direction at every interior point.
Finite legal control rectangles realize its flow exactly. This direction
is visible in the original $02$ coherence pair, even though the reduced
relation phase does not change along it.

Proof. Theorem 3.7 supplies the affine double-wall formula for $w$.
Without imposing loop closure, the same pointwise formula gives

$$
\dot u=\left(\frac12-\frac\kappa r\right)\dot\chi,
\qquad\dot v=-\frac\kappa r\dot\chi.
\tag{8.24}
$$

Thus the two independent real control velocities multiply $P$ and $Q$.
Differentiating the coefficients gives (8.23). The determinant of the
two phase columns $Q,C$ in $(u,v)$ coordinates is $-1/(2r)$, which is
nonzero. Together with $P$ they span the tangent space. This is a
statement about the actual source coordinates of Theorem 8.2.

To realize the commutator rather than infer lawfulness from its name,
choose any nonzero $s$ with $\kappa+s\in(0,r/2)$ and any finite real
$A$. Execute the probability leg from $\kappa$ to $\kappa+s$, a phase
leg of increment $A$, the returning probability leg, and a phase leg
of increment $-A$. The supplied rectangle identity of Theorem 2.6 and
the affine formula for $w$ give exactly

$$
\Delta u=\Delta v=-\frac{sA}{r},\qquad
\Delta\kappa=0,\qquad\Delta\chi=0.
\tag{8.25}
$$

This is the time-$sA$ flow of $C$, with no limiting approximation.
For any desired common phase increment $t$, set $A=-rt/s$. All four
legs are legal and finite; neither sign of $A$ is excluded. Small
rectangles also give arbitrarily small nonzero local displacements.
The finite paths in Theorem 8.2 already prove the full global reachable
domain, so no general bracket-accessibility theorem is needed.

In the observable coordinates (8.17), $C\alpha=0$ and
$C\beta=-1/r$. At fixed $\kappa$ the $02$ output is
$2\sqrt{\kappa Z}\,R_{\delta_{02}^0}\upsilon(\beta)$, so its derivative
along $C$ has norm

$$
\|C y_{02}\|=\frac{2\sqrt{\kappa Z}}r>0.
\tag{8.26}
$$

Consequently the new tangent direction is not removed by the ray gauge
or by the declared read menu. The pure probability direction changes
(8.9), while $Q$ changes $\alpha$ at rate $1/2$; these and (8.26)
also exhibit the three independent directions in the same output map.
The commutator changes the phase of the four bottom modes relative to
the positive middle reference. It is not common phase on all five modes.

The contact description is a consumed explanation of this distribution.
The one-form obtained from the actual probability-weighted phase is

$$
\lambda=2\kappa\,du+(r-2\kappa)\,dv,\qquad
\ker\lambda=\mathcal D,\qquad
\lambda\wedge d\lambda=2r\,d\kappa\wedge du\wedge dv\ne0.
\tag{8.27}
$$

Both vector fields in (8.22) annihilate $\lambda$, and their independence
gives its entire two-dimensional kernel. The displayed exterior
derivative verifies the contact criterion directly in this domain.
The form uses the given probabilities and phase convention, with no
new metric imposed.

To connect this precisely to the classical two-amplitude model, define
the fixed orthonormal vectors incorporating all preparation phases by

$$
|+\rangle=\frac{e^{-i\eta_0}|0\rangle+
                         e^{-i\eta_{13}}|13\rangle}{\sqrt2},\qquad
|-\rangle=\frac{e^{-i\eta_1}|1\rangle+
                         e^{-i\eta_3}|3\rangle}{\sqrt2}.
$$

Then the same source representative (8.5) is exactly

$$
|\psi\rangle=\sqrt r\,(z_+|+\rangle+z_-|-\rangle)+\sqrt Z\,|2\rangle,
\qquad
z_+=\sqrt{\frac{2\kappa}{r}}e^{-iu},\quad
z_-=\sqrt{1-\frac{2\kappa}{r}}e^{-iv}.
\tag{8.28}
$$

This parametrizes precisely
$\{(z_+,z_-)\in\mathbb C^2:|z_+|^2+|z_-|^2=1,\ z_+z_-\ne0\}$,
the part of the unit three-sphere with both amplitudes nonzero. John
Etnyre's
[*Introductory Lectures on Contact Geometry*, §2, Example 2.12, equation (7)](https://arxiv.org/abs/math/0111118v2)
uses the form
$\alpha_{\rm std}=\sum_{j=1}^2(x_j\,dy_j-y_j\,dx_j)
=\operatorname{Im}(\overline z_+\,dz_++\overline z_-\,dz_-)$
on the unit sphere. Under (8.28) its pullback is $-\lambda/r$.
The sign follows from the negative exponential convention, and the
nonzero constant does not change the kernel. Etnyre's criterion
$\alpha\wedge d\alpha\ne0$ therefore describes exactly the native
distribution already verified in (8.27).

The simultaneous phase of $(z_+,z_-)$ is the circle direction ordinarily
removed in the Hopf quotient. Here it is measured against $\sqrt Z|2\rangle$;
removing it would erase precisely the direction detected in (8.26).
The correspondence is with this open source domain and this plane field.
It supplies no free $SU(2)$ control on the two amplitudes, no free
$SO(3)$ action on observations, and no identification with physical
position space. $\square$

### 8.6 Current response, continuation and the remaining bridge

**Proposition 8.8 (Four current coordinates need not update affinely).**
On the double wall, the exact current response (8.18) does not admit a
fixed affine update for a nonzero pure probability displacement $s$,
even on any nonempty open interval of starting heights for which both
$\kappa$ and $\kappa+s$ belong to $(0,r/2)$.

Proof. Use the same open-loop velocities $\dot\kappa=s$ and
$\dot\chi=0$ on $[0,1]$ for every starting state in that interval.
Convexity gives lawful probability paths, and the phases $\alpha,\beta$
remain fixed. The updated middle pair is

$$
z_b'=\sqrt{\frac{\kappa+s}{\kappa}}\,z_b.
\tag{8.29}
$$

If a fixed affine map on $(z_a,z_b)$ gave this update for every state,
its middle block would have form $c_b+M z_a+N z_b$. At any fixed
starting height the two phases vary independently. Averaging over both
circles forces $c_b=0$, varying $\alpha$ forces $M=0$, and varying
$\beta$ forces
$N=\sqrt{(\kappa+s)/\kappa}\,I_2$. This factor is nonconstant on
every such open interval when $s\ne0$, a contradiction. The updates
remain completely determined by the current ray and the specified
legal continuation; the obstruction is to a fixed affine update in
these four response coordinates. $\square$

**Mathematical correspondence 8.9 (Scope of the source-level advance).**
Theorems 8.2, 8.4, 8.6 and 8.7 concern one common preparation, the
original ODE, all of its finite admissible prefixes and the unchanged
coherence menu. Their new operational content is the exact open source
domain, its same-source observation map, its fixed affine capacity over
variable probability, and the visibility of its native commutator.
The real-span and finite rectangle suppliers are Theorem 3.2 and the
immutable declaration cited in Theorem 8.2; the connected measurement
graph is supplied by Theorem 3.12. Neither endpoint result alone states
these prefix conclusions.

At $\kappa=\kappa_0$, imposing $e^{id^{\mathsf T}h}=1$ recovers exactly
the original loop phase domains of Theorem 3.3. On the double wall this
condition is $2(u-v)=0\pmod{2\pi}$, or
$\alpha\in\{0,\pi\}$. It reduces the two independent prefix phases
to the old circle and parity. Theorem 4.2 consequently retains its
closed-loop capacities $6,4,3$. Restricting actual histories further to
zero winding retains Proposition 4.3's value $2$; even nonzero winding
can have the same endpoint and is still outside that restricted history
class. The values $10,6,4$ in (8.11) answer the distinct prefix task.
No averaging over current probabilities or choice of controller record
enters their definition.

The
[observer interface, §10](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)
requires a common linear source, calibrated distance and ordered
response data, together with closure under all declared generators.
The
[harmonic interface, §§9 and 12](FIB_LEGAL_EDGE_LOAD_SECOND_ORDER_LOSS_LOCALIZATION_AND_LOCAL_TILT_AVERAGING_OBSTRUCTION.md)
requires, respectively, an additional rotational intertwining and a
common realization of the specified response family. Those hypotheses
are not supplied by a three-dimensional nonlinear source manifold or
by its contact plane field. In particular, Proposition 8.8 separates
the present current-output factorization from a linear continuation
contract. The native-loop and source-law obstructions of §§6–7 retain
their stated endpoint scope.

The character independence and contact-sphere formulas consumed above
are literature-attested classical tools with their explicit parameter
correspondences. The results for this fixed five-mode source are
repo-derived ordinary proofs, not a claim of worldwide originality.
No Fubini–Study metric theorem is needed for these operational
conclusions; the metric and quotient assertions of §2 keep their
original domains.

Within these hypotheses the double wall is exactly the condition for
three-dimensional current rays. Definition 3.1 keeps the means fixed
and supplies no law selecting that wall. Connecting this conditional
source result to a three-axis predictive or physical interface would
still require a selector of the means and a same-source realization of
the additional tasks and operations. The present result neither erases
the unwrapped controller record nor supplies acquisition, memory or
physical spatial-dimension bounds.

## 8.99 追加锚

## 9. Common native continuations, chronological action and future response

### 9.1 One relative command and its actual source domain

**Definition 9.1 (Relative common-command convention).** Fix precisely the
means, preparation and current source $\mathcal M_b$ of Definition 8.1 and
Theorem 8.2. Write $J_b=(\ell_b,u_b)$ and $W_b=u_b-\ell_b>0$. A command
$\gamma=(a,b):[0,T]\to\mathbb R^2$ starts at $(0,0)$ and is piecewise
$C^1$ or absolutely continuous. Here $b(t)$ is a control increment,
not the subscript denoting the fixed means. The two coordinates have
finite variation; for absolutely continuous paths this follows from
integrability of their derivatives on the compact interval. Set

$$
A_\gamma=a(T),\quad B_\gamma=b(T),\quad
m_\gamma=\min_t a(t),\quad M_\gamma=\max_t a(t).
\tag{9.1}
$$

For a current height $k$ and any actual current real relation lift
$\chi_*$, this command means the original history

$$
\kappa(t)=k+a(t),\qquad \chi(t)=\chi_*+b(t),\qquad
\theta(t)=\theta_*+\int_0^t w(k+a(s))\,db(s).
\tag{9.2}
$$

It is admitted at that state exactly when $k+a(t)\in J_b$ for every
$t$. Thus the common input is the pair of relative increments, or its
prescribed velocities, and not an absolute path that assumes knowledge
of $k$. The same numerical functions $a,b$ are used at every starting
state. Formula (9.2) specifies a family of Definition 3.1 histories;
it asserts no additional actuator, feedback measurement, reset or
uniform resource bound. Its endpoint phase increment is denoted

$$
H_\gamma(k)=\int_0^T w(k+a(t))\,db(t).
\tag{9.3}
$$

All integrals here are ordinary integrals against an absolutely
continuous integrator, including the piecewise $C^1$ case. The
bounded-variation signature used below describes these paths; it does
not enlarge Definition 3.1 to all bounded-variation controls.

**Theorem 9.2 (Exact partial operation, concatenation and reversal).**
The lawful starting-height domain and the induced current-ray map are

$$
D_\gamma=(\ell_b-m_\gamma,\ u_b-M_\gamma),\qquad
T_\gamma(k,[h])=(k+A_\gamma,[h+H_\gamma(k)]),
\tag{9.4}
$$

where an interval with its left endpoint at least its right endpoint
is empty. The source domain is $D_\gamma\times(U_b/\Lambda_b)$.
It is nonempty exactly when $M_\gamma-m_\gamma<W_b$, and it is all
of $\mathcal M_b$ exactly when $a$ is identically zero. A compact
promised interval $[l,u]\subset J_b$ is lawful for every starting
phase exactly when

$$
l+m_\gamma>\ell_b,\qquad u+M_\gamma<u_b.
\tag{9.5}
$$

For an open promised interval $(l,u)\subset J_b$ the corresponding
necessary and sufficient inequalities are non-strict. Endpoint
membership alone, $k,k+A_\gamma\in J_b$, is in general weaker than
lawfulness of the command.

Run $\gamma$ first, then $\delta$, translating the second increment
path by $(A_\gamma,B_\gamma)$ to concatenate them. Write this ordered
path as $\gamma*\delta$. Then

$$
\begin{aligned}
D_{\gamma*\delta}&=D_\gamma\cap(D_\delta-A_\gamma),\\
H_{\gamma*\delta}(k)&=H_\gamma(k)+H_\delta(k+A_\gamma),\\
T_{\gamma*\delta}&=T_\delta\circ T_\gamma
\quad\hbox{on precisely this domain}.
\end{aligned}
\tag{9.6}
$$

Let $\bar\gamma(t)=(a(T-t)-A_\gamma,b(T-t)-B_\gamma)$.
The reversed command has

$$
D_{\bar\gamma}=D_\gamma+A_\gamma,\qquad
H_{\bar\gamma}(k)=-H_\gamma(k-A_\gamma),\qquad
T_{\bar\gamma}=T_\gamma^{-1}.
\tag{9.7}
$$

The maps are smooth bijections between their indicated open source
and image domains. The same formulas hold on the real lift
$J_b\times U_b$, before reducing phase increments modulo $\Lambda_b$.

Proof. Since the extrema are attained, positivity along the whole path
is equivalent to $k+m_\gamma>\ell_b$ and
$k+M_\gamma<u_b$. Also $m_\gamma\le0\le M_\gamma$, because the path
starts at zero. This proves all the interval assertions, including
containment in $J_b$, the nonempty-domain criterion and (9.5).
To contain every point of $J_b$ requires $m_\gamma=0=M_\gamma$;
these extrema force $a\equiv0$. On an open promised interval equality
at either excluded endpoint is allowed, which proves the non-strict
version.

For any admitted $k$, continuity keeps $k+a(t)$ in a compact positive
subinterval. Consequently (9.3) exists and (9.2) obeys the original ODE
almost everywhere, with the original initial state. Its phase derivative
is exactly $w\dot\chi$, and its probability derivative is $d\dot\kappa$.
Since $w\in U_b$ and $d^{\mathsf T}w=1$,

$$
H_\gamma(k)\in U_b,\qquad d^{\mathsf T}H_\gamma(k)=B_\gamma.
\tag{9.8}
$$

Changing a phase representative by $\Lambda_b$ changes its endpoint
by the same lattice vector. Changing $\chi_*$ by a real lift period
does not change $db$ or the endpoint ray. Thus (9.4) is a well-defined
map of the actual rays with arbitrary fixed preparation phases.
Differentiation of (9.3) in $k$ is valid locally to every order: all
relevant derivatives of $w$ are bounded on a common compact positive
interval and the integrator has finite variation. This gives smoothness.

The second path has starting height $k+A_\gamma$, so its additional
lawfulness condition is exactly the intersection in (9.6). Splitting
the phase integral at the join proves its addition law. Equivalently,
its excursions are

$$
m_{\gamma*\delta}=\min(m_\gamma,A_\gamma+m_\delta),\qquad
M_{\gamma*\delta}=\max(M_\gamma,A_\gamma+M_\delta).
\tag{9.9}
$$

Reversal has extrema $m_\gamma-A_\gamma,M_\gamma-A_\gamma$ and
negates the phase integral after shifting the starting height. This
proves (9.7). Its domain is exactly the image-height interval of
$T_\gamma$, so it proves the smooth inverse assertion too. The
concatenation with the reverse is the identity on $D_\gamma$, which
can be a proper subset of $J_b$; it is not an identity command lawful
on the whole fiber. $\square$

### 9.2 Ordered effects on the double wall

**Theorem 9.3 (The chronological summary acts on the original source).**
Assume $X=Y=r/2$. For the actual command in Definition 9.1 put

$$
K_\gamma=\int a\,db,\qquad
\Omega_\gamma=\frac12\int(a\,db-b\,da)
                  =K_\gamma-\frac12A_\gamma B_\gamma.
\tag{9.10}
$$

The order convention is that the earlier coordinate is integrated
first: the signature word $ab$ is
$\int_{s<t}da(s)\,db(t)=K_\gamma$. On the double-wall real lift
$(k,u,v)$ of (8.17), the exact endpoint formula is

$$
T_\gamma(k,u,v)=\left(
 k+A_\gamma,
 u+\frac{B_\gamma}{2}-\frac{kB_\gamma+K_\gamma}{r},
 v-\frac{kB_\gamma+K_\gamma}{r}\right).
\tag{9.11}
$$

Its domain remains (9.4). In particular the signed physical control
integral is $\int\kappa\,d\chi=kB_\gamma+K_\gamma$, not just
$K_\gamma$. The source correspondence uses increments from the
unknown current height, not a substitution of an absolute path for
a common command.

The existing step-two chronological multiplication, in these coordinates,
is

$$
(A,B,K)\star(A',B',K')
 =(A+A',B+B',K+K'+AB'),
\qquad
(A,B,K)^{-1}=(-A,-B,AB-K).
\tag{9.12}
$$

The matrix representative is
$\left(\begin{smallmatrix}1&A&K\\0&1&B\\0&0&1\end{smallmatrix}\right)$.
Thus (9.11) gives a right action of this real Heisenberg group on the
unrestricted real coordinate space: first the unprimed command, then
the primed one. On the positive source it gives only the partial
operations whose actual excursions are lawful. On ray coordinates
$u,v\bmod2\pi$, two such formulas agree on any common nonempty open
height interval, for all phases, exactly when

$$
A=A',\qquad B=B',\qquad K-K'\in2\pi r\mathbb Z.
\tag{9.13}
$$

On real lifts equality requires $K=K'$. Equality of formulas in
(9.13) does not assert equality of lawful domains.

For any compact promised interval $[l,u]\subset(0,r/2)$, a given real
triple $(A,B,K)$ has a representing command lawful on every promised
state if and only if $[l+A,u+A]\subset(0,r/2)$. Hence a triple has
some nonempty lawful source domain if and only if $|A|<r/2$.
The assertion permits finite but arbitrarily large phase variation;
it is not a bound on execution cost. On the entire positive fiber
one fixed lawful command must have $a\equiv0$, so it necessarily has
$A=K=0$.

Proof. Theorem 3.7 supplies the actual coefficients
$w_+=1/2-k/r$ and $w_-=-k/r$. Substitute $k+a(t)$ and integrate
against $db(t)$ to obtain (9.11); the state convention remains
$\psi_s=\sqrt{p_s}e^{-i(\eta_s+h_s)}$. In particular the original
$02$ output phase increases by the increment of $u$, with precisely
the sign in (8.8).

For provenance of the chronological operation, use
[History records, Theorem 161.5](AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md)
with its coordinate path $(x,y)=(a,b)$ and its signed area
$A(q)=\Omega_\gamma$. Its earlier-later cross term is
$(AB'-BA')/2$. The change of central coordinate
$K=\Omega+AB/2$ gives (9.12). This is the same degree-two Chen
supplier described by Chevyrev and Kormilitzin,
[*A Primer on the Signature Method in Machine Learning*, §1.3.3](https://arxiv.org/html/1603.03788v2).
Here its paths are the piecewise $C^1$ or absolutely continuous paths
already admitted by Definition 3.1, and their permission to concatenate
comes from (9.6). No general chronological identity supplies that domain.

One can also check the correspondence directly: splitting $\int a\,db$
at the join gives $K+K'+AB'$. In (9.11) the second command sees
$k+A$, so its extra central term is exactly $AB'$. Integration by
parts gives $\int a\,db+\int b\,da=AB$, proving (9.10) and the
inverse in (9.12). These calculations fix both chronological order
and area normalization.

Equality of endpoint maps first forces $A=A'$ by their probability
coordinate. On real lifts the difference between the two phase
increments is $(B-B')/2$, so equality then forces $B=B'$ and $K=K'$.
On rays, the increment difference of the $v$ coordinates is
$-\{k(B-B')+(K-K')\}/r$. If it takes values in $2\pi\mathbb Z$
on an open height interval, continuity makes it constant and its slope
forces $B=B'$. Its remaining constant is a period exactly under
(9.13); the $u$ condition then agrees. This proves the stated kernel
without confusing equality at one height with equality on a source
domain. Formula (9.11) exists algebraically for every real $k$;
positive probabilities and lawful intermediate paths still require (9.4).

For promised-domain realization, necessity follows from the final
height. Conversely choose a nonzero $s$ small enough that
$[l+s,u+s]\subset(0,r/2)$. Execute the rectangle with increment
vertices

$$
(0,0),\ (s,0),\ (s,q),\ (0,q),\ (0,0),
\qquad q=\frac{K-AB}{s},
\tag{9.14}
$$

then a pure probability leg to $a=A$, then a phase leg to $b=B$.
The rectangle has $K=sq$, the last two legs contribute $AB$, and
both pieces have the required endpoints. All rectangle heights are
lawful on the promise by convexity, as is the probability leg between
$k$ and $k+A$. The finite number $q$ is allowed by Definition 3.1.
This realizes the exact triple, with no limiting bracket construction.
There is a compact interval of starting heights with both endpoints
interior exactly when $|A|<r/2$. The full-domain assertion follows from
Theorem 9.2. $\square$

**Proposition 9.4 (Endpoint, signature and excursion information).**
For the commands of Definition 9.1 the following distinctions hold.
On the double wall, $(A,B,K,m,M)$ determines the entire lawful partial
endpoint operation on real lifts; on rays $K$ may be reduced as in
(9.13). The pair $(A,B)$ alone does not determine that operation even
when the lawful domains agree. The complete ordered signature
without $m,M$ does not determine the lawful domain, even though it
determines endpoint effects at every starting state at which both
compared commands are lawful. These latter two assertions concerning
complete signatures hold in all four mean regimes.

Proof. The first statement is exactly (9.4) and (9.11). To separate
endpoint increments from order, compare the two paths

$$
(0,0)\to(s,0)\to(s,t),\qquad
(0,0)\to(0,t)\to(s,t),\qquad 0<s<r/2.
\tag{9.15}
$$

Both have $(A,B)=(s,t)$, $m=0$, $M=s$, and the same nonempty lawful
domain $(0,r/2-s)$. Their $K$ values are $st$ and zero, respectively.
Their real endpoint phase difference is $-st/r$ in each of $u,v$.
Choose $st\notin2\pi r\mathbb Z$ for distinct rays and hence distinct
original coherence outputs, by Theorem 8.4. The signs agree with the
positive-$s$, positive-$t$ rectangle in (8.25).

For the complete-signature statement, define $S_{i_1\cdots i_n}$ to
be the integral of $dc_{i_1}(t_1)\cdots dc_{i_n}(t_n)$ over
$t_1<\cdots<t_n$, where $(c_a,c_b)=(a,b)$. This is the usual
bounded-variation signature, with the earlier-later convention of
Theorem 9.3; only the admitted absolutely continuous paths are used.
Suppose two such commands have equal complete signatures and are both
lawful at $k$. Their $A,B$ agree at degree one. Repeated integration
of $da$ gives

$$
\int a^n\,db=n!S_{\underbrace{a\cdots a}_{n}b},
\qquad n\ge0.
\tag{9.16}
$$

Indeed the iterated integral of $n$ copies of $da$ up to time $t$ is
$a(t)^n/n!$, by induction using the derivative of $a^n$.
Thus both paths give the same integral of every polynomial in $a$
against $db$. Their combined $a$ ranges lie in one compact interval
inside $J_b-k$. Each function $x\mapsto w_s(k+x)$ is continuous there.
Polynomial uniform approximation, followed by the estimate

$$
\left|\int(f-P)(a)\,db\right|
 \le \|f-P\|_\infty\operatorname{Var}(b),
\tag{9.17}
$$

proves equality of their $H_\gamma(k)$, component by component.
This supplies the source-specific endpoint implication directly from
the signature coordinates; it does not require a path reconstruction
or a convergence assertion about a Taylor series for $w$.

To see the missing domain information, take the constant command and
the command with $b\equiv0$ and probability excursion
$0\to s\to0$, where $0<s<W_b$. Every signature word containing
$b$ vanishes. Every remaining nonempty word has value $A^n/n!=0$.
Both commands therefore have the identity complete signature and the
identity endpoint formula. But their domains are respectively
$J_b$ and $(\ell_b,u_b-s)$. Choose a starting height in
$(u_b-s,u_b)$ to distinguish lawfulness, and one in
$(\ell_b,u_b-s)$ to see that the excursion is an actual lawful history
on a nonempty source domain. Their extrema distinguish the two domains
exactly. This is a direct instance of the tree-like cancellation in
Hambly and Lyons,
[*Uniqueness for the signature of a path of bounded variation and the reduced path group*](https://arxiv.org/abs/math/0507536);
that supplier does not preserve an external positivity guard under
removal of a retraced excursion.

Together with (9.4), equality of complete signatures and equality of
$m,M$ therefore imply equality of lawful partial endpoint operations
in every regime. Neither assertion reconstructs a parametrized history.
Away from the double wall, the failure of signed area to specify even
the real zero-winding phase endpoint is already exactly Theorem 3.5,
with the explicit generic ray witness in Proposition 3.6; those results
are retained with their original fixed starting height. $\square$

### 9.3 The real Lie algebra of the actual native fields

**Theorem 9.5 (Repeated-bracket classification for every allowed mean).**
On $\mathcal M_b$ let $h_a$ be the increment coordinate of pole group
$a$ from Theorem 3.2. The vector fields of the two original velocity
inputs and their successive brackets are

$$
P=\partial_k,\qquad
Q_n=\sum_{a=1}^g w_a^{(n)}(k)\partial_{h_a}\quad(n\ge0),
\qquad Q=Q_0.
\tag{9.18}
$$

Their generated real Lie algebra, meaning finite real linear
combinations of vector fields and their brackets, is exactly

$$
\mathfrak l_b=\mathbb RP+\operatorname{span}_{\mathbb R}
                   \{Q_n:n\ge0\},\qquad
[P,Q_n]=Q_{n+1},\quad[Q_n,Q_j]=0.
\tag{9.19}
$$

Its complete classification is

| Fixed mean regime | Real vector-field Lie algebra | Pointwise tangent rank |
| --- | --- | --- |
| Neither wall | Countably infinite dimensional; $P,Q_0,Q_1,\ldots$ independent | $5$ |
| $E_-$ only | Countably infinite dimensional; the same basis | $4$ |
| $E_+$ only | Countably infinite dimensional; the same basis | $4$ |
| Both walls | Three dimensional, with basis $P,Q_0,Q_1$ and $[P,Q_0]=Q_1$ central | $3$ |

There are no further exceptional allowed values of $X,Y,Z$ in this
classification. It concerns real constant coefficients, not a module
allowing arbitrary coefficient functions. The three-dimensional case
is the Heisenberg algebra realized by (9.11), not the rotation algebra.
None of the ranks or algebra dimensions asserts globally available
flows on the full positive source.

Proof. Vertical coefficients depend only on $k$, so vertical fields
commute and bracketing with $P$ differentiates their coefficients.
Thus the right side of (9.19) is a Lie algebra containing $P,Q$ and
every listed field is an iterated bracket. This proves the equality.
To determine its dimension, let the distinct poles be $\lambda_a$,
with signed multiplicities $c_a=m_a\varepsilon_a$ as in §3.3. Put

$$
F(k)=\prod_{a=1}^g(k-\lambda_a),\qquad
N(k)=\sum_{a=1}^g c_a\prod_{j\ne a}(k-\lambda_j).
\tag{9.20}
$$

The original positive information coefficient and grouped weight are

$$
I(k)=\sum_a\frac{c_a}{k-\lambda_a}=\frac{N(k)}{F(k)},\qquad
w_a(k)=\frac{\prod_{j\ne a}(k-\lambda_j)}{N(k)}.
\tag{9.21}
$$

This is a formula for one coordinate per pole group, not a sum of
its equal components. The four signed modes give

$$
\sum_a c_a=0,\qquad
\sum_a c_a\lambda_a=(X+Y-r)-X-Y=-r\ne0.
\tag{9.22}
$$

Hence $N$ has degree exactly $g-2$, with leading coefficient $-r$.
Furthermore

$$
N(\lambda_a)=c_a\prod_{j\ne a}(\lambda_a-\lambda_j)\ne0.
\tag{9.23}
$$

Thus none of its roots can cancel a numerator in (9.21). The positivity
of $I$ excludes roots in $J_b$. If $g>2$, $N$ is nonconstant and has
a complex root, so every $w_a$ has a genuine pole. At a pole of order
$q\ge1$, its $n$th derivative has pole order $q+n$ with nonzero leading
coefficient. In a finite constant linear relation among
$w_a,w_a',\ldots,w_a^{(n)}$, the largest derivative has the unique
highest pole order and cannot cancel. A relation holding on the real
interval would be a rational-function identity after clearing
denominators, so this complex-pole argument applies. Therefore all
$Q_n$ are linearly independent over $\mathbb R$ when $g>2$.
The $\partial_k$ component then makes $P$ independent as well.

The possible pole exceptions can also be enumerated explicitly.
Before grouping, the numerator over the four mode factors is

$$
N_4(k)=-rk^2+2XYk+XY(r-X-Y),\qquad
\operatorname{disc}(N_4)=4XY(r-X)(r-Y)>0.
\tag{9.24}
$$

In the neither-wall regime its two distinct roots are
$(XY\pm\sqrt{XY(r-X)(r-Y)})/r$, and (9.23) rules out any cancellation.
On $E_-$ only the duplicated factor is $k$, and grouping gives
$N(k)=-rk+2XY$. On $E_+$ only, writing $X=Y=x$, the duplicated
factor is $k-x$, and grouping gives
$N(k)=-rk+x(2x-r)$. Each is genuinely linear, and (9.23) still
excludes cancellations. On both walls the grouped numerator is the
nonzero constant $-r$. These cases exhaust the allowed same-sign
collisions; opposite-sign collisions are excluded by the strict
mean inequalities of Definition 2.1. In particular neither a choice
of the positive middle mass nor a special interior height introduces
an extra finite-dimensional case.

When $g=2$, Theorem 3.7 gives affine $w$, so $Q_n=0$ for $n\ge2$.
The determinant of $Q_0,Q_1$ in $(u,v)$ is $-1/(2r)\ne0$.
Thus $P,Q_0,Q_1$ are a basis, with the central bracket asserted.
Theorem 9.3 supplies its actual chronological representation and
lawful histories. Its nonzero center and vanishing further brackets
also distinguish it from $\mathfrak{so}(3)$.

For pointwise rank in every regime, set $f_a(k)=1/(k-\lambda_a)$.
At a fixed interior $k$, the matrix with columns $f^{(n)}(k)$,
$0\le n<g$, has entries

$$
f_a^{(n)}(k)=(-1)^n n!\,(k-\lambda_a)^{-n-1}.
\tag{9.25}
$$

Its determinant is nonzero: factor $1/(k-\lambda_a)$ from each row
and $(-1)^n n!$ from column $n$, leaving the Vandermonde matrix in
the distinct numbers $1/(k-\lambda_a)$. Multiplication by the
nonzero scalar function $1/I$ changes this derivative-column matrix
by a triangular column transformation with diagonal $1/I$.
Consequently $w,w',\ldots,w^{(g-1)}$ also have independent values
at every $k$. These supply all $g$ vertical tangent directions;
$P$ adds the remaining one. This proves the stated ranks without
identifying tangent rank with the dimension of the vector-field algebra.

The phase flow of $Q$ is lawful for all finite times because it fixes
$k$. The probability flow of $P$ is lawful only while $k+t\in J_b$.
Even the central double-wall endpoint flow, though defined everywhere
as a phase formula, requires an excursion for a nontrivial command
of that central type. By Theorem 9.2 no such excursion command is
lawful on the whole unknown-height fiber. Global flow existence as a
mathematical vector field therefore does not remove the command-domain
restriction. $\square$

### 9.4 Nonlinear prediction and a shared affine encoder

**Definition 9.6 (Future-output factorization on a common domain).**
Fix a nonempty open interval $I\subset J_b$ and use the same realized
source

$$
\mathcal D=I\times(U_b/\Lambda_b).
\tag{9.26}
$$

It is a subset of the reachable domain in Theorem 8.2, with the same
fixed preparation phases. A command is common legal on $\mathcal D$
when $I\subset D_\gamma$. Its future response is the original
$10$-component vector $y(T_\gamma x)$ from (8.8). A shared fixed affine
factorization of dimension $n<\infty$ would consist of one function
$z:\mathcal D\to\mathbb R^n$ and, for each such command, constants
$c_\gamma\in\mathbb R^{10}$ and
$L_\gamma:\mathbb R^n\to\mathbb R^{10}$ satisfying

$$
y(T_\gamma x)=c_\gamma+L_\gamma z(x)
\quad\text{for every }x\in\mathcal D
\text{ and every common legal }\gamma.
\tag{9.27}
$$

The encoder is arbitrary: no linearity, continuity, measurability,
injectivity or computability is assumed. The decoder and offset may
depend on the continuation, fixed means and fixed preparation, but
not on the hidden current state or its producing history. Common
legal commands need not return into $\mathcal D$ for this terminal
query. The phase-only subfamily used below does preserve $\mathcal D$,
so the same lower bound applies if that preservation is required.
A finite sequence is a command by concatenation on its actual domain.
The all-future fixed affine capacity is the least such $n$, or
$+\infty$ if no finite $n$ exists.

**Theorem 9.7 (Exact nonlinear predictive state on the same rays).**
Under the relative command convention, the current ray determines
lawfulness and all future original outputs. Two actual prefixes with
the same current ray admit exactly the same commands and give the
same future outputs under each one. Conversely, equality of future
outputs for all common legal commands, including the constant command,
forces equality of their current rays. Thus the future observational
quotient is exactly $\mathcal M_b$, of intrinsic dimension $g+1$.
It has the global finite real state representation

$$
E(k,[h])=(k,(\cos h_a,\sin h_a)_{a=1}^g)\in\mathbb R^{1+2g},
\tag{9.28}
$$

with nonlinear updates given by (9.4). The ten current outputs are
another sufficient finite representation by Theorem 8.4. On the double
wall the four real coordinates $z=(z_a,z_b)$ of (8.18) are already
sufficient, with the following exact update for a command of summary
$(A,B,K)$ on its lawful domain:

$$
\begin{aligned}
k&=\frac{\|z_b\|^2}{4Z},\\
z_a'&=
\sqrt{\frac{(k+A)(r/2-k-A)}{k(r/2-k)}}\,
 R_{B/2}z_a,\\
z_b'&=\sqrt{\frac{k+A}{k}}\,
 R_{B/2-(kB+K)/r}z_b.
\end{aligned}
\tag{9.29}
$$

These states do not reconstruct real phase lifts, integer winding or
past path lawfulness from their endpoints.

Proof. The command domain depends only on $k$, which is part of the
current ray. Its phase integral (9.3) depends only on that height and
the command, not on any previous history or chosen real phase
representative. Therefore (9.4) yields identical rays and outputs
from identical current rays. This also applies after every lawful
concatenation by (9.6). The constant command is lawful everywhere;
Theorem 8.4 then proves the converse from the unchanged current
outputs. It also supplies the smooth inverse needed for the
output-state representation, and Theorem 8.2 supplies the intrinsic
dimension. Formula (9.28) records precisely $k$ and all grouped phase
classes, so is globally injective and updates each circle by the
rotation through $H_{\gamma,a}(k)$.

For (9.29), (9.11) gives
$\alpha'=\alpha+B/2$ and
$\beta'=\beta+B/2-(kB+K)/r$. Substitute $k'=k+A$ and these angles
into (8.18). All square roots and denominators are positive on the
lawful domain. The fixed preparation phases are contained in the
original decoder $O D_0$ of (8.19); none are set to zero by the update.
The real representation has the same curved three-dimensional image
(8.20), so its four coordinates do not assert intrinsic dimension four.

For the last assertion, the prefixes of Proposition 8.3 with identical
current rays and different lifted winding remain examples here.
Appending the same command adds $B_\gamma$ to both relation lifts;
it does not erase their difference. If winding is queried, the actual
real lift is additional data. Likewise (9.4) predicts future
lawfulness conditional on an actual current source state; it does
not certify a proposed past path. $\square$

**Theorem 9.8 (No finite shared affine encoder for all future outputs).**
For every mean satisfying Definition 2.1, every fixed preparation
phase vector, and every nonempty open interval $I\subset J_b$, there
is no finite $n$ and no factorization (9.27). Nonexistence holds even
when the continuation menu consists only of the universally lawful
phase commands

$$
\gamma_t(s)=(0,ts),\qquad 0\le s\le1,\quad t\in\mathbb R.
\tag{9.30}
$$

More precisely, for any $N$ distinct real values $t_1,\ldots,t_N$,
the constant function and the $2N$ real future $02$ output functions
for these commands are linearly independent on $\mathcal D$.
Thus any shared affine encoder for just these $N$ future pairs
already requires $n\ge2N$. No regularity of the encoder is required.

Proof. The $02$ character is the increment of the pole group containing
mode $0$, since $h_2=0$. For (9.30) the complex number whose real and
imaginary parts are the two original doubled outputs is exactly

$$
Y_t(k,h)=2\sqrt{Zp_0(k)}\,
 e^{i(\delta_{02}^0+h_0)}e^{itw_0(k)}.
\tag{9.31}
$$

This uses the original negative state-phase convention:
$\overline\psi_0\psi_2$ has positive phase
$\delta_{02}^0+h_0+tw_0(k)$. The command fixes every current probability,
is lawful for all of $J_b$ and every real $t$, and preserves
$\mathcal D$ exactly. It is one original phase leg, with variation
$|t|$; it assumes neither unknown-state feedback nor a new operation.

The grouped expression (9.21) proves that $w_0$ is nonconstant on
every nonempty open interval. Its numerator has degree $g-1$ and its
denominator degree $g-2$, with nonzero leading coefficient $-r$.
They have no common root by (9.23). A constant equality on an interval
would imply a polynomial identity between these unequal degrees.
This argument includes both individual walls and $g=2$, where
$w_0=1/2-k/r$. The function is real analytic on $J_b$; hence every
nonempty open interval contains a smaller one on which $w_0'$ is
nonzero and $w_0$ ranges over an open real interval.

Suppose real constants $c,a_j,b_j$ satisfy

$$
c+\sum_{j=1}^N\{a_j\operatorname{Re}Y_{t_j}
                   +b_j\operatorname{Im}Y_{t_j}\}=0
\quad\text{on }\mathcal D.
\tag{9.32}
$$

At a fixed $k$, vary the phase coordinate $h_0$ over its full circle,
which is independent in $U_b/\Lambda_b$ even when mode $0$ belongs
to a multiple-mode group. The zeroth Fourier coefficient gives $c=0$.
The first Fourier coefficient, after dividing by the nonzero factor
$2\sqrt{Zp_0(k)}e^{i\delta_{02}^0}$, gives

$$
\sum_{j=1}^N(a_j-i b_j)e^{it_jw_0(k)}=0.
\tag{9.33}
$$

On a smaller interval set $x=w_0(k)$. Differentiating this identity
with respect to $x$ through orders $0,\ldots,N-1$ at any point $x_*$
gives the matrix $((it_j)^q e^{it_jx_*})_{q,j}$. Its determinant is

$$
\left(\prod_j e^{it_jx_*}\right)
 i^{N(N-1)/2}\prod_{j<l}(t_l-t_j)\ne0.
\tag{9.34}
$$

Thus $a_j-i b_j=0$ for every $j$, proving the claimed real independence
and including the constant. Arbitrary preparation only multiplies
(9.33) by a fixed unit complex factor, so cannot change this conclusion.
This proof works for any finite set of distinct $t_j$, even chosen
inside one bounded open interval of phase increments.

If (9.27) held, all scalar future outputs and the constant would lie
in the real vector space of functions
$\operatorname{span}_{\mathbb R}\{1,z_1,\ldots,z_n\}$, of dimension
at most $n+1$. The independence just proved shows that these $N$ commands
already require dimension at least $2N+1$. Therefore $n\ge2N$ for
every $N$, an impossibility for finite $n$. This is a statement about
functions on the same realized domain, so arbitrary nonlinear or
discontinuous encoders and all continuation-dependent fixed offsets
are still in scope.

The observable-span viewpoint is the classical supplier, as in
Brunton, Brunton, Proctor and Kutz,
[*Koopman invariant subspaces and finite linear representations of nonlinear dynamical systems for control*, §2](https://arxiv.org/html/1510.03007v2),
and [Observer closure, §7](OBSERVER_CLOSURE_SPECTRUM.md).
Here the pullbacks are $f\mapsto f\circ T_{\gamma_t}$, the same source
is (9.26), and the measured functions are the original pair (9.31).
The general viewpoint alone does not supply the nonconstant native
frequency, universal lawfulness, or the arbitrary-encoder obstruction;
those are established above. No linear state-update assumption was
used, so requiring fixed affine updates as well cannot evade the
lower bound. $\square$

### 9.5 The conditional three-dimensional state and the interface boundary

**Corollary 9.9 (Distinct dimensions and retained restrictions).**
Under Definitions 8.1 and 9.1, the double wall has a three-dimensional
nonlinear sufficient current-ray state and a three-dimensional real
native Lie algebra, but infinite all-future fixed affine capacity on
every domain (9.26). Off that wall the native real Lie algebra is
infinite dimensional even though the current-ray state remains finite
dimensional. Neither conclusion changes the current capacities
$10,6,4$ of Theorem 8.6, the closed-loop fixed-base capacities $6,4,3$
of Theorem 4.2, or the zero-winding double-wall value $2$ of
Proposition 4.3. Nor does it give a mean-selection law or a realization
of physical spatial axes.

Proof. Combine Theorems 9.5, 9.7 and 9.8 on their stated domains.
For the current-output task only the constant continuation is queried;
Theorem 8.6 therefore retains its finite factorization. In Theorem 9.8
the starting height ranges over an open interval even though each
witness continuation individually fixes that height. This differs
from a task whose starting probability is fixed once and for all.
At a single height the frequency $w_0(k)$ in (9.31) is constant,
and its future pair lies in the span of the current sine and cosine.
Thus the unbounded-span proof makes no assertion contradicting a
fixed-probability endpoint capacity or closure.

The original loop conditions further fix the terminal height and
require an integral relation-phase winding; they define the smaller
phase domains of Theorem 3.3. On the double wall a command that is
itself a loop based at its current starting height has $A=0$ and
$B=2\pi m$, with real phase integral $kB+K$. At the preparation
height, substitution into (9.11) recovers exactly Theorem 3.7, including
its parity and negative phase convention. For a preceding prefix with
real relation increment $L_*$, the total increment instead is
$L_*+B$; the command winding does not replace that history record.
Actual zero winding still means the relevant real increment is zero,
not merely an endpoint phase class. The finite capacities for the
original restricted tasks are therefore preserved.

The same-source requirement in the
[observer interface, Hypothesis 10.1 and Theorem 10.2](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)
includes a common linear realization, calibrated distance and all
generator closure. The
[harmonic interface, Definitions 9.1 and 12.1](FIB_LEGAL_EDGE_LOAD_SECOND_ORDER_LOSS_LOCALIZATION_AND_LOCAL_TILT_AVERAGING_OBSTRUCTION.md)
requires rotational intertwining and a shared linear response source,
respectively. Theorem 9.8 excludes any finite realization of (9.27)
for the present complete future menu, even with an arbitrary encoder;
it does not negate those conditional interface theorems for their
other declared tasks. The Heisenberg algebra and the partial action
in Theorems 9.3 and 9.5 supply no free $SO(3)$ or $SU(2)$ rotations.
Definition 3.1 keeps the means fixed and contains no rule selecting
$X=Y=r/2$. A physical actuator realizing the relative commands, a
method of acquiring exact expectations, a finite-memory or finite-bit
implementation, and a mapping to spatial axes are additional bridges,
not consequences of these source equations.

The source-specific conclusions here concern the lawful family (9.2),
its exact chronological action, the grouped-pole Lie classification,
and the independent future responses (9.31). They consume the
reachability and current observation results of §§3 and 8, and the
classical chronological and observable-span suppliers at their cited
entries; they assert no worldwide priority for those suppliers or for
these ordinary mathematical deductions. $\square$

## 9.99 追加锚

## 10. Native operational geometry and the second-order bridge

### 10.1 The local native contract

**Definition 10.1 (Native fields, interior domains and added costs).** Fix
precisely Definition 8.1: one full-support fixed-mean source, one preparation
with arbitrary fixed phases, and the two controls of Definition 3.1. Put
$g=4-\mathbf1_{E_-}-\mathbf1_{E_+}$ and use grouped increments $h_a$ on
$\mathcal M_b=J_b\times(U_b/\Lambda_b)$, not a fixed-height slice. The
actual representatives remain (8.5), with its negative phase convention.
The original velocity fields are

$$
P=\partial_\kappa,\qquad
Q=\sum_{a=1}^{g}w_a(\kappa)\partial_{h_a},\qquad
w_a(\kappa)=\frac1{I(\kappa)(\kappa-\lambda_a)}.
\tag{10.1}
$$

Here the distinct grouped poles and $I$ are those of §§3.2 and 9.3; group
multiplicities remain in $I$. A horizontal curve is absolutely continuous
with $\dot q=v^1P+v^2Q$, $v\in L^1$. A relative command $\gamma=(a,b)$
starts at zero and has $v^1=\dot a$, $v^2=\dot b$. Its full path guard is

$$
\kappa(t)=k+a(t)\in J_b\quad\hbox{for every }t.
\tag{10.2}
$$

Choose an open connected $\Omega\Subset\mathcal M_b$, and smooth symmetric
positive definite $A(q)=(a^{ij}(q))$ on a neighbourhood of its closure.
Declare the horizontal energy and length

$$
\mathsf E_A(\gamma)=\int_0^T v^{\mathsf T}A(q)^{-1}v\,dt,
\qquad
\mathsf L_A(\gamma)=\int_0^T\sqrt{v^{\mathsf T}A(q)^{-1}v}\,dt.
\tag{10.3}
$$

Energy may be infinite. The distance $d_A^\Omega$ is the infimum of lengths
of horizontal curves in $\Omega$ joining the specified states. A density,
when used, is separately chosen as $d\mu=\rho(\kappa,h)d\kappa\,dh$, with
$\rho$ smooth and strictly positive near $\overline\Omega$; grouped phases
have period $2\pi$. Neither structure is supplied by the finite alphabet.
The original phase variation is

$$
\mathsf V_\chi(\gamma)=\int_0^T|v^2|\,dt.
\tag{10.4}
$$

For a compact height promise $[l,u]\subset J_b$, the exact common-command
conditions, independent of the initial phases, are

$$
l+m_\gamma>\kappa_-,\qquad u+M_\gamma<\kappa_+.
\tag{10.5}
$$

For an open promise the corresponding inequalities are non-strict. The
command domain is still $D_\gamma$ in (9.4), and its phase increment is
$H_\gamma(k)$ in (9.3). An additional requirement to stay in $\Omega$ is a
restriction of this lawful family, not a replacement for its positivity guard.

**Proposition 10.2 (Command correspondence, chart bounds and cost).** Every
horizontal curve in this contract is an original history from its starting
ray, and conversely every Definition 3.1 history in $\Omega$ is such a curve.
The same prescribed controls give an original-source lawful family on a
height promise exactly under (10.5). Concatenation and reversal retain (9.6)--(9.7), with
their translated domains.

Choose $q_0=(k_0,[h_0])$, a box
$|\kappa-k_0|<\delta$, $|h-h_0|_\infty<\eta<\pi$ whose closure lies in
$\Omega$, and constants $0<\lambda\le\Lambda$ with
$\lambda I_2\le A\le\Lambda I_2$ there. Put
$M=\max_{|k-k_0|\le\delta}|w(k)|_\infty$. Every initial path segment in
this box satisfies

$$
|\kappa-k_0|\le\sqrt\Lambda\,\mathsf L_A,
\quad |h-h_0|_\infty\le M\sqrt\Lambda\,\mathsf L_A,
\quad \mathsf V_\chi\le\sqrt\Lambda\,\mathsf L_A,
\quad \mathsf L_A^2\le T\mathsf E_A.
\tag{10.5a}
$$

Consequently a curve from $q_0$ of length less than
$\min(\delta,\eta/M)/\sqrt\Lambda$ cannot first exit this box. This is
an explicit positive-probability and phase-chart bound for local metric use.

For loops to which Theorem 3.11 applies, with all bottom masses at least
$\varepsilon>0$ and $A\le\Lambda I_2$ along the whole path, its cost bounds give

$$
\mathsf L_A\ge
\frac{16\varepsilon^2}{r\sqrt\Lambda}
\frac{|h_1-h_3|}{|X-Y|},\qquad
\mathsf L_A\ge
\frac{16\varepsilon^2}{r\sqrt\Lambda}
\frac{|h_0-h_{13}|}{|X+Y-r|},
\tag{10.5b}
$$

Here $h_s$ denotes the loop's full five-mode increment, expanded from the
grouped coordinates. Each bound requires its denominator to be nonzero.
For phase-class targets replace the
numerator by its distance to $2\pi\mathbb Z$. On the exact wall the
corresponding increment difference vanishes; there is no division by zero.

**Proof.** In a continuous real phase lift, (10.1) gives
$\dot\kappa=v^1$, $\dot h=w(\kappa)v^2$. Integrating $v$ reconstructs
$a,b$ and gives exactly (9.2). Conversely differentiation of that original
history gives the displayed equation. Path lifting on a compact time
interval uses finitely many torus charts; it preserves absolute continuity.
The coefficient $Q$ never vanishes, and on a compact interior set its inverse
on its one-dimensional image is bounded, so the two control coefficients
are integrable. The identity $d^{\mathsf T}w=1$ also recovers the real
relation increment. Thus no extra phase velocity has been admitted.
Theorem 9.2 supplies precisely the extrema guard and composition rules.

Pointwise $|v|\le\sqrt\Lambda\sqrt{v^{\mathsf T}A^{-1}v}$ gives the
first three estimates by integration; Cauchy--Schwarz gives the fourth.
At a first box exit one of the first two inequalities contradicts the
strict length bound. Combining the third with Theorem 3.11 gives (10.5b),
including its real-lift and positive-margin restrictions. These comparisons
are consequences of the declared norm, not a physical calibration. A distance
between specified rays supplies neither unknown-height feedback nor phase
acquisition, reset, extra controls or a finite-shot readout. $\square$

### 10.2 Bracket growth, anisotropic balls and local volume

**Theorem 10.3 (Native privileged coordinates in every mean regime).** The
flag $\mathcal D^1=\operatorname{span}\{P,Q\}$,
$\mathcal D^{j+1}=\mathcal D^j+[\mathcal D^1,\mathcal D^j]$ has the following
constant growth on each fixed-mean manifold:

$$
\begin{array}{c|c|c|c|c}
\text{regime}&g&\text{growth}&\text{weights}&Q_{\rm vol}\\ \hline
 E_-^c\cap E_+^c&4&(2,3,4,5)&(1,1,2,3,4)&11\\
 E_-\cap E_+^c&3&(2,3,4)&(1,1,2,3)&7\\
 E_-^c\cap E_+&3&(2,3,4)&(1,1,2,3)&7\\
 E_-\cap E_+&2&(2,3)&(1,1,2)&4.
\end{array}
\tag{10.6}
$$

At $q_0=(k_0,[h_0])$ take real grouped phase differences and define

$$
W_{k_0}=\left(\frac{w^{(j)}(k_0)}{j!}\right)_{0\le j<g},\qquad
x=\kappa-k_0,\quad (z_0,\ldots,z_{g-1})^{\mathsf T}=W_{k_0}^{-1}(h-h_0).
\tag{10.6a}
$$

These are privileged coordinates with weights $1$ for $x$ and $j+1$ for
$z_j$. Write $\nu=(1,1,2,\ldots,g)$. For $q_0$ in any compact
$K\Subset\Omega$, there are uniform $c,C,s_0>0$ such that

$$
\{|(x,z)_i|<c s^{\nu_i}\}
\subset B_{d_A^\Omega}(q_0,s)
\subset\{|(x,z)_i|<C s^{\nu_i}\},\qquad 0<s<s_0,
\tag{10.7}
$$

and

$$
c s^{Q_{\rm vol}}\le\mu(B_{d_A^\Omega}(q_0,s))
\le C s^{Q_{\rm vol}},\qquad
Q_{\rm vol}=1+\frac{g(g+1)}2.
\tag{10.8}
$$

Equivalently $d_A^\Omega(q_0,q)\asymp
|x|+\sum_{j=0}^{g-1}|z_j|^{1/(j+1)}$ locally. The estimates are for fixed
means and compact interiors, with no uniformity across a wall or at a
probability endpoint.

**Proof.** Reuse Theorem 9.5: $[P,Q_n]=Q_{n+1}$ and $[Q_i,Q_j]=0$,
where $Q_n=w^{(n)}\cdot\partial_h$. Smooth-coefficient brackets add no
new directions beyond these, so
$\mathcal D^j=\operatorname{span}(P,Q_0,\ldots,Q_{j-1})$ until saturation.
The grouped-pole Vandermonde determinant (9.25) makes the first $g$
vertical vectors independent at every interior height. This gives (10.6)
and invertibility of $W_{k_0}$, with no further exceptional means or heights.

In (10.6a), Taylor's formula gives

$$
P=\partial_x,\qquad Q=\sum_{j=0}^{g-1}f_j(x)\partial_{z_j},\qquad
f_j(x)=x^j+O(x^g).
\tag{10.8a}
$$

Every word in $P,Q$ of length less than $j+1$ annihilates $z_j$ at the
origin; a word containing two $Q$'s, applied to $z_j$, vanishes identically,
since all coefficients depend only on $x$. But $P^jQz_j(0)=j!$. Hence the nonholonomic order of
$z_j$ is exactly $j+1$, and $x$ has order one. This proves the required
privileged property, rather than inferring it from ordinary coordinates.
The weighted dilations and leading fields are explicitly

$$
\delta_s(x,z_0,\ldots,z_{g-1})=(sx,sz_0,s^2z_1,\ldots,s^gz_{g-1}),
\qquad \widehat P=\partial_x,\quad
\widehat Q=\sum_{j=0}^{g-1}x^j\partial_{z_j}.
\tag{10.8b}
$$

The chart is injective whenever $|x|<\delta$ and
$|W_{k_0}z|_\infty<\eta<\pi$. Proposition 10.2 bounds the length before
its first exit. The smooth fields satisfy the bracket condition with step
$g$ everywhere in this chart. Their growth ranks are constant, so all its
points are regular. These are the hypotheses of
[Jean, *Control of Nonholonomic Systems*, Theorem 3.5,
Corollary 3.6 and Remark 3.3](https://arxiv.org/abs/1209.4387v2).
Apply the ball-box estimate to $P,Q$ with the Euclidean control norm.
On a compact interior neighbourhood,
$\mathsf L_{I_2}/\sqrt\Lambda\le\mathsf L_A
\le\mathsf L_{I_2}/\sqrt\lambda$; the same two-sided comparison holds for
distances. Thus the very same privileged coordinates give (10.7) for $A$.
The charts vary smoothly with $k_0$ and phase translation; regularity and a
finite compact cover give uniform constants on $K$.

For volume, $d\mu=\rho(k_0+x,h_0+W_{k_0}z)|\det W_{k_0}|\,dx\,dz$.
Its factor is bounded above and below on these compact charts. Integrating
the two boxes gives (10.8). This also matches Jean's Corollary 4.8: the
adapted frame $(P,Q_0,\ldots,Q_{g-1})$ has lengths $(1,1,2,\ldots,g)$,
a nonzero volume determinant, and a compactly bounded step. No singular
stratum is crossed in this use. The exponent is distinct from state
count, current-ray dimension $g+1$, direct rank two, and the finite or
infinite real Lie-algebra dimension in §9.3. The inverse-gap costs (10.5b)
retain the obstruction to cross-wall uniform synthesis. Varying $\kappa$
alone injects an open interval into the rays, since $p_{13}=\kappa$; the
state set is uncountable in every regime. $\square$

### 10.3 An exact double-wall chart and a sharp central scale

**Theorem 10.4 (Guarded central transport and the original output).** Assume
$X=Y=r/2$. At any actual ray $q_0=(k_0,\alpha_0,\beta_0)$ use the phases
of (8.17), $\alpha=u-v$, $\beta=u$, and the real local differences

$$
c_0=\frac12-\frac{k_0}{r},\qquad
x=\kappa-k_0,\quad y=2(\alpha-\alpha_0),\quad
z=-r\{(\beta-\beta_0)-c_0y\}.
\tag{10.9}
$$

A source chart is $|x|<\delta$, $|y|<2\pi$,
$|c_0y-z/r|<\pi$, where
$0<\delta\le\min(k_0,r/2-k_0)$; all inequalities are strict. In it

$$
P=\partial_x,\qquad Q=\partial_y+x\partial_z,
\qquad [P,Q]=\partial_z.
\tag{10.10}
$$

Declare $A=I_2$. For a compact promise $[l,u]\subset(0,r/2)$, choose
$0<R<\min(l,r/2-u)$ and either sign $s\in\{1,-1\}$. One and the same
relative command is lawful for every height in the promise and every phase,
and closes its real control base with central displacement $\tau=s\pi R^2$.
At every $k_0\in[l,u]$, the distance to its resulting ray is exactly

$$
d_{I_2}(q_0,q_\tau)=2\pi R=2\sqrt{\pi|\tau|},
\qquad \Delta\alpha=0,\quad\Delta\beta=-\tau/r.
\tag{10.11}
$$

Here the distance may allow all positive native paths, or be restricted to
any interior open domain containing the constructed path. The original
$02$ coherence pair differs by

$$
\|y_{02}(q_\tau)-y_{02}(q_0)\|_2
=4\sqrt{k_0Z}\left|\sin\left(\frac{\tau}{2r}\right)\right|.
\tag{10.12}
$$

All other original coherence pairs return, so (10.12) is also the Euclidean
norm of the full ten-component output difference. This holds for arbitrary
preparation phases and arbitrary current phases.

**Proof.** From §8.5, $Q\alpha=1/2$, $Q\beta=1/2-\kappa/r$.
The map (10.9) is invertible with
$\kappa=k_0+x$, $\alpha=\alpha_0+y/2$,
$\beta=\beta_0+c_0y-z/r$, so it gives exactly (10.10), including the
bracket sign. Take, on $0\le t\le1$,

$$
a(t)=x(t)=R\sin(2\pi t),\qquad
b(t)=y(t)=sR(1-\cos(2\pi t)),\qquad z(t)=\int_0^t x\,dy.
\tag{10.13}
$$

Then $A_\gamma=B_\gamma=0$, $m_\gamma=-R$, $M_\gamma=R$ and
$K_\gamma=\tau=s\pi R^2$. Formula (9.11) gives precisely the displayed
phase endpoint. All bottom masses on the common promise are at least
$\min(l-R,r/2-u-R)>0$; the middle mass remains $Z>0$.
The phase variation is $4R<\infty$, so this is an original admissible
zero-winding loop, not a new central actuator.

At a fixed $k_0$, the path satisfies $|x|\le R$, $|y|\le2R$ and
$|z|\le\pi R^2$. Since $R<r/4$ and $0<c_0<1/2$, it has
$|\alpha-\alpha_0|\le R<\pi$ and
$|\beta-\beta_0|\le R+\pi R^2/r<\pi$. Thus one may choose
$R<\delta\le\min(k_0,r/2-k_0)$ in the chart above. Its control norm is
$\sqrt{\dot x^2+\dot y^2}$, so its length is $2\pi R$.

For any rectifiable horizontal path with these real central endpoints,
$x,y$ form a closed planar curve and $\tau=\int x\,dy$. Reparametrize
by arclength on $[0,L]$ and subtract the two coordinate means. Periodic
Wirtinger and Cauchy--Schwarz give the classical intermediate inequality

$$
\left|\int x\,dy\right|
=\frac12\left|\int(x\dot y-y\dot x)\,dt\right|
\le\frac12\left(\int(x^2+y^2)\right)^{1/2}\sqrt L
\le\frac{L^2}{4\pi}.
\tag{10.13a}
$$

The circle attains equality. This lower bound also applies to every
potential shorter path between the actual rays, without assuming its lift:
if $L<2\pi R<\pi/2$, then
$|\Delta\alpha|\le L/2<\pi/4$ and $|\Delta\beta|\le L/2<\pi/4$,
since $|Q\beta|<1/2$ throughout the positive source. Its endpoint must
have $\Delta\alpha=2\pi m$ and
$\Delta\beta=-\tau/r+2\pi n$. As $|\tau|/r<\pi/16$, these bounds force
$m=n=0$. Its real $y$ endpoint is zero and its real $z$ endpoint is $\tau$;
(10.13a) excludes the shorter path. This proves sharp distance on rays,
not just a lower bound in one chosen winding sector. Larger displacements
must be reduced by the phase lattice; (10.11) asserts only the stated range.

The original output (8.8) has radius $2\sqrt{k_0Z}$ and angle
$\delta_{02}^0+\beta$. Its chord under $\Delta\beta=-\tau/r$ gives
(10.12); the arbitrary preparation rotates both vectors equally. In (8.19),
the four bottom-edge pairs depend only on the returned $k_0,\alpha_0$, so
the full output difference has exactly this same norm. For an
explicit instance, let $Z=1/5$, $r=4/5$, $X=Y=2/5$,
$[l,u]=[3/20,1/4]$, $k_0=1/5$, $R=1/20$ and $s=1$.
Every bottom mass is at least
$1/10$ on the whole promised family, while at $k_0$

$$
\tau=\pi/400,\qquad d_{I_2}=\pi/10,\qquad
\Delta\beta=-\pi/320,\qquad
\|\Delta y_{02}\|_2=\frac45\sin(\pi/640)>0.
\tag{10.13b}
$$

For the mature Heisenberg correspondence, put $\zeta=z-xy/2$.
Then (10.10) becomes
$\partial_x-(y/2)\partial_\zeta$ and
$\partial_y+(x/2)\partial_\zeta$, exactly the fields and orthonormal
horizontal norm of [Bonnefont--Juillet, §2.1](https://arxiv.org/abs/1801.04109v2).
Their generator is half the sum of squares; the full sum below uses their
process at time $2t$. The coordinate map applies only on the guarded source
chart, not as a global homogeneous identification of the phase torus.
The sharp constant above follows from (10.13a) with the native norm, so no
unspecified normalization of a central-distance formula is used. $\square$

### 10.4 The principal-symbol obstruction to a Euclidean second order bridge

**Theorem 10.5 (No same-clock full-state elliptic identification).**  Let
$A(q)$ be any smooth positive $2\times2$ native-control covariance and let
$b^1,b^2$ be arbitrary smooth lower-order coefficients.  The most general
second-order operator with this covariance and horizontal drift has
the form

$$
\mathscr G_Af=\sum_{i,j=1}^2a^{ij}(q)X_iX_jf
 +\sum_{i=1}^2b^i(q)X_if,\qquad (X_1,X_2)=(P,Q).
\tag{10.14}
$$

Its principal symbol is

$$
\sigma_q(\xi)=\sum_{i,j=1}^2a^{ij}(q)\,\xi(X_i(q))\xi(X_j(q)).
\tag{10.15}
$$

It has rank exactly two on every current-ray manifold.  Consequently:

1. no smooth change of coordinates on the full current-state manifold can
   identify (10.14), in the same clock, with a nondegenerate isotropic
   Euclidean operator in dimension $g+1$;
2. no smooth three-dimensional target factor of the native state can have a
   nondegenerate elliptic second-order generator induced by (10.14);
3. adding $[P,Q]^2$ supplies a third independent principal direction;
   adding any nonzero further bracket square also changes the specified
   second-order law. Zero brackets supply no direction.

**Proof.** The map
$B_q:\mathbb R^2\to T_q\mathcal M_b$, $B_qe_i=X_i(q)$, is injective because
$P$ has a nonzero $\kappa$ component and $Q$ is nonzero and vertical.  Since $A(q)$ is
positive definite, the contravariant symbol is $B_qA(q)B_q^{\mathsf T}$ and
has rank two.  Equivalently, every covector annihilating both $P$ and $Q$ is
in the symbol kernel.  On the double wall the nonzero covector $dz-x\,dy$ annihilates
both fields in (10.10); $dz$ itself does so at the chart centre $x=0$.
Thus a reachable central direction does not provide principal variance in
the missing cotangent direction.

Under a smooth coordinate map, a principal symbol transforms by an invertible
congruence on cotangent spaces, so its rank is unchanged.  The isotropic
Euclidean operator $\sum_{j=1}^{g+1}\partial_{x_j}^2$ has rank $g+1>2$.
For a smooth map into a three-dimensional target, the pushed-forward symbol
has rank at most two and hence cannot be elliptic of rank three.  Drift terms,
Jacobian terms and the choice between Itô and Stratonovich conventions are
lower order and cannot change (10.15).

The infinitesimal variance statement is the same obstruction.  If
$A=\Sigma\Sigma^{\mathsf T}$ and the native diffusion is written with the
same clock as

$$
dq_t=\sqrt2\sum_{a=1}^2\left(\sum_{i=1}^2\Sigma_{ia}X_i(q_t)\right)\circ dB_t^a
 +\text{(drift)}\,dt,
\tag{10.16}
$$

then for a smooth test $f$ and exit time $\sigma_U$ from a relatively
compact interior chart containing the starting point $q$,

$$
\lim_{t\downarrow0}\frac1t
\operatorname{Var}_q\bigl(f(q_{t\wedge\sigma_U})\bigr)
=2\sigma_q(df_q).
\tag{10.16a}
$$

Here $f$ is smooth near the chart closure. Itô isometry and continuity of
the stopped coefficients give this limit; the drift contributes $o(t)$ to
the variance. Every covector at $q$ is $df_q$ for such a local test.

A covector annihilating the native two-plane has zero variance in this clock,
whereas a nondegenerate three-dimensional Euclidean Brownian motion has
strictly positive variance in every nonzero covector.  Squaring the commutator
would assign positive variance in that missing direction and is therefore a
different stochastic law, not bookkeeping for the original two controls.
More explicitly, a factor would require a smooth map $F$ onto an open
three-dimensional target and a generator $\overline{\mathscr G}$ with
$\mathscr G_A(f\circ F)=(\overline{\mathscr G}f)\circ F$ for all local
smooth tests. Quadratic tests with zero first derivative at $F(q)$ identify
the target symbol with $DF_qB_qA(q)B_q^{\mathsf T}DF_q^{\mathsf T}$, of rank
at most two. Cutoffs supported inside the source and target charts make
these legitimate interior tests for any matched Dirichlet realization.
Hence neither killing nor lower-order terms can repair the rank defect.
A smooth positive clock multiplier also preserves rank, although it changes
the operator; singular scaling limits or homogenization are different
questions. Positive-time smooth transition densities from brackets do not
contradict a rank-two infinitesimal covariance. $\square$

### 10.5 A declared local analytic diffusion and its observable factor

**Definition 10.6 (Added Dirichlet diffusion).** In any one fixed mean regime
choose $I=(l,u)\Subset J_b$ and $\Omega=I\times\mathbb T^g$. Take the
smooth density and positive covariance of Definition 10.1 on a neighbourhood
of $\overline\Omega$. With $X_1=P$, $X_2=Q$, set

$$
d\mu=\rho\,d\kappa\,dh,\qquad
\mathsf T_A[f]=\int_\Omega\sum_{i,j=1}^2a^{ij}
 (X_jf)\overline{X_if}\,d\mu,
\qquad X_i^*=-X_i-\operatorname{div}_\mu X_i.
\tag{10.17}
$$

Close this form from $C_c^\infty(\Omega)$ and take its nonnegative
Friedrichs operator and heat semigroup

$$
\mathcal L_{A,\Omega}=\left(\sum_{i,j}X_i^*(a^{ij}X_j)\right)_{F,\Omega},
\qquad H_t^\Omega=e^{-t\mathcal L_{A,\Omega}}.
\tag{10.18}
$$

The boundary convention is Dirichlet killing at $\kappa=l,u$ and periodic
phases. Both height boundary components are noncharacteristic because
$P\kappa=1$. The single analytic clock $t$ assigns instantaneous control
covariance $2A\,dt$, so the principal part of $-\mathcal L_{A,\Omega}$ is
$\sum a^{ij}X_iX_j$. Density, covariance, clock and killing are additional
structure; Definition 3.1 itself supplies no diffusion.

**Theorem 10.7 (Native local heat, stochastic scales and a weaker factor).**
The added operator has a smooth positive interior heat density
$p_t^\Omega(q,q')$ with respect to $\mu$. Use the privileged chart $\Phi_q$
of (10.6a), centred at $q$, and its dilation (10.8b). Then

$$
\epsilon^{Q_{\rm vol}}p_{\epsilon^2t}^\Omega
 \bigl(q,\Phi_q^{-1}(\delta_\epsilon\xi)\bigr)
\longrightarrow\widehat p_q(t,0,\xi).
\tag{10.19}
$$

The convergence is smooth locally for $t>0$, and uniform for $q$ in compact
interior sets. The tangent operator is
$\sum a^{ij}(q)\widehat X_i\widehat X_j$, with
$(\widehat X_1,\widehat X_2)=(\widehat P,\widehat Q)$ of (10.8b), and its
density is $d\widehat\mu_q=\rho(q)|\det W_k|\,dx\,dz$. In particular,

$$
\mu(B_{d_A^\Omega}(q,\epsilon))\asymp\epsilon^{Q_{\rm vol}},\qquad
p_t^\Omega(q,q)\sim\widehat p_q(1,0,0)t^{-Q_{\rm vol}/2},
\quad \widehat p_q(1,0,0)>0.
\tag{10.20}
$$

Thus the diagonal powers are $11/2,7/2,7/2,2$ in the four regimes. These
are local small-time exponents for this added process, not a global spectral
law or a count of physical axes.

On the double wall, specialize to $A=I_2$ and
$d\mu=d\kappa\,d\alpha\,d\beta$ (unnormalized angular measure). Then
$\mathcal L_{I_2,\Omega}=\bigl(-(P^2+Q^2)\bigr)_{F,\Omega}$.
The change $(u,v)\mapsto(\alpha,\beta)$ has absolute determinant one,
so this is the grouped constant density. An unrestricted real
comparison process, started at $(k,\alpha_0,\beta_0)$, is

$$
\begin{aligned}
dK_t&=\sqrt2\,dB_t^1,\\
d\alpha_t&=\frac1{\sqrt2}\,dB_t^2,\\
d\beta_t&=\sqrt2\left(\frac12-\frac{K_t}{r}\right)dB_t^2,
\end{aligned}
\tag{10.21}
$$

where the two Brownian motions are independent. Project its phases onto the
actual torus and kill at $\tau_I=\inf\{t:K_t\notin I\}$ to obtain exactly
the diffusion in (10.18). The unrestricted process is only a comparison
extension; its states outside $J_b$ are not probability states. On its real
lift, at every finite $t$,

$$
K_t=k+\sqrt2B_t^1,\quad
\alpha_t=\alpha_0+B_t^2/\sqrt2,\quad
\beta_t=\beta_0+\sqrt2\int_0^t(1/2-K_s/r)\,dB_s^2.
\tag{10.22}
$$

Conditionally on the whole $K$ path, the two phase increments are jointly
Gaussian, with

$$
\begin{aligned}
\operatorname{Var}(\alpha_t-\alpha_0\mid K)&=t/2,\\
\operatorname{Var}(\beta_t-\beta_0\mid K)&=2\int_0^t(1/2-K_s/r)^2ds,\\
\operatorname{Cov}(\alpha_t-\alpha_0,\beta_t-\beta_0\mid K)
 &=\int_0^t(1/2-K_s/r)ds.
\end{aligned}
\tag{10.23}
$$

In the centred coordinates (10.9) this unrestricted comparison has exactly

$$
x_t=\sqrt2B_t^1,\quad y_t=\sqrt2B_t^2,\quad
z_t=2\int_0^t B_s^1\,dB_s^2,\qquad
\operatorname{Var}(x_t)=\operatorname{Var}(y_t)=2t,\quad
\operatorname{Var}(z_t)=2t^2.
\tag{10.23a}
$$

These unconditional finite-time moments are not moments of the killed or
wrapped law. If $\sigma$ is the exit time from a fixed coordinate box centred
at the initial point with closure inside the source chart and $\Omega$,
then the corresponding localized statements are
$\operatorname{Var}(x_t\mid\sigma>t)=2t+o(t)$,
$\operatorname{Var}(y_t\mid\sigma>t)=2t+o(t)$ and
$\operatorname{Var}(z_t\mid\sigma>t)=2t^2+o(t^2)$ as $t\downarrow0$.

There is an exact two-dimensional observable factor in the same clock:
for every bounded Borel $f$ on $I\times\mathbb T$,

$$
H_t^\Omega(f\circ\pi)(k,\alpha,\beta)
=\left(e^{t(\partial_k^2+\frac14\partial_\alpha^2)}_{D,I\times\mathbb T}
 f\right)(k,\alpha),\qquad \pi(k,\alpha,\beta)=(k,\alpha).
\tag{10.24}
$$

It retains $p_k$ and the relative bottom phase $\alpha$, and loses the
original middle-reference output

$$
y_{02}(k,\beta)=2\sqrt{kZ}
\begin{pmatrix}\cos(\delta_{02}^0+\beta)\\
\sin(\delta_{02}^0+\beta)\end{pmatrix}.
\tag{10.25}
$$

Locally $y=2\alpha$ makes the factor generator $\partial_k^2+\partial_y^2$;
globally that coordinate has period $4\pi$. It is not a three-target factor.

**Proof.** Write $A=\Sigma\Sigma^{\mathsf T}$ with its smooth positive
square root and $Y_a=\sum_i\Sigma_{ia}X_i$. The form in (10.17) is
$\sum_a\|Y_af\|_2^2$. It is closable: if $f_n\to0$ in $L^2$ and
$Y_af_n\to g_a$ in $L^2$, testing against $Y_a^*\varphi$ for
$\varphi\in C_c^\infty(\Omega)$ gives $g_a=0$. In the interior

$$
-\mathcal L_{A,\Omega}=\sum_aY_a^2+Y_0,\qquad
Y_0=\sum_a(\operatorname{div}_\mu Y_a)Y_a.
\tag{10.25a}
$$

The drift is horizontal and smooth; there is zero potential. An invertible
smooth change of horizontal frame preserves the full bracket flag, as
follows inductively by expanding coefficient brackets. Theorem 10.3 thus
gives strong Hörmander generation, constant ranks and bounded step $g$ on a
neighbourhood of $\overline\Omega$. The manifold is connected, the density
is smooth positive, and the Friedrichs realization is selfadjoint and
nonnegative, with contraction semigroup. These verify the semigroup and
positivity hypotheses in §3.1.2 of
[Colin de Verdière--Hillairet--Trélat,
*Small-time asymptotics of hypoelliptic heat kernels near the diagonal,
nilpotentization and related results*](https://doi.org/10.5802/ahl.93).
Their Theorem B, equation (2.8), uses privileged coordinates, a smooth
horizontal drift and locally bounded bracket step, all verified here.
The drift disappears on rescaling; $\Sigma$ freezes at $q$ and the density
rescales to the displayed $\widehat\mu_q$. This proves (10.19).

Their Theorem 3.2 permits different boundary realizations of the same smooth
operator and density with bounded semigroup norms. Applied to a larger
interior cylinder and the present Dirichlet cylinder, both are contractions
and have identical interior differential expressions. It makes their kernel
difference $O(t^N)$ for every $N$, with derivatives on overlap compacts.
Thus (10.19) is valid away from the declared killing boundary; no new
localization theorem or global homogeneous source is presumed. All points
are regular, which is the supplier's condition for uniformity in $q$.
Positivity of the tangent kernel, $t=1$, and $\epsilon=\sqrt t$ give the
second estimate (10.20); the first was proved in Theorem 10.3.

For the double-wall specialization $P,Q$ have zero divergence in the declared
measure. There is no Itô correction in (10.21), since $QK=0$ and
$Q(Q\beta)=0$, and the two Brownian motions have zero cross variation.
Its generator is $P^2+Q^2$, with the factor $\sqrt2$ fixing the clock.
Integration gives (10.22), and independence of $B^2$ from $K$ gives (10.23).
In (10.9), $c_0=1/2-k/r$, so cancellation of the common $B^2$ term gives
$z_t=2\int B^1dB^2$. Itô isometry gives
$\mathbb E z_t^2=4\int_0^t s\,ds=2t^2$, with zero mean. In this chart
$d\mu=(2r)^{-1}dx\,dy\,dz$; this is the density of its tangent heat kernel,
not unit Lebesgue measure silently substituted into (10.19).

For the localized moments, before exit from a box $|x|<d$, the stopped
martingale $z$ has quadratic variation at most $2d^2t$. Brownian reflection
for $x,y$ and the exponential martingale inequality for stopped $z$ give
$\mathbb P(\sigma\le t)\le C e^{-c/t}$ for this fixed box. The unrestricted
variables in (10.23a) have moments of every order, with Brownian scaling
$x,y=O_{L^m}(\sqrt t)$ and $z=O_{L^m}(t)$. Cauchy--Schwarz bounds their
first and second moments on the exit event by exponentially small errors.
Dividing by $\mathbb P(\sigma>t)$ proves the stated conditional asymptotics.
This argument concerns only the explicit comparison process and this box.

For a smooth factor test, $Q(f\circ\pi)=\tfrac12(\partial_\alpha f)\circ\pi$,
so its generator is $\partial_k^2+\tfrac14\partial_\alpha^2$. Tests compactly
supported in the height interior pull back to $C_c^\infty(\Omega)$.
More strongly, (10.21) projects to this cylinder diffusion and the exit
event is exactly $\{\tau_I\le t\}$ on both sides. The killed expectation
therefore gives (10.24) for bounded Borel tests. Surjectivity makes this
pullback injective and isometric for the supremum norm; it is not a zero
intertwiner. Changing the killing boundary to depend on $\beta$ would not
justify this semigroup identity merely from the generator computation.
Two states with the same $k,\alpha$ and different $\beta\bmod2\pi$ are
actual reachable rays by Theorem 8.2, and (10.25) distinguishes them.
The finite-time stochastic identities, their localized small-time versions
and the original finite-variation histories are therefore distinct contracts.
Brownian control paths are almost surely not Definition 3.1 controls. $\square$

### 10.6 Comparison with the actual spatial and stability contracts

**Proposition 10.8 (The missing second-order spatial correspondence).** For
the same varying-height rays and original controls, the source data are

$$
\begin{array}{c|c|c|c}
\text{regime}&\text{current-ray dimension}&\text{native rank}&Q_{\rm vol}\\ \hline
\text{neither wall}&5&2&11\\
E_-\text{ only}&4&2&7\\
E_+\text{ only}&4&2&7\\
\text{both walls}&3&2&4.
\end{array}
\tag{10.26}
$$

No row supplies a smooth same-clock full-state Euclidean identification or
an elliptic three-target factor of a positive native two-control operator.
Neither the local volume/heat estimates nor the observable factor (10.24)
satisfies the actual dual-scale or rank-three stability hypotheses.

**Proof.** The table and the operator exclusions are Theorems 10.3 and 10.5.
For precise supplier correspondence, [Boundary Geometry,
§52.7](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md)
identifies the Euclidean dual-scale contract as an infinite Euclidean spatial
domain, isotropic second-order field, unscreened attractive point source,
second-order localization and the specified form domain. Native probability
and phase coordinates furnish none of those additional identifications.
The same-source obligation in [Continuation III,
§81.5](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md)
requires an actual source map inducing the operator on stated function spaces,
with measures, variances, domains, boundaries and clocks matched. It also
requires the field and potential to correspond under that same map. The
factor (10.24) does meet a bounded-observable operator correspondence on its
stated cylinder, but has only two target coordinates and loses (10.25).

Continuation III Definition 82.1 instead fixes a connected simply connected
stratified nilpotent group with $\dim V_1=3$, a positive horizontal inner
product, three left-invariant orthonormal fields, Haar measure and the
positive homogeneous point-source Green kernel of their sum of squares.
Its kinetic form and attractive field use this same operator, measure and
clock on the full punctured test core. Nonabelianity then forces $Q\ge5$;
this rank-three implication is essential to its scaling instability.
The literal §82.3 example is $H^1\times\mathbb R$, with a third independent
Brownian input, topological dimension four and $Q=5$. It is not the native
rank-two double-wall chart (10.10). Adding its extra Euclidean field would
alter both the source and the principal symbol.

Definition 83.1 fixes three smooth independent fields, strong Hörmander
generation, a smooth positive density, a relatively compact smooth domain
in a flow box, and a Dirichlet Friedrichs realization. Its matched field is
the full Green integral of that realization, coupled to the same kinetic
form. Its local implication uses $Q(o)\ge2n-3\ge5$ when $n>3$ because
exactly three weights are one. The native structure instead has exactly two
weights one. Even the native double-wall tangent has $Q=4$, where the
hypothetical homogeneous Green weight and kinetic localization would both
scale as $s^{-2}$; the strict power comparison in §82.2 or §83.2 gives no
coupling-independent conclusion at that critical exponent. No such
attractive potential or stability requirement is part of Definition 3.1.

Thus local control volume, local diagonal heat power, real Lie-algebra
dimension, affine response capacity and physical axes remain different
quantities. A smooth positive two-control covariance cannot supply the
missing third instantaneous variance. The density, stochastic clock and
Dirichlet law in §10.5 are explicit additions, and do not establish a
physical kinetic/field relation, a bound state, a global Green law, free
rotations, mean selection, or a finite-bit acquisition guarantee.
The fixed-mean law has no operation choosing $X=Y=r/2$.

The separate [native affine continuation result, §§4--6](https://github.com/the-omega-institute/trureturing/blob/6ea83df2b1efe0fbbe16220bc9870321dc2b74b3/docs/develop/theory/FIB_NATIVE_CONTINUATION_AFFINE_OBSTRUCTION_AND_APPROXIMATION.md)
concerns exact affine updates and positive-band probability-leg
approximation; it supplies none of these metric, diffusion or physical
correspondences. The new deductions here are their distinct native
control-coordinate, cost, output and second-order applications. Jean's
estimates and the cited heat results are literature-attested intermediates;
no general classical theorem or worldwide priority is claimed. $\square$

### 10.7 Finite measure and the precise killed Green boundary

**Proposition 10.9 (Native finite-volume and killed-domain limits).** With
the explicitly chosen constant density $d\mu_0=d\kappa\,dh$, the whole
positive source has

$$
\mu_0(\mathcal M_b)=(\kappa_+-\kappa_-)(2\pi)^g<\infty.
\tag{10.27}
$$

Consequently its metric balls cannot satisfy a positive lower bound
$cR^{Q_{\rm vol}}$ for every $R>0$. This is a limitation for this density,
not for arbitrary densities with singular endpoint growth.

For the double-wall identity-covariance Dirichlet realization in Theorem 10.7,
let $\Gamma_q(q')=\int_0^\infty p_t^\Omega(q,q')\,dt$. Its full integral is
positive, finite and smooth for $q'\ne q$, is infinite at $q'=q$, and obeys

$$
\int_\Omega\Gamma_q(q')\,d\mu(q')
=\frac{(k-l)(u-k)}2\le\frac{(u-l)^2}{8},\qquad q=(k,\alpha,\beta).
\tag{10.28}
$$

**Proof.** Integrate the constant density over the finite interval and the
$g$ phase circles to get (10.27). Every ball is a subset of this finite
measure space, whereas $cR^{Q_{\rm vol}}\to\infty$, proving the global
volume obstruction. On each $\Omega\Subset\mathcal M_b$, any smooth
positive density defined near its closure also has finite total mass by
boundedness and compactness. These facts preclude importing all-scale
homogeneous volume growth from the local chart.

In the double-wall cylinder, apply the one-dimensional Dirichlet Poincaré
inequality at each $(\alpha,\beta)$ and then integrate over the torus:

$$
\|f\|_{L^2(\mu)}^2\le\frac{(u-l)^2}{\pi^2}\|Pf\|_{L^2(\mu)}^2
\le\frac{(u-l)^2}{\pi^2}\mathsf T_{I_2}[f],\qquad
\mathcal L_{I_2,\Omega}\ge\lambda_D:=\frac{\pi^2}{(u-l)^2}>0.
\tag{10.29}
$$

The estimate passes from $C_c^\infty(\Omega)$ to the closed form domain.
Symmetry and the semigroup law therefore give, for $t\ge1$,

$$
0\le p_t^\Omega(q,q')\le e^{-\lambda_D(t-1)}
\sqrt{p_1^\Omega(q,q)p_1^\Omega(q',q')}.
\tag{10.30}
$$

Indeed each time-$1/2$ kernel row has squared $L^2$ norm equal to the
corresponding diagonal time-one kernel; the intervening operator has norm
at most $e^{-\lambda_D(t-1)}$. For $q'\ne q$, the off-diagonal
flatness at $t=0$ in the cited heat paper §3.2.1 gives $O(t^N)$ on compact
sets for every $N$. These small- and large-time bounds make $\Gamma_q$
finite off $q$. Integrating the heat equation against compactly supported
tests gives $\mathcal L_{I_2,\Omega}\Gamma_q=\delta_q$ in distributions;
hypoellipticity then gives smoothness off $q$. Positivity follows from the
positive interior heat density. At $q'=q$, (10.20) has power $t^{-2}$,
whose integral at zero diverges.

For spatial integrability and (10.28), the kernel row mass is exactly
$\mathbb P_q(\tau_I>t)$, by the killed representation (10.21).
The bounded nonnegative function $v(k)=(k-l)(u-k)/2$ has $v''=-1$ and
zero boundary values. Itô's formula at $t\wedge\tau_I$ gives
$\mathbb E v(K_{t\wedge\tau_I})=v(k)-\mathbb E(t\wedge\tau_I)$.
Nonnegativity first implies $\mathbb E\tau_I\le v(k)<\infty$; bounded
convergence then gives equality. Tonelli's theorem yields (10.28), including
integrability despite the single-point infinite value. This also justifies
the distributional heat integration above, with the terminal contribution
zero by the spectral gap and smoothing. None of these killed-domain facts
asserts an all-scale unscreened field on the original source, an attractive
interaction, an attained binding state or a physical spatial realization.
$\square$

## 10.99 追加锚
