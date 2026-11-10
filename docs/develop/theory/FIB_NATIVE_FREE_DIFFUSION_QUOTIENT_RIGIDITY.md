# Native free diffusion descent and hidden-circle rigidity

> The statements below are ordinary mathematical proofs in the `generic-v1`
> theorem/proof format. They are not Lean-kernel-certified declarations.

## 1. The fixed source and its existing behavioral quotient

**Definition 1.1 (source and owning references).** Write [N] for
[Probability, phase transport and holonomy](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md),
[B] for its
[observation-quotient continuation](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY_CONTINUATION.md),
and [G] for
[Native two-control Green attraction, critical stability and periodic binding](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md).
Fix the double wall, with

$$
0<Z<1,\qquad r=1-Z,\qquad L=r/2,\qquad X=Y=L,
\qquad J=(0,L).
$$

The five probabilities, in mode order $(0,1,2,3,13)$, are

$$
p_k=(k,L-k,Z,L-k,k),\qquad k\in J.
\tag{1.1}
$$

Fix an arbitrary preparation height and arbitrary preparation phases
$\theta_s^0$. They remain fixed throughout. Phase coordinates are increments,
not constraints equating the preparation phases. In the negative phase
convention a representative at $(k,\alpha,\beta)$ is

$$
\begin{aligned}
\psi_0&=\sqrt{k}\,e^{-i(\theta_0^0+\beta)},&
\psi_1&=\sqrt{L-k}\,e^{-i(\theta_1^0+\beta-\alpha)},\\
\psi_2&=\sqrt Z\,e^{-i\theta_2^0},&
\psi_3&=\sqrt{L-k}\,e^{-i(\theta_3^0+\beta-\alpha)},\\
\psi_{13}&=\sqrt{k}\,e^{-i(\theta_{13}^0+\beta)}.
\end{aligned}
\tag{1.2}
$$

Thus $\alpha=u-v$ and $\beta=u$ for the two grouped increments $u,v$.
Both $\alpha$ and $\beta$ have period $2\pi$. The integral change of torus
coordinates $(u,v)\mapsto(u-v,u)$ has determinant one. There is no further
finite quotient. The source and the bottom behavioral quotient are

$$
\mathcal M=J\times\mathbb T^2,\qquad
\mathcal B=J\times\mathbb T,\qquad
\pi(k,\alpha,\beta)=(k,\alpha),\qquad
\mathbb T=\mathbb R/(2\pi\mathbb Z).
\tag{1.3}
$$

After removing the fixed preparation rotations, the independent bottom
coherence and middle-reference coherence are respectively

$$
z=\sqrt{k(L-k)}e^{i\alpha},\qquad w=\sqrt{Zk}e^{i\beta}.
\tag{1.4}
$$

The raw outputs retain their original factor two and their fixed rotations.
[N, Theorem 8.2] realizes every point of $\mathcal M$ by a finite original
history. [B, Theorems 10.5--10.6] identify (1.3) as the exact quotient for
bottom outputs and command lawfulness, including refusal. This quotient
is an input here, not a consequence of any diffusion assumption.

**Definition 1.2 (complete native command contract).** A relative command
$\gamma=(a,b)$ starts at $(0,0)$ and is absolutely continuous or piecewise
$C^1$, as in [N, Definitions 3.1 and 9.1]. Put

$$
A_\gamma=a(T),\quad B_\gamma=b(T),\quad
K_\gamma=\int_0^T a\,db,\quad
m_\gamma=\min a,\quad M_\gamma=\max a.
$$

It is legal at height $k$ exactly when

$$
k+m_\gamma>0,\qquad k+M_\gamma<L.
\tag{1.5}
$$

The endpoint action, on precisely this domain, is

$$
\begin{aligned}
k'&=k+A_\gamma,\\
\alpha'&=\alpha+B_\gamma/2,\\
\beta'&=\beta+B_\gamma/2-(kB_\gamma+K_\gamma)/r.
\end{aligned}
\tag{1.6}
$$

Angles in (1.6) are reduced modulo their actual periods. If a command is
also required to remain in $I=(l,h)\Subset J$, its additional guard is
$k+m_\gamma>l$ and $k+M_\gamma<h$. Concatenation takes the intersection
of the first guard and the pulled-back second guard; endpoint membership
alone is insufficient. Formula (1.6) is the supplied partial action,
not an everywhere-defined height translation.

Its two direct fields, in these same coordinates, are

$$
P=\partial_k,\qquad
Q=\tfrac12\partial_\alpha+c(k)\partial_\beta,
\qquad c(k)=\tfrac12-k/r,
\qquad [P,Q]=-r^{-1}\partial_\beta.
\tag{1.7}
$$

The control histories just specified have finite variation. Brownian
sample paths in the added analysis below are not such histories. None of
the definitions adds a reset, an actuator, a mean selector or an analytic
amplitude-preparation operation.

## 2. The full smooth Green contract and the candidate base form

**Definition 2.1 (the killed horizontal Friedrichs realization).** Fix any
nonempty $I=(l,h)\Subset J$ and put

$$
\Omega=I\times\mathbb T^2,\qquad B=I\times\mathbb T.
$$

Use the full class of [G, Definition 1.3]: $\rho$ is real, smooth and
strictly positive, and

$$
A=\begin{pmatrix}a&b\\b&d\end{pmatrix}
\tag{2.1}
$$

is real, smooth, symmetric and positive definite on an open neighbourhood
of $\overline\Omega$. Coefficients may depend on all three coordinates.
All angular integrals are unnormalized. With $X_1=P,X_2=Q$, set

$$
\begin{aligned}
d\mu&=\rho\,dk\,d\alpha\,d\beta,\\
\mathcal E(F,V)&=\int_\Omega\sum_{i,j=1}^2
 a^{ij}(X_jF)\overline{X_iV}\,d\mu,\\
\mathcal F&=\overline{C_c^\infty(\Omega)}^{(\|\cdot\|_2^2+\mathcal E[\cdot])^{1/2}}.
\end{aligned}
\tag{2.2}
$$

Compact support refers to the open height interval; all phases are
periodic. The operator and its sign are

$$
\begin{aligned}
D(\mathcal L)&=\{F\in\mathcal F:\ \exists W\in L^2(\mu),\
\mathcal E(F,V)=\langle W,V\rangle_\mu\ \text{for all }V\in\mathcal F\},\\
\mathcal LF&=W,\qquad H_t=e^{-t\mathcal L},\qquad \mathscr G=-\mathcal L.
\end{aligned}
\tag{2.3}
$$

The inner product is linear in its first argument. The form is the
horizontal closure, not an asserted isotropic $H^1_0(\Omega)$ domain.
The only killing is at $k=l,h$. The analytic control covariance is
$2A\,dt$, in the original clock $t$. The free operator (2.3) contains
no Green attraction or other potential.

Both fields have zero divergence for $dk\,d\alpha\,d\beta$. Consequently
its interior differential generator is

$$
\mathscr GF=\rho^{-1}\{P[\rho(aPF+bQF)]+Q[\rho(bPF+dQF)]\}.
\tag{2.4}
$$

Define the two projected drift coefficients

$$
B_1=\rho^{-1}\{P(\rho a)+Q(\rho b)\},\qquad
B_2=(2\rho)^{-1}\{P(\rho b)+Q(\rho d)\}.
\tag{2.5}
$$

These are functions upstairs until shown otherwise. For a base test $f$,

$$
\mathscr G(f\circ\pi)
=a f_{kk}+b f_{k\alpha}+\tfrac d4 f_{\alpha\alpha}
+B_1 f_k+B_2 f_\alpha,
\tag{2.6}
$$

where derivatives on the right are evaluated at $\pi(q)$.
In particular the coefficient of the mixed derivative is $b$, not $2b$.

**Definition 2.2 (pushforward measure, conditional projection and averages).**
For every coefficient pair in Definition 2.1, define

$$
\begin{aligned}
m(k,\alpha)&=\int_0^{2\pi}\rho(k,\alpha,\beta)\,d\beta,
&d\nu&=m\,dk\,d\alpha=\pi_*\mu,\\
A_{\rm av}(k,\alpha)&=\frac1m\int_0^{2\pi}\rho A\,d\beta,
&D&=\operatorname{diag}(1,1/2),\qquad C_{\rm av}=DA_{\rm av}D.
\end{aligned}
\tag{2.7}
$$

All these base coefficients are smooth on the closed cylinder and
uniformly positive in the appropriate sense. The pullback and its Hilbert
space adjoint are

$$
Uf=f\circ\pi,\qquad
(K_\rho F)(k,\alpha)=\frac1m\int_0^{2\pi}\rho F\,d\beta,
\qquad U^*=K_\rho.
\tag{2.8}
$$

Thus $U:L^2(\nu)\to L^2(\mu)$ is an isometry,
$K_\rho U=1$, $\mathcal H=\operatorname{ran}U$ is closed, and
$\Pi=UK_\rho$ is its orthogonal projection. A function in $\mathcal H$
is called basic; for a smooth function this means independence of $\beta$.

There is always the base form

$$
\begin{aligned}
\mathcal E_{\rm av}(f,g)
&=\int_B (\nabla f)^{\mathsf T}C_{\rm av}\overline{\nabla g}\,d\nu,\\
\mathcal V&=H^1_0(B)
:=\overline{C_c^\infty(B)}^{H^1(B)},\\
D(\mathcal L_{\rm av})
&=\{f\in\mathcal V:\ \exists v\in L^2(\nu),\
\mathcal E_{\rm av}(f,g)=\langle v,g\rangle_\nu\ \text{for all }g\in\mathcal V\},\\
\mathcal L_{\rm av}f&=v,\qquad S_t^{\rm av}=e^{-t\mathcal L_{\rm av}}.
\end{aligned}
\tag{2.9}
$$

Here $H^1_0(B)$ imposes zero trace at the two height faces and periodicity
in $\alpha$, not a cut or Dirichlet condition on the circle.
Uniform ellipticity makes the form norm equivalent to this Sobolev norm.
Equation (2.9) specifies the actual completed operator domain without
replacing it by its differential expression.

**Definition 2.3 (four distinct descent assertions).** The following
assertions concern this particular $\Omega$, $\pi$ and clock.

1. Coefficient symmetry means $\partial_\beta A=0$ and
   $\partial_\beta\rho=0$ on $\Omega$.
2. Differential projectability means $\mathscr G(Uf)$ is basic for every
   $f\in C_c^\infty(B)$.
3. Completed invariance means $H_t\mathcal H\subset\mathcal H$ for every
   $t\ge0$, for the Friedrichs semigroup (2.3).
4. All-start killed descent means that the pushforward killed path law is
   the same for every two interior representatives with the same $\pi$.
   The common laws form a diffusion on $B$ in the original time, with
   death at the exit of its height from $I$. Projection sends the upstairs
   cemetery point to the downstairs cemetery point.

A killed path includes its cemetery tail and hence its lifetime. Equality
of a single marginal, or equality after randomizing the starting fiber,
is not assertion 4. The native behavioral equivalence of Definition 1.1
is a separate, already supplied statement about deterministic guarded
commands; it holds regardless of the choice of $\rho,A$.

## 3. Exact classification on the killed cylinder

**Theorem 3.1 (full-class hidden-circle rigidity).** For every choice in
Definition 2.1, the four assertions of Definition 2.3 are equivalent.
When they hold, write $\rho=\rho_0(k,\alpha)$ and $A=A_0(k,\alpha)$ on
$\Omega$. The common descended diffusion is exactly the one from (2.9),
with

$$
m=2\pi\rho_0,\qquad A_{\rm av}=A_0,\qquad C_0=DA_0D,
\qquad
\overline{\mathscr G}f=m^{-1}\operatorname{div}_{k,\alpha}
 (m C_0\nabla f).
\tag{3.1}
$$

The completed form, operator, semigroup and lifetime correspondences are

$$
\begin{aligned}
U\mathcal V&=\mathcal F\cap\mathcal H,\qquad
\mathcal E(Uf,Ug)=\mathcal E_{\rm av}(f,g),\\
U D(\mathcal L_{\rm av})&=D(\mathcal L)\cap\mathcal H,
\qquad \mathcal L U=U\mathcal L_{\rm av},\\
H_tU&=US_t^{\rm av},\\
\tau_\Omega&=\inf\{t:K_t\notin I\}=\tau_B
\quad\text{under the projected path coupling}.
\end{aligned}
\tag{3.2}
$$

The semigroup identity holds for every interior starting point and every
bounded Borel base function, using the killed transition versions. The
path-law identity holds for the whole killed path, not just in $L^2$ or
outside an unspecified exceptional set.

The equivalent symmetry condition is required only on $\Omega$.
Smoothness extends its zero $\beta$ derivatives to $\overline\Omega$;
it does not force symmetry on a neighbourhood outside the chosen cylinder.

Proof. The proof separates the source-specific converse from the standard
analytic correspondences, whose hypotheses are checked below.

For the converse, suppose differential projectability holds. At any base
point use compactly supported tests with zero first derivative and arbitrary
symmetric second derivative in a local circle chart. Comparing (2.6) at
two points of its fiber forces $a,b,d$ to have the same values there.
The map from control covariance to base symbol is

$$
A\longmapsto DAD=\begin{pmatrix}a&b/2\\b/2&d/4\end{pmatrix},
\tag{3.3}
$$

which is injective. Thus the entire $A$, not merely one variance, is basic.
Tests with arbitrary first derivative and zero second derivative then
force $B_1,B_2$ to be basic.

Put $s=\log\rho$, a globally defined real smooth periodic function. Since
$A$ is basic, (2.5) becomes

$$
\begin{pmatrix}B_1\\2B_2\end{pmatrix}
=
\begin{pmatrix}\partial_k a+\tfrac12\partial_\alpha b\\
\partial_k b+\tfrac12\partial_\alpha d\end{pmatrix}
+A\begin{pmatrix}Ps\\Qs\end{pmatrix}.
\tag{3.4}
$$

Invertibility of $A$ now shows that both $Ps$ and $Qs$ are basic. For
$g=\partial_\beta s$, commutation with $P,Q$ gives $Pg=Qg=0$.
The actual bracket in (1.7) gives

$$
0=[P,Q]g=-r^{-1}\partial_\beta g.
\tag{3.5}
$$

Consequently $g$ is independent of $\beta$ on each fiber. Periodicity of
the real logarithm yields

$$
2\pi g(k,\alpha)=\int_0^{2\pi}\partial_\beta s\,d\beta=0.
\tag{3.6}
$$

Hence $\rho$ is basic. This is the native rigidity step: a general
projection criterion alone does not force symmetry of a density.
Positivity, the injective symbol map, the nonzero bracket and the actual
circle period all enter this argument. Conversely, if $\rho,A$ are basic,
(2.6) is immediately basic and equals (3.1).

Next identify the restricted domain, without yet assuming symmetry.
Compactness of $\overline\Omega$ gives uniform two-sided bounds for
$\rho,A$; thus the full form norm is equivalent to

$$
\|F\|_{L^2(dq)}^2+\|PF\|_{L^2(dq)}^2+\|QF\|_{L^2(dq)}^2,
\qquad dq=dk\,d\alpha\,d\beta.
\tag{3.7}
$$

Let $M_0F=(2\pi)^{-1}\int F\,d\beta$ be unweighted angular averaging.
On the smooth core,

$$
\partial_k M_0F=M_0PF,\qquad
\tfrac12\partial_\alpha M_0F=M_0QF.
\tag{3.8}
$$

The second identity uses periodicity to integrate
$c(k)\partial_\beta F$ to zero. Jensen's inequality and (3.7) show that,
if $F_n\to Uf$ in the full form norm, then $M_0F_n$ is Cauchy in
$H^1_0(B)$ and converges in $L^2$ to $f$. This proves
$\mathcal F\cap\mathcal H\subset U\mathcal V$.
Conversely, approximate any $f\in\mathcal V$ by base core functions and
pull them back. Fubini gives exactly

$$
\mathcal E(Uf,Ug)=\mathcal E_{\rm av}(f,g)
\tag{3.9}
$$

first on the core and then by closure. This proves the first line of
(3.2) for every coefficient pair. In particular a closed restricted
averaged form always exists. Its existence has not established invariance.

Assume now coefficient symmetry. Translations
$R_\theta F(k,\alpha,\beta)=F(k,\alpha,\beta+\theta)$ are unitary in
$L^2(\mu)$, preserve the core, commute with $P,Q$, and preserve the form.
Their average is precisely $\Pi=UM_0=UK_\rho$. The action is strongly
continuous in the form norm, as follows first on the core and then by
its density. Averaging and Jensen therefore give

$$
\Pi\mathcal F\subset\mathcal F,\qquad
\mathcal E(\Pi F,(1-\Pi)V)=0\quad(F,V\in\mathcal F).
\tag{3.10}
$$

For the second assertion average the second argument over translations;
the first argument is fixed by them and the averaged second argument is
zero. Thus the closed form is an orthogonal direct sum on $\mathcal H$
and $\mathcal H^\perp$. Equivalently, in the variational equation for
$(\lambda+\mathcal L)^{-1}F$, the two components decouple. Uniqueness of
that equation makes its resolvent, and hence its semigroup, preserve both
subspaces. This is also the autonomous subspace case of the closed-form
invariance criterion in [ADO, Theorem 2.2]: take the Hilbert space
$L^2(\mu)$, form space $\mathcal F$ with its form norm, convex set
$\mathcal H$, projection $\Pi$, and forcing zero. Boundedness and
quasi-coercivity follow from (2.2); (3.10) verifies the criterion on the
completed domain, not just on smooth functions.

For clarity, the operator-domain assertion does not follow merely by
writing (2.6). If $f\in D(\mathcal L_{\rm av})$ and $V\in\mathcal F$,
(3.9)--(3.10) give

$$
\mathcal E(Uf,V)=\mathcal E(Uf,\Pi V)
=\langle U\mathcal L_{\rm av}f,V\rangle_\mu.
\tag{3.11}
$$

This proves $Uf\in D(\mathcal L)$ with the asserted image. Conversely,
if $Uf\in D(\mathcal L)$, the reducing subspace property implies
$\mathcal LUf\in\mathcal H$; testing its variational equation on all
$Ug$, $g\in\mathcal V$, proves $f\in D(\mathcal L_{\rm av})$.
This proves the second line of (3.2) and the $L^2$ semigroup identity.

In the other direction, suppose only completed invariance. Every
$Uf$ with $f\in C_c^\infty(B)$ lies in $D(\mathcal L)$: integration by
parts gives the smooth compactly supported representative $-\mathscr GUf$
in its variational definition. The difference quotients
$(H_tUf-Uf)/t$ belong to the closed subspace $\mathcal H$ and converge in
$L^2$ to $\mathscr GUf$. Hence this smooth function is basic almost
everywhere. A smooth function that is fiber constant almost everywhere
for a smooth positive density is fiber constant everywhere: its
$\beta$ derivative vanishes distributionally, hence pointwise.
This proves differential projectability. The equivalence of assertions
1--3 is now established with the genuine completed domains.

It remains to connect the actual killed path laws. The relevant standard
facts are smooth SDE uniqueness, the absorbing realization of a regular
local Dirichlet form, and interior heat smoothing. Here is their
correspondence, including the reasons no exceptional starting point or
additional lifetime is introduced.

Choose the smooth positive square root $\Sigma$ of $A$, and define

$$
Y_j=\sum_{i=1}^2\Sigma_{ij}X_i,\qquad
Y_0=\sum_{j=1}^2(\operatorname{div}_\mu Y_j)Y_j.
$$

Direct expansion of the adjoints in (2.2) gives

$$
\mathscr G=\sum_{j=1}^2Y_j^2+Y_0.
\tag{3.12}
$$

Thus the smooth Stratonovich equation uses noise fields $\sqrt2Y_j$
and drift $Y_0$. Smooth local coefficients give a unique strong solution
from every point up to exit; this is [HR, Theorem 3.1], with its noise
fields multiplied by $\sqrt2$. The coefficients extend past the compact
closure, so there is no explosion before the height exit. The phases
are compact circles. Their wrapping introduces no new stopping time.

The form is regular and strongly local: its defining core is uniformly
dense in $C_0(\Omega)$ and dense in its form domain, its energy is local,
and the normal-contraction chain rule gives the Markov property.
A smooth positive Radon measure has full support. The absorbing, or part,
realization of this form is obtained by stopping the corresponding local
process on leaving $\Omega$; its domain is exactly the closure (2.2).
This is the usual Dirichlet-form stopping correspondence used in
[G, Definitions 1.3 and Proposition 2.1]. One can apply it on a slightly
larger interior cylinder and then take the part on $\Omega$: the smaller
core, density and differential expression are precisely (2.2)--(2.4).
To identify the part-form core, first approximate by form functions with
compact support inside the smaller open cylinder, as in the regular
part-form construction. Local mollification and a smooth partition of
unity then approximate these functions by $C_c^\infty(\Omega)$ in the
horizontal form norm: Friedrichs mollification for each smooth first-order
field makes its commutator with convolution tend to zero. All supports
remain away from the height faces. Thus the part closure is the specified
closure, with no larger boundary domain inserted.
On each compactly contained region the associated process solves the
martingale problem for (3.12). Uniqueness of the smooth SDE identifies
this process with the stopped SDE wherever the form construction initially
provides it.

There is no boundary ambiguity in this identification. The normal
quadratic variation is $2a\,dt$, bounded below by a positive constant,
and the normal drift $B_1$ is bounded. For example near the lower face,
$v(k)=1-e^{-\lambda(k-l)}$ satisfies

$$
\mathscr Gv=e^{-\lambda(k-l)}(\lambda B_1-\lambda^2a)<0
\tag{3.13}
$$

for fixed sufficiently large $\lambda$; the reflected expression works
at the upper face. These barriers verify regularity of the height faces for the absorbing
realization already selected by the part form. The part-form domain,
rather than the interior differential expression alone, specifies this
boundary condition. Continuous paths
leave the open cylinder precisely when their height hits one of its
faces. In particular the part-process stopping time is the stated $\tau_I$.

Finally the bracket in (1.7) spans the missing tangent direction at every
interior point. The smooth invertible frame change to the $Y_j$ preserves
this bracket-generating property, and $Y_0$ is horizontal. Interior
hypoellipticity therefore supplies the smooth heat kernel of the
selfadjoint realization; [G, Proposition 2.1] and [H, §3.1.2] apply with
zero potential. For compactly supported continuous tests the killed SDE
expectation is also continuous in its interior starting point. To see the boundary issue
in this assertion, use continuous dependence of the smooth SDE on initial
data on a slightly larger cylinder. At a height-face hit the scalar
height has nondegenerate martingale part and bounded drift, so it crosses
the exterior immediately almost surely (the local Brownian oscillation
property after time change). This makes earlier exit stable under uniform
path approximation. If exit occurs exactly at the tested time, the test
vanishes near the face and its terminal contribution still converges to
zero. Before exit, ordinary continuous dependence applies. Bounded
convergence proves the asserted continuity. The form heat solution is
continuous by the interior smoothing just established. Their initially
almost-everywhere identification therefore extends everywhere because
$\mu$ has full support. Equality on these tests gives
equality of transition measures, then on bounded Borel tests by the
monotone-class theorem. This constructs the canonical transition version
at every point; uniqueness of the SDE determines its path laws there.
It does not infer a statement about all points from bare $L^2$ equality.
The standard stopping correspondence and heat inputs here provide
existence and identification, not the coefficient converse (3.4)--(3.6).

For additional normalization detail, in local coordinates the instantaneous
covariance and Itô drift of this SDE are

$$
2MAM^{\mathsf T}\,dt,\qquad
M=\begin{pmatrix}1&0\\0&1/2\\0&c\end{pmatrix},\qquad
\begin{pmatrix}B_1\\B_2\\2cB_2-b/r\end{pmatrix}.
\tag{3.14}
$$

The last term $-b/r$ uses $PQ\beta=Pc=-1/r$; it is not discarded when
there is a cross covariance. Equations (3.12)--(3.14) keep the original
$2A\,dt$ control clock and the original angular coordinates.

Under coefficient symmetry, the first two coordinate equations are the
autonomous Itô system

$$
d\begin{pmatrix}K_t\\\alpha_t\end{pmatrix}
=\begin{pmatrix}B_1\!\downarrow\\B_2\!\downarrow\end{pmatrix}(K_t,\alpha_t)\,dt
+\sqrt2\,D\Sigma_0(K_t,\alpha_t)\,dW_t,
\tag{3.15}
$$

where a downward arrow denotes the corresponding base function, and
$\alpha$ is taken modulo $2\pi$. Its uniformly elliptic generator is
exactly (3.1). Its absorbing Friedrichs realization is (2.9), by the same
form/stopping correspondence (now with an ordinary elliptic form).
Starting two upstairs solutions at $(k,\alpha,\beta_1)$ and
$(k,\alpha,\beta_2)$ with the same Brownian motion gives identical
$(K,\alpha)$ paths by uniqueness of (3.15). Both are stopped at exactly
$\tau_I$. This proves assertion 4, the pointwise semigroup formula, and
the lifetime equality in (3.2). There is no time change.

The lifetime is finite almost surely. Indeed $a\ge a_*>0$ and
$|B_1|\le b_*$ on the closure. For $\lambda>b_*/a_*$, a positive
multiple of
$e^{\lambda(h-l)}-e^{\lambda(k-l)}$ is nonnegative on $\overline I$
and has generator at most $-1$. Stopped Itô's formula bounds
$\mathbb E_q(t\wedge\tau_I)$ by its finite initial value. Monotone
convergence gives $\mathbb E_q\tau_I<\infty$. This argument applies
also before imposing symmetry and concerns this fixed cylinder only.

Conversely, assertion 4 makes $H_tUf$ fiber constant for every bounded
base test. For $f\in C_c^\infty(B)$, stopped Dynkin's formula and the
smooth core give, for every interior $q$,

$$
\lim_{t\downarrow0}\frac{(H_tUf)(q)-(Uf)(q)}t
=(\mathscr GUf)(q).
\tag{3.16}
$$

The integrand in Dynkin's formula is bounded, and path continuity at its
interior start gives this limit. Therefore $\mathscr GUf$ is fiber
constant, proving assertion 2. This completes the four-way equivalence.
All converse calculations took place on $\Omega$; no observation of the
process before killing can force coefficients outside it. $\square$

**Proposition 3.2 (the normalization and exterior boundary are exact).**
In Theorem 3.1 the base coordinate covariance is $2C_0\,dt$ and the base
control-frame covariance, in the frame
$(\partial_k,\tfrac12\partial_\alpha)$, is $2A_0\,dt$.
The unnormalized pushforward density is $2\pi\rho_0$, and no symmetry
outside the killed cylinder is necessary.

Proof. These are respectively the first two rows of (3.14) and the
integral in (2.7). If one instead writes the base measure as
$\rho_0\,dk\,d\alpha$, both its form and its squared norm are divided
by $2\pi$, so the generator is unchanged, but $U$ is no longer an
isometry: its squared norm is multiplied by $2\pi$. The isometry in
(3.2) uses $\nu$, without that change. Rescaling only the form would
change the clock and would not be (3.2).

For an explicit exterior distinction, begin with $A=I_2,\rho=1$ and
choose a nonzero smooth height function $\zeta$ supported just above $h$
in a larger interval contained in $J$, with $\zeta=0$ at and below $h$.
For example it may be positive arbitrarily close above $h$ and flat at
$h$. Set $\rho=\exp(\zeta(k)\cos\beta)$ there. This extends the same
coefficients on $\overline\Omega$, remains smooth positive, and violates
hidden-circle symmetry arbitrarily close outside the upper face.
The killed form and every killed law on $\Omega$ are unchanged.
Thus a neighbourhood-wide symmetry converse would be false. $\square$

## 4. Native representatives and separating tests

**Mathematical input 4.1 (supplied native admissibility of separating fibers).**
For every interior $k$, every $\alpha$, and every pair $\beta_1,\beta_2$,
the states $(k,\alpha,\beta_j)$ are exact current rays from the same
fixed preparation, under the original two controls. They have identical
bottom behavior with all complete guards. Distinct $\beta_j$ modulo
$2\pi$ remain distinguishable by the original middle-reference output.

Proof. Besides the supplied realization [N, Theorem 8.2], an explicit
double-wall construction is available. Choose two distinct interior
heights $k_1,k_2$. For real lifts of any target $\alpha,\beta$, prescribe
two fixed-height control-phase legs $t_1,t_2$ satisfying

$$
t_1+t_2=2\alpha,\qquad c(k_1)t_1+c(k_2)t_2=\beta.
\tag{4.1}
$$

The determinant is $c(k_2)-c(k_1)\ne0$, so finite real solutions exist.
Move from the preparation height to $k_1$, then to $k_2$, and finally
to $k$, keeping the phase control fixed on those height legs; execute
the two phase legs at their indicated heights. Every height segment lies
inside the convex interval $J$. This is a finite piecewise linear
Definition 1.2 history, with no bound on its required resources asserted.
If the preparation height is in $I$, both auxiliary heights can also be
chosen in $I$. Otherwise the native preparation history precedes the
analytic diffusion, whose killing clock starts at the chosen state.
Formula (1.7) gives (4.1), so its endpoint has the required coordinates.
Apply the construction separately to $\beta_1$ and $\beta_2$ without
changing preparation phases or means.

Equations (1.4)--(1.6) give identical bottom outputs and refusals for this
pair, whereas $w=\sqrt{Zk}e^{i\beta}$ distinguishes the two rays. Fixed
preparation rotations and the original output factor two preserve both
statements. $\square$

**Proposition 4.2 (a full-class test for failed descent).** If coefficient
symmetry fails on $\Omega$, there are two admissible same-fiber states
$q_1,q_2$ and a bounded real $f\in C_c^\infty(B)$ for which

$$
\delta=(\mathscr GUf)(q_1)-(\mathscr GUf)(q_2)\ne0,
\qquad
(H_tUf)(q_1)-(H_tUf)(q_2)=t\delta+o(t).
\tag{4.2}
$$

One can choose a pure second-derivative test when the projected symbol
fails, and a pure first-derivative test when the symbol descends but the
projected drift fails. In either case the completed form, and not only
the differential expression, fails to reduce to the quotient.

Proof. If $A$ is not basic, choose a fiber pair with
$\Delta C=D[A(q_1)-A(q_2)]D\ne0$. In a chart at the common base point
$x$, choose $f$ with zero gradient and Hessian $\Delta C$ at $x$, by
multiplying the corresponding quadratic polynomial by a smooth cutoff
which equals one near $x$. Its support can be kept away from the height
faces and the boundary of the circle chart. Then (2.6) gives

$$
\delta=\operatorname{tr}((\Delta C)^2)>0.
\tag{4.3}
$$

No drift cancellation can remove this symbol test. Equivalently the
carré du champ of locally linear base tests measures the quadratic form
$DAD$, with covariation $2DAD\,dt$.

If $A$ is basic but $\rho$ is not, the converse (3.4)--(3.6) implies
that $(B_1,B_2)$ is not basic somewhere. Choose a same-fiber pair with
nonzero drift difference $\Delta B$, and a cutoff locally linear test
whose gradient is $\Delta B$ and whose Hessian is zero at $x$. Then
$\delta=|\Delta B|^2>0$. These two cases exhaust failure of coefficient
symmetry. Input 4.1 makes the chosen points actual native rays,
not formal states in an enlarged probability fiber. Equation (3.16)
proves the killed-law difference (4.2).

For an explicit completed-domain witness, put

$$
W=(1-\Pi)\mathscr GUf.
\tag{4.4}
$$

This is smooth, compactly supported in height, orthogonal to
$\mathcal H$, and nonzero in $L^2(\mu)$. Smoothness and positive density
turn the fiber discrepancy into a discrepancy on a set of positive
measure. Both $Uf$ and $W$ are in the full smooth core, and

$$
\mathcal E(Uf,W)=\langle-\mathscr GUf,W\rangle_\mu
=-\|W\|_2^2\ne0.
\tag{4.5}
$$

Thus the completed form has an actual nonzero cross term. If its
selfadjoint semigroup preserved $\mathcal H$, that subspace would be
reducing and this cross term would vanish. This is a genuine completed
failure on the original height boundary.

The base tests are functions of the existing behavioral quotient. Its
height can be reconstructed from two bottom observations with a small
common legal height increment, as in [B, (10.14)], and its phase from
(1.4). This explains their source meaning; it does not assert an
instantaneous nondisturbing implementation of a whole stochastic path
measurement or a precision guarantee. $\square$

**Proposition 4.3 (explicit symbol and drift counterexamples).** Fix any
$I\Subset J$, any interior $(k_*,\alpha_*)$, and $0<\eta<1$. Both of
the following coefficient pairs satisfy the full smooth-positive Green
contract and fail all-start descent.

For a symbol failure use

$$
\rho=1,\qquad A=\operatorname{diag}(1+\eta\cos\beta,1).
\tag{4.6}
$$

At $\beta=0,\pi$ the initial height quadratic variations are respectively
$2(1+\eta)dt$ and $2(1-\eta)dt$. A cutoff equal to
$(k-k_*)^2$ near the base point gives generator values $2(1+\eta)$ and
$2(1-\eta)$.

For a drift failure with identical projected symbols use

$$
A=I_2,\qquad \rho=e^{\eta\sin\beta}.
\tag{4.7}
$$

Here $B_1=0$ and

$$
B_2=\tfrac\eta2 c(k)\cos\beta.
\tag{4.8}
$$

At $\beta=0,\pi$, a height cutoff equal to one near $k_*$ times
$\sin(\alpha-\alpha_*)$ has generator values
$\eta c(k_*)/2$ and $-\eta c(k_*)/2$. Their difference is nonzero because
$c(k_*)>0$ on $J$.

Proof. Positivity is uniform on a neighbourhood of the closed cylinder:
in (4.6) the eigenvalues are at least $1-\eta$, and (4.7) has positive
smooth density. Substitution in (2.5)--(2.6) gives all displayed values.
The cutoffs have the stated jets, so no boundary or cutoff term enters
the comparison. Input 4.1 supplies the same-fiber representatives;
Proposition 4.2 supplies the completed failure as well as the pointwise
small-time law separation. $\square$

## 5. Averaging, prescribed fiber laws and the reversible qualification

**Proposition 5.1 (the averaged form is not a projected evolution).** For
every $\rho,A$ in Definition 2.1, (2.9) is the closed restriction of the
full form to basic functions, with the exact domain in (3.9). Nevertheless
the operators

$$
C_t=K_\rho H_tU
\tag{5.1}
$$

need not form a semigroup or equal $S_t^{\rm av}$. In this reversible
contract they form a semigroup for all $t\ge0$ if and only if the
equivalent conditions of Theorem 3.1 hold.

Proof. The domain and form assertions were proved using (3.7)--(3.9),
without symmetry. For core $f,g$, integration by parts shows

$$
K_\rho\mathscr GUf=-\mathcal L_{\rm av}f.
\tag{5.2}
$$

One may alternatively integrate (2.4) over the periodic hidden circle;
the $\beta$ divergence integrates to zero. Thus even agreement of the
compressed generator with the averaged differential operator holds in
the entire class. It is weaker than a semigroup identity.

Indeed selfadjointness of $H_t$ and $K_\rho=U^*$ give the exact bounded
operator identity

$$
C_{2t}-C_t^2
=U^*H_t(1-\Pi)H_tU
=[(1-\Pi)H_tU]^*[(1-\Pi)H_tU].
\tag{5.3}
$$

If $(C_t)$ is a semigroup, the right side is zero, so
$H_t\mathcal H\subset\mathcal H$ for every $t$. Theorem 3.1 applies.
The converse follows from (3.2). For the test and $W$ in (4.4),
strong differentiation at zero gives the more explicit discrepancy

$$
\langle f,(C_{2t}-C_t^2)f\rangle_\nu
=t^2\|W\|_\mu^2+o(t^2)>0
\quad\text{for all sufficiently small }t>0.
\tag{5.4}
$$

In (4.7), $m=\int e^{\eta\sin\beta}d\beta$ is a positive constant
and $A_{\rm av}=I_2$. The restricted averaged generator is therefore
$\partial_k^2+\tfrac14\partial_\alpha^2$, exactly as for the constant
case [N, (10.24)]. Equations (4.8), (4.5) and (5.4) show why that average
does not make the original diffusion sufficient for every representative.
$\square$

**Definition 5.2 (a specified mixing kernel).** A fiber probability kernel
$\Lambda$ assigns a probability $\Lambda_x$ on $\pi^{-1}(x)$ for each
$x\in B$, and acts on functions by integration. It satisfies $\Lambda U=1$.
An intertwining for this prescribed law is

$$
\Lambda H_t=S_t\Lambda.
\tag{5.5}
$$

This concerns processes started with distribution $\Lambda_x$ on a fiber.
It differs in direction and quantifiers from the all-start pullback
identity $H_tU=US_t$. Cemetery points are sent to cemetery points, and
the killed convention remains in force in (5.5). One-time compression
$\Lambda H_tU$ without (5.5) need not supply a Markov path law.

**Proposition 5.3 (a genuine weaker mixing law in the same native class).**
There are smooth positive $\rho$ and $A=I_2$ in Definition 2.1 with no
all-start descent, and a smooth strictly positive fiber probability
kernel $\Lambda$ for which (5.5) holds with the killed base generator
$\partial_k^2+\tfrac14\partial_\alpha^2$. For every base start, the
projected process started with this specified fiber distribution has
that Markov killed path law and the same height lifetime. This kernel
is not the conditional kernel of the reversible measure $\mu$.

Proof. Let $\mathscr G_0=P^2+Q^2$, with $A=I_2,\rho=1$, and denote its
killed semigroup by $H_t^0$. Choose $k_*\in I$ and the real solution
$v$ of

$$
v''(k)=c(k)^2v(k),\qquad v(k_*)=1,\quad v'(k_*)=0.
\tag{5.6}
$$

It exists smoothly on a neighbourhood of the closed interval. Choose a
nonzero real $\epsilon$ sufficiently small that

$$
h_0(k,\beta)=1+\epsilon v(k)\cos\beta>0
\tag{5.7}
$$

on a slightly larger closed cylinder. Direct calculation gives

$$
\mathscr G_0h_0=(v''-c^2v)\epsilon\cos\beta=0,
\qquad \int_0^{2\pi}h_0\,d\beta=2\pi.
\tag{5.8}
$$

Set $\rho=h_0^2$ and keep $A=I_2$. These are admissible fixed
coefficients; $\epsilon$ is just a nonzero parameter in this construction,
not a limiting procedure. The new generator is

$$
\mathscr G^hF
=\mathscr G_0F+2(P\log h_0)PF+2(Q\log h_0)QF
=h_0^{-1}\mathscr G_0(h_0F).
\tag{5.9}
$$

The transform in (5.9) also holds for the completed killed operators.
Indeed multiplication $J_hF=h_0F$ is a unitary map from
$L^2(h_0^2dq)$ to $L^2(dq)$. Both it and its inverse preserve the
horizontal Dirichlet closures, by bounded smooth coefficients and the
product rule. For core functions, integration by parts and
$\mathscr G_0h_0=0$ give

$$
\mathcal E_0(h_0F,h_0V)=\mathcal E_h(F,V).
\tag{5.10}
$$

The extra terms on expansion are the explicitly defined local integral

$$
\int_\Omega\sum_{i=1}^2(X_i h_0)X_i(h_0F\overline V)\,dq
=-\int_\Omega h_0F\overline V\,\mathscr G_0h_0\,dq=0.
$$

The tested product has compact support; $h_0$ itself is not claimed to
belong to the zero-boundary form domain. Closing (5.10) and applying the
variational domain definition give

$$
D(\mathcal L_h)=h_0^{-1}D(\mathcal L_0),\qquad
H_t^hF=h_0^{-1}H_t^0(h_0F).
\tag{5.11}
$$

There is no extra zeroth-order killing term, precisely because (5.8)
is harmonic. The same Dirichlet height faces remain. Pointwise versions
of (5.11) follow by the heat regularity and full-support argument used
in Theorem 3.1.

Define

$$
(\Lambda F)(k,\alpha)
=\frac1{2\pi}\int_0^{2\pi}h_0(k,\beta)F(k,\alpha,\beta)\,d\beta.
\tag{5.12}
$$

This is a probability kernel by (5.7)--(5.8). The original measure in
this example is still $h_0^2dq$, whose pushforward is

$$
d\nu_h=\bigl(2\pi+\pi\epsilon^2v(k)^2\bigr)\,dk\,d\alpha.
$$

The comparison semigroup $S_t^0$ is the constant-contract base semigroup,
with reference measure $d\nu_0=2\pi\,dk\,d\alpha$, coordinate
covariance $2\operatorname{diag}(1,1/4)\,dt$ and the original height
killing. In general it is not the restricted averaged semigroup for
$\nu_h$. The weak identity below is an identity of probability kernels,
not an isometry that replaces the original pushforward measure.
Let $M_0$ again denote uniform fiber averaging. For the constant contract,
Theorem 3.1 (or [N, (10.24)] and symmetry) gives
$M_0H_t^0=S_t^0M_0$, including the killed boundary. Therefore

$$
\Lambda H_t^hF=M_0H_t^0(h_0F)
=S_t^0M_0(h_0F)=S_t^0\Lambda F.
\tag{5.13}
$$

This calculation applies to bounded Borel functions, since $h_0$ is
bounded above and below on the closed cylinder and the transition
identities hold pointwise.

For completeness, the Markov path statement in this example follows
directly from (5.13), not just from its one-time consequence. If
$M_{Uf}$ means multiplication by a base test upstairs, then

$$
\Lambda M_{Uf}=M_f\Lambda.
\tag{5.14}
$$

Use the upstairs Markov property to express any finite-dimensional
expectation from $\Lambda_x$ as an alternating product of $H^h$ and
multiplications $M_{Uf_j}$. Move $\Lambda$ successively through this
product using (5.13)--(5.14). The result is exactly the corresponding
product of $S^0$ and $M_{f_j}$ from $x$. The same calculation with an
arbitrary bounded upstairs terminal test proves the conditional-kernel
statement given the past projected observations, on survival.
Adjoining the absorbing cemetery gives all cylinder distributions;
continuous paths before death and their cemetery tails determine the
killed path law. The height of a projection is the original height, so
its lifetime is identical pathwise.

Nevertheless $\rho=h_0^2$ is not basic at $k=k_*$, and its projected
angular drift is

$$
B_2=Q\log h_0
=-\frac{c(k)\epsilon v(k)\sin\beta}
 {1+\epsilon v(k)\cos\beta}.
\tag{5.15}
$$

At $k_*$, hidden phases $\pi/2$ and $3\pi/2$ give opposite nonzero
drifts. They are the admissible same-fiber rays of Input 4.1.
Hence Theorem 3.1 or the linear-jet test excludes all-start descent.
The reversible conditional kernel is proportional to $h_0^2\,d\beta$,
whereas (5.12) is proportional to $h_0\,d\beta$. Equality would force
$h_0$ constant on each fiber, contrary to (5.7) at $k_*$. Thus this is a
specified mixing law, not the canonical reversible conditional law.
$\square$

**Proposition 5.4 (canonical reversible mixing cannot evade rigidity).**
For the full contract (2.2), if the prescribed kernel in (5.5) is
$K_\rho=U^*$ and $S_t$ is a bounded base semigroup on $L^2(\nu)$, then
all four conditions of Theorem 3.1 hold and $S_t=S_t^{\rm av}$.
Likewise, if the projected processes started from $K_\rho(x,\cdot)$
for every base point form one Markov semigroup, that semigroup is already
the all-start quotient. A single chosen initial distribution, without
this assertion for every base point, is not covered by the conclusion.

Proof. From $K_\rho H_t=S_tK_\rho$ and $K_\rho U=1$ one gets
$S_t=U^*H_tU$. Each $S_t$ is therefore selfadjoint; taking Hilbert
adjoints of the intertwining gives $H_tU=US_t$. Thus completed
invariance holds, and Theorem 3.1 identifies the coefficient symmetry,
domains and all-start laws. Alternatively, for the second assertion the
one-time transition operators are exactly $C_t$ in (5.1). The Markov
semigroup assumption and the positive defect identity (5.3) imply
invariance even without assuming a full-kernel intertwining.
This explains why Proposition 5.3 needs a noncanonical fiber law.
Reversibility here means selfadjointness of the killed semigroup in the
original measure; it does not posit a stationary probability after
absorption. It is an essential qualification, not a permission to replace
that measure by a convenient average.
$\square$

## 6. Supplier correspondence and the retained mathematical boundary

**Mathematical citation 6.1 (general inputs and the native gap).** The
following general inputs are literature-attested. They are used inside
the preceding proofs and are not claimed as new general theorems.

| Primary source | Supplied input and its exact role here |
| --- | --- |
| [ELL] K. D. Elworthy, Y. Le Jan, X.-M. Li, *The Geometry of Filtering*, [arXiv:0810.2253v1](https://arxiv.org/pdf/0810.2253v1), Definition 2.0.6 and (2.1), p.19; Lemma 2.1.1 | Projectibility is the identity on pullbacks, and the symbol transforms by the tangent map. Here the smooth surjection is the product projection $\pi$, and its restriction to the horizontal frame is the invertible matrix $D$. This supplies the general projectability language and symbol test; it supplies neither (3.4)--(3.6) nor a killed-domain conclusion. The numbering quoted is that of this PDF version. |
| [ADO] W. Arendt, D. Dier, E. M. Ouhabaz, *Invariance of Convex Sets for Non-autonomous Evolution Equations Governed by Forms*, [arXiv:1303.1167v1](https://arxiv.org/pdf/1303.1167v1), Theorem 2.2, p.3 | Its sufficient closed-form criterion applies with constant time dependence, zero forcing, the closed subspace $\mathcal H$ and projection $\Pi$. The required completed-domain inclusion and cross-form inequality are proved in (3.10). The necessity used here is proved directly by generator differentiation, not attributed to the non-autonomous theorem. |
| [HR] S. Hochgerner, T. S. Ratiu, *Geometry of non-holonomic diffusion*, [arXiv:1204.6438v1](https://arxiv.org/pdf/1204.6438v1), Theorem 3.1, p.21, and Theorem 3.2, pp.24--25 | The first supplies smooth SDE existence, uniqueness up to explosion and its diffusion family; our noise fields are $\sqrt2Y_j$. The second is a symmetry-based path-space reduction supplier. Under (3.1), hidden-circle translations are a smooth proper free action, the noise fields and drift are invariant, and the noise representation can be trivial. The proof here additionally checks stopping at the common height exit and the Friedrichs realization. Neither theorem asserts the source-specific converse. |
| [H] Y. Colin de Verdière, L. Hillairet, E. Trélat, *Small-time asymptotics of hypoelliptic heat kernels near the diagonal, nilpotentization and related results*, Annales Henri Lebesgue 4 (2021), [DOI 10.5802/ahl.93](https://ahl.centre-mersenne.org/item/10.5802/ahl.93.pdf), §3.1.2, pp.918--920 | Selfadjoint semigroup and interior smooth-kernel facts apply to (3.12): a smooth positive measure, strong Hörmander fields, horizontal smooth drift and zero potential. The probabilistic interpretation on a larger manifold is localized using the absorbing part realization. This is not a theorem that equality almost everywhere automatically implies path equality at exceptional points; continuity and SDE uniqueness perform that step explicitly above. |

The absorbing-form correspondence is the regular strongly local
Dirichlet-form construction of a diffusion and its part on an open set;
see M. Fukushima, Y. Oshima, M. Takeda,
*Dirichlet Forms and Symmetric Markov Processes*, second edition,
[DOI 10.1515/9783110218091](https://doi.org/10.1515/9783110218091).
Its use here is also the one already embodied in [G, §§1--2]: closure of
the compact core, smooth positive full-support measure, and killing at
exit from the same open cylinder. The
regularity, locality, SDE uniqueness, boundary and pointwise-version
hypotheses needed in this application were checked in Theorem 3.1.

The repo-derived contribution is the classification for the full
variable-coefficient class of [G, Definition 1.3], especially the native
converse (3.3)--(3.6), its completed and all-start interpretation, and the
admissible separating tests. [N, (10.24)] already supplies the constant
all-start example; [B, chapter 10] already supplies the native quotient
and its complete partial domains. Neither that constant example nor the
narrower constant-coefficient family in [G, Definition 4.1] is substituted
for the full class. The general projection calculus, form-invariance
criterion, stochastic reduction and harmonic transformation are reused
methods. Their composition here is not a worldwide originality claim.

**Definition 6.2 (scope of the conclusion).** The classification concerns
only free analytic diffusion on this fixed interior cylinder and this
fixed native quotient. It makes no assertion about Green-potential energy,
attraction, stability thresholds, an amplitude memory space or a limit of
covariances. Equality of projected laws is not a preparation or acquisition
procedure. The stochastic covariance, density and time parameter are
additional analytic structure; they are not consequences of the original
finite-variation command law, and the proof constructs no CPTP
implementation of that nonlinear law.

The quantities retained from the source have different meanings:

| Quantity | Meaning in this contract |
| --- | --- |
| $3$ | Dimension of the full current-ray manifold $J\times\mathbb T^2$. |
| $2$ | Rank of the two direct native fields. |
| $(2,3)$ | Growth vector from their first nonzero bracket. |
| $4$ | Local bracket-weighted volume exponent, not the base dimension. |
| $2$ | Dimension of the bottom behavioral base $J\times\mathbb T$. |
| Persistent predictive information | Depends on the observation task: the hidden phase remains available to the middle-reference menu, and failures in §4 make it relevant to added free-law prediction even for a bottom quotient. |
| Physical axes | Require a separate source-to-space realization, measure, domain and clock correspondence absent from these hypotheses. |

The theorem neither selects the double-wall means nor identifies three
physical spatial axes. It supplies no new attraction classification,
precision bound, resource bound or Brownian-control preparation. A physical explanation of three spatial axes, and a classification of
Green-energy or amplitude-memory behavior, are not established by this
free-descent classification.

## 追加锚（本行以下为增补区）

## 7. The native central period and the unchanged full endpoint

**Definition 7.1 (two carriers and their source data).** Retain the native
source of Definitions 1.1--1.2, writing $H_{\rm n}=r/2$ for its upper
height wall, so that $L$ can denote the endpoint differential operator.
Fix one preparation height $k_0\in(0,H_{\rm n})$, preparation coordinates
$(\alpha_0,\beta_0)$ and all the original preparation rotations. No
preparation parameter varies with an unknown input. The mathematical
suppliers in this section and §§8--10 are taken at revision
`69eee5580efb61cf70564cc46a0fa24fc18351dd`.

Write [E] for [the original endpoint appendix, §112](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md#112-the-original-maximal-domain-selector-and-the-full-endpoint-propagation-limit)
and [S] for [its positivity and source-contact continuation, §§115--116](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md#115-positivity-and-the-full-ground-state-form-of-the-actual-endpoint).
Their endpoint data are exactly

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad
(x,y,z,w)(x',y',z',w')
 =(x+x',y+y',z+z',w+w'+xy'),\\
d\mu=dx\,dy\,dz\,dw,\qquad
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\qquad L=-\sum_{i=1}^3X_i^2,\\
L\Gamma=\delta_e,\qquad \deg\Gamma=-3,\qquad
a,\eta>0,\qquad g_c=16\sqrt{a\eta},\\
S_{\min}=(aL-\eta\partial_w^2-g_c\Gamma)
                 |_{C_c^\infty(G\setminus\{e\};\mathbb C)}.
\end{gathered}
\tag{7.1}
$$

The notation $S_{\min}$ distinguishes this operator from reference [S].
Let $h$ be the supplied coefficient-positive, $L^2(\mu)$-normalized zero
state, $c_h=C(h)>0$ and $\rho_*=A(h)/C(h)$. The full endpoint, its
transform and their entire complex domains remain

$$
\begin{gathered}
D(H)=\{u\in D(S_{\min}^*):A(u)=\rho_*C(u)\},\qquad
Hu=S_{\min}^*u,\\
m=h^2\mu,\qquad J_hv=hv,\qquad
K=J_h^{-1}HJ_h,\qquad T_t=e^{-tK},\\
\mathscr V=\mathscr V_0\dotplus\mathbb C1,\qquad
D(K)=\{v\in\mathscr V:hv\in D(S_{\min}^*),
                            A(hv)=\rho_*C(hv)\}.
\end{gathered}
\tag{7.2}
$$

Here $\mathscr V_0$ and the integral energy are precisely [S, (115.14)--(115.15)].
In particular $m(G)=1$, $T_t$ is conservative and selfadjoint in $L^2(m)$,
and $h$ is smooth and positive on $G\setminus\{e\}$. A source start
always means the legitimate version of [S, Theorem 116.4]. There is no
ordinary value $h(e)$ in these definitions. All Hilbert pairings below
are antilinear in their first slot.

Set $c_0=1/2-k_0/r$ and $\ell=2\pi r$. The slab and the intermediate
quotient are

$$
\begin{gathered}
\mathcal S=\{-k_0<x<H_{\rm n}-k_0\}\subset G,\qquad
d_n=(0,0,0,n\ell),\\
\mathcal B_\ell=G/\{d_n:n\in\mathbb Z\},\qquad
\pi_\ell:G\longrightarrow\mathcal B_\ell,\qquad b_0=\pi_\ell(e),\\
\Psi(x,y,z,w)
 =\bigl(k_0+x,[\alpha_0+y/2],
                    [\beta_0+c_0y-w/r]\bigr),\qquad p\in\mathcal S.
\end{gathered}
\tag{7.3}
$$

Both brackets reduce modulo $2\pi$. The quotient retains real $y,z$;
only $w$ is reduced modulo $\ell$.

**Proposition 7.2 (the supplied chronology gives this actual slab map).**
The map (7.3) preserves every original command and its entire prefix
guard wherever the command is lawful. It preserves all ten original
signed doubled coherence outputs there. Central translation by $d_n$
is an actual kernel of these native partial-action formulas. These
assertions identify neither $\mathcal B_\ell$ with the native ray
manifold nor the full endpoint dynamics with native command dynamics.

Proof. For a relative command $\gamma=(a_c,b_c)$ put
$A=a_c(T)$, $B=b_c(T)$ and $J=\int a_c\,db_c$. Regard its chronological
triple as $c_\gamma=(A,B,0,J)\in G$. Right multiplication gives

$$
p c_\gamma=(x+A,y+B,z,w+J+xB).
\tag{7.4}
$$

Substitution into (7.3), at native height $k=k_0+x$, gives exactly

$$
\Psi(p c_\gamma)
 =\bigl(k+A,[\alpha+B/2],
               [\beta+(1/2-k/r)B-J/r]\bigr).
\tag{7.5}
$$

This is [N, Theorem 9.3], equivalently (1.6), with the same sign and
the same real area $J$. For every prefix replace $(A,B,J)$ by
$(a_c(t),b_c(t),\int_0^t a_c\,db_c)$. The whole lifted path remains
in $\mathcal S$ exactly when

$$
k+\min_{[0,T]}a_c>0,\qquad
k+\max_{[0,T]}a_c<H_{\rm n}.
\tag{7.6}
$$

For two commands, the chronological product is
$(A+A',B+B',0,J+J'+AB')$, just as in [N, (9.12)]. Its allowed
domain is the first guard intersected with the inverse image of the
second guard under the first action. Thus (7.5) respects concatenation
with actual refusal domains, rather than just endpoint membership.
Differentiating (7.3) gives

$$
D\Psi X_1=P,\qquad D\Psi X_2=Q,\qquad
D\Psi X_3=0,\qquad D\Psi\partial_w=-r^{-1}\partial_\beta.
\tag{7.7}
$$

In particular $z$ is an extra endpoint coordinate, not a third original
control supplied by this map.

For completeness, the exact output formula can be written without
changing the fixed rotations. In edge order
$((0,1),(0,2),(0,3),(1,13),(3,13))$, let
$\delta_e=\theta_i^{\rm ref}-\theta_j^{\rm ref}$ denote those rotations.
With $u(t)=(\cos t,\sin t)$, the five pairs are

$$
\begin{aligned}
Y_{01}&=2\sqrt{k(H_{\rm n}-k)}\,u(\delta_{01}+\alpha),\\
Y_{02}&=2\sqrt{Zk}\,u(\delta_{02}+\beta),\\
Y_{03}&=2\sqrt{k(H_{\rm n}-k)}\,u(\delta_{03}+\alpha),\\
Y_{1,13}&=2\sqrt{k(H_{\rm n}-k)}\,u(\delta_{1,13}-\alpha),\\
Y_{3,13}&=2\sqrt{k(H_{\rm n}-k)}\,u(\delta_{3,13}-\alpha).
\end{aligned}
\tag{7.8}
$$

The probabilities are still $(k,H_{\rm n}-k,Z,H_{\rm n}-k,k)$.
These are the signed outputs of [N, §8.3] and [Native continuation,
Definition 2.1 and Lemma 2.2](FIB_NATIVE_CONTINUATION_AFFINE_OBSTRUCTION_AND_APPROXIMATION.md#2-the-original-outputs-and-the-reused-static-result).
Fixed coordinate offsets $(\alpha_0,\beta_0)$ are included in (7.3);
they impose no equality of preparation phases. Equations (7.5) and
(7.8) prove preservation of the complete menu, with no whitening.

Replacing $w$ by $w+n\ell$ changes $\beta$ by $-2\pi n$ and leaves
everything in (7.5)--(7.8) unchanged. This period is native: at any
interior starting height choose a nonzero height displacement $d$
whose segment stays interior, and execute the four legs
$(0,0)\to(d,0)\to(d,t)\to(0,t)\to(0,0)$ in command coordinates.
Their $A=B=0$ and $J=dt$; choosing $t=n\ell/d$ realizes this central
increment by a finite original history. The choice of $d$ can also
serve a compact interior promise of starting heights. It does not
make that one history lawful at every height in the full open source.
Equality of central endpoint formulas does not erase excursion guards.

The distinct points $\pi_\ell(x,y,z,w)$ and
$\pi_\ell(x,y,z',w)$ already have the same image under $\Psi$ when
$z\ne z'$. Additional identifications involving the $y$ period also
remain. Finally $\Psi$ has no native positive-height meaning outside
$\mathcal S$. Thus $\mathcal B_\ell$ is only the stated intermediate
test carrier. $\square$

**Definition 7.3 (arbitrary fiber mixing and its operator types).** A
candidate is a Borel probability kernel $\Lambda$ from $\mathcal B_\ell$
to $G$ satisfying

$$
\Lambda_b(\pi_\ell^{-1}\{b\})=1,\qquad
\Lambda_{b_0}=\delta_e,
\tag{7.9}
$$

and a conservative Markov semigroup $Q_t$ on $\mathcal B_\ell$ with

$$
\Lambda T_t=Q_t\Lambda
\quad(t\ge0)
\tag{7.10}
$$

on all bounded complex Borel functions on $G$. At this stage the
operators have types
$U:\mathscr B_b(\mathcal B_\ell)\to\mathscr B_b(G)$,
$Uf=f\circ\pi_\ell$, and
$\Lambda:\mathscr B_b(G)\to\mathscr B_b(\mathcal B_\ell)$.
Fiber support gives $\Lambda U=I$. No Hilbert adjoint or density of
$\Lambda$ is assumed. Transition versions at the source are those
of (7.2); properly exceptional sets away from the source are understood
as in [S, Theorems 116.3--116.4].

## 8. One original source forces the fiber probabilities

**Proposition 8.1 (source occupation forces the reversible conditional law).**
For the fixed endpoint and source of Definition 7.1, a candidate in
Definition 7.3 necessarily satisfies

$$
m=\nu\Lambda,\qquad \nu=(\pi_\ell)_*m.
\tag{8.1}
$$

Consequently $\Lambda$ is the conditional law of $m$ on the fibers,
$\nu$-almost everywhere, although this was not a hypothesis. More
explicitly choose the Borel section
$s(b)=(x,y,z,\bar w)$ with $0\le\bar w<\ell$, and put
$q_n(b)=s(b)d_n$. Relative to raw quotient measure
$d\bar\mu=dx\,dy\,dz\,d\bar w$, define

$$
\begin{gathered}
S(b)=\sum_{n\in\mathbb Z}h(q_n(b))^2,\qquad
d\nu=S\,d\bar\mu,\\
p_n(b)=\frac{h(q_n(b))^2}{S(b)}.
\end{gathered}
\tag{8.2}
$$

These are defined on the common full-measure set where $0<S<\infty$
and $b\ne b_0$. On that set
$\Lambda_b=\sum_n p_n(b)\delta_{q_n(b)}$.
For every discount $\lambda>0$, use precisely [S, (115.4), (116.1)]
with that discount:

$$
\begin{gathered}
n_\lambda=h-\lambda(F+\lambda)^{-1}h,\qquad
b_\lambda=n_\lambda/h,\qquad d_\lambda=\int_G b_\lambda\,dm,\\
S_\lambda(b)=\sum_n b_\lambda(q_n(b))h(q_n(b))^2.
\end{gathered}
\tag{8.3}
$$

Here $F$ is the supplied Friedrichs operator used in the exact full
resolvent formula, not a replacement for $H$ or $K$. For each fixed
$\lambda$, a candidate must also satisfy, for $\nu$-almost every $b$,

$$
\Lambda_b(\{q_n(b)\})
 =\frac{b_\lambda(q_n(b))h(q_n(b))^2}{S_\lambda(b)}
 =p_n(b)\quad(n\in\mathbb Z).
\tag{8.4}
$$

In particular the same fixed fiber probabilities must disintegrate every
discounted original source response. Null sets in (8.4) may depend on
$\lambda$; no uncountable intersection is asserted.

Proof. The source response [S, (116.14)] gives the probability measure

$$
\zeta_\lambda(dq)
 :=\lambda\int_0^\infty e^{-\lambda t}T_t(e,dq)\,dt
 =\frac{b_\lambda(q)}{d_\lambda}\,m(dq).
\tag{8.5}
$$

This is a trace-defined source response, not evaluation of a formula
containing $h(e)$. The supplied $0\le b_\lambda\le1$ and
$d_\lambda>0$ give its positivity and normalization. The spectral
limit already established in [S, (116.12)] says

$$
\|b_\lambda-1\|_{L^2(m)}
 =\|\lambda(F+\lambda)^{-1}h\|_{L^2(\mu)}\longrightarrow0,
\qquad d_\lambda\longrightarrow1
\quad(\lambda\downarrow0).
\tag{8.6}
$$

It uses $\ker F=\{0\}$, not a positive spectral gap. Since $m$ is a
probability measure, (8.6) implies convergence of (8.5) to $m$ in total
variation. For the norm $\|\sigma\|_{\rm TV}=\sup_{|f|\le1}|\sigma f|$,
one explicit bound is

$$
\|\zeta_\lambda-m\|_{\rm TV}
 \le\frac{\|b_\lambda-1\|_{L^1(m)}+|1-d_\lambda|}{d_\lambda}
 \longrightarrow0.
\tag{8.7}
$$

Now (7.9)--(7.10), applied at $b_0$, give equality of transition
measures

$$
T_t(e,\cdot)=Q_t(b_0,\cdot)\Lambda,\qquad
Q_t(b_0,\cdot)=(\pi_\ell)_*T_t(e,\cdot).
\tag{8.8}
$$

The second identity uses fiber support. It also ensures the time
measurability needed to integrate this base law, directly from the
legitimate source transition function. Put
$\nu_\lambda=(\pi_\ell)_*\zeta_\lambda$. Integrating (8.8) yields
$\zeta_\lambda=\nu_\lambda\Lambda$. Pushforward and application of a
probability kernel contract total variation, so

$$
\|\nu_\lambda-\nu\|_{\rm TV}
 \le\|\zeta_\lambda-m\|_{\rm TV},\qquad
\|\nu_\lambda\Lambda-\nu\Lambda\|_{\rm TV}
 \le\|\nu_\lambda-\nu\|_{\rm TV}.
\tag{8.9}
$$

Taking limits proves (8.1). Thus one fixed original source, through its
entire time-homogeneous response, has forced the conditional law of
the invariant measure. No density, continuity or reversibility of
$\Lambda$ was used.

Tonelli applied to the countable cells of raw Haar measure gives
$\int S\,d\bar\mu=\|h\|_2^2=1$. Smooth positivity of $h$ off $e$
makes $S>0$ almost everywhere. Therefore $S$ is finite and positive
almost everywhere and $\nu$ is equivalent to $\bar\mu$. A kernel
supported on the fiber is a countable sum with Borel weights
$\lambda_n(b)=\Lambda_b(\{q_n(b)\})$; the graphs of the Borel sections
$q_n$ are Borel, which verifies measurability of these weights. Apply
(8.1) to the Borel sets $\{q_n(b):b\in E\}$ for arbitrary Borel $E$.
Their two measures have densities $h(q_n(b))^2$ and
$S(b)\lambda_n(b)$ relative to $\bar\mu$. Equality gives (8.2),
simultaneously for the countably many $n$.

The same argument applied to
$\zeta_\lambda=\nu_\lambda\Lambda$ gives the first expression in
(8.4) wherever $S_\lambda>0$. To check that this is a full
$\nu$-measure set, note that $n_\lambda$ is nonnegative, nonzero,
smooth on $G\setminus\{e\}$ and solves
$(S_{\min}^*+\lambda)n_\lambda=0$ there. The first two assertions
are [S, Theorem 115.2]; smoothness follows by interior elliptic
regularity from (8.3). The local principal matrix is the supplied
positive matrix (115.10), and the local potential is smooth and
bounded. The elliptic Harnack principle on connected
$G\setminus\{e\}$ therefore makes $n_\lambda$ strictly positive
there, just as for $h$ in [S, Theorem 115.2]. Consequently
$b_\lambda>0$ off $e$, and $\zeta_\lambda$ is equivalent to $m$.
Their pushforwards $\nu_\lambda$ and $\nu$ are equivalent. Also
$\int S_\lambda\,d\bar\mu=d_\lambda<\infty$. This proves all
claims in (8.4). It additionally forces
$b_\lambda(q_n(b))=S_\lambda(b)/S(b)$ for all $n$, almost everywhere.

The fiber above $b_0$ is countable and has $m$-measure zero, so
$\nu(\{b_0\})=0$. The proof assigns no ordinary value to $h(e)$ and
does not contradict $\Lambda_{b_0}=\delta_e$ by changing an
almost-everywhere conditional version at that null base point. Its
consequence is instead the global identity (8.1). $\square$

## 9. Full-domain exclusion of the arbitrary Borel route

**Theorem 9.1 (no source-anchored fiber-kernel intertwining).** For every
actual original $0<Z<1$, every fixed preparation in Definition 7.1 and
every fixed original $a,\eta>0$, there is no candidate in Definition
7.3. This excludes arbitrary Borel probability kernels supported on
these central fibers, with no smoothness, finite-support, affine or
canonical-kernel hypothesis. It concerns the original conservative
full endpoint and its original clock.

Proof. Assume a candidate exists. Proposition 8.1 first supplies the
Hilbert-space structures that were not assumed for that candidate.
The pullback is an isometry
$U:L^2(\mathcal B_\ell,\nu;\mathbb C)\to L^2(G,m;\mathbb C)$;
its closed range $\mathcal H_\ell$ consists of basic functions. Jensen's
inequality and $\nu\Lambda=m$ make
$\Lambda:L^2(m)\to L^2(\nu)$ a contraction. For bounded inputs,
fiber support and (8.1) give

$$
\langle Uf,F_1\rangle_m=\langle f,\Lambda F_1\rangle_\nu,
\qquad U^*=\Lambda,\qquad \Pi=UU^*.
\tag{9.1}
$$

Density extends these statements to the displayed Hilbert spaces;
$\Lambda$ in (9.1) means its almost-everywhere operator class. For
any properly exceptional set $N$ of [S], $m(N)=0$ and $e\notin N$.
Equation (8.1) gives $\Lambda_b(N)=0$ for $\nu$-almost every $b$.
Thus the Hilbert argument uses only legitimate transition versions,
while (8.8) uses the legitimate source start. For each bounded base $f$,

$$
\nu Q_t f=\nu\Lambda T_tUf=mT_tUf=mUf=\nu f.
\tag{9.2}
$$

Hence $Q_t$ is an $L^2(\nu)$ contraction by Jensen, and the bounded-Borel
intertwining extends to these $L^2$ spaces. Multiplying it by $U$ gives

$$
Q_t=U^*T_tU=Q_t^*,\qquad
U^*T_t=Q_tU^*,\qquad T_tU=UQ_t.
\tag{9.3}
$$

The last equality is the Hilbert adjoint of the middle one, using the
first and the supplied selfadjointness of $T_t$. Strong continuity of
$Q_t$ also follows from its compression formula. Thus $\mathcal H_\ell$
and $\mathcal H_\ell^\perp$ reduce the actual $T_t$ and its generator
$K$. This is the adjoint argument of Proposition 5.4; its canonical
premise has now been proved from the source, rather than presumed.
The cylinder coefficient classification of Theorem 3.1 is not being
transferred to this different carrier or domain.

We next test this reduction by vectors genuinely in the full domain
(7.2). Write $Dq=qd_1$ and take any
$q\in G\setminus\{e,d_{-1}\}$. Choose a relatively compact open
coordinate box $O$ about $q$, small enough that $\pi_\ell$ is injective
on $O$, $O$ and $DO$ are disjoint, and both closures avoid $e$.
For any real $\varphi\in C_c^\infty(O)$ define a function on $G$ by

$$
W(p)=\frac{\varphi(p)}{h(p)^2}\quad(p\in O),\qquad
W(Dp)=-\frac{\varphi(p)}{h(Dp)^2}\quad(p\in O),
\qquad W=0\text{ elsewhere}.
\tag{9.4}
$$

Compact support of $\varphi$ makes these prescriptions smooth across
the boundaries of the two boxes. Positivity of $h$ there gives
$W\in C_c^\infty(G\setminus\{e\})$. More specifically,
$hW\in C_c^\infty(G\setminus\{e\})\subset D(H)$ with
$A(hW)=C(hW)=0$. Thus $W\in D(K)$ for the actual selector (7.2).
This is a test in the full operator, not a claim that its domain is
the Friedrichs domain or the punctured core alone.

For every bounded basic $Uf$, the contributions of the two boxes to
$\langle Uf,W\rangle_m$ cancel exactly: raw Haar measure is unchanged
by $D$ and $Uf(Dp)=Uf(p)$. Density gives $W\in\mathcal H_\ell^\perp$.
Reduction and $W\in D(K)$ give $KW\in\mathcal H_\ell^\perp$.
For example, this follows by taking the $L^2$ limit of
$(I-T_t)W/t$ inside that closed orthogonal complement. Therefore

$$
\langle Uf,KW\rangle_m=0
\tag{9.5}
$$

for every bounded base $f$, without a generator-domain assumption on
its periodic pullback.

On either compact box the actual generator applied to $W$ is
$K W=-\mathcal D_h W$, where the supplied ground-transform formula is

$$
\mathcal D_h v
 =a\sum_{i=1}^3 X_i^2v+\eta\partial_w^2v
   +2a\sum_{i=1}^3(X_i\log h)X_iv
   +2\eta(\partial_w\log h)\partial_wv.
\tag{9.6}
$$

Choose now $f\in C_c^\infty(\mathcal B_\ell;\mathbb R)$, smooth on
the quotient manifold. Its pullback is smooth and bounded, although
it need not be in $D(K)$ or have compact support on $G$. All uses of
integration by parts below are on the compact support of $W$ away
from $e$. Local weighted divergence symmetry of (9.6), or its direct
product-rule expansion, gives from (9.5)

$$
0=\int_G (Uf)KW\,dm
 =-\int_O\varphi(p)
       \{\mathcal D_h(Uf)(p)-\mathcal D_h(Uf)(Dp)\}\,d\mu(p).
\tag{9.7}
$$

There is no source or infinity boundary term. In particular (9.7) is
deduced from full-domain semigroup reduction and a valid $D(K)$ test;
it is not differentiation of an unverified global periodic test in
the generator domain. Since $\varphi$ is arbitrary and the difference
is smooth, (9.7) proves equality of the two generator expressions
pointwise on $O$ for every such $f$.

All second-order coefficients in (9.6) are already invariant under
$D$. There is no symbol-rank comparison here. Put

$$
\Delta_i(p)=(X_i\log h)(p)-(X_i\log h)(Dp),\qquad
\Delta_w(p)=(\partial_w\log h)(p)-(\partial_w\log h)(Dp).
$$

On the common quotient chart choose cutoff base tests with any
prescribed first derivatives at $\pi_\ell(p)$. Subtracting (9.6) in
(9.7) makes their coefficients

$$
2a\Delta_1,\quad 2a\Delta_2,\quad 2a\Delta_3,
       \quad 2ax\Delta_2+2\eta\Delta_w
\tag{9.8}
$$

in coordinate order $(x,y,z,w)$. Their vanishing, with $a,\eta>0$,
forces every $\Delta_i$ and $\Delta_w$ to be zero. Since
$\partial_y=X_2-x\partial_w$, this says

$$
\nabla\{\log h(Dp)-\log h(p)\}=0
\qquad(p\in G\setminus\{e,d_{-1}\}).
\tag{9.9}
$$

That punctured space is connected: its underlying manifold is
$\mathbb R^4$ with two points removed. Both logarithms are smooth
there. Thus a single constant $c>0$ satisfies

$$
h(Dp)=c\,h(p)\quad(p\ne e,d_{-1}).
\tag{9.10}
$$

Even a nonunit constant cannot coexist with the supplied $L^2(\mu)$
normalization. Choose a bounded box $E$ of positive measure with its
$w$ coordinate strictly between $0$ and $\ell$, away from $e$.
Its translates $D^nE$ are disjoint. Iterating (9.10), ignoring the
irrelevant countable source orbit if necessary, gives

$$
0<\int_E h^2\,d\mu<\infty,\qquad
\int_{D^nE}h^2\,d\mu
   =c^{2n}\int_Eh^2\,d\mu\quad(n\in\mathbb Z).
\tag{9.11}
$$

The bilateral sum $\sum_{n\in\mathbb Z}c^{2n}$ diverges for every
$c>0$, contradicting $\|h\|_2^2=1$. This is the familiar repeated-cell
$L^2$ argument, used already in [G, Proposition 11.1], with its
necessary constant-multiplier variant included. The new step leading
to it was the forced conditional law from one legitimate source and
the full-domain paired tests, not a new periodic-amplitude obstruction.
This contradiction proves the theorem. $\square$

## 10. Literature correspondence and the exact surviving scope

**Mathematical citation 10.1 (standard tools and source-specific content).**
The intertwining convention is the standard one in S. Pal and
M. Shkolnikov, [*Intertwining diffusions and wave equations*,
arXiv:1306.0857v2, §1, Definitions 1--2](https://arxiv.org/html/1306.0857v2#S1).
Their stochastic link $L$ is $\Lambda$ here, their upstairs semigroup
$P_t$ is the present $T_t$, their downstairs semigroup $Q_t$ has the
same role as here, and their equation $Q_tL=LP_t$ is (7.10). The
initial conditional law at the distinguished base source is exactly
$\Lambda_{b_0}=\delta_e$. The state spaces here are $G$ and
$\mathcal B_\ell$, with a link concentrated on a countable covering
fiber, not a density with respect to four-dimensional Lebesgue
measure. Consequently the differentiable link-density and joint
diffusion hypotheses of their Theorems 1--2 are not assumed or used.
No regularity of $Q_t$ is supplied by analogy with their SDEs.

Their convention (1.1)--(1.2) puts a factor $1/2$ before a covariance
matrix. In the present local formula that matrix is twice

$$
\begin{pmatrix}
a&0&0&0\\
0&a&0&ax\\
0&0&a&0\\
0&ax&0&ax^2+\eta
\end{pmatrix},
\tag{10.1}
$$

and the drift is precisely the first-order part of (9.6). This is
only the parameter correspondence off the source. The full operator
and source response are (7.2) and (8.5), not an SDE extension inferred
from that matrix. The discount $\lambda$ in (8.5) multiplies the
original time $t$; it does not rescale it.

Uniqueness of conditional laws on standard Borel spaces, contraction
of total variation by kernels, Jensen's inequality, Hilbert adjoints
and the spectral theorem are established tools. Their elementary
uses are shown in (8.5)--(9.5). The source input that makes them
decisive is specifically [S, (116.12)--(116.14)] for the actual selector
(112.5). Proposition 5.3 shows why an arbitrary mixing law cannot
be assumed reversible in the general killed native class. Proposition
8.1 proves that premise for this conservative source-anchored candidate;
the adjoint step then reuses Proposition 5.4's mechanism. The endpoint
application and its source-forced weights (8.2)--(8.4), together with
the full-domain test (9.4)--(9.9), are repo-derived ordinary deductions.
Neither standard intertwining theory nor the reused periodic-source
observations alone supply that deduction. No worldwide priority or
Lean certification is asserted.

**Definition 10.2 (carrier and operation boundaries).** The native
guarded lift, its lifetime approximations and its real chronological
area are supplied by [Guarded lift limits, §§2--4](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#2-the-original-source-its-guard-and-its-entire-chronological-path).
They retain finite lawful histories and their separate stochastic-law
premises. The free hidden-circle rigidity of §§1--6, the
[variable-coefficient Green model, §§1--3](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md#1-fixed-model-and-the-exact-question),
and the [central-noise model, Definitions 1.1--1.2](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md#1-fixed-source-conditional-law-and-the-matched-operator)
use native phase cylinders with inherited height killing. Their
central noise, source density and kinetic normalization are not the
global $a,\eta,\Gamma,h$ of (7.1)--(7.2). The
[spatial-cap source form, Proposition 5.2](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md#5-the-natural-logarithmic-source-form-and-positive-point-capacity)
and its [all-real cap limit, Theorem 12.1](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md#12-the-all-real-parameter-operator-limit)
also retain different outer domains and source pairs. No identification
of their parameters, clocks, walls or operators is used here.

Theorem 9.1 excludes one fixed, time-homogeneous probabilistic
intertwining through the actual native central period, anchored at the
one original endpoint source. It does not exclude time-dependent or
history-conditioned posterior kernels, retained real-area histories,
or source-law representations with a different state contract. In
particular the exact nonlinear pure-state action and its lawful
pushforward on retained source laws in [B, §12.3](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY_CONTINUATION.md#123-the-surviving-nonlinear-state-and-source-law-action)
remain intact; their Theorem 12.2 is a distinct affine/CPTP result and
is not an antecedent of this proof.

Failure on $\mathcal B_\ell$ alone proves nothing about all coarser
quotients: a link from a coarser space need not factor through a
fiber-supported link on this intermediate covering. The map $\Psi$
continues to have precisely its slab domain and native readouts; it
has not become a map of the full endpoint into the positive native
source. A full native source/evolution/representation/readout
correspondence, and a determination of physical spatial dimension,
remain unresolved.

## 追加锚（本行以下为增补区）

## 11. The actual preparation fiber and its false-source polarity

**Definition 11.1 (the unchanged source and a restricted observation).**
Retain all data of Definition 7.1: every $0<Z<1$, $r=1-Z$,
$H_{\rm n}=r/2$, every preparation height $k_0\in(0,H_{\rm n})$,
all its fixed preparation rotations and coordinates
$(\alpha_0,\beta_0)$, and the original $a,\eta>0$. The endpoint is
exactly (7.1)--(7.2), with raw Haar measure, the unit-source
$\Gamma$, $g_c=16\sqrt{a\eta}$, the full complex selector (112.5),
and the coefficient-positive normalized $h$. Write
$(\mathscr E,\mathscr V)$ for its entire transformed form
[S, (115.15)] on $L^2(G,m;\mathbb C)$, $m=h^2\mu$, and
$\mathbf Z_t$ for the conservative diffusion of [S, §116].
Probability statements use the real form of this same complex form.

Let $\mathcal R:J\times\mathbb T^2\to\mathbb R^{10}$ be exactly the
five ordered pairs in (7.8), with their signed components, factors two
and original rotations. Put

$$
q_0=(k_0,[\alpha_0],[\beta_0]),\qquad
v_0=\mathcal R(q_0),\qquad
\Phi=\mathcal R\circ\Psi\quad\hbox{on }\mathcal S.
\tag{11.1}
$$

Choose any closed height interval $I=[l,u]\Subset J$ with
$l<k_0<u$, and define

$$
\begin{gathered}
D_I=\{p\in G:l<k_0+x(p)<u\},\qquad
\theta_I=\inf\{t\ge0:\mathbf Z_t\notin D_I\},\\
E_I=\mathcal R(I\times\mathbb T^2),\qquad
O_t^I=\Phi(\mathbf Z_{t\wedge\theta_I}).
\end{gathered}
\tag{11.2}
$$

The last expression at a finite exit uses the continuous extension of
$\Phi$ to $\overline D_I$, which is still inside the native slab.
It is held at that exit value. If $\theta_I=\infty$, there is no
holding. This stops only an observation: $\mathbf Z$ remains the
original conservative full process after $\theta_I$.
All original commands still have precisely their entire domains (1.5)
and (7.6), with their prefix guards and actual periods. The interval
$I$ is an additional observation restriction, not a new source
condition or a replacement for those command domains.

**Theorem 11.2 (the exact fiber and polarity for the full endpoint form).**
For every parameter and preparation of Definition 11.1, the complete
preparation-output fiber on $\mathcal S$ is

$$
\begin{gathered}
\mathfrak F=\Phi^{-1}\{v_0\}
 =\bigcup_{j,n\in\mathbb Z}
   \{(0,4\pi j,z,4\pi r c_0j-2\pi rn):z\in\mathbb R\},\\
c_0=\tfrac12-k_0/r,\qquad
\mathfrak F_{\rm false}=\mathfrak F\setminus\{e\},\qquad
\operatorname{Cap}_1(\mathfrak F_{\rm false})=0
 <\operatorname{Cap}_1(\{e\}).
\end{gathered}
\tag{11.3}
$$

Capacity is for the entire form $(\mathscr E,\mathscr V)$, not for
an off-source replacement process. There is one properly exceptional
set $N$ for the full diffusion, containing $\mathfrak F_{\rm false}$,
with $e\notin N$, such that for every $p\in G\setminus N$,

$$
\mathbb P_p\{\mathbf Z_t\in G\setminus N
                  \hbox{ for every }t\ge0\}=1.
\tag{11.4}
$$

The full lifetime, source regularity, contact and zero-residence
statements of [S, Theorems 116.3--116.4] hold with this same $N$.
In particular, for any $I$ as above and $p\in D_I\setminus N$,

$$
\mathbb P_p\{\,O_t^I=v_0
       \ \Longleftrightarrow\ (t<\theta_I\hbox{ and }\mathbf Z_t=e)
                       \hbox{ for every }t\ge0\,\}=1.
\tag{11.5}
$$

**Proof.** From the actual second pair of (7.8),

$$
k=\frac{|Y_{02}|^2}{4Z}.
\tag{11.6}
$$

Thus equality of the ten outputs first forces $k=k_0$; the symmetry
$k\leftrightarrow H_{\rm n}-k$ of the bottom amplitude creates no
second height in this fiber. At this height the positive amplitudes
$2\sqrt{k_0(H_{\rm n}-k_0)}$ and $2\sqrt{Zk_0}$ make equality
of $Y_{01}$ and $Y_{02}$ equivalent to
$[\alpha]=[\alpha_0]$ and $[\beta]=[\beta_0]$ respectively.
The fixed rotations cancel in each comparison, without being set
equal to one another. The other three pairs then agree as well.
Substitute (7.3). Its first two conditions are $x=0$ and $y=4\pi j$.
Its last is $c_0y-w/r=2\pi n$, giving exactly (11.3).
The coordinate $z$ is unrestricted. This includes the entire line
$\{(0,0,z,0):z\in\mathbb R\}$ through $e$, not just the discrete
central orbit used in §§7--9.

Here is a local capacity estimate for all of this false fiber.
Exhaust each line in (11.3), with $e$ omitted, by countably many
compact segments having positive distance from $e$. For the line
through $e$, use separate positive and negative $z$ segments bounded
away from zero. Fix one segment $C$ on the line with constants
$y_j=4\pi j$ and $w_{jn}=4\pi r c_0j-2\pi rn$. Choose a smooth
compact $z$ cutoff $\chi$ equal to one near its $z$ interval and a
smooth compact cutoff $\xi$ on $\mathbb R^3$ equal to one near zero.
For sufficiently small $\epsilon>0$ put

$$
u_\epsilon(x,y,z,w)
 =\chi(z)\xi\bigl((x,y-y_j,w-w_{jn})/\epsilon\bigr).
\tag{11.7}
$$

Choose these cutoffs with support in one fixed compact subset of
$G\setminus\{e\}$. In the line-through-$e$ case this is possible
because the $z$ support avoids zero. In all other cases the fixed
normal displacement from that line to $e$ is nonzero. Then
$u_\epsilon\in C_c^\infty(G\setminus\{e\};\mathbb R)
\subset\mathscr V_0\subset\mathscr V$ and is one near $C$.
Smooth positivity of $h$ on this compact set and boundedness of the
principal matrix (10.1) give a constant $C_1$, independent of small
$\epsilon$, for which

$$
\|u_\epsilon\|_{L^2(m)}^2\le C_1\epsilon^3,\qquad
\mathscr E[u_\epsilon]\le C_1(\epsilon+\epsilon^3).
\tag{11.8}
$$

Indeed there are three normal coordinates of volume order
$\epsilon^3$; each normal derivative has size at most
$C/\epsilon$, and the $z$ derivative is bounded. The local energy
is bounded above by a constant times the ordinary Euclidean gradient
integral. This uses the full integral form [S, (115.15)] on these
punctured tests. It does not split any singular kinetic or potential
energy at $e$. The variational definition of outer capacity gives
$\operatorname{Cap}_1(C)=0$. Countable subadditivity over the stated
segments proves the zero capacity of $\mathfrak F_{\rm false}$.
The last strict inequality in (11.3) is exactly
[S, (116.4)], with discount one; it is reused here.

For a regular symmetric Dirichlet form, a Borel set of zero shifted
capacity is contained in a properly exceptional set. Its complement
is invariant for the associated process, so avoidance holds for all
times from every start in that complement. These are the standard
capacity/exceptional-set facts of Fukushima--Oshima--Takeda,
*Dirichlet Forms and Symmetric Markov Processes*, second edition,
[Chapters 2 and 4](https://doi.org/10.1515/9783110218091).
The capacity and exceptional-set conventions are also stated in
Chen--Fukushima--Ying,
[*Traces of symmetric Markov processes and their characterizations*,
arXiv:math/0606784v1, §2 and Appendix](https://arxiv.org/pdf/math/0606784v1).
Apply them to the full regular form supplied in [S, Theorem 115.3].
Take such an envelope together with the properly exceptional set in
[S, Theorems 116.3--116.4]. A countable union of properly exceptional
sets is properly exceptional. None can contain the nonpolar $e$.
Conservation gives (11.4) with all $t\ge0$, including the source start.
In particular this is one pathwise avoidance statement, rather than
separate almost-everywhere assertions for each deterministic time.

Before $\theta_I$, equality of the outputs is equivalent to membership
in $\mathfrak F$, whose only attainable point on these paths is $e$.
If $\theta_I<\infty$, path continuity makes its height either $l$ or
$u$. Formula (11.6) distinguishes either from $k_0$, also for the
subsequent held path. This proves (11.5). The set $N$ does not depend
on $I$; the same avoidance event proves the assertion for each such
observation restriction. $\square$

## 12. Observed source reset and the original-clock exit correction

**Definition 12.1 (the observed filtration and source potentials).**
For a legitimate start $p\in D_I\setminus N$, use the completed,
right-continuous natural filtration $\mathcal F_t^O$ of $O^I$ under
$\mathbb P_p$, contained in the corresponding usual full-process
filtration. A stopping time below is an $\mathcal F^O$ stopping time.
The observation determines its own exit time: by (11.6),

$$
\theta_I=\inf\left\{t\ge0:
       \frac{|(O_t^I)_{02}|^2}{4Z}\notin(l,u)\right\}.
\tag{12.1}
$$

Here $(O_t^I)_{02}$ denotes the two components of its original
$02$ pair. Keep the original clock $t$ and write $\lambda>0$ for
a discount, distinct from the fixed native parameter $r=1-Z$.
Use exactly (8.3) and [S, (116.13)--(116.14)]:

$$
\begin{gathered}
b_\lambda=1-\lambda h^{-1}(F+\lambda)^{-1}h,
\quad d_\lambda=\int b_\lambda\,dm>0,
\quad R_\lambda=(K+\lambda)^{-1},\\
R_\lambda f(e)=\frac1{\lambda d_\lambda}
                    \int_G b_\lambda f\,dm.
\end{gathered}
\tag{12.2}
$$

The last value is the supplied source trace, equivalently the process
potential, for bounded complex Borel $f$. At legitimate other points
use process-potential versions, and for $b_\lambda$ use the
hitting-potential version of [S, (116.9)]. No ordinary value $h(e)$
is introduced.

**Theorem 12.2 (reset at an observed preparation stopping time).**
Let $S$ be any observed stopping time, possibly infinite, and put

$$
A_S=\{S<\infty,\ S<\theta_I,\ O_S^I=v_0\}.
\tag{12.3}
$$

For every bounded Borel functional $F_0$ of a continuous held output
path on $[0,\infty)$, with the topology of uniform convergence on
compact time intervals,

$$
\mathbb E_p\left[
 \mathbf1_{A_S} F_0\bigl((O_{S+t}^I)_{t\ge0}\bigr)
                         \mid\mathcal F_S^O\right]
 =\mathbf1_{A_S}\,
       \mathbb E_e F_0\bigl((O_t^I)_{t\ge0}\bigr).
\tag{12.4}
$$

The product on the left is set to zero off $A_S$, so no value at
$S=\infty$ is needed. In particular the delayed observed hitting times

$$
S_s=\inf\{t\ge s:O_t^I=v_0\},\qquad s\ge0,
\tag{12.5}
$$

are stopping times and obey (12.4) on $\{S_s<\theta_I\}$.
For the source start, almost surely,

$$
\begin{gathered}
\theta_I>0,\qquad
\inf\{t>0:O_t^I=v_0\}=0,\\
\int_0^T\mathbf1_{\{v_0\}}(O_t^I)\,dt=0
                         \quad\hbox{for every finite }T\ge0.
\end{gathered}
\tag{12.6}
$$

The same zero-residence assertion holds from every
$p\in D_I\setminus N$. Thus observed returns near zero are genuine
source contacts, without a positive interval of holding there.

**Proof.** The exit reconstruction (12.1) and continuity show that
$A_S\in\mathcal F_S^O$. Containment of the observed usual filtration
in the full usual filtration makes $S$ a full-process stopping time.
On $A_S$, (11.5) gives $\mathbf Z_S=e$. Apply the strong Markov
property of the supplied diffusion at $S$, on $\{S<\infty\}$,
localizing to $\{S\le n\}$ if necessary. Conditional on its entire
full-process past, the future path on $A_S$ has law $\mathbb P_e$.
Since $S<\theta_I$, the residual observation exit is the first exit
of this future path from the very same $D_I$, and the future readout
uses the same preparation rotations and map $\Phi$. Apply this
measurable stopped-and-held readout to the future path and condition
once more on $\mathcal F_S^O$. This proves (12.4), first for cylinder
functions and then for bounded Borel path functionals by the monotone
class theorem. This argument also establishes the measurability of
the stopped-path functional used there.

The first hitting time after a deterministic $s$ of a closed set by
a continuous adapted process is a stopping time in its usual
filtration. Apply this to $\{v_0\}$. Equality of the observed and
actual contact sets in (11.5) identifies every such contact before
exit. For a source start, continuity at the interior point $e$ gives
$\theta_I>0$. The supplied self-regularity
$\mathbb P_e\{\inf\{t>0:\mathbf Z_t=e\}=0\}=1$
then gives arbitrarily small positive observed contacts before exit.
Finally use (11.5) and the all-time zero-residence assertion
[S, (116.15)]. Holding after exit contributes no preparation-output
residence because its height differs from $k_0$. $\square$

The strong Markov and source-regularity inputs here are those of the
full symmetric diffusion in [S, Theorem 116.3]. The finely closed-set
regularity convention used there is the one in
[Chen--Fukushima--Ying, §4 before (4.1)](https://arxiv.org/pdf/math/0606784v1).
Equation (12.4) is an observational conditional-law identity. It does
not add a native reset command, erase retained native history or
assert the same detector under arbitrary interventions.

**Theorem 12.3 (contact and occupation with the observation exit retained).**
Let

$$
\tau_e=\inf\{t\ge0:\mathbf Z_t=e\},\qquad
\tau_O^I=\inf\{t\ge0:O_t^I=v_0\}.
$$

For $p\in D_I\setminus N$, the first observed contact is $\tau_e$
on $\{\tau_e<\theta_I\}$ and is infinite otherwise. For every
$\lambda>0$ its exact transform is

$$
\mathbb E_p[e^{-\lambda\tau_O^I};\tau_O^I<\infty]
 =b_\lambda(p)
  -\mathbb E_p[e^{-\lambda\theta_I}b_\lambda(\mathbf Z_{\theta_I});
                                      \theta_I<\tau_e].
\tag{12.7}
$$

For bounded complex Borel $g$ on $E_I$, define the bounded extension
on the original full carrier by

$$
\widehat g(p)=
 \begin{cases}g(\Phi(p)),&p\in D_I,\\0,&p\notin D_I.\end{cases}
\tag{12.8}
$$

The original source-start occupation before observation exit is

$$
\begin{aligned}
\mathbb E_e\int_0^{\theta_I}e^{-\lambda t}g(O_t^I)\,dt
 &=\frac1{\lambda d_\lambda}
                 \int_G b_\lambda\widehat g\,dm\\
 &\quad-\mathbb E_e[e^{-\lambda\theta_I}
                  R_\lambda\widehat g(\mathbf Z_{\theta_I});
                                      \theta_I<\infty].
\end{aligned}
\tag{12.9}
$$

For the complete held observation there is also exactly the holding
term:

$$
\mathbb E_e\int_0^\infty e^{-\lambda t}g(O_t^I)\,dt
 =\mathbb E_e\int_0^{\theta_I}e^{-\lambda t}g(O_t^I)\,dt
   +\frac1\lambda\mathbb E_e[e^{-\lambda\theta_I}
                         g(O_{\theta_I}^I);\theta_I<\infty].
\tag{12.10}
$$

All discounts multiply the original $t$. In particular the pre-exit
occupation for $g=1$ is
$\lambda^{-1}\mathbb E_e[1-e^{-\lambda\theta_I}]$, with
$e^{-\lambda\infty}=0$, while the complete held occupation is
$1/\lambda$.

**Proof.** Equation (11.5) and the boundary height prove the first
assertion. Split the full hitting transform
$b_\lambda(p)=\mathbb E_p[e^{-\lambda\tau_e}]$ at the earlier of
contact and exit. There is no finite tie, since $e$ is interior to
$D_I$. On $\{\theta_I<\tau_e\}$ the strong Markov property at
$\theta_I$ gives the discounted future hitting transform
$e^{-\lambda\theta_I}b_\lambda(\mathbf Z_{\theta_I})$.
This proves (12.7), also at $p=e$, where $\tau_e=0$ and the
correction event is empty. Omitting that event would give an
incorrect source-start formula.

For a bounded Borel $f$ on $G$, the ordinary strong Markov splitting
of its full process potential gives

$$
R_\lambda f(e)
 =\mathbb E_e\int_0^{\theta_I}e^{-\lambda t}f(\mathbf Z_t)\,dt
  +\mathbb E_e[e^{-\lambda\theta_I}R_\lambda f(\mathbf Z_{\theta_I});
                                               \theta_I<\infty].
\tag{12.11}
$$

Absolute integrability follows from $\|f\|_\infty/\lambda$;
real and imaginary parts justify the complex identity. Apply it to
(12.8) and use exactly the supplied full-source normalization (12.2).
This yields (12.9). After finite observation exit the held output is
constant, so direct integration gives (12.10). The assertions for
$g=1$ follow by integrating a constant in the original time.
The exit term in (12.9) includes all subsequent full-process visits
seen by $R_\lambda\widehat g$, even though the observation has
stopped. It is not a new killing or a change of the source law.
At an observed return stopping time, (12.4) applies these same formulas
to the future held observation. $\square$

## 13. A history-retaining Brownian reference has a different return law

**Definition 13.1 (finite held topology and the free first-level premise).**
Fix $T>0$, the same $I$, preparation and readout as above. Give

$$
\mathcal X_{I,T}=C([0,T],E_I),\qquad
 d_\infty(\omega,\omega')
       =\sup_{0\le t\le T}|\omega(t)-\omega'(t)|
\tag{13.1}
$$

the uniform topology. It is a Polish space since $E_I$ is a compact
subset of $\mathbb R^{10}$. In fact $\mathcal R$ restricted to
$I\times\mathbb T^2$ is a homeomorphism onto $E_I$: (11.6) recovers
the height, and the nonzero $01$ and $02$ pairs recover both phases.
This topology retains the full signed ten-output path, not only its
terminal output, a phase-unwrapped surrogate or a cemetery jump.

A free first-level reference in this section means any joint law
carrying a planar Brownian pair $(A_t,B_t)$ started at $(0,0)$ with

$$
\mathbb E\!\left[
 \begin{pmatrix}A_t\\B_t\end{pmatrix}
 \begin{pmatrix}A_s&B_s\end{pmatrix}\right]
       =2\min(t,s)\,\mathsf D,\qquad
\mathsf D=\mathsf D^{\mathsf T}>0,
\tag{13.2}
$$

and any continuous real retained central history $J_t$ with $J_0=0$,
possibly with arbitrary extra randomness. No independence of $J$
from the Brownian pair is assumed; even dependence on its complete
future is allowed for this comparison. Only the marginal law of the
pair in (13.2) is required. Put

$$
\begin{gathered}
\vartheta_I=\inf\{t\in[0,T]:k_0+A_t\notin(l,u)\},
\qquad \inf\varnothing=\infty,\\
q_t^{\rm ref}
 =(k_0+A_t,[\alpha_0+B_t/2],
                 [\beta_0+c_0B_t-J_t/r]),\qquad t\le\vartheta_I,\\
O_t^{\rm ref}=\mathcal R(q_{t\wedge\vartheta_I}^{\rm ref}),
                    \qquad 0\le t\le T.
\end{gathered}
\tag{13.3}
$$

Let $\mu_{I,T}$ be the law of this held output in (13.1), and let
$\nu_{I,T}$ be the law of $(O_t^I)_{0\le t\le T}$ under the
legitimate original source start $\mathbb P_e$.
The reference covariance-$2$ convention of
[Guarded lift limits, Theorem 6.1](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#6-direct-joint-convergence-including-the-chronological-coordinate)
is $\mathsf D=I_2$. A scalar free horizontal coefficient $a$ in the
same clock corresponds to $\mathsf D=aI_2$, not to changing $t$.
This is an additional stochastic premise, not a consequence of
finite-variation native syntax. The arbitrary $J$ includes the
canonical area, area drift and continuous independent central noise
of the separately declared native references.

**Theorem 13.2 (source-return singularity for every such retained history).**
For every nondegenerate $\mathsf D$ in (13.2), every allowed joint
central history and every $T>0$,

$$
\mu_{I,T}\perp\nu_{I,T}.
\tag{13.4}
$$

More precisely, there is a Borel event $\mathcal A_{I,T}$ on the
actual held ten-output path space such that

$$
\begin{gathered}
\mathcal A_{I,T}
 =\{\omega:\hbox{for every }\delta>0
       \hbox{ there is }t\in(0,\min(\delta,T))
                                     \hbox{ with }\omega(t)=v_0\},\\
\nu_{I,T}(\mathcal A_{I,T})=1,\qquad
\mu_{I,T}\{\omega:\omega(t)=v_0
                         \hbox{ for some }t\in(0,T]\}=0.
\end{gathered}
\tag{13.5}
$$

Consequently, on any complete-history sampling space carrying the
reference (13.3), no probability law absolutely continuous with
respect to that sampling law can have held output law $\nu_{I,T}$.
This includes every normalized nonnegative integrable weight depending
on all retained histories and all auxiliary randomness.

**Proof.** Theorem 12.2 gives arbitrarily small positive contacts from
$e$ before its strictly positive observation exit, hence the first
probability in (13.5). The event is Borel in the uniform topology.
For example set $\delta_n=T/(n+1)$ and express it as

$$
\mathcal A_{I,T}
 =\bigcap_{n\ge1}\ \bigcup_{m:\,1/m<\delta_n}
   \left\{\omega:
    \min_{t\in[1/m,\delta_n]}|\omega(t)-v_0|=0\right\}.
\tag{13.6}
$$

Each minimum is a continuous function of $\omega$ in (13.1).
Positive-time returns are used; all these paths already have the
same initial output $v_0$.

For a reference path before exit, the two pairs used in (11.6)
and the fiber proof imply

$$
O_t^{\rm ref}=v_0
 \quad\Longrightarrow\quad A_t=0,\qquad B_t\in4\pi\mathbb Z.
\tag{13.7}
$$

This implication does not involve $J$. A nondegenerate planar
Brownian motion avoids each fixed point at all strictly positive
times, including a return to its starting point. The exact standard
statement is Mörters--Peres, *Brownian Motion*,
[public draft, Corollary 2.23, p.52](https://www.stat.berkeley.edu/~aldous/205B/bmbook.pdf):
for $d\ge2$, $\mathbb P_x\{y\in B(0,1]\}=0$ for every $x,y$.
For (13.2), choose an invertible matrix $C$ with
$CC^{\mathsf T}=2\mathsf D$. Then $(A,B)$ has the law of $CW$
for a standard planar Brownian motion $W$ of covariance $tI_2$.
Apply the cited statement to each point
$C^{-1}(0,4\pi j)$, using Brownian scaling for the fixed finite
horizon, and take the countable union over $j$. This is a comparison
of laws with their declared covariance; the observations in (13.3)
remain in the original time. It proves that (13.7) never occurs at
positive time almost surely, independently of the joint choice of
$J$. At and after a finite exit, the held height is $l$ or $u$ and
cannot be $k_0$. This proves the second probability in (13.5) and
therefore (13.4).

Finally let $\mathbb P$ be any complete-history reference law with
output map $O$ and let $\mathbb Q\ll\mathbb P$. The preimage
$O^{-1}(\mathcal A_{I,T})$ is $\mathbb P$-null by (13.5), so is
$\mathbb Q$-null. Its image law cannot be $\nu_{I,T}$, which assigns
it mass one. In particular $d\mathbb Q=W\,d\mathbb P$ with
$W\ge0$, $\mathbb E_{\mathbb P}W=1$ cannot change this conclusion.
No filtration, conditional-kernel regularity or Markov property of
the retained history is needed for this absolute-continuity argument.
$\square$

## 14. Escape of sampling mass in lawful finite approximations

**Definition 14.1 (same-stage laws of actual native executions).**
For each $n$, let $(\Omega_n,\mathbb P_n)$ carry actually executed
finite lawful native histories from the same preparation, with their
original clock, original prefix guards, ordinary chronological area
and exact ten-output map. Let $V_n:\Omega_n\to\mathcal X_{I,T}$
be their output path, held at their own observation exit from
$(l,u)$, or at a lawful execution stop if the output is thereafter
held. Any extra retained history and sampling randomness may be part
of $\Omega_n$. No common sampling space or coupling across $n$ is
required. Set

$$
\begin{gathered}
w_n\ge0,\qquad\mathbb E_{\mathbb P_n}w_n=1,\qquad
 d\mathbb Q_n=w_n\,d\mathbb P_n,\\
\mu_n=(V_n)_*\mathbb P_n,\qquad
\nu_n=(V_n)_*\mathbb Q_n.
\end{gathered}
\tag{14.1}
$$

The weights act on the same actual histories and readout at stage
$n$. Weak convergence below is on the held uniform topology (13.1).
The definition imposes no stochastic law on an individual original
finite-variation history; the two limit laws are separate hypotheses.

**Theorem 14.2 (complete bounded-weight escape and divergence).**
Suppose the unweighted output laws and the normalized weighted output
laws of Definition 14.1 satisfy, for a reference of Definition 13.1,

$$
\mu_n\Rightarrow\mu_{I,T},\qquad
\nu_n\Rightarrow\nu_{I,T}.
\tag{14.2}
$$

Then every bounded-weight portion loses all its weighted mass:

$$
\begin{gathered}
\lim_{n\to\infty}\mathbb E_{\mathbb P_n}
                   [w_n\mathbf1_{\{w_n\le M\}}]=0
                                \quad\hbox{for every }0<M<\infty,\\
\lim_{n\to\infty}\mathbb E_{\mathbb P_n}
                   [w_n\mathbf1_{\{w_n>M\}}]=1.
\end{gathered}
\tag{14.3}
$$

In particular the weights are not uniformly integrable. For every
$p>1$,

$$
\mathbb E_{\mathbb P_n}w_n^p\longrightarrow\infty,\qquad
D(\mathbb Q_n\Vert\mathbb P_n)
 =\mathbb E_{\mathbb P_n}[w_n\log w_n]\longrightarrow\infty.
\tag{14.4}
$$

Here $0\log0=0$ and infinite values are allowed. These are moments
and entropy of the two sampling laws at the same finite stage.
No entropy comparison between an absolutely continuous control path
and a diffusion path is asserted, and (14.2) supplies no divergence
rate or existence of such a weighting family.

**Proof.** Write $\mu=\mu_{I,T}$ and $\nu=\nu_{I,T}$.
Theorem 13.2 gives a Borel set of $\mu$-measure zero and
$\nu$-measure one. On a Polish space, regularity of probability
measures gives, for any $\epsilon>0$, a compact subset $K$ of that
set with $\nu(K)>1-\epsilon$, and an open neighbourhood $U$ of
$K$ with $\mu(U)<\epsilon$. Choose a continuous function
$0\le f\le1$ that is one on $K$ and zero outside $U$. Such a
function exists by the elementary distance construction for disjoint
closed sets in a metric space. Thus

$$
\mu f<\epsilon,\qquad \nu(1-f)<\epsilon.
\tag{14.5}
$$

For a fixed finite $M>0$, positivity and (14.1) give

$$
\begin{aligned}
\mathbb E_{\mathbb P_n}[w_n\mathbf1_{\{w_n\le M\}}]
 &\le M\mathbb E_{\mathbb P_n}f(V_n)
           +\mathbb E_{\mathbb P_n}[w_n(1-f(V_n))]\\
 &=M\mu_nf+\nu_n(1-f).
\end{aligned}
\tag{14.6}
$$

Both test functions are bounded and continuous. Apply the two weak
limits (14.2), obtaining a limsup at most $(M+1)\epsilon$.
Let $\epsilon\downarrow0$. This proves the first line of (14.3);
normalization proves the second. This argument uses continuous
separators of the singular limit laws. It never passes an exact-return
event through weak convergence, nor requires a joint limit of
$(V_n,w_n)$.

For any fixed $M>1$,

$$
\begin{aligned}
\mathbb E_{\mathbb P_n}w_n^p
 &\ge M^{p-1}\mathbb E_{\mathbb P_n}
                          [w_n\mathbf1_{\{w_n>M\}}],\\
\mathbb E_{\mathbb P_n}[w_n\log w_n]
 &\ge(\log M)\mathbb E_{\mathbb P_n}
                          [w_n\mathbf1_{\{w_n>M\}}]-e^{-1}.
\end{aligned}
\tag{14.7}
$$

The last bound uses $x\log x\ge-e^{-1}$ on $[0,\infty)$, so
its negative part is always integrable. First take the liminf in
$n$ and use (14.3), then let $M\to\infty$. This proves (14.4).
The tail mass limit one for every $M$ also contradicts uniform
integrability directly. $\square$

**Definition 14.3 (standard-tool correspondence and the native boundary).**
The capacity/exceptional-set correspondence and the strong Markov
property are established symmetric Dirichlet-form tools, used here
with the full form [S, (115.15)], its source trace and its legitimate
source start. The local tube estimate (11.7)--(11.8) checks their
set-specific hypothesis for the exact native preparation-output
fiber, including its punctured line through the nonpolar source.
It is distinct from proving the source capacity or a general
potential-theoretic theorem. The standard Brownian input in Theorem
13.2 is precisely Mörters--Peres Corollary 2.23 with the invertible
covariance correspondence specified there. Measure regularity,
continuous separation and the elementary inequalities (14.6)--(14.7)
are standard probability tools, not a new general entropy theorem.
Their application here consumes the source-specific singularity
(13.5), which depends on both the exact output fiber and the retained
original source.

The supplied native guarded lift and its held-path continuity in
[Guarded lift limits, §§2--4](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#2-the-original-source-its-guard-and-its-entire-chronological-path)
retain their original finite histories, prefix guards and real areas.
Its [Proposition 9.3](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#9-sufficient-law-and-weighting-data-for-selecting-the-reference)
already supplies weighting transfer when a joint weight limit and
uniform integrability are given. Theorem 14.2 instead concerns the
two stated output-law limits on varying sampling spaces; it shows
complete loss of every bounded-weight portion for the singular
original-source target. It makes no new claim about the existence,
optimality or cost of those guarded approximations. The free
hidden-circle rigidity of §§1--6, the fixed Borel central-fiber
exclusion of §§7--10 and the affine/CPTP obstruction of [B, §12]
are separate supplied results, not new conclusions of this append.
The difference here is the actual source-return event in the full
ten-output history, which is tested without imposing a fixed
fiber kernel or a source-independent affine map.

The [central-noise Green model](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md#1-fixed-source-conditional-law-and-the-matched-operator),
[variable-coefficient Green model](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md#1-fixed-model-and-the-exact-question),
[spatial-cap source form](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md#5-the-natural-logarithmic-source-form-and-positive-point-capacity)
and its [all-real cap limit](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md#12-the-all-real-parameter-operator-limit)
keep their own carriers, walls, measures, coefficients and source
domains. Their processes and capacities are not substituted for
(7.2). Only a model with the first-level premise (13.2) and the
actual output formula (13.3) is subject to Theorem 13.2. An arbitrary
retained central history under that same premise cannot change
(13.7); a source law changing the first-level premise is outside that
assertion. In particular nonlinear native source-law actions of
[B, §12.3] retain their original contracts. These theorems neither
exclude all history-dependent correspondences nor construct one.

Equations (11.5), (12.4) and (12.9) are necessary tests on the
source/readout restriction of any proposed same-source, same-clock
realization of the full endpoint. They provide no map beyond the
native slab, no stochastic generation from bare finite commands,
no identification of the full source domain with a native command
domain, and no derivation of physical spatial dimension. The genuine
native source/evolution/representation/readout bridge remains
unresolved. The deductions here are ordinary source-specific
mathematics, without a worldwide-priority or Lean-certification claim.

## 追加锚（本行以下为增补区）

## 15. The returning marked source specified by the original killed operator

**Definition 15.1 (fixed endpoint, excursion marks and added source information).**
Retain without alteration Definitions 7.1 and 11.1, including every
$a,\eta>0$, $g_c=16\sqrt{a\eta}$, the unit-source degree-$-3$
$\Gamma$, raw Haar measure $\mu$, the entire complex selector (112.5),
$h$, $m=h^2\mu$, $J_h$, $H$, $K$ and their original clock. In
particular $m(G)=1$. In §§15--19 write [GL] for
[Guarded lift limits and diffusion selection](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md);
[N] keeps its original meaning from Definition 1.1. Write $M=G\setminus\{e\}$ and use exactly the
source-killed supplier

$$
 A_0=J_h^{-1}FJ_h,\qquad P_t^0=J_h^{-1}e^{-tF}J_h,
 \qquad R_\lambda^0=(A_0+\lambda)^{-1}.
\tag{15.1}
$$

Here $A_0$ is only a new notation for [S, (116.11)], not a
replacement for $K$. All discounts $\lambda>0$ refer to original
elapsed time. With $E_F$ the spectral resolution of $F$, put

$$
 \nu(B)=\langle h,E_F(B)h\rangle_{L^2(\mu)},\qquad
 q_t=J_h^{-1}Fe^{-tF}h,\qquad
 \kappa(t)=\int_{(0,\infty)}s e^{-ts}\,\nu(ds),\quad t>0.
\tag{15.2}
$$

The measure $\nu$ is a probability measure with $\nu(\{0\})=0$.
The symbol $q_t$ denotes an $L^2(m)$ density; it assigns no value
$h(e)$.

A returning mark consists of a duration $0<\zeta<\infty$ and a
continuous path $\omega:[0,\infty)\to G$ with
$\omega(0)=\omega(\zeta)=e$, $\omega(t)\in M$ for $0<t<\zeta$,
and $\omega(t)=e$ after $\zeta$. Its four coordinates, including $z$,
are retained. Denote this standard Borel space by $\mathcal W$.
One can realize it as a Borel subset of
$(0,\infty)\times C([0,\infty),G)$: avoidance on compact subintervals
of $(0,\zeta)$ is expressed by positive minima of the distance to
$e$, using rational subintervals. For killed cylinder expressions only,
put $\omega(t)=\Delta$ when $t\ge\zeta$ and set every test on $M$
equal to zero at $\Delta$.

The additional source premise in this construction is sampling a
Poisson random measure on $(0,\infty)\times\mathcal W$ with the
intensity specified below, including its complete real-valued marks
and labels. This is a declared stochastic source, not a consequence
of bare finite FIB commands. The construction does not take a full
endpoint trajectory as its random input. Such a trajectory will be
constructed from these marks. Exact mark access, including the
infinitely many small marks, is an information premise. The hidden
$z$ coordinate is retained source information, with no additional
native actuator or readout.

**Theorem 15.2 (positive entrance and all returning-excursion cylinders).**
There is a unique sigma-finite returning mark measure $\mathbf n$,
with no mass on duration zero, whose complete killed cylinders are,
for $0<t_1<\cdots<t_j$ and bounded nonnegative Borel $f_i$ on $M$,

$$
\begin{aligned}
 &\mathbf n\left[\mathbf1_{\{\zeta>t_j\}}
                     \prod_{i=1}^j f_i(\omega(t_i))\right]\\
 &\quad=\int_M q_{t_1}(p)
   \left[M_{f_1}P^0_{t_2-t_1}M_{f_2}\cdots
                    P^0_{t_j-t_{j-1}}M_{f_j}1\right](p)\,m(dp).
\end{aligned}
\tag{15.3}
$$

Here $M_f$ is multiplication by $f$; for $j=1$ the right side
is $\int q_{t_1}f_1\,dm$, with no transition factor.
Every $q_t$ is nonnegative, is not zero, and has finite mass
$\kappa(t)>0$. It is an entrance law in the measure sense:

$$
\begin{gathered}
 (q_t m)P_s^0=q_{t+s}m,\qquad
 \int_0^\infty q_t\,dt=1,\qquad
 \int_0^\infty e^{-\lambda t}q_t\,dt
     =1-\lambda R_\lambda^0 1=b_\lambda,\\
 \mathbf n(\zeta>t)=\kappa(t),\qquad
 \mathbf n(\zeta\in dt)
       =\left(\int_{(0,\infty)}s^2e^{-ts}\nu(ds)\right)dt.
\end{gathered}
\tag{15.4}
$$

The integral of $q_t$ without discount is a strong improper $L^2(m)$
integral. For nonnegative Borel tests the corresponding measure
identity holds by Tonelli. With
$d_\lambda=\langle h,h-\lambda(F+\lambda)^{-1}h\rangle$, the exact
normalizations are

$$
\begin{gathered}
 \mathbf n[\zeta]=1,\qquad \mathbf n(\mathcal W)=\infty,\\
 \mathbf n[1-e^{-\lambda\zeta}]
    =\lambda\int_0^\infty e^{-\lambda t}\kappa(t)\,dt
    =\lambda d_\lambda=:\varphi(\lambda),\\
 \varphi(\lambda)=\operatorname{Cap}_\lambda(\{e\}),\qquad
 \varphi'(0+)=1.
\end{gathered}
\tag{15.5}
$$

All cylinders are for the same original $F,h,m$ and original duration;
no duration rescaling or change of source condition occurs.

**Proof.** First, $P_t^0 1=h^{-1}e^{-tF}h$ is the supplied killed
survival in [S, (116.9)]. It decreases with $t$ and is between zero
and one. Spectral calculus makes it differentiable in $L^2(m)$
for every $t>0$, with derivative $-q_t$. Difference quotients and
closedness of the positive cone show $q_t\ge0$. Moreover,

$$
 \|q_t\|_{L^2(m)}\le\sup_{s\ge0}s e^{-ts}<\infty,
 \qquad \int q_t\,dm=\langle h,Fe^{-tF}h\rangle=\kappa(t)>0.
\tag{15.6}
$$

The strict last inequality follows from the probability normalization
and absence of spectral mass at zero. Thus $q_t m$ is a positive
finite entrance measure, rather than a signed formal inverse Laplace
transform. Selfadjointness gives
$P_s^0q_t=q_{t+s}$; integrating against Borel tests proves the first
identity of (15.4). Strong continuity for $t>0$ supplies a jointly
measurable density version, for instance by step approximations in
$t$ and an almost-everywhere convergent subsequence in product
measure on compact positive-time intervals.

For $0<\epsilon<R$, spectral integration gives

$$
 \int_\epsilon^R q_t\,dt
       =J_h^{-1}(e^{-\epsilon F}-e^{-RF})h.
\tag{15.7}
$$

As $\epsilon\downarrow0$, $R\uparrow\infty$, the right side tends
strongly to $1$, since $\ker F=\{0\}$. Positivity proves the
measure identity as well. Its discounted counterpart has spectral
multiplier $s/(s+\lambda)$ and is exactly $b_\lambda$.

Here is the primary excursion result used to obtain a continuous
returning mark measure, as opposed to just formal cylinder numbers.
Fukushima--Tanaka, *Poisson point processes attached to symmetric
diffusions*, Ann. IHP Probab. Statist. 41 (2005), 419--459,
[DOI 10.1016/j.anihpb.2004.10.004, §3.1, Theorem 3.1 and
(3.4)--(3.12)](https://www.numdam.org/item/AIHPB_2005__41_3_419_0.pdf),
identifies the recurrent-point excursion entrance law with the unique
entrance law integrating to $m$. Its uniqueness assertion is Lemma
2.2(i); its complete cylinder assertion is (3.12). Its hypotheses
are checked here with their $S=G$, distinguished point $a=e$,
$S_0=M$, speed measure $m=h^2\mu$, real form
$(\mathscr E,\mathscr V)$, and absorbed process $P_t^0$ of (15.1).
The space is locally compact, separable and metrizable; $e$ is
non-isolated; $m$ is full-support Radon and $m(\{e\})=0$.
Regularity and strong locality are [S, Theorem 115.3]. Their B.2
holds with their hitting function $\phi=1$ quasi-everywhere by
[S, (116.10)]. Their B.3 holds with
$1\in\mathscr V$, $\mathscr E[1]=0$. The source is legitimate,
regular, recurrent and instantaneous by [S, Theorems 116.3--116.4].
The absorbed process is the part on $M$, with the entire domain
in [S, (116.11)], not the two-zero-coefficient restriction of $K$.
Their $u_\lambda$ is our $b_\lambda$.
These are precisely the hypotheses of the recurrent framework in
§3.1. The one-point compactification example in §3.2 and the
independent-extension assumptions A.1--A.4 of §4 are not invoked.

Apply that theorem to the supplied full diffusion as an existence
and normalization witness. Its excursion measure has entrance law
integrating to $m$. Equation (15.7) and the entrance identity identify
that law as $q_t m$, by the cited uniqueness. Hence (3.12) gives
exactly (15.3) on continuous excursions returning to $e$. This proves
existence with the stated path support; it is more than a scalar
resolvent calculation. For uniqueness, restrict to
$\{\zeta>1/k\}$, which has finite measure. Cylinders at rational
times, with later survival tests and killed evaluations, determine
both the duration and the continuous path, so determine this finite
measure. The sets $\{\zeta>1/k\}$ exhaust $\mathcal W$.
Consequently the explicitly given cylinders determine $\mathbf n$
uniquely. This use of the full diffusion verifies existence of the
mark law; it does not supply a sampled full trajectory to the new
source.

Take $f_1=1$ in (15.3). Then
$\mathbf n(\zeta>t)=\kappa(t)$. Differentiation for $t>0$ is
justified by boundedness of $s^2e^{-ts}$ on intervals bounded away
from zero, giving the lifetime density in (15.4). Tonelli gives
$\int_0^\infty\kappa(t)dt=\nu((0,\infty))=1$.
There is no atom at infinite lifetime since $\kappa(t)\to0$ as
$t\to\infty$.

Finally $h\notin\mathcal Q_c$: otherwise
$1=J_h^{-1}h\in\mathscr V_0$, contradicting its source trace one
in [S, (116.3)]. The spectral characterization of the form domain
of $F$ therefore gives
$\int s\,\nu(ds)=\infty$. Monotone convergence shows
$\kappa(t)\uparrow\infty$ as $t\downarrow0$. Thus
$\mathbf n(\mathcal W)=\infty$. The discounted tail integral is
$\int s/(s+\lambda)\nu(ds)=d_\lambda$ by [S, (116.17)].
The capacity equality follows from [S, (116.4)], with its original
energy normalization. Also $d_\lambda\to1$ as
$\lambda\downarrow0$, which proves $\varphi'(0+)=1$.
This proves every normalization in (15.5). $\square$

## 16. Original-duration synthesis of the entire source-start law

**Definition 16.1 (the marked source map).** Sample a Poisson random
measure $\Pi$ with intensity $d\ell\,\mathbf n(d\omega)$ on
$(0,\infty)\times\mathcal W$. A label $\ell$ indexes source local
time; it is not the elapsed time of a native command. Almost surely
there is at most one atom at any label. Put

$$
 \tau_\ell=\int_{(0,\ell]\times\mathcal W}\zeta(\omega)
                     \,\Pi(ds,d\omega),\qquad \tau_0=0.
\tag{16.1}
$$

For an atom $(\ell,\omega_\ell)$ define the synthesized path by

$$
 \mathsf Z_t=\omega_\ell(t-\tau_{\ell-})
       \quad\hbox{if }\tau_{\ell-}<t<\tau_\ell,
 \qquad \mathsf Z_t=e\quad\hbox{at all other times}.
\tag{16.2}
$$

The endpoint convention agrees with the continuous mark endpoints.
Define the auxiliary continuous clock

$$
 \mathsf L_t=\inf\{\ell\ge0:\tau_\ell>t\}.
\tag{16.3}
$$

Each mark is used for its full original duration. Formula (16.2)
adds no holding interval, killing, drift in the inverse clock or
retiming of any mark.

**Theorem 16.2 (full path, complex domain and source response).**
The map (16.1)--(16.2) is measurable, has continuous paths on $G$
and infinite lifetime almost surely, and its law is exactly the
original full source-start law $\mathbb P_e$. In particular, for
$0<t_1<\cdots<t_j$ and bounded complex Borel $f_i$ on $G$,

$$
 \mathbb E\prod_{i=1}^j f_i(\mathsf Z_{t_i})
  =\operatorname{tr}\left[
       T_{t_1}\bigl(f_1T_{t_2-t_1}
             (f_2\cdots T_{t_j-t_{j-1}}f_j)\bigr)\right].
\tag{16.4}
$$

The trace in this formula is well defined by positive-time smoothing
as in [S, Theorem 117.2]. The reconstructed transition family from
other legitimate starts is obtained by running (15.1) until its
first source contact and appending an independent copy of (16.2).
It is the original full transition family, including its source.
On the entire complex $L^2(G,m)$ its resolvent is

$$
 R_\lambda=R_\lambda^0+
      \frac{|b_\lambda\rangle\langle b_\lambda|}
                              {\lambda d_\lambda},
 \qquad
 R_\lambda f(e)=\frac{\int b_\lambda f\,dm}{\lambda d_\lambda}.
\tag{16.5}
$$

Under $J_h$ its generator is exactly $H$, with the full domain

$$
\begin{gathered}
 D(H)=\{u\in D(S_{\min}^*):A(u)=\rho_*C(u)\},
 \qquad Hu=S_{\min}^*u,\\
 D(K)=\{v\in\mathscr V:hv\in D(S_{\min}^*),
                              A(hv)=\rho_*C(hv)\}.
\end{gathered}
\tag{16.6}
$$

These are the unchanged selector (112.5) and (7.2). Equality holds
for the entire complex resolvent set as well, by equality of the
selfadjoint operators. The exact original source coefficient response
for $\phi\in L^2(G,\mu;\mathbb C)$ is

$$
 \frac{C((H+\lambda)^{-1}\phi)}{c_h}
  =\frac{\langle h-\lambda(F+\lambda)^{-1}h,\phi\rangle}
                              {\lambda d_\lambda}.
\tag{16.7}
$$

Moreover $\mathsf L$ is the source PCAF normalized by Revuz measure
$\delta_e$, and

$$
\begin{gathered}
 \mathbb E e^{-\lambda\tau_\ell}
       =e^{-\ell\lambda d_\lambda},\qquad
 \mathbb E_e\int_0^\infty e^{-\lambda t}\,d\mathsf L_t
       =\frac1{\lambda d_\lambda},\\
 U_\lambda\delta_e(p)=\frac{b_\lambda(p)}{\lambda d_\lambda}.
\end{gathered}
\tag{16.8}
$$

The local clock is auxiliary; the process in (16.4)--(16.7) still
uses elapsed time $t$.

**Proof.** Since $\mathbf n\zeta=1$, the Poisson integral (16.1)
is finite for every finite $\ell$, with expectation $\ell$.
It is a driftless subordinator. Its Poisson exponential formula and
(15.5) prove the first identity in (16.8). There is no killing
term because $\varphi(0+)=0$. There is no linear drift term:
(16.1) is a sum of jumps, and equivalently
$\varphi(\lambda)/\lambda=d_\lambda\to0$ as
$\lambda\to\infty$, by dominated convergence in (116.17).
Infinite mark intensity makes $\tau$ strictly increasing almost
surely. Indeed, every fixed positive label interval contains a mark
with probability one, and a countable intersection over rational
intervals suffices. Independent increments over unit label intervals
are identically distributed, nonnegative, and have mean one.
Their strong law implies $\tau_\ell\to\infty$. Thus the original
elapsed-time half-line is covered by the excursion intervals and
their complementary range, with no terminal death. The complement
has zero Lebesgue measure, since the sum of excursion lengths up
to $\tau_\ell$ is exactly $\tau_\ell$.

Measurability can be made explicit without ordering infinitely many
small marks by a first label. Exhaust mark space by
$\{\zeta>1/k\}$. On a bounded label interval each restriction
has finitely many atoms, which can be ordered measurably by label.
Their duration sums increase to (16.1). The unique interval
containing a fixed $t$ in its interior, if one exists, can then be
identified by the countable family of atom inequalities
$\tau_{\ell-}<t<\tau_\ell$. Evaluation of its continuous mark
is measurable. Set the value to $e$ on the complement. This proves
measurability of all time evaluations of (16.2).

To verify continuity and the complete law, use exactly the recurrent
excursion statement already checked in Theorem 15.2. Under the
supplied law $\mathbb P_e$, the inverse of the Revuz-$\delta_e$
PCAF and its excursion marks form the Poisson process of
Fukushima--Tanaka (3.4)--(3.7). By Theorem 3.1 there, its intensity
is $d\ell\,\mathbf n$, with all cylinders (15.3).
Their (3.3) and §2.2 use this same Revuz normalization.
The inverse has zero drift because ordinary residence at $e$ is
zero, and no killing because recurrence gives infinite total local
time. It is precisely the sum of its excursion durations.
Reconstructing that reference path by (16.2) returns it at every
time: away from $e$ it lies in its unique excursion, and on the
remaining times its value is $e$ by continuity. This is an exact
path identity, not merely an occupation identity.

The same reference witness also verifies the small-mark condition
needed for continuity of the new concatenation. For every
$\delta>0$,

$$
 \mathbf n\{\sup_{v\le\zeta}|\omega(v)-e|>\delta\}<\infty.
\tag{16.9}
$$

Indeed, on a bounded label interval the reference inverse time is
finite almost surely. Uniform continuity of the reference diffusion
on that finite elapsed-time interval implies that every excursion
reaching distance greater than $\delta$ has duration at least a
sample-dependent positive number. Only finitely many such disjoint
intervals fit there. Were the measure in (16.9) infinite, its
Poisson count on every positive label interval would instead be
infinite almost surely, a contradiction. Thus on any bounded label
interval of the new Poisson source there are only finitely many
marks exceeding any fixed positive size. Within an excursion the
new path is continuous. At a time in the complementary range,
these finitely many large excursions approach their continuous
endpoints, while all other excursions stay within $\delta$ of
$e$. Let $\delta\downarrow0$ through a countable sequence. This
proves continuity of (16.2) at all remaining times as well, on every
finite elapsed horizon since $\tau_\ell\uparrow\infty$.
Together with the measurable rational evaluations above it proves
measurability into $C([0,\infty),G)$.

Poisson random measures with the same sigma-finite intensity have
the same law, as follows first from their joint counts on disjoint
finite-intensity sets and then by exhaustion. Apply this measurable
continuous-path map to our independently sampled measure and to the
reference excursion measure. Their image laws coincide, and the
latter is exactly $\mathbb P_e$. Thus (16.4) follows by the original
Markov property, for all bounded complex tests. In this proof the
given full process certifies existence, support and equality of
laws; its trajectory is not an input supplied to the construction.
The sampled input consists of the explicitly specified returning
marks, including their nontrivial cylinder correlations.

For a legitimate start $p\ne e$, the part process reaches the same
$e$ almost surely by [S, (116.10)]. Its stopped path is the original
path up to contact, and strong Markov gives an independent original
source-start future. The just-proved source-start law therefore
identifies the entire appended law. Splitting the potential there
gives $R_\lambda^0 f(p)+b_\lambda(p)R_\lambda f(e)$.
Alternatively compute the source potential directly from the new
Poisson measure. Tonelli and its compensation formula give, for
bounded nonnegative $f$,

$$
\begin{aligned}
 \mathbb E\int_0^\infty e^{-\lambda t}f(\mathsf Z_t)dt
 &=\int_0^\infty\mathbb E e^{-\lambda\tau_{\ell-}}d\ell\,
       \mathbf n\left[\int_0^\zeta e^{-\lambda u}f(\omega(u))du\right]\\
 &=\frac1{\varphi(\lambda)}
                \int_0^\infty e^{-\lambda u}\int q_u f\,dm\,du
  =\frac{\int b_\lambda f\,dm}{\lambda d_\lambda}.
\end{aligned}
\tag{16.10}
$$

The complementary range contributes no elapsed-time integral. A
left-limit inverse is used in the compensation step because it is
predictable; at each fixed label it has the same Laplace transform
as $\tau_\ell$. Conservation bounds the integral of a bounded
complex input by $\|f\|_\infty/\lambda$, so real and imaginary
parts extend the identity. Together with the contact splitting this
proves (16.5). Its $L^2$ extension is exactly the bounded rank-one
formula of [S, (116.13)]. Equality of one positive resolvent of
closed selfadjoint operators identifies both operator and domain;
hence (16.6), (16.7) and the entire complex resolvent identification
follow, with no Friedrichs substitution for $H$.

For normalization of the clock, [S, (116.4)] gives

$$
 \mathscr E_\lambda\left[
       \frac{b_\lambda}{\lambda d_\lambda},v\right]
             =\operatorname{tr}v=\widetilde v(e).
\tag{16.11}
$$

Thus $\delta_e$ is a finite-energy smooth measure, with potential
$b_\lambda/(\lambda d_\lambda)$. The PCAF in the recurrent
excursion theorem is its Revuz-$\delta_e$ PCAF, not a scalar
multiple chosen from a Brownian convention. The joint law of
(16.2)--(16.3) is the corresponding reference joint law, by the
same measurable Poisson map. Directly, change variables for a
continuous increasing function and its right-continuous inverse to
obtain

$$
 \mathbb E\int_0^\infty e^{-\lambda t}d\mathsf L_t
   =\int_0^\infty\mathbb E e^{-\lambda\tau_\ell}d\ell
   =\frac1{\lambda d_\lambda}.
\tag{16.12}
$$

This agrees with the trace-one normalization in (16.11). All
normalizations are consequently fixed by the actual source capacity.
No positive spectral gap was used. $\square$

## 17. A measurable finite native-command law consuming the marked source

**Definition 17.1 (observation and finite-list command space).**
Fix any $I=[l,u]\Subset(0,H_{\rm n})$ with $l<k_0<u$ and finite
$T>0$. Construct $\mathsf Z$ from Definition 16.1, and put

$$
\begin{gathered}
 \theta=\inf\{t\ge0:k_0+x(\mathsf Z_t)\notin(l,u)\},
 \qquad S=T\wedge\theta,\\
 (A_t,B_t,W_t)=(x,y,w)(\mathsf Z_{t\wedge S}),\qquad
 O_t=\mathcal R\bigl(k_0+A_t,
        [\alpha_0+B_t/2],[\beta_0+c_0B_t-W_t/r]\bigr).
\end{gathered}
\tag{17.1}
$$

Then $O$ is exactly the original held observation $O^I$ on $[0,T]$.
The full source $\mathsf Z$ is not stopped or killed at $\theta$.

Encode a finite piecewise linear command by its finite increasing
list of break times and its real two-control vertices, beginning at
$(0,0)$; omit a terminal zero-length hold. The disjoint union of
these finite-dimensional Borel parameter spaces is a standard Borel
command space. Lawfulness is the original strict height-extrema
condition (7.6), and the real chronological integral is always
computed from the same interpolated command.

For $0<\rho\le(u-l)/4$, select the least integer $m\ge0$ for
which the partition $s_i=iS/2^m$, $0\le i\le2^m$, satisfies,
on every cell $[s,t]=[s_i,s_{i+1}]$,

$$
\begin{gathered}
 \sup_{s\le v\le t}|A_v-A_s|\le\rho,\qquad
 \sup_{s\le v\le t}|B_v-B_s|\le\rho,\\
 \sup_{s\le v\le t}|W_v-W_s-A_s(B_v-B_s)|\le\rho^2.
\end{gathered}
\tag{17.2}
$$

Almost surely $S>0$. Continuity on $[0,S]$ and boundedness of
$A$ imply that such a finite $m$ exists. At the null exceptional
inputs use the zero command. For each cell put

$$
 h_i=k_0+A_s,\quad X=A_t-A_s,\quad Y=B_t-B_s,
 \quad C=W_t-W_s-A_sY.
\tag{17.3}
$$

Use the already supplied inward connector [GL, Lemma 17.1]: set
$d=\rho$ when $h_i\le(l+u)/2$, $d=-\rho$ otherwise, and
$q=C/d$. Its relative vertices are

$$
 (0,0),\ (d,0),\ (d,q),\ (0,q),\ (0,0),\ (0,Y),\ (X,Y),
\tag{17.4}
$$

with each leg assigned exactly $(t-s)/6$ original time units.
Translate by $(A_s,B_s)$, concatenate the cells, and hold from $S$
to $T$. Denote the resulting original controls by $(a_\rho,b_\rho)$
and their actually executed integral by
$J_\rho(v)=\int_0^v a_\rho\,db_\rho$.
Formula (17.4) is a reused geometric supplier; the new input to it
is the returning source law of §§15--16, not a Brownian first level.

**Theorem 17.2 (finite law, prefix guards and the full signed readout limit).**
For every fixed $I,T$ and $\rho$ above, Definition 17.1 defines a
measurable probability law on finite lawful original commands.
Every command has finitely many linear legs of positive duration,
with finite pathwise velocities, and obeys at all prefixes

$$
 k_0+\min_{[0,T]}a_\rho\ge l>0,
 \qquad k_0+\max_{[0,T]}a_\rho\le u<H_{\rm n}.
\tag{17.5}
$$

Its own first observation exit from $(l,u)$ equals $\theta$ whenever
$\theta\le T$, including $\theta=T$; otherwise it has no such exit
on $[0,T]$. Its chronological triple agrees with $(A,B,W)$ at every
partition endpoint and throughout the final hold. With
$K_I=\max(|l-k_0|,|u-k_0|)$ it satisfies

$$
\begin{gathered}
 \|a_\rho-A\|_\infty\le3\rho,\qquad
 \|b_\rho-B\|_\infty\le4\rho,\\
 \|J_\rho-W\|_\infty\le4K_I\rho+4\rho^2.
\end{gathered}
\tag{17.6}
$$

For every deterministic $\rho_n\downarrow0$ in the allowed range,
the complete ten-output held paths of these actual commands converge
almost surely uniformly on $[0,T]$ to $O$. Their probability laws
therefore converge weakly to the original held source-start output
law $\nu_{I,T}$ of §13. The outputs include every ordered signed
component, every factor two and every fixed preparation rotation in
(7.8), with the original $2\pi$ phases and unchanged probabilities.

The selector uses the complete source marks and offline exact
stopped-path information, including $S$ and the cell oscillations
in (17.2). It asserts neither causal or finite-bit acquisition nor
any uniform command count, speed, energy or other resource bound.
Hidden $z$ is never a native command coordinate or readout.

**Proof.** Formula (16.2) is a measurable source path map. The first
exit from the open height interval is a Borel path functional, and
so are its censored value and the stopped path. Continuity at the
interior source gives $S>0$. Supremum functionals in (17.2) can be
evaluated on rational relative fractions of each cell. They are
Borel functions of the path and of $S$; hence the first successful
integer $m$ is measurable. Uniform continuity makes the first two
oscillations tend to zero as $m\to\infty$. The third tends to zero
as well, bounded by the oscillation of $W$ plus $K_I$ times that
of $B$. This proves finite termination for each fixed $\rho$,
without a uniform modulus assumption on the source law.

At every cell start $h_i\in(l,u)$, and its terminal height is in
$[l,u]$; it can lie on the boundary only at $S=\theta\le T$.
Conditions (17.2)--(17.3) imply all the hypotheses of [GL, Lemma
17.1], with the stronger $|X|,|Y|\le\rho$, $|C|\le\rho^2$.
That supplier proves that the entire inward rectangle and phase
leg remain interior, that the final height leg reaches a boundary
only at its terminal time, and that the endpoint relative integral
is exactly $C$. Its prefix bounds are
$|x|\le2\rho$, $|y|\le3\rho$, $|j|\le3\rho^2$.
It does not use a primitive central command. The rectangle actually
executes the real value $dq=C$, with the sign of $C$ unchanged.

Inductively, if the global integral equals $W_s$ at the beginning
of a cell, at its end it is
$W_s+A_sY+C=W_t$. The same induction gives the two first-level
endpoints. Thus there is no reset of the integral at a join, and
the chronological cross term $A_sY$ is retained. For a partial
prefix $v$ in this cell the exact global integral is
$W_s+A_s y(v)+j(v)$. Subtract the target identity
$W_v=W_s+A_s(B_v-B_s)+C_{s,v}$ from (17.2). The just-quoted
supplier bounds give (17.6). After $S$ both triples are held at
their exactly matching endpoint. This also proves (17.5) and exact
observation exit. Since $I$ is strictly inside the original native
slab, boundary arrival for the observation remains strictly lawful
for the original command. The entire numerical command still has
precisely its original domain
$(-\min a_\rho,H_{\rm n}-\max a_\rho)$; the claim is at the fixed
preparation, not uniformly over all starting heights in that domain.

Each of the finitely many cells has positive length and six finite
vertices. The connector and final hold therefore give a finite
list of actual native instructions with finite pathwise variation
and velocities. On each event specifying $m$, their times, vertices,
orientation and slopes are Borel functions of the selected data.
Thus the finite-list command map is measurable. This proves an
actual pushforward command law, not only existence of a conditional
law on unspecified controls.

Apply the supplied lift continuity [GL, Theorem 3.1] to (17.6).
Explicitly the real phase differences are bounded by
$\tfrac12\|b_\rho-B\|_\infty$ and
$|c_0|\|b_\rho-B\|_\infty+r^{-1}\|J_\rho-W\|_\infty$.
Reduce these same phases modulo $2\pi$. The exact ten-output map
(7.8) is uniformly continuous on $I\times\mathbb T^2$, with all
its preparation rotations fixed. It carries uniform triple
convergence to uniform convergence of the complete outputs.
Because every stage has the exact same observation exit on the
horizon, this holds for the held paths as stated. Almost-sure
uniform convergence implies weak convergence of their laws by
bounded continuous tests. Theorem 16.2 identifies the limiting
law as the actual $\nu_{I,T}$. No exact-contact event was passed
through weak convergence. Neither $z$ nor a new central actuator
enters this deterministic selector. All stochastic dependence of
the visible coordinates on $z$ remains part of the declared
complete-mark source law. $\square$

## 18. The source clock is observable from completed preparation-return gaps

**Definition 18.1 (completed gaps and spectral normalization).**
For the exact original source-start ten-output path $O^I$ define its
contact set before observation exit by $\{t<\theta:O_t^I=v_0\}$.
Use the height from (11.6) to determine $\theta$, as in (12.1).
For $t\ge0$ and $\epsilon>0$ let $C_\epsilon^I(t)$ be the number
of connected gaps $(g,d)$ away from the preparation output for
which

$$
 0\le g<d<\theta,\qquad d\le t,\qquad d-g>\epsilon.
\tag{18.1}
$$

Both endpoints must be genuine contacts; $g=0$ is permitted only
when it is such an endpoint. A gap still open at $t$, a gap cut by
observation exit, and the held post-exit segment are excluded. In
particular its partial observed length is never substituted for a
completed duration. These gaps and their counts are Borel functions
of the exact continuous output history through $t$ (and, when exit
has occurred, its observed exit). They can be enumerated by taking
the component containing each rational noncontact time and retaining
its first rational representative. For this enumeration, endpoints
are infima or suprema of the closed zero set of
$|O^I-v_0|$ before exit, which are Borel functionals. Completed gaps
longer than $\epsilon$ are disjoint and fit in $[0,t]$, so there
are finitely many.

Use exactly the denominator $\kappa(\epsilon)$ of (15.2), rather
than a Brownian power or an unnormalized count. It is continuous
and strictly decreasing from infinity to zero as
$\epsilon$ runs from zero to infinity.

**Theorem 18.2 (normalized observable clock, uniformly on finite horizons).**
Under the exact source-start law, on an event of probability one,
for every finite $T$,

$$
 \lim_{\epsilon\downarrow0}
 \sup_{0\le t\le T}
  \left|\frac{C_\epsilon^I(t)}{\kappa(\epsilon)}
                       -\mathsf L_{t\wedge\theta}\right|=0.
\tag{18.2}
$$

In particular the convergence holds uniformly in probability and
recovers the Revuz-$\delta_e$-normalized source clock stopped only
for observation. For $M>0$, $\delta>0$ and
$\kappa(\epsilon)>2/\delta$, one has the explicit localization
bound

$$
\begin{aligned}
 &\mathbb P\left\{
   \sup_{t\le T}\left|
       C_\epsilon^I(t)/\kappa(\epsilon)
                  -\mathsf L_{t\wedge\theta}\right|>\delta\right\}\\
 &\quad\le\mathbb P\{\mathsf L_T>M\}
             +\frac{16M}{\delta^2\kappa(\epsilon)}.
\end{aligned}
\tag{18.3}
$$

The clock and count use the original time units. The normalization
has the spectral and source identities (15.5), (16.8), (16.11);
no factor $1/2$ is inserted.

**Proof.** First reuse the exact all-time result (11.5): before
observation exit the preparation-output contacts are exactly
$\mathsf Z_t=e$, simultaneously for all times, and the held exit
output is different from $v_0$. Thus every completed gap in
(18.1) is exactly one complete excursion interval of (16.2), with
its original duration. This is a use of the supplied detector,
not a new detector or reset theorem. No false-contact issue is
inferred from an approximate command path.

For $\ell\ge0$ write

$$
 N_\epsilon(\ell)=
   \Pi((0,\ell]\times\{\zeta>\epsilon\}).
\tag{18.4}
$$

It is a Poisson counting process in label time, with rate
$\mathbf n(\zeta>\epsilon)=\kappa(\epsilon)$.
The inverse clock is continuous because $\tau$ is strictly
increasing and unbounded. At an elapsed time $s$, every mark with
label strictly smaller than $\mathsf L_s$ has completed; the mark
at $\mathsf L_s$, if there is one, is either the current unfinished
excursion or has just completed. Hence there is at most one
uncounted mark among labels at most $\mathsf L_s$. At
$s=t\wedge\theta$, a possible exit-cut excursion is this same
single mark, and must be excluded even if its partial duration
exceeds $\epsilon$. There is no contact at finite $\theta$,
because its height is $l$ or $u$, different from $k_0$.
Consequently, simultaneously for all $t\le T$,

$$
 \left|C_\epsilon^I(t)
                -N_\epsilon(\mathsf L_{t\wedge\theta})\right|\le1.
\tag{18.5}
$$

Zero ordinary source residence and absence of inverse drift ensure
that no additional source interval is being omitted in this
comparison. Infinite small excursions cause no ambiguity: after
restricting to $\zeta>\epsilon$ both sides count finitely many
marks on bounded label intervals.

The compensated process
$N_\epsilon(\ell)-\kappa(\epsilon)\ell$ is a square-integrable
martingale on $[0,M]$ with terminal variance
$M\kappa(\epsilon)$. The usual martingale maximal inequality yields

$$
 \mathbb E\sup_{\ell\le M}
   \left|N_\epsilon(\ell)/\kappa(\epsilon)-\ell\right|^2
             \le\frac{4M}{\kappa(\epsilon)}.
\tag{18.6}
$$

On $\{\mathsf L_T\le M\}$, (18.5) bounds the supremum in
(18.3) by the label supremum in (18.6) plus
$1/\kappa(\epsilon)$. Markov's inequality with threshold
$\delta/2$ proves (18.3). The clock is finite on finite elapsed
horizons since $\tau$ is unbounded, so this also proves uniform
convergence in probability, first fixing $M$ and then letting it
increase.

For the stronger almost-sure assertion, choose the unique
$\epsilon_j>0$ satisfying $\kappa(\epsilon_j)=j^2$.
Existence follows from the continuous strictly decreasing range
proved in (15.4)--(15.6). For every integer $M$ and every fixed
positive rational tolerance, (18.6) and the summability of
$\sum_j j^{-2}$ imply by Borel--Cantelli that

$$
 \sup_{\ell\le M}|N_{\epsilon_j}(\ell)/j^2-\ell|
                                      \longrightarrow0
                    \quad\hbox{almost surely}.
\tag{18.7}
$$

Take the countable intersection over those $M$ and tolerances.
If $\epsilon_{j+1}\le\epsilon\le\epsilon_j$, monotonicity
of the counts and of their rates gives, simultaneously for all
$\ell\le M$,

$$
 \frac{N_{\epsilon_j}(\ell)}{(j+1)^2}
 \le\frac{N_\epsilon(\ell)}{\kappa(\epsilon)}
 \le\frac{N_{\epsilon_{j+1}}(\ell)}{j^2}.
\tag{18.8}
$$

Since $(j+1)^2/j^2\to1$, the lower and upper bounds both
converge uniformly to $\ell$ on $[0,M]$. Thus (18.7) holds for
all real $\epsilon\downarrow0$. Apply (18.5), and on each sample
choose an integer $M>\mathsf L_T$. A countable intersection over
integer elapsed horizons proves (18.2) simultaneously for every
finite $T$. This argument establishes the convergence mode; it
does not assume independence between $\mathsf L_T$ and the counts.

Finally Theorem 16.2 identifies the reconstructed clock with the
PCAF of Revuz measure $\delta_e$, and (16.11) fixes its exact
normalization. Formula (18.2), involving only the observed path
and the known original-source spectral denominator, therefore makes
that clock observable from the exact history. It recovers its
stopped value at exit by completed pre-exit gaps, even though the
exit-cut gap contributes no completed duration. The full process
and its clock continue after exit; that future is not recovered
from the held observation. $\square$

## 19. Source correspondences and remaining realization obligations

**Definition 19.1 (mature inputs and the source-specific deduction).**
Fukushima--Tanaka Lemma 2.2, Theorem 2.2 and §3.1 Theorem 3.1,
(3.3)--(3.12), supply the general recurrent-point excursion and
inverse-local-time framework. Their measure $m_0=\phi m$ is $m$
here, their $\phi=1$, their $u_\lambda=b_\lambda$, their absorbed
semigroup is the transform of the original $F$, their entrance
measure is $q_t m$, their lifetime measure $\Theta$ has tail
$\kappa$, and their inverse local-time exponent is
$\lambda(u_\lambda,1)=\lambda d_\lambda$. Their local time is
normalized by Revuz measure $\delta_a$, here $\delta_e$.
The original $a$ in our endpoint remains its fixed positive kinetic
coefficient, not the distinguished-point symbol of that paper.
No compactification, Poincare inequality, spectral gap or assumption
A.4 from its independent-extension construction is imported.
Poisson uniqueness and compensation, spectral calculus, and the
martingale inequality used in (18.6) are standard tools inside
these source-specific deductions, not new general theorems.

The additional deduction for this source is the positive density
$J_h^{-1}Fe^{-tF}h$ with its full mark cylinders, the explicit
spectral lifetime and normalization, their original-duration full
endpoint synthesis, the measurable finite native-command consumer
of that particular source, and the completed-preparation-gap clock
with its spectral denominator and uniform convergence. The domain
identification uses [S, §§115--116] exactly; [S, §117]'s
positive-time source densities describe full transitions, whereas
$q_t m$ describes one still-uncompleted excursion and is not a
probability transition density. They are not interchanged.
The mark construction is neither an abstract disintegration of a
supplied full trajectory nor a scalar-lifetime proxy for its
complete law: the actual source input has all of (15.3), and the
path law equality is established before its native output is taken.
These are ordinary source-specific results without a worldwide
priority or Lean-certification claim.

The geometry used in (17.4) and its guards is already [GL, §§2--4,
Lemma 17.1 and Definition 17.2]. Its Brownian offline mesh and
resource conclusions in §§16--18 are not transferred to this
source. The new measurable mesh uses only continuity of the
explicitly generated source and has no expectation or uniform
resource bound. The prefix action is exactly (7.4)--(7.8), including
its central period $2\pi r$ and original phases $2\pi$.
The false-fiber polarity, exact detector and source reset of §§11--12
are reused only at their exact source law. The Brownian-reference
singularity and bounded-weight-mass escape of §§13--14 remain
valid: the marked law changes the first-level source premise;
it is not a bounded reweighting of that planar Brownian reference.
No new version of those exclusions is inferred.

The free hidden-circle rigidity and arbitrary fixed Borel
central-fiber exclusion of §§1--10 remain unchanged. The
[variable-coefficient Green model](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md#1-fixed-model-and-the-exact-question),
[central-noise Green model](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md#1-fixed-source-conditional-law-and-the-matched-operator),
and [spatial-cap and all-real limits](FIB_NATIVE_SPATIAL_CAP_RETAINED_AND_RESONANT_LIMITS.md#12-the-all-real-parameter-operator-limit)
retain their different carriers, wall conditions, clocks and source
domains. They supply no substitution for $H$, $F$, $h$ or $m$
in this construction. The lawful nonlinear/source-law possibility
in [B, §12.3] is consistent with this additional marked source
premise; its affine/CPTP obstruction is not repeated or overturned.

**Definition 19.2 (the exact positive construction and unpaid boundary).**
The established correspondence is a complete marked returning
source, an original-duration full endpoint law, and, for each fixed
$I,T$, a sequence of measurable laws on original finite lawful
commands whose actual complete held outputs converge to the
original source-start observation. The auxiliary $z$ information
is kept in the source law and discarded only by the native
readout; it is not a native control. Formula (18.2) is an exact-law
history functional, not a finite-resolution detector, and is not
asserted for approximate command paths merely because their laws
converge weakly.

Acquisition of the Poisson source and its complete marks from the
bare native system remains unresolved. The offline selector uses
exact exit and modulus information and has no causal, finite-bit,
finite-shot or uniform resource realization claim. A family of
finite native-command laws does not supply arbitrary-intervention
equivalence or a source-independent affine/CPTP implementation.
The map $\Psi$ still has only its original slab domain; there is
no native map after slab exit, even though the full endpoint
continues conservatively there. The full native legal-source,
evolution, representation and readout correspondence, and the
physical spatial dimension, remain unpaid. No finite result here
settles the continuing why-three programme.

## 追加锚（本行以下为增补区）


## 20. Finite source samples with explicitly normalized joint laws

**Definition 20.1 (unchanged endpoint and the finite sampling premise).**
Retain every datum of Definitions 7.1, 11.1 and 15.1, in particular
$F,h,m$, the original entrance law $q_t m$, killed transition kernel
$P_t^0$, spectral probability $\nu$, and lifetime tail $\kappa$.
The full operator is still $H$, with the entire complex selector
(112.5); $F$ is used only in its already established source-killed
role (15.1). Fix a finite original elapsed horizon $T>0$, a local-time
budget $\Lambda>0$, and deterministic $0<\epsilon,\delta\le1$.
The local-time budget is not an elapsed-time horizon. Put

$$
\begin{gathered}
 \mathfrak d(v)=\int_{(0,\infty)}s^2e^{-vs}\nu(ds),\qquad v>0,\\
 \beta_\epsilon=\int_0^\epsilon v\mathfrak d(v)\,dv,
 \qquad
 \chi_\epsilon(\lambda)=\int_0^\epsilon
           (1-e^{-\lambda v})\mathfrak d(v)\,dv,\\
 \mathcal D_{\delta,T}=
       \{j\delta: j\ge1,\ j\delta<T\}\cup\{T\},
 \qquad M_\delta=\lceil T/\delta\rceil.
\end{gathered}
\tag{20.1}
$$

Thus $\mathfrak d$ is the original excursion-duration density, not
an additional spectral measure or a new source condition. The grid
contains at most $M_\delta$ positive times and has gaps at most
$\delta$ when zero is included.

The added interface supplies exact samples of the following finite
list, with the joint laws specified in Lemma 20.2 and Definition 20.3:
a Poisson count, ordered real labels, one duration and finitely many
four-coordinate evaluations for each retained excursion, and one
nonnegative scalar duration total in each intervening label interval.
These are exact-real sampling primitives. No continuous excursion
mark, entire source trajectory, target observation-exit flag, or
target modulus is supplied. In particular the intervening scalar is
literally a sum of durations; it does not specify the small excursions'
positions, shapes or individual lifetimes. All four sampled coordinates,
including hidden $z$, belong to the added source information. Sampling
$z$ is neither an original observation nor a native actuator.

**Lemma 20.2 (joint duration and finite entrance/killed samples).**
For any deterministic $0<t_1<\cdots<t_j<v$, define a finite measure
on $M^j$ by

$$
\begin{aligned}
 \mathcal C_v^{t_1,\ldots,t_j}(dp_1\cdots dp_j)
  ={}&q_{t_1}(p_1)m(dp_1)
       P^0_{t_2-t_1}(p_1,dp_2)\cdots\\
    &\hspace{12mm}P^0_{t_j-t_{j-1}}(p_{j-1},dp_j)
                          q_{v-t_j}(p_j).
\end{aligned}
\tag{20.2}
$$

For $j=1$ there is no transition factor. For $j=0$, the measure on
the singleton empty tuple has mass $\mathfrak d(v)$. In every case
the total mass in (20.2) is $\mathfrak d(v)$, a finite strictly
positive number. Integrating out any evaluation gives the same
formula with that evaluation deleted. Jointly measurable versions
can be used, and versions on null sets do not affect these measures.

Consequently the following is a probability law on finite tuples:

$$
 \mathbb P\bigl(V\in dv,\ (P_t)_{t\in\mathcal D_{\delta,T},\,t<v}
                              \in d\mathbf p\bigr)
  =\frac{\mathbf1_{\{v>\epsilon\}}}{\kappa(\epsilon)}
       \mathcal C_v^{\mathcal D_{\delta,T}\cap(0,v)}
                              (d\mathbf p)\,dv.
\tag{20.3}
$$

The tuple includes precisely the listed evaluations at times strictly
less than $V$. The values at zero and at a finite completed duration
are $e$, deterministically. If $V>T$, the tuple includes the evaluation
at $T$. This is exactly the finite evaluation-and-duration marginal
of $\mathbf n(\,\cdot\mid\zeta>\epsilon)$, with no full mark required
as an input.

**Proof.** Spectral calculus and (15.4) give
$0<\mathfrak d(v)<\infty$ and
$\int_\epsilon^\infty\mathfrak d(v)dv=\kappa(\epsilon)$.
The nonnegative jointly measurable densities $q_t$ may be chosen as
in Theorem 15.2. The transition kernel is the original part-process
kernel. At every node its distributions are absolutely continuous
with respect to $m$: symmetry of $P_t^0$ preserves this property
under transition, and multiplication by a bounded cylinder test
preserves it as well. Properly exceptional sets and changes of
$d m$-versions therefore do not affect the expressions.

The identities $P_s^0q_t=q_{s+t}$ and symmetry show that the integral
of (20.2), for $j\ge1$, is

$$
 \langle q_{t_1},q_{v-t_1}\rangle_{L^2(m)}
   =\langle Fe^{-t_1F}h,Fe^{-(v-t_1)F}h\rangle_{L^2(\mu)}
   =\mathfrak d(v).
\tag{20.4}
$$

Integrating an interior node uses Chapman--Kolmogorov. Integrating
the first uses the entrance identity; integrating the last uses
$P_s^0q_t=q_{s+t}$. These prove finite consistency, including the
empty tuple. Products of Borel kernels give joint measurability
on each region $v>t_j$.

To check that the terminal factor specifies the original duration,
not just a normalized candidate, use (15.4):
$-\partial_s P_s^0 1=q_s$ in $L^2(m)$ for $s>0$.
Its integrated nonnegative version says that the remaining killed
lifetime at $p$ has density $q_s(p)ds$, for $m$-almost every $p$.
Indeed integrate the $L^2$ identity over any positive compact time
interval, then use monotonicity of survival and Fubini. Insert this
density after the last node of (15.3). It gives (20.2) times $dv$
as the joint measure of the evaluations and $\zeta\in dv$.
There is no infinite-lifetime atom by (15.4). Partitioning the
$v$-axis at the finitely many times of $\mathcal D_{\delta,T}$
then gives (20.3). Its normalization is the preceding integral of
$\mathfrak d$. This proof uses only the established excursion
cylinders and killed survival, not a bridge conditioned to hit an
exceptional point at a fixed time. $\square$

**Definition 20.3 (the finite list and its independence).**
Draw $\mathsf N\sim\operatorname{Poisson}(\Lambda\kappa(\epsilon))$.
Given $\mathsf N=n$, take $n$ independent uniform labels on
$(0,\Lambda)$ and order them as
$0<\ell_1<\cdots<\ell_n<\Lambda$. Set $\ell_0=0$ and
$\ell_{n+1}=\Lambda$. Independently of these labels, take $n$
independent tuples $(V_i,\mathbf P_i)$ with law (20.3).
Conditional on the ordered labels, independently of those tuples
and independently for $i=0,\ldots,n$, draw $U_i\ge0$ with law

$$
 \mathbb E[e^{-\lambda U_i}\mid\ell_1,\ldots,\ell_n]
   =\exp[-(\ell_{i+1}-\ell_i)\chi_\epsilon(\lambda)],
       \qquad \lambda\ge0.
\tag{20.5}
$$

This declares conditional independence. The $U_i$ need not be
unconditionally independent of the ordered labels or of each other.
There is no additional independent resampling of the terminal state
of an excursion. Its completed terminal state remains $e$.

**Proposition 20.4 (existence, source coupling and finite primitive counts).**
Equations (20.3)--(20.5) define a normalized Borel probability law
on a countable disjoint union of finite-dimensional spaces.
Under a proof coupling with the original Poisson source of §16,
the $V_i,\mathbf P_i$ are exactly its evaluations on the atoms
with $\ell\le\Lambda$, $\zeta>\epsilon$, and

$$
 U_i=\sum_{\ell_i<\ell<\ell_{i+1},\,\zeta\le\epsilon}\zeta,
 \qquad
 C_\Lambda:=\sum_{i=0}^{\mathsf N}U_i+
                     \sum_{i=1}^{\mathsf N}V_i=\tau_\Lambda.
\tag{20.6}
$$

Endpoints at the listed labels cause no ambiguity: the small-atom
process has no atom at any of these independent labels. Almost surely
every listed random variable is finite, and

$$
\begin{gathered}
 \mathbb E C_\Lambda=\Lambda,\qquad
 \mathbb E\sum_{i=0}^{\mathsf N}U_i=\Lambda\beta_\epsilon,
 \qquad \beta_\epsilon\downarrow0\quad(\epsilon\downarrow0),\\
 \mathbb P(C_\Lambda<T)
       \le\min(1,e^{\lambda T-\Lambda\varphi(\lambda)})
                  \quad(\lambda>0).
\end{gathered}
\tag{20.7}
$$

Counting one call for the count, one per uniform label, one per tuple
(20.3), and one per scalar (20.5), the number of calls is
$3\mathsf N+2$, with expectation $3\Lambda\kappa(\epsilon)+2$.
Counting instead all supplied real coordinate entries and the one
integer count gives the upper bound

$$
 2+(3+4M_\delta)\mathsf N,
 \qquad
 \mathbb E[\text{entries}]
       \le2+(3+4M_\delta)\Lambda\kappa(\epsilon).
\tag{20.8}
$$

These count exact samples and entries, not bits, shots, computational
operations or native physical resources. The count is finite almost
surely, not bounded deterministically. For example
$\mathbb P(\mathsf N>B)\le\Lambda\kappa(\epsilon)/B$ for $B>0$.

**Proof.** Since $\mathbf n[\zeta]=1$, the measure
$\mathbf1_{(0,\epsilon]}(v)\mathfrak d(v)dv$ has finite first
moment $\beta_\epsilon\le1$. Its drift-zero subordinator increment
of parameter $d\ge0$ exists, with Laplace transform
$e^{-d\chi_\epsilon(\lambda)}$. One elementary construction of
this scalar law is the monotone limit of compound Poisson sums
restricted to $b<v\le\epsilon$ as $b\downarrow0$; their means
are bounded by $d\beta_\epsilon$, so the limit is finite almost
surely. The Laplace transforms pass by bounded convergence.
Uniqueness of Laplace transforms identifies (20.5). Dependence of
the law on $d$ is Borel; for instance the associated increments are
continuous in probability since their expected difference over
an increment of length $c$ is $c\beta_\epsilon$.
This construction proves existence of a scalar distribution. It
places no infinite list in the sampling interface.

The Poisson restriction to $\zeta>\epsilon$ has finite rate
$\kappa(\epsilon)$. The marking and restriction properties of a
Poisson measure give exactly the count, ordered labels and tuple
law above; its restriction to $\zeta\le\epsilon$ is independent.
Its duration sums on disjoint label intervals have (20.5).
This proves the asserted joint law and the coupling. These are
standard Poisson properties, here with the intensity (15.3), not
an additional construction of a complete-mark source.

Compensation gives both expectations in (20.7), and dominated
convergence of $\int_0^\epsilon v\mathfrak d(v)dv$ gives its limit.
The Laplace transform of (20.6) is

$$
 \mathbb E e^{-\lambda C_\Lambda}
 =\exp\left[-\Lambda\left(\chi_\epsilon(\lambda)
       +\int_\epsilon^\infty(1-e^{-\lambda v})
                                       \mathfrak d(v)dv\right)\right]
 =e^{-\Lambda\varphi(\lambda)}.
\tag{20.9}
$$

Markov's inequality applied to $e^{-\lambda C_\Lambda}$ gives
the coverage bound. Counting the one integer, $\mathsf N$ labels,
$\mathsf N$ durations, $\mathsf N+1$ scalar totals and at most
$4M_\delta\mathsf N$ coordinate entries proves (20.8).
The preceding normalization and Borel kernels prove the remaining
measurability assertions. $\square$

## 21. Same-time finite source interpolation and observation exits

**Definition 21.1 (the finite interpolated source).**
For each tuple in (20.3), interpolate its four ordinary real
coordinates linearly between zero at age zero, its sampled nodes,
and zero at age $V_i$ if $V_i\le T$. If $V_i>T$, interpolate only
up to its sampled value at age $T$. Denote this finite polygon by
$Q_i$ on $[0,\min(V_i,T)]$. The zero vector denotes $e$ in the
fixed coordinates of $G$; interpolation is coordinate interpolation,
not group multiplication and not a native command.

Put

$$
 b_i=\sum_{j=0}^{i-1}U_j+\sum_{j=1}^{i-1}V_j,
       \qquad 1\le i\le\mathsf N.
\tag{21.1}
$$

On $[0,T]$ set $\widehat{\mathsf Z}_t=Q_i(t-b_i)$ when
$b_i\le t\le b_i+V_i$ for a retained excursion whose interval
meets $[0,T]$. Set it equal to $e$ at all remaining times,
including after $C_\Lambda$ if $C_\Lambda<T$.
Zero-length intervals are omitted. The definitions agree at all
joins and give a continuous finite polygon on $[0,T]$.
Every retained interval has its entire original duration $V_i$;
only the portion intersecting the horizon needs evaluation.
Every $U_i$ is represented by an interval of that exact length.
No duration is deleted or redistributed among retained intervals.

**Theorem 21.2 (original-time source approximation and coverage error).**
The finite-list map in Definition 21.1 is Borel. Under the source
coupling in Proposition 20.4, all retained interval starts and ends
are exactly their original elapsed times in (16.2).
For the maximum norm on the four coordinates write

$$
 \Omega_R(q;v)=\sup_{s,t\in[0,R],\,|s-t|\le v}|q_t-q_s|_\infty.
\tag{21.2}
$$

On $\{C_\Lambda\ge T\}$ one has the same-time bound

$$
 \|\widehat{\mathsf Z}-\mathsf Z\|_{[0,T],\infty}
      \le\Omega_{T+1}(\mathsf Z;\epsilon\vee\delta).
\tag{21.3}
$$

In particular for $a_*>0$, $\lambda>0$,

$$
\begin{aligned}
 \mathbb P(\|\widehat{\mathsf Z}-\mathsf Z\|_{[0,T],\infty}>a_*)
 \le{}&\min(1,e^{\lambda T-\Lambda\varphi(\lambda)})\\
 &+\mathbb P(\Omega_{T+1}(\mathsf Z;
                         \epsilon\vee\delta)>a_*).
\end{aligned}
\tag{21.4}
$$

For every deterministic $\Lambda_n\uparrow\infty$ and
$\epsilon_n,\delta_n\downarrow0$, the finite-list laws admit a
common proof coupling on which their paths converge uniformly on
$[0,T]$ almost surely to the original full source-start process.
Their laws consequently converge weakly to its original law.
This includes hidden $z$ in the source approximation. The modulus
in (21.3)--(21.4) is a proof quantity; the finite-list map never
queries it.

**Proof.** In the coupling, $U_i$ sums exactly all small durations
between the two successive retained labels. There is no inverse-clock
drift by (16.1). Thus (21.1) is exactly $\tau_{\ell_i-}$, and
$b_i+V_i=\tau_{\ell_i}$, proving elapsed-time correctness.
On one discarded excursion of duration at most $\epsilon$,
$\mathsf Z$ is within $\Omega_{T+1}(\mathsf Z;\epsilon)$ of its
initial value $e$ at every relevant time. Although its individual
location inside a represented $U_i$ was not sampled, the approximation
is $e$ throughout that whole interval, so the same bound applies.
At a source time both paths have value $e$.
On a retained excursion, each polygon value is a convex combination
of two true coordinate values at times at most $\delta$ apart.
For a time at most $T$, both endpoints used are at most $T+\delta$.
Each is within $\Omega_{T+1}(\mathsf Z;\delta)$ of the true value
at that time. This proves (21.3), hence (21.4).

By §16, $\tau_\Lambda\uparrow\infty$ almost surely as
$\Lambda\uparrow\infty$. Thus coverage holds eventually under
the common Poisson coupling. The continuous path $\mathsf Z$ is
uniformly continuous on $[0,T+1]$, so (21.3) tends to zero almost
surely. The construction has the stipulated finite marginal law
at each stage; this coupling is not an extra path input. Independent
stage draws retain the weak-convergence conclusion, without a claim
that they converge almost surely to one another. Finite lists of
sums, comparisons and coordinate interpolations prove the Borel
assertion. $\square$

**Lemma 21.3 (the original source strictly crosses each observation wall).**
Fix exactly $I=[l,u]\Subset(0,H_{\rm n})$ with $l<k_0<u$.
Let $\theta$ be the original observation exit in (17.1).
On $\{\theta<\infty\}$ the height
$k_0+x(\mathsf Z_t)$ strictly crosses its attained boundary
arbitrarily soon after $\theta$, almost surely. Consequently, if
continuous paths $q_n$ starting at $e$ converge uniformly to
$\mathsf Z$ on $[0,T]$, their censored first observation exits
$S_n=T\wedge\inf\{t:k_0+x(q_n(t))\notin(l,u)\}$ satisfy
$S_n\to S=T\wedge\theta$ almost surely, and

$$
 \|q_n(\,\cdot\wedge S_n)
           -\mathsf Z(\,\cdot\wedge S)\|_{[0,T],\infty}\to0.
\tag{21.5}
$$

**Proof.** Both observation walls have $x=l-k_0\ne0$ or
$x=u-k_0\ne0$, so every wall point is in $M$ and has a relatively
compact neighbourhood disjoint from the singular source. On such
a neighbourhood $h$ is smooth and positive. The local generator
of the actual transformed form [S, (115.15)] is

$$
 \mathscr A=a\sum_{j=1}^3X_j^2+\eta\partial_w^2
       +2a\sum_{j=1}^3(X_j\log h)X_j
       +2\eta(\partial_w\log h)\partial_w.
\tag{21.6}
$$

The potential cancels by $S_{\min}^*h=0$. Its principal matrix is
locally uniformly positive by [S, (115.10)]. Smooth local SDE
uniqueness identifies the associated diffusion up to neighbourhood
exit, on the legitimate process versions; the path avoids the
properly exceptional set. In particular its height increment from
a wall, up to that local exit, is

$$
 dx_t=\sqrt{2a}\,dB_t+2a\,\partial_x\log h(\mathsf Z_t)dt.
\tag{21.7}
$$

The drift is bounded on a smaller compact neighbourhood. Brownian
motion has positive and negative oscillations arbitrarily close to
zero which dominate every bounded multiple of elapsed time, for
example by its small-time law of the iterated logarithm. Thus
(21.7) crosses both sides of its initial height immediately.
Continuity makes the neighbourhood exit time positive. Apply the
strong Markov property at $\theta$, localized to a countable cover
of the two walls, to obtain the asserted strict outward crossings.
This argument uses neither regularity at the singular source nor
a Brownian first-level law for the whole process.

For the exit conclusion, every compact time interval strictly before
$S$ has a positive distance of the target height from the two walls.
Uniform convergence gives $\liminf S_n\ge S$. If $S<T$, an outward
crossing in every interval $(S,S+b)$, $0<b<T-S$, gives
$\limsup S_n\le S+b$. If $S=T$, the upper bound $S_n\le T$
already suffices. This includes the case $\theta=T$ without needing
any sampled information beyond $T$. Hence $S_n\to S$.
The stopped-path difference is bounded by
$\|q_n-\mathsf Z\|_{[0,T],\infty}
 +\Omega_T(\mathsf Z;|S_n-S|)$, which proves (21.5).
Uniform convergence has therefore been supplemented by the needed
crossing theorem, not used as a hitting-time theorem by itself.
$\square$

**Proposition 21.4 (finite-horizon held error statement).**
For $b>0$, put $H_t=k_0+x(\mathsf Z_t)$ and, with $S=T\wedge\theta$,

$$
\begin{aligned}
 D_-(b)&=\min_{0\le t\le(S-b)_+}\min(H_t-l,u-H_t),\\
 D_+(b)&=\begin{cases}
 \displaystyle\max_{S\le t\le S+b}\max(l-H_t,H_t-u),
                      &S\le T-b,\\
 +\infty,             &S>T-b,
 \end{cases}
 \qquad D(b)=\min(D_-(b),D_+(b)).
\end{aligned}
\tag{21.8}
$$

Then $D(b)>0$ almost surely. For the finite interpolation put
$\widehat S=T\wedge\inf\{t:k_0+x(\widehat{\mathsf Z}_t)
\notin(l,u)\}$. If its unstopped coordinate error is at most
$a_*<D(b)$, then

$$
 |\widehat S-S|\le b,\qquad
 \|\widehat{\mathsf Z}(\,\cdot\wedge\widehat S)
       -\mathsf Z(\,\cdot\wedge S)\|_{[0,T],\infty}
       \le a_*+\Omega_T(\mathsf Z;b).
\tag{21.9}
$$

For $S<b$, the lower exit bound is automatic and $D_-(b)$ may
still be taken at time zero as written.

**Proof.** The interval ending at $(S-b)_+$ precedes the first exit,
or consists of the interior initial point, giving $D_-(b)>0$.
When $S\le T-b$, it is a finite exit and Lemma 21.3 gives a strict
outward overshoot before $S+b$, so $D_+(b)>0$. Otherwise the upper
exit bound follows from $\widehat S\le T<S+b$. Uniform height
error smaller than $D_-(b)$ prevents an earlier exit before $S-b$,
and error smaller than $D_+(b)$ forces an exit by $S+b$ whenever
that condition is needed. The stopped-coordinate inequality follows
as in (21.5). These margins are used to express a probability bound;
they are not queried by the finite construction. $\square$

## 22. A finite-input law on actual native histories and all ten outputs

**Definition 22.1 (finite-data stopping and connector partition).**
Compute $\widehat S$ from the finite polygon of Definition 21.1,
using its linear height segments, and hold its coordinate triple

$$
 (A_t,B_t,W_t)=(x,y,w)(\widehat{\mathsf Z}_{t\wedge\widehat S})
                  \quad(0\le t\le T).
\tag{22.1}
$$

This is the approximating polygon's own exit, computed from the
acquired data. It is not the original target's $S$.
Let $K_I=\max(|l-k_0|,|u-k_0|)$ and
$0<\rho\le(u-l)/4$. Partition $[0,\widehat S]$ at every polygon
vertex. For each of its positive-length linear cells with total
increments $(\Delta A,\Delta B,\Delta W)$ subdivide into $m$ equal
time cells, where

$$
 m=\max\left(1,
 \left\lceil\frac{|\Delta A|}{\rho}\right\rceil,
 \left\lceil\frac{|\Delta B|}{\rho}\right\rceil,
 \left\lceil\frac{|\Delta W|+K_I|\Delta B|}{\rho^2}
                                                \right\rceil\right).
\tag{22.2}
$$

At every resulting cell $[s,t]$, set
$X=A_t-A_s$, $Y=B_t-B_s$, $C=W_t-W_s-A_sY$.
Execute the already supplied original six-leg inward connector
(17.4), with start height $k_0+A_s$, relative endpoint $(X,Y,C)$,
and exactly $(t-s)/6$ original time for each leg. Translate its
two controls by $(A_s,B_s)$, concatenate, and hold from
$\widehat S$ to $T$. Denote these actual controls by
$(a_{\epsilon,\delta,\Lambda,\rho},
  b_{\epsilon,\delta,\Lambda,\rho})$, and their actual integral
by $J=\int a\,db$. These definitions use only the finite list and
deterministic parameters. Hidden $z$ is discarded at this stage;
neither $w$ nor $z$ is commanded directly.

**Theorem 22.2 (complete finite-source-information correspondence).**
For every fixed $I,T$ and parameters above, Definition 22.1 is a
Borel map from the normalized finite source list to a finite lawful
original native history. At every prefix it satisfies

$$
 l\le k_0+a(t)\le u,\qquad
 0<k_0+\min a\le k_0+\max a<H_{\rm n}.
\tag{22.3}
$$

Its entire original command domain is still
$(-\min a,H_{\rm n}-\max a)$, with the original concatenation
and refusal guards. If the polygon has an observation exit by $T$,
the command's own first observation exit is exactly that same time;
otherwise it has no observation exit on the horizon. Its real
chronological triple agrees with (22.1) at every connector endpoint,
and satisfies

$$
 \|a-A\|_\infty\le3\rho,\qquad
 \|b-B\|_\infty\le4\rho,\qquad
 \|J-W\|_\infty\le4K_I\rho+4\rho^2.
\tag{22.4}
$$

If $R_0$ is the number of linear cells before $\widehat S$, then
$R_0\le\mathsf N(M_\delta+2)+1$. Writing $V_A,V_B,V_W$ for
the three finite variations on $[0,\widehat S]$, the number of
linear native legs, including a possible final hold, is bounded by

$$
 6\left(R_0+\frac{V_A+V_B}{\rho}
                  +\frac{V_W+K_IV_B}{\rho^2}\right)+1.
\tag{22.5}
$$

All executed velocities are finite pathwise. No uniform speed or
energy bound is asserted.

Let $\mathcal O^{\epsilon,\delta,\Lambda,\rho}$ be the complete ten
held outputs of this actual command. For every deterministic
$\Lambda_n\uparrow\infty$ and
$\epsilon_n,\delta_n,\rho_n\downarrow0$ in the stated ranges,
there is a proof coupling such that

$$
 \|\mathcal O^{\epsilon_n,\delta_n,\Lambda_n,\rho_n}
                              -O^I\|_{[0,T]}\longrightarrow0,
 \qquad
 \widehat S_n\longrightarrow T\wedge\theta_I
                      \quad\hbox{almost surely}.
\tag{22.6}
$$

Thus their probability laws converge to the original
$\nu_{I,T}$ in the uniform ten-output held-path topology (13.1).
The probabilities, phases of period $2\pi$, signed pairs, factors
two and every fixed preparation rotation are precisely (7.3),
(7.5) and (7.8). This is a conditional correspondence for the added
finite source interface; it is not bare-native acquisition.

**Proof.** The finite source polygon starts at $e$, so
$\widehat S>0$. All its heights before $\widehat S$ are interior,
and its height at $\widehat S$ is in $I$. Its finitely many vertices
and its own first height exit are Borel functions of the list;
a linear segment's first boundary intersection is found by a
comparison and a linear ratio, with the constant-segment case
handled separately.

On every subdivision in (22.2), linearity gives
$|X|,|Y|\le\rho$, and, since $|A_s|\le K_I$,
$|C|\le\rho^2$. At an intermediate time $v$ in the same cell,
$W_v-W_s-A_s(B_v-B_s)$ is linear in $v$ and has absolute value
at most $\rho^2$. Thus the finite-data partition satisfies exactly
the oscillation inequalities used in Theorem 17.2, now for this
known polygon, without asking the original source for a modulus.
Apply the already proved connector geometry [GL, Lemma 17.1] and
the deterministic prefix/integral argument of Theorem 17.2.
They give (22.3)--(22.4), the endpoint identities, and equality
of the command's observation exit with the polygon's own exit.
The observation walls are strictly inside the original slab, so
arrival and holding there obey the strict original guard.
The relative rectangle executes $dq=C$, with its real sign;
translation retains the cross term $A_sY$. Hence at a join its
new global integral is $W_s+A_sY+C=W_t$. No central reset or
new primitive is used.

There are at most $M_\delta+1$ polygon cells per retained mark
and $\mathsf N+1$ intervening holds. Clipping at $T$ and then at
the first observation exit does not increase this count, giving
the bound for $R_0$. For each original cell the maximum of the
three ceilings and one in (22.2) is at most one plus the sum of
their nonnegative arguments. Summing gives (22.5). Every resulting
cell has positive length and finite vertices, so all six assigned
durations are positive and all slopes finite. Ceilings, orientations,
finite sums and the connector formulas are Borel on the countable
disjoint union of finite-list spaces. This establishes an actual
finite-input pushforward law on the command space of Definition
17.1, with no unspecified control-selection kernel.

Under the common proof coupling, Theorem 21.2 gives uniform source
convergence and Lemma 21.3 gives the censored exits and stopped
triples' convergence. Equation (22.4) then gives convergence of
the actual chronological triples to
$(x,y,w)(\mathsf Z_{\,\cdot\wedge S})$. Apply the supplied native
lift continuity [GL, Theorem 3.1]. In particular the real phases
are exactly

$$
 \alpha(t)=\alpha_0+b(t)/2,\qquad
 \beta(t)=\beta_0+c_0b(t)-J(t)/r.
\tag{22.7}
$$

Only then reduce modulo $2\pi$ and apply (7.8). That map is
uniformly continuous on $I\times\mathbb T^2$, and retains all
five ordered signed pairs and their fixed rotations. Its limiting
held path is exactly (17.1), whose law is $\nu_{I,T}$ by §16.
This proves (22.6) and weak convergence. The six legs consume the
same original time cell; the scalar totals in (20.6) preserve all
hidden durations. Neither step changes the original clock.
$\square$

**Corollary 22.3 (finite-stage accuracy under the declared interface).**
There is a finite constant $C_I$ such that the map from real triples
to the ten outputs in (7.3), (7.8), restricted to heights in $I$,
is $C_I$-Lipschitz for the maximum norm. Set
$d_\rho=\max(4\rho,4K_I\rho+4\rho^2)$.
For every $a_*,b,c>0$ and $\lambda>0$, under the proof coupling,

$$
\begin{aligned}
 &\mathbb P\left(
 \|\mathcal O^{\epsilon,\delta,\Lambda,\rho}-O^I\|_{[0,T]}
                      >C_I(d_\rho+a_*+c)\right)\\
 &\quad\le\min(1,e^{\lambda T-\Lambda\varphi(\lambda)})
       +\mathbb P(\Omega_{T+1}(\mathsf Z;
                                 \epsilon\vee\delta)>a_*)\\
 &\qquad\quad+\mathbb P(D(b)\le a_*)
       +\mathbb P(\Omega_T(\mathsf Z;b)>c).
\end{aligned}
\tag{22.8}
$$

The same right side without the last term bounds
$\mathbb P(|\widehat S-S|>b)$.
For every desired output error $e_*>0$ and failure probability
$p_*>0$, deterministic finite choices of
$\Lambda,\epsilon,\delta,\rho$ make the left probability at
threshold $e_*$ smaller than $p_*$. They use finitely many exact
sampling entries in expectation by (20.8), and finitely many actual
native legs pathwise by (22.5). No target-path queries are added by
this assertion. A numerical effective rate for choosing the
parameters from $(e_*,p_*)$ is not asserted.

**Proof.** The square-root amplitudes in (7.8) have bounded derivatives
on $I$; the phase derivatives in (22.7) are constant and sine and
cosine are globally Lipschitz. This gives the claimed $C_I$, including
the Euclidean norm on the ten outputs after enlarging the constant.
Outside the four exceptional events in (22.8), (21.3) and (21.9)
bound the stopped triple error by $a_*+c$ and its censored exit
error by $b$. Add (22.4) and apply that Lipschitz map. The union
bound proves (22.8) and the lifetime version.

For the existence assertion, first make $d_\rho$ and $c$ small
enough for the required output threshold, then choose $b>0$ with
the last probability small, using continuity. For this fixed $b$,
$D(b)>0$ almost surely, so choose $a_*>0$ small enough for both
the threshold and the third probability. Choose $\epsilon,\delta$
small enough for the second probability by continuity, and finally
choose finite $\Lambda$ large enough for the first by
$\varphi(\lambda)>0$. These are deterministic law-dependent choices;
none is a measurement of a sampled target path. The finite primitive
and command bounds are already established. $\square$

## 23. Mature methods and the precise finite-information boundary

**Definition 23.1 (supplier correspondence and scope).**
The entrance and returning-excursion law is exactly §15, with the
recurrent framework of Fukushima--Tanaka,
[*Poisson point processes attached to symmetric diffusions*,
§3.1, Theorem 3.1 and (3.12)](https://www.numdam.org/item/AIHPB_2005__41_3_419_0.pdf).
Their distinguished point is $e$, absorbed semigroup is $P_t^0$,
entrance measure is $q_t m$, and speed measure is the unchanged
$h^2\mu$. All its required recurrent-point and original-domain
hypotheses were checked in Theorem 15.2; no compactification or
Poincare hypothesis from that paper's different construction is used.
Equation (20.2) adds the original duration density as a terminal
factor by differentiation of killed survival. It is a finite
joint law, not a new general bridge theorem.

Replacing small excursions by the source at their original times is
the mature truncation map in Lambert--Simatos,
[*The weak convergence of regenerative processes using some excursion
path decompositions*, §3.2, (3) and Lemma 3.1](https://www.numdam.org/item/10.1214/12-AIHP531.pdf),
with their size functional equal to original duration $\zeta$.
Poisson restriction, marking, scalar subordinator sums and coordinate
interpolation are likewise mature tools. The direct bound (21.3)
specializes these tools to this continuous source and keeps every
duration. No general regenerative-convergence theorem is claimed.
Yano, [*Functional limit theorems for processes pieced together from
excursions*, arXiv:1309.2652v3, Definition 2.3, Remark 2.4 and
Theorem 2.5](https://arxiv.org/html/1309.2652v3), explicitly separates
path convergence from lifetime convergence. Its full theorem and its
general convergence hypotheses are not invoked here: retained
excursion durations and starts agree exactly by (20.6), and the
observation-exit passage is separately proved in Lemma 21.3.

Chaumont--Uribe Bravo,
[*Markovian bridges: weak continuity and pathwise constructions*,
arXiv:0905.2155v3, Theorem 1 and (H1)--(H3)](https://arxiv.org/html/0905.2155v3),
requires Feller and transition-density continuity hypotheses for its
bridge construction. No such bridge from the singular source is
assumed or invoked here. The finite measures (20.2) follow directly
from the original entrance/killed suppliers; no unverified bridge
hypothesis or endpoint heat-kernel value is imported.

The repo-derived source-specific composite conclusion is (20.3)--(22.8): a finite
explicitly normalized source interface, exact scalar accounting for
all omitted shapes' elapsed durations, same-time approximation of
the unchanged full source, justified observation exits, and a Borel
consumer in actual finite lawful native commands preserving all ten
held outputs in the limit. Its deterministic connectors, prefix
guards, real chronological integral and phase map are the already
paid results of §7, Theorem 17.2 and [GL, Lemma 17.1 and Theorem
3.1]. Its full limiting source, complex selector, measure and source
response are §16 and [S, §§115--116]. No new claim about the source
clock of §18 is drawn from these approximate laws.

The free diffusion rigidity of §§1--6, central-fiber exclusion of
§§7--10, source-contact and Brownian-reference exclusions of
§§11--14, and the affine/CPTP obstruction of [B, §12.2] are unchanged.
The nonlinear/source-law action in [B, §12.3] retains its original
contract. Variable-coefficient Green, independent central-noise Green,
and spatial-cap/all-real limit suppliers retain the different carriers,
walls, sources and clocks specified in Definition 19.1. None replaces
$F,h,m$, the raw unit-source degree-$-3$ $\Gamma$, fixed
$a,\eta>0$, $g_c=16\sqrt{a\eta}$ or the entire original complex
domain. Coordinate polygons and their observation holds are finite
approximations, not replacement source boundary conditions.

**Definition 23.2 (remaining acquisition and realization obligations).**
The new premise is the ability to draw the finite lists with exactly
(20.3)--(20.5). Their shapes are given by finitely many genuine
source evaluations and their hidden durations by scalar original
inverse-clock increments. Complete continuous marks and queries
for the original trajectory's exact observation exit or modulus
are unnecessary construction inputs under this premise.
The proof coupling may contain complete paths, but the consumer
receives only the displayed finite entries and uses only their
specified evaluations and duration sums. Hidden $z$ remains part
of the joint source law and never becomes native control or output.

Acquisition of these exact-real samplers from bare native operations
remains unresolved. Labels, durations, finite skeletons and aggregate
small-duration totals are available offline in the declared interface;
causal delivery is not proved. Finite bits, finite shots, numerical
sampler evaluation, effective accuracy rates, uniform native resources
and physical implementation remain separate obligations. The finite
primitive expectations are not uniform physical resource bounds.
The full source continues conservatively after an observation exit,
whereas the command output is held. There is no extension of $\Psi$
after its original slab, arbitrary-intervention equivalence,
source-independent affine/CPTP realization, or complete native
legal-source/evolution/representation/readout correspondence here.
The physical spatial dimension and the full why-three objective
remain unresolved. These are ordinary conditional mathematical
results, with no Lean-certification or worldwide-priority claim.

## 追加锚（本行以下为增补区）


## 24. Timed entrance and killed releases from the original source

**Definition 24.1 (original data and two timed laws).** Retain exactly
Definitions 7.1, 11.1 and 15.1, for every original $a,\eta>0$.
Thus $F$ has only its source-killed role, $P_t^0=J_h^{-1}e^{-tF}J_h$,
$q_t=J_h^{-1}Fe^{-tF}h$, $m=h^2\mu$, and $\nu,\kappa$ are (15.2).
The full conservative process has the entire complex domains (7.2),
(16.6), original source trace and response (16.5)--(16.7), and selector
[E, (112.5)]. Neither a value $h(e)$ nor a new source condition is used.
All times below are original elapsed times.

Fix $\epsilon,\delta>0$. Use the already defined $\mathfrak d$ and
$\chi_\epsilon$ of (20.1), and put $c_\epsilon=\kappa(\epsilon)$.
Let $\mathsf D^\epsilon$ be the driftless subordinator with Levy measure
$\mathbf1_{(0,\epsilon]}(v)\mathfrak d(v)dv$; only its scalar laws
are used in the following probability measure on $[0,\infty)$:

$$
\begin{gathered}
 \mathsf U_\epsilon(B)=\int_0^\infty
 c_\epsilon e^{-c_\epsilon b}
               \mathbb P(\mathsf D_b^\epsilon\in B)\,db,\\
 \int e^{-\lambda u}\mathsf U_\epsilon(du)
       =\frac{c_\epsilon}{c_\epsilon+\chi_\epsilon(\lambda)},
                  \qquad \lambda\ge0,\\
 \mathsf W_\epsilon(dv,dp)
       =\mathsf U_\epsilon(d(v-\epsilon))
                    \frac{q_\epsilon(p)m(dp)}{c_\epsilon},
              \qquad v\ge\epsilon,\quad p\in M.
\end{gathered}
\tag{24.1}
$$

The notation in the last line means the pushforward under
$(u,p)\mapsto(u+\epsilon,p)$. It is a joint elapsed-wait/state law,
not advance disclosure of either variable.
For $p\in M$ define the marked killed-release kernel by

$$
\begin{aligned}
 \mathsf K_\delta(p;ds,\mathrm C,dp')
   &=\mathbf1_{(0,\delta]}(s)q_s(p)\,ds\,\delta_e(dp'),\\
 \mathsf K_\delta(p;ds,\mathrm D,dp')
   &=\delta_\delta(ds)P_\delta^0(p,dp').
\end{aligned}
\tag{24.2}
$$

Type $\mathrm C$ denotes first original-source contact. Type
$\mathrm D$ denotes survival for $\delta$ and the then current state.
The legitimate versions and normalization of this formula are part
of the next assertion. Neither law is a full-process transition
sampler $T_t(p,\cdot)$.

**Lemma 24.2 (normalization and reached-state versions).** The laws
(24.1)--(24.2) have Borel probability versions on their indicated
spaces. There is one Borel $m$-null set $B\subset M$, containing the
properly exceptional set away from $e$, such that for $p\notin B$
(24.2) is the actual joint law of

$$
 (\tau_e\wedge\delta,\mathrm C,e)\quad\hbox{if }\tau_e\le\delta,
 \qquad (\delta,\mathrm D,Z_\delta)\quad\hbox{if }\tau_e>\delta
\tag{24.3}
$$

under the original legitimate $\mathbb P_p$. On $B$ any Borel
probability extension may be used. Every non-source state reached
by the recursion below avoids $B$ almost surely. The set $B$ is
not asserted polar beyond the properly exceptional subset.

**Proof.** Theorem 15.2 gives $0<c_\epsilon<\infty$,
$\int q_\epsilon dm=c_\epsilon$ and
$\int_0^\infty v\mathfrak d(v)dv=1$.
Thus the displayed Levy measure is admissible, has no killing or
drift, and has exponent $\chi_\epsilon$. Integrating its probability
laws against the exponential probability density proves both
normalization of $\mathsf U_\epsilon$ and its Laplace formula.
Consequently $\mathsf W_\epsilon$ is a Borel probability law.
Subordinator laws and the entrance density here are the scalar and
one-evaluation suppliers of §§15, 20, without a new normalization claim.

Choose the original Borel Hunt kernel $P_t^0$ outside its properly
exceptional set, and the nonnegative jointly measurable $q_s$ of
Theorem 15.2. The integrated identity
$-\partial_sP_s^01=q_s$ used in Lemma 20.2 implies, off an
$m$-null Borel set,

$$
 P_a^01(p)-P_b^01(p)=\int_a^bq_s(p)ds
                         \quad(0<a<b<\infty).
\tag{24.4}
$$

To obtain a common set, first impose this identity at all positive
rational endpoints. Let $a\downarrow0$, $b\uparrow\infty$ through
rationals. Continuity at time zero from a legitimate $p\ne e$,
source recurrence [S, (116.10)] and monotone convergence give
$\int_0^\infty q_s(p)ds=1$. Right-continuity of killed survival
then extends (24.4) to every endpoint. In particular its lifetime
law is absolutely continuous, with density $q_s(p)$, and

$$
 \int_0^\delta q_s(p)ds+P_\delta^01(p)=1.
\tag{24.5}
$$

Enlarge the null set to $B$ as stated. Equations (24.3)--(24.5)
prove the probability and original-law assertions; ties at
$\tau_e=\delta$ have probability zero. Defining the kernel to be
$\delta_{(\delta,\mathrm C,e)}$ on $B$ gives a Borel extension.
No ordinary value at the source enters this argument.

An entrance release has distribution $q_\epsilon m/c_\epsilon$,
which is absolutely continuous with respect to $m$. If $\xi\ll m$
is any finite input measure, symmetry implies
$\xi P_\delta^0\ll m$: for $m(A)=0$, $P_\delta^01_A=0$
$m$-a.e. Thus every survived state release remains absolutely
continuous, also after weighting by a past event. Source contacts
are exactly $e$, which is legitimate and outside the properly
exceptional set. Induction over the countably many releases proves
avoidance of $B$ at every non-source input. This justifies the
state-indexed versions actually consumed, without an assertion about
arbitrary exceptional starting states. $\square$

**Theorem 24.3 (recursive timed correspondence with one original source).**
Start at elapsed time zero with the source flag $e$. In source mode
use $\mathsf W_\epsilon$, release its state with type $\mathrm E$
when its wait expires, and enter killed mode. In killed mode at a
released state $p$, use $\mathsf K_\delta(p;\cdot)$; a type
$\mathrm D$ event repeats killed mode at its released state and a
type $\mathrm C$ event reenters source mode. Add each elapsed wait
to the preceding event time. This defines a joint law of all finite
released prefixes by the usual iterated Borel kernels.

There is a coupling with one unchanged full original source
$\mathsf Z\sim\mathbb P_e$ in which every released state is its
actual state at its release time. Each event time is a stopping
time in its usual source filtration $\mathcal F^{\mathsf Z}$.
During a source-mode wait, the event is the first time a new
excursion has reached age $\epsilon$, not a forecast of its lifetime.
In killed mode it is precisely (24.3), in the original clock.
The source is never killed at a type $\mathrm C$ event.
On $[0,T]$ the number of completed events is at most

$$
 2\lfloor T/\epsilon\rfloor+\lfloor T/\delta\rfloor,
\tag{24.6}
$$

and the number of initiated timed primitives is at most this bound
plus one. A primitive still pending at $T$ supplies only nonarrival.

**Proof.** On a source path started at $e$ at time $c$, let
$g_c(t)=\sup\{s\in[c,t]:\mathsf Z_s=e\}$ and set

$$
 D_\epsilon(c)=\inf\{t\ge c:t-g_c(t)\ge\epsilon\}.
\tag{24.7}
$$

This uses only the path through the indicated time. More explicitly,
$\{D_\epsilon(c)<t\}$ is the union, over rational $v<t$ with
$v>c+\epsilon$, of the events
$g_c(v)<v-\epsilon$. The latter says that the compact segment
$[v-\epsilon,v]$ contains no source visit and is a Borel event in
$\mathcal F_v^{\mathsf Z}$. An excursion reaching age $\epsilon$
has strictly greater lifetime, so has such rational times immediately
after its age-$\epsilon$ time. Right-continuity of the filtration
proves the stopping assertion; the same argument after a source
stopping time proves the recursive assertion. The state at that time
is measurable in its stopping-time sigma-field. All these path
functionals are Borel, by the same rational and compact-minimum tests.

Use the original excursion representation of §§15--16 only as a
proof witness. The first label $E$ with $\zeta>\epsilon$ is exponential
of rate $c_\epsilon$. The excursions with $\zeta\le\epsilon$
are independent of these labels, with duration subordinator
$\mathsf D^\epsilon$. There is no inverse-clock drift. The elapsed
start of that first long excursion is therefore
$\mathsf D_{E-}^\epsilon$, and its age-$\epsilon$ state has law
$q_\epsilon m/c_\epsilon$, independent of that elapsed start.
Independence follows by restriction and marking of the original
Poisson measure; conditionally on $E=b$ the small total has law
$\mathsf D_b^\epsilon$, since a fixed label is not an atom.
This gives exactly (24.1), with release at
$c+\mathsf D_{E-}^\epsilon+\epsilon$.
The original lifetime density $\mathfrak d(v)dv$ gives no mass to
$\zeta=\epsilon$, and $D_\epsilon(c)<\infty$ almost surely.
These assertions require no bridge from a singular fixed endpoint.

At an entrance release, apply the strong Markov property of the
original full diffusion at $D_\epsilon(c)$. Until its next source
contact its law is precisely the part process (15.1), with the
entire killed domain [S, (116.11)]. Lemma 24.2 gives (24.2).
At a survived release the same strong Markov argument restarts
that part law. At source contact the full process restarts with
$\mathbb P_e$, by [S, Theorem 116.4]; apply (24.7) again.
Induction proves every iterated joint kernel, not only one-event
marginals. Lemma 24.2 supplies all reached-state qualifications.
This constructs the claimed coupling and identifies the recursive
law without supplying a complete path to its consumer.

Each completed entrance uses a disjoint elapsed wait of at least
$\epsilon$, so there are at most $\lfloor T/\epsilon\rfloor$
such events. Each completed type $\mathrm D$ consumes a disjoint
$\delta$ interval, so there are at most $\lfloor T/\delta\rfloor$
of those. A type $\mathrm C$ closes an episode begun by a distinct
entrance, so its count is bounded by the entrance count. These facts
prove (24.6), rule out finite-time accumulation, and bound initiated
primitives since only one is pending at a time. $\square$

## 25. Acquired information and the same-time released approximation

**Assumption 25.1 (timed service, calibration and clock).** An added
analytic service implements exactly the recursive timed laws
(24.1)--(24.2), calibrated to the fixed original $F,h,q,P^0,\nu,\kappa$.
Its availability is an additional model premise; the law/coupling
in Theorem 24.3 does not install it in bare native operations.
An exact original elapsed clock is available. Requests and numerical
calculation have zero analytic time overhead. A primitive discloses
only its type, current four real state coordinates and timestamp at
arrival. While pending it supplies the passage of the clock and
nonarrival, with no pending value, random seed or future timestamp.
The initial source flag and preparation parameters are known.

Let $R_i,C_i,P_i$ denote the successive release times, types and
states. The acquired filtration $\mathcal G_t$ is the usual
augmentation of the sigma-field generated by the marked records

$$
 \sum_{R_i\le s}\mathbf1_{\{C_i=c\}}f(R_i,P_i),
     \qquad 0\le s\le t,\quad c\in\{\mathrm E,\mathrm C,\mathrm D\},
\tag{25.1}
$$

for bounded Borel $f$. Request modes and times are determined by these
records. This definition includes all nonarrival events and their
elapsed durations. There is no independent initial seed.
Only arrivals from (24.2) in killed mode announce source contact;
source mode does not announce its infinitely many small source visits.
A contact notification concerns the original point $e$, not merely
one of the false preparation contacts of §11. Exact hidden $z$
information belongs to this added source service, with no native
$z$ actuator or extra output.

**Theorem 25.2 (filtration containment and released-state accuracy).**
Under Theorem 24.3's coupling,
$\mathcal G_t\subseteq\mathcal F_t^{\mathsf Z}$ for every $t$.
Let $V_t$ be the last released state, with initial value $e$,
held constant between releases and changed to $e$ at type
$\mathrm C$. Then $V$ is a finite right-continuous step path on
$[0,T]$, measurable from the acquired prefix, and

$$
 \sup_{0\le t\le T}|V_t-\mathsf Z_t|_\infty
       \le\Omega_T(\mathsf Z;\epsilon\vee\delta).
\tag{25.2}
$$

Here $\Omega_T$ is the original coordinate modulus (21.2); it is
only a proof quantity. No query for it is part of the service.

**Proof.** The stopping-time and stopped-state assertions of Theorem
24.3 make every variable in (25.1) measurable in
$\mathcal F_t^{\mathsf Z}$. Nonarrival, including a pending request
started at an earlier random event time, is measurable there as well.
Usual augmentation preserves containment because the containing
filtration is complete and right-continuous. This proves containment
for the actual timed records, rather than just a generative kernel
with a hidden seed revealed at time zero.

In killed mode, if the last release was at $s$ and the next one has
not arrived, then $t-s<\delta$, and $V_t=\mathsf Z_s$.
In source mode $V_t=e$. Before (24.7), the current excursion has
age less than $\epsilon$, so either $\mathsf Z_t=e$, or its most
recent source visit $g_c(t)$ is less than $\epsilon$ time units
old. Hence $|\mathsf Z_t-e|_\infty\le\Omega_T(\mathsf Z;\epsilon)$.
Unannounced earlier small excursions need not be identified.
At every release the new value is exactly $\mathsf Z_t$.
This proves (25.2), including all waiting intervals and endpoints.
Finiteness is (24.6). No Poisson label or complete excursion is
supplied, and no small-duration total or list is supplied separately
or in advance. At a type $\mathrm E$ release time $R$ for a
source-mode request begun at the known time $c$, Theorem 24.3 gives
$R-c-\epsilon=\mathsf D^\epsilon_{E-}$. This retrospective total of
the preceding small-excursion durations in that episode is measurable
from the released prefix, hence belongs to
$\mathcal G_R\subseteq\mathcal F_R^{\mathsf Z}$.
The consumer of §26 does not use this total. $\square$

## 26. Prospective execution by actual original native histories

**Assumption 26.1 (real numerical actuation).** Retain exactly the
preparations, probabilities, periods, native fields, partial command
law, concatenation and refusal of Definitions 1.1--1.2 and §7.
A finite list of real two-control vertices and positive real durations
known at issuance may be executed as its specified piecewise linear
history in the original clock. Finite exact numerical computations
and zero-velocity holds are available. No uniform precision, speed,
energy, processing cost or physical realization is assumed.
No direct central or $z$ operation, integral reset, amplitude
preparation or new readout is added.

**Definition 26.2 (one-cell prospective prescription).** Fix any
original allowed preparation, $I=[l,u]\Subset(0,H_{\rm n})$ with
$l<k_0<u$, $T>0$, integer $N\ge2$ and
$0<\rho\le(u-l)/4$. Put $\Delta=T/N$, $t_j=j\Delta$, and
$P_j=V_{t_j}$, $0\le j<N$. At a grid time include all records
which have arrived at that time. Thus $P_0=e$.
Define the following continuous four-coordinate polygon as a
mathematical description of the successive prescriptions:

$$
 Q(t)=e\ (0\le t\le\Delta),\qquad
 Q(t_j+s)=(1-s/\Delta)P_{j-1}+(s/\Delta)P_j,
 \quad 0\le s\le\Delta,\quad 1\le j<N.
\tag{26.1}
$$

Coordinate interpolation uses the fixed real coordinates of $G$.
At $t_j$ the entire next cell is known from the released prefix.
Put $\widehat S=T\wedge\inf\{t:k_0+x(Q(t))\notin(l,u)\}$.
This global notation is not an input containing its future value.
At $t_j$, if no own observation exit has occurred, compute just the
first boundary intersection of that cell's known linear height
segment. Clip that cell at that intersection, if present, and issue
no later nonconstant command after the resulting own exit.

Start with zero controls on $[0,\Delta]$. For every remaining
positive cell portion $[s,t]$ to be executed, its two endpoint
triples $(A,B,W)=(x,y,w)(Q)$ are already known at its grid start.
Subdivide that portion into $m$ equal cells, with $m$ exactly (22.2),
using its total increments and $K_I=\max(|l-k_0|,|u-k_0|)$.
For each subdivision use the existing six-leg connector (17.4),
with the same inward orientation and real area, translated by its
current two-control start. Assign each leg one sixth of that
subdivision's original elapsed duration. All these numerical
instructions are issued at the grid start; they act only after it.
Hold at own observation exit, or end at $T$.
Call the resulting actual controls $(a_*,b_*)$ and set
$J_* =\int a_*\,db_*$. The star labels a finite design, not a limit.
The source service can continue through $T$ after this output hold;
the consumer ignores its subsequent records.

**Theorem 26.3 (finite lawful prospective consumer and exact own exit).**
Definition 26.2 is a Borel map from the finite timed record to a
finite original native history. Every issued numerical profile is
$\mathcal G_{t_j}$-measurable. Its own censored observation exit is
exactly $\widehat S$, and for all actual prefixes

$$
 l\le k_0+a_*(t)\le u,
 \qquad 0<k_0+\min a_*\le k_0+\max a_*<H_{\rm n}.
\tag{26.2}
$$

Its complete numerical command has exactly the original domain
$(-\min a_*,H_{\rm n}-\max a_*)$, including refusal and the original
pulled-back domain under concatenation. With
$(A,B,W)(t)=(x,y,w)(Q(t\wedge\widehat S))$, one has

$$
 \|a_*-A\|_\infty\le3\rho,\qquad
 \|b_*-B\|_\infty\le4\rho,\qquad
 \|J_*-W\|_\infty\le4K_I\rho+4\rho^2.
\tag{26.3}
$$

All actual legs have finite pathwise velocities and positive durations.
The probabilities and all ten held outputs are exactly those of
(7.8), with phases

$$
 \alpha_*=[\alpha_0+b_*/2],\qquad
 \beta_*=[\beta_0+c_0b_*-J_*/r],\qquad
 k_*=k_0+a_*.
\tag{26.4}
$$

In particular both positive-$\alpha$ pairs, both negative-$\alpha$
pairs and the $\beta$ pair retain their ordered signs, factors two,
fixed preparation rotations and actual $2\pi$ periods.

**Proof.** At $t_j$, $P_{j-1},P_j$ are known, and no instruction
on $[0,t_j)$ is changed. A boundary intersection of the next known
linear segment is computed by a comparison and a linear ratio;
a constant segment is treated separately. Until that intersection
all anchor heights are interior; the final one, if any, is on the
observation boundary. Thus every positive portion used in the
prescription has positive duration and finite endpoints.

Apply the deterministic subdivision and connector argument of
Theorem 22.2 on this known portion. Equation (22.2) guarantees
$|X|,|Y|\le\rho$, $|C|\le\rho^2$ and the same bounds at every
linear prefix of its desired triple, where
$C=\Delta W-A_s\Delta B$. The supplied [GL, Lemma 17.1] makes
every connector's height interior except possibly its final height
at the clipped boundary. Its real relative integral ends at $C$.
Under translation its global integral at a partial prefix is
$W_s+A_s y+j$, hence ends at
$W_s+A_s\Delta B+C=W_t$. This is the original chronological
cross term, not an assignment to a central control. Induction over
all subdivisions and grid cells proves endpoint matching and
(26.3), by the same deterministic estimates as (22.4).
It also proves that no connector reaches an observation wall
earlier than its polygon, and its final height leg reaches that
wall exactly at the polygon's crossing time. This proves the
own-exit assertion and (26.2). Arriving at $l$ or $u$ remains
strictly lawful for the original, larger native slab.

For the realized numerical list, original lawfulness at another
height is still precisely the extrema test (7.6), with the original
phases unrestricted. Its exact domain is therefore the interval
stated in the theorem. Applying [N, Theorems 9.2--9.3] to each
concatenation retains its refusal and pulled-back guard. This
assertion evaluates the same numerical command on its domain;
it does not rerun this preparation-dependent policy at other heights.
A source-contact flag merely supplies a future target value. It
never resets the actual controls, their phases or their accumulated
real integral.

There are at most $N$ polygon portions including the initial hold.
The number of subdivisions of each is finite, since all its
increments are finite. More explicitly, with $V_A,V_B,V_W$ the
finite variations of the stopped polygon triple, the native leg
count is bounded by

$$
 6\left(N+\frac{V_A+V_B}{\rho}
                    +\frac{V_W+K_IV_B}{\rho^2}\right)+1.
\tag{26.5}
$$

This is the reused ceiling bound (22.5), now applied cell by cell
at issuance. Every leg divides a finite increment by a positive
duration, giving finite pathwise velocity and variation. There
are finitely many releases and primitive initiations by (24.6).
The finite comparisons, clipping ratios, ceilings and connector
formulas are Borel, also on the countable union of the finite-list
spaces of Definition 17.1. They establish the asserted actual
pushforward command law and issuance measurability. The command
through each time is a function of the acquired prefix and clock.
Finally (7.5) gives exactly (26.4) and the probabilities
$(k_*,H_{\rm n}-k_*,Z,H_{\rm n}-k_*,k_*)$. Substitution in (7.8)
proves every signed-pair assertion. Hidden $z$ never enters these
controls or readouts. $\square$

## 27. Joint original-time held outputs and the consumer's own exit

**Theorem 27.1 (original-source causal-release correspondence).**
Under Assumptions 25.1 and 26.1, fix any original $a,\eta>0$,
allowed preparation, interior $I$ and finite $T$ as above.
For every deterministic sequence
$\epsilon_n,\delta_n,\rho_n\downarrow0$ and $N_n\to\infty$,
with the stated positive design ranges, the corresponding finite
laws have a common coupling with the unchanged original source
such that

$$
 \|\mathcal O_n-O^I\|_{[0,T]}\longrightarrow0,
 \qquad \widehat S_n\longrightarrow T\wedge\theta_I
                              \quad\hbox{almost surely}.
\tag{27.1}
$$

Here $\mathcal O_n(t)$ is the actual ten-output path of Definition
26.2 held at its own observation exit; $O^I(t)$ is precisely (17.1)
at the same original elapsed time $t$. In particular their joint
laws with the censored own exit converge in the uniform ten-output
path topology times $[0,T]$. The consumer observes neither the
original target exit nor any target modulus. Source contacts and
observation exits are distinct events throughout this assertion.

**Proof.** Use one original full source as Theorem 24.3's witness
for all designs, taking the countable intersection of their
probability-one version and coupling events. By (25.2), for the
unstopped virtual polygon (26.1),

$$
 \|Q_n-\mathsf Z\|_{[0,T],\infty}
 \le \Omega_T(\mathsf Z;\epsilon_n\vee\delta_n)
                         +\Omega_T(\mathsf Z;2T/N_n).
\tag{27.2}
$$

Indeed, on a cell $[t_j,t_{j+1}]$ its endpoints are sampled from
$V$ at $t_{j-1},t_j$. Each endpoint differs from the source at the
same sample time by at most the first modulus. Both sample times
are at distance at most $2T/N_n$ from the present time. A convex
combination gives (27.2). On the first cell the polygon is $e$
and the second modulus alone suffices. Continuity makes (27.2)
tend to zero almost surely. This is a same-time bound: no time
change, retrospective endpoint execution, deleted duration or
redistributed waiting time is involved.

For completeness, the passage to the consumer's own exit uses the
specific crossing supplier Lemma 21.3. Write $S=T\wedge\theta_I$.
On every compact time interval strictly before $S$, the source
height is uniformly inside $(l,u)$, so (27.2) gives
$\liminf\widehat S_n\ge S$. If $S<T$, the original source height
strictly crosses its attained wall arbitrarily soon after $S$:
that lemma uses the locally elliptic original generator (21.6),
positive coefficient $a$, bounded localized drift away from $e$,
and the strong Markov property at that wall. Each such strict
outward value before $S+b<T$ forces the continuous polygon to
exit by $S+b$ for all sufficiently large $n$. Thus
$\limsup\widehat S_n\le S$. If $S=T$, the censored upper bound is
already $T$, including target exit exactly at $T$.
This proves the exit convergence using strict crossings, not
uniform path convergence alone. Theorem 26.3 identifies these
polygon exits with actual native own exits, which is the additional
passage needed for the prospective consumer.

Uniform continuity of the original path now gives

$$
 \|Q_n(\,\cdot\wedge\widehat S_n)
       -\mathsf Z(\,\cdot\wedge S)\|_{[0,T],\infty}
 \le\|Q_n-\mathsf Z\|_{[0,T],\infty}
                +\Omega_T(\mathsf Z;|\widehat S_n-S|)\to0.
\tag{27.3}
$$

Add (26.3). The resulting actual triples converge uniformly to
$(x,y,w)(\mathsf Z_{\,\cdot\wedge S})$. Formula (26.4) bounds
the real phase errors by one half of the $b$ error and by
$|c_0|$ times that error plus $r^{-1}$ times the integral error.
Reducing only then modulo $2\pi$ and using uniform continuity
of the exact ten-output map (7.8) on $I\times\mathbb T^2$
proves (27.1), for every fixed preparation rotation. Weak joint
convergence follows by bounded continuous tests. The source used
in this proof continues conservatively after every observation
exit. Only actual native outputs are held. $\square$

**Corollary 27.2 (finite designs at fixed error and risk).** For every
positive output tolerance and positive failure probability there
are deterministic finite choices of $\epsilon,\delta,N,\rho$ for
which the joint output/censored-own-exit error exceeds that
tolerance with probability less than the prescribed risk.
All timed requests and actual native legs are finite on $[0,T]$.

**Proof.** Choose any sequence in Theorem 27.1. Its almost-sure
joint convergence implies convergence in probability, so some finite
index meets the two prescribed constants. The bounds (24.6),
(26.5) apply at that index. This proves existence of law-dependent
finite designs, without an effective parameter-selection rate or
a path-modulus input. $\square$

## 28. Method correspondence and remaining source obligations

**Definition 28.1 (mature inputs and the source-specific composite).**
The excursion input is Fukushima--Tanaka,
[*Poisson point processes attached to symmetric diffusions*,
DOI 10.1016/j.anihpb.2004.10.004, §3.1, Theorem 3.1,
(3.4)--(3.12)](https://www.numdam.org/item/AIHPB_2005__41_3_419_0.pdf).
Its $S,a,S_0,m,p_t^0,\mu_t$ are exactly
$G,e,M,h^2\mu,P_t^0,q_tm$ here; the recurrent-point hypotheses
are those already checked in Theorem 15.2. Independent Poisson
restriction, scalar subordinator mixing, strong Markov restarting
and finite deterministic interpolation are mature methods.
The age-$\epsilon$ announcement keeps their information in the
original filtration instead of revealing the selected excursion's
future duration. No separate general excursion theorem is asserted.

Lambert--Simatos,
[*The weak convergence of regenerative processes using some excursion
path decompositions*, DOI 10.1214/12-AIHP531, §3.2, (3) and
Lemma 3.1](https://www.numdam.org/item/10.1214/12-AIHP531.pdf),
uses truncation of excursions with a size functional. With size
$\zeta$, its whole-excursion retention criterion involves lifetime;
it is not itself a causal acquisition rule. Formula (24.7) instead
announces elapsed age, and (25.2) covers its still-unannounced prefix
by continuity in the same original time. No uniform resource or
regenerative convergence hypothesis is borrowed from that paper.
Yano, [*Functional limit theorems for processes pieced together from
excursions*, arXiv:1309.2652v3, Definition 2.3, Remark 2.4 and
Theorem 2.5](https://arxiv.org/html/1309.2652v3), distinguishes path
convergence from lifetime convergence. Its general limit theorem is
not invoked: the own-exit argument is (27.2)--(27.3) with the original
wall-crossing supplier. Chaumont--Uribe Bravo,
[*Markovian bridges: weak continuity and pathwise constructions*,
arXiv:0905.2155v3, Theorem 1 and (H1)--(H3)](https://arxiv.org/html/0905.2155v3),
requires a Feller family and appropriate transition-density continuity
for its endpoint bridges. No unverified such hypothesis at $e$ is
used in (24.1)--(24.4).

The repo-derived composite is the specific timed laws and their
recursive original-source coupling, original-filtration release
ceiling, and prospective finite actual-native consumer with the
same-time ten-output/censored-own-exit limit (27.1). Its source
trace, full complex selector and killed domain are §§15--16 and
[S, §§115--116]; its original partial-action map is §7. The connector
geometry, real chronology, guards and deterministic estimates are
reused from [GL, Lemma 17.1], Theorems 17.2 and 22.2, not new
steering theory. The Brownian-target causal contracts of [GL,
§§26--40] and its paid-point contract of §41 have different source
laws and observations. They neither install (25.1) nor transfer a
Brownian estimate to the original source here. No almost-sure fixed
hard tube or Brownian resource rate is asserted by (27.1).

**Definition 28.2 (added premises and the exact unpaid boundary).**
Calibration and availability of the exact timed service, including
source-versus-false-contact discrimination, hidden four-coordinate
states, nonarrival monitoring, immediate notification and exact
original-clock timestamps, are Assumption 25.1. Finite exact real
computation and original two-control execution are Assumption 26.1.
These are explicit analytic model additions. Deriving their joint
law and filtration coupling is not deriving their availability from
bare FIB. No omitted-gap total or list is supplied separately or in
advance; at entrance arrival the preceding small-duration total is
retrospectively inferable as in the proof of Theorem 25.2, but is not
used by the consumer. No pending sample, seed, future lifetime,
Poisson label, complete mark, full source path, target exit or target
modulus is available to execution.
A full path is only the coupling witness; the acquired finite
record is exactly (25.1). All decisions use its released prefix.

Native acquisition, finite bits or shots, effective sampler evaluation,
effective accuracy rates, uniform information/leg/speed/energy bounds,
and physical timed notification and actuation remain separate
obligations. The realized finite command has its entire original
partial domain; the causal service law does not assert arbitrary
intervention equivalence, install a source-independent affine/CPTP
action, or provide a post-slab map for $\Psi$. Sections 1--14 and
[B, §§12.1--12.3] retain their free/central-fiber, contact, reference-law
and affine/CPTP boundaries and their surviving nonlinear source-law
actions. The variable-coefficient, independent-central-noise and
spatial-cap/all-real-limit suppliers retain the different carriers,
sources, walls and clocks specified in Definition 19.1.
No source-clock recovery of §18 follows from these approximations.
The original complete native legal-source/evolution/representation/
readout correspondence, physical spatial dimension and full
why-three objective remain unresolved. These are conditional ordinary
mathematical results, with no Lean-certification or worldwide-priority
claim.

## 追加锚（本行以下为增补区）
