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
